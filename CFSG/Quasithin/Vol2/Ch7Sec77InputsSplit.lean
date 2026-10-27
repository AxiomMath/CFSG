module

public import CFSG.Quasithin.Vol2.Ch7Sec77A23Stmts
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Quasithin.Vol2.Ch7Sec77Inputs

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint

variable {S : Type} [Group S] [Finite S]

omit [Finite S] in
theorem not_isCyclic_of_elemAbelian_four {Z : Subgroup S} (hZ : IsElemAbelian 2 Z)
    (hZc : Nat.card Z = 4) : ¬ IsCyclic ↥Z := by
  intro hcyc
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have h1 : orderOf g = 4 := by rw [orderOf_eq_card_of_forall_mem_zpowers hg, hZc]
  have h2 : g ^ 2 = 1 := Subtype.ext (by simpa using hZ.2 g g.2)
  have h3 := orderOf_dvd_of_pow_eq_one h2
  rw [h1] at h3
  omega

omit [Finite S] in
theorem isElemAbelian_two_mono {A B : Subgroup S} (hAB : A ≤ B) (hB : IsElemAbelian 2 B) :
    IsElemAbelian 2 A := CFSG.Open.IsElemAbelian.mono hB hAB

theorem exists_four_le_center {P E : Subgroup S} (hEP : E ≤ P) (hE : IsElemAbelian 2 E)
    (hEcard : Nat.card E = 16) (hPN : P ≤ Subgroup.normalizer (E : Set S))
    (hidx : (P ⊓ Subgroup.centralizer (E : Set S)).relIndex P ≤ 2) :
    ∃ Z : Subgroup S, Z ≤ E ∧ Z ≤ P ⊓ Subgroup.centralizer (P : Set S) ∧ IsElemAbelian 2 Z ∧
      Nat.card Z = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  set C : Subgroup S := E ⊓ Subgroup.centralizer (P : Set S) with hC
  have hCcard : 4 ≤ Nat.card C := by
    by_cases hPE : P ≤ Subgroup.centralizer (E : Set S)
    · have hCE : C = E := le_antisymm inf_le_left fun v hv =>
        ⟨hv, Subgroup.mem_centralizer_iff.mpr fun x hx =>
          (Subgroup.mem_centralizer_iff.mp (hPE hx) v hv).symm⟩
      rw [hCE, hEcard]
      omega
    obtain ⟨t, htP, htE⟩ : ∃ t ∈ P, t ∉ Subgroup.centralizer (E : Set S) := by
      by_contra h
      push Not at h
      exact hPE h
    set D := P ⊓ Subgroup.centralizer (E : Set S) with hD
    have hidx2 : (D.subgroupOf P).index = 2 := by
      have h1 : D.relIndex P ≠ 1 := fun h =>
        htE ((Subgroup.relIndex_eq_one.mp h) htP).2
      have h0 : D.relIndex P ≠ 0 := Subgroup.index_ne_zero_of_finite
      change D.relIndex P = 2
      omega
    have ht2 : t ^ 2 ∈ Subgroup.centralizer (E : Set S) := by
      have h1 := Subgroup.sq_mem_of_index_two hidx2 ⟨t, htP⟩
      rw [Subgroup.mem_subgroupOf] at h1
      exact h1.2
    have htN := hPN htP
    have hmemE : ∀ v ∈ E, t * v * t⁻¹ * v⁻¹ ∈ E := fun v hv =>
      E.mul_mem ((Subgroup.mem_normalizer_iff.mp htN v).mp hv) (E.inv_mem hv)
    let f : ↥E →* ↥E := MonoidHom.mk' (fun v => ⟨t * v * t⁻¹ * (v : S)⁻¹, hmemE v v.2⟩)
      (fun v w => by
        apply Subtype.ext
        have ha := (Subgroup.mem_normalizer_iff.mp htN v).mp v.2
        have hb := (Subgroup.mem_normalizer_iff.mp htN w).mp w.2
        simp only [Subgroup.coe_mul, mul_inv_rev]
        have e1 := hEc _ (E.inv_mem v.2) _ hb
        have e2 := hEc _ (E.inv_mem v.2) _ (E.inv_mem w.2)
        calc t * (↑v * ↑w) * t⁻¹ * ((↑w)⁻¹ * (↑v)⁻¹)
            = (t * ↑v * t⁻¹) * (t * ↑w * t⁻¹) * ((↑w)⁻¹ * (↑v)⁻¹) := by group
          _ = (t * ↑v * t⁻¹) * (t * ↑w * t⁻¹) * ((↑v)⁻¹ * (↑w)⁻¹) := by rw [e2]
          _ = (t * ↑v * t⁻¹) * ((↑v)⁻¹ * (t * ↑w * t⁻¹)) * (↑w)⁻¹ := by
              rw [e1]; group
          _ = t * ↑v * t⁻¹ * (↑v)⁻¹ * (t * ↑w * t⁻¹ * (↑w)⁻¹) := by group)
    have hfv : ∀ v : ↥E, ((f v : ↥E) : S) = t * v * t⁻¹ * (v : S)⁻¹ := fun v => rfl
    have hff : f.range ≤ f.ker := by
      rintro _ ⟨v, rfl⟩
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      rw [hfv, hfv, OneMemClass.coe_one]
      set a : S := t * v * t⁻¹ with ha
      have haE : a ∈ E := (Subgroup.mem_normalizer_iff.mp htN v).mp v.2
      have hta : t * a * t⁻¹ = v := by
        have h1 := Subgroup.mem_centralizer_iff.mp ht2 v v.2
        calc t * a * t⁻¹ = t ^ 2 * v * (t ^ 2)⁻¹ := by rw [ha, pow_two]; group
          _ = v := by rw [← h1]; group
      have hsq : (v : S) * a⁻¹ * ((v : S) * a⁻¹) = 1 := by
        have := hE.2 _ (E.mul_mem v.2 (E.inv_mem haE))
        rwa [pow_two] at this
      have e1 := hEc _ v.2 _ (E.inv_mem haE)
      calc t * (a * (↑v)⁻¹) * t⁻¹ * (a * (↑v)⁻¹)⁻¹
          = (t * a * t⁻¹) * (t * (↑v)⁻¹ * t⁻¹) * ((↑v) * a⁻¹) := by group
        _ = (↑v) * a⁻¹ * ((↑v) * a⁻¹) := by rw [hta, ha]; group
        _ = 1 := hsq
    have hkerC : f.ker.map E.subtype ≤ C := by
      rintro _ ⟨v, hv, rfl⟩
      have hv1 : t * v * t⁻¹ * (v : S)⁻¹ = 1 := by
        rw [← hfv]
        exact congrArg Subtype.val hv
      have htv : t * v = v * t := by
        have := hv1
        calc t * ↑v = (t * ↑v * t⁻¹ * (↑v)⁻¹) * ↑v * t := by group
          _ = ↑v * t := by rw [this, one_mul]
      refine ⟨v.2, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
      by_cases hxD : x ∈ Subgroup.centralizer (E : Set S)
      · exact (Subgroup.mem_centralizer_iff.mp hxD v v.2).symm
      ·
        have h1 : t⁻¹ * x ∈ D := by
          have hmul := (Subgroup.mul_mem_iff_of_index_two hidx2 (a := (⟨t, htP⟩ : ↥P)⁻¹)
            (b := ⟨x, hx⟩))
          simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] at hmul
          refine hmul.2 (iff_of_false (fun h => htE ?_) (fun h => hxD h.2))
          have := D.inv_mem h
          rw [inv_inv] at this
          exact this.2
        have h2 := Subgroup.mem_centralizer_iff.mp h1.2 v v.2
        show x * (v : S) = (v : S) * x
        calc x * (v : S) = t * ((t⁻¹ * x) * (v : S)) := by group
          _ = t * ((v : S) * (t⁻¹ * x)) := by rw [← h2]
          _ = (t * (v : S)) * (t⁻¹ * x) := by group
          _ = ((v : S) * t) * (t⁻¹ * x) := by rw [htv]
          _ = (v : S) * x := by group
    have hcard := Subgroup.card_ker_mul_card_range f
    rw [hEcard] at hcard
    have hle := Subgroup.card_le_of_le hff
    have hk : Nat.card f.ker = Nat.card (f.ker.map E.subtype) :=
      (Subgroup.card_map_of_injective E.subtype_injective).symm
    have hkC := Subgroup.card_le_of_le hkerC
    by_contra hlt
    have h3 : Nat.card f.ker ≤ 3 := by omega
    have h4 : Nat.card f.ker * Nat.card f.range ≤ 3 * 3 :=
      Nat.mul_le_mul h3 (hle.trans h3)
    omega
  have hE2 : IsPGroup 2 ↥E := by
    refine IsPGroup.of_card (n := 4) ?_
    rw [hEcard]
    norm_num
  have hC2 : IsPGroup 2 ↥C := hE2.to_le inf_le_left
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2) (G := ↥C)).mp hC2
  have h4 : 2 ^ 2 ∣ Nat.card ↥C := by
    rw [hk]
    refine pow_dvd_pow 2 ?_
    by_contra h
    have : 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 2 h4
  refine ⟨K.map C.subtype, (Subgroup.map_subtype_le K).trans inf_le_left,
    ((Subgroup.map_subtype_le K).trans (le_inf (inf_le_left.trans hEP) inf_le_right)),
    isElemAbelian_two_mono ((Subgroup.map_subtype_le K).trans inf_le_left) hE, ?_⟩
  rw [Subgroup.card_map_of_injective C.subtype_injective, hK]
  norm_num

omit [Finite S] in
theorem not_forall_isCyclic_center {P Z : Subgroup S} (hP : IsSylowTwoOf P ⊤)
    (hZ : Z ≤ P ⊓ Subgroup.centralizer (P : Set S)) (hZe : IsElemAbelian 2 Z)
    (hZcard : Nat.card Z = 4) :
    ¬ ∀ T : Sylow 2 S, IsCyclic (Subgroup.center ↥(T : Subgroup S)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro h
  have hP2 : IsPGroup 2 ↥P := hP.2.1
  have hPidx : ¬ 2 ∣ P.index := by
    have := hP.2.2
    rwa [show (P.subgroupOf ⊤).index = P.index from Subgroup.relIndex_top_right P] at this
  have hcP : IsCyclic (Subgroup.center ↥P) := by
    have := h (hP2.toSylow hPidx)
    rwa [IsPGroup.toSylow_coe] at this
  have hZP : Z ≤ P := hZ.trans inf_le_left
  have hle : Z.subgroupOf P ≤ Subgroup.center ↥P := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro y
    have hz' : (z : S) ∈ Subgroup.centralizer (P : Set S) := (hZ (Subgroup.mem_subgroupOf.mp hz)).2
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hz' y y.2)
  have hcyc : IsCyclic ↥((Z.subgroupOf P).subgroupOf (Subgroup.center ↥P)) := inferInstance
  have e1 : ↥((Z.subgroupOf P).subgroupOf (Subgroup.center ↥P)) ≃* ↥(Z.subgroupOf P) :=
    Subgroup.subgroupOfEquivOfLe hle
  have e2 : ↥(Z.subgroupOf P) ≃* ↥Z := Subgroup.subgroupOfEquivOfLe hZP
  have hcZ : IsCyclic ↥Z := isCyclic_of_surjective (e1.trans e2).toMonoidHom (e1.trans e2).surjective
  exact not_isCyclic_of_elemAbelian_four hZe hZcard hcZ

theorem a23NoncyclicCenterFact_of (hcyc : A23CyclicCenterFact) (hsmall : A23SmallTwoRankFact) :
    A23NoncyclicCenterFact := by
  intro S _ _ hs hnab hlist P E Z hP hEP hE hEcard hZ hZe hZcard
  have hno16 : ¬ ∀ E' : Subgroup S, IsElemAbelian 2 E' → Nat.card E' ≤ 8 := fun h => by
    have := h E hE
    omega
  have hnocyc := not_forall_isCyclic_center hP hZ hZe hZcard
  rcases hlist with ⟨n, hn5, hn8, ⟨e⟩⟩ | hodd | (⟨f, hch⟩ | htits) | ⟨n, hn, hmod⟩ |
      ⟨s, hs', ⟨e⟩⟩
  ·
    by_cases h7 : n ≤ 7
    · exact absurd (hsmall S (Or.inl ⟨n, hn5, h7, ⟨e⟩⟩)) hno16
    · have hn : n = 8 := by omega
      subst hn
      exact absurd (hcyc S (Or.inl ⟨e⟩)) hnocyc
  ·
    exact absurd (hsmall S (Or.inr (Or.inl hodd))) hno16
  ·
    rcases hch with ⟨hf, h⟩ | ⟨hf, h⟩ | ⟨hf, h⟩ | ⟨hf, h⟩ | ⟨hf, h⟩ | ⟨hf, h⟩ | ⟨hfo, hf, h⟩ |
        ⟨hfo, hf, h⟩
    · exact ⟨f, hf, Or.inl h⟩
    · by_cases hf1 : f = 1
      · subst hf1
        exact absurd (hsmall S (Or.inr (Or.inr (Or.inl h)))) hno16
      · exact ⟨f, by omega, Or.inr (Or.inl h)⟩
    · exact ⟨f, hf, Or.inr (Or.inr (Or.inl h))⟩
    · exact ⟨f, hf, Or.inr (Or.inr (Or.inr (Or.inl h)))⟩
    · exact ⟨f, hf, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))⟩
    · by_cases hf1 : f = 1
      · subst hf1
        exact absurd (hcyc S (Or.inr (Or.inr (Or.inl h)))) hnocyc
      · exact ⟨f, by omega, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))⟩
    · exact ⟨f, by omega, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))⟩
    · exact ⟨f, by omega, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))⟩
  ·
    exact absurd (hcyc S (Or.inr (Or.inr (Or.inr (Or.inl htits))))) hnocyc
  ·
    exact absurd (hcyc S (Or.inr (Or.inl ⟨n, hn, hmod⟩))) hnocyc
  ·
    by_cases hJ1 : s = .J1
    · subst hJ1
      exact absurd (hsmall S (Or.inr (Or.inr (Or.inr ⟨e⟩)))) hno16
    · refine absurd (hcyc S (Or.inr (Or.inr (Or.inr (Or.inr ⟨s, ?_, ⟨e⟩⟩))))) hnocyc
      rcases hs' with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp_all

theorem a23FourCentralFact_of (h2 : A23NoncyclicCenterFact) (h3 : LieCentralIndexFact) :
    A23FourCentralFact := by
  intro S _ _ hs hnab hlist P E hP hEP hE hEcard hPN hidx
  obtain ⟨Z, -, hZc, hZe, hZcard⟩ := exists_four_le_center hEP hE hEcard hPN hidx
  have hLie := h2 S hs hnab hlist P E Z hP hEP hE hEcard hZc hZe hZcard
  refine ⟨hLie, fun x hx => h3 S hLie P hP x (hEP hx) ?_⟩
  have hle : P ⊓ Subgroup.centralizer (E : Set S) ≤ P ⊓ Subgroup.centralizer ({x} : Set S) :=
    inf_le_inf_left _ (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hx))
  exact (Subgroup.relIndex_le_of_le_left hle Subgroup.index_ne_zero_of_finite).trans hidx

end CFSG.Quasithin.H13
