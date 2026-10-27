module

public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1NNC
public import CFSG.GH74.KGroups.U33
public import CFSG.Quasithin.EmptyFaithful.SBc11List
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
public import Certificates.Certificate7137

public section

namespace CFSG.Quasithin.H13.KGG2



theorem factorization_seven {m : ℕ} (hm : m ∣ 27) : (224 * m).factorization 7 = 1 := by
  have hm0 : m ≠ 0 := by rintro rfl; norm_num at hm
  have h7 : ¬ 7 ∣ m := fun h => by
    have := Nat.dvd_trans h hm
    norm_num at this
  rw [Nat.factorization_mul (by norm_num) hm0, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd h7,
    show (224 : ℕ) = 2 ^ 5 * 7 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
    Finsupp.add_apply, Nat.factorization_pow, Finsupp.smul_apply,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 7 ∣ 2),
    Nat.Prime.factorization_self (by decide : Nat.Prime 7)]
  simp

theorem eq_top_of_dvd_card {D : Type*} [Group D] [Finite D] (hD : Nat.card D = 6048)
    (hs : IsSimpleGroup D)
    (hN : ∀ Q : Sylow 7 D, Nat.card (Subgroup.normalizer ((Q : Subgroup D) : Set D)) = 21)
    (H : Subgroup D) (h224 : 224 ∣ Nat.card H) : H = ⊤ := by
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨m, hm⟩ := h224
  have hm27 : m ∣ 27 := by
    have h1 := Subgroup.card_subgroup_dvd_card H
    rw [hm, hD, show (6048 : ℕ) = 224 * 27 by norm_num] at h1
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h1
  have hm0 : m ≠ 0 := by rintro rfl; norm_num at hm27
  let Q : Sylow 7 H := default
  have hQcard : Nat.card (Q : Subgroup H) = 7 := by
    rw [Q.card_eq_multiplicity, hm, factorization_seven hm27, pow_one]
  have hQD : Nat.card ((Q : Subgroup H).map H.subtype) = 7 := by
    rw [Nat.card_congr ((Q : Subgroup H).equivMapOfInjective H.subtype
      H.subtype_injective).toEquiv.symm, hQcard]
  let Q' : Sylow 7 D := Sylow.ofCard ((Q : Subgroup H).map H.subtype) (by
    rw [hQD, hD, show (6048 : ℕ) = 864 * 7 by norm_num, Nat.factorization_mul (by norm_num)
      (by norm_num), Finsupp.add_apply, Nat.Prime.factorization_self (by decide : Nat.Prime 7),
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 7 ∣ 864)]; norm_num)
  have hQ' : (Q' : Subgroup D) = (Q : Subgroup H).map H.subtype := Sylow.coe_ofCard _ _
  set NH := Subgroup.normalizer ((Q : Subgroup H) : Set H) with hNH
  have hNmap : NH.map H.subtype ≤ Subgroup.normalizer ((Q' : Subgroup D) : Set D) := by
    rintro _ ⟨n, hn0, rfl⟩
    have hn : n ∈ NH := hn0
    rw [hNH, Subgroup.mem_normalizer_iff] at hn
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [hQ']
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨n * q * n⁻¹, (hn q).mp hq, by simp⟩
    · rintro ⟨q, hq, hqx⟩
      simp only [Subgroup.coe_subtype] at hqx
      have hx : x ∈ H := by
        have h1 : (n : D)⁻¹ * (n * x * (n : D)⁻¹) * n ∈ H := by
          rw [← hqx]
          exact H.mul_mem (H.mul_mem (H.inv_mem n.2) q.2) n.2
        simpa [mul_assoc] using h1
      refine ⟨⟨x, hx⟩, (hn ⟨x, hx⟩).mpr ?_, rfl⟩
      have : (n * ⟨x, hx⟩ * n⁻¹ : H) = q := Subtype.ext (by simp [hqx])
      rw [this]
      exact hq
  have hN21 : Nat.card NH ∣ 21 := by
    have h1 := Subgroup.card_dvd_of_le hNmap
    rw [hN Q', Nat.card_congr (NH.equivMapOfInjective H.subtype
      H.subtype_injective).toEquiv.symm] at h1
    exact h1
  have hN7 : 7 ∣ Nat.card NH := by
    have := Subgroup.card_dvd_of_le (Subgroup.le_normalizer (H := (Q : Subgroup H)))
    rwa [hQcard] at this
  have hmod : NH.index ≡ 1 [MOD 7] := by
    have h1 := card_sylow_modEq_one 7 H
    rw [Sylow.card_eq_index_normalizer Q] at h1
    exact h1
  have hmul := Subgroup.card_mul_index NH
  rw [hm] at hmul
  have hN721 : Nat.card NH = 7 ∨ Nat.card NH = 21 := by
    have h1 : Nat.card NH ∈ Nat.divisors 21 := Nat.mem_divisors.mpr ⟨hN21, by norm_num⟩
    rw [show Nat.divisors 21 = {1, 3, 7, 21} by decide] at h1
    simp only [Finset.mem_insert, Finset.mem_singleton] at h1
    rcases h1 with h | h | h | h
    · rw [h] at hN7; norm_num at hN7
    · rw [h] at hN7; norm_num at hN7
    · exact Or.inl h
    · exact Or.inr h
  have hm' : m = 1 ∨ m = 3 ∨ m = 9 ∨ m = 27 := by
    have h1 : m ∈ Nat.divisors 27 := Nat.mem_divisors.mpr ⟨hm27, by norm_num⟩
    rw [show Nat.divisors 27 = {1, 3, 9, 27} by decide] at h1
    simpa using h1
  have hidx : (Nat.card NH = 7 ∧ m = 9 ∧ NH.index = 288) ∨ m = 27 := by
    unfold Nat.ModEq at hmod
    rcases hN721 with h | h <;> rcases hm' with rfl | rfl | rfl | rfl <;> rw [h] at hmul <;>
      first | exact Or.inr rfl | (left; refine ⟨h, rfl, ?_⟩; omega) | (exfalso; omega)
  rcases hidx with ⟨-, rfl, hidx288⟩ | rfl
  ·
    have hcard7 : ∀ R : Sylow 7 H, Nat.card ((R : Subgroup H).map H.subtype) =
        7 ^ (Nat.card D).factorization 7 := by
      intro R
      rw [Nat.card_congr ((R : Subgroup H).equivMapOfInjective H.subtype
        H.subtype_injective).toEquiv.symm, R.card_eq_multiplicity, hm, factorization_seven hm27,
        hD, show (6048 : ℕ) = 864 * 7 by norm_num, Nat.factorization_mul (by norm_num)
        (by norm_num), Finsupp.add_apply, Nat.Prime.factorization_self (by decide : Nat.Prime 7),
        Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 7 ∣ 864)]
    let φ : Sylow 7 H → Sylow 7 D := fun R => Sylow.ofCard _ (hcard7 R)
    have hφ : ∀ R, ((φ R : Sylow 7 D) : Subgroup D) = (R : Subgroup H).map H.subtype :=
      fun R => Sylow.coe_ofCard _ _
    have hφinj : Function.Injective φ := by
      intro R₁ R₂ h
      apply Sylow.ext
      apply Subgroup.map_injective H.subtype_injective
      rw [← hφ, ← hφ, h]
    have hnD : Nat.card (Sylow 7 D) = 288 := by
      have h1 := Subgroup.card_mul_index (Subgroup.normalizer ((Q' : Subgroup D) : Set D))
      have h2 : Nat.card (Sylow 7 D) =
          (Subgroup.normalizer ((Q' : Subgroup D) : Set D)).index :=
        Sylow.card_eq_index_normalizer Q'
      rw [hN Q', hD] at h1
      rw [h2]
      omega
    have hnH : Nat.card (Sylow 7 H) = 288 := by
      have h2 : Nat.card (Sylow 7 H) = NH.index := Sylow.card_eq_index_normalizer Q
      rw [h2]
      exact hidx288
    have hφsurj : Function.Surjective φ :=
      (hφinj.bijective_of_nat_card_le (by rw [hnD, hnH])).2
    have hcl : Subgroup.normalClosure ((Q' : Subgroup D) : Set D) ≤ H := by
      rw [Subgroup.normalClosure, Subgroup.closure_le]
      intro x hx
      obtain ⟨a, ha, hax⟩ := Group.mem_conjugatesOfSet_iff.mp hx
      obtain ⟨c, rfl⟩ := isConj_iff.mp hax
      obtain ⟨R, hR⟩ := hφsurj (c • Q')
      have h1 : c * a * c⁻¹ ∈ ((c • Q' : Sylow 7 D) : Subgroup D) := by
        rw [Sylow.coe_subgroup_smul]
        exact Subgroup.smul_mem_pointwise_smul _ (MulAut.conj c) _ ha
      rw [← hR, hφ] at h1
      obtain ⟨r, -, hr⟩ := h1
      rw [← hr]
      exact r.2
    have hnorm : (Subgroup.normalClosure ((Q' : Subgroup D) : Set D)).Normal :=
      Subgroup.normalClosure_normal
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.normalClosure ((Q' : Subgroup D) : Set D)) with hb | ht
    · exfalso
      have hle : (Q' : Subgroup D) ≤ ⊥ := hb ▸ Subgroup.subset_normalClosure
      have h1 := Subgroup.card_le_of_le hle
      rw [Subgroup.card_bot, hQ', hQD] at h1
      omega
    · exact eq_top_iff.mpr (ht ▸ hcl)
  · exact Subgroup.eq_top_of_card_eq H (by rw [hm, hD])


section Model

open CFSG.GH74.KGroups CFSG.GH74.KGroups.U33 CFSG.Sporadic.Schreier

private theorem card_subgroup_eq_length' {S : Type*} [Group S] {E : Subgroup S} {El : List S}
    (hEl : ∀ x, x ∈ E ↔ x ∈ El) (hnd : El.Nodup) : Nat.card E = El.length := by
  classical
  have hset : (E : Set S) = ↑El.toFinset := by
    ext x
    simp [hEl x]
  have : Nat.card E = (E : Set S).ncard := Nat.card_coe_set_eq _
  rw [this, hset, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd]

theorem y7_mem : pa * pb ∈ QP.originalSubgroup := by
  rw [QP_closure]
  exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))

theorem mem_normalizer_zpowers_iff {G : Type*} [Group G] [Finite G] {y g : G} :
    g ∈ Subgroup.normalizer ((Subgroup.zpowers y : Subgroup G) : Set G) ↔
      g * y * g⁻¹ ∈ Subgroup.zpowers y := by
  constructor
  · intro hg
    exact (Subgroup.mem_normalizer_iff.mp hg y).mp (Subgroup.mem_zpowers y)
  · intro hg
    have hle : (Subgroup.zpowers y).map (MulAut.conj g).toMonoidHom ≤ Subgroup.zpowers y := by
      rw [MonoidHom.map_zpowers]
      exact Subgroup.zpowers_le.mpr hg
    have heq : (Subgroup.zpowers y).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers y :=
      Subgroup.eq_of_le_of_card_ge hle (by
        rw [Nat.card_congr ((Subgroup.zpowers y).equivMapOfInjective _
          (MulAut.conj g).injective).toEquiv.symm])
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact hle ⟨h, hh, rfl⟩
    · intro hh
      rw [← heq] at hh
      obtain ⟨h', hh', hhh⟩ := hh
      have : h' = h := by
        have := hhh
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
        exact mul_left_cancel (mul_right_cancel this)
      rw [← this]
      exact hh'

theorem card_normalizer_y7 :
    Nat.card (Subgroup.normalizer ((Subgroup.zpowers (⟨pa * pb, y7_mem⟩ : ↥QP.originalSubgroup) :
      Subgroup ↥QP.originalSubgroup) : Set ↥QP.originalSubgroup)) = 21 := by
  obtain ⟨h7, h1, hc⟩ := Certificates.certificate7137
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  set y : ↥QP.originalSubgroup := ⟨pa * pb, y7_mem⟩ with hy
  have hyv : (y : Equiv.Perm (Fin 28)) = pa * pb := rfl
  have hy7 : orderOf y = 7 := by
    refine orderOf_eq_prime (Subtype.ext ?_) (fun h => h1 ?_)
    · rw [Subgroup.coe_pow, hyv, h7, OneMemClass.coe_one]
    · rw [← hyv, h, OneMemClass.coe_one]
  set N := Subgroup.normalizer ((Subgroup.zpowers y : Subgroup ↥QP.originalSubgroup) :
    Set ↥QP.originalSubgroup) with hN
  have hmem : ∀ x : Equiv.Perm (Fin 28), x ∈ N.map QP.originalSubgroup.subtype ↔
      x ∈ (elemsT QP).filter fun g =>
        (List.range 7).any fun i => decide (g * (pa * pb) * g⁻¹ = (pa * pb) ^ i) := by
    intro x
    rw [List.mem_filter, mem_elemsT QP QP_ok]
    constructor
    · rintro ⟨g, hg0, rfl⟩
      have hg : g ∈ N := hg0
      refine ⟨g.2, ?_⟩
      rw [hN] at hg
      have h2 := (mem_normalizer_zpowers_iff.mp hg)
      rw [mem_zpowers_iff_mem_range_orderOf, hy7] at h2
      obtain ⟨i, hi, hgi⟩ := Finset.mem_image.mp h2
      rw [List.any_eq_true]
      refine ⟨i, List.mem_range.mpr (Finset.mem_range.mp hi), ?_⟩
      rw [decide_eq_true_eq]
      have := congrArg Subtype.val hgi
      simp only [Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_inv, hyv] at this
      exact this.symm
    · rintro ⟨hx, hany⟩
      refine ⟨⟨x, hx⟩, ?_, rfl⟩
      show (⟨x, hx⟩ : ↥QP.originalSubgroup) ∈ N
      rw [hN, mem_normalizer_zpowers_iff, mem_zpowers_iff_mem_range_orderOf, hy7]
      rw [List.any_eq_true] at hany
      obtain ⟨i, hi, hgi⟩ := hany
      rw [decide_eq_true_eq] at hgi
      refine Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (List.mem_range.mp hi), ?_⟩
      apply Subtype.ext
      simp only [Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_inv, hyv]
      exact hgi.symm
  have hcard := card_subgroup_eq_length' hmem
    ((nodup_elemsT QP QP_ok).filter _)
  rw [hc] at hcard
  rw [← hcard, Nat.card_congr (N.equivMapOfInjective _
    QP.originalSubgroup.subtype_injective).toEquiv]

theorem card_normalizer_sylow_seven
    {D : Type*} [Group D] [Finite D] (e : D ≃* ↥QP.originalSubgroup) (Q : Sylow 7 D) :
    Nat.card (Subgroup.normalizer ((Q : Subgroup D) : Set D)) = 21 := by
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hDcard : Nat.card D = 6048 := by
    rw [Nat.card_congr e.toEquiv, card_group QP QP_ok, QP_valid.2]
  set y : ↥QP.originalSubgroup := ⟨pa * pb, y7_mem⟩ with hy
  let Q₀ : Subgroup D := Subgroup.zpowers (e.symm y)
  have hQ₀map : Q₀.map e.toMonoidHom = Subgroup.zpowers y := by
    rw [MonoidHom.map_zpowers]
    simp
  have hN₀ : Nat.card (Subgroup.normalizer (Q₀ : Set D)) = 21 := by
    rw [Nat.card_congr ((Subgroup.normalizer (Q₀ : Set D)).equivMapOfInjective e.toMonoidHom
      e.injective).toEquiv, Subgroup.map_equiv_normalizer_eq, hQ₀map]
    exact card_normalizer_y7
  have hQ₀card : Nat.card Q₀ = 7 := by
    rw [Nat.card_congr (Q₀.equivMapOfInjective e.toMonoidHom e.injective).toEquiv, hQ₀map,
      Nat.card_zpowers]
    obtain ⟨h7, h1, -⟩ := Certificates.certificate7137
    have hyv : (y : Equiv.Perm (Fin 28)) = pa * pb := rfl
    refine orderOf_eq_prime (Subtype.ext ?_) (fun h => h1 ?_)
    · rw [Subgroup.coe_pow, hyv, h7, OneMemClass.coe_one]
    · rw [← hyv, h, OneMemClass.coe_one]
  let P₀ : Sylow 7 D := Sylow.ofCard Q₀ (by
    rw [hQ₀card, hDcard, show (6048 : ℕ) = 864 * 7 by norm_num, Nat.factorization_mul (by norm_num)
      (by norm_num), Finsupp.add_apply, Nat.Prime.factorization_self (by decide : Nat.Prime 7),
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 7 ∣ 864)]; norm_num)
  have hP₀ : (P₀ : Subgroup D) = Q₀ := Sylow.coe_ofCard _ _
  have h1 : (Subgroup.normalizer ((Q : Subgroup D) : Set D)).index =
      (Subgroup.normalizer ((P₀ : Subgroup D) : Set D)).index := by
    have e1 : Nat.card (Sylow 7 D) = (Subgroup.normalizer ((Q : Subgroup D) : Set D)).index :=
      Sylow.card_eq_index_normalizer Q
    have e2 : Nat.card (Sylow 7 D) = (Subgroup.normalizer ((P₀ : Subgroup D) : Set D)).index :=
      Sylow.card_eq_index_normalizer P₀
    rw [← e1, ← e2]
  have hm1 := Subgroup.card_mul_index (Subgroup.normalizer ((Q : Subgroup D) : Set D))
  have hm2 := Subgroup.card_mul_index (Subgroup.normalizer ((P₀ : Subgroup D) : Set D))
  rw [hP₀, hN₀] at hm2
  rw [hP₀] at h1
  rw [h1, hDcard] at hm1
  rw [hDcard] at hm2
  have hidx : (Subgroup.normalizer (Q₀ : Set D)).index = 288 := by omega
  rw [hidx] at hm1
  omega

end Model

theorem card_subgroupOf_eq {G : Type*} [Group G] (H K : Subgroup G) :
    Nat.card (H.subgroupOf K) = Nat.card ↥(H ⊓ K) := by
  rw [← Subgroup.inf_subgroupOf_right,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : H ⊓ K ≤ K)).toEquiv]

theorem lem1211NNG2_holds :
    CFSG.Quasithin.H13.Lem1211NNG2 := by
  intro Y _ _ X P hX hP h7
  obtain ⟨hXcard, -, D, hDn, hDidx, hDpsu⟩ := hX
  obtain ⟨e⟩ := CFSG.GH74.KGroups.U33.equiv_of_lieModel (K := ↥D) (Or.inl ⟨by decide, hDpsu⟩)
  have hDcard : Nat.card D = 6048 := CFSG.Quasithin.SBc11.card_of_isPSU_three_three hDpsu
  have hDs : IsSimpleGroup D :=
    CFSG.Quasithin.SBc11.isSimpleGroup_of_list (Or.inr (Or.inr hDpsu))
  obtain ⟨⟨hPX, S, hS, hNS⟩, hPne, -⟩ := hP
  have hSP : S ≤ P := fun s hs => hNS (Subgroup.mem_inf.mpr ⟨hS.1 hs, Subgroup.le_normalizer hs⟩)
  have hScard : Nat.card S = 64 := by
    rw [CFSG.QuasithinUnique.IsSylowTwoOf.card_eq hS, CFSG.QuasithinUnique.twoPart, hXcard,
      show (12096 : ℕ) = 2 ^ 6 * 189 by norm_num, Nat.factorization_mul (by norm_num)
      (by norm_num), Finsupp.add_apply, Nat.factorization_pow, Finsupp.smul_apply,
      Nat.Prime.factorization_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 189)]
    norm_num
  set P' : Subgroup ↥X := P.subgroupOf X with hP'
  set S' : Subgroup ↥X := S.subgroupOf X with hS'
  have hP'card : Nat.card P' = Nat.card P :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPX).toEquiv
  have hS'card : Nat.card S' = 64 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS.1).toEquiv, hScard]
  have hS'P' : S' ≤ P' := fun x hx => (hSP hx : (x : Y) ∈ P)
  have h64 : 64 ∣ Nat.card P' := hS'card ▸ Subgroup.card_dvd_of_le hS'P'
  have h7' : 7 ∣ Nat.card P' := hP'card ▸ h7
  have hPD : ¬ P' ≤ D := by
    intro h
    have := Subgroup.card_dvd_of_le (hS'P'.trans h)
    rw [hS'card, hDcard] at this
    norm_num at this
  have hrel : D.relIndex P' = 2 := by
    have h1 : D.relIndex P' ∣ 2 := hDidx ▸ Subgroup.relIndex_dvd_index_of_normal D P'
    rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h | h
    · exact absurd (Subgroup.relIndex_eq_one.mp h) hPD
    · exact h
  have hmul : Nat.card ↥(D ⊓ P') * 2 = Nat.card P' := by
    have := Subgroup.card_mul_index (D.subgroupOf P')
    rw [card_subgroupOf_eq] at this
    rw [show (D.subgroupOf P').index = D.relIndex P' from rfl, hrel] at this
    exact this
  have hH : 224 ∣ Nat.card (P'.subgroupOf D) := by
    rw [card_subgroupOf_eq, inf_comm]
    have h448 : 64 * 7 ∣ Nat.card P' :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h64 h7'
    rw [show (64 : ℕ) * 7 = 224 * 2 by norm_num] at h448
    rw [← hmul] at h448
    exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) h448
  have hHtop := eq_top_of_dvd_card hDcard hDs (card_normalizer_sylow_seven e) _ hH
  have hDP : D ≤ P' := by
    intro d hd
    have : (⟨d, hd⟩ : ↥D) ∈ P'.subgroupOf D := hHtop ▸ Subgroup.mem_top _
    exact this
  have hP'top : P' = ⊤ := by
    have h1 : Nat.card ↥(D ⊓ P') = 6048 := by rw [inf_eq_left.mpr hDP, hDcard]
    have h2 : Nat.card P' = 12096 := by rw [← hmul, h1]
    exact Subgroup.eq_top_of_card_eq P' (by rw [h2, hXcard])
  apply hPne
  apply le_antisymm hPX
  intro x hx
  have : (⟨x, hx⟩ : ↥X) ∈ P' := hP'top ▸ Subgroup.mem_top _
  exact this

end CFSG.Quasithin.H13.KGG2
