module

public import CFSG.OddTranspositions.FourEightBase
public import CFSG.OddTranspositions.G2aCertificate

public section

namespace CFSG.OddTranspositions.QZ

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge
open CFSG.Timmesfeld.Bridge.Asc72
open CFSG.EvenSporadicStandard.HSStd.InvCent.Harada commutatorElement Equiv
open Config

variable {G : Type} [Group G] [Finite G]

theorem relIndex_centralizer_le_two {X A : Subgroup G} (e : X ≃* alternatingGroup (Fin 5))
    (hAX : A ≤ Subgroup.normalizer (X : Set G)) {x y : G} (hx : x ∈ X) (hy : y ∈ X) (hx2 : orderOf x = 2)
    (hy2 : orderOf y = 2) (hxy : orderOf (x * y) = 3)
    (hAx : A ≤ Subgroup.centralizer ({x, y} : Set G)) :
    (A ⊓ Subgroup.centralizer (X : Set G)).relIndex A ≤ 2 := by
  classical
  set x' : X := ⟨x, hx⟩
  set y' : X := ⟨y, hy⟩
  let φ : A →* MulAut X := X.normalizerMonoidHom.comp (Subgroup.inclusion hAX)
  have hker : φ.ker = (A ⊓ Subgroup.centralizer (X : Set G)).subgroupOf A := by
    ext a
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf, SetLike.coe_mem,
      true_and, Subgroup.mem_centralizer_iff, MulEquiv.ext_iff, MulAut.one_apply, Subtype.ext_iff,
      φ, MonoidHom.comp_apply, Subgroup.normalizerMonoidHom_apply_apply_coe]
    constructor
    · intro h h' hh'
      have := h ⟨h', hh'⟩
      simp only [Subgroup.coe_inclusion] at this
      exact (mul_inv_eq_iff_eq_mul.mp this).symm
    · intro h h'
      simp only [Subgroup.coe_inclusion]
      rw [← h h' h'.2]; group
  let T := {τ : MulAut (alternatingGroup (Fin 5)) // τ (e x') = e x' ∧ τ (e y') = e y'}
  have hT : Nat.card T ≤ 2 := by
    apply card_aut_fix_S3_le_two
    · rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]; exact hx2
    · rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]; exact hy2
    · rw [← map_mul, MulEquiv.orderOf_eq]
      change orderOf (⟨x * y, X.mul_mem hx hy⟩ : X) = 3
      rw [Subgroup.orderOf_mk]; exact hxy
  let F : φ.range → T := fun σ => ⟨(e.symm.trans σ.1).trans e, by
    obtain ⟨a, ha⟩ := σ.2
    have hfix : ∀ g ∈ ({x, y} : Set G), ∀ (hg : g ∈ X), σ.1 ⟨g, hg⟩ = ⟨g, hg⟩ := by
      intro g hg hgX
      rw [← ha]
      apply Subtype.ext
      simp only [φ, MonoidHom.comp_apply, Subgroup.normalizerMonoidHom_apply_apply_coe,
        Subgroup.coe_inclusion]
      have := Subgroup.mem_centralizer_iff.mp (hAx a.2) g hg
      rw [← this]; group
    refine ⟨?_, ?_⟩
    · simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
      rw [hfix x (by simp) hx]
    · simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
      rw [hfix y (by simp) hy]⟩
  have hF : Function.Injective F := by
    intro σ τ h
    apply Subtype.ext
    ext g
    have := congrArg (fun t : T => e.symm (t.1 (e g))) h
    simpa [F] using this
  rw [Subgroup.relIndex, ← hker, Subgroup.index_ker]
  exact (Nat.card_le_card_of_injective F hF).trans hT

theorem card_le_two_of_comm_of_class_gen {Q : Type*} [Group Q] [Finite Q]
    (hcomm : ∀ a b : Q, a * b = b * a) {C : Set Q} (hC : ∃ c, C = {g | IsConj c g})
    (h2 : ∀ c ∈ C, c * c = 1) (hgen : Subgroup.closure C = ⊤) : Nat.card Q ≤ 2 := by
  obtain ⟨c, rfl⟩ := hC
  have hCc : {g | IsConj c g} = ({c} : Set Q) := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, isConj_iff]
    constructor
    · rintro ⟨h, rfl⟩; rw [hcomm h c, mul_assoc, mul_inv_cancel, mul_one]
    · rintro rfl; exact ⟨1, by simp⟩
  have hcc := h2 c (IsConj.refl c)
  rw [hCc, ← Subgroup.zpowers_eq_closure] at hgen
  rw [← Subgroup.card_top, ← hgen, Nat.card_zpowers]
  exact Nat.le_of_dvd two_pos (orderOf_dvd_of_pow_eq_one (by rw [pow_two, hcc]))

theorem quotient_comm_of_L225 {Y : Type} [Group Y] [Finite Y] (M : Subgroup Y) [M.Normal]
    (hC : Subgroup.centralizer (M : Set Y) = ⊥)
    (hM : CFSG.Blueprint.LieModel M .PSL 2 5 2) :
    ∀ a b : Y ⧸ M, a * b = b * a := by
  have hle : commutator Y ≤ M := commutator_le_of_card_outer_dvd_four hC (card_outer_L225 hM)
  rintro ⟨a⟩ ⟨b⟩
  change (a : Y ⧸ M) * b = b * a
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
  have h : ⁅b⁻¹, a⁻¹⁆ ∈ commutator Y := by
    rw [commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  convert hle h using 1
  simp only [commutatorElement_def]; group

theorem exists_mem_not_mem_commute_of_not_isConj {P B : Subgroup G} {z a : G}
    (hP : IsPGroup 2 P) (hBP : B ≤ P) (hBn : (B.subgroupOf P).Normal) (hzc : ∀ x ∈ P, Commute x z)
    (hz2 : z * z = 1) (hzB : Subgroup.zpowers z < B) (ha : a ∈ P) (hconj : ¬ IsConj a (a * z)) :
    ∃ e ∈ B, e ∉ Subgroup.zpowers z ∧ Commute e a := by
  have hZn : ((Subgroup.zpowers z).subgroupOf P).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hn
    have : (g : G) * n * (g : G)⁻¹ = n := by
      rw [← hk, ((hzc g g.2).zpow_right k).eq, mul_inv_cancel_right]
    simpa [this] using hn
  obtain ⟨e, heB, hez, hcomm⟩ := exists_mem_not_mem_comm_mem hP hBP hBn hZn hzB
  refine ⟨e, heB, hez, ?_⟩
  rcases eq_one_or_eq_of_mem_zpowers hz2 (hcomm a ha) with h | h
  · have : a * e = e * a := by
      have := congrArg (· * e * a) h
      simpa [mul_assoc] using this
    exact this.symm
  · exfalso
    apply hconj
    rw [isConj_iff]
    refine ⟨e, ?_⟩
    have hz' : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
    have h2 : e * a * e⁻¹ * a⁻¹ = z := by
      rw [← hz', ← h]; group
    calc e * a * e⁻¹ = (e * a * e⁻¹ * a⁻¹) * a := by group
      _ = a * z := by rw [h2]; exact ((hzc a ha).eq).symm

theorem exists_inv_mem_centralizer {A X : Subgroup G} (e : X ≃* alternatingGroup (Fin 5))
    (hA : IsPGroup 2 A) (hAX : A ≤ Subgroup.normalizer (X : Set G)) {x y z : G} (hx : x ∈ X)
    (hy : y ∈ X) (hx2 : orderOf x = 2) (hy2 : orderOf y = 2) (hxy : orderOf (x * y) = 3)
    (hAx : A ≤ Subgroup.centralizer ({x, y} : Set G)) (hz2 : orderOf z = 2)
    (hzA : Subgroup.zpowers z < A) (hzX : z ∉ Subgroup.centralizer (X : Set G)) :
    ∃ t ∈ A, orderOf t = 2 ∧ t ∉ Subgroup.zpowers z ∧ t ∈ Subgroup.centralizer (X : Set G) := by
  classical
  set A₀ := A ⊓ Subgroup.centralizer (X : Set G)
  have hidx := relIndex_centralizer_le_two e hAX hx hy hx2 hy2 hxy hAx
  have hcard : A₀.relIndex A * Nat.card (A₀ ⊓ A :) = Nat.card A :=
    Subgroup.relIndex_mul_card A₀ A
  have hA₀A : A₀ ⊓ A = A₀ := inf_eq_left.mpr inf_le_left
  rw [hA₀A] at hcard
  have hzcard : Nat.card (Subgroup.zpowers z) = 2 := by rw [Nat.card_zpowers, hz2]
  have hlt : 2 < Nat.card A := hzcard ▸ Subgroup.card_lt_of_lt hzA
  have hA₀ : Nat.card A₀ ≠ 1 := by
    intro h1; rw [h1, mul_one] at hcard
    have h3 : Nat.card A ≤ 2 := by rw [← hcard]; exact hidx
    omega
  have hA₀p : IsPGroup 2 A₀ := hA.to_le inf_le_left
  have h2 : 2 ∣ Nat.card A₀ := hA₀p.card_eq_or_dvd.resolve_left hA₀
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have ht2 : orderOf (t : G) = 2 := by rwa [Subgroup.orderOf_coe]
  refine ⟨t, t.2.1, ht2, fun htz => ?_, t.2.2⟩
  have hz1 : z * z = 1 := by rw [← sq, ← hz2, pow_orderOf_eq_one]
  rcases eq_one_or_eq_of_mem_zpowers hz1 htz with h | h
  · rw [h, orderOf_one] at ht2; norm_num at ht2
  · exact hzX (h ▸ t.2.2)

namespace Config

variable {D : Set G} {u w v z a : G} {K₁ S' : Subgroup G}

theorem exists_inv_centralizing_core {S' K X₁ : Subgroup G} {z a u₁ u₂ : G}
    (hP : IsPGroup 2 S') (hBn : ((S' ⊓ Subgroup.centralizer (K : Set G)).subgroupOf S').Normal)
    (hzc : ∀ s ∈ S', Commute s z) (hzS : z ∈ S') (hz2 : orderOf z = 2)
    (hzK : z ∈ Subgroup.centralizer (K : Set G)) (ha : a ∈ S') (hconj : ¬ IsConj a (a * z))
    (hB : Subgroup.zpowers z < S' ⊓ Subgroup.centralizer (K : Set G))
    (e₁ : X₁ ≃* alternatingGroup (Fin 5))
    (hnorm : S' ⊓ Subgroup.centralizer (K : Set G) ⊓ Subgroup.centralizer ({a} : Set G) ≤
      Subgroup.normalizer (X₁ : Set G))
    (hzX : z ∉ Subgroup.centralizer (X₁ : Set G)) (hu₁ : u₁ ∈ K) (hu₂ : u₂ ∈ K)
    (hx : a * u₁ ∈ X₁) (hy : a * u₂ ∈ X₁) (hx2 : orderOf (a * u₁) = 2)
    (hy2 : orderOf (a * u₂) = 2) (hxy : orderOf (a * u₁ * (a * u₂)) = 3) :
    ∃ t : G, orderOf t = 2 ∧ t ∉ Subgroup.zpowers z ∧ t ∈ Subgroup.centralizer (K : Set G) ∧
      Commute t a ∧ t ∈ Subgroup.centralizer (X₁ : Set G) := by
  have hz1 : z * z = 1 := by rw [← sq, ← hz2, pow_orderOf_eq_one]
  obtain ⟨e, heB, hez, hea⟩ := exists_mem_not_mem_commute_of_not_isConj hP inf_le_left hBn hzc
    hz1 hB ha hconj
  set A := S' ⊓ Subgroup.centralizer (K : Set G) ⊓ Subgroup.centralizer ({a} : Set G)
  have hmemA : ∀ s, s ∈ S' ⊓ Subgroup.centralizer (K : Set G) → Commute s a → s ∈ A := by
    intro s hs hsa
    refine ⟨hs, Subgroup.mem_centralizer_singleton_iff.mpr hsa.eq⟩
  have hzA : Subgroup.zpowers z < A := by
    refine lt_of_le_of_ne ((Subgroup.zpowers_le).mpr
      (hmemA z ⟨hzS, hzK⟩ (hzc a ha).symm)) fun h => hez ?_
    exact h ▸ hmemA e heB hea
  have hAc : A ≤ Subgroup.centralizer ({a * u₁, a * u₂} : Set G) := by
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    have hsa : s * a = a * s := Subgroup.mem_centralizer_singleton_iff.mp hs.2
    have hsK := Subgroup.mem_centralizer_iff.mp hs.1.2
    rintro g (rfl | rfl)
    · rw [mul_assoc, hsK u₁ hu₁, ← mul_assoc, ← hsa, mul_assoc]
    · rw [mul_assoc, hsK u₂ hu₂, ← mul_assoc, ← hsa, mul_assoc]
  obtain ⟨t, htA, ht2, htz, htX⟩ := exists_inv_mem_centralizer e₁ (hP.to_le (inf_le_left.trans
    inf_le_left)) hnorm hx hy hx2 hy2 hxy hAc hz2 hzA hzX
  refine ⟨t, ht2, htz, htA.1.2, ?_, htX⟩
  exact Subgroup.mem_centralizer_singleton_iff.mp htA.2


theorem exists_inv_centralizing (hQ : Config D u w v z a K₁ S')
    (hB : Subgroup.zpowers z < S' ⊓ Subgroup.centralizer (thirdK D z : Set G)) :
    ∃ e : G, orderOf e = 2 ∧ e ∉ Subgroup.zpowers z ∧
      thirdK D z ≤ Subgroup.centralizer ({e} : Set G) ∧
      thirdK D a ≤ Subgroup.centralizer ({e} : Set G) := by
  obtain ⟨hz1', hz1, huΔ, -, -, hzD⟩ := hQ.z_facts
  obtain ⟨X₁, ⟨eX⟩, hX, hXa, hda, hcard⟩ := hQ.conj_data
  obtain ⟨u', hu'Δ, hu'a, hord⟩ := hQ.u_pair
  obtain ⟨g, hg⟩ := isConj_iff.mp hQ.a_conj
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [sq]; exact hz1') hz1
  have hzc : ∀ s ∈ S', Commute s z := fun s hs =>
    Subgroup.mem_centralizer_singleton_iff.mp (hQ.z_central.2 hs)
  have hzX := hQ.z_not_mem_centralizer hX hcard
  have ha2 : a * a = 1 := by
    rw [← hg]; calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [hz1']; group
  have haD : a ∉ D := fun haD => hzD (by
    have := hQ.setup.normal g⁻¹ a haD
    rwa [← hg, show g⁻¹ * (g * z * g⁻¹) * g⁻¹⁻¹ = z by group] at this)
  have hua : Commute u a := hQ.a_comm_u.symm
  have hmemΔa : ∀ t ∈ Delta D z, Commute t a → t ∈ Delta D a := fun t ht hta =>
    mem_Delta_iff.mpr ⟨(mem_Delta_iff.mp ht).1, hta⟩
  have hord2 : ∀ t ∈ Delta D z, Commute t a → orderOf (a * t) = 2 := by
    intro t ht hta
    have ht2 : t * t = 1 := hQ.setup.oddT.mul_self_eq_one (mem_Delta_iff.mp ht).1
    refine orderOf_eq_prime ?_ ?_
    · have hre : a * t * (a * t) = (a * a) * (t * t) := by
        rw [mul_assoc a t, ← mul_assoc t a t, hta.eq]; group
      rw [sq, hre, ha2, ht2, one_mul]
    · intro h
      apply haD
      have : a = t⁻¹ := eq_inv_of_mul_eq_one_left h
      rw [this, inv_eq_of_mul_eq_one_right ht2]
      exact (mem_Delta_iff.mp ht).1
  have hxy : orderOf (a * u * (a * u')) = 3 := by
    rw [show a * u * (a * u') = u * u' by
      calc a * u * (a * u') = a * (u * a) * u' := by group
        _ = a * (a * u) * u' := by rw [hua.eq]
        _ = (a * a) * (u * u') := by group
        _ = u * u' := by rw [ha2, one_mul]]
    exact hord
  have hnorm : S' ⊓ Subgroup.centralizer (thirdK D z : Set G) ⊓
      Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (X₁ : Set G) := by
    intro s hs
    have hsa : Commute s a := Subgroup.mem_centralizer_singleton_iff.mp hs.2
    have key : ∀ r : G, Commute r a → ∀ x ∈ X₁, r * x * r⁻¹ ∈ X₁ := fun r hra =>
      conj_mem_of_conj_mem_sup eX hXa fun t ht => by
        rw [← hX] at ht ⊢; exact conj_mem_thirdK_of_commute hQ.setup.normal hra ht
    exact mem_normalizer_of_conj (key s hsa) (key s⁻¹ hsa.inv_left)
  have hzK : z ∈ Subgroup.centralizer (thirdK D z : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact Subgroup.mem_centralizer_singleton_iff.mp (thirdK_le_centralizer hh)
  obtain ⟨t, ht2, htz, htK, hta, htX⟩ := exists_inv_centralizing_core hQ.sylow.1
    (normal_centralizer_thirdK hQ.setup.normal hzc) hzc hQ.z_central.1 hz2 hzK hQ.a_mem
    hQ.az_not_conj hB eX hnorm hzX (Delta_subset_thirdK huΔ) (Delta_subset_thirdK hu'Δ)
    (hda u (hmemΔa u huΔ hua)) (hda u' (hmemΔa u' hu'Δ hu'a)) (hord2 u huΔ hua)
    (hord2 u' hu'Δ hu'a) hxy
  refine ⟨t, ht2, htz, fun k hk => ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp htK k hk
  · rw [hX]
    refine sup_le (fun x hx => ?_) ((Subgroup.zpowers_le).mpr
      (Subgroup.mem_centralizer_singleton_iff.mpr hta.eq.symm))
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp htX x hx


end Config

end CFSG.OddTranspositions.QZ
