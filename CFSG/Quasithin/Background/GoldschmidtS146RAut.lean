module

public import CFSG.Quasithin.Background.GoldschmidtS146RDyn2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113OverSmall
public import CFSG.Quasithin.Background.GoldschmidtS146RArith
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoAllFields
public import CFSG.LocalAnalysis.ComponentInitial.FieldNineAlternatingSix
public import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyBasic

public section

namespace CFSG.Quasithin.GoldS146R

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement

section Aut

variable {G : Type} [Group G] [Finite G] {H J K T : Subgroup G} [(J.subgroupOf H).Normal]

omit [Finite G] in
theorem conj_eq_inner_of_not_outer (hKH : K ≤ H) (hTH : T ≤ H) (hOJ : pCoreOf 2 K ≤ J) {t : G}
    (ht : t ∈ T) (hin : ¬ KbarInducesOuter K t) :
    ∃ kb ∈ imgJ H J K, ∀ q ∈ imgJ H J K,
      ((⟨t, hTH ht⟩ : ↥H) : ↥H ⧸ J.subgroupOf H) * q *
        ((⟨t, hTH ht⟩ : ↥H) : ↥H ⧸ J.subgroupOf H)⁻¹ = kb * q * kb⁻¹ := by
  unfold KbarInducesOuter at hin
  push Not at hin
  obtain ⟨k, hk, hcon⟩ := hin
  set Q := ↥H ⧸ J.subgroupOf H with hQ
  let tb : Q := ((⟨t, hTH ht⟩ : ↥H) : Q)
  let kb : Q := ((⟨k, hKH hk⟩ : ↥H) : Q)
  have hC : ∀ q ∈ imgJ H J K, (tb * kb⁻¹) * q = q * (tb * kb⁻¹) := by
    intro q hq
    obtain ⟨x, hx, rfl⟩ := mem_imgJ.mp hq
    have h1 := hcon (x : G) hx
    have h2 : (⁅t * k⁻¹, (x : G)⁆) ∈ J := hOJ h1
    have h3 : ((⟨t, hTH ht⟩ * ⟨k, hKH hk⟩⁻¹ * x * (⟨t, hTH ht⟩ * ⟨k, hKH hk⟩⁻¹)⁻¹ * x⁻¹ : ↥H) :
        Q) = 1 := by
      refine (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr ?_)
      simpa [commutatorElement_def] using h2
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h3
    have h4 := mul_inv_eq_one.mp h3
    have h5 := mul_inv_eq_iff_eq_mul.mp h4
    simpa [tb, kb, mul_assoc] using h5
  have hkbKs : kb ∈ imgJ H J K := mem_imgJ.mpr ⟨⟨k, hKH hk⟩, hk, rfl⟩
  refine ⟨kb, hkbKs, fun q hq => ?_⟩
  have hq' : kb * q * kb⁻¹ ∈ imgJ H J K :=
    (imgJ H J K).mul_mem ((imgJ H J K).mul_mem hkbKs hq) ((imgJ H J K).inv_mem hkbKs)
  have h1 := hC _ hq'
  calc tb * q * tb⁻¹ = ((tb * kb⁻¹) * (kb * q * kb⁻¹)) * (tb * kb⁻¹)⁻¹ := by group
    _ = ((kb * q * kb⁻¹) * (tb * kb⁻¹)) * (tb * kb⁻¹)⁻¹ := by rw [h1]
    _ = kb * q * kb⁻¹ := by group

theorem center_eq_bot_of_card_168 {Z : Type} [Group Z] (hs : IsSimpleGroup Z)
    (hcard : Nat.card Z = 168) : Subgroup.center Z = ⊥ := by
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center Z) with h | h
  · exact h
  · exfalso
    have hfin : Finite Z := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
    have hcomm : ∀ a b : Z, a * b = b * a := fun a b => by
      have : b ∈ Subgroup.center Z := by rw [h]; trivial
      exact (Subgroup.mem_center_iff.mp this) a
    let _ : CommGroup Z := { (inferInstance : Group Z) with mul_comm := hcomm }
    have hp := IsSimpleGroup.prime_card (α := Z)
    rw [hcard] at hp
    exact absurd hp (by norm_num)

theorem autCard_le_of_inner (hKH : K ≤ H) (hTH : T ≤ H) (hHK : H ≤ Subgroup.normalizer (K : Set G))
    (hOJ : pCoreOf 2 K ≤ J) (hT2 : IsPGroup 2 T) (hsimple : IsSimpleGroup ↥(imgJ H J K))
    (hcard : Nat.card ↥(imgJ H J K) = 168) (hin : ∀ t ∈ T, ¬ KbarInducesOuter K t) :
    E2.autCard (imgJ H J T) (imgJ H J K) ≤ 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKnorm : (K.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr hHK
  have hKsN : (imgJ H J K).Normal := normal_imgJ hKnorm
  let ρ : ↥(imgJ H J T) →* MulAut ↥(imgJ H J K) :=
    (MulAut.conjNormal (H := imgJ H J K)).comp (imgJ H J T).subtype
  have hnormTs : imgJ H J T ≤ Subgroup.normalizer ((imgJ H J K : Subgroup (↥H ⧸ J.subgroupOf H)) :
      Set (↥H ⧸ J.subgroupOf H)) := by
    intro a _
    rw [Subgroup.normalizer_eq_top_iff.mpr hKsN]
    trivial
  have hkernel : ρ.ker = (imgJ H J T ⊓ Subgroup.centralizer
      ((imgJ H J K : Subgroup (↥H ⧸ J.subgroupOf H)) : Set (↥H ⧸ J.subgroupOf H))).subgroupOf
      (imgJ H J T) := by
    ext a
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_iff]
    constructor
    · intro h
      refine ⟨a.2, fun q hq => ?_⟩
      have h1 : ((ρ a) ⟨q, hq⟩ : ↥(imgJ H J K)) = ⟨q, hq⟩ := by rw [h]; rfl
      have h2 : ((a : ↥(imgJ H J T)) : ↥H ⧸ J.subgroupOf H) * q *
          ((a : ↥(imgJ H J T)) : ↥H ⧸ J.subgroupOf H)⁻¹ = q := congrArg Subtype.val h1
      exact (mul_inv_eq_iff_eq_mul.mp h2).symm
    · rintro ⟨-, h⟩
      refine MulEquiv.ext fun q => Subtype.ext ?_
      show ((a : ↥(imgJ H J T)) : ↥H ⧸ J.subgroupOf H) * q *
        ((a : ↥(imgJ H J T)) : ↥H ⧸ J.subgroupOf H)⁻¹ = q
      exact mul_inv_eq_iff_eq_mul.mpr (h q q.2).symm
  have hauteq : E2.autCard (imgJ H J T) (imgJ H J K) = Nat.card ↥ρ.range := by
    unfold E2.autCard
    rw [inf_of_le_left hnormTs]
    show ((_ : Subgroup (↥H ⧸ J.subgroupOf H)).subgroupOf (imgJ H J T)).index = _
    rw [← hkernel]
    exact Subgroup.index_ker ρ
  let ι : ↥(imgJ H J K) →* MulAut ↥(imgJ H J K) := MulAut.conj
  have hrange : ρ.range ≤ ι.range := by
    rintro _ ⟨a, rfl⟩
    obtain ⟨h, hhT, hha⟩ := mem_imgJ.mp a.2
    obtain ⟨kb, hkb, hkbq⟩ := conj_eq_inner_of_not_outer (J := J) hKH hTH hOJ hhT (hin _ hhT)
    refine ⟨⟨kb, hkb⟩, ?_⟩
    refine MulEquiv.ext fun q => Subtype.ext ?_
    show kb * q * kb⁻¹ = ((a : ↥(imgJ H J T)) : ↥H ⧸ J.subgroupOf H) * q *
      ((a : ↥(imgJ H J T)) : ↥H ⧸ J.subgroupOf H)⁻¹
    rw [← hha]
    exact (hkbq q q.2).symm
  have hcenter := center_eq_bot_of_card_168 hsimple hcard
  have hι : Function.Injective ι := by
    intro k k' hkk
    have h1 : ∀ x : ↥(imgJ H J K), k * x * k⁻¹ = k' * x * k'⁻¹ := fun x => by
      have := congrArg (fun f : MulAut ↥(imgJ H J K) => f x) hkk
      simpa [ι, MulAut.conj_apply] using this
    have hz : k'⁻¹ * k ∈ Subgroup.center ↥(imgJ H J K) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h2 : (k'⁻¹ * k) * g * (k'⁻¹ * k)⁻¹ = g := by
        calc (k'⁻¹ * k) * g * (k'⁻¹ * k)⁻¹ = k'⁻¹ * (k * g * k⁻¹) * k' := by group
          _ = k'⁻¹ * (k' * g * k'⁻¹) * k' := by rw [h1 g]
          _ = g := by group
      exact (mul_inv_eq_iff_eq_mul.mp h2).symm
    rw [hcenter, Subgroup.mem_bot] at hz
    exact (inv_mul_eq_one.mp hz).symm
  have hcardι : Nat.card ↥ι.range = 168 := by
    rw [← hcard]
    exact (Nat.card_congr (MonoidHom.ofInjective hι).toEquiv).symm
  have hdvd : Nat.card ↥ρ.range ∣ 168 := hcardι ▸ Subgroup.card_dvd_of_le hrange
  have hTs2 : IsPGroup 2 ↥(imgJ H J T) :=
    IsPGroup.map (hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTH).symm) _
  have hr2 : IsPGroup 2 ↥ρ.range :=
    hTs2.of_surjective ρ.rangeRestrict (MonoidHom.rangeRestrict_surjective ρ)
  obtain ⟨a, ha⟩ := hr2.exists_card_eq
  rw [hauteq, ha]
  rw [ha] at hdvd
  by_contra hgt
  push Not at hgt
  have h4 : 4 ≤ a := by
    by_contra h
    have : a ≤ 3 := by omega
    interval_cases a <;> omega
  have h16 : 2 ^ 4 ∣ 2 ^ a := pow_dvd_pow 2 h4
  have := h16.trans hdvd
  omega


end Aut

section Glue2

variable {G : Type} [Group G] [Finite G] {T M K : Subgroup G}

local notation "Jk" => kerIn ((K ⊔ T) ⊓ M) (K ⊔ T)

theorem outer_of_autCard (c : Ctx146 T M K)
    (hKs : IsPSL 2 7 1 ↥(E2.star ((K ⊔ T) ⊓ M) (K ⊔ T) K))
    (h8 : 8 < E2.autCard (E2.star ((K ⊔ T) ⊓ M) (K ⊔ T) T)
      (E2.star ((K ⊔ T) ⊓ M) (K ⊔ T) K)) :
    (KbarIsL3Two K ∨ KbarIsA6 K) ∧
      ∃ s ∈ T ⊓ Subgroup.normalizer (K : Set G), KbarNontrivialOnDynkin K s := by
  have hKJ := c.inf_kerIn
  have hOJ : pCoreOf 2 K ≤ Jk := by
    rw [← hKJ]
    exact inf_le_right
  obtain ⟨e⟩ := nonempty_kbar_equiv_imgJ (J := Jk) c.le_H hKJ
  have hsimpKs : IsSimpleGroup ↥(imgJ (K ⊔ T) Jk K) := by
    have := c.simple
    exact e.symm.isSimpleGroup
  have hcard' : Nat.card ↥(E2.star ((K ⊔ T) ⊓ M) (K ⊔ T) K) = 168 := by
    have := card_isPSL_two_odd hKs (by norm_num : (7 : ℕ) ≠ 2)
    omega
  have hcard : Nat.card ↥(imgJ (K ⊔ T) Jk K) = 168 := hcard'
  have hL3 : KbarIsL3Two K := by
    obtain ⟨e'⟩ := CFSG.QuasithinUnique.Bridge.Over.nonempty_equiv_sl_three_two_of_model_seven hKs
    exact ⟨e.trans e'⟩
  have hout : ∃ t ∈ T, KbarInducesOuter K t := by
    by_contra hno
    push Not at hno
    have hT2 : IsPGroup 2 T := c.sylow.2.1
    have hHK : K ⊔ T ≤ Subgroup.normalizer (K : Set G) :=
      sup_le Subgroup.le_normalizer c.norm
    have hle := autCard_le_of_inner (J := Jk) c.le_H le_sup_right hHK hOJ hT2 hsimpKs hcard hno
    exact absurd hle (not_le.mpr h8)
  obtain ⟨t, ht, hO⟩ := hout
  exact ⟨Or.inl hL3, t, ⟨ht, c.norm ht⟩, Or.inl ⟨hL3, hO⟩⟩

end Glue2

end CFSG.Quasithin.GoldS146R
