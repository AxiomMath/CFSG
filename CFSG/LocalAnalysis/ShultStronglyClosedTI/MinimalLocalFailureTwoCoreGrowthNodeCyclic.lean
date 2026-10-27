module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAbelianNormalizer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoSemilinear
public import CFSG.CharacterTheory.TwoRankLowerBound.AbelianRankOne

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.LinearChain.TwoCoreGrowthNode

open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {G : Type*} [Group G] [Finite G]

theorem two_subgroup_isCyclic_of_semilinear {B J P : Subgroup G} (hPB : P ≤ B)
    (hP : IsPGroup 2 P) {k₀ : Type*} [Field k₀] [Finite k₀] (hk₀ : Odd (Nat.card k₀ - 1))
    (ι : B →* k₀ˣ ⋊[ringAutUnits k₀] RingAut k₀) (hker : ι.ker = J.subgroupOf B)
    (hBinv : ∀ u ∈ B, orderOf u = 2 → u ∈ J)
    (hJsmall : ∀ W : Subgroup G, W ≤ J → IsPGroup 2 W → Nat.card W ≤ 2) :
    IsCyclic P := by
  have hPJ : Nat.card (P ⊓ J : Subgroup G) ≤ 2 :=
    hJsmall (P ⊓ J) inf_le_right (hP.to_le inf_le_left)
  have hinvol : ∀ a : P, (a : G) ∈ J → a ≠ 1 → orderOf a = 2 := by
    intro a haJ ha1
    let a' : (P ⊓ J : Subgroup G) := ⟨a, a.2, haJ⟩
    have hdvd : orderOf a' ∣ Nat.card (P ⊓ J : Subgroup G) := orderOf_dvd_natCard a'
    have hle : orderOf a' ≤ 2 := (Nat.le_of_dvd Nat.card_pos hdvd).trans hPJ
    have hpos : 0 < orderOf a' := orderOf_pos a'
    have hne : orderOf a' ≠ 1 := by
      intro h1
      apply ha1
      have h1' : a' = 1 := orderOf_eq_one_iff.mp h1
      exact Subtype.ext (show (a : G) = 1 from congrArg Subtype.val h1')
    have h2 : orderOf a' = 2 := by omega
    have hcoe : orderOf (a : G) = orderOf a' := Subgroup.orderOf_coe a'
    rw [← Subgroup.orderOf_coe a, hcoe, h2]
  have hunique : ∀ a b : P, orderOf a = 2 → orderOf b = 2 → a = b := by
    intro a b ha hb
    have haJ : (a : G) ∈ J := hBinv a (hPB a.2) ((Subgroup.orderOf_coe a).trans ha)
    have hbJ : (b : G) ∈ J := hBinv b (hPB b.2) ((Subgroup.orderOf_coe b).trans hb)
    let a' : (P ⊓ J : Subgroup G) := ⟨a, a.2, haJ⟩
    let b' : (P ⊓ J : Subgroup G) := ⟨b, b.2, hbJ⟩
    have ha' : orderOf a' = 2 := by
      rw [← Subgroup.orderOf_coe a']
      exact (Subgroup.orderOf_coe a).trans ha
    have hcard2 : Nat.card (P ⊓ J : Subgroup G) = 2 :=
      le_antisymm hPJ (Nat.le_of_dvd Nat.card_pos (ha' ▸ orderOf_dvd_natCard a'))
    obtain ⟨y, -, hyuniq⟩ := (Nat.card_eq_two_iff' (1 : (P ⊓ J : Subgroup G))).mp hcard2
    have ha1 : a' ≠ 1 := fun h1 => by
      rw [h1, orderOf_one] at ha'
      omega
    have hb1 : b' ≠ 1 := fun h1 => by
      have hb' : orderOf b' = 2 := by
        rw [← Subgroup.orderOf_coe b']
        exact (Subgroup.orderOf_coe b).trans hb
      rw [h1, orderOf_one] at hb'
      omega
    have hab : a' = b' := (hyuniq a' ha1).trans (hyuniq b' hb1).symm
    exact Subtype.ext (congrArg (fun x : (P ⊓ J : Subgroup G) => (x : G)) hab)
  let ψ : P →* RingAut k₀ :=
    SemidirectProduct.rightHom.comp (ι.comp (Subgroup.inclusion hPB))
  have hψ : ψ.ker ≤ Subgroup.center P := by
    intro p hp
    have hrange : ι (Subgroup.inclusion hPB p) ∈
        (SemidirectProduct.inl : k₀ˣ →* k₀ˣ ⋊[ringAutUnits k₀] RingAut k₀).range := by
      rw [SemidirectProduct.range_inl_eq_ker_rightHom]
      exact hp
    obtain ⟨c, hc⟩ := hrange
    obtain ⟨n, hn⟩ := hP p
    have hdvd2 : orderOf (ι (Subgroup.inclusion hPB p)) ∣ 2 ^ n := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← map_pow, ← map_pow, hn, map_one, map_one]
    have hdvdodd : orderOf (ι (Subgroup.inclusion hPB p)) ∣ Nat.card k₀ - 1 := by
      rw [← hc, orderOf_injective _ (SemidirectProduct.inl_injective (φ := ringAutUnits k₀)) c,
        ← Nat.card_units k₀]
      exact orderOf_dvd_natCard c
    have hcop : Nat.Coprime (2 ^ n) (Nat.card k₀ - 1) :=
      (Nat.coprime_two_left.mpr hk₀).pow_left n
    have hord : orderOf (ι (Subgroup.inclusion hPB p)) = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop hdvd2 hdvdodd
    have hpker : Subgroup.inclusion hPB p ∈ ι.ker :=
      MonoidHom.mem_ker.mpr (orderOf_eq_one_iff.mp hord)
    rw [hker] at hpker
    have hpJ : (p : G) ∈ J := hpker
    rw [Subgroup.mem_center_iff]
    intro a
    by_cases hp1 : p = 1
    · rw [hp1, mul_one, one_mul]
    · have hp2 : orderOf p = 2 := hinvol p hpJ hp1
      have hconj : orderOf (a * p * a⁻¹) = 2 := by
        have h := (MulAut.conj a).orderOf_eq p
        rw [MulAut.conj_apply] at h
        rw [h, hp2]
      have heq : a * p * a⁻¹ = p := hunique _ _ hconj hp2
      calc
        a * p = a * p * a⁻¹ * a := by group
        _ = p * a := by rw [heq]
  let : IsCyclic (RingAut k₀) :=
    CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic k₀
  let : CommGroup P := commGroupOfCyclicCenterQuotient ψ hψ
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  exact CFSG.TwoRankLowerBound.Helpers.abelian_two_group_cyclic_of_unique_involution_of_card_eq_pow
    n P hP hn hunique

end CFSG.ShultStronglyClosedTI.LinearChain.TwoCoreGrowthNode
