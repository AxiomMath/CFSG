module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Steps
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Quotient
import CFSG.RankThree.PartOne.S12.Sec1511SPEFStar
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.PerfectResiduals
import CFSG.GroupTheory.PCore.PrimeSetCore

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

theorem fstarPreimage_le (p : ℕ) (H : Subgroup G) : fstarPreimage p H ≤ H :=
  Subgroup.map_subtype_le _

theorem layerLift_le (p : ℕ) (H : Subgroup G) : layerLift p H ≤ H :=
  (Subgroup.map_subtype_le _).trans (fstarPreimage_le p H)

theorem le_normalizer_layerLift (p : ℕ) (H : Subgroup G) :
    H ≤ Subgroup.normalizer (layerLift p H : Set G) := by
  haveI : (CFSG.generalizedFitting (↥H ⧸ CFSG.pPrimeCore p ↥H)).Normal :=
    CFSG.LocalCores.generalized_fitting_characteristic.2
  have hH₀ : H ≤ Subgroup.normalizer ((fstarPreimage p H : Subgroup G) : Set G) :=
    CFSG.ABGLocalTools.le_normalizer_map_subtype H
      ((CFSG.generalizedFitting (↥H ⧸ CFSG.pPrimeCore p ↥H)).comap
        (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H)))
  have hchar : (CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual
      ↥(fstarPreimage p H)).Characteristic :=
    CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual_characteristic
  exact hH₀.trans
    (CFSG.RankThreeCoreUniqueness.Helpers.normalizer_le_normalizer_characteristic_map
      (fstarPreimage p H) (CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual
        ↥(fstarPreimage p H)) hchar)

theorem commutator_layerLift (p : ℕ) (H : Subgroup G) :
    ⁅layerLift p H, layerLift p H⁆ = layerLift p H :=
  Subgroup.isPerfect_iff.mp
    (CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidualOf_isPerfect
      (fstarPreimage p H))

theorem map_layerLift_eq (p : ℕ) (H : Subgroup G)
    (hL : ⁅CFSG.generalizedFitting (↥H ⧸ CFSG.pPrimeCore p ↥H),
      CFSG.generalizedFitting (↥H ⧸ CFSG.pPrimeCore p ↥H)⁆ =
      CFSG.generalizedFitting (↥H ⧸ CFSG.pPrimeCore p ↥H)) :
    ((layerLift p H).subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H)) =
      CFSG.generalizedFitting (↥H ⧸ CFSG.pPrimeCore p ↥H) := by
  classical
  let K₀ : Subgroup ↥H := CFSG.pPrimeCore p ↥H
  let π : ↥H →* (↥H ⧸ K₀) := QuotientGroup.mk' K₀
  let Lbar : Subgroup (↥H ⧸ K₀) := CFSG.generalizedFitting (↥H ⧸ K₀)
  let H₀ : Subgroup ↥H := Lbar.comap π
  let A : Subgroup G := fstarPreimage p H
  let PR : Subgroup ↥A := CFSG.perfectResidual ↥A
  have hAH : A ≤ H := fstarPreimage_le p H
  have hAH' : ∀ x : ↥A, A.subtype x ∈ H := fun x => hAH x.2
  have hA : A = H₀.map H.subtype := rfl
  haveI : Group.IsPerfect ↥Lbar := Subgroup.isPerfect_iff.mpr hL
  let φ : ↥A →* (↥H ⧸ K₀) := π.comp (A.subtype.codRestrict H hAH')
  have hφmem : ∀ x : ↥A, φ x ∈ Lbar := by
    intro x
    have hx : (x : G) ∈ H₀.map H.subtype := hA ▸ x.2
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    have hyl : π y ∈ Lbar := hy
    have hxy : A.subtype.codRestrict H hAH' x = y := Subtype.ext hyx.symm
    show π (A.subtype.codRestrict H hAH' x) ∈ Lbar
    rw [hxy]
    exact hyl
  let φ' : ↥A →* ↥Lbar := φ.codRestrict Lbar hφmem
  have hφ'surj : Function.Surjective φ' := by
    intro y
    obtain ⟨h, hh⟩ := QuotientGroup.mk'_surjective K₀ (y : ↥H ⧸ K₀)
    have hh₀ : h ∈ H₀ := by
      show π h ∈ Lbar
      rw [hh]
      exact y.2
    have hmem : (h : G) ∈ A := by
      rw [hA]
      exact Subgroup.mem_map_of_mem H.subtype hh₀
    refine ⟨⟨(h : G), hmem⟩, ?_⟩
    apply Subtype.ext
    show π (A.subtype.codRestrict H hAH' ⟨(h : G), hmem⟩) = (y : ↥H ⧸ K₀)
    rw [show A.subtype.codRestrict H hAH' ⟨(h : G), hmem⟩ = h from Subtype.ext rfl, hh]
  have hPRtop : PR.map φ' = ⊤ :=
    CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_surjects_to_perfect_image
      φ' hφ'surj
  have hmapφ : PR.map φ = Lbar := by
    apply le_antisymm
    · rintro _ ⟨x, -, rfl⟩
      exact hφmem x
    · intro y hy
      have hy' : (⟨y, hy⟩ : ↥Lbar) ∈ PR.map φ' := by
        rw [hPRtop]
        exact Subgroup.mem_top _
      obtain ⟨x, hx, hx'⟩ := Subgroup.mem_map.mp hy'
      exact Subgroup.mem_map.mpr ⟨x, hx, congrArg Subtype.val hx'⟩
  have hJ : (layerLift p H).subgroupOf H =
      PR.map (A.subtype.codRestrict H hAH') := by
    ext h
    constructor
    · intro hh
      rw [Subgroup.mem_subgroupOf] at hh
      change (h : G) ∈ PR.map A.subtype at hh
      obtain ⟨x, hx, hx'⟩ := Subgroup.mem_map.mp hh
      exact Subgroup.mem_map.mpr ⟨x, hx, Subtype.ext hx'⟩
    · intro hh
      obtain ⟨x, hx, hx'⟩ := Subgroup.mem_map.mp hh
      rw [Subgroup.mem_subgroupOf]
      change (h : G) ∈ PR.map A.subtype
      exact Subgroup.mem_map.mpr ⟨x, hx, congrArg Subtype.val hx'⟩
  calc ((layerLift p H).subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H))
      = ((layerLift p H).subgroupOf H).map π := rfl
    _ = (PR.map (A.subtype.codRestrict H hAH')).map π := by rw [hJ]
    _ = PR.map (π.comp (A.subtype.codRestrict H hAH')) := by rw [Subgroup.map_map]
    _ = PR.map φ := rfl
    _ = Lbar := hmapφ
    _ = CFSG.generalizedFitting (↥H ⧸ CFSG.pPrimeCore p ↥H) := rfl

namespace Sec7Core4



theorem isSimpleGroup_generalizedFitting_quotient (k : Sec7Core4 G) {H : Subgroup G}
    (hH : Config k H) :
    IsSimpleGroup ↥(CFSG.generalizedFitting (↥H ⧸ CFSG.pPrimeCore k.p ↥H)) ∧
      (∃ a b : ↥(CFSG.generalizedFitting (↥H ⧸ CFSG.pPrimeCore k.p ↥H)), a * b ≠ b * a) ∧
      (CFSG.generalizedFitting (↥H ⧸ CFSG.pPrimeCore k.p ↥H)).Normal ∧
      Subgroup.centralizer ((CFSG.generalizedFitting (↥H ⧸ CFSG.pPrimeCore k.p ↥H) :
        Subgroup (↥H ⧸ CFSG.pPrimeCore k.p ↥H)) : Set (↥H ⧸ CFSG.pPrimeCore k.p ↥H)) = ⊥ := by
  have hp : k.p.Prime := k.prime
  haveI : Fact k.p.Prime := ⟨hp⟩
  let K₀ : Subgroup ↥H := CFSG.pPrimeCore k.p ↥H
  let Lbar : Subgroup (↥H ⧸ K₀) := CFSG.generalizedFitting (↥H ⧸ K₀)
  have hO : CFSG.pPrimeCore k.p (↥H ⧸ K₀) = ⊥ := CFSG.pPrimeCore_quotient_eq_bot hp
  have hY : IsStronglyPEmbedded k.p (((H ⊓ k.M).subgroupOf H).map (QuotientGroup.mk' K₀)) :=
    isStronglyPEmbedded_map_quotient_pPrimeCore k hH
  exact CFSG.RankThree.PartOne.Sec1511.spe_fstar hp hO hY

theorem dvd_card_generalizedFitting_quotient (k : Sec7Core4 G) {H : Subgroup G}
    (hH : Config k H) :
    k.p ∣ Nat.card ↥(CFSG.generalizedFitting (↥H ⧸ CFSG.pPrimeCore k.p ↥H)) := by
  have hp : k.p.Prime := k.prime
  haveI : Fact k.p.Prime := ⟨hp⟩
  let K₀ : Subgroup ↥H := CFSG.pPrimeCore k.p ↥H
  let Lbar : Subgroup (↥H ⧸ K₀) := CFSG.generalizedFitting (↥H ⧸ K₀)
  by_contra h
  have hcop : Nat.Coprime k.p (Nat.card ↥Lbar) := (hp.coprime_iff_not_dvd).mpr h
  haveI : Lbar.Normal := CFSG.LocalCores.generalized_fitting_characteristic.2
  have hle : Lbar ≤ CFSG.pPrimeCore k.p (↥H ⧸ K₀) :=
    CFSG.RankThree.PartOne.Sec1511.le_pPrimeCore_of_isSubnormal_p
      (inferInstance : Lbar.Normal).isSubnormal hcop
  rw [CFSG.pPrimeCore_quotient_eq_bot hp] at hle
  have hbot : Lbar = ⊥ := le_bot_iff.mp hle
  haveI : IsSimpleGroup ↥Lbar := (isSimpleGroup_generalizedFitting_quotient k hH).1
  exact (Subgroup.nontrivial_iff_ne_bot Lbar).1 inferInstance hbot

theorem step72L (k : Sec7Core4 G) : Step72L k := by
  intro H hH hJM
  have hp : k.p.Prime := k.prime
  haveI : Fact k.p.Prime := ⟨hp⟩
  let K₀ : Subgroup ↥H := CFSG.pPrimeCore k.p ↥H
  let π : ↥H →* (↥H ⧸ K₀) := QuotientGroup.mk' K₀
  let Lbar : Subgroup (↥H ⧸ K₀) := CFSG.generalizedFitting (↥H ⧸ K₀)
  have hsimple := isSimpleGroup_generalizedFitting_quotient k hH
  haveI : IsSimpleGroup ↥Lbar := hsimple.1
  have hperf : ⁅Lbar, Lbar⁆ = Lbar :=
    Subgroup.isPerfect_iff.mp
      (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hsimple.2.1).1.1
  have hmap : ((layerLift k.p H).subgroupOf H).map π = Lbar := map_layerLift_eq k.p H hperf
  have hN : IsStronglyPEmbedded k.p (((H ⊓ k.M).subgroupOf H).map π) :=
    isStronglyPEmbedded_map_quotient_pPrimeCore k hH
  have hle : Lbar ≤ ((H ⊓ k.M).subgroupOf H).map π := by
    rw [← hmap]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono H (le_inf (layerLift_le k.p H) hJM))
  haveI : Lbar.Normal := CFSG.LocalCores.generalized_fitting_characteristic.2
  exact hN.not_dvd_card_of_normal_le hle (dvd_card_generalizedFitting_quotient k hH)

end Sec7Core4

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
