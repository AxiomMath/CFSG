module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Steps
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.LayerBasic
import CFSG.Alternating.Multipliers.OddKernel
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Lemmas
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.Foundations
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.GroupTheory.PCore.Transport
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.Quasithin.Background.A1bGroups
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.theorem_3_4
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem eight70_layerLift_map_alternatingTen (k : Section7.Sec7Core4 G)
    {H : Subgroup G} (hH : k.Config H)
    (e : ↥(CFSG.generalizedFitting (↥H ⧸ CFSG.pPrimeCore k.p ↥H)) ≃*
      alternatingGroup (Fin 10)) :
    ∃ φ : ↥(Section7.layerLift k.p H) →* alternatingGroup (Fin 10),
      Function.Surjective φ ∧
        φ.ker ≤ ((CFSG.pPrimeCore k.p ↥H).map H.subtype).subgroupOf
          (Section7.layerLift k.p H) ∧
        ((CFSG.pPrimeCore k.p ↥H).map H.subtype).subgroupOf
          (Section7.layerLift k.p H) ≤ φ.ker := by
  classical
  have hp : k.p.Prime := k.prime
  have : Fact k.p.Prime := ⟨hp⟩
  let K : Subgroup ↥H := CFSG.pPrimeCore k.p ↥H
  let π : ↥H →* (↥H ⧸ K) := QuotientGroup.mk' K
  let Lbar : Subgroup (↥H ⧸ K) := CFSG.generalizedFitting (↥H ⧸ K)
  let J : Subgroup G := Section7.layerLift k.p H
  let KG : Subgroup G := K.map H.subtype
  have hJH : J ≤ H := Section7.layerLift_le k.p H
  have hsimple := k.isSimpleGroup_generalizedFitting_quotient hH
  have : IsSimpleGroup ↥Lbar := hsimple.1
  have hLbarperf : ⁅Lbar, Lbar⁆ = Lbar :=
    Subgroup.isPerfect_iff.mp
      (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hsimple.2.1).1.1
  have hmap : (J.subgroupOf H).map π = Lbar := Section7.map_layerLift_eq k.p H hLbarperf
  let φ₀ : ↥J →* (↥H ⧸ K) := π.comp (Subgroup.inclusion hJH)
  have hφ₀range : φ₀.range = Lbar := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
    exact hmap
  let φL : ↥J →* ↥Lbar := φ₀.codRestrict Lbar
    (fun x => hφ₀range ▸ ⟨x, rfl⟩)
  have hφLsurj : Function.Surjective φL := by
    intro y
    have hy : (y : ↥H ⧸ K) ∈ φ₀.range := by
      rw [hφ₀range]
      exact y.2
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, Subtype.ext hx⟩
  let φ : ↥J →* alternatingGroup (Fin 10) := e.toMonoidHom.comp φL
  have hφsurj : Function.Surjective φ := e.surjective.comp hφLsurj
  have hker_le : ∀ x : ↥J, φ x = 1 → (x : G) ∈ KG := by
    intro x hx
    have hxL : φL x = 1 := by
      apply e.injective
      simpa [φ] using hx
    have hx₀ : φ₀ x = 1 := by
      simpa [φL] using congrArg Subtype.val hxL
    exact Subgroup.mem_map_of_mem H.subtype
      ((QuotientGroup.eq_one_iff (Subgroup.inclusion hJH x)).mp hx₀)
  have hKG_le : KG.subgroupOf J ≤ φ.ker := by
    intro x hx
    have hxKG : (x : G) ∈ KG := Subgroup.mem_subgroupOf.mp hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxKG
    have hincl : Subgroup.inclusion hJH x = y := Subtype.ext hyx.symm
    have hmemK : Subgroup.inclusion hJH x ∈ K := by
      rw [hincl]
      exact hy
    have hx₀ : φ₀ x = 1 := by
      show π (Subgroup.inclusion hJH x) = 1
      exact (QuotientGroup.eq_one_iff (Subgroup.inclusion hJH x)).mpr hmemK
    have hxL : φL x = 1 :=
      Subtype.ext (by simpa [φL] using hx₀)
    show e (φL x) = 1
    rw [hxL, map_one]
  exact ⟨φ, hφsurj, fun x hx => Subgroup.mem_subgroupOf.mpr (hker_le x hx), hKG_le⟩

private theorem eight70_layerLift_ker_center_and_odd (k : Section7.Sec7Core4 G)
    {H : Subgroup G} (hH : k.Config H)
    (h75 : ⁅Section7.layerLift k.p H,
      (CFSG.pPrimeCore k.p ↥H).map H.subtype⁆ = ⊥)
    (φ : ↥(Section7.layerLift k.p H) →* alternatingGroup (Fin 10))
    (hker : φ.ker ≤ ((CFSG.pPrimeCore k.p ↥H).map H.subtype).subgroupOf
      (Section7.layerLift k.p H)) :
    φ.ker ≤ Subgroup.center ↥(Section7.layerLift k.p H) ∧ Odd (Nat.card φ.ker) := by
  classical
  let J : Subgroup G := Section7.layerLift k.p H
  let KG : Subgroup G := (CFSG.pPrimeCore k.p ↥H).map H.subtype
  have hcent : KG ≤ Subgroup.centralizer (J : Set G) := by
    rw [Subgroup.commutator_comm] at h75
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := KG) (H₂ := J)).mp h75
  constructor
  · intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp
      (hcent (Subgroup.mem_subgroupOf.mp (hker hx))) (y : G) y.2
  · have hcardsub : Nat.card ↥(KG.subgroupOf J) = Nat.card (KG ⊓ J : Subgroup G) := by
      have hsub : KG.subgroupOf J = (KG ⊓ J).subgroupOf J := by
        ext x
        simp [Subgroup.mem_subgroupOf]
      rw [hsub, CFSG.natCard_subgroupOf_eq (KG ⊓ J) J inf_le_right]
    have hdiv : Nat.card φ.ker ∣ Nat.card ↥KG :=
      (Subgroup.card_dvd_of_le hker).trans (hcardsub ▸
        Subgroup.card_dvd_of_le (inf_le_left : KG ⊓ J ≤ KG))
    have hoddKG : Odd (Nat.card ↥KG) := by
      rw [Subgroup.card_map_of_injective H.subtype_injective]
      exact k.odd_card_pPrimeCore_of_not_le hH.not_le hH.two_le_pRank
    exact Odd.of_dvd_nat hoddKG hdiv

theorem eight70_layer_equiv (k : Section7.Sec7Core4 G) {H : Subgroup G} (hH : k.Config H)
    (h75 : k.Step75)
    (hF : Nonempty (↥(CFSG.generalizedFitting (↥H ⧸ CFSG.pPrimeCore k.p ↥H)) ≃*
      alternatingGroup (Fin 10))) :
    Nonempty (↥(Section7.layerLift k.p H) ≃* alternatingGroup (Fin 10)) ∧
      Section7.layerLift k.p H ⊓ (CFSG.pPrimeCore k.p ↥H).map H.subtype = ⊥ := by
  classical
  obtain ⟨e⟩ := hF
  obtain ⟨φ, hφsurj, hker_le, hKG_le⟩ :=
    eight70_layerLift_map_alternatingTen (k := k) (H := H) hH e
  have hcenter_odd := eight70_layerLift_ker_center_and_odd k hH (h75 H hH) φ hker_le
  have hperf : Group.IsPerfect ↥(Section7.layerLift k.p H) :=
    Subgroup.isPerfect_iff.mpr (Section7.commutator_layerLift k.p H)
  have hcard : Nat.card φ.ker = 1 :=
    CFSG.Alternating.Multipliers.card_ker_eq_one_of_odd
      (P := ↥(Section7.layerLift k.p H)) (m := 8) (by norm_num) φ hφsurj
      hcenter_odd.1 hcenter_odd.2
  have hkerbot : φ.ker = ⊥ := Subgroup.card_eq_one.mp hcard
  have hφinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hkerbot
  refine ⟨⟨MulEquiv.ofBijective φ ⟨hφinj, hφsurj⟩⟩, ?_⟩
  rw [eq_bot_iff]
  intro x hx
  have hxker : (⟨x, hx.1⟩ : ↥(Section7.layerLift k.p H)) ∈ φ.ker :=
    hKG_le (Subgroup.mem_subgroupOf.mpr hx.2)
  have hx1 : (⟨x, hx.1⟩ : ↥(Section7.layerLift k.p H)) = 1 := by
    rw [hkerbot] at hxker
    simpa using hxker
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val hx1)

omit [Finite G] in
theorem eight70_le_layerLift {p : ℕ} {H X : Subgroup G} (hXH : X ≤ H) (hX : ⁅X, X⁆ = X)
    (hXF : (X.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H)) ≤
      CFSG.generalizedFitting (↥H ⧸ CFSG.pPrimeCore p ↥H)) :
    X ≤ Section7.layerLift p H := by
  classical
  have hXA : X ≤ Section7.fstarPreimage p H := by
    intro x hx
    refine Subgroup.mem_map.mpr ⟨⟨x, hXH hx⟩, ?_, rfl⟩
    exact hXF (Subgroup.mem_map.mpr
      ⟨⟨x, hXH hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩)
  let A : Subgroup G := Section7.fstarPreimage p H
  let S : Subgroup ↥A := X.subgroupOf A
  have hmapXA : S.map A.subtype = X := Subgroup.map_subgroupOf_eq_of_le hXA
  have hSperf : ⁅S, S⁆ = S := by
    apply Subgroup.map_injective A.subtype_injective
    rw [Subgroup.map_commutator, hmapXA, hX]
  have hSle : S ≤ CFSG.perfectResidual ↥A := by
    refine le_iInf fun n => ?_
    induction n with
    | zero => exact le_top
    | succ n ih =>
      rw [derivedSeries_succ]
      calc S = ⁅S, S⁆ := hSperf.symm
        _ ≤ ⁅derivedSeries ↥A n, derivedSeries ↥A n⁆ := Subgroup.commutator_mono ih ih
  have hmapS := Subgroup.map_mono (f := A.subtype) hSle
  rw [hmapXA] at hmapS
  exact hmapS

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
