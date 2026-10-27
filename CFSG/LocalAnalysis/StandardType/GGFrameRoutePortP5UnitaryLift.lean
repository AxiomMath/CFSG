module

public import CFSG.ClassicalGroups.Unitary.Finite
public import CFSG.LocalAnalysis.ComponentClassification.CentralQuotientComponents
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP5Cover
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP5UnitaryFix
public import CFSG.LocalAnalysis.ComponentClassification.PrimeComplementQuotientComponents

public section

namespace CFSG.StandardType.FrameRoute.UnitaryModel

open CFSG.Assembly CFSG.SeitzReduction.UnitaryPilot CFSG.LocalAnalysis.ComponentInitial
open CFSG.ClassicalGroups.UnitaryFlag
open scoped commutatorElement

variable {K : Type} [Field K] {d : ℕ}

theorem coverComponent_suBlock_eq (hK : Nat.card K = 4) {G : Type} [Group G] {L : Subgroup G}
    {φ : ↥(LargeEvenSUGroup (Fin d) K 2) →* ↥L}
    {θ : ↥L ⧸ Subgroup.center ↥L ≃* LargeEvenProj (LargeEvenSUGroup (Fin d) K 2)}
    (hθ : ∀ s, θ (QuotientGroup.mk (φ s)) = LargeEvenProjMk _ s)
    {I : Finset (Fin d)} (h4 : 4 ≤ I.card) :
    coverComponent θ (suBlock hK I) =
      (unitaryBlock (⟨Nat.prime_two, le_rfl, hK⟩ : UnitaryFieldData 2 1 K) I).map
        (L.subtype.comp φ) := by
  let h : UnitaryFieldData 2 1 K := ⟨Nat.prime_two, le_rfl, hK⟩
  let U : Subgroup ↥(LargeEvenSUGroup (Fin d) K 2) := unitaryBlock h I
  let : Finite K := h.finite
  have hcard : Nat.card K = (2 ^ 1) ^ 2 := by simpa using hK
  have hnq : (I.card, 2 ^ 1) ≠ (3, 2) := fun hh => by
    have := congrArg Prod.fst hh
    omega
  have hperfSU : Group.IsPerfect (unitarySU 2 1 K I.card) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU (K := K) (p := 2) (f := 1)
      (n := I.card) hcard (by omega) hnq
  have hperfU : Group.IsPerfect ↥U :=
    @Group.IsPerfect.ofSurjective (unitarySU 2 1 K I.card) ↥U _ _
      (unitaryBlockEquiv h I).toMonoidHom hperfSU (unitaryBlockEquiv h I).surjective
  have hcommU : ⁅U, U⁆ = U := by
    have hmap : (commutator ↥U).map U.subtype = ⁅U, U⁆ := by
      rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype]
    rw [← hmap, hperfU.commutator_eq_top, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hcomp : (coverMap θ).comp φ = LargeEvenProjMk _ := by
    ext s
    simpa [coverMap, LargeEvenProjMk, QuotientGroup.mk'_apply] using hθ s
  have hmapBlock : (U.map φ).map (coverMap θ) = suBlock hK I := by
    rw [Subgroup.map_map, hcomp]
    rfl
  have hcomap : (suBlock hK I).comap (coverMap θ) = U.map φ ⊔ Subgroup.center ↥L := by
    rw [← hmapBlock, Subgroup.comap_map_eq, coverMap_ker]
  have hderiv : CFSG.RankThree.PartOne.derivedPreimage (coverMap θ) (suBlock hK I) =
      U.map φ := by
    unfold CFSG.RankThree.PartOne.derivedPreimage
    rw [hcomap, CFSG.ComponentClassification.CatalogueBPrimeJoin.commutator_sup_central]
    · rw [← Subgroup.map_commutator, hcommU]
    · exact le_rfl
  have hcover : coverComponent θ (suBlock hK I) = U.map (L.subtype.comp φ) := by
    unfold coverComponent
    rw [hderiv, Subgroup.map_map]
  simpa [U, h] using hcover

theorem nonempty_coverComponent_suBlock_mulEquiv (hK : Nat.card K = 4) {G : Type} [Group G]
    {L : Subgroup G} {φ : ↥(LargeEvenSUGroup (Fin d) K 2) →* ↥L}
    (hker : ∀ g, φ g = 1 → ∃ c : K,
      ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = Matrix.diagonal fun _ => c)
    {θ : ↥L ⧸ Subgroup.center ↥L ≃* LargeEvenProj (LargeEvenSUGroup (Fin d) K 2)}
    (hθ : ∀ s, θ (QuotientGroup.mk (φ s)) = LargeEvenProjMk _ s)
    {I : Finset (Fin d)} (h4 : 4 ≤ I.card) (hId : I.card < d) :
    Nonempty (↥(coverComponent θ (suBlock hK I)) ≃* unitarySU 2 1 K I.card) := by
  let h : UnitaryFieldData 2 1 K := ⟨Nat.prime_two, le_rfl, hK⟩
  let U : Subgroup ↥(LargeEvenSUGroup (Fin d) K 2) := unitaryBlock h I
  have hcover := coverComponent_suBlock_eq hK hθ h4
  have hinj : Function.Injective ((L.subtype.comp φ).comp U.subtype) := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have huφ : φ u.1 = 1 := Subtype.ext (by simpa using hu)
    obtain ⟨c, hc⟩ := hker u.1 huφ
    obtain ⟨j, -, hj⟩ : ∃ j, j ∈ (Finset.univ : Finset (Fin d)) ∧ j ∉ I :=
      Finset.exists_mem_notMem_of_card_lt_card (by simpa using hId)
    have hmem : u.1 ∈ unitaryBlock h I := u.2
    have hjj : ((u.1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) j j = 1 := by
      have h1 := (mem_unitaryBlock (h := h)).mp hmem j j (Or.inl hj)
      simpa using h1
    rw [hc] at hjj
    have hc1 : c = 1 := by simpa using hjj
    have hu1 : (u.1 : GL (Fin d) K) = 1 := by
      refine Units.ext ?_
      rw [hc, hc1]
      simp
    exact Subtype.ext (Subtype.ext hu1)
  let e : ↥U ≃* ((L.subtype.comp φ).comp U.subtype).range := MonoidHom.ofInjective hinj
  have hrange : ((L.subtype.comp φ).comp U.subtype).range =
      coverComponent θ (suBlock hK I) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    simpa [U, h] using hcover.symm
  exact ⟨((e.trans (MulEquiv.subgroupCongr hrange)).symm).trans
    (unitaryBlockEquiv h I).symm⟩

end CFSG.StandardType.FrameRoute.UnitaryModel
