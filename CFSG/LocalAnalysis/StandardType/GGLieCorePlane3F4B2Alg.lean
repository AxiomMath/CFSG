module

public import CFSG.LocalAnalysis.StandardType.GGLieCorePlane3F4Defs
public import CFSG.LocalAnalysis.StandardType.GGFamLabelAssembly
import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.RationalB2Part2
import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.B2Inner
import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.NativePinFinalPart2
import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.JointShapesPart2
import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.SelectedLiteralPart2
import CFSG.LocalAnalysis.StandardType.GGLieCoreSmallSetup
import CFSG.HardMathSupport.Timmesfeld.LangTorus.ExcPin
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.IsAlgClosed.Basic
public import CFSG.LocalAnalysis.StandardType.GGFamAssembly

public section

namespace CFSG.StandardType.LieCore

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType
  CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.SeitzReduction.F4Pilot CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KF4
  CFSG.ComponentClassification.CatLeafProof
  CFSG.StandardType.F4ExplicitPos.BaseChange
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Open (StatedLieTag StatedSp)
open scoped Matrix

private theorem l10lG5_ncard_pair (j : Fin Tag.F4.rank) :
    ({Pi.single j 1, -Pi.single j 1} : Set (Fin Tag.F4.rank → ℤ)).ncard = 2 := by
  rw [Set.ncard_pair]
  intro h
  have := congrFun h j
  simp at this

private theorem l10lG5_ncard_parabolicRoots_f4LongSupport :
    (parabolicRoots Tag.F4 f4LongSupport).ncard = 6 := by
  have hnone : none ∉ ({some 0, some 1} : Finset (Option (Fin Tag.F4.rank))) := by
    decide +kernel
  have hCJ : ∀ j : Fin Tag.F4.rank,
      some j ∈ ({some 0, some 1} : Finset (Option (Fin Tag.F4.rank))) ↔ j ∈ f4LongSupport := by
    intro j; rw [mem_f4LongSupport]; revert j; decide +kernel
  have hroots : kacF4.rootsOf (↑({some 0, some 1} : Finset (Option (Fin Tag.F4.rank))) :
      Set (Option (Fin Tag.F4.rank))) = parabolicRoots Tag.F4 f4LongSupport :=
    rootsOf_eq_parabolicRoots_narrow kacF4 facts_F4 (J := f4LongSupport) hnone hCJ
  have hθ : kacF4.θ = ![2, 3, 4, 2] := rfl
  calc (parabolicRoots Tag.F4 f4LongSupport).ncard
      = (kacF4.rootsOf (↑({some 0, some 1} : Finset (Option (Fin Tag.F4.rank))) :
          Set (Option (Fin Tag.F4.rank)))).ncard := by rw [hroots]
    _ = kacCount Tag.F4 kacF4.θ ({some 0, some 1} : Finset (Option (Fin Tag.F4.rank))) :=
        ncard_rootsOf kacF4 facts_F4 ⟨none, hnone⟩
    _ = kacCount Tag.F4 ![2, 3, 4, 2]
        ({some 0, some 1} : Finset (Option (Fin Tag.F4.rank))) := by rw [hθ]
    _ = 6 := by decide +kernel

private theorem l10lG5_ncard_parabolicRoots_f4ShortSupport :
    (parabolicRoots Tag.F4 f4ShortSupport).ncard = 6 := by
  have hnone : none ∉ ({some 2, some 3} : Finset (Option (Fin Tag.F4.rank))) := by
    decide +kernel
  have hCJ : ∀ j : Fin Tag.F4.rank,
      some j ∈ ({some 2, some 3} : Finset (Option (Fin Tag.F4.rank))) ↔ j ∈ f4ShortSupport := by
    intro j; rw [mem_f4ShortSupport]; revert j; decide +kernel
  have hroots : kacF4.rootsOf (↑({some 2, some 3} : Finset (Option (Fin Tag.F4.rank))) :
      Set (Option (Fin Tag.F4.rank))) = parabolicRoots Tag.F4 f4ShortSupport :=
    rootsOf_eq_parabolicRoots_narrow kacF4 facts_F4 (J := f4ShortSupport) hnone hCJ
  have hθ : kacF4.θ = ![2, 3, 4, 2] := rfl
  calc (parabolicRoots Tag.F4 f4ShortSupport).ncard
      = (kacF4.rootsOf (↑({some 2, some 3} : Finset (Option (Fin Tag.F4.rank))) :
          Set (Option (Fin Tag.F4.rank)))).ncard := by rw [hroots]
    _ = kacCount Tag.F4 kacF4.θ ({some 2, some 3} : Finset (Option (Fin Tag.F4.rank))) :=
        ncard_rootsOf kacF4 facts_F4 ⟨none, hnone⟩
    _ = kacCount Tag.F4 ![2, 3, 4, 2]
        ({some 2, some 3} : Finset (Option (Fin Tag.F4.rank))) := by rw [hθ]
    _ = 6 := by decide +kernel

private theorem l10lG5_shape_b2
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {D : LangDatum Tag.F4 L}
    {ρ : Equiv.Perm (Fin Tag.F4.rank → ℤ)} {a₁ a₂ : Fin Tag.F4.rank → Lˣ}
    (h : GGLieF4PlaneHyp D ρ a₁ a₂)
    (i : KernelComponent (jointChar a₁ a₂))
    (hshape : compRank (componentRoots (jointChar a₁ a₂) i) = 2 ∧
      (componentRoots (jointChar a₁ a₂) i).ncard = 8) :
    ∃ w : WeylGroup Tag.F4,
      componentRoots (jointChar a₁ a₂) i = (fun α => w • α) '' b2LeviRoots := by
  have ha : ∀ j, a₁ j ^ 3 = 1 := pow_eq_one_of_rootDiagUnit_pow (a := a₁) h.pow₁
  have hd : ∀ j, a₂ j ^ 3 = 1 := pow_eq_one_of_rootDiagUnit_pow (a := a₂) h.pow₂
  have hne : rootDiagUnit Tag.F4 a₁ ≠ 1 ∨ rootDiagUnit Tag.F4 a₂ ≠ 1 := by
    by_contra hc
    push Not at hc
    have hbot : Subgroup.closure ({rootDiagUnit Tag.F4 a₁, rootDiagUnit Tag.F4 a₂} :
        Set (ModGL Tag.F4 L)) = ⊥ := by
      rw [eq_bot_iff, Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact Subgroup.mem_bot.mpr hc.1
      · exact Subgroup.mem_bot.mpr hc.2
    have hcard := h.card
    rw [hbot, Subgroup.card_bot] at hcard
    norm_num at hcard
  obtain ⟨w, hcases⟩ :=
    CFSG.StandardType.F4ExplicitPos.JointShapes.f4_joint_component_six_shape
      (p := 3) (by norm_num) (by decide) a₁ a₂ ha hd hne i
  rcases hcases with ⟨j, hj⟩ | hlong | hshort | hb2 | hb3 | hc3
  · exfalso
    have h8 := hshape.2
    rw [hj, ncard_image_smul] at h8
    rw [l10lG5_ncard_pair j] at h8
    omega
  · exfalso
    have h8 := hshape.2
    rw [hlong, ncard_image_smul] at h8
    rw [l10lG5_ncard_parabolicRoots_f4LongSupport] at h8
    omega
  · exfalso
    have h8 := hshape.2
    rw [hshort, ncard_image_smul] at h8
    rw [l10lG5_ncard_parabolicRoots_f4ShortSupport] at h8
    omega
  · exact ⟨w, hb2⟩
  · exfalso
    have h8 := hshape.2
    rw [hb3, ncard_image_smul] at h8
    rw [CFSG.StandardType.F4ExplicitPos.SelectedLiteral.ncard_parabolicRoots_f4LeviB3] at h8
    omega
  · exfalso
    have h8 := hshape.2
    rw [hc3, ncard_image_smul] at h8
    rw [CFSG.StandardType.F4ExplicitPos.SelectedLiteral.ncard_parabolicRoots_f4LeviC3] at h8
    omega

theorem ggLieF4B2_fixedGroup_alg
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharP Ω 2] [Algebra (ZMod 2) Ω]
    [Algebra.IsAlgebraic (ZMod 2) Ω] {D : LangDatum Tag.F4 Ω}
    {ρ : Equiv.Perm (Fin Tag.F4.rank → ℤ)} {a₁ a₂ : Fin Tag.F4.rank → Ωˣ}
    (h : GGLieF4PlaneHyp D ρ a₁ a₂)
    {f : ℕ} (hf : 1 ≤ f) (hqf : D.q = 2 ^ f) (i : KernelComponent (jointChar a₁ a₂))
    (hshape : compRank (componentRoots (jointChar a₁ a₂) i) = 2 ∧
      (componentRoots (jointChar a₁ a₂) i).ncard = 8)
    (hρΨ : (ρ : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ)) ''
      componentRoots (jointChar a₁ a₂) i = componentRoots (jointChar a₁ a₂) i) :
    GGLieSp4Model ↥(rootSpan Tag.F4 Ω (componentRoots (jointChar a₁ a₂) i) ⊓ D.model) f := by
  obtain ⟨w, hΨ⟩ := l10lG5_shape_b2 h i hshape
  have hS : ∀ γ ∈ b2LeviRoots, IsRoot Tag.F4 γ := fun γ hγ => (mem_b2LeviRoots.1 hγ).1
  let n : ModGL Tag.F4 Ω := canonicalRep (coxeterSystem Tag.F4) Ω w
  have hnRange : MonoidHom.range (CFSG.StandardType.F4ExplicitPos.RationalB2.conjIMB2 Ω n) =
      rootSpan Tag.F4 Ω (componentRoots (jointChar a₁ a₂) i) := by
    rw [CFSG.StandardType.F4ExplicitPos.RationalB2.range_conjIMB2 Ω n,
      CFSG.RankThree.PartOne.KE.map_conj_rootSpan (L := Ω) w hS, ← hΨ]
  have hker : ∀ γ ∈ kernelRoots (jointChar a₁ a₂),
      ρ γ ∈ kernelRoots (jointChar a₁ a₂) := by
    intro γ hγ
    have := iterate_mem_kernelRoots_jointChar h.frob h.mem₁ h.mem₂ 1 hγ
    rwa [Function.iterate_one] at this
  have hinner : twistInner (componentRoots (jointChar a₁ a₂) i) ρ :=
    CFSG.StandardType.F4ExplicitPos.B2Inner.b2_component_rho_twistInner
      (D := D) (ρ := ρ) h.frob i hΨ hρΨ
  obtain ⟨σ, z, hσc, hzZ, hnorm, hgoal⟩ :=
    CFSG.StandardType.F4ExplicitPos.NativePinFinal.exists_untwist_one_step_native
      D f hf hqf ρ h.frob i hker hinner
  let : Algebra (ZMod 2) (GaloisField 2 f) := inferInstance
  let : Algebra.IsAlgebraic (ZMod 2) (GaloisField 2 f) := inferInstance
  let : Algebra (GaloisField 2 f) Ω :=
    (IsAlgClosed.lift (R := ZMod 2) (S := GaloisField 2 f) (M := Ω)).toRingHom.toAlgebra
  have hKcard : Nat.card (GaloisField 2 f) = 2 ^ f :=
    GaloisField.card (p := 2) (n := f) (by omega)
  have hσ : ∀ c, σ c = c ^ Nat.card (GaloisField 2 f) := fun c => by rw [hσc c, hqf, hKcard]
  have hn : bcGL (τ := Tag.F4) σ.toRingHom n = n :=
    CFSG.StandardType.F4ExplicitPos.PinnedBaseChange.bcGL_canonicalRep (τ := Tag.F4) σ.toRingHom
      (coxeterSystem Tag.F4) w
  have hn_adj : n ∈ adjointGroup Tag.F4 Ω :=
    CFSG.LieType.Chevalley.canonicalRep_mem_adjointGroup (coxeterSystem Tag.F4) Ω w
  have hz_adj : z ∈ adjointGroup Tag.F4 Ω :=
    CFSG.StandardType.F4ExplicitPos.NativePinFinal.Zsub_le_adjointGroup (jointChar a₁ a₂) hzZ
  have hbc : bcGL (τ := Tag.F4) σ.toRingHom = frobGL σ := by
    unfold CFSG.StandardType.F4ExplicitPos.BaseChange.bcGL
    rw [CFSG.StandardType.F4ExplicitPos.BaseChange.bcEndHom_eq_entrywiseHom]
  have hzH : ∀ g, g ∈ MonoidHom.range (CFSG.StandardType.F4ExplicitPos.RationalB2.conjIMB2 Ω n) ↔
      z * g * z⁻¹ ∈ MonoidHom.range (CFSG.StandardType.F4ExplicitPos.RationalB2.conjIMB2 Ω n) := by
    intro g
    rw [hnRange]
    exact CFSG.StandardType.F4ExplicitPos.NativePinFinal.normalizesAll_apply hnorm i g
  have hzF : ∀ g ∈ MonoidHom.range (CFSG.StandardType.F4ExplicitPos.RationalB2.conjIMB2 Ω n),
      D.step (z * g * z⁻¹) = z * bcGL (τ := Tag.F4) σ.toRingHom g * z⁻¹ := by
    intro g hg
    rw [hnRange] at hg
    rw [hbc]
    exact hgoal g hg
  let κ : StatedSp 2 (GaloisField 2 f) →* ModGL Tag.F4 Ω :=
    ((MulAut.conj z).toMonoidHom.comp
      (CFSG.StandardType.F4ExplicitPos.RationalB2.conjIMB2 Ω n)).comp
      (statedSpMap (algebraMap (GaloisField 2 f) Ω) 2)
  have hκrange : κ.range = rootSpan Tag.F4 Ω (componentRoots (jointChar a₁ a₂) i) ⊓ D.model := by
    change MonoidHom.range (((MulAut.conj z).toMonoidHom.comp
        (CFSG.StandardType.F4ExplicitPos.RationalB2.conjIMB2 Ω n)).comp
        (statedSpMap (algebraMap (GaloisField 2 f) Ω) 2)) = _
    rw [CFSG.StandardType.F4ExplicitPos.RationalB2.range_PhiB2_eq_inf_model Ω D σ.toRingHom hσ
      n z hn_adj hz_adj hn hzH hzF, hnRange]
  have hκinj : Function.Injective κ := by
    change Function.Injective (((MulAut.conj z).toMonoidHom.comp
      (CFSG.StandardType.F4ExplicitPos.RationalB2.conjIMB2 Ω n)).comp
      (statedSpMap (algebraMap (GaloisField 2 f) Ω) 2))
    exact CFSG.StandardType.F4ExplicitPos.RationalB2.PhiB2_injective Ω n z
  refine ⟨GaloisField 2 f, inferInstance, inferInstance, hKcard, ?_⟩
  exact ⟨((MonoidHom.ofInjective hκinj).trans (MulEquiv.subgroupCongr hκrange)).symm⟩

end CFSG.StandardType.LieCore
