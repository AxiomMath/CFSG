module

public import CFSG.LocalAnalysis.StandardType.GGTwE6RootAsCoreDefs
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeToralityTw
public import CFSG.LieType.SeitzGeneration.ExcHighThree.KillsRootGroup
public import CFSG.RankThree.Chevalley.SteinbergBTE6HighestRootGraph
import CFSG.LocalAnalysis.StandardType.GGTwE6RootKernelCount
import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.Normalizer
import CFSG.LocalAnalysis.SeitzReduction.EPilotRoots

public section

namespace CFSG.StandardType.TwE6RootAs

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LieType.SeitzGeneration.ExcHighThree
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Chevalley


theorem w0_smul_permLattice (x : Fin TwistTag.E6.tag.rank → ℤ) :
    e6HRReflProd • permLattice TwistTag.E6.perm x = -x := by
  rw [e6HRReflProd_smul]
  have h := permLattice_permLattice_symm TwistTag.E6.perm x
  rw [show TwistTag.E6.perm.symm = TwistTag.E6.perm by decide] at h
  rw [h]

theorem image_w0_familyKernel {L : Type} [Field L] {ι : Type}
    (a : ι → Fin TwistTag.E6.tag.rank → Lˣ) :
    (fun α => e6HRReflProd • permLattice TwistTag.E6.perm α) '' familyKernel a =
      familyKernel a := by
  simp only [w0_smul_permLattice]
  ext β
  constructor
  · rintro ⟨α, hα, rfl⟩
    exact neg_mem_familyKernel a hα
  · intro hβ
    exact ⟨-β, neg_mem_familyKernel a hβ, neg_neg β⟩

theorem exists_twFrob_w0_eq_mul {L : Type} [Field L] [IsAlgClosed L] {ℓ : ℕ} [Fact ℓ.Prime]
    [CharP L ℓ] {f : ℕ} (hf : 1 ≤ f) {ι : Type} (a : ι → Fin TwistTag.E6.tag.rank → Lˣ) :
    ∀ c ∈ familyGroup (K := L) a, ∃ z ∈ familyGroup (K := L) a,
      twFrob TwistTag.E6 (canonicalRep (coxeterSystem TwistTag.E6.tag) L e6HRReflProd)
        (iterateFrobenius L ℓ f) z = z * c := by
  have hFrs : Function.Surjective (iterateFrobenius L ℓ f) := fun y => by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y (pow_pos (Fact.out : ℓ.Prime).pos f)
    exact ⟨x, by rw [iterateFrobenius_def, hx]⟩
  have e : ∀ g, frobTwistGL TwistTag.E6.tag L ℓ f
      (canonicalRep (coxeterSystem TwistTag.E6.tag) L e6HRReflProd * diagramMap TwistTag.E6 L) g =
        twFrob TwistTag.E6 (canonicalRep (coxeterSystem TwistTag.E6.tag) L e6HRReflProd)
          (iterateFrobenius L ℓ f) g := fun g => by
    rw [frobTwistGL_apply, twFrob_apply, CFSG.LieType.Chevalley.twistHom_apply]
    group
  intro c hc
  obtain ⟨z, hz, hzc⟩ := lang_familyGroup_of_mapsTo ℓ a f hf
    (canonicalRep (coxeterSystem TwistTag.E6.tag) L e6HRReflProd * diagramMap TwistTag.E6 L)
    (fun g hg => by
      rw [e]
      exact twFrob_mem_familyGroup TwistTag.E6 hFrs e6HRReflProd a (image_w0_familyKernel a) hg)
    c hc
  refine ⟨z, hz, ?_⟩
  have h2 := e z
  rw [frobTwistGL_apply] at h2
  rw [← h2, ← hzc]
  group

theorem mem_closure_rootReflection_of_smul_eq {L : Type} [Field L]
    {γ : Fin TwistTag.E6.tag.rank → ℤ} (hγ : IsRoot TwistTag.E6.tag γ) (ζ : Lˣ)
    {u : WeylGroup TwistTag.E6.tag} (hu : u • γ = γ) :
    u ∈ Subgroup.closure (rootReflection '' familyKernel (fun _ : Unit => corootTuple γ ζ)) := by
  obtain ⟨x, hx⟩ := CFSG.SeitzReduction.EPilot.exists_smul_eq_highRoot
    (τ := TwistTag.E6.tag) (Or.inl rfl) hγ
  have hθ : (x * u * x⁻¹) • CFSG.SeitzReduction.highRoot TwistTag.E6.tag =
      CFSG.SeitzReduction.highRoot TwistTag.E6.tag := by
    rw [← hx, mul_smul, mul_smul, inv_smul_smul, hu]
  have hP :=
    CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis.mem_parabolicWeylGroup_of_smul_highRoot
      TwistTag.E6.tag hθ
  have hle : parabolicWeylGroup TwistTag.E6.tag
      (CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis.Jθ TwistTag.E6.tag) ≤
      (Subgroup.closure (rootReflection '' familyKernel (fun _ : Unit => corootTuple γ ζ))).comap
        (MulAut.conj x⁻¹).toMonoidHom := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨j, hj, rfl⟩
    have hj' : j ≠ CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis.iθ TwistTag.E6.tag := hj
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    change x⁻¹ * simple TwistTag.E6.tag j * x⁻¹⁻¹ ∈
      Subgroup.closure (rootReflection '' familyKernel (fun _ : Unit => corootTuple γ ζ))
    rw [← rootReflection_eq_conj (β := x⁻¹ • Pi.single j 1) rfl]
    refine Subgroup.subset_closure ⟨x⁻¹ • Pi.single j 1,
      ⟨IsRoot.smul (isRoot_single _ j) _, fun _ => ?_⟩, rfl⟩
    have h1 : iform (x⁻¹ • (Pi.single j 1 : Fin TwistTag.E6.tag.rank → ℤ)) γ = 0 := by
      rw [← iform_smul x, smul_inv_smul, hx, iform_comm,
        CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis.iform_highRoot_apply,
        Pi.single_eq_of_ne hj'.symm, mul_zero]
    rw [CFSG.StandardType.TwE6RootKill.rootChar_corootTuple, h1, zpow_zero]
  have h := hle hP
  rw [Subgroup.mem_comap] at h
  have e : (MulAut.conj x⁻¹).toMonoidHom (x * u * x⁻¹) = u := by
    show x⁻¹ * (x * u * x⁻¹) * x⁻¹⁻¹ = u
    group
  rwa [e] at h

end CFSG.StandardType.TwE6RootAs

end
