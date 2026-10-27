module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanG2QTor
import CFSG.Blueprint.ChevalleyRootArtifact

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Blueprint.Chevalley CFSG.AGLEmbedding.KFactProofs.G2Q

@[expose] noncomputable def g2AdjFixDim {L : Type} [Field L] (x : ModGL .G2 L) : ℕ :=
  Module.finrank L (LinearMap.ker ((x : Module.End L (RootModule .G2 L)) - 1))

theorem g2AdjFixDim_conj {L : Type} [Field L] (g x : ModGL .G2 L) :
    g2AdjFixDim (g * x * g⁻¹) = g2AdjFixDim x := by
  unfold g2AdjFixDim
  have h : LinearMap.ker (((g * x * g⁻¹ : ModGL .G2 L) : Module.End L (RootModule .G2 L)) - 1) =
      (LinearMap.ker ((x : Module.End L (RootModule .G2 L)) - 1)).map
        (g.toLinearEquiv : RootModule .G2 L →ₗ[L] RootModule .G2 L) := by
    ext v
    rw [Submodule.mem_map_equiv, LinearMap.mem_ker, LinearMap.mem_ker]
    have h1 : ((g⁻¹ : ModGL .G2 L) : Module.End L (RootModule .G2 L)) *
        (g : Module.End L (RootModule .G2 L)) = 1 := Units.inv_mul g
    have h2 : (g : Module.End L (RootModule .G2 L)) *
        ((g⁻¹ : ModGL .G2 L) : Module.End L (RootModule .G2 L)) = 1 := Units.mul_inv g
    have hs : g.toLinearEquiv.symm v = ((g⁻¹ : ModGL .G2 L) : Module.End L (RootModule .G2 L)) v :=
      rfl
    rw [hs]
    have e1 : ((g * x * g⁻¹ : ModGL .G2 L) : Module.End L (RootModule .G2 L)) v =
        (g : Module.End L (RootModule .G2 L))
          ((x : Module.End L (RootModule .G2 L))
            (((g⁻¹ : ModGL .G2 L) : Module.End L (RootModule .G2 L)) v)) := rfl
    have e2 : (g : Module.End L (RootModule .G2 L))
        (((g⁻¹ : ModGL .G2 L) : Module.End L (RootModule .G2 L)) v) = v := by
      rw [← Module.End.mul_apply, h2, Module.End.one_apply]
    simp only [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero, e1]
    constructor
    · intro hv
      have := congrArg ((g⁻¹ : ModGL .G2 L) : Module.End L (RootModule .G2 L)) hv
      rw [← Module.End.mul_apply, h1, Module.End.one_apply] at this
      exact this
    · intro hv
      rw [hv, e2]
  rw [h]
  exact LinearEquiv.finrank_map_eq g.toLinearEquiv _

private def longRoot : Fin 6 → (Fin Tag.G2.rank → ℤ) :=
  ![![1, 0], ![-1, 0], ![1, 3], ![-1, -3], ![2, 3], ![-2, -3]]

private theorem longRoot_injective : Function.Injective longRoot := by decide +kernel

private theorem longRoot_isRoot
    (i : Fin 6) : IsRoot .G2 (longRoot i) := by
  fin_cases i <;> exact (g2_root_certificate.1 _).2 (by decide +kernel)

private theorem longRoot_dvd (i : Fin 6) :
    (3 : ℤ) ∣ ∑ j, Tag.G2.cartan ir j * longRoot i j := by
  fin_cases i <;> decide +kernel

theorem eight_le_g2AdjFixDim_tz_one
    {L : Type} [Field L] {ω : Lˣ} (hω : ω ^ 3 = 1) :
    8 ≤ g2AdjFixDim (tz 1 ω : ModGL .G2 L) := by
  classical
  let lab : Fin 2 ⊕ Fin 6 → Label .G2 :=
    Sum.map id (fun i => (⟨longRoot i, longRoot_isRoot i⟩ : {v // IsRoot .G2 v}))
  have hinj : Function.Injective lab :=
    Sum.map_injective.2 ⟨Function.injective_id, fun a b h =>
      longRoot_injective (congrArg Subtype.val h)⟩
  have hfix : ∀ i, ((tz 1 ω : ModGL .G2 L) : Module.End L (RootModule .G2 L))
      (Finsupp.single (lab i) (1 : L)) = Finsupp.single (lab i) 1 := by
    rintro (j | i)
    · have h := torusElt_hVec (τ := .G2) (R := L) ir j ω
      rw [tz_right]
      exact h
    · have hα := longRoot_isRoot i
      have hω' : ((ω ^ (∑ j, Tag.G2.cartan ir j * longRoot i j) : Lˣ) : L) = 1 := by
        obtain ⟨k, hk⟩ := longRoot_dvd i
        rw [hk, zpow_mul]
        simp [hω]
      have h := torusElt_rootVec (τ := .G2) (R := L) ir ω hα
      rw [hω', one_smul] at h
      have e : Finsupp.single (lab (Sum.inr i)) (1 : L) = rootVec .G2 L (longRoot i) :=
        (rootVec_eq_single_of_isRoot hα).symm
      rw [e, tz_right]
      exact h
  have hmem : ∀ i, Finsupp.single (lab i) (1 : L) ∈
      LinearMap.ker (((tz 1 ω : ModGL .G2 L) : Module.End L (RootModule .G2 L)) - 1) := by
    intro i
    rw [LinearMap.mem_ker, LinearMap.sub_apply, hfix i, Module.End.one_apply, sub_self]
  let F : Fin 2 ⊕ Fin 6 → LinearMap.ker
      (((tz 1 ω : ModGL .G2 L) : Module.End L (RootModule .G2 L)) - 1) :=
    fun i => ⟨Finsupp.single (lab i) 1, hmem i⟩
  have hli : LinearIndependent L F := by
    refine LinearIndependent.of_comp (LinearMap.ker _).subtype ?_
    exact (Finsupp.basisSingleOne (R := L) (ι := Label .G2)).linearIndependent.comp lab hinj
  have h8 : Fintype.card (Fin 2 ⊕ Fin 6) = 8 := by simp
  have := hli.fintype_card_le_finrank
  rw [h8] at this
  exact this

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
