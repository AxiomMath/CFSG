module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaCovers
public import CFSG.Quasithin.Background.B5FinTransport
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Sp4TwoNat

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open CFSG.Quasithin
open scoped Matrix

theorem exists_statedOmegaMinus_natTransport {K₁ K₂ : Type} [Field K₁] [Field K₂] [Finite K₁]
    [Finite K₂] (hcard : Nat.card K₁ = Nat.card K₂) (m : ℕ) {b₁ c₁ : K₁} {b₂ c₂ : K₂}
    (hirr₁ : ∀ s : K₁, s ^ 2 + b₁ * s + c₁ ≠ 0) (hirr₂ : ∀ s : K₂, s ^ 2 + b₂ * s + c₂ ≠ 0) :
    ∃ (χ : StatedOmega (StatedQuadMinus m K₁ b₁ c₁) ≃* StatedOmega (StatedQuadMinus m K₂ b₂ c₂))
      (B : Multiplicative (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K₁) ≃*
        Multiplicative (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K₂)),
      ∀ γ x, B (natAct (StatedOmega (StatedQuadMinus m K₁ b₁ c₁)) γ x) =
        natAct (StatedOmega (StatedQuadMinus m K₂ b₂ c₂)) (χ γ) (B x) := by
  classical
  obtain ⟨σ, -⟩ : ∃ σ : K₁ ≃+* K₂, True :=
    ⟨CFSG.ClassicalInvolution.Upgrade.fieldIsoOfCard hcard, trivial⟩
  obtain ⟨g, hg⟩ := CFSG.SeitzReduction.F4Pilot.exists_gl_isometry_statedQuadMinus m
    (CFSG.ClassicalInvolution.Upgrade.irreducible_map σ hirr₁) hirr₂
  obtain ⟨χ, hχ⟩ : ∃ χ : StatedOmega (StatedQuadMinus m K₁ b₁ c₁) ≃*
      StatedOmega (StatedQuadMinus m K₂ b₂ c₂), ∀ γ,
      ((χ γ : StatedOmega (StatedQuadMinus m K₂ b₂ c₂)) :
        GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K₂) =
        g * CFSG.Adapters.RankTwoModelTransports.glCongr σ
          (γ : GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K₁) * g⁻¹ :=
    ⟨(((CFSG.Adapters.RankTwoModelTransports.glCongr σ).subgroupMap _).trans
        (MulEquiv.subgroupCongr (CFSG.ClassicalInvolution.Upgrade.map_statedOmega σ
          (CFSG.ClassicalInvolution.Upgrade.statedQuadMinus_comp σ rfl rfl)))).trans
      (((MulAut.conj g).subgroupMap _).trans (MulEquiv.subgroupCongr
        (CFSG.ClassicalInvolution.Upgrade.map_statedOmega_conj g hg))), fun _ => rfl⟩
  let Bv : (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K₁) ≃+ (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K₂) :=
    (AddEquiv.piCongrRight fun _ => σ.toAddEquiv).trans
      (Matrix.toLinearEquiv' ((g : GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K₂) :
        Matrix (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K₂)
        (Units.invertible g)).toAddEquiv
  have hBv : ∀ v, Bv v = ((g : GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K₂) :
      Matrix (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K₂) *ᵥ
        (fun i => σ (v i)) := fun _ => rfl
  refine ⟨χ, Bv.toMultiplicative, fun γ x => ?_⟩
  apply Multiplicative.toAdd.injective
  change Bv ((((γ : StatedOmega (StatedQuadMinus m K₁ b₁ c₁)) :
        GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K₁) :
        Matrix (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K₁) *ᵥ
      Multiplicative.toAdd x) =
    (((χ γ : StatedOmega (StatedQuadMinus m K₂ b₂ c₂)) :
        GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K₂) :
        Matrix (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K₂) *ᵥ
      Bv (Multiplicative.toAdd x)
  have hmv : ∀ (M : Matrix (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2)
      (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K₁) (v : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K₁),
      (fun i => σ ((M *ᵥ v) i)) = (M.map σ) *ᵥ (fun i => σ (v i)) :=
    fun M v => funext fun i => RingHom.map_mulVec (σ : K₁ →+* K₂) M v i
  have hgg : ∀ y : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K₂,
      ((g⁻¹ : GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K₂) :
        Matrix (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K₂) *ᵥ
        (((g : GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K₂) :
          Matrix (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K₂) *ᵥ y)
        = y := fun y => by rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  rw [hBv, hBv, hχ, hmv, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, hgg, CFSG.Adapters.RankTwoModelTransports.glCongr_coe]

theorem isoMod_of_realizesVia_nat_intertwine {W : Type} [CommGroup W] {ι₁ ι₂ : Type}
    [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂] {K₁ K₂ : Type} [Field K₁]
    [Field K₂] {Γ₁ : Subgroup (GL ι₁ K₁)} {Γ₂ : Subgroup (GL ι₂ K₂)}
    {H : Subgroup (MulAut W)} {U₁ U₂ : Subgroup W} {π₁ : ↥Γ₁ →* ↥H} {π₂ : ↥Γ₂ →* ↥H}
    (h₁ : (FFModel.nat Γ₁).RealizesVia H U₁ ⊥ π₁) (h₂ : (FFModel.nat Γ₂).RealizesVia H U₂ ⊥ π₂)
    (φ : ↥Γ₁ →* ↥Γ₂) (hφ : Function.Surjective φ) (hπ : π₂.comp φ = π₁)
    (A : Multiplicative (ι₁ → K₁) ≃* Multiplicative (ι₂ → K₂))
    (hA : ∀ γ x, A (natAct Γ₁ γ x) = natAct Γ₂ (φ γ) (A x)) :
    CFSG.Quasithin.H.Pair.IsoMod H U₁ U₂ := by
  let Ê : ↥(FFModel.nat Γ₁).sec →* ↥(FFModel.nat Γ₂).sec :=
    { toFun := fun m => ⟨A m.1, Subgroup.mem_top _⟩
      map_one' := Subtype.ext (map_one A)
      map_mul' := fun a b => Subtype.ext (map_mul A a.1 b.1) }
  have hÊ : Function.Surjective Ê := fun m =>
    ⟨⟨A.symm m.1, Subgroup.mem_top _⟩, Subtype.ext (A.apply_symm_apply m.1)⟩
  have h₂' := FFModel.RealizesVia.of_surjHom (FFModel.nat_isActionModel Γ₁) h₂ φ hφ Ê hÊ
    (fun σ m _ => hA σ m.1) (fun m =>
      (Subgroup.mem_bot.trans (MulEquiv.map_eq_one_iff A)).trans Subgroup.mem_bot.symm)
  subst hπ
  exact Inputs1719.pair_isoMod_of_realizesVia_common h₁ h₂'

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
