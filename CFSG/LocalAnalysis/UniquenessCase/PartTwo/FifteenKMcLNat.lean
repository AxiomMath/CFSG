module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKMcLDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.McLaughlinTypesForms
public import CFSG.Quasithin.Background.B4Models

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.HardMathSupport.Solomon.Coordinator

theorem s15k_mcl_realizes_nat {W : Type} [CommGroup W] {J : Subgroup (MulAut W)}
    {R : Subgroup W} (D : McRep J R) {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι (ZMod 2) D.V) (Γ : Subgroup (Matrix.GeneralLinearGroup ι (ZMod 2)))
    (hΓ : D.ρ.range.map (mclt_glMatrixEquiv b).toMonoidHom = Γ) :
    (FFModel.nat Γ).Realizes J R ⊥ := by
  classical
  let f : ↥J →* Matrix.GeneralLinearGroup ι (ZMod 2) :=
    (mclt_glMatrixEquiv b).toMonoidHom.comp D.ρ
  have hf : Function.Injective f := (mclt_glMatrixEquiv b).injective.comp D.inj
  have hrange : f.range = Γ := by
    rw [← hΓ]
    exact (MonoidHom.map_range _ _).symm
  let Φ : ↥J ≃* ↥Γ := (MonoidHom.ofInjective hf).trans (MulEquiv.subgroupCongr hrange)
  have hΦ : ∀ j : ↥J, ((Φ j : ↥Γ) : Matrix.GeneralLinearGroup ι (ZMod 2)) =
      mclt_glMatrixEquiv b (D.ρ j) := fun j => rfl
  have hπ : ∀ γ : ↥Γ, mclt_glMatrixEquiv b (D.ρ (Φ.symm γ)) =
      (γ : Matrix.GeneralLinearGroup ι (ZMod 2)) := by
    intro γ
    rw [← hΦ, MulEquiv.apply_symm_apply]
  let φ : Multiplicative D.V →* Multiplicative (ι → ZMod 2) :=
    AddMonoidHom.toMultiplicative b.equivFun.toLinearMap.toAddMonoidHom
  have hφ : ∀ x, Multiplicative.toAdd (φ x) = b.equivFun (Multiplicative.toAdd x) := fun x => rfl
  have hφinj : Function.Injective φ := fun x y hxy => by
    apply Multiplicative.toAdd.injective
    apply b.equivFun.injective
    rw [← hφ, ← hφ, hxy]
  have key : ∃ β : ↥R →* ↥(⊤ : Subgroup (Multiplicative (ι → ZMod 2))) ⧸
      (⊥ : Subgroup (Multiplicative (ι → ZMod 2))).subgroupOf ⊤,
      Function.Surjective β ∧ (∀ u : ↥R, β u = 1 ↔ (u : W) ∈ (⊥ : Subgroup W)) ∧
      ∀ (γ : ↥Γ) (u : ↥R) (m : ↥(⊤ : Subgroup (Multiplicative (ι → ZMod 2))))
        (hu : ((Φ.symm γ : ↥J) : MulAut W) (u : W) ∈ R)
        (hm : natAct Γ γ (m : Multiplicative (ι → ZMod 2)) ∈
          (⊤ : Subgroup (Multiplicative (ι → ZMod 2)))),
        β u = QuotientGroup.mk m →
          β ⟨((Φ.symm γ : ↥J) : MulAut W) (u : W), hu⟩ =
            QuotientGroup.mk ⟨natAct Γ γ (m : Multiplicative (ι → ZMod 2)), hm⟩ := by
    let β : ↥R →* ↥(⊤ : Subgroup (Multiplicative (ι → ZMod 2))) ⧸
        (⊥ : Subgroup (Multiplicative (ι → ZMod 2))).subgroupOf ⊤ :=
      (QuotientGroup.mk' _).comp ((Subgroup.topEquiv.symm.toMonoidHom).comp
        (φ.comp D.e.toMonoidHom))
    have hβ : ∀ u : ↥R, β u = QuotientGroup.mk (Subgroup.topEquiv.symm (φ (D.e u))) :=
      fun u => rfl
    refine ⟨β, ?_, ?_, ?_⟩
    · intro q
      induction q using QuotientGroup.induction_on with
      | H x =>
        refine ⟨D.e.symm (Multiplicative.ofAdd (b.equivFun.symm (Multiplicative.toAdd x.1))), ?_⟩
        rw [hβ]
        congr 1
        apply Subtype.ext
        change φ (D.e (D.e.symm _)) = (x : Multiplicative (ι → ZMod 2))
        rw [MulEquiv.apply_symm_apply]
        apply Multiplicative.toAdd.injective
        rw [hφ, toAdd_ofAdd, LinearEquiv.apply_symm_apply]
    · intro u
      have h1 : β u = 1 ↔ φ (D.e u) = 1 := by
        rw [hβ]
        change (QuotientGroup.mk (Subgroup.topEquiv.symm (φ (D.e u))) :
          ↥(⊤ : Subgroup (Multiplicative (ι → ZMod 2))) ⧸ _) = 1 ↔ _
        rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.mem_bot]
        rfl
      have h2 : φ (D.e u) = 1 ↔ u = 1 := by
        rw [← map_one φ, hφinj.eq_iff, ← map_one D.e, D.e.injective.eq_iff]
      rw [h1, h2, Subgroup.mem_bot]
      exact ⟨fun h => by rw [h]; rfl, fun h => Subtype.ext h⟩
    · intro γ u m hu hm hβm
      rw [hβ] at hβm
      have hm' : (m : Multiplicative (ι → ZMod 2)) = φ (D.e u) := by
        have h0 := QuotientGroup.eq.mp hβm
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_bot] at h0
        exact (inv_mul_eq_one.mp h0).symm
      rw [hβ]
      congr 1
      apply Subtype.ext
      change φ (D.e ⟨(Φ.symm γ : MulAut W) u, hu⟩) = natAct Γ γ (m : Multiplicative (ι → ZMod 2))
      rw [hm', D.hρ (Φ.symm γ) u hu]
      apply Multiplicative.toAdd.injective
      rw [hφ, toAdd_ofAdd]
      change _ = Multiplicative.toAdd (Multiplicative.ofAdd
        (((γ : Matrix.GeneralLinearGroup ι (ZMod 2)) : Matrix ι ι (ZMod 2)).mulVec
          (Multiplicative.toAdd (φ (D.e u)))))
      rw [toAdd_ofAdd, hφ, ← hπ γ, mclt_glMatrixEquiv_mulVec]
  refine ⟨Φ.symm.toMonoidHom, ?_⟩
  unfold FFModel.RealizesVia
  refine ⟨Φ.symm.surjective, bot_le, bot_le, fun h u hu => D.stable (h : MulAut W) h.2 u hu,
    ?_, fun γ m hm => Subgroup.mem_top _, ?_, key⟩
  · intro h z hz
    rw [Subgroup.mem_bot] at hz ⊢
    rw [hz]
    exact map_one (h : MulAut W)
  · show ∀ (γ : ↥Γ) (m : Multiplicative (ι → ZMod 2)),
      m ∈ (⊥ : Subgroup (Multiplicative (ι → ZMod 2))) →
        natAct Γ γ m ∈ (⊥ : Subgroup (Multiplicative (ι → ZMod 2)))
    intro γ m hm
    rw [Subgroup.mem_bot] at hm ⊢
    subst hm
    simp [natAct]

theorem s15k_mcl_top {W : Type} [CommGroup W] {J : Subgroup (MulAut W)} {R : Subgroup W}
    (D : McRep J R) (h2 : 2 ≤ Module.finrank (ZMod 2) D.V) (h : D.ρ.range = ⊤) :
    ∃ n : ℕ, 2 ≤ n ∧ BinaryNaturalSL J R ⊥ n 1 := by
  refine ⟨Module.finrank (ZMod 2) D.V, h2, ZMod 2, inferInstance, inferInstance, by simp, ?_⟩
  refine s15k_mcl_realizes_nat D (Module.finBasisOfFinrankEq (ZMod 2) D.V rfl)
    (CFSG.Open.StatedSL (Module.finrank (ZMod 2) D.V) (ZMod 2)) ?_
  rw [h, mclt_statedSL_eq_top]
  exact Subgroup.map_top_of_surjective _ (mclt_glMatrixEquiv _).surjective

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
