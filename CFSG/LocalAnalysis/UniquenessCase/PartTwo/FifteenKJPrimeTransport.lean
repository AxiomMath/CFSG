module

public import CFSG.Quasithin.Background.B5FinTransport
public import CFSG.Adapters.RankTwoModelTransports
import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Quasithin.Background.B4ModelsAction

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Adapters.RankTwoModelTransports

theorem s15k_jp_nat_transport {W : Type} [CommGroup W] {ι : Type} [Fintype ι] [DecidableEq ι]
    {K L : Type} [Field K] [Field L] (φ : K ≃+* L)
    {ΓK : Subgroup (Matrix.GeneralLinearGroup ι K)}
    {ΓL : Subgroup (Matrix.GeneralLinearGroup ι L)}
    (hΓ : ΓK.map (glCongr (ι := ι) φ).toMonoidHom = ΓL)
    {J : Subgroup (MulAut W)} {R Z : Subgroup W} (h : (FFModel.nat ΓK).Realizes J R Z) :
    (FFModel.nat ΓL).Realizes J R Z := by
  obtain ⟨π, hπ⟩ := h
  let t : ↥ΓK ≃* ↥ΓL :=
    ((glCongr (ι := ι) φ).subgroupMap ΓK).trans (MulEquiv.subgroupCongr hΓ)
  have ht : ∀ x : ↥ΓK, ((t x : ↥ΓL) : Matrix.GeneralLinearGroup ι L) =
      glCongr (ι := ι) φ (x : Matrix.GeneralLinearGroup ι K) := fun x => rfl
  let θ : ↥ΓL →* ↥ΓK := t.symm.toMonoidHom
  have hθ : Function.Surjective θ := t.symm.surjective
  have hθt : ∀ σ : ↥ΓL, glCongr (ι := ι) φ ((θ σ : ↥ΓK) : Matrix.GeneralLinearGroup ι K) =
      (σ : Matrix.GeneralLinearGroup ι L) := by
    intro σ
    rw [← ht]
    exact congrArg Subtype.val (t.apply_symm_apply σ)
  let ε : Multiplicative (ι → L) →* Multiplicative (ι → K) :=
    AddMonoidHom.toMultiplicative (AddMonoidHom.compLeft (φ.symm : L →+ K) ι)
  have hε : ∀ m : Multiplicative (ι → L), Multiplicative.toAdd (ε m) =
      φ.symm ∘ Multiplicative.toAdd m := fun m => rfl
  let Ê : ↥(⊤ : Subgroup (Multiplicative (ι → L))) →* ↥(⊤ : Subgroup (Multiplicative (ι → K))) :=
    (ε.comp (⊤ : Subgroup (Multiplicative (ι → L))).subtype).codRestrict ⊤ (fun _ => trivial)
  have hÊs : Function.Surjective Ê := by
    intro y
    refine ⟨⟨Multiplicative.ofAdd (φ ∘ Multiplicative.toAdd (y : Multiplicative (ι → K))),
      trivial⟩, Subtype.ext ?_⟩
    apply Multiplicative.toAdd.injective
    funext i
    show φ.symm (φ (Multiplicative.toAdd (y : Multiplicative (ι → K)) i)) = _
    exact φ.symm_apply_apply _
  have hact : ∀ (σ : ↥ΓL) (m : ↥(⊤ : Subgroup (Multiplicative (ι → L))))
      (hm : natAct ΓL σ (m : Multiplicative (ι → L)) ∈ (⊤ : Subgroup (Multiplicative (ι → L)))),
      ((Ê ⟨natAct ΓL σ (m : Multiplicative (ι → L)), hm⟩ :
        ↥(⊤ : Subgroup (Multiplicative (ι → K)))) : Multiplicative (ι → K)) =
        natAct ΓK (θ σ) ((Ê m : ↥(⊤ : Subgroup (Multiplicative (ι → K)))) :
          Multiplicative (ι → K)) := by
    intro σ m hm
    apply Multiplicative.toAdd.injective
    show φ.symm ∘ ((((σ : Matrix.GeneralLinearGroup ι L) : Matrix ι ι L)).mulVec
      (Multiplicative.toAdd (m : Multiplicative (ι → L)))) =
      (((θ σ : ↥ΓK) : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K).mulVec
        (φ.symm ∘ Multiplicative.toAdd (m : Multiplicative (ι → L)))
    have h1 := CFSG.ClassicalInvolution.Upgrade.glCongr_mulVec φ
      ((θ σ : ↥ΓK) : Matrix.GeneralLinearGroup ι K)
      (φ.symm ∘ Multiplicative.toAdd (m : Multiplicative (ι → L)))
    rw [hθt σ] at h1
    have h2 : φ ∘ (φ.symm ∘ Multiplicative.toAdd (m : Multiplicative (ι → L))) =
        Multiplicative.toAdd (m : Multiplicative (ι → L)) := by
      funext i
      exact φ.apply_symm_apply _
    rw [h2] at h1
    rw [h1]
    funext i
    exact φ.symm_apply_apply _
  have hker : ∀ m : ↥(⊤ : Subgroup (Multiplicative (ι → L))),
      ((Ê m : ↥(⊤ : Subgroup (Multiplicative (ι → K)))) : Multiplicative (ι → K)) ∈
        (⊥ : Subgroup (Multiplicative (ι → K))) ↔
      (m : Multiplicative (ι → L)) ∈ (⊥ : Subgroup (Multiplicative (ι → L))) := by
    intro m
    show Multiplicative.ofAdd (φ.symm ∘ Multiplicative.toAdd (m : Multiplicative (ι → L))) ∈
        (⊥ : Subgroup (Multiplicative (ι → K))) ↔ (m : Multiplicative (ι → L)) ∈
        (⊥ : Subgroup (Multiplicative (ι → L)))
    rw [Subgroup.mem_bot, Subgroup.mem_bot]
    constructor
    · intro h0
      have h3 := congrArg Multiplicative.toAdd h0
      apply Multiplicative.toAdd.injective
      funext i
      have h4 := congrFun h3 i
      exact φ.symm.injective (by simpa using h4)
    · intro h0
      rw [h0]
      apply Multiplicative.toAdd.injective
      funext i
      simp
  exact ⟨π.comp θ, FFModel.RealizesVia.of_surjHom (FFModel.nat_isActionModel ΓL) hπ θ hθ Ê hÊs
    hact hker⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
