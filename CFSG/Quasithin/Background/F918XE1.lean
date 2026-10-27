module

public import CFSG.Quasithin.Background.F918X1
public import CFSG.Quasithin.Background.F918X4
public import CFSG.Quasithin.Background.B5FinS8Core
public import CFSG.Quasithin.Background.G64ExtSq
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.Quasithin.F918X

open CFSG.Quasithin CFSG.Assembly.LowTwoRank

@[expose] noncomputable def extSq4Twist :
    Equiv.Perm (Fin 8) →* MulAut (FFModel.extSq (ZMod 2) 4).Mod :=
  (MulAut.congr B5FinS8.G8).toMonoidHom.comp (FFModel.symDn_isActionModel 8).modAct

theorem extSq4Twist_alt (σ : ↥(alternatingGroup (Fin 8))) :
    extSq4Twist (σ : Equiv.Perm (Fin 8)) =
      (FFModel.extSq_isActionModel (ZMod 2) 4).modAct (B5FinS8.alpha σ) := by
  ext y
  change B5FinS8.G8 ((FFModel.symDn_isActionModel 8).modAct (σ : Equiv.Perm (Fin 8))
    (B5FinS8.G8.symm y)) = _
  rw [B5FinS8.G8_modAct, MulEquiv.apply_symm_apply]

theorem extSq4Twist_conj (τ : Equiv.Perm (Fin 8)) (σ σ' : ↥(alternatingGroup (Fin 8)))
    (h : (σ' : Equiv.Perm (Fin 8)) = τ * (σ : Equiv.Perm (Fin 8)) * τ⁻¹) :
    extSq4Twist τ * (FFModel.extSq_isActionModel (ZMod 2) 4).modAct (B5FinS8.alpha σ) *
        (extSq4Twist τ)⁻¹ = (FFModel.extSq_isActionModel (ZMod 2) 4).modAct (B5FinS8.alpha σ') := by
  rw [← extSq4Twist_alt, ← extSq4Twist_alt, h, map_mul, map_mul, map_inv]

theorem alphaA8_bijective : Function.Bijective B5FinS8.alpha :=
  ⟨B5FinS8.slEquiv.symm.injective.comp B5FinS8.alphaHom_bijective.1, B5FinS8.alpha_surjective⟩

theorem extSq4_bijective {V : Type} [CommGroup V] {L : Subgroup (MulAut V)}
    {π : (FFModel.extSq (ZMod 2) 4).Gam →* ↥L}
    (hπ : (FFModel.extSq (ZMod 2) 4).RealizesVia L ⊤ ⊥ π) : Function.Bijective π :=
  ⟨hπ.injective_of_faithful (G64.extSq_faithful (by norm_num)), hπ.1⟩

theorem mem_realized_extSq4 {V : Type} [CommGroup V] {L : Subgroup (MulAut V)}
    {π : (FFModel.extSq (ZMod 2) 4).Gam →* ↥L}
    (hπ : (FFModel.extSq (ZMod 2) 4).RealizesVia L ⊤ ⊥ π) (α : MulAut ↥L) :
    α ∈ realized L := by
  obtain ⟨θ, hθ⟩ := exists_theta_of_bijective (extSq4_bijective hπ) α
  let a : ↥(alternatingGroup (Fin 8)) ≃* ↥(StatedSL 4 (ZMod 2)) :=
    MulEquiv.ofBijective B5FinS8.alpha alphaA8_bijective
  obtain ⟨τ, hτ⟩ := (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 8
    (by norm_num) (by norm_num)).2 (a.trans (θ.trans a.symm))
  refine mem_realized_of_twist (FFModel.extSq_isActionModel (ZMod 2) 4) hπ α θ hθ
    (extSq4Twist τ) (fun γ => ?_)
  obtain ⟨σ, rfl⟩ := alphaA8_bijective.2 γ
  have h1 := congrArg (fun e : MulAut ↥(alternatingGroup (Fin 8)) =>
    ((e σ : ↥(alternatingGroup (Fin 8))) : Equiv.Perm (Fin 8))) hτ
  simp only [MulAut.conjNormal_apply] at h1
  have h2 : θ (B5FinS8.alpha σ) = B5FinS8.alpha ((a.trans (θ.trans a.symm)) σ) := by
    show θ (a σ) = a (a.symm (θ (a σ)))
    exact (a.apply_symm_apply _).symm
  rw [h2]
  exact extSq4Twist_conj τ σ _ h1.symm

theorem case10Twist_holds : Case10Twist := by
  intro V _ _ _ G L A _ h10
  obtain ⟨π, hπ⟩ := h10.1
  refine ⟨stableMod_of_forall fun α => mem_realized_extSq4 hπ α, Or.inr (Or.inl ?_)⟩
  exact Or.inr (Or.inl ⟨ZMod 2, inferInstance, inferInstance, Nat.card_zmod 2,
    ⟨(MulEquiv.ofBijective π (extSq4_bijective hπ)).symm⟩⟩)

end CFSG.Quasithin.F918X
