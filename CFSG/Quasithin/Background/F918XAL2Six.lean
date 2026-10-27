module

public import CFSG.Quasithin.Background.F918X3
public import CFSG.Quasithin.Background.F918X1
public import CFSG.Quasithin.Background.Sp4InfAut6
public import CFSG.Quasithin.Background.F918XAL2Basic
public import CFSG.Quasithin.Background.B4ModelsAction

public section

namespace CFSG.Quasithin.F918X

open CFSG.Quasithin

namespace AL2

@[expose] noncomputable def permModAut (n : ℕ) :
    Equiv.Perm (Fin n) →* MulAut (FFModel.altDn n).Mod :=
  (FFModel.symDn_isActionModel n).modAct

theorem modAct_altDn_eq (n : ℕ) (γ : ↥(alternatingGroup (Fin n))) :
    (FFModel.altDn_isActionModel n).modAct γ = permModAut n (γ : Equiv.Perm (Fin n)) := rfl

theorem permModAut_conj (n : ℕ) (τ : Equiv.Perm (Fin n)) (θ : MulAut ↥(alternatingGroup (Fin n)))
    (hθ : ∀ γ : ↥(alternatingGroup (Fin n)),
      ((θ γ : ↥(alternatingGroup (Fin n))) : Equiv.Perm (Fin n)) = τ * γ * τ⁻¹)
    (γ : ↥(alternatingGroup (Fin n))) :
    permModAut n τ * (FFModel.altDn_isActionModel n).modAct γ * (permModAut n τ)⁻¹ =
      (FFModel.altDn_isActionModel n).modAct (θ γ) := by
  rw [modAct_altDn_eq, modAct_altDn_eq, ← map_inv, ← map_mul, ← map_mul, hθ]

theorem mem_realized_conj {V : Type} [CommGroup V] {L : Subgroup (MulAut V)} {n : ℕ}
    {π : ↥(alternatingGroup (Fin n)) →* ↥L} (hπ : (FFModel.altDn n).RealizesVia L ⊤ ⊥ π)
    (e : ↥(alternatingGroup (Fin n)) ≃* ↥L) (he : ∀ γ, e γ = π γ) (τ : Equiv.Perm (Fin n))
    (θ : MulAut ↥(alternatingGroup (Fin n)))
    (hθ : ∀ γ : ↥(alternatingGroup (Fin n)),
      ((θ γ : ↥(alternatingGroup (Fin n))) : Equiv.Perm (Fin n)) = τ * γ * τ⁻¹) :
    MulAut.congr e θ ∈ realized L := by
  have key : ∀ γ : ↥(alternatingGroup (Fin n)), (MulAut.congr e θ) (π γ) = π (θ γ) := by
    intro γ
    rw [← he γ, ← he (θ γ)]
    simp [MulAut.congr_apply]
  exact mem_realized_of_twist (FFModel.altDn_isActionModel n) hπ _ θ key
    (permModAut n τ) (permModAut_conj n τ θ hθ)

end AL2

theorem case6Twist_holds : Case6Twist := by
  intro V _ _ _ G L A hHyp hcase
  obtain ⟨-, -, hq, -⟩ := hHyp
  obtain ⟨-, ⟨π, hπ⟩, -⟩ := hcase
  have hs : IsSimpleGroup ↥(alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have hbij : Function.Bijective (π : ↥(alternatingGroup (Fin 6)) →* ↥L) :=
    AL2.bijective_of_surjective_of_quasisimple (A := ↥(alternatingGroup (Fin 6))) hq π hπ.1
  let e : ↥(alternatingGroup (Fin 6)) ≃* ↥L := MulEquiv.ofBijective π hbij
  refine ⟨?_, Or.inl (AL2.center_eq_bot_of_mulEquiv e (alternatingGroup.center_eq_bot (by simp)))⟩
  have hle : Sp4Inf.conjAlt6.range.map
      (MulAut.congr e : MulAut ↥(alternatingGroup (Fin 6)) →* MulAut ↥L) ≤ realized L := by
    rintro _ ⟨_, ⟨τ, rfl⟩, rfl⟩
    exact AL2.mem_realized_conj hπ e (fun γ => rfl) τ (Sp4Inf.conjAlt6 τ)
      (fun γ => Sp4Inf.coe_conjAlt6 τ γ)
  have hdvd := Subgroup.index_dvd_of_le hle
  rw [Subgroup.index_map_equiv, Sp4Inf.index_range_conjAlt6] at hdvd
  exact Nat.le_of_dvd (by norm_num) hdvd

end CFSG.Quasithin.F918X
