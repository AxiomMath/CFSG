module

public import CFSG.Quasithin.Background.F918Z0Def
public import CFSG.Quasithin.Background.F918Z5BDens

public section

namespace CFSG.Quasithin.SwapModel

open scoped Matrix

section Model

variable {V : Type} [CommGroup V] {G : Type} [AddCommGroup G]

@[expose] def matAut (β : V ≃* Multiplicative G) (s : MulAut V) : G ≃+ G where
  toFun M := Multiplicative.toAdd (β (s (β.symm (Multiplicative.ofAdd M))))
  invFun M := Multiplicative.toAdd (β (s.symm (β.symm (Multiplicative.ofAdd M))))
  left_inv M := by simp
  right_inv M := by simp
  map_add' M N := by simp [ofAdd_add]

theorem matAut_apply (β : V ≃* Multiplicative G) (s : MulAut V) (v : V) :
    matAut β s (Multiplicative.toAdd (β v)) = Multiplicative.toAdd (β (s v)) := by
  simp [matAut]

end Model

section Relations

variable {V : Type} [CommGroup V] {D X : Subgroup (MulAut V)} {F : Type} [Field F] {d r : ℕ}
  {β : V ≃* Multiplicative (Matrix (Fin d) (Fin r) F)}
  {ρ : ↥D →* Matrix.GeneralLinearGroup (Fin d) F}
  {σ : ↥X →* Matrix.GeneralLinearGroup (Fin r) F}

theorem matAut_mul_left (hM : IsMatModel D X β ρ σ) (s : MulAut V) (g : ↥D) (x : ↥X)
    (hgx : s * (g : MulAut V) = (x : MulAut V) * s) (M : Matrix (Fin d) (Fin r) F) :
    matAut β s ((ρ g : Matrix (Fin d) (Fin d) F) * M) =
      matAut β s M * ((σ x : Matrix (Fin r) (Fin r) F))ᵀ := by
  obtain ⟨v, rfl⟩ : ∃ v, Multiplicative.toAdd (β v) = M :=
    ⟨β.symm (Multiplicative.ofAdd M), by simp⟩
  have h1 : (ρ g : Matrix (Fin d) (Fin d) F) * Multiplicative.toAdd (β v) =
      Multiplicative.toAdd (β ((g : MulAut V) v)) := by
    rw [hM.hρ g v, toAdd_ofAdd]
  have h2 : s ((g : MulAut V) v) = (x : MulAut V) (s v) := by
    have := congrArg (fun t : MulAut V => t v) hgx
    simpa using this
  rw [h1, matAut_apply, h2, hM.hσ x (s v), toAdd_ofAdd, matAut_apply]

theorem matAut_mul_left_of_normalizes (hM : IsMatModel D X β ρ σ) (a : MulAut V) (g g' : ↥D)
    (hgg : a * (g : MulAut V) = (g' : MulAut V) * a) (M : Matrix (Fin d) (Fin r) F) :
    matAut β a ((ρ g : Matrix (Fin d) (Fin d) F) * M) =
      (ρ g' : Matrix (Fin d) (Fin d) F) * matAut β a M := by
  obtain ⟨v, rfl⟩ : ∃ v, Multiplicative.toAdd (β v) = M :=
    ⟨β.symm (Multiplicative.ofAdd M), by simp⟩
  have h1 : (ρ g : Matrix (Fin d) (Fin d) F) * Multiplicative.toAdd (β v) =
      Multiplicative.toAdd (β ((g : MulAut V) v)) := by
    rw [hM.hρ g v, toAdd_ofAdd]
  have h2 : a ((g : MulAut V) v) = (g' : MulAut V) (a v) := by
    have := congrArg (fun t : MulAut V => t v) hgg
    simpa using this
  rw [h1, matAut_apply, h2, hM.hρ g' (a v), toAdd_ofAdd, matAut_apply]

theorem closure_rho_eq_top (hd : 0 < d) (hM : IsMatModel D X β ρ σ) :
    AddSubgroup.closure (Set.range fun g : ↥D =>
      ((ρ g : Matrix.GeneralLinearGroup (Fin d) F) : Matrix (Fin d) (Fin d) F)) = ⊤ := by
  refine SqModel.closure_eq_top_of_irr_of_comm hd ⟨1, by simp⟩ ?_ ?_ ?_
  · rintro _ ⟨g, rfl⟩ _ ⟨h, rfl⟩
    exact ⟨g * h, by simp⟩
  · intro W hW
    exact hM.I_irr W fun g w hw => hW _ ⟨g, rfl⟩ w hw
  · intro φ hφ
    exact hM.comm_F φ fun g w => hφ _ ⟨g, rfl⟩ w

end Relations

end CFSG.Quasithin.SwapModel
