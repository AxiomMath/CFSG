module

public import CFSG.Quasithin.Background.SmithB45MatM22
public import CFSG.Quasithin.Background.SmithB45MatIndFlag

public section

namespace CFSG.Quasithin.B45Mat.Ind

open CFSG.QuasithinUnique.Setup.X3E CFSG.Quasithin.H.Mathieu CFSG.Quasithin.B45Mat.M22
  CFSG.CharacterTheory.SteinbergBY CFSG.Monster.Code Module

theorem lin_matOf_eq {n : ℕ} {F : MulAut (Multiplicative (Fin n → ZMod 2))} {f : ℕ → ℕ}
    (hF : ∀ m, F (toW n m) = toW n (f m)) :
    lin n (matOf n f) = Matrix.toLin' (mulAutMat n F) := by
  refine lin_eq_of_toVec fun k => ?_
  rw [matOf, getD_map_range _ _ k.isLt, Matrix.toLin'_apply, mulAutMat_mulVec]
  have h1 : (Multiplicative.ofAdd (Pi.single k 1 : Fin n → ZMod 2)) = toW n (2 ^ k.val) := by
    rw [toW, bvec_two_pow]
  rw [h1, hF]
  rfl

abbrev m22Dim4 : Fin 4 → ℕ := ![1, 10, 10, 34]

@[expose] noncomputable def m22Rep4 :
    ∀ i : Fin 4, G22 →* Matrix (Fin (m22Dim4 i)) (Fin (m22Dim4 i)) (ZMod 2)
  | 0 => rep1
  | 1 => rep10a
  | 2 => rep10b
  | 3 => rep34

theorem m22_binary_small36
    (W : Type) [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (τ : Representation (ZMod 2) G22 W) (hτ : τ.IsIrreducible)
    (hW : finrank (ZMod 2) W ≤ 36) :
    ∃ i, Nonempty (τ.Equiv (matrixBaseChange (RingHom.id (ZMod 2)) (m22Rep4 i))) := by
  refine exists_binary_equiv m22Rep4 (fun i => ?_) 36 (fun U _ _ _ σ hσ hU => ?_) W τ hτ hW
  · fin_cases i
    · exact isIrreducible_rep1 _
    · exact isIrreducible_rep10a _
    · exact isIrreducible_rep10b _
    · exact isIrreducible_rep34 _
  · obtain ⟨-, j, ⟨e⟩⟩ := m22ClosureRep_complete (AlgebraicClosure (ZMod 2)) U σ hσ
    have hdim : finrank (AlgebraicClosure (ZMod 2)) U = m22Dim j := by
      rw [e.toLinearEquiv.finrank_eq, Module.finrank_fin_fun]
    fin_cases j
    · exact ⟨0, ⟨e⟩⟩
    · exact ⟨1, ⟨e⟩⟩
    · exact ⟨2, ⟨e⟩⟩
    · exact ⟨3, ⟨e⟩⟩
    all_goals
      exfalso
      simp only [m22Dim] at hdim
      norm_num [hdim] at hU

theorem isTrivial_of_finrank_le_two {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V] (τ : Representation (ZMod 2) G22 V)
    (hV : finrank (ZMod 2) V ≤ 2) : ∀ g v, τ g v = v := by
  obtain ⟨-, -, hsimp⟩ := CFSG.Sporadic.Mathieu.fam_m22_simplicity
  have hcard : Nat.card G22 = 443520 := CFSG.Sporadic.Mathieu.card_M22
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have hker : τ.asGroupHom.ker = ⊤ := by
    have := τ.asGroupHom.normal_ker
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal τ.asGroupHom.ker with h | h
    · exfalso
      have hinj : Function.Injective τ.asGroupHom := (MonoidHom.ker_eq_bot_iff _).1 h
      have : Finite (V →ₗ[ZMod 2] V) := Finite.of_injective _ DFunLike.coe_injective
      have : Finite (V →ₗ[ZMod 2] V)ˣ := Finite.of_injective _ Units.val_injective
      have h1 : Nat.card G22 ≤ Nat.card (V →ₗ[ZMod 2] V)ˣ := Nat.card_le_card_of_injective _ hinj
      have h2 : Nat.card (V →ₗ[ZMod 2] V)ˣ ≤ Nat.card (V →ₗ[ZMod 2] V) :=
        Nat.card_le_card_of_injective _ Units.val_injective
      have h3 : Nat.card (V →ₗ[ZMod 2] V) ≤ Nat.card (V → V) :=
        Nat.card_le_card_of_injective _ DFunLike.coe_injective
      have h4 : Nat.card V = 2 ^ finrank (ZMod 2) V := by
        rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
      have h5 : Nat.card V ≤ 4 := by
        rw [h4]
        calc 2 ^ finrank (ZMod 2) V ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hV
          _ = 4 := by norm_num
      have h6 : Nat.card (V → V) ≤ 256 := by
        rw [Nat.card_fun]
        have h7 : 0 < Nat.card V := Nat.card_pos
        interval_cases (Nat.card V) <;> norm_num
      omega
    · exact h
  intro g v
  have hg' : g ∈ τ.asGroupHom.ker := hker ▸ Subgroup.mem_top g
  have hg : τ.asGroupHom g = 1 := MonoidHom.mem_ker.1 hg'
  have h1 := congrArg (fun u : (V →ₗ[ZMod 2] V)ˣ => (u : V →ₗ[ZMod 2] V) v) hg
  simpa [Representation.asGroupHom_apply] using h1

theorem mog22_le_mog23 : mog22 ≤ mog23 := inf_le_left

noncomputable abbrev iota22 :
    G22 →* ↥mog23 :=
  (Subgroup.inclusion mog22_le_mog23).comp psiS22

theorem coe_iota22 (g : G22) :
    ((iota22 g : ↥mog23) : Equiv.Perm (Fin 24)) =
      CFSG.Monster.B.TwoA.psiHom (g : Equiv.Perm (Fin 22)) :=
  rfl

end CFSG.Quasithin.B45Mat.Ind
