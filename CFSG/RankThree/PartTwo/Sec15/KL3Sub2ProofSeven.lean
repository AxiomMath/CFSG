module

public import Mathlib.FieldTheory.Finiteness
public import Mathlib.GroupTheory.PGroup
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Tactic.NormNum.Prime

public section

namespace CFSG.RankThree.PartTwo.Sec15

namespace KL3Sub2Proof

open Matrix

theorem dvd_three_of_pow_mod_seven {k : ℕ} (h : 25 ^ k % 7 = 1) : k % 3 = 0 := by
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 3 ∧ k = 3 * q + r :=
    ⟨k / 3, k % 3, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod k 3).symm⟩
  rw [pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod] at h
  norm_num at h
  interval_cases r <;> simp_all

variable {K : Type} [Field K] [Finite K]

theorem card_modEq_card_fixed {p : ℕ} [Fact p.Prime] {x : GL (Fin 3) K} (hx : orderOf x = p)
    (W : Submodule K (Fin 3 → K)) (hW : ∀ w ∈ W, (x : Matrix (Fin 3) (Fin 3) K) *ᵥ w ∈ W) :
    Nat.card W ≡ Nat.card {w : W // (x : Matrix (Fin 3) (Fin 3) K) *ᵥ (w : Fin 3 → K) = w}
      [MOD p] := by
  classical
  set Z := Subgroup.zpowers x with hZ
  have hZp : IsPGroup p Z := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  have hfin : IsOfFinOrder x := orderOf_pos_iff.mp (by rw [hx]; exact (Fact.out : p.Prime).pos)
  have hpow : ∀ n : ℕ, ∀ w ∈ W, ((x ^ n : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w ∈ W := by
    intro n
    induction n with
    | zero => intro w hw; simpa using hw
    | succ n ih =>
      intro w hw
      rw [pow_succ, Units.val_mul, ← Matrix.mulVec_mulVec]
      exact ih _ (hW w hw)
  have hZW : ∀ g : Z, ∀ w ∈ W, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w ∈ W := by
    rintro ⟨g, hg⟩ w hw
    rw [hZ, ← hfin.mem_powers_iff_mem_zpowers] at hg
    obtain ⟨n, rfl⟩ := hg
    exact hpow n w hw
  let _ : MulAction Z W :=
    { smul := fun g w => ⟨((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w, hZW g w w.2⟩
      one_smul := fun w => Subtype.ext (by
        show ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ (w : Fin 3 → K) = w
        simp)
      mul_smul := fun g g' w => Subtype.ext (by
        show (((g * g' : Z) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ (w : Fin 3 → K) =
          ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
            (((g' : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ (w : Fin 3 → K))
        rw [Matrix.mulVec_mulVec]
        rfl) }
  have hmod := hZp.card_modEq_card_fixedPoints W
  have hfix : Nat.card (MulAction.fixedPoints Z W) =
      Nat.card {w : W // (x : Matrix (Fin 3) (Fin 3) K) *ᵥ (w : Fin 3 → K) = w} := by
    apply Nat.card_congr
    refine Equiv.subtypeEquivRight fun w => ?_
    constructor
    · intro h
      have := congrArg Subtype.val (h ⟨x, Subgroup.mem_zpowers x⟩)
      exact this
    · intro h g
      have hxn : ∀ n : ℕ,
          ((x ^ n : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ (w : Fin 3 → K) = w := by
        intro n
        induction n with
        | zero => simp
        | succ n ih => rw [pow_succ, Units.val_mul, ← Matrix.mulVec_mulVec, h, ih]
      obtain ⟨g, hg⟩ := g
      rw [hZ, ← hfin.mem_powers_iff_mem_zpowers] at hg
      obtain ⟨n, rfl⟩ := hg
      exact Subtype.ext (hxn n)
  rw [hfix] at hmod
  exact hmod

theorem irreducible_of_orderOf_eq_seven (hK : Nat.card K = 25) {x : GL (Fin 3) K}
    (hx : orderOf x = 7) (W : Submodule K (Fin 3 → K))
    (hW : ∀ w ∈ W, (x : Matrix (Fin 3) (Fin 3) K) *ᵥ w ∈ W) : W = ⊥ ∨ W = ⊤ := by
  classical
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let F : Submodule K (Fin 3 → K) :=
    { carrier := {v | (x : Matrix (Fin 3) (Fin 3) K) *ᵥ v = v}
      add_mem' := fun {v w} hv hw => by
        simp only [Set.mem_ofPred_eq] at hv hw ⊢
        rw [Matrix.mulVec_add, hv, hw]
      zero_mem' := by simp
      smul_mem' := fun c v hv => by
        simp only [Set.mem_ofPred_eq] at hv ⊢
        rw [Matrix.mulVec_smul, hv] }
  have hdim : ∀ U : Submodule K (Fin 3 → K), Nat.card U = 25 ^ Module.finrank K U := by
    intro U
    rw [Module.natCard_eq_pow_finrank (K := K) (V := U), hK]
  have hle3 : ∀ U : Submodule K (Fin 3 → K), Module.finrank K U ≤ 3 := fun U => by
    have := Submodule.finrank_le U
    rwa [Module.finrank_fin_fun] at this
  have hF : F = ⊥ := by
    have hmod := card_modEq_card_fixed hx ⊤ (fun w _ => Submodule.mem_top)
    have h1 : Nat.card {w : (⊤ : Submodule K (Fin 3 → K)) //
        (x : Matrix (Fin 3) (Fin 3) K) *ᵥ (w : Fin 3 → K) = w} = Nat.card F :=
      Nat.card_congr
        { toFun := fun w => ⟨w.1.1, w.2⟩
          invFun := fun v => ⟨⟨v.1, Submodule.mem_top⟩, v.2⟩
          left_inv := fun w => rfl
          right_inv := fun v => rfl }
    rw [h1, hdim, hdim, finrank_top, Module.finrank_fin_fun] at hmod
    have h3 : (25 ^ Module.finrank K F) % 7 = 1 := by
      have := hmod.symm
      unfold Nat.ModEq at this
      rw [this]
      norm_num
    have hd := dvd_three_of_pow_mod_seven h3
    have hd3 := hle3 F
    have hcases : Module.finrank K F = 0 ∨ Module.finrank K F = 3 := by omega
    rcases hcases with h0 | h3'
    · exact Submodule.finrank_eq_zero.mp h0
    · exfalso
      have htop : F = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [h3', Module.finrank_fin_fun])
      have hx1 : x = 1 := by
        apply Units.ext
        rw [Units.val_one]
        ext i j
        have hv : (Pi.single j 1 : Fin 3 → K) ∈ F := htop ▸ Submodule.mem_top
        have := congrFun hv i
        simp only [Matrix.mulVec_single_one, Matrix.col_apply] at this
        rw [this, Matrix.one_apply]
        simp [Pi.single_apply]
      rw [hx1, orderOf_one] at hx
      omega
  have hmod := card_modEq_card_fixed hx W hW
  have h1 : Nat.card {w : W // (x : Matrix (Fin 3) (Fin 3) K) *ᵥ (w : Fin 3 → K) = w} = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b => ?_⟩, ⟨⟨0, by simp⟩⟩⟩
    have ha : (a.1 : Fin 3 → K) ∈ F := a.2
    have hb : (b.1 : Fin 3 → K) ∈ F := b.2
    rw [hF, Submodule.mem_bot] at ha hb
    exact Subtype.ext (Subtype.ext (ha.trans hb.symm))
  rw [h1, hdim] at hmod
  have hd := dvd_three_of_pow_mod_seven hmod
  have hd3 := hle3 W
  have hcases : Module.finrank K W = 0 ∨ Module.finrank K W = 3 := by omega
  rcases hcases with h0 | h3'
  · exact Or.inl (Submodule.finrank_eq_zero.mp h0)
  · exact Or.inr (Submodule.eq_top_of_finrank_eq (by rw [h3', Module.finrank_fin_fun]))

end KL3Sub2Proof

end CFSG.RankThree.PartTwo.Sec15
