module

public import CFSG.Quasithin.Vol2.KGFactL34Uni

public section

namespace CFSG.Quasithin.H13.Ch4

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Quasithin.H13.KGL34A

variable {F : Type} [Field F]

theorem exists_conj_unitriangular_of_isPGroup [Finite F] [CharP F 2]
    {H : Subgroup (SpecialLinearGroup (Fin 3) F)} (hH : IsPGroup 2 H) :
    ∃ g : SpecialLinearGroup (Fin 3) F, ∀ y ∈ H, g⁻¹ * y * g ∈ unitriangular 3 F := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hHS⟩ := hH.exists_le_sylow
  obtain ⟨P₀, hP₀⟩ := exists_sylow_unitriangular (K := F) 2 (n := 3) (by norm_num)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (SpecialLinearGroup (Fin 3) F) P₀ S
  refine ⟨g, fun y hy => ?_⟩
  have hyS : y ∈ (S : Subgroup (SpecialLinearGroup (Fin 3) F)) := hHS hy
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at hyS
  obtain ⟨u, hu, hyu⟩ := hyS
  have hy' : y = g * u * g⁻¹ := hyu.symm
  rw [hy', show g⁻¹ * (g * u * g⁻¹) * g = u by group, ← hP₀]
  exact hu

@[expose] def slFix (E : Subgroup (SpecialLinearGroup (Fin 3) F)) : Submodule F (Fin 3 → F) where
  carrier := {x | ∀ X ∈ E, (X : Matrix (Fin 3) (Fin 3) F).mulVec x = x}
  add_mem' := fun {x y} hx hy X hX => by rw [Matrix.mulVec_add, hx X hX, hy X hX]
  zero_mem' := fun X _ => Matrix.mulVec_zero _
  smul_mem' := fun μ x hx X hX => by rw [Matrix.mulVec_smul, hx X hX]

theorem mem_slFix {E : Subgroup (SpecialLinearGroup (Fin 3) F)} {x : Fin 3 → F} :
    x ∈ slFix E ↔ ∀ X ∈ E, (X : Matrix (Fin 3) (Fin 3) F).mulVec x = x := Iff.rfl

section Unitriangular

variable [Finite F] [CharP F 2] {E : Subgroup (SpecialLinearGroup (Fin 3) F)}

omit [CharP F 2] in
theorem surjective_row_of_card (hEU : E ≤ unitriangular 3 F)
    (hR : ∀ u ∈ E, (u : Matrix (Fin 3) (Fin 3) F) 1 2 = 0) (hcard : Nat.card E = Nat.card F ^ 2) :
    Function.Surjective fun u : ↥E =>
      (((u : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 1,
        ((u : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 2) := by
  have hinj := injective_row hEU hR
  refine (hinj.bijective_of_nat_card_le ?_).2
  rw [Nat.card_prod, hcard, sq]

omit [CharP F 2] in
theorem surjective_col_of_card (hEU : E ≤ unitriangular 3 F)
    (hC : ∀ u ∈ E, (u : Matrix (Fin 3) (Fin 3) F) 0 1 = 0) (hcard : Nat.card E = Nat.card F ^ 2) :
    Function.Surjective fun u : ↥E =>
      (((u : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 1 2,
        ((u : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 2) := by
  have hinj := injective_col hEU hC
  refine (hinj.bijective_of_nat_card_le ?_).2
  rw [Nat.card_prod, hcard, sq]

theorem col_of_card (hEU : E ≤ unitriangular 3 F) (hc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hs : ∀ x ∈ E, x * x = 1) (hcard : Nat.card E = Nat.card F ^ 2)
    (hfix : Nat.card F ^ 2 ≤ Nat.card (slFix E)) :
    ∀ u ∈ E, (u : Matrix (Fin 3) (Fin 3) F) 0 1 = 0 := by
  rcases row_or_col hEU hc hs with hR | hC
  · exfalso
    have hsurj := surjective_row_of_card hEU hR hcard
    obtain ⟨u₁, hu₁⟩ := hsurj (1, 0)
    obtain ⟨u₂, hu₂⟩ := hsurj (0, 1)
    simp only [Prod.mk.injEq] at hu₁ hu₂
    have hfix' : ∀ x ∈ slFix E, x 1 = 0 ∧ x 2 = 0 := by
      intro x hx
      have h1 := congrFun ((mem_slFix.mp hx) u₁ u₁.2) 0
      have h2 := congrFun ((mem_slFix.mp hx) u₂ u₂.2) 0
      rw [eq_of_row (hEU u₁.2) (hR _ u₁.2), hu₁.1, hu₁.2] at h1
      rw [eq_of_row (hEU u₂.2) (hR _ u₂.2), hu₂.1, hu₂.2] at h2
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h1 h2
      exact ⟨h1, h2⟩
    have hle : Nat.card (slFix E) ≤ Nat.card F := by
      refine Nat.card_le_card_of_injective (fun x : ↥(slFix E) => (x : Fin 3 → F) 0)
        fun x y hxy => ?_
      have hx := hfix' x x.2
      have hy := hfix' y y.2
      apply Subtype.ext
      funext i
      fin_cases i
      · exact hxy
      · simp [hx.1, hy.1]
      · simp [hx.2, hy.2]
    have hq : 2 ≤ Nat.card F := by
      have := Fintype.ofFinite F
      rw [Nat.card_eq_fintype_card]
      exact Fintype.one_lt_card
    have : Nat.card F < Nat.card F ^ 2 := by
      calc Nat.card F = Nat.card F * 1 := (mul_one _).symm
        _ < Nat.card F * Nat.card F := Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
        _ = Nat.card F ^ 2 := (sq _).symm
    omega
  · exact hC

omit [CharP F 2] in
theorem eq_of_col_of_card {E E' : Subgroup (SpecialLinearGroup (Fin 3) F)}
    (hEU : E ≤ unitriangular 3 F) (hE'U : E' ≤ unitriangular 3 F)
    (hC : ∀ u ∈ E, (u : Matrix (Fin 3) (Fin 3) F) 0 1 = 0)
    (hC' : ∀ u ∈ E', (u : Matrix (Fin 3) (Fin 3) F) 0 1 = 0)
    (hcard : Nat.card E = Nat.card F ^ 2) (hcard' : Nat.card E' = Nat.card F ^ 2) : E = E' := by
  have hsub : E' ≤ E := by
    intro u hu
    obtain ⟨u', hu'⟩ := surjective_col_of_card hEU hC hcard
      ((u : Matrix (Fin 3) (Fin 3) F) 1 2, (u : Matrix (Fin 3) (Fin 3) F) 0 2)
    simp only [Prod.mk.injEq] at hu'
    have h1 : u = u' := by
      apply Subtype.ext
      rw [eq_of_col (hE'U hu) (hC' u hu), eq_of_col (hEU u'.2) (hC _ u'.2), hu'.1, hu'.2]
    rw [h1]
    exact u'.2
  exact (Subgroup.eq_of_le_of_card_ge hsub (by rw [hcard, hcard'])).symm

end Unitriangular

theorem mulVec_of_col {u : SpecialLinearGroup (Fin 3) F} (hu : u ∈ unitriangular 3 F)
    (h01 : (u : Matrix (Fin 3) (Fin 3) F) 0 1 = 0) (x : Fin 3 → F) :
    (u : Matrix (Fin 3) (Fin 3) F).mulVec x =
      x + x 2 • ![(u : Matrix (Fin 3) (Fin 3) F) 0 2, (u : Matrix (Fin 3) (Fin 3) F) 1 2, 0] := by
  rw [eq_of_col hu h01]
  funext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring

theorem coord_two_eq_zero_of_cocycle {ι : Type*} {X : ι → SpecialLinearGroup (Fin 3) F}
    (hU : ∀ i, X i ∈ unitriangular 3 F) (hC : ∀ i, (X i : Matrix (Fin 3) (Fin 3) F) 0 1 = 0)
    (hsurj : ∀ b c : F, ∃ i, (X i : Matrix (Fin 3) (Fin 3) F) 1 2 = b ∧
      (X i : Matrix (Fin 3) (Fin 3) F) 0 2 = c)
    {w : ι → Fin 3 → F}
    (hw : ∀ i j, (X j : Matrix (Fin 3) (Fin 3) F).mulVec (w i) - w i =
      (X i : Matrix (Fin 3) (Fin 3) F).mulVec (w j) - w j) (i : ι) : w i 2 = 0 := by
  have hd : ∀ j x, (X j : Matrix (Fin 3) (Fin 3) F).mulVec x - x =
      x 2 • ![(X j : Matrix (Fin 3) (Fin 3) F) 0 2, (X j : Matrix (Fin 3) (Fin 3) F) 1 2, 0] := by
    intro j x
    rw [mulVec_of_col (hU j) (hC j) x, add_sub_cancel_left]
  obtain ⟨j₁, hj₁b, hj₁c⟩ := hsurj 0 1
  obtain ⟨j₂, hj₂b, hj₂c⟩ := hsurj 1 0
  have e₁ := hw i j₁
  have e₂ := hw i j₂
  rw [hd, hd, hj₁b, hj₁c] at e₁
  rw [hd, hd, hj₂b, hj₂c] at e₂
  have e₁0 := congrFun e₁ 0
  have e₁1 := congrFun e₁ 1
  have e₂0 := congrFun e₂ 0
  have e₂1 := congrFun e₂ 1
  simp only [Pi.smul_apply, Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_mul, mul_one,
    mul_zero] at e₁0 e₁1 e₂0 e₂1
  by_contra hne
  have ha : (X i : Matrix (Fin 3) (Fin 3) F) 0 2 ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at e₁0
    exact hne e₁0
  have hb : (X i : Matrix (Fin 3) (Fin 3) F) 1 2 = 0 := by
    have h1 : w j₁ 2 ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at e₁0
      exact hne e₁0
    have h2 := e₁1.symm
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h h1
    · exact h
  rw [hb, mul_zero] at e₂1
  exact hne e₂1

end CFSG.Quasithin.H13.Ch4
