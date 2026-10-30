module

public import CFSG.RankThree.GF2n.Smith81.S81YUWittA
public import CFSG.RankThree.GF2n.Smith81.S81YUWittB
public import CFSG.RankThree.GF2n.Smith81.S81XU2

public section

namespace CFSG.RankThree.GF2n.Smith81.RootGenU

open CFSG.RankThree.GF2n.Smith81.U6Cube CFSG.RankThree.GF2n.Smith81.A5Cube
  CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary CFSG.LieType.BorelTits
  Matrix exteriorPower
  CFSG.RankThree.GF2n.Smith81 CFSG.RankThree.GF2n.Smith81.RootGen

variable {F : Type} [Field F] [Finite F] [CharP F 2] {σ : F ≃+* F}

theorem u6_move_core (hσ : IsUnitaryInvolution σ) {a b : Fin 6 → F} (ha : a ≠ 0)
    (haa : herm σ a a = 0) (hbb : herm σ b b = 0) (hab : herm σ a b = 0)
    {v : Fin 3 → Fin 6 → F} (hv : ιMulti F 3 v ≠ 0) (hiso : ∀ i j, ∑ k, σ (v i k) * v j k = 0)
    (hav : a ∈ Submodule.span F (Set.range v)) :
    ∃ h : SUid σ 6, ((h : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).mulVec a = a ∧
      ∀ i, herm σ b (((h : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).mulVec (v i)) = 0 := by
  have hvli : LinearIndependent F v :=
    CFSG.RankThree.GF2n.Smith81.A5Cube.linearIndependent_of_ιMulti_ne_zero hv
  have hL : ∀ x ∈ Submodule.span F (Set.range v), ∀ y ∈ Submodule.span F (Set.range v),
      herm σ x y = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨i, rfl⟩ := hx
        obtain ⟨j, rfl⟩ := hy
        exact hiso i j
      | zero => simp
      | add y y' _ _ h1 h2 => rw [herm_add_right, h1, h2, add_zero]
      | smul c y _ h1 => rw [herm_smul_right, h1, mul_zero]
    | zero => intro y _; simp
    | add x x' _ _ h1 h2 => intro y hy; rw [herm_add_left, h1 y hy, h2 y hy, add_zero]
    | smul c x _ h1 => intro y hy; rw [herm_smul_left, h1 y hy, mul_zero]
  obtain ⟨X, Y, hX, hY, hli, hspan⟩ := exists_ordered_basis hvli ha hav
  have hmem3 : ∀ i, (![X, a, Y] : Fin 3 → Fin 6 → F) i ∈ Submodule.span F (Set.range v) := by
    intro i
    fin_cases i <;> simp [hX, hav, hY]
  have hisoXaY : ∀ i j, herm σ (![X, a, Y] i) (![X, a, Y] j) = 0 :=
    fun i j => hL _ (hmem3 i) _ (hmem3 j)
  by_cases hperp : ∀ i, herm σ b (v i) = 0
  ·
    refine ⟨1, ?_, ?_⟩
    · simp
    · intro i
      simpa using hperp i
  ·
    have hb : herm σ X b ≠ 0 ∨ herm σ Y b ≠ 0 := by
      by_contra hcon
      push Not at hcon
      obtain ⟨hXb, hYb⟩ := hcon
      have hbX : herm σ b X = 0 := by rw [herm_conj σ hσ.invol X b, hXb, map_zero]
      have hbY : herm σ b Y = 0 := by rw [herm_conj σ hσ.invol Y b, hYb, map_zero]
      have hba : herm σ b a = 0 := by rw [herm_conj σ hσ.invol a b, hab, map_zero]
      have hbw : ∀ w ∈ Submodule.span F ({X, a, Y} : Set (Fin 6 → F)), herm σ b w = 0 := by
        intro w hw
        induction hw using Submodule.span_induction with
        | mem x hx =>
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
          rcases hx with h | h | h
          · rw [h]; exact hbX
          · rw [h]; exact hba
          · rw [h]; exact hbY
        | zero => simp
        | add x y _ _ h1 h2 => rw [herm_add_right, h1, h2, add_zero]
        | smul c x _ h1 => rw [herm_smul_right, h1, mul_zero]
      exact hperp fun i => hbw _ (hspan i)
    obtain ⟨c', -, hbc', hli', hiso''⟩ := exists_ti_triple_ext hσ hli hisoXaY hab hbb hb
    obtain ⟨g, l, -, hgX, hga, hgY⟩ :=
      u6_witt_two hσ (CFSG.RankThree.GF2n.Smith81.u6_iotaMulti_ne_zero_of_li hli) hisoXaY
        (CFSG.RankThree.GF2n.Smith81.u6_iotaMulti_ne_zero_of_li hli') hiso''
    have hga' : ((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).mulVec a = a := hga
    have hgX' : ((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).mulVec X = l • c' := hgX
    have hgY' : ((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).mulVec Y = b := hgY
    have hba : herm σ b a = 0 := by rw [herm_conj σ hσ.invol a b, hab, map_zero]
    have hfin : ∀ w ∈ Submodule.span F ({X, a, Y} : Set (Fin 6 → F)),
        herm σ b (((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).mulVec w) = 0 := by
      intro w hw
      induction hw using Submodule.span_induction with
      | mem x hx =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with h | h | h
        · rw [h, hgX', herm_smul_right, hbc', mul_zero]
        · rw [h, hga']; exact hba
        · rw [h, hgY']; exact hbb
      | zero => simp
      | add x y _ _ h1 h2 => rw [Matrix.mulVec_add, herm_add_right, h1, h2, add_zero]
      | smul c x _ h1 => rw [Matrix.mulVec_smul, herm_smul_right, h1, mul_zero]
    exact ⟨g, hga', fun i => hfin _ (hspan i)⟩

end CFSG.RankThree.GF2n.Smith81.RootGenU
