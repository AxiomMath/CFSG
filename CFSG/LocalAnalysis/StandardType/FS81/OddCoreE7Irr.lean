module

public import CFSG.LocalAnalysis.StandardType.FS81.OddCoreE7P
public import CFSG.LocalAnalysis.StandardType.FS81.OddCoreOrth3

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType.FrameRoute.FS81

open scoped Matrix

@[expose] def hSix : Set (Matrix (Fin 8) (Fin 8) (ZMod 3)) :=
  spSet fun σ s => σ 0 = 0 ∧ s 0 = 1 ∧ σ 1 = 1 ∧ s 1 = 1 ∧ ∏ i : Fin 6, s i.succ.succ = 1

theorem hSix_subset_hSeven : hSix ⊆ hSeven := by
  rintro _ ⟨σ, s, hs, ⟨h0, hs0, h1, -, hp⟩, rfl⟩
  exact ⟨σ, s, hs, ⟨h0, hs0, h1, hp⟩, rfl⟩

theorem sgnOn_mem_hSix {T : Finset (Fin 8)} (h0 : (0 : Fin 8) ∉ T) (h1 : (1 : Fin 8) ∉ T)
    (heven : Even T.card) : spMat 1 (sgnOn T) ∈ hSix :=
  ⟨1, sgnOn T, isSign_sgnOn T, ⟨rfl, if_neg h0, rfl, if_neg h1, by
    rw [prod_succ_succ_sgnOn h0 h1, heven.neg_one_pow]⟩, rfl⟩

theorem perm_mem_hSix {π : Equiv.Perm (Fin 8)} (h0 : π 0 = 0) (h1 : π 1 = 1) :
    spMat π (fun _ => 1) ∈ hSix :=
  ⟨π, fun _ => 1, fun _ => Or.inl rfl, ⟨h0, rfl, h1, rfl, by simp⟩, rfl⟩

theorem t1_mem_hSeven : spMat 1 (sgnOn {1}) ∈ hSeven :=
  ⟨1, sgnOn {1}, isSign_sgnOn _, ⟨rfl, if_neg (by decide), rfl,
    Finset.prod_eq_one fun i _ => if_neg ((by decide : ∀ i : Fin 6,
      i.succ.succ ∉ ({1} : Finset (Fin 8))) i)⟩, rfl⟩

theorem fin8_cases (j : Fin 8) : j = 0 ∨ j = 1 ∨ 2 ≤ j.val := by
  revert j
  decide

theorem subset_of_hSix_invariant {U : Submodule (ZMod 3) (Fin 8 → ZMod 3)}
    (hW : ∀ A ∈ hSix, ∀ u ∈ U, A *ᵥ u ∈ U) {v : Fin 8 → ZMod 3} (hv : v ∈ U)
    {i : Fin 8} (hi : 2 ≤ i.val) (hvi : v i ≠ 0) {w : Fin 8 → ZMod 3} (hw0 : w 0 = 0)
    (hw1 : w 1 = 0) : w ∈ U := by
  obtain ⟨j, l, hj, hl, hji, hli, hjl⟩ := (by decide : ∀ i : Fin 8, 2 ≤ i.val →
    ∃ j l : Fin 8, 2 ≤ j.val ∧ 2 ≤ l.val ∧ j ≠ i ∧ l ≠ i ∧ j ≠ l) i hi
  have h01 : ∀ a : Fin 8, 2 ≤ a.val → (0 : Fin 8) ≠ a ∧ (1 : Fin 8) ≠ a := by decide
  have hT : ∀ a b : Fin 8, 2 ≤ a.val → 2 ≤ b.val → a ≠ b → spMat 1 (sgnOn {a, b}) ∈ hSix := by
    intro a b ha hb hab
    refine sgnOn_mem_hSix ?_ ?_ (by rw [Finset.card_pair hab]; exact even_two)
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨(h01 a ha).1, (h01 b hb).1⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨(h01 a ha).2, (h01 b hb).2⟩
  have huU : v - spMat 1 (sgnOn {i, j}) *ᵥ v ∈ U :=
    U.sub_mem hv (hW _ (hT i j hi hj (Ne.symm hji)) v hv)
  have hu'U := U.add_mem huU (hW _ (hT j l hj hl hjl) _ huU)
  have hei : Pi.single i 1 ∈ U := by
    have := U.smul_mem (v i)⁻¹ hu'U
    rwa [sgnOn_isolate (Ne.symm hji) (Ne.symm hli), ← Pi.single_smul', smul_eq_mul,
      inv_mul_cancel₀ hvi] at this
  have hek : ∀ k : Fin 8, 2 ≤ k.val → Pi.single k 1 ∈ U := by
    intro k hk
    have hP := hW _ (perm_mem_hSix (π := Equiv.swap i k)
      (Equiv.swap_apply_of_ne_of_ne (h01 i hi).1 (h01 k hk).1)
      (Equiv.swap_apply_of_ne_of_ne (h01 i hi).2 (h01 k hk).2)) _ hei
    rwa [spMat_mulVec_single, Equiv.swap_apply_left, one_mul] at hP
  rw [← Finset.univ_sum_single w]
  refine U.sum_mem fun k _ => ?_
  rcases fin8_cases k with rfl | rfl | hk
  · rw [hw0, Pi.single_zero]
    exact U.zero_mem
  · rw [hw1, Pi.single_zero]
    exact U.zero_mem
  · have := U.smul_mem (w k) (hek k hk)
    rwa [← Pi.single_smul', smul_eq_mul, mul_one] at this

theorem e1_mem_of_hSeven_invariant {U : Submodule (ZMod 3) (Fin 8 → ZMod 3)}
    (hW : ∀ A ∈ hSeven, ∀ u ∈ U, A *ᵥ u ∈ U) {v : Fin 8 → ZMod 3} (hv : v ∈ U)
    (hv1 : v 1 ≠ 0) : Pi.single 1 1 ∈ U := by
  have h := U.sub_mem hv (hW _ t1_mem_hSeven v hv)
  have heq : v - spMat 1 (sgnOn {1}) *ᵥ v = Pi.single 1 (2 * v 1) := by
    funext x
    rw [Pi.sub_apply, mulVec_sgnOn_apply]
    by_cases hx : x = 1
    · subst hx
      simp only [sgnOn, Finset.mem_singleton, if_true, Pi.single_eq_same]
      ring
    · simp only [sgnOn, Finset.mem_singleton, hx, if_false, one_mul, sub_self,
        Pi.single_eq_of_ne hx]
  rw [heq] at h
  have h2 : 2 * v 1 ≠ 0 := mul_ne_zero (by decide) hv1
  have := U.smul_mem (2 * v 1)⁻¹ h
  rwa [← Pi.single_smul', smul_eq_mul, inv_mul_cancel₀ h2] at this

theorem card_hSeven_lt : Nat.card ↥hSeven < 2903040 := by
  let F : {f : Equiv.Perm (Fin 8) // ∀ a, ¬ (a ≠ 0 ∧ a ≠ 1) → f a = a} × (Fin 8 → Bool) →
      Matrix (Fin 8) (Fin 8) (ZMod 3) :=
    fun q => spMat q.1.1 (fun i => if q.2 i then 1 else -1)
  have hsub : hSeven ⊆ Set.range F := by
    rintro _ ⟨σ, s, hs, ⟨h0, -, h1, -⟩, rfl⟩
    refine ⟨(⟨σ, fun a ha => ?_⟩, fun i => decide (s i = 1)), ?_⟩
    · rw [not_and_or, not_not, not_not] at ha
      rcases ha with rfl | rfl
      · exact h0
      · exact h1
    · show spMat σ _ = spMat σ s
      congr 1
      funext i
      show (if decide (s i = 1) = true then (1 : ZMod 3) else -1) = s i
      rcases hs i with h | h <;> rw [h] <;> decide
  have hP : Nat.card {f : Equiv.Perm (Fin 8) // ∀ a, ¬ (a ≠ 0 ∧ a ≠ 1) → f a = a} = 720 := by
    rw [← Nat.card_congr (Equiv.Perm.subtypeEquivSubtypePerm fun a : Fin 8 => a ≠ 0 ∧ a ≠ 1),
      Nat.card_perm, Nat.card_eq_fintype_card]
    rfl
  calc Nat.card ↥hSeven ≤ Nat.card ↥(Set.range F) := Nat.card_mono (Set.toFinite _) hsub
    _ ≤ Nat.card ({f : Equiv.Perm (Fin 8) // ∀ a, ¬ (a ≠ 0 ∧ a ≠ 1) → f a = a} × (Fin 8 → Bool)) :=
        Nat.card_le_card_of_surjective (Set.rangeFactorization F) Set.rangeFactorization_surjective
    _ < 2903040 := by
        rw [Nat.card_prod, hP, Nat.card_fun, Nat.card_eq_fintype_card (α := Bool),
          Nat.card_eq_fintype_card (α := Fin 8)]
        decide

theorem e7_exists_move {Xg : Subgroup (GL (Fin 8) (ZMod 3))}
    (hstab : ∀ x ∈ Xg, (x : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ Pi.single 0 1 = Pi.single 0 1 →
      (∃ c : ZMod 3, (x : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ Pi.single 1 1 = c • Pi.single 1 1) →
      (x : Matrix (Fin 8) (Fin 8) (ZMod 3)) ∈ hSeven)
    (hcard : Nat.card ↥(Xg ⊓ fixE0 7) = 2903040) :
    ∃ x ∈ Xg, (x : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ Pi.single 0 1 = Pi.single 0 1 ∧
      ¬ ∃ c : ZMod 3, (x : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ Pi.single 1 1 = c • Pi.single 1 1 := by
  by_contra h
  push Not at h
  let f : ↥(Xg ⊓ fixE0 7) → ↥hSeven := fun x =>
    ⟨((x : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3)),
      hstab x x.2.1 x.2.2 (h x x.2.1 x.2.2)⟩
  have hf : Function.Injective f := fun x y hxy =>
    Subtype.ext (Units.ext (congrArg Subtype.val hxy))
  have : Finite ↥hSeven := Set.toFinite _ |>.to_subtype
  have hle := Nat.card_le_card_of_injective f hf
  rw [hcard] at hle
  exact absurd card_hSeven_lt (not_lt.mpr hle)

theorem e7_not_H0_invariant {Xg : Subgroup (GL (Fin 8) (ZMod 3))}
    (hH : ∀ A ∈ hSeven, ∃ x ∈ Xg, (x : Matrix (Fin 8) (Fin 8) (ZMod 3)) = A)
    (hstab : ∀ x ∈ Xg, (x : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ Pi.single 0 1 = Pi.single 0 1 →
      (∃ c : ZMod 3, (x : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ Pi.single 1 1 = c • Pi.single 1 1) →
      (x : Matrix (Fin 8) (Fin 8) (ZMod 3)) ∈ hSeven)
    (hcard : Nat.card ↥(Xg ⊓ fixE0 7) = 2903040)
    (hCA : ∀ x ∈ Xg, (x : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ Pi.single 0 1 = Pi.single 0 1 →
      ∀ v : Fin 8 → ZMod 3, v 0 = 0 → ((x : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ v) 0 = 0)
    (hH0 : ∀ x ∈ Xg, (x : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ Pi.single 0 1 = Pi.single 0 1 →
      ∀ v : Fin 8 → ZMod 3, v 1 = 0 → ((x : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ v) 1 = 0) :
    False := by
  have hinvL : ∀ (y : GL (Fin 8) (ZMod 3)) (v : Fin 8 → ZMod 3),
      ((y⁻¹ : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ
        ((y : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ v) = v := fun y v => by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have hinvR : ∀ (y : GL (Fin 8) (ZMod 3)) (v : Fin 8 → ZMod 3),
      (y : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ
        (((y⁻¹ : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ v) = v :=
    fun y v => by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  have hinvfix : ∀ (y : GL (Fin 8) (ZMod 3)) (v : Fin 8 → ZMod 3),
      (y : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ v = v →
        ((y⁻¹ : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ v = v :=
    fun y v hv => by
    conv_lhs => rw [← hv]
    exact hinvL y v
  let S : Subgroup (GL (Fin 8) (ZMod 3)) :=
    { carrier := {y | y ∈ Xg ∧ (∀ v : Fin 8 → ZMod 3, v 1 = 0 →
          (y : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ v = v) ∧
        ((y : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ Pi.single 1 1) 0 = 0 ∧
        ((y : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ Pi.single 1 1) 1 = 1}
      mul_mem' := fun {y y'} hy hy' => by
        simp only [Set.mem_setOf_eq] at hy hy' ⊢
        obtain ⟨hyX, hyv, hy0, hy1⟩ := hy
        obtain ⟨hy'X, hy'v, hy'0, hy'1⟩ := hy'
        have hb : ((y' : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ Pi.single 1 1 - Pi.single 1 1 :
            Fin 8 → ZMod 3) 1 = 0 := by
          rw [Pi.sub_apply, hy'1, Pi.single_eq_same, sub_self]
        have himg : ((y * y' : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ
            Pi.single 1 1 = (y : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ Pi.single 1 1 +
              ((y' : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ Pi.single 1 1 - Pi.single 1 1) := by
          rw [Units.val_mul, ← Matrix.mulVec_mulVec]
          conv_lhs => rw [show (y' : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ Pi.single 1 1 =
            Pi.single 1 1 + ((y' : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ Pi.single 1 1 -
              Pi.single 1 1) by abel]
          rw [Matrix.mulVec_add, hyv _ hb]
        refine ⟨Xg.mul_mem hyX hy'X, fun v hv => ?_, ?_, ?_⟩
        · rw [Units.val_mul, ← Matrix.mulVec_mulVec, hy'v v hv, hyv v hv]
        · rw [himg, Pi.add_apply, Pi.sub_apply, hy0, hy'0]
          simp
        · rw [himg, Pi.add_apply, hy1, hb, add_zero]
      one_mem' := by
        simp only [Set.mem_setOf_eq]
        exact ⟨Xg.one_mem, fun v _ => by rw [Units.val_one, Matrix.one_mulVec], by simp, by simp⟩
      inv_mem' := fun {y} hy => by
        simp only [Set.mem_setOf_eq] at hy ⊢
        obtain ⟨hyX, hyv, hy0, hy1⟩ := hy
        have hb : ((y : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ Pi.single 1 1 - Pi.single 1 1 :
            Fin 8 → ZMod 3) 1 = 0 := by
          rw [Pi.sub_apply, hy1, Pi.single_eq_same, sub_self]
        have himg : ((y⁻¹ : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ
            Pi.single 1 1 = Pi.single 1 1 -
              ((y : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ Pi.single 1 1 - Pi.single 1 1) := by
          have h1 : (y : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ (Pi.single 1 1 -
              ((y : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ Pi.single 1 1 - Pi.single 1 1)) =
                Pi.single 1 1 := by
            rw [Matrix.mulVec_sub, hyv _ hb]
            abel
          conv_lhs => rw [← h1]
          exact hinvL y _
        refine ⟨Xg.inv_mem hyX, fun v hv => hinvfix y v (hyv v hv), ?_, ?_⟩
        · rw [himg, Pi.sub_apply, Pi.sub_apply, hy0]
          simp
        · rw [himg, Pi.sub_apply, hb, sub_zero, Pi.single_eq_same] }
  have hSmem : ∀ y, y ∈ S ↔ y ∈ Xg ∧ (∀ v : Fin 8 → ZMod 3, v 1 = 0 →
      (y : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ v = v) ∧
      ((y : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ Pi.single 1 1) 0 = 0 ∧
      ((y : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ Pi.single 1 1) 1 = 1 := fun _ => Iff.rfl
  have hS_le : S ≤ Xg ⊓ fixE0 7 := fun y hy => by
    obtain ⟨hyX, hyv, -, -⟩ := (hSmem y).mp hy
    exact ⟨hyX, hyv _ (by simp)⟩
  have hSb : ∀ y ∈ S, ∀ b : Fin 8 → ZMod 3,
      (y : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ Pi.single 1 1 = Pi.single 1 1 + b →
        b 0 = 0 ∧ b 1 = 0 := by
    intro y hy b hyb
    obtain ⟨-, -, hy0, hy1⟩ := (hSmem y).mp hy
    rw [hyb, Pi.add_apply] at hy0 hy1
    rw [Pi.single_eq_same] at hy1
    exact ⟨by simpa using hy0, add_eq_left.mp hy1⟩
  have hadd : ∀ a b : Fin 8 → ZMod 3,
      (∃ y ∈ S, (y : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ Pi.single 1 1 = Pi.single 1 1 + a) →
      (∃ y ∈ S, (y : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ Pi.single 1 1 = Pi.single 1 1 + b) →
      ∃ y ∈ S, (y : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ Pi.single 1 1 =
        Pi.single 1 1 + (a + b) := by
    rintro a b ⟨y, hy, hya⟩ ⟨y', hy', hy'b⟩
    obtain ⟨-, hyv, -, -⟩ := (hSmem y).mp hy
    refine ⟨y * y', S.mul_mem hy hy', ?_⟩
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hy'b, Matrix.mulVec_add, hya,
      hyv b (hSb y' hy' b hy'b).2, add_assoc]
  have hnsmul : ∀ (k : ℕ) (a : Fin 8 → ZMod 3),
      (∃ y ∈ S, (y : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ Pi.single 1 1 = Pi.single 1 1 + a) →
      ∃ y ∈ S, (y : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ Pi.single 1 1 =
        Pi.single 1 1 + k • a := by
    intro k a ha
    induction k with
    | zero => exact ⟨1, S.one_mem, by rw [zero_nsmul, add_zero, Units.val_one, Matrix.one_mulVec]⟩
    | succ k ih =>
      rw [succ_nsmul]
      exact hadd _ _ ih ha
  let Γ : Submodule (ZMod 3) (Fin 8 → ZMod 3) :=
    { carrier := {b | ∃ y ∈ S, (y : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ Pi.single 1 1 =
        Pi.single 1 1 + b}
      add_mem' := fun {a b} ha hb => hadd a b ha hb
      zero_mem' := ⟨1, S.one_mem, by rw [add_zero, Units.val_one, Matrix.one_mulVec]⟩
      smul_mem' := fun c a ha => by
        have hval : c • a = c.val • a := by
          rw [← Nat.cast_smul_eq_nsmul (ZMod 3), ZMod.natCast_zmod_val]
        show ∃ y ∈ S, _
        rw [hval]
        exact hnsmul c.val a ha }
  have hΓ : ∀ A ∈ hSix, ∀ u ∈ Γ, A *ᵥ u ∈ Γ := by
    intro A hA u hu
    obtain ⟨y, hy, hyu⟩ := hu
    obtain ⟨hyX, hyv, -, -⟩ := (hSmem y).mp hy
    obtain ⟨hu0, hu1⟩ := hSb y hy u hyu
    obtain ⟨h, hhX, rfl⟩ := hH A (hSix_subset_hSeven hA)
    obtain ⟨σ, s, -, ⟨hσ0, hs0, hσ1, hs1, -⟩, hhσ⟩ := hA
    have he0 : (h : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
      rw [hhσ, spMat_mulVec_single, hσ0, hs0, one_mul]
    have he1 : (h : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ Pi.single 1 1 = Pi.single 1 1 := by
      rw [hhσ, spMat_mulVec_single, hσ1, hs1, one_mul]
    have hzapp : ∀ v, ((h * y * h⁻¹ : GL (Fin 8) (ZMod 3)) :
        Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ v = (h : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ
          ((y : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ
            (((h⁻¹ : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ v)) := by
      intro v
      simp only [Units.val_mul, ← Matrix.mulVec_mulVec]
    have hze1 : ((h * y * h⁻¹ : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ
        Pi.single 1 1 = Pi.single 1 1 + (h : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ u := by
      rw [hzapp, hinvfix h _ he1, hyu, Matrix.mulVec_add, he1]
    have hhu0 := hCA h hhX he0 u hu0
    have hhu1 := hH0 h hhX he0 u hu1
    refine ⟨h * y * h⁻¹, (hSmem _).mpr ⟨Xg.mul_mem (Xg.mul_mem hhX hyX) (Xg.inv_mem hhX),
      fun v hv => ?_, ?_, ?_⟩, hze1⟩
    · rw [hzapp, hyv _ (hH0 h⁻¹ (Xg.inv_mem hhX) (hinvfix h _ he0) v hv), hinvR]
    · rw [hze1, Pi.add_apply, hhu0, add_zero]
      simp
    · rw [hze1, Pi.add_apply, hhu1, add_zero, Pi.single_eq_same]
  obtain ⟨x, hxX, hxe, hxmove⟩ := e7_exists_move hstab hcard
  have hxiX := Xg.inv_mem hxX
  have hxie := hinvfix x _ hxe
  obtain ⟨c, hc⟩ : ∃ c : ZMod 3,
      ((x : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ Pi.single 1 1) 1 = c := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : Fin 8 → ZMod 3,
      a = (x : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ Pi.single 1 1 - c • Pi.single 1 1 := ⟨_, rfl⟩
  have hxe1 : (x : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ Pi.single 1 1 = c • Pi.single 1 1 + a := by
    rw [ha]
    abel
  have ha0 : a 0 = 0 := by
    rw [ha, Pi.sub_apply, hCA x hxX hxe _ (by simp)]
    simp
  have ha1 : a 1 = 0 := by
    rw [ha, Pi.sub_apply, hc]
    simp
  have hc0 : c ≠ 0 := by
    intro h0
    have h1 := hH0 x⁻¹ hxiX hxie _ (hc.trans h0)
    rw [hinvL] at h1
    simp at h1
  have hcc : c * c = 1 := (by decide : ∀ c : ZMod 3, c ≠ 0 → c * c = 1) c hc0
  obtain ⟨k, hk2, hak⟩ : ∃ k : Fin 8, 2 ≤ k.val ∧ a k ≠ 0 := by
    by_contra h
    push Not at h
    refine hxmove ⟨c, ?_⟩
    have ha' : a = 0 := by
      funext j
      rcases fin8_cases j with rfl | rfl | hj
      · exact ha0
      · exact ha1
      · exact h j hj
    rw [hxe1, ha', add_zero]
  obtain ⟨y₁, hy₁X, hy₁⟩ := hH _ t1_mem_hSeven
  have hy₁v : ∀ v : Fin 8 → ZMod 3,
      (y₁ : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ v = v + v 1 • Pi.single 1 1 := by
    intro v
    rw [hy₁]
    funext j
    rw [mulVec_sgnOn_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hj : j = 1
    · subst hj
      simp only [sgnOn, Finset.mem_singleton, if_true, Pi.single_eq_same, mul_one]
      generalize v 1 = t
      revert t
      decide
    · simp only [sgnOn, Finset.mem_singleton, hj, if_false, one_mul, Pi.single_eq_of_ne hj,
        mul_zero, add_zero]
  have hτapp : ∀ v, ((y₁ * (x * y₁ * x⁻¹) : GL (Fin 8) (ZMod 3)) :
      Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ v = (y₁ : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ
        ((x : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ ((y₁ : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ
          (((x⁻¹ : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ v))) := by
    intro v
    simp only [Units.val_mul, ← Matrix.mulVec_mulVec]
  have hr : ∀ v : Fin 8 → ZMod 3, v 1 = 0 → (x : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ
      ((y₁ : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ
        (((x⁻¹ : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ v)) = v := by
    intro v hv
    rw [hy₁v, hH0 x⁻¹ hxiX hxie v hv, zero_smul, add_zero, hinvR]
  have hxi1 : (((x⁻¹ : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ
      Pi.single 1 1) 1 = c := by
    have h1 := hinvL x (Pi.single 1 1)
    rw [hxe1, Matrix.mulVec_add, Matrix.mulVec_smul] at h1
    have h2 := congrFun h1 1
    rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hH0 x⁻¹ hxiX hxie a ha1, add_zero,
      Pi.single_eq_same] at h2
    calc _ = c * c * ((((x⁻¹ : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ
          Pi.single 1 1) 1) := by rw [hcc, one_mul]
      _ = c := by rw [mul_assoc, h2, mul_one]
  have hτe1 : ((y₁ * (x * y₁ * x⁻¹) : GL (Fin 8) (ZMod 3)) :
      Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ Pi.single 1 1 = Pi.single 1 1 + c • a := by
    rw [hτapp, hy₁v (((x⁻¹ : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ
      Pi.single 1 1), hxi1, Matrix.mulVec_add, hinvR, Matrix.mulVec_smul, hxe1, hy₁v]
    funext j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, ha1, Pi.single_eq_same]
    have h3 : (3 : ZMod 3) = 0 := by decide
    linear_combination (2 * (Pi.single 1 1 : Fin 8 → ZMod 3) j) * hcc +
      ((Pi.single 1 1 : Fin 8 → ZMod 3) j) * h3
  have hτS : y₁ * (x * y₁ * x⁻¹) ∈ S := by
    refine (hSmem _).mpr ⟨Xg.mul_mem hy₁X (Xg.mul_mem (Xg.mul_mem hxX hy₁X) hxiX),
      fun v hv => ?_, ?_, ?_⟩
    · rw [hτapp, hr v hv, hy₁v, hv, zero_smul, add_zero]
    · rw [hτe1, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ha0, mul_zero, add_zero]
      simp
    · rw [hτe1, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ha1, mul_zero, add_zero,
        Pi.single_eq_same]
  have hA'Γ : ∀ w : Fin 8 → ZMod 3, w 0 = 0 → w 1 = 0 → w ∈ Γ := fun w hw0 hw1 =>
    subset_of_hSix_invariant hΓ (⟨_, hτS, hτe1⟩ : c • a ∈ Γ) hk2
      (by rw [Pi.smul_apply, smul_eq_mul]; exact mul_ne_zero hc0 hak) hw0 hw1
  let ψ : ↥S → (Fin 6 → ZMod 3) := fun y i =>
    (((y : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ Pi.single 1 1)
      i.succ.succ
  have hψinj : Function.Injective ψ := by
    rintro ⟨y, hy⟩ ⟨y', hy'⟩ hyy
    obtain ⟨-, hyv, hy0, hy1⟩ := (hSmem y).mp hy
    obtain ⟨-, hy'v, hy'0, hy'1⟩ := (hSmem y').mp hy'
    have he1 : (y : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ Pi.single 1 1 =
        (y' : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ Pi.single 1 1 := by
      funext j
      rcases fin8_cases j with rfl | rfl | hj
      · rw [hy0, hy'0]
      · rw [hy1, hy'1]
      · obtain ⟨i, rfl⟩ : ∃ i : Fin 6, j = i.succ.succ :=
          ⟨⟨j.val - 2, by have := j.isLt; omega⟩, Fin.ext (by simp only [Fin.val_succ]; omega)⟩
        exact congrFun hyy i
    apply Subtype.ext
    apply Units.ext
    refine Matrix.ext_of_mulVec_single fun j => ?_
    by_cases hj : j = 1
    · subst hj
      exact he1
    · have hj1 : (Pi.single j 1 : Fin 8 → ZMod 3) 1 = 0 := Pi.single_eq_of_ne (Ne.symm hj) _
      rw [hyv _ hj1, hy'v _ hj1]
  have hψsurj : Function.Surjective ψ := by
    intro f
    obtain ⟨y, hy, hyw⟩ := hA'Γ (Fin.cons 0 (Fin.cons 0 f) : Fin 8 → ZMod 3) rfl rfl
    refine ⟨⟨y, hy⟩, funext fun i => ?_⟩
    show ((y : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ Pi.single 1 1) i.succ.succ = f i
    rw [hyw, Pi.add_apply, Pi.single_eq_of_ne ((by decide : ∀ i : Fin 6,
      (i.succ.succ : Fin 8) ≠ 1) i), zero_add]
    simp only [Fin.cons_succ]
  have hcardS : Nat.card ↥S = 3 ^ 6 := by
    rw [Nat.card_eq_of_bijective ψ ⟨hψinj, hψsurj⟩, Nat.card_fun, Nat.card_zmod,
      Nat.card_eq_fintype_card (α := Fin 6), Fintype.card_fin]
  have hdvd : Nat.card ↥S ∣ 2903040 := hcard ▸ Subgroup.card_dvd_of_le hS_le
  rw [hcardS] at hdvd
  exact absurd hdvd (by decide)

theorem e7_A_le_of_invariant {Xg : Subgroup (GL (Fin 8) (ZMod 3))}
    (hH : ∀ A ∈ hSeven, ∃ x ∈ Xg, (x : Matrix (Fin 8) (Fin 8) (ZMod 3)) = A)
    (hstab : ∀ x ∈ Xg, (x : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ Pi.single 0 1 = Pi.single 0 1 →
      (∃ c : ZMod 3, (x : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ Pi.single 1 1 = c • Pi.single 1 1) →
      (x : Matrix (Fin 8) (Fin 8) (ZMod 3)) ∈ hSeven)
    (hcard : Nat.card ↥(Xg ⊓ fixE0 7) = 2903040)
    (hCA : ∀ x ∈ Xg, (x : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ Pi.single 0 1 = Pi.single 0 1 →
      ∀ v : Fin 8 → ZMod 3, v 0 = 0 → ((x : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ v) 0 = 0)
    (U : Submodule (ZMod 3) (Fin 8 → ZMod 3))
    (hU : ∀ x ∈ Xg, (x : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ Pi.single 0 1 = Pi.single 0 1 →
      ∀ u ∈ U, (x : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ u ∈ U)
    (v : Fin 8 → ZMod 3) (hv : v ∈ U) (i : Fin 8) (hi0 : i ≠ 0) (hvi : v i ≠ 0)
    (w : Fin 8 → ZMod 3) (hw : w 0 = 0) : w ∈ U := by
  have hHU : ∀ A ∈ hSeven, ∀ u ∈ U, A *ᵥ u ∈ U := by
    intro A hA u hu
    obtain ⟨x, hx, rfl⟩ := hH A hA
    obtain ⟨σ, s, -, ⟨hσ0, hs0, -, -⟩, hxσ⟩ := hA
    exact hU x hx (by rw [hxσ, spMat_mulVec_single, hσ0, hs0, one_mul]) u hu
  have hSU : ∀ A ∈ hSix, ∀ u ∈ U, A *ᵥ u ∈ U := fun A hA => hHU A (hSix_subset_hSeven hA)
  have hA'U : ∀ w : Fin 8 → ZMod 3, w 0 = 0 → w 1 = 0 → w ∈ U := by
    by_contra hcon
    have hvan : ∀ u ∈ U, ∀ k : Fin 8, 2 ≤ k.val → u k = 0 := by
      intro u hu k hk
      by_contra huk
      exact hcon fun w hw0 hw1 => subset_of_hSix_invariant hSU hu hk huk hw0 hw1
    have hi1 : i = 1 := by
      rcases fin8_cases i with rfl | rfl | hi
      · exact absurd rfl hi0
      · rfl
      · exact absurd (hvan v hv i hi) hvi
    subst hi1
    have he1 := e1_mem_of_hSeven_invariant hHU hv hvi
    obtain ⟨x, hxX, hxe, hxmove⟩ := e7_exists_move hstab hcard
    refine hxmove ⟨((x : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ Pi.single 1 1) 1, ?_⟩
    have hxU := hU x hxX hxe _ he1
    funext j
    rcases fin8_cases j with rfl | rfl | hj
    · rw [hCA x hxX hxe _ (by simp)]
      simp
    · simp
    · have hj1 : j ≠ 1 := by
        rintro rfl
        exact absurd hj (by decide)
      rw [hvan _ hxU j hj, Pi.smul_apply, Pi.single_eq_of_ne hj1, smul_zero]
  have he1U : (Pi.single 1 1 : Fin 8 → ZMod 3) ∈ U := by
    by_contra hcon
    have hvan : ∀ u ∈ U, u 1 = 0 := fun u hu => by
      by_contra hu1
      exact hcon (e1_mem_of_hSeven_invariant hHU hu hu1)
    refine e7_not_H0_invariant hH hstab hcard hCA fun x hxX hxe u hu1 => ?_
    have hA' : u - u 0 • Pi.single 0 1 ∈ U := hA'U _ (by simp) (by simp [hu1])
    have hsplit : u = u 0 • Pi.single 0 1 + (u - u 0 • Pi.single 0 1) := by abel
    rw [hsplit, Matrix.mulVec_add, Matrix.mulVec_smul, hxe, Pi.add_apply,
      hvan _ (hU x hxX hxe _ hA')]
    simp
  have hsplit : w = (w - w 1 • Pi.single 1 1) + w 1 • Pi.single 1 1 := by abel
  rw [hsplit]
  exact U.add_mem (hA'U _ (by simp [hw]) (by simp)) (U.smul_mem _ he1U)

theorem e7_transv_of_normal3 {Xg Mg : Subgroup (GL (Fin 8) (ZMod 3))}
    (hH : ∀ A ∈ hSeven, ∃ x ∈ Xg, (x : Matrix (Fin 8) (Fin 8) (ZMod 3)) = A)
    (hstab : ∀ x ∈ Xg, (x : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ Pi.single 0 1 = Pi.single 0 1 →
      (∃ c : ZMod 3, (x : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ Pi.single 1 1 = c • Pi.single 1 1) →
      (x : Matrix (Fin 8) (Fin 8) (ZMod 3)) ∈ hSeven)
    (hcard : Nat.card ↥(Xg ⊓ fixE0 7) = 2903040)
    (hCA : ∀ x ∈ Xg, (x : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ Pi.single 0 1 = Pi.single 0 1 →
      ∀ v : Fin 8 → ZMod 3, v 0 = 0 → ((x : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ v) 0 = 0)
    (hfus : ∃ x ∈ Xg, ∃ i : Fin 8, i ≠ 0 ∧
      ((x : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ Pi.single 0 1) i ≠ 0)
    (hMn : ∀ g ∈ Xg, ∀ m ∈ Mg, g * m * g⁻¹ ∈ Mg)
    (hM3 : ∀ m ∈ Mg, m ^ 3 = 1) (hne : Mg ≠ ⊥) :
    (∀ x ∈ Xg, ∀ v : Fin 8 → ZMod 3, v 0 = 0 →
        ((x : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ v) 0 = 0) ∧
      ∀ β : Fin 8 → ZMod 3, β 0 = 0 → ∃ m ∈ Mg,
        (m : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ Pi.single 0 1 = Pi.single 0 1 + β ∧
          ∀ v : Fin 8 → ZMod 3, v 0 = 0 →
            (m : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ v = v :=
  transv_of_normal3_of_irred (e7_A_le_of_invariant hH hstab hcard hCA) hfus hMn hM3 hne

end CFSG.StandardType.FrameRoute.FS81

end
