module

public import CFSG.RankThree.PartOne.SEITZQ1.Twist
public import CFSG.RankThree.PartOne.Q1327T.Item7D4W

public noncomputable section

namespace CFSG.RankThree.PartOne.SEITZQ1

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.PartOne.KF4 CFSG.RankThree.PartOne.KLR

theorem quadForm_neg_single_zero : ReeTag.F4.quadForm (-Pi.single 0 1) = 4 := by decide +kernel

theorem quadForm_neg_single_three : ReeTag.F4.quadForm (-Pi.single 3 1) = 2 := by decide +kernel

theorem dualRoot_neg_single_zero :
    ReeTag.F4.dualRoot (-Pi.single 0 1) = -Pi.single 3 1 := by
  funext k; fin_cases k <;> decide +kernel

theorem dualRoot_neg_single_three :
    ReeTag.F4.dualRoot (-Pi.single 3 1) = -Pi.single 0 1 := by
  funext k; fin_cases k <;> decide +kernel

theorem dualRoot_single_zero : ReeTag.F4.dualRoot (Pi.single 0 1) = Pi.single 3 1 := by
  funext k; fin_cases k <;> decide +kernel

theorem dualRoot_single_three : ReeTag.F4.dualRoot (Pi.single 3 1) = Pi.single 0 1 := by
  funext k; fin_cases k <;> decide +kernel

variable {L : Type} [Field L] [CharP L 2]

@[expose] def q1A (L : Type) [Field L] (i : Fin ReeTag.F4.tag.rank) (x : L) :
    ModGL ReeTag.F4.tag L :=
  pinnedX ReeTag.F4.tag L (-Pi.single i 1) x * pinnedX ReeTag.F4.tag L (Pi.single i 1) 1

@[expose] def q1CA (ω : L) : ModGL ReeTag.F4.tag L := q1A L 0 ω * q1A L 3 ω

@[expose] def q1CL (ω : L) : ModGL ReeTag.F4.tag L :=
  canonicalRep (coxeterSystem ReeTag.F4.tag) L q1V * q1CA ω *
    (canonicalRep (coxeterSystem ReeTag.F4.tag) L q1V)⁻¹

@[expose] def q1C (ω : L) : ModGL ReeTag.F4.tag L := q1CA ω * q1CL ω

theorem canonicalRep_simple_eq_pinnedX (i : Fin ReeTag.F4.tag.rank) :
    canonicalRep (coxeterSystem ReeTag.F4.tag) L ((coxeterSystem ReeTag.F4.tag).simple i) =
      pinnedX ReeTag.F4.tag L (Pi.single i 1) 1 * pinnedX ReeTag.F4.tag L (-Pi.single i 1) 1 *
        pinnedX ReeTag.F4.tag L (Pi.single i 1) 1 := by
  rw [canonicalRep_simple, CFSG.Blueprint.Chevalley.weylElt_eq_xUnit_mul, pinnedX_single,
    pinnedX_neg_single]
  simp [CharTwo.neg_eq]

theorem q1A_mul_simple (i : Fin ReeTag.F4.tag.rank) (x : L) :
    q1A L i x * canonicalRep (coxeterSystem ReeTag.F4.tag) L ((coxeterSystem ReeTag.F4.tag).simple i) =
      q1A L i (x + 1) := by
  rw [canonicalRep_simple_eq_pinnedX, q1A, q1A, pinnedX_add]
  have h2 : pinnedX ReeTag.F4.tag L (Pi.single i 1) 1 * pinnedX ReeTag.F4.tag L (Pi.single i 1) 1 =
      1 := by
    rw [← pinnedX_add, CharTwo.add_self_eq_zero, pinnedX_zero]
  calc pinnedX ReeTag.F4.tag L (-Pi.single i 1) x * pinnedX ReeTag.F4.tag L (Pi.single i 1) 1 *
        (pinnedX ReeTag.F4.tag L (Pi.single i 1) 1 * pinnedX ReeTag.F4.tag L (-Pi.single i 1) 1 *
          pinnedX ReeTag.F4.tag L (Pi.single i 1) 1)
      = pinnedX ReeTag.F4.tag L (-Pi.single i 1) x *
          (pinnedX ReeTag.F4.tag L (Pi.single i 1) 1 * pinnedX ReeTag.F4.tag L (Pi.single i 1) 1) *
          pinnedX ReeTag.F4.tag L (-Pi.single i 1) 1 * pinnedX ReeTag.F4.tag L (Pi.single i 1) 1 := by
        group
    _ = _ := by rw [h2, mul_one]

omit [CharP L 2] in
theorem q1A_mem_adjoint (i : Fin ReeTag.F4.tag.rank) (x : L) :
    q1A L i x ∈ adjointGroup ReeTag.F4.tag L :=
  mul_mem (pinnedX_mem_adjointGroup _ x) (pinnedX_mem_adjointGroup _ 1)

variable {a : ℕ} {F : MulAut (adjointGroup ReeTag.F4.tag L)}

theorem q1A_zero_fext (hF : IsReeFrob a F) (x : L) :
    Fext F (q1A L 0 x) = q1A L 3 (x ^ 2 ^ a) := by
  rw [q1A, Fext_mul F (pinnedX_mem_adjointGroup _ x) (pinnedX_mem_adjointGroup _ 1),
    hF.fext_pinnedX (isRoot_neg_single _ _), hF.fext_pinnedX (isRoot_single _ _),
    dualRoot_neg_single_zero, dualRoot_single_zero, one_pow, rootExp, quadForm_neg_single_zero]
  rfl

theorem q1A_three_fext (hF : IsReeFrob a F) (x : L) :
    Fext F (q1A L 3 x) = q1A L 0 (x ^ 2 ^ (a + 1)) := by
  rw [q1A, Fext_mul F (pinnedX_mem_adjointGroup _ x) (pinnedX_mem_adjointGroup _ 1),
    hF.fext_pinnedX (isRoot_neg_single _ _), hF.fext_pinnedX (isRoot_single _ _),
    dualRoot_neg_single_three, dualRoot_single_three, one_pow, rootExp,
    quadForm_neg_single_three]
  rfl

theorem quadForm_single_zero : ReeTag.F4.quadForm (Pi.single 0 1) = 4 := by decide +kernel

omit [CharP L 2] in
theorem q1A_zero_commute_three (x y : L) : Commute (q1A L 0 x) (q1A L 3 y) := by
  have h1 : Commute (pinnedX ReeTag.F4.tag L (-Pi.single 0 1) x)
      (pinnedX ReeTag.F4.tag L (-Pi.single 3 1) y) :=
    commute_pinnedX_of_long_orthogonal (isRoot_neg_single _ _) (isRoot_neg_single _ _)
      quadForm_neg_single_zero (by decide +kernel) _ _
  have h2 : Commute (pinnedX ReeTag.F4.tag L (-Pi.single 0 1) x)
      (pinnedX ReeTag.F4.tag L (Pi.single 3 1) 1) :=
    commute_pinnedX_of_long_orthogonal (isRoot_neg_single _ _) (isRoot_single _ _)
      quadForm_neg_single_zero (by decide +kernel) _ _
  have h3 : Commute (pinnedX ReeTag.F4.tag L (Pi.single 0 1) 1)
      (pinnedX ReeTag.F4.tag L (-Pi.single 3 1) y) :=
    commute_pinnedX_of_long_orthogonal (isRoot_single _ _) (isRoot_neg_single _ _)
      quadForm_single_zero (by decide +kernel) _ _
  have h4 : Commute (pinnedX ReeTag.F4.tag L (Pi.single 0 1) 1)
      (pinnedX ReeTag.F4.tag L (Pi.single 3 1) 1) :=
    commute_pinnedX_of_long_orthogonal (isRoot_single _ _) (isRoot_single _ _)
      quadForm_single_zero (by decide +kernel) _ _
  exact (h1.mul_right h2).mul_left (h3.mul_right h4)

theorem omega_pow_two_pow {ω : L} (hω : ω ^ 2 + ω + 1 = 0) :
    ∀ a : ℕ, (Even a → ω ^ 2 ^ a = ω) ∧ (Odd a → ω ^ 2 ^ a = ω + 1) := by
  have h2 : (2 : L) = 0 := CharTwo.two_eq_zero
  have hsq : ω ^ 2 = ω + 1 := by linear_combination hω - (ω + 1) * h2
  intro a
  induction a with
  | zero => exact ⟨fun _ => by simp, fun h => absurd h (by decide)⟩
  | succ a ih =>
    rw [pow_succ, pow_mul]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [ih.2 (Nat.not_even_iff_odd.1 (Nat.even_add_one.1 h))]
      linear_combination hsq + (ω + 1) * h2
    · rw [ih.1 (Nat.not_odd_iff_even.1 (Nat.odd_add_one.1 h)), hsq]

theorem simple_smul_eq_wordMat (i : Fin ReeTag.F4.tag.rank) (γ : Fin ReeTag.F4.tag.rank → ℤ) :
    (coxeterSystem ReeTag.F4.tag).simple i • γ =
      CFSG.RankThree.Lattice.wordMat Tag.F4 [i] *ᵥ γ := by
  rw [← CoxeterSystem.wordProd_singleton]
  exact CFSG.RankThree.PartOne.KE.wordProd_smul_eq_wordMat_mulVec Tag.F4 _ _

theorem commute_canonicalRep_pinnedX {w : WeylGroup ReeTag.F4.tag}
    {γ : Fin ReeTag.F4.tag.rank → ℤ} (hγ : IsRoot ReeTag.F4.tag γ) (hw : w • γ = γ) (t : L) :
    Commute (canonicalRep (coxeterSystem ReeTag.F4.tag) L w) (pinnedX ReeTag.F4.tag L γ t) := by
  have h := canonicalRep_conj_pinnedX (L := L) w hγ t
  rw [hw, mul_inv_eq_iff_eq_mul] at h
  exact h

theorem commute_simple_q1A (i j : Fin ReeTag.F4.tag.rank)
    (h : (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0)) (y : L) :
    Commute (canonicalRep (coxeterSystem ReeTag.F4.tag) L ((coxeterSystem ReeTag.F4.tag).simple i))
      (q1A L j y) := by
  have hfix : (coxeterSystem ReeTag.F4.tag).simple i • (Pi.single j 1 : Fin ReeTag.F4.tag.rank → ℤ) =
      Pi.single j 1 ∧ (coxeterSystem ReeTag.F4.tag).simple i •
        (-Pi.single j 1 : Fin ReeTag.F4.tag.rank → ℤ) = -Pi.single j 1 := by
    rw [simple_smul_eq_wordMat, simple_smul_eq_wordMat]
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      exact ⟨by funext k; fin_cases k <;> decide +kernel, by funext k; fin_cases k <;> decide +kernel⟩
  exact (commute_canonicalRep_pinnedX (isRoot_neg_single _ _) hfix.2 y).mul_right
    (commute_canonicalRep_pinnedX (isRoot_single _ _) hfix.1 1)

theorem q1CA_fext (hF : IsReeFrob a F) {ω : L} (hω : ω ^ 2 + ω + 1 = 0) :
    Fext F (q1CA ω) =
      q1CA ω * canonicalRep (coxeterSystem ReeTag.F4.tag) L
        ((coxeterSystem ReeTag.F4.tag).simple (q1Par a)) := by
  rw [q1CA, Fext_mul F (q1A_mem_adjoint 0 ω) (q1A_mem_adjoint 3 ω), q1A_zero_fext hF,
    q1A_three_fext hF]
  rcases Nat.even_or_odd a with ha | ha
  · have hp : q1Par a = 0 := by simp [q1Par, Nat.even_iff.1 ha]
    rw [hp, (omega_pow_two_pow hω a).1 ha, (omega_pow_two_pow hω (a + 1)).2 (Even.add_one ha),
      ← q1A_mul_simple, ← mul_assoc, ← (q1A_zero_commute_three ω ω).eq]
  · have hp : q1Par a = 3 := by simp [q1Par, Nat.odd_iff.1 ha]
    rw [hp, (omega_pow_two_pow hω a).2 ha, (omega_pow_two_pow hω (a + 1)).1 (Odd.add_one ha),
      ← q1A_mul_simple, mul_assoc, (commute_simple_q1A 3 0 (Or.inr ⟨rfl, rfl⟩) ω).eq,
      ← mul_assoc, ← (q1A_zero_commute_three ω ω).eq]

omit [CharP L 2] in
theorem q1CA_mem_adjoint (ω : L) : q1CA ω ∈ adjointGroup ReeTag.F4.tag L :=
  mul_mem (q1A_mem_adjoint 0 ω) (q1A_mem_adjoint 3 ω)

omit [CharP L 2] in
theorem q1CL_mem_adjoint (ω : L) : q1CL ω ∈ adjointGroup ReeTag.F4.tag L :=
  mul_mem (mul_mem (canonicalRep_mem_adjointGroup _ L _) (q1CA_mem_adjoint ω))
    (inv_mem (canonicalRep_mem_adjointGroup _ L _))

omit [CharP L 2] in
theorem q1C_mem_adjoint (ω : L) : q1C ω ∈ adjointGroup ReeTag.F4.tag L :=
  mul_mem (q1CA_mem_adjoint ω) (q1CL_mem_adjoint ω)

omit [CharP L 2] in
theorem q1V_weylPerm : ReeTag.F4.weylPerm q1V = q1V := by
  have h1 : ∀ (l : List (Fin ReeTag.F4.tag.rank)) (u : Fin ReeTag.F4.tag.rank → ℤ),
      (coxeterSystem ReeTag.F4.tag).wordProd l • u =
        CFSG.RankThree.Lattice.wordMat Tag.F4 l *ᵥ u := fun l u =>
    CFSG.RankThree.PartOne.KE.wordProd_smul_eq_wordMat_mulVec Tag.F4 l u
  rw [q1V, ReeTag.weylPerm_wordProd]
  refine CFSG.RankThree.E6.eq_of_smul_single_eq fun j => ?_
  rw [h1, h1]
  fin_cases j <;> (funext k; fin_cases k <;> decide +kernel)

theorem q1CL_eq (ω : L) :
    q1CL ω = pinnedX ReeTag.F4.tag L (q1V • -Pi.single 0 1) ω *
      pinnedX ReeTag.F4.tag L (q1V • Pi.single 0 1) 1 *
      pinnedX ReeTag.F4.tag L (q1V • -Pi.single 3 1) ω *
      pinnedX ReeTag.F4.tag L (q1V • Pi.single 3 1) 1 := by
  rw [← canonicalRep_conj_pinnedX q1V (isRoot_neg_single _ _),
    ← canonicalRep_conj_pinnedX q1V (isRoot_single _ _),
    ← canonicalRep_conj_pinnedX q1V (isRoot_neg_single _ _),
    ← canonicalRep_conj_pinnedX q1V (isRoot_single _ _), q1CL, q1CA, q1A, q1A]
  group

theorem commute_simple_q1CL {i : Fin ReeTag.F4.tag.rank} (hi : i = 0 ∨ i = 3) (ω : L) :
    Commute (canonicalRep (coxeterSystem ReeTag.F4.tag) L ((coxeterSystem ReeTag.F4.tag).simple i))
      (q1CL ω) := by
  have hfix : ∀ γ : Fin ReeTag.F4.tag.rank → ℤ, (γ = -Pi.single 0 1 ∨ γ = Pi.single 0 1 ∨
      γ = -Pi.single 3 1 ∨ γ = Pi.single 3 1) →
      (coxeterSystem ReeTag.F4.tag).simple i • (q1V • γ) = q1V • γ := by
    intro γ hγ
    rw [simple_smul_eq_wordMat, q1V_smul]
    rcases hi with rfl | rfl <;> rcases hγ with rfl | rfl | rfl | rfl <;>
      (funext k; fin_cases k <;> decide +kernel)
  have hr : ∀ γ : Fin ReeTag.F4.tag.rank → ℤ, IsRoot ReeTag.F4.tag γ →
      IsRoot ReeTag.F4.tag (q1V • γ) := fun γ hγ => IsRoot.smul hγ q1V
  rw [q1CL_eq]
  refine ((((commute_canonicalRep_pinnedX (hr _ (isRoot_neg_single _ _))
    (hfix _ (Or.inl rfl)) ω).mul_right (commute_canonicalRep_pinnedX (hr _ (isRoot_single _ _))
    (hfix _ (Or.inr (Or.inl rfl))) 1)).mul_right (commute_canonicalRep_pinnedX
    (hr _ (isRoot_neg_single _ _)) (hfix _ (Or.inr (Or.inr (Or.inl rfl)))) ω)).mul_right
    (commute_canonicalRep_pinnedX (hr _ (isRoot_single _ _)) (hfix _ (Or.inr (Or.inr (Or.inr rfl))))
      1))

theorem q1N_eq (a : ℕ) :
    q1N L a = canonicalRep (coxeterSystem ReeTag.F4.tag) L
        ((coxeterSystem ReeTag.F4.tag).simple (q1Par a)) *
      canonicalRep (coxeterSystem ReeTag.F4.tag) L q1V *
      canonicalRep (coxeterSystem ReeTag.F4.tag) L
        ((coxeterSystem ReeTag.F4.tag).simple (q1Par a)) *
      (canonicalRep (coxeterSystem ReeTag.F4.tag) L q1V)⁻¹ := by
  have hinv : canonicalRep (coxeterSystem ReeTag.F4.tag) L q1V⁻¹ =
      (canonicalRep (coxeterSystem ReeTag.F4.tag) L q1V)⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← CFSG.RankThree.PartOne.Q1327T.canonicalRep_mul_charTwo,
      inv_mul_cancel, canonicalRep_one]
  have hw : q1W (q1Par a) = (coxeterSystem ReeTag.F4.tag).simple (q1Par a) * q1V *
      (coxeterSystem ReeTag.F4.tag).simple (q1Par a) * q1V⁻¹ := by
    rw [q1W, q1WWord, CoxeterSystem.wordProd_append, CoxeterSystem.wordProd_append,
      CoxeterSystem.wordProd_append, CoxeterSystem.wordProd_singleton,
      CoxeterSystem.wordProd_reverse, ← q1V]
  rw [q1N, hw, CFSG.RankThree.PartOne.Q1327T.canonicalRep_mul_charTwo,
    CFSG.RankThree.PartOne.Q1327T.canonicalRep_mul_charTwo,
    CFSG.RankThree.PartOne.Q1327T.canonicalRep_mul_charTwo, hinv]

theorem q1C_fext (hF : IsReeFrob a F) {ω : L} (hω : ω ^ 2 + ω + 1 = 0) :
    Fext F (q1C ω) = q1C ω * q1N L a := by
  have hv := canonicalRep_mem_adjointGroup (coxeterSystem ReeTag.F4.tag) L q1V
  have hCL : Fext F (q1CL ω) = q1CL ω *
      (canonicalRep (coxeterSystem ReeTag.F4.tag) L q1V *
        canonicalRep (coxeterSystem ReeTag.F4.tag) L
          ((coxeterSystem ReeTag.F4.tag).simple (q1Par a)) *
        (canonicalRep (coxeterSystem ReeTag.F4.tag) L q1V)⁻¹) := by
    rw [q1CL, Fext_conj F hv (q1CA_mem_adjoint ω), hF.fext_canonicalRep, q1V_weylPerm,
      q1CA_fext hF hω]
    group
  rw [q1C, Fext_mul F (q1CA_mem_adjoint ω) (q1CL_mem_adjoint ω), q1CA_fext hF hω, hCL, q1N_eq]
  simp only [mul_assoc]
  rw [← mul_assoc (canonicalRep (coxeterSystem ReeTag.F4.tag) L
    ((coxeterSystem ReeTag.F4.tag).simple (q1Par a))) (q1CL ω),
    (commute_simple_q1CL (q1Par_cases a) ω).eq]
  group

end CFSG.RankThree.PartOne.SEITZQ1
