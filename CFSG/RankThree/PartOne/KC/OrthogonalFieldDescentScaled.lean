module

public import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescentSplit

public section

namespace CFSG.RankThree.PartOne.KCOrthogonalDescent

open Module QuadraticMap CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.Orthogonal

variable {F W : Type} [Field F] [AddCommGroup W] [Module F W] {Q : QuadraticForm F W}

namespace HypSplit

variable {m δ : ℕ} (H : HypSplit Q m δ)

@[expose] def scaleUnits (m δ : ℕ) (u : Fˣ) : Fin m ⊕ Fin m ⊕ Fin δ → Fˣ :=
  Sum.elim 1 (Sum.elim (fun _ => u) 1)

@[expose] noncomputable def scaled (u : Fˣ) : Basis (Fin m ⊕ Fin m ⊕ Fin δ) F W :=
  H.b.unitsSMul (scaleUnits m δ u)

theorem scaled_inl (u : Fˣ) (i : Fin m) : H.scaled u (.inl i) = H.b (.inl i) := by
  simp [scaled, scaleUnits, Basis.unitsSMul_apply]

theorem scaled_inr_inl (u : Fˣ) (i : Fin m) :
    H.scaled u (.inr (.inl i)) = (u : F) • H.b (.inr (.inl i)) := by
  simp [scaled, scaleUnits, Basis.unitsSMul_apply, Units.smul_def]

theorem scaled_inr_inr (u : Fˣ) (j : Fin δ) :
    H.scaled u (.inr (.inr j)) = H.b (.inr (.inr j)) := by
  simp [scaled, scaleUnits, Basis.unitsSMul_apply]

theorem scaled_eval (u : Fˣ) (x y : Fin m → F) (z : Fin δ → F) :
    Q (∑ i, x i • H.scaled u (.inl i) + ∑ i, y i • H.scaled u (.inr (.inl i)) +
      ∑ j, z j • H.scaled u (.inr (.inr j))) =
    (u : F) * ∑ i, x i * y i + Q (∑ j, z j • H.b (.inr (.inr j))) := by
  simp only [scaled_inl, scaled_inr_inl, scaled_inr_inr, smul_smul]
  rw [H.eval x (fun i => y i * (u : F)) z]
  congr 1
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem Q_eq_scaled (u : Fˣ) (w : W) :
    Q w = (u : F) * ∑ i, (H.scaled u).repr w (.inl i) * (H.scaled u).repr w (.inr (.inl i)) +
      Q (∑ j, (H.scaled u).repr w (.inr (.inr j)) • H.b (.inr (.inr j))) := by
  have h := (H.scaled u).sum_repr w
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type] at h
  have h2 : ∑ i, (H.scaled u).repr w (.inl i) • H.scaled u (.inl i) +
      ∑ i, (H.scaled u).repr w (.inr (.inl i)) • H.scaled u (.inr (.inl i)) +
      ∑ j, (H.scaled u).repr w (.inr (.inr j)) • H.scaled u (.inr (.inr j)) = w := by
    rw [add_assoc]
    exact h
  conv_lhs => rw [← h2]
  exact H.scaled_eval u _ _ _

theorem tail_one (H : HypSplit Q m 1) (z : Fin 1 → F) :
    Q (∑ j, z j • H.b (.inr (.inr j))) = z 0 ^ 2 * Q (H.b (.inr (.inr 0))) := by
  rw [Fin.sum_univ_one, map_smul_eq_sq Q]

theorem tail_two (H : HypSplit Q m 2) (z : Fin 2 → F) :
    Q (∑ j, z j • H.b (.inr (.inr j))) = z 0 ^ 2 * Q (H.b (.inr (.inr 0))) +
      z 1 ^ 2 * Q (H.b (.inr (.inr 1))) +
      z 0 * z 1 * polar Q (H.b (.inr (.inr 0))) (H.b (.inr (.inr 1))) := by
  rw [Fin.sum_univ_two, QuadraticMap.map_add (⇑Q), map_smul_eq_sq Q, map_smul_eq_sq Q,
    polar_smul_left_eq Q, polar_smul_right_eq Q]
  ring

theorem Q_tail_one_ne_zero (H : HypSplit Q m 1) : Q (H.b (.inr (.inr 0))) ≠ 0 := by
  intro h0
  have := H.aniso (fun _ => 1) (by rw [tail_one, h0, mul_zero])
  exact one_ne_zero (congrFun this 0)

theorem Q_tail_two_ne_zero (H : HypSplit Q m 2) : Q (H.b (.inr (.inr 0))) ≠ 0 := by
  intro h0
  have := H.aniso ![1, 0] (by rw [tail_two, h0]; simp)
  exact one_ne_zero (congrFun this 0)

@[expose] def plusEquiv (n : ℕ) : (Fin n ⊕ Fin n ⊕ Fin 0) ≃ (Fin n ⊕ Fin n) :=
  Equiv.sumCongr (Equiv.refl _) (Equiv.sumEmpty (Fin n) (Fin 0))

@[expose] def oddEquiv (n : ℕ) : (Fin n ⊕ Fin n ⊕ Fin 1) ≃ (Fin n ⊕ Fin n ⊕ Unit) :=
  Equiv.sumCongr (Equiv.refl _) (Equiv.sumCongr (Equiv.refl _) finOneEquiv)

theorem Q_eq_repr (w : W) :
    Q w = ∑ i, H.b.repr w (.inl i) * H.b.repr w (.inr (.inl i)) +
      Q (∑ j, H.b.repr w (.inr (.inr j)) • H.b (.inr (.inr j))) := by
  have h := H.b.sum_repr w
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type] at h
  have h2 : ∑ i, H.b.repr w (.inl i) • H.b (.inl i) +
      ∑ i, H.b.repr w (.inr (.inl i)) • H.b (.inr (.inl i)) +
      ∑ j, H.b.repr w (.inr (.inr j)) • H.b (.inr (.inr j)) = w := by
    rw [add_assoc]
    exact h
  conv_lhs => rw [← h2]
  exact H.eval _ _ _

theorem displayPlus {n : ℕ} (H : HypSplit Q n 0) (w : W) :
    StatedQuadPlus n F ((H.b.reindex (plusEquiv n)).equivFun w) = Q w := by
  rw [H.Q_eq_repr w]
  have h0 : ∑ j : Fin 0, H.b.repr w (.inr (.inr j)) • H.b (.inr (.inr j)) = 0 :=
    Finset.sum_of_isEmpty _
  rw [h0, QuadraticMap.map_zero, add_zero, StatedQuadPlus]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [plusEquiv, Basis.equivFun_apply]

theorem displayOdd {n : ℕ} (H : HypSplit Q n 1) (u : Fˣ)
    (hu : (u : F) = Q (H.b (.inr (.inr 0)))) (w : W) :
    StatedQuadOdd n F (((H.scaled u).reindex (oddEquiv n)).equivFun w) =
      ((u⁻¹ : Fˣ) : F) * Q w := by
  rw [Q_eq_scaled H u w, tail_one, ← hu]
  have hu0 : (u : F) ≠ 0 := u.ne_zero
  rw [StatedQuadOdd]
  have h1 : ∀ i, ((H.scaled u).reindex (oddEquiv n)).equivFun w (.inl i) =
      (H.scaled u).repr w (.inl i) := by
    intro i
    simp [oddEquiv, Basis.equivFun_apply]
  have h2 : ∀ i, ((H.scaled u).reindex (oddEquiv n)).equivFun w (.inr (.inl i)) =
      (H.scaled u).repr w (.inr (.inl i)) := by
    intro i
    simp [oddEquiv, Basis.equivFun_apply]
  have h3 : ((H.scaled u).reindex (oddEquiv n)).equivFun w (.inr (.inr ())) =
      (H.scaled u).repr w (.inr (.inr 0)) := by
    have h0 : (finOneEquiv.symm () : Fin 1) = 0 := Subsingleton.elim _ _
    simp [oddEquiv, Basis.equivFun_apply, h0]
  rw [h3]
  simp only [h1, h2]
  rw [Units.val_inv_eq_inv_val]
  field_simp

theorem displayMinus {n : ℕ} (H : HypSplit Q (n - 1) 2) (u : Fˣ)
    (hu : (u : F) = Q (H.b (.inr (.inr 0)))) (w : W) :
    StatedQuadMinus n F (((u⁻¹ : Fˣ) : F) * polar Q (H.b (.inr (.inr 0))) (H.b (.inr (.inr 1))))
      (((u⁻¹ : Fˣ) : F) * Q (H.b (.inr (.inr 1)))) ((H.scaled u).equivFun w) =
      ((u⁻¹ : Fˣ) : F) * Q w := by
  rw [Q_eq_scaled H u w, tail_two, ← hu]
  have hu0 : (u : F) ≠ 0 := u.ne_zero
  rw [StatedQuadMinus]
  simp only [Basis.equivFun_apply]
  rw [Units.val_inv_eq_inv_val]
  field_simp
  ring

end HypSplit

end CFSG.RankThree.PartOne.KCOrthogonalDescent
