module

public import CFSG.Quasithin.Background.JonesParshallSL3Perfect

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open Matrix Matrix.SpecialLinearGroup
open CFSG.Quasithin.JonesParshall (SL3 sl3Diag sl3Diag_coe sl3Diag_conj_transvection
  sl3Diag_ne_zero)

namespace K7

section Torus

variable {W : Type*} [CommGroup W]

@[expose] def commHom (D : MulAut W) : W →* W where
  toFun w := D w * w⁻¹
  map_one' := by rw [map_one, one_mul, inv_one]
  map_mul' a b := by rw [map_mul, mul_inv, mul_mul_mul_comm]

theorem commHom_apply (D : MulAut W) (w : W) : commHom D w = D w * w⁻¹ := rfl

theorem le_range_commHom [Finite W] (D : MulAut W) {M : Subgroup W}
    (hM : ∀ m ∈ M, D m ∈ M) (hfix : ∀ m ∈ M, D m = m → m = 1) : M ≤ (commHom D).range := by
  let φ : M → M := fun m => ⟨commHom D m, M.mul_mem (hM m m.2) (M.inv_mem m.2)⟩
  have hinj : Function.Injective φ := by
    intro a b hab
    have h := congrArg Subtype.val hab
    change commHom D a = commHom D b at h
    have h1 : commHom D ((a : W) * (b : W)⁻¹) = 1 := by rw [map_mul, map_inv, h, mul_inv_cancel]
    rw [commHom_apply, mul_inv_eq_one] at h1
    exact Subtype.ext (mul_inv_eq_one.mp (hfix _ (M.mul_mem a.2 (M.inv_mem b.2)) h1))
  intro m hm
  obtain ⟨a, ha⟩ := Finite.surjective_of_injective hinj ⟨m, hm⟩
  exact ⟨a, congrArg Subtype.val ha⟩

theorem range_commHom_inf (D : MulAut W) {k : ℕ} (hk : Odd k) (hD : D ^ k = 1)
    (hW : ∀ w : W, w ^ 2 = 1) {Z : Subgroup W} (hZ : ∀ z ∈ Z, D z = z) :
    (commHom D).range ⊓ Z = ⊥ := by
  rw [eq_bot_iff]
  rintro u ⟨⟨w, rfl⟩, hu⟩
  have hZi : ∀ i : ℕ, (D ^ i) (commHom D w) = commHom D w := by
    intro i
    induction i with
    | zero => rw [pow_zero, MulAut.one_apply]
    | succ i ih => rw [pow_succ', MulAut.mul_apply, ih, hZ _ hu]
  have h1 : ∏ i ∈ Finset.range k, (D ^ i) (commHom D w) = 1 := by
    have e : ∀ i, (D ^ i) (commHom D w) = (D ^ (i + 1)) w / (D ^ i) w := by
      intro i
      rw [commHom_apply, map_mul, map_inv, pow_succ, MulAut.mul_apply, div_eq_mul_inv]
    simp_rw [e]
    rw [Finset.prod_range_div (fun i => (D ^ i) w), hD, pow_zero, div_self']
  simp_rw [hZi, Finset.prod_const, Finset.card_range] at h1
  obtain ⟨j, rfl⟩ := hk
  rw [pow_succ, pow_mul, hW, one_pow, one_mul] at h1
  exact Subgroup.mem_bot.mpr h1

end Torus

section SL3

variable {K : Type} [Field K]

theorem comm_transvection {d : Fin 3 → K} (h : d 0 * d 1 * d 2 = 1) {i j : Fin 3} (hij : i ≠ j)
    (hd : d i = d j) (a : K) :
    sl3Diag d h * transvection hij a = transvection hij a * sl3Diag d h := by
  rw [← mul_inv_eq_iff_eq_mul, sl3Diag_conj_transvection, hd, mul_comm (d j) a,
    mul_inv_cancel_right₀ (sl3Diag_ne_zero h j)]

theorem transvection_comm_eq {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a : K) :
    transvection hij a * transvection hjk 1 * transvection hij (-a) * transvection hjk (-1) =
      transvection hik a := by
  apply Subtype.ext
  simp only [coe_mul, transvection_coe, mul_add, add_mul, one_mul, mul_one,
    single_mul_single_same, single_mul_single_of_ne _ _ _ _ hik.symm,
    single_mul_single_of_ne _ _ _ _ hjk.symm, single_mul_single_of_ne _ _ _ _ hij.symm]
  simp only [zero_mul, add_zero, mul_neg, mul_one, neg_neg, ← single_neg]
  abel

theorem sl3_induction {P : SL3 K → Prop} (hmul : ∀ A B, P A → P B → P (A * B))
    {d d' : Fin 3 → K} (h : d 0 * d 1 * d 2 = 1) (h' : d' 0 * d' 1 * d' 2 = 1)
    (hd : d 0 = d 1) (hd' : d' 1 = d' 2)
    (hC : ∀ A, sl3Diag d h * A = A * sl3Diag d h → P A)
    (hC' : ∀ A, sl3Diag d' h' * A = A * sl3Diag d' h' → P A) (M : SL3 K) : P M := by
  have h01 : ∀ a, P (transvection (show (0 : Fin 3) ≠ 1 by decide) a) := fun a =>
    hC _ (comm_transvection h _ hd a)
  have h10 : ∀ a, P (transvection (show (1 : Fin 3) ≠ 0 by decide) a) := fun a =>
    hC _ (comm_transvection h _ hd.symm a)
  have h12 : ∀ a, P (transvection (show (1 : Fin 3) ≠ 2 by decide) a) := fun a =>
    hC' _ (comm_transvection h' _ hd' a)
  have h21 : ∀ a, P (transvection (show (2 : Fin 3) ≠ 1 by decide) a) := fun a =>
    hC' _ (comm_transvection h' _ hd'.symm a)
  refine diagonal_transvection_induction' P M (fun i j hij c hc => hC _ ?_) (fun i j hij a => ?_)
    hmul
  · apply Subtype.ext
    simp only [coe_mul, sl3Diag_coe, diag2n_coe, diagonal_mul_diagonal]
    congr 1
    funext k
    exact mul_comm _ _
  · fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact h01 a
    · rw [← transvection_comm_eq (show (0 : Fin 3) ≠ 1 by decide) (show (1 : Fin 3) ≠ 2 by decide)
        (show (0 : Fin 3) ≠ 2 by decide) a]
      exact hmul _ _ (hmul _ _ (hmul _ _ (h01 a) (h12 1)) (h01 (-a))) (h12 (-1))
    · exact h10 a
    · exact absurd rfl hij
    · exact h12 a
    · rw [← transvection_comm_eq (show (2 : Fin 3) ≠ 1 by decide) (show (1 : Fin 3) ≠ 0 by decide)
        (show (2 : Fin 3) ≠ 0 by decide) a]
      exact hmul _ _ (hmul _ _ (hmul _ _ (h21 a) (h10 1)) (h21 (-a))) (h10 (-1))
    · exact h21 a
    · exact absurd rfl hij

end SL3

end K7

end CFSG.Quasithin.Vol2.Ch11.SecB
