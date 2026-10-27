module

public import CFSG.OddTranspositions.PartThree.FiveReflection
public import CFSG.Open.StatedDefs

public section

namespace CFSG.OddTranspositions.PartThree

open Matrix CFSG.Open

lemma zmod5_pair_sq (a b : ZMod 5) : (a + 2 * b) * (a - 2 * b) = a ^ 2 + b ^ 2 := by
  have h : ∀ a b : ZMod 5, (a + 2 * b) * (a - 2 * b) = a ^ 2 + b ^ 2 := by decide
  exact h a b

lemma zmod5_pair_sq_zero (a b : ZMod 5) (h₁ : a + 2 * b = 0) (h₂ : a - 2 * b = 0) :
    a = 0 ∧ b = 0 := by
  have h : ∀ a b : ZMod 5, a + 2 * b = 0 → a - 2 * b = 0 → a = 0 ∧ b = 0 := by decide
  exact h a b h₁ h₂

lemma zmod5_mul_eq_zero {ν x : ZMod 5} (hν : ν ≠ 0) (h : ν * x = 0) : x = 0 := by
  have h' : ∀ ν x : ZMod 5, ν ≠ 0 → ν * x = 0 → x = 0 := by decide
  exact h' ν x hν h

lemma finProdFinEquiv_zero (n : ℕ) (j : Fin n) :
    finProdFinEquiv ((0 : Fin 2), j) = (⟨j.1, by omega⟩ : Fin (2 * n)) := by
  ext; rw [finProdFinEquiv_apply_val]; simp

lemma finProdFinEquiv_one (n : ℕ) (j : Fin n) :
    finProdFinEquiv ((1 : Fin 2), j) = (⟨j.1 + n, by omega⟩ : Fin (2 * n)) := by
  ext; rw [finProdFinEquiv_apply_val]; simp

lemma sum_pair_even (n : ℕ) (g : Fin (2 * n) → ZMod 5) :
    ∑ i : Fin (2 * n), g i =
      ∑ j : Fin n, (g (⟨j.1, by omega⟩ : Fin (2 * n)) +
        g (⟨j.1 + n, by omega⟩ : Fin (2 * n))) := by
  rw [← Equiv.sum_comp (finProdFinEquiv (m := 2) (n := n)) g, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, Finset.sum_add_distrib, finProdFinEquiv_zero,
    finProdFinEquiv_one]

@[expose] def fiveOddCoord (n : ℕ) (ν : ZMod 5) (i : Fin n ⊕ Fin n ⊕ Unit) :
    (Fin (2 * n + 1) → ZMod 5) →ₗ[ZMod 5] ZMod 5 :=
  match i with
  | Sum.inl j =>
      LinearMap.proj (R := ZMod 5) (φ := fun _ => ZMod 5)
          (Fin.castSucc (⟨j.1, by omega⟩ : Fin (2 * n))) +
        (2 : ZMod 5) • LinearMap.proj (R := ZMod 5) (φ := fun _ => ZMod 5)
          (Fin.castSucc (⟨j.1 + n, by omega⟩ : Fin (2 * n)))
  | Sum.inr (Sum.inl j) =>
      ν • (LinearMap.proj (R := ZMod 5) (φ := fun _ => ZMod 5)
            (Fin.castSucc (⟨j.1, by omega⟩ : Fin (2 * n))) +
          (-2 : ZMod 5) • LinearMap.proj (R := ZMod 5) (φ := fun _ => ZMod 5)
            (Fin.castSucc (⟨j.1 + n, by omega⟩ : Fin (2 * n))))
  | Sum.inr (Sum.inr _) =>
      LinearMap.proj (R := ZMod 5) (φ := fun _ => ZMod 5) (Fin.last (2 * n))

@[expose] def fiveOddMap (n : ℕ) (ν : ZMod 5) :
    (Fin (2 * n + 1) → ZMod 5) →ₗ[ZMod 5] (Fin n ⊕ Fin n ⊕ Unit → ZMod 5) :=
  LinearMap.pi (φ := fun _ => ZMod 5) (fiveOddCoord n ν)

lemma statedQuadOdd_fiveOddMap (n : ℕ) (ε : Bool) (ν : ZMod 5)
    (hνα : ν * (if ε then 1 else 2) = -1) (v : Fin (2 * n + 1) → ZMod 5) :
    (∑ j : Fin n, (fiveOddMap n ν v) (Sum.inl j) *
        (fiveOddMap n ν v) (Sum.inr (Sum.inl j))) +
      (fiveOddMap n ν v) (Sum.inr (Sum.inr ())) ^ 2 = ν * fiveForm (2 * n) ε v v := by
  have hpair : ∀ a b : ZMod 5,
      (a + 2 * b) * (ν * (a + (-2) * b)) = ν * (a ^ 2 + b ^ 2) := by
    intro a b
    rw [show a + (-2 : ZMod 5) * b = a - 2 * b by ring_nf]
    rw [← mul_assoc, mul_comm (a + 2 * b) ν, mul_assoc, zmod5_pair_sq]
  simp only [fiveForm, fiveOddMap, fiveOddCoord, LinearMap.pi_apply, LinearMap.add_apply,
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]
  have hL : (∑ j : Fin n,
        (v (Fin.castSucc (⟨j.1, by omega⟩ : Fin (2 * n))) +
            2 * v (Fin.castSucc (⟨j.1 + n, by omega⟩ : Fin (2 * n)))) *
          (ν * (v (Fin.castSucc (⟨j.1, by omega⟩ : Fin (2 * n))) +
            (-2) * v (Fin.castSucc (⟨j.1 + n, by omega⟩ : Fin (2 * n)))))) =
      ν * (∑ i : Fin (2 * n), (v (Fin.castSucc i)) ^ 2) := by
    rw [Finset.sum_congr rfl (fun j _ => hpair _ _), ← Finset.mul_sum]
    congr 1
    exact (sum_pair_even n (fun i => (v (Fin.castSucc i)) ^ 2)).symm
  rw [hL]
  have hR : (∑ i : Fin (2 * n), v (Fin.castSucc i) * v (Fin.castSucc i)) =
      ∑ i : Fin (2 * n), (v (Fin.castSucc i)) ^ 2 :=
    Finset.sum_congr rfl (fun i _ => by rw [sq])
  rw [hR, mul_sub, ← mul_assoc, hνα]
  ring

lemma fiveOddMap_eq_zero (n : ℕ) {ν : ZMod 5} (hν : ν ≠ 0)
    {w : Fin (2 * n + 1) → ZMod 5} (hw : fiveOddMap n ν w = 0) : w = 0 := by
  have hx : ∀ j : Fin n, w (Fin.castSucc (⟨j.1, by omega⟩ : Fin (2 * n))) +
      2 * w (Fin.castSucc (⟨j.1 + n, by omega⟩ : Fin (2 * n))) = 0 := by
    intro j
    have h := congr_fun hw (Sum.inl j)
    simpa [fiveOddMap, fiveOddCoord, LinearMap.pi_apply, LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.proj_apply, smul_eq_mul, Pi.zero_apply] using h
  have hy : ∀ j : Fin n, w (Fin.castSucc (⟨j.1, by omega⟩ : Fin (2 * n))) -
      2 * w (Fin.castSucc (⟨j.1 + n, by omega⟩ : Fin (2 * n))) = 0 := by
    intro j
    have h := congr_fun hw (Sum.inr (Sum.inl j))
    have h' : ν * w (Fin.castSucc (⟨j.1, by omega⟩ : Fin (2 * n))) +
        ν * ((-2) * w (Fin.castSucc (⟨j.1 + n, by omega⟩ : Fin (2 * n)))) = 0 := by
      simpa [fiveOddMap, fiveOddCoord, LinearMap.pi_apply, LinearMap.add_apply, LinearMap.smul_apply,
        LinearMap.proj_apply, smul_eq_mul, Pi.zero_apply] using h
    rw [← mul_add] at h'
    have hb : w (Fin.castSucc (⟨j.1, by omega⟩ : Fin (2 * n))) +
        (-2) * w (Fin.castSucc (⟨j.1 + n, by omega⟩ : Fin (2 * n))) = 0 :=
      zmod5_mul_eq_zero hν h'
    rwa [show w (Fin.castSucc (⟨j.1, by omega⟩ : Fin (2 * n))) -
        2 * w (Fin.castSucc (⟨j.1 + n, by omega⟩ : Fin (2 * n))) =
      w (Fin.castSucc (⟨j.1, by omega⟩ : Fin (2 * n))) +
        (-2) * w (Fin.castSucc (⟨j.1 + n, by omega⟩ : Fin (2 * n))) by ring_nf]
  have hz : w (Fin.last (2 * n)) = 0 := by
    have h := congr_fun hw (Sum.inr (Sum.inr ()))
    simpa [fiveOddMap, fiveOddCoord, LinearMap.pi_apply, LinearMap.proj_apply, Pi.zero_apply] using h
  funext i
  rcases i.eq_castSucc_or_eq_last with ⟨i', rfl⟩ | rfl
  · rcases Nat.lt_or_ge (i' : ℕ) n with hlt | hge
    · have hi : i' = (⟨i'.1, by omega⟩ : Fin (2 * n)) := Fin.ext rfl
      rw [hi]
      exact (zmod5_pair_sq_zero _ _ (hx ⟨i'.1, hlt⟩) (hy ⟨i'.1, hlt⟩)).1
    · let j : Fin n := ⟨i'.1 - n, by omega⟩
      have hji : (⟨j.1 + n, by omega⟩ : Fin (2 * n)) = i' := by
        ext; simp [j]; omega
      rw [← hji]
      exact (zmod5_pair_sq_zero _ _ (hx j) (hy j)).2
  · exact hz

lemma fiveOddMap_injective (n : ℕ) {ν : ZMod 5} (hν : ν ≠ 0) :
    Function.Injective (fiveOddMap n ν) := by
  intro u v huv
  have h0 : fiveOddMap n ν (u - v) = 0 := by rw [map_sub]; exact sub_eq_zero.mpr huv
  exact sub_eq_zero.mp (fiveOddMap_eq_zero n hν h0)

lemma card_odd (n : ℕ) :
    Fintype.card (Fin (2 * n + 1) → ZMod 5) =
      Fintype.card (Fin n ⊕ Fin n ⊕ Unit → ZMod 5) := by
  simp only [Fintype.card_fun]
  congr 1
  simp only [Fintype.card_fin, Fintype.card_sum, Fintype.card_unit]
  omega

lemma sum_pair_eq {k n : ℕ} (hn : k + 1 = 2 * n) (g : Fin (k + 1) → ZMod 5) :
    ∑ i : Fin (k + 1), g i =
      ∑ j : Fin n, (g (⟨j.1, by omega⟩ : Fin (k + 1)) +
        g (⟨j.1 + n, by omega⟩ : Fin (k + 1))) := by
  rw [(Equiv.sum_comp (finCongr hn).symm g).symm]
  rw [sum_pair_even n (fun i : Fin (2 * n) => g ((finCongr hn).symm i))]
  apply Finset.sum_congr rfl
  intro j _
  rw [show (finCongr hn).symm (⟨j.1, by omega⟩ : Fin (2 * n)) =
        (⟨j.1, by omega⟩ : Fin (k + 1)) by
      ext; simp [finCongr_symm_apply_coe],
    show (finCongr hn).symm (⟨j.1 + n, by omega⟩ : Fin (2 * n)) =
        (⟨j.1 + n, by omega⟩ : Fin (k + 1)) by
      ext; simp [finCongr_symm_apply_coe]]

lemma two_ne_zero_zmod5 : (2 : ZMod 5) ≠ 0 := by decide

lemma zmod5_pair_sq' (a b : ZMod 5) : (a + 2 * b) * (a + (-2) * b) = a ^ 2 + b ^ 2 := by
  rw [show a + (-2 : ZMod 5) * b = a - 2 * b by ring]
  exact zmod5_pair_sq a b

lemma zmod5_pair_sq_zero' (a b : ZMod 5) (h₁ : a + 2 * b = 0) (h₂ : a + (-2) * b = 0) :
    a = 0 ∧ b = 0 := by
  have h : ∀ a b : ZMod 5, a + 2 * b = 0 → a + (-2) * b = 0 → a = 0 ∧ b = 0 := by decide
  exact h a b h₁ h₂

def fiveScaleCoordLast (k : ℕ) (i : Fin (k + 1)) :
    (Fin (k + 1) → ZMod 5) →ₗ[ZMod 5] ZMod 5 :=
  if i = Fin.last k then
    (2 : ZMod 5) • LinearMap.proj (R := ZMod 5) (φ := fun _ => ZMod 5) i
  else LinearMap.proj (R := ZMod 5) (φ := fun _ => ZMod 5) i

def fiveScaleLast (k : ℕ) : (Fin (k + 1) → ZMod 5) →ₗ[ZMod 5] (Fin (k + 1) → ZMod 5) :=
  LinearMap.pi (φ := fun _ => ZMod 5) (fiveScaleCoordLast k)

lemma fiveScaleLast_eq_zero {k : ℕ} {w : Fin (k + 1) → ZMod 5}
    (hw : fiveScaleLast k w = 0) : w = 0 := by
  funext i
  have h := congr_fun hw i
  simp only [fiveScaleLast, fiveScaleCoordLast, LinearMap.pi_apply, LinearMap.smul_apply,
    LinearMap.proj_apply, smul_eq_mul, Pi.zero_apply] at h
  by_cases hi : i = Fin.last k
  · rw [if_pos hi] at h
    exact zmod5_mul_eq_zero two_ne_zero_zmod5 h
  · rw [if_neg hi] at h
    exact h

def fivePlusCoord {k n : ℕ} (hn : k + 1 = 2 * n) (i : Fin n ⊕ Fin n) :
    (Fin (k + 1) → ZMod 5) →ₗ[ZMod 5] ZMod 5 :=
  match i with
  | Sum.inl j =>
      LinearMap.proj (R := ZMod 5) (φ := fun _ => ZMod 5) (⟨j.1, by omega⟩ : Fin (k + 1)) +
        (2 : ZMod 5) • LinearMap.proj (R := ZMod 5) (φ := fun _ => ZMod 5)
          (⟨j.1 + n, by omega⟩ : Fin (k + 1))
  | Sum.inr j =>
      LinearMap.proj (R := ZMod 5) (φ := fun _ => ZMod 5) (⟨j.1, by omega⟩ : Fin (k + 1)) +
        (-2 : ZMod 5) • LinearMap.proj (R := ZMod 5) (φ := fun _ => ZMod 5)
          (⟨j.1 + n, by omega⟩ : Fin (k + 1))

def fivePlusLinear {k n : ℕ} (hn : k + 1 = 2 * n) :
    (Fin (k + 1) → ZMod 5) →ₗ[ZMod 5] (Fin n ⊕ Fin n → ZMod 5) :=
  LinearMap.pi (φ := fun _ => ZMod 5) (fivePlusCoord hn)

lemma fivePlusLinear_eq_zero {k n : ℕ} (hn : k + 1 = 2 * n) {w : Fin (k + 1) → ZMod 5}
    (hw : fivePlusLinear hn w = 0) : w = 0 := by
  have hx : ∀ j : Fin n, w (⟨j.1, by omega⟩ : Fin (k + 1)) +
      2 * w (⟨j.1 + n, by omega⟩ : Fin (k + 1)) = 0 := by
    intro j
    have h := congr_fun hw (Sum.inl j)
    simpa [fivePlusLinear, fivePlusCoord, LinearMap.pi_apply, LinearMap.add_apply,
      LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul, Pi.zero_apply] using h
  have hy : ∀ j : Fin n, w (⟨j.1, by omega⟩ : Fin (k + 1)) +
      (-2) * w (⟨j.1 + n, by omega⟩ : Fin (k + 1)) = 0 := by
    intro j
    have h := congr_fun hw (Sum.inr j)
    simpa [fivePlusLinear, fivePlusCoord, LinearMap.pi_apply, LinearMap.add_apply,
      LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul, Pi.zero_apply] using h
  funext i
  rcases Nat.lt_or_ge (i : ℕ) n with hlt | hge
  · have hi : i = (⟨i.1, by omega⟩ : Fin (k + 1)) := Fin.ext rfl
    rw [hi]
    exact (zmod5_pair_sq_zero' _ _ (hx ⟨i.1, hlt⟩) (hy ⟨i.1, hlt⟩)).1
  · let j : Fin n := ⟨i.1 - n, by omega⟩
    have hi : i = (⟨j.1 + n, by omega⟩ : Fin (k + 1)) := by
      ext; simp [j]; omega
    rw [hi]
    exact (zmod5_pair_sq_zero' _ _ (hx j) (hy j)).2

lemma statedQuadPlus_fivePlusMap {k n : ℕ} (hn : k + 1 = 2 * n)
    (v : Fin (k + 1) → ZMod 5) :
    (∑ j : Fin n, (fivePlusLinear hn (fiveScaleLast k v)) (Sum.inl j) *
        (fivePlusLinear hn (fiveScaleLast k v)) (Sum.inr j)) =
      fiveForm k true v v := by
  set w := fiveScaleLast k v with hw
  have hpair : ∀ a b : ZMod 5, (a + 2 * b) * (a + (-2) * b) = a ^ 2 + b ^ 2 :=
    fun a b => zmod5_pair_sq' a b
  have hsum : (∑ j : Fin n, (w (⟨j.1, by omega⟩ : Fin (k + 1)) ^ 2 +
        w (⟨j.1 + n, by omega⟩ : Fin (k + 1)) ^ 2)) =
      ∑ i : Fin (k + 1), w i ^ 2 := (sum_pair_eq hn (fun i => w i ^ 2)).symm
  simp only [fivePlusLinear, fivePlusCoord, LinearMap.pi_apply, LinearMap.add_apply,
    LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]
  rw [Finset.sum_congr rfl (fun j _ => hpair _ _), hsum, Fin.sum_univ_castSucc]
  have hv : ∀ i : Fin k, w (Fin.castSucc i) = v (Fin.castSucc i) := by
    intro i
    have hi : Fin.castSucc i ≠ Fin.last k := by
      intro h
      have := congrArg Fin.val h
      simp only [Fin.val_castSucc, Fin.val_last] at this
      omega
    simp only [hw, fiveScaleLast, fiveScaleCoordLast, LinearMap.pi_apply,
      LinearMap.proj_apply, if_neg hi]
  have hlast : w (Fin.last k) = 2 * v (Fin.last k) := by
    simp only [hw, fiveScaleLast, fiveScaleCoordLast, LinearMap.pi_apply,
      LinearMap.smul_apply, LinearMap.proj_apply, ite_true, smul_eq_mul]
  rw [Finset.sum_congr rfl (fun i _ => by rw [hv i]), hlast]
  simp only [fiveForm, if_true, one_mul]
  rw [Finset.sum_congr rfl (fun i _ => by rw [sq])]
  have hsc : ∀ S z : ZMod 5, S + (2 * z) ^ 2 = S - z * z := by decide
  exact hsc _ _

lemma card_plus {k n : ℕ} (hn : k + 1 = 2 * n) :
    Fintype.card (Fin (k + 1) → ZMod 5) = Fintype.card (Fin n ⊕ Fin n → ZMod 5) := by
  simp only [Fintype.card_fun]
  congr 1
  simp only [Fintype.card_fin, Fintype.card_sum]
  omega

@[expose] noncomputable def fivePlusEquiv {k n : ℕ} (hn : k + 1 = 2 * n) :
    (Fin (k + 1) → ZMod 5) ≃ₗ[ZMod 5] (Fin n ⊕ Fin n → ZMod 5) :=
  LinearEquiv.ofBijective ((fivePlusLinear hn).comp (fiveScaleLast k)) <| by
    refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨?_, card_plus hn⟩
    intro u v huv
    have h0 : ((fivePlusLinear hn).comp (fiveScaleLast k)) (u - v) = 0 := by
      rw [map_sub, huv]; simp
    have h1 : fiveScaleLast k (u - v) = 0 :=
      fivePlusLinear_eq_zero hn (by simpa using h0)
    exact sub_eq_zero.mp (fiveScaleLast_eq_zero h1)

lemma two_pred_le {k n : ℕ} (hn : k + 1 = 2 * n) : 2 * (n - 1) ≤ k + 1 := by
  have h : 2 * (n - 1) ≤ 2 * n := Nat.mul_le_mul_left 2 (Nat.sub_le n 1)
  omega

lemma two_pred_lt {k n : ℕ} (hn : k + 1 = 2 * n) : 2 * (n - 1) < k + 1 := by
  have h : 2 * (n - 1) ≤ 2 * n := Nat.mul_le_mul_left 2 (Nat.sub_le n 1)
  omega

lemma two_pred_succ_lt {k n : ℕ} (hn : k + 1 = 2 * n) : 2 * (n - 1) + 1 < k + 1 := by
  have h : 2 * (n - 1) ≤ 2 * n := Nat.mul_le_mul_left 2 (Nat.sub_le n 1)
  have hn1 : 1 ≤ n := by omega
  omega

lemma sum_fin_pred_eq {k n : ℕ} (hn : k + 1 = 2 * n) (g : Fin (k + 1) → ZMod 5) :
    (∑ i : Fin k, g (Fin.castSucc i)) =
      (∑ i : Fin (2 * (n - 1)), g (Fin.castLE (two_pred_le hn) i)) +
        g (⟨2 * (n - 1), two_pred_lt hn⟩ : Fin (k + 1)) := by
  have hk : k = 2 * (n - 1) + 1 := by omega
  rw [(Equiv.sum_comp (finCongr hk).symm (fun i : Fin k => g (Fin.castSucc i))).symm]
  rw [Fin.sum_univ_castSucc]
  congr 1

def fiveMinusCoord {k n : ℕ} (hn : k + 1 = 2 * n)
    (i : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) :
    (Fin (k + 1) → ZMod 5) →ₗ[ZMod 5] ZMod 5 :=
  match i with
  | Sum.inl j =>
      LinearMap.proj (R := ZMod 5) (φ := fun _ => ZMod 5)
          (Fin.castLE (two_pred_le hn) (⟨j.1, by omega⟩ : Fin (2 * (n - 1)))) +
        (2 : ZMod 5) • LinearMap.proj (R := ZMod 5) (φ := fun _ => ZMod 5)
          (Fin.castLE (two_pred_le hn) (⟨j.1 + (n - 1), by omega⟩ : Fin (2 * (n - 1))))
  | Sum.inr (Sum.inl j) =>
      LinearMap.proj (R := ZMod 5) (φ := fun _ => ZMod 5)
          (Fin.castLE (two_pred_le hn) (⟨j.1, by omega⟩ : Fin (2 * (n - 1)))) +
        (-2 : ZMod 5) • LinearMap.proj (R := ZMod 5) (φ := fun _ => ZMod 5)
          (Fin.castLE (two_pred_le hn) (⟨j.1 + (n - 1), by omega⟩ : Fin (2 * (n - 1))))
  | Sum.inr (Sum.inr c) =>
      LinearMap.proj (R := ZMod 5) (φ := fun _ => ZMod 5)
        (⟨2 * (n - 1) + c.1, by omega⟩ : Fin (k + 1))

def fiveMinusLinear {k n : ℕ} (hn : k + 1 = 2 * n) :
    (Fin (k + 1) → ZMod 5) →ₗ[ZMod 5] (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → ZMod 5) :=
  LinearMap.pi (φ := fun _ => ZMod 5) (fiveMinusCoord hn)

lemma fiveMinusLinear_eq_zero {k n : ℕ} (hn : k + 1 = 2 * n) {w : Fin (k + 1) → ZMod 5}
    (hw : fiveMinusLinear hn w = 0) : w = 0 := by
  have hx : ∀ j : Fin (n - 1),
      w (Fin.castLE (two_pred_le hn) (⟨j.1, by omega⟩ : Fin (2 * (n - 1)))) +
        2 * w (Fin.castLE (two_pred_le hn)
          (⟨j.1 + (n - 1), by omega⟩ : Fin (2 * (n - 1)))) = 0 := by
    intro j
    have h := congr_fun hw (Sum.inl j)
    simpa [fiveMinusLinear, fiveMinusCoord, LinearMap.pi_apply, LinearMap.add_apply,
      LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul, Pi.zero_apply] using h
  have hy : ∀ j : Fin (n - 1),
      w (Fin.castLE (two_pred_le hn) (⟨j.1, by omega⟩ : Fin (2 * (n - 1)))) +
        (-2) * w (Fin.castLE (two_pred_le hn)
          (⟨j.1 + (n - 1), by omega⟩ : Fin (2 * (n - 1)))) = 0 := by
    intro j
    have h := congr_fun hw (Sum.inr (Sum.inl j))
    simpa [fiveMinusLinear, fiveMinusCoord, LinearMap.pi_apply, LinearMap.add_apply,
      LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul, Pi.zero_apply] using h
  have hu : w (⟨2 * (n - 1), two_pred_lt hn⟩ : Fin (k + 1)) = 0 := by
    have h := congr_fun hw (Sum.inr (Sum.inr 0))
    simpa [fiveMinusLinear, fiveMinusCoord, LinearMap.pi_apply, LinearMap.proj_apply,
      Pi.zero_apply] using h
  have hv : w (⟨2 * (n - 1) + 1, two_pred_succ_lt hn⟩ : Fin (k + 1)) = 0 := by
    have h := congr_fun hw (Sum.inr (Sum.inr 1))
    simpa [fiveMinusLinear, fiveMinusCoord, LinearMap.pi_apply, LinearMap.proj_apply,
      Pi.zero_apply] using h
  funext i
  rcases Nat.lt_or_ge (i : ℕ) (n - 1) with hlt | hge
  · have hi : i = Fin.castLE (two_pred_le hn) (⟨i.1, by omega⟩ : Fin (2 * (n - 1))) :=
      Fin.ext rfl
    rw [hi]
    exact (zmod5_pair_sq_zero' _ _ (hx ⟨i.1, hlt⟩) (hy ⟨i.1, hlt⟩)).1
  · rcases Nat.lt_or_ge (i : ℕ) (2 * (n - 1)) with hlt2 | hge2
    · let j : Fin (n - 1) := ⟨i.1 - (n - 1), by omega⟩
      have hi : i = Fin.castLE (two_pred_le hn)
          (⟨j.1 + (n - 1), by omega⟩ : Fin (2 * (n - 1))) := by
        ext; simp only [Fin.val_castLE]; simp [j]; omega
      rw [hi]
      exact (zmod5_pair_sq_zero' _ _ (hx j) (hy j)).2
    · rcases Nat.lt_or_ge (i : ℕ) (2 * (n - 1) + 1) with hlt3 | hge3
      · have hiv : i.val = 2 * (n - 1) := le_antisymm (Nat.lt_succ_iff.mp hlt3) hge2
        have hi : i = (⟨2 * (n - 1), two_pred_lt hn⟩ : Fin (k + 1)) := Fin.ext hiv
        rw [hi]; exact hu
      · have hiv : i.val = 2 * (n - 1) + 1 :=
          le_antisymm (Nat.lt_succ_iff.mp (by omega : i.val < 2 * (n - 1) + 2)) hge3
        have hi : i = (⟨2 * (n - 1) + 1, two_pred_succ_lt hn⟩ : Fin (k + 1)) := Fin.ext hiv
        rw [hi]; exact hv

lemma statedQuadMinus_fiveMinusMap {k n : ℕ} (hn : k + 1 = 2 * n)
    (v : Fin (k + 1) → ZMod 5) :
    (∑ j : Fin (n - 1), (fiveMinusLinear hn v) (Sum.inl j) *
        (fiveMinusLinear hn v) (Sum.inr (Sum.inl j))) +
      (fiveMinusLinear hn v) (Sum.inr (Sum.inr 0)) ^ 2 +
      (3 : ZMod 5) * (fiveMinusLinear hn v) (Sum.inr (Sum.inr 1)) ^ 2 =
      fiveForm k false v v := by
  have hpair : ∀ a b : ZMod 5, (a + 2 * b) * (a + (-2) * b) = a ^ 2 + b ^ 2 :=
    fun a b => zmod5_pair_sq' a b
  have hlastidx : (⟨2 * (n - 1) + 1, two_pred_succ_lt hn⟩ : Fin (k + 1)) = Fin.last k := by
    ext; simp only [Fin.val_last]; omega
  have hform : fiveForm k false v v =
      (∑ i : Fin (2 * (n - 1)), (v (Fin.castLE (two_pred_le hn) i)) ^ 2) +
        (v (⟨2 * (n - 1), two_pred_lt hn⟩ : Fin (k + 1))) ^ 2 -
          2 * (v (Fin.last k)) ^ 2 := by
    simp only [fiveForm, Bool.false_eq_true, if_false]
    rw [Finset.sum_congr rfl (fun i _ => by rw [← sq]),
      sum_fin_pred_eq hn (fun i => (v i) ^ 2), ← sq]
  simp only [fiveMinusLinear, fiveMinusCoord, LinearMap.pi_apply, LinearMap.add_apply,
    LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul, Fin.val_zero, Fin.val_one,
    Nat.add_zero]
  rw [Finset.sum_congr rfl (fun j _ => hpair _ _)]
  rw [← sum_pair_even (n - 1) (fun i : Fin (2 * (n - 1)) =>
    (v (Fin.castLE (two_pred_le hn) i)) ^ 2)]
  rw [hlastidx, hform]
  have hsc : ∀ A z : ZMod 5, A + 3 * z ^ 2 = A - 2 * z ^ 2 := by decide
  exact hsc _ _

lemma card_minus {k n : ℕ} (hn : k + 1 = 2 * n) :
    Fintype.card (Fin (k + 1) → ZMod 5) =
      Fintype.card (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → ZMod 5) := by
  simp only [Fintype.card_fun]
  congr 1
  simp only [Fintype.card_fin, Fintype.card_sum]
  omega

@[expose] noncomputable def fiveMinusEquiv {k n : ℕ} (hn : k + 1 = 2 * n) :
    (Fin (k + 1) → ZMod 5) ≃ₗ[ZMod 5] (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → ZMod 5) :=
  LinearEquiv.ofBijective (fiveMinusLinear hn) <| by
    refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨?_, card_minus hn⟩
    intro u v huv
    have h0 : fiveMinusLinear hn (u - v) = 0 := by rw [map_sub, huv]; simp
    exact sub_eq_zero.mp (fiveMinusLinear_eq_zero hn h0)

end CFSG.OddTranspositions.PartThree
