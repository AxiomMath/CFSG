module

public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Pi
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.RankThree.PartOne.KF1514B

variable {K : Type*} [Field K]

@[expose] def det2 (u v : Fin 2 → K) : K := u 0 * v 1 - u 1 * v 0

@[expose] def Orth {m : ℕ} (L : Fin m → Fin 2 → K) : Prop :=
  ∀ i j, det2 (L i) (L j) = 0

theorem det2_self (u : Fin 2 → K) : det2 u u = 0 := by
  simp only [det2]; ring

theorem det2_comm (u v : Fin 2 → K) : det2 v u = -det2 u v := by
  simp only [det2]; ring

theorem det2_smul_left (l : K) (u v : Fin 2 → K) : det2 (l • u) v = l * det2 u v := by
  simp only [det2, Pi.smul_apply, smul_eq_mul]; ring

theorem det2_smul_right (l : K) (u v : Fin 2 → K) : det2 u (l • v) = l * det2 u v := by
  simp only [det2, Pi.smul_apply, smul_eq_mul]; ring

theorem exists_smul_of_det2 {v w : Fin 2 → K} (hv : v ≠ 0) (h : det2 v w = 0) :
    ∃ l : K, w = l • v := by
  simp only [det2] at h
  by_cases h0 : v 0 = 0
  · have h1 : v 1 ≠ 0 := fun h1 => hv (funext fun i => by fin_cases i <;> simp [h0, h1])
    refine ⟨w 1 / v 1, funext fun i => ?_⟩
    fin_cases i
    · simp only [Fin.zero_eta, Pi.smul_apply, smul_eq_mul, h0, mul_zero]
      rw [h0, zero_mul, zero_sub, neg_eq_zero] at h
      exact (mul_eq_zero.1 h).resolve_left h1
    · simp only [Fin.mk_one, Pi.smul_apply, smul_eq_mul]
      field_simp
  · refine ⟨w 0 / v 0, funext fun i => ?_⟩
    fin_cases i
    · simp only [Fin.zero_eta, Pi.smul_apply, smul_eq_mul]
      field_simp
    · simp only [Fin.mk_one, Pi.smul_apply, smul_eq_mul]
      field_simp
      linear_combination h

theorem det2_trans {u v w : Fin 2 → K} (hv : v ≠ 0) (h1 : det2 u v = 0) (h2 : det2 v w = 0) :
    det2 u w = 0 := by
  simp only [det2] at h1 h2 ⊢
  have e0 : v 0 * (u 0 * w 1 - u 1 * w 0) = 0 := by
    linear_combination u 0 * h2 + w 0 * h1
  have e1 : v 1 * (u 0 * w 1 - u 1 * w 0) = 0 := by
    linear_combination w 1 * h1 + u 1 * h2
  by_cases h0 : v 0 = 0
  · have h1' : v 1 ≠ 0 := fun h1' => hv (funext fun i => by fin_cases i <;> simp [h0, h1'])
    exact (mul_eq_zero.1 e1).resolve_left h1'
  · exact (mul_eq_zero.1 e0).resolve_left h0

theorem rankOne_of_orth {m : ℕ} {L : Fin m → Fin 2 → K} (hL : Orth L) :
    ∃ (w : Fin 2 → K) (a : Fin m → K), ∀ i, L i = a i • w := by
  by_cases hz : ∀ i, L i = 0
  · exact ⟨0, 0, fun i => by simp [hz i]⟩
  · push Not at hz
    obtain ⟨i₀, hi₀⟩ := hz
    have hch : ∀ j, ∃ l : K, L j = l • L i₀ := fun j => exists_smul_of_det2 hi₀ (hL i₀ j)
    choose a ha using hch
    exact ⟨L i₀, a, ha⟩

theorem cross_of_orth_add {m : ℕ} {L L' : Fin m → Fin 2 → K} (hsum : Orth (L + L'))
    {w w' : Fin 2 → K} {a a' : Fin m → K} (hd : ∀ i, L i = a i • w) (hd' : ∀ i, L' i = a' i • w') :
    det2 w w' = 0 ∨ ∀ i j, a i * a' j = a' i * a j := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hdet, i, j, hij⟩ := hcon
  have h0 := hsum i j
  have hi : (L + L') i = a i • w + a' i • w' := by rw [Pi.add_apply, hd i, hd' i]
  have hj : (L + L') j = a j • w + a' j • w' := by rw [Pi.add_apply, hd j, hd' j]
  rw [hi, hj] at h0
  have : (a i * a' j - a' i * a j) * det2 w w' = 0 := by
    simp only [det2, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h0 ⊢
    linear_combination h0
  rcases mul_eq_zero.1 this with h1 | h1
  · exact hij (by linear_combination h1)
  · exact hdet h1

theorem rowsParallel_smul {m : ℕ} {a a₀ : Fin m → K} (ha₀ : a₀ ≠ 0)
    (h : ∀ i j, a i * a₀ j = a₀ i * a j) : ∃ μ : K, ∀ i, a i = μ * a₀ i := by
  obtain ⟨j₀, hj₀⟩ : ∃ j, a₀ j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact ha₀ (funext hcon)
  refine ⟨a j₀ / a₀ j₀, fun i => ?_⟩
  have := h i j₀
  field_simp
  linear_combination this

theorem rowsParallel_trans {m : ℕ} {a a₁ a₀ : Fin m → K} (ha₁ : a₁ ≠ 0)
    (h1 : ∀ i j, a i * a₁ j = a₁ i * a j) (h2 : ∀ i j, a₁ i * a₀ j = a₀ i * a₁ j) :
    ∀ i j, a i * a₀ j = a₀ i * a j := by
  intro i j
  obtain ⟨k, hk⟩ : ∃ k, a₁ k ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact ha₁ (funext hcon)
  have h3 : a₁ k * (a i * a₀ j - a₀ i * a j) = 0 := by
    have e1 := h1 i k
    have e2 := h1 j k
    have e3 := h2 i j
    linear_combination a₀ j * e1 - a₀ i * e2 + a k * e3
  have h4 := (mul_eq_zero.1 h3).resolve_left hk
  linear_combination h4

theorem rankOne_family {m : ℕ} (𝓛 : AddSubgroup (Fin m → Fin 2 → K))
    (h : ∀ L ∈ 𝓛, Orth L) :
    (∃ w : Fin 2 → K, w ≠ 0 ∧ ∀ L ∈ 𝓛, ∃ a : Fin m → K, ∀ i, L i = a i • w) ∨
    (∃ a₀ : Fin m → K, ∀ L ∈ 𝓛, ∃ w : Fin 2 → K, ∀ i, L i = a₀ i • w) := by
  classical
  by_cases hbot : ∀ L ∈ 𝓛, L = 0
  · left
    refine ⟨Pi.single 0 1, ?_, fun L hL => ⟨0, fun i => ?_⟩⟩
    · intro h0
      have := congrFun h0 0
      simp at this
    · rw [hbot L hL]; simp
  · push Not at hbot
    obtain ⟨L₀, hL₀, hL₀ne⟩ := hbot
    obtain ⟨w₀, a₀, hdec₀⟩ := rankOne_of_orth (h L₀ hL₀)
    have hw₀ : w₀ ≠ 0 := fun hw => hL₀ne (funext fun i => by simp [hdec₀ i, hw])
    have ha₀ : a₀ ≠ 0 := fun ha => hL₀ne (funext fun i => by simp [hdec₀ i, ha])
    have cross : ∀ L ∈ 𝓛, ∀ (w : Fin 2 → K) (a : Fin m → K), (∀ i, L i = a i • w) →
        det2 w w₀ = 0 ∨ ∀ i j, a i * a₀ j = a₀ i * a j := fun L hL w a hd =>
      cross_of_orth_add (h (L + L₀) (𝓛.add_mem hL hL₀)) hd hdec₀
    by_cases hbad : ∃ L₁ ∈ 𝓛, ∃ (w₁ : Fin 2 → K) (a₁ : Fin m → K),
        (∀ i, L₁ i = a₁ i • w₁) ∧ a₁ ≠ 0 ∧ det2 w₁ w₀ ≠ 0
    ·
      right
      refine ⟨a₀, fun L hL => ?_⟩
      obtain ⟨L₁, hL₁, w₁, a₁, hd₁, ha₁, hdet₁⟩ := hbad
      have hrow₁ : ∀ i j, a₁ i * a₀ j = a₀ i * a₁ j :=
        (cross L₁ hL₁ w₁ a₁ hd₁).resolve_left hdet₁
      have hw₁ : w₁ ≠ 0 := fun hw => hdet₁ (by rw [hw]; simp [det2])
      obtain ⟨w, a, hd⟩ := rankOne_of_orth (h L hL)
      by_cases hz : w = 0 ∨ a = 0
      · refine ⟨0, fun i => ?_⟩
        rcases hz with hz | hz <;> simp [hd i, hz]
      · push Not at hz
        obtain ⟨hw, ha⟩ := hz
        have hrow : ∀ i j, a i * a₀ j = a₀ i * a j := by
          by_contra hcon
          have h0 : det2 w w₀ = 0 := (cross L hL w a hd).resolve_right hcon
          have h1 : det2 w w₁ = 0 ∨ ∀ i j, a i * a₁ j = a₁ i * a j :=
            cross_of_orth_add (h (L + L₁) (𝓛.add_mem hL hL₁)) hd hd₁
          rcases h1 with h1 | h1
          · apply hdet₁
            have h2 : det2 w₁ w = 0 := by rw [det2_comm, h1, neg_zero]
            exact det2_trans hw h2 h0
          · exact hcon (rowsParallel_trans ha₁ h1 hrow₁)
        obtain ⟨μ, hμ⟩ := rowsParallel_smul ha₀ hrow
        refine ⟨μ • w, fun i => ?_⟩
        rw [hd i, hμ i, smul_smul, mul_comm]
    · push Not at hbad
      left
      refine ⟨w₀, hw₀, fun L hL => ?_⟩
      obtain ⟨w, a, hd⟩ := rankOne_of_orth (h L hL)
      by_cases hz : w = 0 ∨ a = 0
      · refine ⟨0, fun i => ?_⟩
        rcases hz with hz | hz <;> simp [hd i, hz]
      · push Not at hz
        obtain ⟨hw, ha⟩ := hz
        have hdet : det2 w w₀ = 0 := hbad L hL w a hd ha
        obtain ⟨l, hl⟩ := exists_smul_of_det2 hw₀ (by rw [det2_comm, hdet, neg_zero] : det2 w₀ w = 0)
        exact ⟨fun i => a i * l, fun i => by rw [hd i, hl, smul_smul]⟩

section Counting

variable [Finite K]

theorem card_fin_fun (n : ℕ) : Nat.card (Fin n → K) = Nat.card K ^ n := by
  rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin]

theorem card_prod_self : Nat.card (K × K) = Nat.card K ^ 2 := by
  rw [Nat.card_prod]; ring

theorem card_le_sq_of_row {m : ℕ} (𝓛 : AddSubgroup (Fin m → Fin 2 → K)) (a₀ : Fin m → K)
    (h : ∀ L ∈ 𝓛, ∃ w : Fin 2 → K, ∀ i, L i = a₀ i • w) : Nat.card 𝓛 ≤ Nat.card K ^ 2 := by
  classical
  have hq : Nat.card (Fin 2 → K) = Nat.card K ^ 2 := card_fin_fun 2
  by_cases ha₀ : a₀ = 0
  · have hz : ∀ L ∈ 𝓛, L = 0 := fun L hL => by
      obtain ⟨w, hw⟩ := h L hL
      funext i
      simp [hw i, ha₀]
    have hsub : Subsingleton 𝓛 := ⟨fun x y => Subtype.ext (by rw [hz x x.2, hz y y.2])⟩
    have hinj : Function.Injective (fun _ : 𝓛 => (0 : Fin 2 → K)) :=
      Function.injective_of_subsingleton _
    calc Nat.card 𝓛 ≤ Nat.card (Fin 2 → K) := Nat.card_le_card_of_injective _ hinj
      _ = Nat.card K ^ 2 := hq
  · obtain ⟨j₀, hj₀⟩ : ∃ j, a₀ j ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact ha₀ (funext hcon)
    have hinj : Function.Injective (fun L : 𝓛 => (a₀ j₀)⁻¹ • ((L : Fin m → Fin 2 → K) j₀)) := by
      intro L L' hLL'
      apply Subtype.ext
      obtain ⟨w, hw⟩ := h L L.2
      obtain ⟨w', hw'⟩ := h L' L'.2
      have e1 : (a₀ j₀)⁻¹ • ((L : Fin m → Fin 2 → K) j₀) = w := by
        rw [hw j₀, smul_smul, inv_mul_cancel₀ hj₀, one_smul]
      have e2 : (a₀ j₀)⁻¹ • ((L' : Fin m → Fin 2 → K) j₀) = w' := by
        rw [hw' j₀, smul_smul, inv_mul_cancel₀ hj₀, one_smul]
      have hww : w = w' := by rw [← e1, ← e2]; exact hLL'
      funext i
      rw [hw i, hw' i, hww]
    calc Nat.card 𝓛 ≤ Nat.card (Fin 2 → K) := Nat.card_le_card_of_injective _ hinj
      _ = Nat.card K ^ 2 := hq

@[expose] def coef {m : ℕ} (w : Fin 2 → K) (k : Fin 2) (L : Fin m → Fin 2 → K) (i : Fin m) : K :=
  (w k)⁻¹ * L i k

theorem coef_spec {m : ℕ} {w : Fin 2 → K} {k : Fin 2} (hk : w k ≠ 0) {L : Fin m → Fin 2 → K}
    {a : Fin m → K} (h : ∀ i, L i = a i • w) (i : Fin m) : coef w k L i = a i := by
  simp only [coef, h i, Pi.smul_apply, smul_eq_mul]
  field_simp

theorem eq_of_coef_eq {m : ℕ} {w : Fin 2 → K} {k : Fin 2} (hk : w k ≠ 0)
    {L L' : Fin m → Fin 2 → K} {a a' : Fin m → K} (h : ∀ i, L i = a i • w)
    (h' : ∀ i, L' i = a' i • w) (hc : coef w k L = coef w k L') : L = L' := by
  funext i
  have e := congrFun hc i
  rw [coef_spec hk h, coef_spec hk h'] at e
  rw [h i, h' i, e]

theorem exists_ne_zero_coord {w : Fin 2 → K} (hw : w ≠ 0) : ∃ k : Fin 2, w k ≠ 0 := by
  by_contra hcon
  push Not at hcon
  exact hw (funext hcon)

theorem card_le_sq_of_third_zero (𝓛 : AddSubgroup (Fin 3 → Fin 2 → K)) (h : ∀ L ∈ 𝓛, Orth L)
    (hz : ∀ L ∈ 𝓛, L 2 = 0) : Nat.card 𝓛 ≤ Nat.card K ^ 2 := by
  classical
  rcases rankOne_family 𝓛 h with ⟨w, hw, hA⟩ | ⟨a₀, hB⟩
  · obtain ⟨k, hk⟩ := exists_ne_zero_coord hw
    have hinj : Function.Injective
        (fun L : 𝓛 => (coef w k (L : Fin 3 → Fin 2 → K) 0, coef w k (L : Fin 3 → Fin 2 → K) 1)) := by
      intro L L' hLL'
      apply Subtype.ext
      obtain ⟨a, ha⟩ := hA L L.2
      obtain ⟨a', ha'⟩ := hA L' L'.2
      have e0 : coef w k (L : Fin 3 → Fin 2 → K) 0 = coef w k (L' : Fin 3 → Fin 2 → K) 0 :=
        congrArg Prod.fst hLL'
      have e1 : coef w k (L : Fin 3 → Fin 2 → K) 1 = coef w k (L' : Fin 3 → Fin 2 → K) 1 :=
        congrArg Prod.snd hLL'
      have e2 : coef w k (L : Fin 3 → Fin 2 → K) 2 = coef w k (L' : Fin 3 → Fin 2 → K) 2 := by
        simp only [coef, hz L L.2, hz L' L'.2, Pi.zero_apply, mul_zero]
      refine eq_of_coef_eq hk ha ha' (funext fun i => ?_)
      fin_cases i
      · exact e0
      · exact e1
      · exact e2
    calc Nat.card 𝓛 ≤ Nat.card (K × K) := Nat.card_le_card_of_injective _ hinj
      _ = Nat.card K ^ 2 := card_prod_self
  · exact card_le_sq_of_row 𝓛 a₀ hB

end Counting

end CFSG.RankThree.PartOne.KF1514B
