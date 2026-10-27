module

public import CFSG.Quasithin.EmptyFaithful.S143UE

public section

namespace CFSG.Quasithin

namespace S143

namespace InspW2

open SL23

@[expose] def sl3MinusOne : SL3 :=
  ⟨!![2, 0; 0, 2], by rw [Matrix.det_fin_two_of]; decide⟩

theorem sl3_center : ∀ m : SL3, (∀ n : SL3, m * n = n * m) → m = 1 ∨ m = sl3MinusOne := by
  decide

theorem sl3_minusOne_sq : sl3MinusOne * sl3MinusOne = 1 := by decide

theorem sl3_minusOne_ne : sl3MinusOne ≠ 1 := by decide

theorem sl3_minusOne_central : ∀ n : SL3, sl3MinusOne * n = n * sl3MinusOne := by decide

theorem sl3_normal_closure : ∀ n : SL3, n ≠ 1 → ∃ k : SL3, ∃ j : Fin 12,
    n ^ (j : ℕ) = sl3MinusOne ∨ (n * (k * n⁻¹ * k⁻¹)) ^ (j : ℕ) = sl3MinusOne := by decide

theorem zmod4_inv_unique : ∀ u v : Multiplicative (ZMod 4), u * u = 1 → v * v = 1 → u ≠ 1 →
    v ≠ 1 → u = v := by decide

theorem z4StarSL23_struct {P : Type*} [Group P] (hP : IsZ4StarSL23 P) :
    ∃ ι : P, ι * ι = 1 ∧ ι ≠ 1 ∧ (∀ g : P, g * ι = ι * g) ∧
      (∀ y : P, (∀ g : P, g * y = y * g) → y ^ 4 = 1 ∧ (y * y = 1 → y = 1 ∨ y = ι)) ∧
      (∀ N : Subgroup P, N.Normal → N ≠ ⊥ → ι ∈ N) := by
  classical
  obtain ⟨hcard, A, B, ⟨hAB, hsup⟩, hA4, hAcyc, ⟨e⟩⟩ := hP
  have hfin : Finite P := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hcom : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := fun a ha b hb =>
    (Subgroup.mem_centralizer_iff.mp (hAB ha) b hb).symm
  set ι : P := ((e.symm sl3MinusOne : ↥B) : P) with hι
  have hιB : ι ∈ B := (e.symm sl3MinusOne).2
  have hι2 : ι * ι = 1 := by
    have : e.symm sl3MinusOne * e.symm sl3MinusOne = 1 := by
      rw [← map_mul, sl3_minusOne_sq, map_one]
    exact congrArg Subtype.val this
  have hι1 : ι ≠ 1 := fun h => sl3_minusOne_ne (by
    have : e.symm sl3MinusOne = 1 := Subtype.ext h
    simpa using congrArg e this)
  have hBc : ∀ b ∈ B, (∀ s ∈ B, b * s = s * b) → b = 1 ∨ b = ι := by
    intro b hb hbc
    rcases sl3_center (e ⟨b, hb⟩) (fun n => by
      have h2 : (⟨b, hb⟩ : ↥B) * e.symm n = e.symm n * ⟨b, hb⟩ :=
        Subtype.ext (hbc (e.symm n) (e.symm n).2)
      simpa using congrArg e h2) with h | h
    · left
      have : (⟨b, hb⟩ : ↥B) = 1 := by simpa using congrArg e.symm h
      exact congrArg Subtype.val this
    · right
      have : (⟨b, hb⟩ : ↥B) = e.symm sl3MinusOne := by rw [← h]; simp
      exact congrArg Subtype.val this
  have hB24 : Nat.card ↥B = 24 := by rw [Nat.card_congr e.toEquiv]; exact card_sl3
  have hinf : Nat.card ↥(A ⊓ B) = 2 := by
    have h := card_sup_mul_card_inf_of_le_centralizer hAB
    rw [hsup, Subgroup.card_top, hcard, hA4, hB24] at h
    omega
  have hιA : ι ∈ A := by
    by_contra hnA
    have hbot : A ⊓ B = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      rcases hBc x hx.2 (fun s hs => hcom x hx.1 s hs) with h | h
      · exact h
      · exact absurd (h ▸ hx.1) hnA
    rw [hbot, Subgroup.card_bot] at hinf
    omega
  have hA4' : ∀ y ∈ A, y ^ 4 = 1 := by
    intro y hy
    have := pow_card_eq_one' (G := ↥A) (x := ⟨y, hy⟩)
    rw [hA4] at this
    exact congrArg Subtype.val this
  have hAinv : ∀ y ∈ A, y * y = 1 → y ≠ 1 → y = ι := by
    intro y hy hy2 hy1
    obtain ⟨φ⟩ : Nonempty (↥A ≃* Multiplicative (ZMod 4)) := by
      have := zmodCyclicMulEquiv hAcyc
      rw [hA4] at this
      exact ⟨this.symm⟩
    have := zmod4_inv_unique (φ ⟨y, hy⟩) (φ ⟨ι, hιA⟩)
      (by rw [← map_mul]; exact (map_eq_one_iff φ φ.injective).mpr (Subtype.ext hy2))
      (by rw [← map_mul]; exact (map_eq_one_iff φ φ.injective).mpr (Subtype.ext hι2))
      (fun h => hy1 (congrArg Subtype.val ((map_eq_one_iff φ φ.injective).mp h)))
      (fun h => hι1 (congrArg Subtype.val ((map_eq_one_iff φ φ.injective).mp h)))
    exact congrArg Subtype.val (φ.injective this)
  have hdecomp : ∀ y : P, ∃ a ∈ A, ∃ b ∈ B, y = a * b := fun y =>
    CFSG.Quasithin.mem_sup_of_commute hAB (hsup ▸ Subgroup.mem_top y)
  have hcentral : ∀ y : P, (∀ g : P, g * y = y * g) → y ∈ A := by
    intro y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := hdecomp y
    have hbc : ∀ s ∈ B, b * s = s * b := by
      intro s hs
      have h1 := hy s
      have h2 : a * (s * b) = a * (b * s) := by
        calc a * (s * b) = (a * s) * b := by rw [mul_assoc]
          _ = (s * a) * b := by rw [hcom a ha s hs]
          _ = s * (a * b) := by rw [mul_assoc]
          _ = (a * b) * s := h1
          _ = a * (b * s) := by rw [mul_assoc]
      exact (mul_left_cancel h2).symm
    refine A.mul_mem ha ?_
    rcases hBc b hb hbc with h | h
    · rw [h]; exact A.one_mem
    · rw [h]; exact hιA
  refine ⟨ι, hι2, hι1, fun g => ?_, fun y hy => ⟨hA4' y (hcentral y hy), fun hy2 => ?_⟩, ?_⟩
  · obtain ⟨a, ha, b, hb, rfl⟩ := hdecomp g
    have hb' : b * ι = ι * b := by
      have h := sl3_minusOne_central (e ⟨b, hb⟩)
      have : (⟨b, hb⟩ : ↥B) * e.symm sl3MinusOne = e.symm sl3MinusOne * ⟨b, hb⟩ := by
        apply e.injective
        simpa using h.symm
      exact congrArg Subtype.val this
    calc a * b * ι = a * (b * ι) := by rw [mul_assoc]
      _ = a * (ι * b) := by rw [hb']
      _ = (a * ι) * b := by rw [mul_assoc]
      _ = (ι * a) * b := by rw [hcom a ha ι hιB]
      _ = ι * (a * b) := by rw [mul_assoc]
  · by_cases hy1 : y = 1
    · exact Or.inl hy1
    · exact Or.inr (hAinv y (hcentral y hy) hy2 hy1)
  · intro N hN hN1
    obtain ⟨⟨n, hnN⟩, hn1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hN1
    obtain ⟨a, ha, b, hb, rfl⟩ := hdecomp n
    by_cases hbc : ∀ s ∈ B, b * s = s * b
    · have hbA : b ∈ A := by
        rcases hBc b hb hbc with h | h
        · rw [h]; exact A.one_mem
        · rw [h]; exact hιA
      have hnA : a * b ∈ A := A.mul_mem ha hbA
      by_cases hn2 : (a * b) * (a * b) = 1
      · have : a * b = ι := hAinv _ hnA hn2 (fun h => hn1 (Subtype.ext h))
        rw [← this]; exact hnN
      · have h4 : ((a * b) * (a * b)) * ((a * b) * (a * b)) = 1 := by
          rw [← hA4' _ hnA, show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
        have : (a * b) * (a * b) = ι := hAinv _ (A.mul_mem hnA hnA) h4 hn2
        rw [← this]; exact N.mul_mem hnN hnN
    · push Not at hbc
      obtain ⟨s, hs, hbs⟩ := hbc
      have hu : b * s * b⁻¹ ∈ B := B.mul_mem (B.mul_mem hb hs) (B.inv_mem hb)
      have hmB : b * s * b⁻¹ * s⁻¹ ∈ B := B.mul_mem hu (B.inv_mem hs)
      have hmN : b * s * b⁻¹ * s⁻¹ ∈ N := by
        have e1 : b * s * b⁻¹ * s⁻¹ = (a * b) * (s * (a * b)⁻¹ * s⁻¹) := by
          have hau : a * (b * s * b⁻¹) = (b * s * b⁻¹) * a := hcom a ha _ hu
          calc b * s * b⁻¹ * s⁻¹ = (a * (b * s * b⁻¹) * a⁻¹) * s⁻¹ := by
                rw [hau]; group
            _ = (a * b) * (s * (a * b)⁻¹ * s⁻¹) := by group
        rw [e1]
        exact N.mul_mem hnN (hN.conj_mem _ (N.inv_mem hnN) s)
      have hm1 : (⟨b * s * b⁻¹ * s⁻¹, hmB⟩ : ↥B) ≠ 1 := by
        intro h
        have h' : b * s * b⁻¹ * s⁻¹ = 1 := congrArg Subtype.val h
        exact hbs (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h'))
      set m : ↥B := ⟨b * s * b⁻¹ * s⁻¹, hmB⟩ with hmdef
      have hmN' : (m : P) ∈ N := hmN
      obtain ⟨k', j, hj⟩ :=
        sl3_normal_closure (e m) (fun h => hm1 (by simpa using congrArg e.symm h))
      have hkm : (((e.symm k' : ↥B) : P) * (m : P)⁻¹ * ((e.symm k' : ↥B) : P)⁻¹) ∈ N :=
        hN.conj_mem _ (N.inv_mem hmN') _
      rcases hj with hj | hj
      · have h1 : m ^ (j : ℕ) = e.symm sl3MinusOne := by
          apply e.injective
          rw [map_pow, MulEquiv.apply_symm_apply]
          exact hj
        have h2 : ((m ^ (j : ℕ) : ↥B) : P) = ι := congrArg Subtype.val h1
        rw [← h2, Subgroup.coe_pow]
        exact N.pow_mem hmN' _
      · have h1 : (m * (e.symm k' * m⁻¹ * (e.symm k')⁻¹)) ^ (j : ℕ) = e.symm sl3MinusOne := by
          apply e.injective
          simp only [map_pow, map_mul, map_inv, MulEquiv.apply_symm_apply]
          exact hj
        have h2 : (((m * (e.symm k' * m⁻¹ * (e.symm k')⁻¹)) ^ (j : ℕ) : ↥B) : P) = ι :=
          congrArg Subtype.val h1
        rw [← h2, Subgroup.coe_pow]
        have : (((m * (e.symm k' * m⁻¹ * (e.symm k')⁻¹) : ↥B)) : P) ∈ N := by
          simpa using N.mul_mem hmN' hkm
        exact N.pow_mem this _

theorem z4StarSL23_normal_contains {P : Type*} [Group P] (hP : IsZ4StarSL23 P) {z : P}
    (hz2 : z * z = 1) (hz1 : z ≠ 1) (hzc : ∀ g : P, g * z = z * g) {N : Subgroup P}
    (hN : N.Normal) (hN1 : N ≠ ⊥) : z ∈ N := by
  obtain ⟨ι, -, -, -, hy, hnorm⟩ := z4StarSL23_struct hP
  rcases (hy z hzc).2 hz2 with h | h
  · exact absurd h hz1
  · rw [h]; exact hnorm N hN hN1

theorem z4StarSL23_central_pow_four {P : Type*} [Group P] (hP : IsZ4StarSL23 P) {y : P}
    (hy : ∀ g : P, g * y = y * g) : y ^ 4 = 1 := by
  obtain ⟨ι, -, -, -, hc, -⟩ := z4StarSL23_struct hP
  exact (hc y hy).1

end InspW2

end S143

end CFSG.Quasithin
