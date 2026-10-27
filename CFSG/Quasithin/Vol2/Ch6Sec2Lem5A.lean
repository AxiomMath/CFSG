module

public import CFSG.Quasithin.Vol2.Ch6SL2Fix
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.TotallySplit

public section

namespace CFSG.Quasithin.H13

variable {K : Type} [Field K]

theorem det2_add_left_ch625 (x x' y : Fin 2 → K) : det2 (x + x') y = det2 x y + det2 x' y := by
  simp only [det2, Pi.add_apply]; ring

theorem det2_add_right_ch625 (x y y' : Fin 2 → K) : det2 x (y + y') = det2 x y + det2 x y' := by
  simp only [det2, Pi.add_apply]; ring

theorem det2_smul_left_ch625 (c : K) (x y : Fin 2 → K) : det2 (c • x) y = c * det2 x y := by
  simp only [det2, Pi.smul_apply, smul_eq_mul]; ring

theorem det2_smul_right_ch625 (c : K) (x y : Fin 2 → K) : det2 x (c • y) = c * det2 x y := by
  simp only [det2, Pi.smul_apply, smul_eq_mul]; ring

theorem det2_self_ch625 (x : Fin 2 → K) : det2 x x = 0 := by
  simp only [det2]; ring

theorem det2_comm_ch625 (x y : Fin 2 → K) : det2 y x = - det2 x y := by
  simp only [det2]; ring

theorem eq_basis_ch625 (v : Fin 2 → K) : v = v 0 • ![1, 0] + v 1 • ![0, 1] := by
  funext i
  fin_cases i <;> simp

theorem det2_e_ch625 : det2 (![1, 0] : Fin 2 → K) ![0, 1] = 1 := by
  simp [det2]

theorem det2_semilinear {f : (Fin 2 → K) → (Fin 2 → K)} {σ : K →+* K}
    (hadd : ∀ v w, f (v + w) = f v + f w) (hsmul : ∀ (c : K) v, f (c • v) = σ c • f v)
    (x y : Fin 2 → K) :
    det2 (f x) (f y) = σ (det2 x y) * det2 (f ![1, 0]) (f ![0, 1]) := by
  have hf : ∀ v : Fin 2 → K, f v = σ (v 0) • f ![1, 0] + σ (v 1) • f ![0, 1] := by
    intro v
    conv_lhs => rw [eq_basis_ch625 v]
    rw [hadd, hsmul, hsmul]
  rw [hf x, hf y]
  simp only [det2_add_left_ch625, det2_add_right_ch625, det2_smul_left_ch625,
    det2_smul_right_ch625, det2_self_ch625]
  rw [det2_comm_ch625 (f ![1, 0]) (f ![0, 1])]
  simp only [det2, map_sub, map_mul]
  ring

section Four

variable [Finite K] (hK : Nat.card K = 4)
include hK

omit [Finite K] in
theorem two_eq_zero_ch625 : (2 : K) = 0 := by
  have h4 : ((Nat.card K : ℕ) : K) = 0 := by
    have := (card_nsmul_eq_zero' : Nat.card K • (1 : K) = 0)
    rwa [nsmul_eq_mul, mul_one] at this
  rw [hK] at h4
  have : (2 : K) * 2 = 0 := by
    have e : ((4 : ℕ) : K) = 2 * 2 := by norm_num
    rw [← e]
    exact h4
  exact mul_self_eq_zero.mp this

omit [Finite K] in
theorem add_self_ch625 (c : K) : c + c = 0 := by
  rw [← two_mul, two_eq_zero_ch625 hK, zero_mul]

omit [Finite K] in
theorem neg_eq_ch625 (c : K) : -c = c := by
  rw [neg_eq_iff_add_eq_zero, add_self_ch625 hK]

theorem pow_four_ch625 (c : K) : c ^ 4 = c := by
  have := Fintype.ofFinite K
  have hc : Fintype.card K = 4 := by rw [← Nat.card_eq_fintype_card, hK]
  have := FiniteField.pow_card c
  rwa [hc] at this

theorem pow_three_ch625 {c : K} (hc : c ≠ 0) : c ^ 3 = 1 := by
  have h := pow_four_ch625 hK c
  have e : c ^ 4 = c ^ 3 * c := pow_succ c 3
  rw [e] at h
  exact mul_right_cancel₀ hc (h.trans (one_mul c).symm)

theorem sq_add_self_ch625 (c : K) : c ^ 2 + c = 0 ∨ c ^ 2 + c = 1 := by
  have h2 := two_eq_zero_ch625 hK
  have h4 := pow_four_ch625 hK c
  have hs : (c ^ 2 + c) * (c ^ 2 + c - 1) = 0 := by
    linear_combination h4 + c ^ 3 * h2
  rcases mul_eq_zero.mp hs with h | h
  · exact Or.inl h
  · right
    linear_combination h

omit [Finite K] in
theorem eq_zero_or_one_ch625 {c : K} (h : c ^ 2 + c = 0) : c = 0 ∨ c = 1 := by
  have h2 := two_eq_zero_ch625 hK
  have hc : c * (c - 1) = 0 := by linear_combination h - c * h2
  rcases mul_eq_zero.mp hc with hc | hc
  · exact Or.inl hc
  · exact Or.inr (by linear_combination hc)

theorem ringAut_ch625 (σ : K ≃+* K) : (∀ c, σ c = c) ∨ (∀ c, σ c = c ^ 2) := by
  have h2 := two_eq_zero_ch625 hK
  have key : ∀ c : K, σ c = c ∨ (σ c = c + 1 ∧ c ^ 2 + c = 1) := by
    intro c
    have hs : σ (c ^ 2 + c) = c ^ 2 + c := by
      rcases sq_add_self_ch625 hK c with h | h <;> rw [h]
      · exact map_zero σ
      · exact map_one σ
    have hs' : σ c ^ 2 + σ c = c ^ 2 + c := by rw [← map_pow, ← map_add, hs]
    have h1 : (σ c - c) * (σ c + c + 1) = 0 := by
      linear_combination hs'
    rcases mul_eq_zero.mp h1 with h | h
    · exact Or.inl (by linear_combination h)
    · right
      have hσ : σ c = c + 1 := by linear_combination h - (c + 1) * h2
      refine ⟨hσ, ?_⟩
      rcases sq_add_self_ch625 hK c with h0 | h0
      · exfalso
        rcases eq_zero_or_one_ch625 hK h0 with hc | hc
        · rw [hc, map_zero, zero_add] at hσ
          exact zero_ne_one hσ
        · rw [hc, map_one] at hσ
          have : (1 : K) = 0 := by linear_combination -hσ
          exact one_ne_zero this
      · exact h0
  by_cases hid : ∀ c, σ c = c
  · exact Or.inl hid
  · right
    push Not at hid
    obtain ⟨c₀, hc₀⟩ := hid
    obtain ⟨hσ₀, hq₀⟩ := (key c₀).resolve_left hc₀
    intro c
    rcases key c with h | ⟨h, hq⟩
    · rcases sq_add_self_ch625 hK c with h0 | h0
      · rw [h]
        rcases eq_zero_or_one_ch625 hK h0 with hc | hc <;> rw [hc] <;> ring
      · exfalso
        have hp : (c - c₀) * (c + c₀ + 1) = 0 := by
          linear_combination h0 - hq₀
        rcases mul_eq_zero.mp hp with hp | hp
        · have hcc : c = c₀ := by linear_combination hp
          rw [hcc] at h
          exact hc₀ h
        · have hcc : c = c₀ + 1 := by linear_combination hp - (c₀ + 1) * h2
          rw [hcc, map_add, map_one, hσ₀] at h
          have : (1 : K) = 0 := by linear_combination h
          exact one_ne_zero this
    · rw [h]
      linear_combination -hq + c * h2

theorem sq_sq_ch625 (c : K) : (c ^ 2) ^ 2 = c := by
  rw [← pow_mul]
  exact pow_four_ch625 hK c

omit [Finite K] hK in
theorem eq_inv_of_mul_sq_eq_ch625 {c d : K} (hc : c ≠ 0) (h : d * c ^ 2 = c) : c = d⁻¹ := by
  have hd : d ≠ 0 := by
    rintro rfl
    rw [zero_mul] at h
    exact hc h.symm
  have h1 : d * c = 1 := by
    have e : d * c ^ 2 = (d * c) * c := by ring
    rw [e] at h
    exact mul_right_cancel₀ hc (h.trans (one_mul c).symm)
  exact eq_inv_of_mul_eq_one_right h1

theorem eq_of_three_ch625 {a b c e : K} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (he : e ≠ 0)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : e = a ∨ e = b ∨ e = c := by
  classical
  have := Fintype.ofFinite K
  have hcard : Fintype.card K = 4 := by rw [← Nat.card_eq_fintype_card, hK]
  by_contra hcon
  push Not at hcon
  obtain ⟨hea, heb, hec⟩ := hcon
  have hsub : ({0, a, b, c, e} : Finset K).card ≤ 4 := hcard ▸ Finset.card_le_univ _
  rw [Finset.card_insert_of_notMem (by simp [Ne.symm ha, Ne.symm hb, Ne.symm hc, Ne.symm he]),
    Finset.card_insert_of_notMem (by simp [hab, hac, Ne.symm hea]),
    Finset.card_insert_of_notMem (by simp [hbc, Ne.symm heb]),
    Finset.card_pair (Ne.symm hec)] at hsub
  omega

theorem card_eq_four_cases_ch625 (P : AddSubgroup (Fin 2 → K)) (hP : Nat.card P = 4) :
    (∃ v : Fin 2 → K, v ≠ 0 ∧ ∀ w, w ∈ P ↔ ∃ c : K, w = c • v) ∨
    (∃ x y : Fin 2 → K, det2 x y ≠ 0 ∧ ∀ w, w ∈ P ↔ (w = 0 ∨ w = x ∨ w = y ∨ w = x + y)) := by
  classical
  obtain ⟨x, hxP, hx0⟩ : ∃ x ∈ P, x ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have : P = ⊥ := (AddSubgroup.eq_bot_iff_forall P).mpr hcon
    rw [this, AddSubgroup.card_bot] at hP
    norm_num at hP
  by_cases hline : ∀ w ∈ P, ∃ c : K, w = c • x
  · left
    refine ⟨x, hx0, fun w => ⟨hline w, ?_⟩⟩
    set S := (Submodule.span K {x}).toAddSubgroup with hS
    have hPS : P ≤ S := fun w hw => by
      obtain ⟨c, rfl⟩ := hline w hw
      exact Submodule.smul_mem _ c (Submodule.subset_span rfl)
    have hS4 : Nat.card S = 4 := by
      rw [← hK]
      exact (Nat.card_congr (LinearEquiv.toSpanNonzeroSingleton K _ x hx0).toEquiv).symm
    have hPeq : P = S := AddSubgroup.eq_of_le_of_card_ge hPS (by rw [hS4, hP])
    rintro ⟨c, rfl⟩
    rw [hPeq]
    exact Submodule.smul_mem _ c (Submodule.subset_span rfl)
  · right
    push Not at hline
    obtain ⟨y, hyP, hy⟩ := hline
    have hdet : det2 x y ≠ 0 := fun h0 => by
      obtain ⟨c, hc⟩ := exists_eq_smul_of_det2_eq_zero hx0 h0
      exact hy c hc
    refine ⟨x, y, hdet, fun w => ⟨fun hw => ?_, ?_⟩⟩
    · by_contra hcon
      push Not at hcon
      obtain ⟨hw0, hwx, hwy, hwxy⟩ := hcon
      have hy0 : y ≠ 0 := fun h0 => hy 0 (by rw [h0, zero_smul])
      have hxy : x ≠ y := fun h0 => hy 1 (by rw [h0, one_smul])
      have hxy0 : x + y ≠ 0 := fun h0 => hy (-1) (by
        rw [neg_one_smul]
        exact (neg_eq_of_add_eq_zero_right h0).symm)
      have hxxy : x ≠ x + y := fun h0 => hy0 (by
        have := congrArg (· - x) h0
        simpa using this.symm)
      have hyxy : y ≠ x + y := fun h0 => hx0 (by
        have := congrArg (· - y) h0
        simpa using this.symm)
      have hsub : (↑({0, x, y, x + y, w} : Finset (Fin 2 → K)) : Set (Fin 2 → K)) ⊆
          (P : Set (Fin 2 → K)) := by
        intro z hz
        simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
          Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl | rfl | rfl | rfl
        · exact P.zero_mem
        · exact hxP
        · exact hyP
        · exact P.add_mem hxP hyP
        · exact hw
      have h5 : ({0, x, y, x + y, w} : Finset (Fin 2 → K)).card = 5 := by
        rw [Finset.card_insert_of_notMem (by simp [Ne.symm hx0, Ne.symm hy0, Ne.symm hxy0,
            Ne.symm hw0]),
          Finset.card_insert_of_notMem (by simp [hxy, hxxy, Ne.symm hwx]),
          Finset.card_insert_of_notMem (by simp [hyxy, Ne.symm hwy]),
          Finset.card_pair (Ne.symm hwxy)]
      have := Set.ncard_le_ncard hsub (Set.toFinite _)
      rw [Set.ncard_coe_finset, h5, ← Nat.card_coe_set_eq] at this
      have hc : Nat.card ↥(P : Set (Fin 2 → K)) = Nat.card P := rfl
      omega
    · rintro (rfl | rfl | rfl | rfl)
      · exact P.zero_mem
      · exact hxP
      · exact hyP
      · exact P.add_mem hxP hyP

@[expose] def planeAddSub (x y : Fin 2 → K) : AddSubgroup (Fin 2 → K) where
  carrier := {w | w = 0 ∨ w = x ∨ w = y ∨ w = x + y}
  zero_mem' := Or.inl rfl
  add_mem' := by
    have h2 : ∀ w : Fin 2 → K, w + w = 0 := fun w => by
      rw [← two_smul K w, two_eq_zero_ch625 hK, zero_smul]
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rcases ha with ha | ha | ha | ha <;> rw [ha]
    · rw [zero_add]; exact hb
    · rcases hb with hb | hb | hb | hb <;> rw [hb]
      · rw [add_zero]; exact Or.inr (Or.inl rfl)
      · exact Or.inl (h2 _)
      · exact Or.inr (Or.inr (Or.inr rfl))
      · exact Or.inr (Or.inr (Or.inl (by rw [← add_assoc, h2, zero_add])))
    · rcases hb with hb | hb | hb | hb <;> rw [hb]
      · rw [add_zero]; exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr (add_comm _ _)))
      · exact Or.inl (h2 _)
      · exact Or.inr (Or.inl (by rw [add_comm x, ← add_assoc, h2, zero_add]))
    · rcases hb with hb | hb | hb | hb <;> rw [hb]
      · rw [add_zero]; exact Or.inr (Or.inr (Or.inr rfl))
      · exact Or.inr (Or.inr (Or.inl (by rw [add_comm x y, add_assoc, h2, add_zero])))
      · exact Or.inr (Or.inl (by rw [add_assoc, h2, add_zero]))
      · exact Or.inl (h2 _)
  neg_mem' := by
    have hneg : ∀ w : Fin 2 → K, -w = w := fun w => by
      rw [neg_eq_iff_add_eq_zero, ← two_smul K w, two_eq_zero_ch625 hK, zero_smul]
    intro a ha
    simp only [Set.mem_ofPred_eq, hneg] at ha ⊢
    exact ha

omit [Finite K] in
theorem mem_planeAddSub {x y w : Fin 2 → K} :
    w ∈ planeAddSub hK x y ↔ (w = 0 ∨ w = x ∨ w = y ∨ w = x + y) := Iff.rfl

theorem exists_ne_zero_ne_one_ch625 : ∃ ω : K, ω ≠ 0 ∧ ω ≠ 1 := by
  classical
  by_contra hcon
  push Not at hcon
  have := Fintype.ofFinite K
  have hcard : Fintype.card K ≤ 2 := by
    calc Fintype.card K = (Finset.univ : Finset K).card := rfl
      _ ≤ ({0, 1} : Finset K).card := Finset.card_le_card fun c _ => by
          by_cases hc : c = 0
          · simp [hc]
          · simp [hcon c hc]
      _ ≤ 2 := Finset.card_le_two
  rw [← Nat.card_eq_fintype_card, hK] at hcard
  omega

omit [Finite K] in
theorem card_planeAddSub {x y : Fin 2 → K} (hxy : det2 x y ≠ 0) :
    Nat.card (planeAddSub hK x y) = 4 := by
  classical
  have hx0 : x ≠ 0 := by rintro rfl; apply hxy; simp [det2]
  have hy0 : y ≠ 0 := by rintro rfl; apply hxy; simp [det2]
  have hxy' : x ≠ y := by rintro rfl; exact hxy (det2_self_ch625 x)
  have hxy0 : x + y ≠ 0 := by
    intro h0
    apply hxy
    have : y = -x := (neg_eq_of_add_eq_zero_right h0).symm
    rw [this, ← neg_one_smul K x, det2_smul_right_ch625, det2_self_ch625, mul_zero]
  have hxxy : x ≠ x + y := fun h0 => hy0 (by
    have := congrArg (· - x) h0
    simpa using this.symm)
  have hyxy : y ≠ x + y := fun h0 => hx0 (by
    have := congrArg (· - y) h0
    simpa using this.symm)
  have hset : ((planeAddSub hK x y : AddSubgroup (Fin 2 → K)) : Set (Fin 2 → K)) =
      ↑({0, x, y, x + y} : Finset (Fin 2 → K)) := by
    ext w
    simp only [SetLike.mem_coe, mem_planeAddSub, Finset.coe_insert, Finset.coe_singleton,
      Set.mem_insert_iff, Set.mem_singleton_iff]
  have h4 : ({0, x, y, x + y} : Finset (Fin 2 → K)).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [Ne.symm hx0, Ne.symm hy0, Ne.symm hxy0]),
      Finset.card_insert_of_notMem (by simp [hxy', hxxy]), Finset.card_pair hyxy]
  calc Nat.card ↥(planeAddSub hK x y) =
        Nat.card ↥((planeAddSub hK x y : AddSubgroup (Fin 2 → K)) : Set (Fin 2 → K)) := rfl
    _ = Nat.card ↥((↑({0, x, y, x + y} : Finset (Fin 2 → K))) : Set (Fin 2 → K)) := by
        rw [hset]
    _ = 4 := by rw [Nat.card_coe_set_eq, Set.ncard_coe_finset, h4]

end Four

end CFSG.Quasithin.H13
