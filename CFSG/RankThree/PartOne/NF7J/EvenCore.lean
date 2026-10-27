module

public import CFSG.RankThree.PartOne.NF7J.EvenTab
public import CFSG.RankThree.PartOne.NF7J.EvenCount

public section

namespace CFSG.RankThree.PartOne.NF7J

section Core

variable {M : Type*} [Group M]

structure EvenHyp (Φ : M32 → Subgroup M) (y : ℕ → M) : Prop where
  conj : ∀ h : M32, det3 h = 1 → ∃ σ : MulAut M, ∀ g g₁ : M32, det3 g = 1 → h * g = g₁ * h →
    Φ g₁ = (Φ g).map σ.toMonoidHom
  y3 : ∀ i < 4, y i ^ 3 = 1
  y1 : ∀ i < 4, y i ≠ 1
  ycomm : ∀ i < 4, ∀ j < 4, y i * y j = y j * y i
  ydist : ∀ i < 4, ∀ j < 4, i ≠ j → y i ∉ Subgroup.zpowers (y j)
  yclos : ∀ i < 4, ∀ j < 4, ∀ k < 4, i ≠ j → i ≠ k → j ≠ k →
    y i ∈ Subgroup.zpowers (y j) ⊔ Subgroup.zpowers (y k)
  base : ∀ i < 4, Φ (mk32 (baseNode i)) = Subgroup.zpowers (y i)


variable {Φ : M32 → Subgroup M} {y : ℕ → M} (H : EvenHyp Φ y)

include H in
theorem EvenHyp.mate_data {e : ℕ × ℕ × ℕ × ℕ × ℕ} (he : chkMateE e = true) :
    ∃ σ : MulAut M, Φ (mk32 e.1) = (Subgroup.zpowers (y e.2.2.2.1)).map σ.toMonoidHom ∧
      Φ (mk32 e.2.1) = (Subgroup.zpowers (y e.2.2.2.2)).map σ.toMonoidHom ∧ e.2.2.2.1 < 4 ∧
        e.2.2.2.2 < 4 ∧ e.2.2.2.1 ≠ e.2.2.2.2 := by
  simp only [chkMateE, Bool.and_eq_true, decide_eq_true_eq] at he
  obtain ⟨⟨⟨⟨⟨hh, hi⟩, hj⟩, hij⟩, h1⟩, h2⟩ := he
  obtain ⟨σ, hσ⟩ := H.conj _ hh
  refine ⟨σ, ?_, ?_, hi, hj, hij⟩
  · rw [hσ _ _ (det3_base _ hi) h1, H.base _ hi]
  · rw [hσ _ _ (det3_base _ hj) h2, H.base _ hj]

include H in
theorem EvenHyp.mate_ne {e : ℕ × ℕ × ℕ × ℕ × ℕ} (he : chkMateE e = true) :
    Φ (mk32 e.1) ≠ Φ (mk32 e.2.1) := by
  obtain ⟨σ, h1, h2, hi, hj, hij⟩ := H.mate_data he
  intro h
  rw [h1, h2] at h
  have h3 := Subgroup.map_injective σ.injective h
  apply H.ydist _ hi _ hj hij
  rw [← h3]
  exact Subgroup.mem_zpowers _

include H in
theorem EvenHyp.node_data {e : ℕ × ℕ} (he : chkNodeE e = true) :
    ∃ s : M, s ^ 3 = 1 ∧ s ≠ 1 ∧ Φ (mk32 e.1) = Subgroup.zpowers s := by
  simp only [chkNodeE, Bool.and_eq_true, decide_eq_true_eq] at he
  obtain ⟨hh, h1⟩ := he
  obtain ⟨σ, hσ⟩ := H.conj _ hh
  have h0 : (0 : ℕ) < 4 := by decide
  have hb : mk32 (baseNode 0) = mk32 84 := rfl
  refine ⟨σ (y 0), ?_, ?_, ?_⟩
  · rw [← map_pow, H.y3 0 h0, map_one]
  · intro h
    exact H.y1 0 h0 (σ.injective (by rw [h, map_one]))
  · have := hσ (mk32 84) _ (det3_base 0 h0) h1
    rw [this, ← hb, H.base 0 h0, MonoidHom.map_zpowers]
    rfl

include H in
theorem EvenHyp.ord3_ne : Φ (mk32 84) ≠ Φ (mk32 161) := by
  obtain ⟨hg, hc1, hc2, hmate⟩ := trick_ok
  obtain ⟨e, he, hee⟩ := List.any_eq_true.1 hmate
  simp only [Bool.and_eq_true, beq_iff_eq] at hee
  obtain ⟨⟨he1, he2⟩, hchk⟩ := hee
  have hne := H.mate_ne hchk
  rw [he1, he2] at hne
  obtain ⟨τ, hτ⟩ := H.conj _ hg
  have a1 := hτ (mk32 84) (mk32 84) det3_84_161.1 hc1
  have a2 := hτ (mk32 161) (mk32 279) det3_84_161.2 hc2
  intro heq
  apply hne
  rw [a2, ← heq, ← a1]

include H in
theorem EvenHyp.pair_ne : ∀ t ∈ invCodes, ∀ t' ∈ invCodes, t ≠ t' →
    Φ (mk32 t) ≠ Φ (mk32 t') := by
  intro t ht t' ht' htt'
  have hc := List.all_eq_true.1 pair_cover t ht
  have hc' := List.all_eq_true.1 hc t' ht'
  simp only [Bool.or_eq_true, beq_iff_eq] at hc'
  rcases hc' with (h | hm) | ho
  · exact absurd h htt'
  · obtain ⟨e, he, hee⟩ := List.any_eq_true.1 hm
    simp only [Bool.and_eq_true, beq_iff_eq] at hee
    obtain ⟨⟨he1, he2⟩, hchk⟩ := hee
    have := H.mate_ne hchk
    rwa [he1, he2] at this
  · obtain ⟨e, he, hee⟩ := List.any_eq_true.1 ho
    simp only [Bool.and_eq_true, beq_iff_eq] at hee
    obtain ⟨⟨he1, he2⟩, hchk⟩ := hee
    simp only [chkOrd3E, Bool.and_eq_true, decide_eq_true_eq] at hchk
    obtain ⟨⟨hh, h1⟩, h2⟩ := hchk
    obtain ⟨σ, hσ⟩ := H.conj _ hh
    have a1 := hσ (mk32 84) _ det3_84_161.1 h1
    have a2 := hσ (mk32 161) _ det3_84_161.2 h2
    intro heq
    rw [he1] at a1
    rw [he2] at a2
    rw [a1, a2] at heq
    exact H.ord3_ne (Subgroup.map_injective σ.injective heq)

include H in
theorem EvenHyp.mate_comm {e : ℕ × ℕ × ℕ × ℕ × ℕ} (he : chkMateE e = true) {u v : M}
    (hu : u ∈ Φ (mk32 e.1)) (hv : v ∈ Φ (mk32 e.2.1)) : u * v = v * u := by
  obtain ⟨σ, h1, h2, hi, hj, -⟩ := H.mate_data he
  rw [h1] at hu
  rw [h2] at hv
  obtain ⟨a, ha, rfl⟩ := hu
  obtain ⟨b, hb, rfl⟩ := hv
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
  obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
  have hc : Commute (y e.2.2.2.1) (y e.2.2.2.2) := H.ycomm _ hi _ hj
  show σ ((y e.2.2.2.1) ^ k) * σ ((y e.2.2.2.2) ^ l) = σ ((y e.2.2.2.2) ^ l) * σ ((y e.2.2.2.1) ^ k)
  rw [← map_mul, ← map_mul, (hc.zpow_zpow k l).eq]

include H in
theorem EvenHyp.step_le {Q : Subgroup M} {S : List ℕ} {e : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ}
    (he : stepOK S e = true) (hS : ∀ t ∈ S, Φ (mk32 t) ≤ Q) : Φ (mk32 e.1) ≤ Q := by
  simp only [stepOK, Bool.and_eq_true, decide_eq_true_eq] at he
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hh, hi⟩, hj⟩, hk⟩, hij⟩, hki⟩, hkj⟩, ha⟩, hb⟩, h1⟩, h2⟩, h3⟩ := he
  obtain ⟨σ, hσ⟩ := H.conj _ hh
  have ea := hσ _ _ (det3_base _ hi) h1
  have eb := hσ _ _ (det3_base _ hj) h2
  have et := hσ _ _ (det3_base _ hk) h3
  rw [H.base _ hi] at ea
  rw [H.base _ hj] at eb
  rw [H.base _ hk] at et
  have hclos := H.yclos _ hk _ hi _ hj hki hkj hij
  rw [et]
  calc (Subgroup.zpowers (y e.2.2.2.2.1)).map σ.toMonoidHom
      ≤ (Subgroup.zpowers (y e.2.2.1) ⊔ Subgroup.zpowers (y e.2.2.2.1)).map σ.toMonoidHom :=
        Subgroup.map_mono (Subgroup.zpowers_le.2 hclos)
    _ = (Subgroup.zpowers (y e.2.2.1)).map σ.toMonoidHom ⊔
          (Subgroup.zpowers (y e.2.2.2.1)).map σ.toMonoidHom := Subgroup.map_sup _ _ _
    _ = Φ (mk32 e.2.2.2.2.2.1) ⊔ Φ (mk32 e.2.2.2.2.2.2) := by rw [ea, eb]
    _ ≤ Q := sup_le (hS _ ha) (hS _ hb)

include H in
theorem EvenHyp.steps_le {Q : Subgroup M} (es : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ)) :
    ∀ (S : List ℕ), stepsCheck S es = true → (∀ t ∈ S, Φ (mk32 t) ≤ Q) →
      ∀ t ∈ stepsOut S es, Φ (mk32 t) ≤ Q := by
  induction es with
  | nil =>
    intro S _ hS
    simpa [stepsOut] using hS
  | cons e es ih =>
    intro S hc hS
    simp only [stepsCheck, Bool.and_eq_true] at hc
    obtain ⟨he, hes⟩ := hc
    have hS' : ∀ t ∈ e.1 :: S, Φ (mk32 t) ≤ Q := by
      intro t ht
      rcases List.mem_cons.1 ht with rfl | ht
      · exact H.step_le he hS
      · exact hS t ht
    exact ih (e.1 :: S) hes hS'

theorem zpowers_eq_of_mem [Finite M] {s t : M} (hs : s ^ 3 = 1) (hs1 : s ≠ 1) (ht : t ^ 3 = 1) (ht1 : t ≠ 1)
    (h : t ∈ Subgroup.zpowers s) : Subgroup.zpowers t = Subgroup.zpowers s := by
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hos : orderOf s = 3 := orderOf_eq_prime hs hs1
  have hot : orderOf t = 3 := orderOf_eq_prime ht ht1
  apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 h)
  rw [Nat.card_zpowers, Nat.card_zpowers, hos, hot]

theorem invCodes_code : ∀ i j : Fin 21, invCodes.getD i 0 = invCodes.getD j 0 → i = j := by decide

theorem invCodes_mem : ∀ i : Fin 21, invCodes.getD i 0 ∈ invCodes := by decide

include H in
theorem even_core [Finite M] : False := by
  classical
  have hgen : ∀ t ∈ invCodes, ∃ s : M, s ^ 3 = 1 ∧ s ≠ 1 ∧ Φ (mk32 t) = Subgroup.zpowers s := by
    intro t ht
    have hc := List.all_eq_true.1 node_cover t ht
    obtain ⟨e, he, hee⟩ := List.any_eq_true.1 hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hee
    obtain ⟨he1, hchk⟩ := hee
    have := H.node_data hchk
    rw [he1] at this
    exact this
  choose! gen hg3 hg1 hgΦ using hgen
  have h84 : (84 : ℕ) ∈ invCodes := by decide
  have h124 : (124 : ℕ) ∈ invCodes := by decide
  have h167 : (167 : ℕ) ∈ invCodes := by decide
  set Q : Subgroup M := Φ (mk32 84) ⊔ Φ (mk32 124) ⊔ Φ (mk32 167) with hQ
  have hinit : ∀ t ∈ [84, 124, 167], Φ (mk32 t) ≤ Q := by
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · exact le_trans le_sup_left le_sup_left
    · exact le_trans le_sup_right le_sup_left
    · exact le_sup_right
  have hall : ∀ t ∈ invCodes, Φ (mk32 t) ≤ Q := by
    intro t ht
    have hcov := of_decide_eq_true (List.all_eq_true.1 steps_cover t ht)
    exact H.steps_le stepTab [84, 124, 167] steps_ok hinit t hcov
  obtain ⟨hm1, hm2, hm3⟩ := triple_mates
  have commOf : ∀ a b : ℕ, mateTab.any (fun e => e.1 == a && e.2.1 == b && chkMateE e) = true →
      ∀ u v : M, u ∈ Φ (mk32 a) → v ∈ Φ (mk32 b) → u * v = v * u := by
    intro a b hmt u v hu hv
    obtain ⟨e, he, hee⟩ := List.any_eq_true.1 hmt
    simp only [Bool.and_eq_true, beq_iff_eq] at hee
    obtain ⟨⟨he1, he2⟩, hchk⟩ := hee
    rw [← he1] at hu
    rw [← he2] at hv
    exact H.mate_comm hchk hu hv
  have mem_gen : ∀ t ∈ invCodes, gen t ∈ Φ (mk32 t) := by
    intro t ht
    rw [hgΦ t ht]
    exact Subgroup.mem_zpowers _
  have c12 : Commute (gen 84) (gen 124) :=
    commOf 84 124 hm1 _ _ (mem_gen 84 h84) (mem_gen 124 h124)
  have c13 : Commute (gen 84) (gen 167) :=
    commOf 84 167 hm2 _ _ (mem_gen 84 h84) (mem_gen 167 h167)
  have c23 : Commute (gen 124) (gen 167) :=
    commOf 124 167 hm3 _ _ (mem_gen 124 h124) (mem_gen 167 h167)
  have hQle : Q ≤ Subgroup.closure ({gen 84, gen 124, gen 167} : Set M) := by
    rw [hQ, hgΦ 84 h84, hgΦ 124 h124, hgΦ 167 h167]
    refine sup_le (sup_le (Subgroup.zpowers_le.2 (Subgroup.subset_closure ?_))
      (Subgroup.zpowers_le.2 (Subgroup.subset_closure ?_)))
      (Subgroup.zpowers_le.2 (Subgroup.subset_closure ?_))
    · simp
    · simp
    · simp
  refine count_false (gen 84) (gen 124) (gen 167) c12 c13 c23 (hg3 84 h84) (hg3 124 h124)
    (hg3 167 h167) (fun i => gen (invCodes.getD i 0)) (fun i => hg3 _ (invCodes_mem i))
    (fun i => hg1 _ (invCodes_mem i)) ?_ ?_
  · intro i
    exact hQle (hall _ (invCodes_mem i) (mem_gen _ (invCodes_mem i)))
  · intro i j hij hmem
    have heq := zpowers_eq_of_mem (hg3 _ (invCodes_mem i)) (hg1 _ (invCodes_mem i))
      (hg3 _ (invCodes_mem j)) (hg1 _ (invCodes_mem j)) hmem
    rw [← hgΦ _ (invCodes_mem i), ← hgΦ _ (invCodes_mem j)] at heq
    have hne : invCodes.getD j 0 ≠ invCodes.getD i 0 := fun h => hij (invCodes_code j i h).symm
    exact H.pair_ne _ (invCodes_mem j) _ (invCodes_mem i) hne heq

end Core

section Indep

variable {M : Type*} [Group M]

@[expose] def aT (i : ℕ) : ℤ := [1, 1, 0, -1].getD i 0

@[expose] def bT (i : ℕ) : ℤ := [0, -1, 1, -1].getD i 0

@[expose] def yEF (e f : M) (i : ℕ) : M := e ^ aT i * f ^ bT i

theorem zpow_congr3 {z : M} (hz : z ^ 3 = 1) {a b : ℤ} (h : (3 : ℤ) ∣ a - b) : z ^ a = z ^ b := by
  obtain ⟨k, hk⟩ := h
  have e1 : a = b + 3 * k := by omega
  have h3 : z ^ (3 : ℤ) = 1 := by exact_mod_cast hz
  rw [e1, zpow_add, zpow_mul, h3, one_zpow, mul_one]

theorem indep_eq {e f : M} (he3 : e ^ 3 = 1) (hf3 : f ^ 3 = 1) {a b a' b' : ℤ}
    (ha : (3 : ℤ) ∣ a - a') (hb : (3 : ℤ) ∣ b - b') : e ^ a * f ^ b = e ^ a' * f ^ b' := by
  rw [zpow_congr3 he3 ha, zpow_congr3 hf3 hb]

theorem yEF_pow {e f : M} (hc : Commute e f) (a b m : ℤ) :
    (e ^ a * f ^ b) ^ m = e ^ (a * m) * f ^ (b * m) := by
  rw [(((hc.zpow_zpow a b)).mul_zpow m), ← zpow_mul, ← zpow_mul]

theorem yEF_dvd {e f : M}
    (hindep : ∀ a b : ℤ, e ^ a * f ^ b = 1 → (3 : ℤ) ∣ a ∧ (3 : ℤ) ∣ b) {a b a' b' : ℤ}
    (hc : Commute e f) (h : e ^ a * f ^ b = e ^ a' * f ^ b') :
    (3 : ℤ) ∣ a - a' ∧ (3 : ℤ) ∣ b - b' := by
  apply hindep
  have : e ^ (a - a') * f ^ (b - b') = (e ^ a * f ^ b) * (e ^ a' * f ^ b')⁻¹ := by
    have c : Commute (f ^ (b - b')) (e ^ a')⁻¹ := (hc.symm.zpow_zpow (b - b') a').inv_right
    calc e ^ (a - a') * f ^ (b - b') = (e ^ a * (e ^ a')⁻¹) * f ^ (b - b') := by rw [zpow_sub]
      _ = e ^ a * ((e ^ a')⁻¹ * f ^ (b - b')) := by rw [mul_assoc]
      _ = e ^ a * (f ^ (b - b') * (e ^ a')⁻¹) := by rw [c.eq]
      _ = e ^ a * ((f ^ b * (f ^ b')⁻¹) * (e ^ a')⁻¹) := by rw [zpow_sub]
      _ = (e ^ a * f ^ b) * ((f ^ b')⁻¹ * (e ^ a')⁻¹) := by simp only [mul_assoc]
      _ = (e ^ a * f ^ b) * (e ^ a' * f ^ b')⁻¹ := by rw [mul_inv_rev]
  rw [this, h]
  simp

theorem aT_ne : ∀ i < 4, ¬ ((3 : ℤ) ∣ aT i ∧ (3 : ℤ) ∣ bT i) := by decide

theorem aT_dist : ∀ i < 4, ∀ j < 4, i ≠ j → ∀ m : ℤ,
    ¬ ((3 : ℤ) ∣ m * aT j - aT i ∧ (3 : ℤ) ∣ m * bT j - bT i) := by
  intro i hi j hj hij m
  interval_cases i <;> interval_cases j <;> simp [aT, bT] at hij ⊢ <;> omega

theorem aT_clos : ∀ i j k : Fin 4, i ≠ j → i ≠ k → j ≠ k →
    ∃ α : Fin 3, ∃ β : Fin 3, (3 : ℤ) ∣ aT i - (((α : ℕ) : ℤ) * aT j + ((β : ℕ) : ℤ) * aT k) ∧
      (3 : ℤ) ∣ bT i - (((α : ℕ) : ℤ) * bT j + ((β : ℕ) : ℤ) * bT k) := by decide

theorem nf_mul {e f : M} (hc : Commute e f) (a b a' b' : ℤ) :
    (e ^ a * f ^ b) * (e ^ a' * f ^ b') = e ^ (a + a') * f ^ (b + b') := by
  have c : Commute (f ^ b) (e ^ a') := hc.symm.zpow_zpow b a'
  calc (e ^ a * f ^ b) * (e ^ a' * f ^ b') = e ^ a * ((f ^ b * e ^ a') * f ^ b') := by
        simp only [mul_assoc]
    _ = e ^ a * ((e ^ a' * f ^ b) * f ^ b') := by rw [c.eq]
    _ = (e ^ a * e ^ a') * (f ^ b * f ^ b') := by simp only [mul_assoc]
    _ = e ^ (a + a') * f ^ (b + b') := by rw [zpow_add, zpow_add]

end Indep

section OfIndep

variable {M : Type*} [Group M]

theorem EvenHyp.of_indep {Φ : M32 → Subgroup M} (e f : M) (he3 : e ^ 3 = 1) (hf3 : f ^ 3 = 1)
    (hc : Commute e f) (hindep : ∀ a b : ℤ, e ^ a * f ^ b = 1 → (3 : ℤ) ∣ a ∧ (3 : ℤ) ∣ b)
    (hconj : ∀ h : M32, det3 h = 1 → ∃ σ : MulAut M, ∀ g g₁ : M32, det3 g = 1 → h * g = g₁ * h →
      Φ g₁ = (Φ g).map σ.toMonoidHom)
    (hbase : ∀ i < 4, Φ (mk32 (baseNode i)) = Subgroup.zpowers (yEF e f i)) :
    EvenHyp Φ (yEF e f) := by
  refine ⟨hconj, ?_, ?_, ?_, ?_, ?_, hbase⟩
  · intro i hi
    unfold yEF
    have h3 : (e ^ aT i * f ^ bT i) ^ 3 = e ^ (aT i * 3) * f ^ (bT i * 3) := by
      have := yEF_pow hc (aT i) (bT i) 3
      simpa using this
    rw [h3, mul_comm (aT i) 3, mul_comm (bT i) 3, zpow_mul, zpow_mul]
    have e3 : e ^ (3 : ℤ) = 1 := by exact_mod_cast he3
    have f3 : f ^ (3 : ℤ) = 1 := by exact_mod_cast hf3
    rw [e3, f3]
    simp
  · intro i hi h
    unfold yEF at h
    apply aT_ne i hi
    have := hindep _ _ h
    exact this
  · intro i hi j hj
    unfold yEF
    have c11 : Commute (e ^ aT i) (e ^ aT j) := (Commute.refl e).zpow_zpow _ _
    have c12 : Commute (e ^ aT i) (f ^ bT j) := hc.zpow_zpow _ _
    have c21 : Commute (f ^ bT i) (e ^ aT j) := hc.symm.zpow_zpow _ _
    have c22 : Commute (f ^ bT i) (f ^ bT j) := (Commute.refl f).zpow_zpow _ _
    exact ((c11.mul_right c12).mul_left (c21.mul_right c22)).eq
  · intro i hi j hj hij hmem
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hmem
    unfold yEF at hm
    rw [yEF_pow hc] at hm
    obtain ⟨d1, d2⟩ := yEF_dvd hindep hc hm
    apply aT_dist i hi j hj hij m
    exact ⟨by rw [mul_comm m]; exact d1, by rw [mul_comm m]; exact d2⟩
  · intro i hi j hj k hk hij hik hjk
    obtain ⟨α, β, d1, d2⟩ := aT_clos ⟨i, hi⟩ ⟨j, hj⟩ ⟨k, hk⟩ (fun h => hij (congrArg Fin.val h))
      (fun h => hik (congrArg Fin.val h)) (fun h => hjk (congrArg Fin.val h))
    have hy : yEF e f i = yEF e f j ^ ((α : ℕ) : ℤ) * yEF e f k ^ ((β : ℕ) : ℤ) := by
      unfold yEF
      rw [yEF_pow hc, yEF_pow hc, nf_mul hc]
      apply indep_eq he3 hf3
      · convert d1 using 2
        ring
      · convert d2 using 2
        ring
    rw [hy]
    exact Subgroup.mul_mem_sup (Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _)
      (Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _)

end OfIndep

end CFSG.RankThree.PartOne.NF7J
