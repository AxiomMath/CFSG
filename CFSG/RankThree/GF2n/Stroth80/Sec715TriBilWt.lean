module

public import CFSG.RankThree.GF2n.Stroth80.Sec715TriNF
public import CFSG.LieType.D4Small.WeightClass

public section

namespace CFSG.RankThree.GF2n.Stroth80.Tri

open CFSG.LieType.D4Small
open scoped symmDiff

variable {N : ℕ}

theorem bil_nontrivial (h3 : 3 ≤ N) : Nontrivial (ZMod N) := by
  haveI : Fact (1 < N) := ⟨by omega⟩
  infer_instance

theorem bil_isUnit_two (hN : Odd N) : IsUnit (2 : ZMod N) := by
  have h2 : ((2 : ℕ) : ZMod N) = 2 := by norm_num
  rw [← h2, ZMod.isUnit_iff_coprime]
  exact Nat.coprime_two_left.mpr hN

theorem bil_two_mul_ne_zero (h3 : 3 ≤ N) {b₀ : ZMod N} (hb : IsUnit (2 * b₀)) :
    2 * b₀ ≠ 0 := by
  haveI := bil_nontrivial h3
  exact hb.ne_zero

theorem bil_four_mul_ne_zero (hN : Odd N) (h3 : 3 ≤ N) {b₀ : ZMod N} (hb : IsUnit (2 * b₀)) :
    4 * b₀ ≠ 0 := by
  haveI := bil_nontrivial h3
  have h4 : 4 * b₀ = 2 * (2 * b₀) := by ring
  rw [h4]
  exact ((bil_isUnit_two hN).mul hb).ne_zero

theorem bil_ne_neg (h3 : 3 ≤ N) {b₀ : ZMod N} (hb : IsUnit (2 * b₀)) : b₀ ≠ -b₀ := by
  intro h
  apply bil_two_mul_ne_zero h3 hb
  linear_combination h

theorem bil_ne_zero_of_isUnit_two_mul (h3 : 3 ≤ N) {b₀ : ZMod N} (hb : IsUnit (2 * b₀)) :
    b₀ ≠ 0 := by
  intro h
  apply bil_two_mul_ne_zero h3 hb
  rw [h, mul_zero]

theorem bil_three_mul_ne (hN : Odd N) (h3 : 3 ≤ N) {b₀ : ZMod N} (hb : IsUnit (2 * b₀)) :
    3 * b₀ ≠ b₀ ∧ 3 * b₀ ≠ -b₀ := by
  have h2 := bil_two_mul_ne_zero h3 hb
  have h4 := bil_four_mul_ne_zero hN h3 hb
  constructor
  · intro h
    apply h2
    linear_combination h
  · intro h
    apply h4
    linear_combination h

@[expose] def bilSpinW (b₀ : ZMod N) (s : Finset (Fin 4)) : Fin 4 → ZMod N :=
  fun i => if i ∈ s then -b₀ else b₀

@[expose] def bilSpinSg (s : Finset (Fin 4)) (i : Fin 4) : ℤ := if i ∈ s then -1 else 1

theorem bil_spinSg_eq (s : Finset (Fin 4)) (i : Fin 4) :
    bilSpinSg s i = 1 ∨ bilSpinSg s i = -1 := by
  unfold bilSpinSg
  split_ifs <;> simp

theorem bil_spinW_apply_eq (b₀ : ZMod N) (s : Finset (Fin 4)) (i : Fin 4) :
    bilSpinW b₀ s i = (bilSpinSg s i : ZMod N) * b₀ := by
  by_cases h : i ∈ s <;> simp [bilSpinW, bilSpinSg, h]

theorem bil_isSpinWt_spinW {b₀ : ZMod N} (hb : b₀ ≠ -b₀) {e : ℕ} {s : Finset (Fin 4)} :
    IsSpinWt b₀ e (bilSpinW b₀ s) ↔ s.card % 2 = e % 2 := by
  have hf : Finset.univ.filter (fun i => bilSpinW b₀ s i = -b₀) = s := by
    ext i
    by_cases h : i ∈ s <;> simp [bilSpinW, h, hb]
  unfold IsSpinWt
  rw [hf]
  refine ⟨fun h => h.2, fun h => ⟨fun i => ?_, h⟩⟩
  by_cases hi : i ∈ s <;> simp [bilSpinW, hi]

theorem bil_exists_spinW_of_isSpinWt {b₀ : ZMod N} (hb : b₀ ≠ -b₀) {e : ℕ} {a : Fin 4 → ZMod N}
    (h : IsSpinWt b₀ e a) : ∃ s : Finset (Fin 4), s.card % 2 = e % 2 ∧ a = bilSpinW b₀ s := by
  refine ⟨Finset.univ.filter (fun i => a i = -b₀), h.2, ?_⟩
  funext i
  rcases h.1 i with hi | hi
  · simp [bilSpinW, hi, hb]
  · simp [bilSpinW, hi]

private theorem bil_card_symmDiff_pair_all :
    ∀ (s : Finset (Fin 4)) (p k : Fin 4), p ≠ k → (s ∆ {p, k}).card % 2 = s.card % 2 := by
  decide

theorem bil_card_symmDiff_pair (s : Finset (Fin 4)) {p k : Fin 4} (h : p ≠ k) :
    (s ∆ {p, k}).card % 2 = s.card % 2 :=
  bil_card_symmDiff_pair_all s p k h

private theorem bil_card_compl_symmDiff_single_all :
    ∀ (s : Finset (Fin 4)) (p : Fin 4), ((s ∆ {p})ᶜ).card % 2 = (s.card + 1) % 2 := by
  decide

theorem bil_card_compl_symmDiff_single (s : Finset (Fin 4)) (p : Fin 4) :
    ((s ∆ {p})ᶜ).card % 2 = (s.card + 1) % 2 :=
  bil_card_compl_symmDiff_single_all s p

theorem bil_compl_symmDiff_compl_symmDiff (s : Finset (Fin 4)) (p : Fin 4) :
    ((s ∆ {p})ᶜ ∆ {p})ᶜ = s := by
  revert s p
  decide

private theorem bil_symmDiff_pair_single_all :
    ∀ (s : Finset (Fin 4)) (p k : Fin 4), p ≠ k → s ∆ {p, k} ∆ {k} = s ∆ {p} := by
  decide

theorem bil_symmDiff_pair_single (s : Finset (Fin 4)) {p k : Fin 4} (h : p ≠ k) :
    s ∆ {p, k} ∆ {k} = s ∆ {p} :=
  bil_symmDiff_pair_single_all s p k h

private theorem bil_compl_symmDiff_pair_all :
    ∀ (s : Finset (Fin 4)) (p k : Fin 4), p ≠ k → (s ∆ {p})ᶜ ∆ {p, k} = (s ∆ {k})ᶜ := by
  decide

theorem bil_compl_symmDiff_pair (s : Finset (Fin 4)) {p k : Fin 4} (h : p ≠ k) :
    (s ∆ {p})ᶜ ∆ {p, k} = (s ∆ {k})ᶜ :=
  bil_compl_symmDiff_pair_all s p k h

private theorem bil_even_decomp_all : ∀ D : Finset (Fin 4), D.card % 2 = 0 →
    D = ∅ ∨ (∃ p k, p ≠ k ∧ D = {p, k}) ∨ D = Finset.univ := by
  decide

private theorem bil_symmDiff_univ_all :
    ∀ s : Finset (Fin 4), s ∆ Finset.univ = (s ∆ {0, 1}) ∆ {2, 3} := by
  decide

private theorem bil_symmDiff_symmDiff_all :
    ∀ s s' : Finset (Fin 4), s ∆ (s ∆ s') = s' := by
  decide

private theorem bil_card_symmDiff_even_all :
    ∀ s s' : Finset (Fin 4), s.card % 2 = s'.card % 2 → (s ∆ s').card % 2 = 0 := by
  decide

theorem bil_conn_aux {R : Type*} (F : Finset (Fin 4) → Fin 4 → R) {r : ℕ}
    (hM2 : ∀ s p k, s.card % 2 = r → p ≠ k → F s p = F s k)
    (hM1 : ∀ s p k, s.card % 2 = r → p ≠ k → F s p = F (s ∆ {p, k}) k)
    {s s' : Finset (Fin 4)} (hs : s.card % 2 = r) (hs' : s'.card % 2 = r) (p p' : Fin 4) :
    F s p = F s' p' := by
  have hp : ∀ t, t.card % 2 = r → ∀ q q', F t q = F t q' := by
    intro t ht q q'
    by_cases hq : q = q'
    · rw [hq]
    · exact hM2 t q q' ht hq
  have hG : ∀ t q k, t.card % 2 = r → q ≠ k → F t 0 = F (t ∆ {q, k}) 0 := by
    intro t q k ht hqk
    rw [hp t ht 0 q, hM1 t q k ht hqk,
      hp _ (by rw [bil_card_symmDiff_pair t hqk]; exact ht) k 0]
  have h01 : (0 : Fin 4) ≠ 1 := by decide
  have h23 : (2 : Fin 4) ≠ 3 := by decide
  rw [hp s hs p 0, hp s' hs' p' 0]
  have hD := bil_card_symmDiff_even_all s s' (hs.trans hs'.symm)
  have hs'' : s' = s ∆ (s ∆ s') := (bil_symmDiff_symmDiff_all s s').symm
  generalize s ∆ s' = D at hD hs''
  subst hs''
  rcases bil_even_decomp_all D hD with rfl | ⟨q, k, hqk, rfl⟩ | rfl
  · rw [show s ∆ (∅ : Finset (Fin 4)) = s from symmDiff_bot s]
  · exact hG s q k hs hqk
  · rw [bil_symmDiff_univ_all]
    exact (hG s 0 1 hs h01).trans
      (hG _ 2 3 (by rw [bil_card_symmDiff_pair s h01]; exact hs) h23)

private theorem bil_spin_sum_eq_zero_iff {b₀ : ZMod N} (hb : 2 * b₀ ≠ 0) (s s' : Finset (Fin 4))
    (j : Fin 4) :
    bilSpinW b₀ s j + bilSpinW b₀ s' j = 0 ↔ ¬ (j ∈ s ↔ j ∈ s') := by
  by_cases h1 : j ∈ s <;> by_cases h2 : j ∈ s' <;> simp [bilSpinW, h1, h2]
  · intro h; apply hb; linear_combination -h
  · intro h; apply hb; linear_combination h

theorem bil_spin_add_spin {b₀ c : ZMod N} (hb : 2 * b₀ ≠ 0) (hc : c ≠ 0)
    {s s' : Finset (Fin 4)} (h : IsNatWt c (bilSpinW b₀ s + bilSpinW b₀ s')) :
    ∃ p, s' = (s ∆ {p})ᶜ := by
  obtain ⟨i, hi⟩ := h
  obtain ⟨v, hv0, hv⟩ : ∃ v : ZMod N, v ≠ 0 ∧ bilSpinW b₀ s + bilSpinW b₀ s' = Pi.single i v := by
    rcases hi with hi | hi
    · exact ⟨c, hc, hi⟩
    · exact ⟨-c, neg_ne_zero.mpr hc, hi⟩
  refine ⟨i, ?_⟩
  have hcoord : ∀ j, j ≠ i → ¬ (j ∈ s ↔ j ∈ s') := by
    intro j hji
    rw [← bil_spin_sum_eq_zero_iff hb s s' j]
    have := congrFun hv j
    rw [Pi.single_apply, if_neg hji] at this
    exact this
  have hi' : (i ∈ s ↔ i ∈ s') := by
    by_contra hne
    apply hv0
    have := congrFun hv i
    rw [Pi.single_apply, if_pos rfl] at this
    rw [← this]
    exact (bil_spin_sum_eq_zero_iff hb s s' i).mpr hne
  ext j
  rw [Finset.mem_compl, Finset.mem_symmDiff]
  by_cases hji : j = i
  · subst hji
    simp only [Finset.mem_singleton, not_true_eq_false, and_false, true_and, false_or]
    tauto
  · have := hcoord j hji
    simp only [Finset.mem_singleton, hji, false_and, and_true, not_false_eq_true, true_and,
      or_false]
    tauto

private theorem bil_exists_ne_ne : ∀ i k : Fin 4, ∃ j : Fin 4, j ≠ i ∧ j ≠ k := by decide

theorem bil_natWt_eq {σ : ZMod N} {a : Fin 4 → ZMod N} (h : IsNatWt σ a) :
    ∃ k u, (u = σ ∨ u = -σ) ∧ a = Pi.single k u := by
  obtain ⟨k, hk | hk⟩ := h
  · exact ⟨k, σ, Or.inl rfl, hk⟩
  · exact ⟨k, -σ, Or.inr rfl, hk⟩

theorem bil_natWt_ne_zero {σ u : ZMod N} (hσ : σ ≠ 0) (hu : u = σ ∨ u = -σ) : u ≠ 0 := by
  rcases hu with rfl | rfl
  · exact hσ
  · exact neg_ne_zero.mpr hσ

theorem bil_isNatWt_single {σ u : ZMod N} (hu : u = σ ∨ u = -σ) (k : Fin 4) :
    IsNatWt σ (Pi.single k u) := by
  rcases hu with rfl | rfl
  · exact ⟨k, Or.inl rfl⟩
  · exact ⟨k, Or.inr rfl⟩

theorem bil_nat_add_nat {σ c : ZMod N} (hσ : σ ≠ 0) (hc : c ≠ 0) {a b : Fin 4 → ZMod N}
    (ha : IsNatWt σ a) (hb : IsNatWt σ b) (hab : IsNatWt c (a + b)) : a = b := by
  obtain ⟨k, u, hu, rfl⟩ := bil_natWt_eq ha
  obtain ⟨l, u', hu', rfl⟩ := bil_natWt_eq hb
  obtain ⟨i, v, hv, hsum⟩ := bil_natWt_eq hab
  have hu0 := bil_natWt_ne_zero hσ hu
  have hu0' := bil_natWt_ne_zero hσ hu'
  have hv0 := bil_natWt_ne_zero hc hv
  have hkl : k = l := by
    by_contra hkl
    have h1 := congrFun hsum k
    have h2 := congrFun hsum l
    simp only [Pi.add_apply, Pi.single_apply, if_pos rfl, if_neg hkl, if_neg (Ne.symm hkl),
      add_zero, zero_add] at h1 h2
    have hki : k = i := by
      by_contra hki
      rw [if_neg hki] at h1
      exact hu0 h1
    have hli : l = i := by
      by_contra hli
      rw [if_neg hli] at h2
      exact hu0' h2
    exact hkl (hki.trans hli.symm)
  subst hkl
  have hik : k = i := by
    by_contra hik
    have h1 := congrFun hsum i
    simp only [Pi.add_apply, Pi.single_apply, if_pos rfl, if_neg (Ne.symm hik), add_zero] at h1
    exact hv0 h1.symm
  subst hik
  have h1 := congrFun hsum k
  simp only [Pi.add_apply, Pi.single_eq_same] at h1
  congr 1
  rcases hu with rfl | rfl <;> rcases hu' with rfl | rfl
  · rfl
  · exfalso; apply hv0; rw [← h1]; ring
  · exfalso; apply hv0; rw [← h1]; ring
  · rfl

theorem bil_not_natWt_add_spin {σ c b₀ : ZMod N} {e : ℕ} (hb₀ : b₀ ≠ 0) {a b : Fin 4 → ZMod N}
    (ha : IsNatWt σ a) (hb : IsSpinWt b₀ e b) : ¬ IsNatWt c (a + b) := by
  intro h
  obtain ⟨k, u, hu, rfl⟩ := bil_natWt_eq ha
  obtain ⟨i, v, hv, hsum⟩ := bil_natWt_eq h
  obtain ⟨j, hji, hjk⟩ := bil_exists_ne_ne i k
  have h1 := congrFun hsum j
  simp only [Pi.add_apply, Pi.single_apply, if_neg hji, if_neg hjk, zero_add] at h1
  rcases hb.1 j with h2 | h2
  · exact hb₀ (h2 ▸ h1)
  · exact hb₀ (neg_eq_zero.mp (h2 ▸ h1))

theorem bil_not_natWt_spin_add {σ c b₀ : ZMod N} {e : ℕ} (hb₀ : b₀ ≠ 0) {a b : Fin 4 → ZMod N}
    (ha : IsSpinWt b₀ e a) (hb : IsNatWt σ b) : ¬ IsNatWt c (a + b) := by
  rw [add_comm]
  exact bil_not_natWt_add_spin hb₀ hb ha

theorem bil_spinSg_symmDiff_pair_left (s : Finset (Fin 4)) {p k : Fin 4} (h : p ≠ k) :
    bilSpinSg (s ∆ {p, k}) p = -bilSpinSg s p := by
  by_cases hp : p ∈ s <;> simp [bilSpinSg, hp, Finset.mem_symmDiff]

theorem bil_spinSg_symmDiff_pair_right (s : Finset (Fin 4)) {p k : Fin 4} (h : p ≠ k) :
    bilSpinSg (s ∆ {p, k}) k = -bilSpinSg s k := by
  by_cases hk : k ∈ s <;> simp [bilSpinSg, hk, Finset.mem_symmDiff]

theorem bil_spinSg_symmDiff_pair_other (s : Finset (Fin 4)) {p k i : Fin 4} (hp : i ≠ p)
    (hk : i ≠ k) : bilSpinSg (s ∆ {p, k}) i = bilSpinSg s i := by
  by_cases hi : i ∈ s <;> simp [bilSpinSg, hi, Finset.mem_symmDiff, hp, hk]

theorem bil_spinSg_compl_symmDiff_self (s : Finset (Fin 4)) (p : Fin 4) :
    bilSpinSg ((s ∆ {p})ᶜ) p = bilSpinSg s p := by
  by_cases hp : p ∈ s <;> simp [bilSpinSg, hp, Finset.mem_symmDiff]

theorem bil_spinSg_compl_symmDiff_other (s : Finset (Fin 4)) {p i : Fin 4} (h : i ≠ p) :
    bilSpinSg ((s ∆ {p})ᶜ) i = -bilSpinSg s i := by
  by_cases hi : i ∈ s <;> simp [bilSpinSg, hi, Finset.mem_symmDiff, h]

@[expose] def bilSpinRoot (s : Finset (Fin 4)) (p k : Fin 4) : Fin 4 → ℤ :=
  Pi.single p (-bilSpinSg s p) + Pi.single k (-bilSpinSg s k)

theorem bil_isD4Root_spinRoot (s : Finset (Fin 4)) {p k : Fin 4} (h : p ≠ k) :
    IsD4Root (bilSpinRoot s p k) := by
  refine isD4Root_single_add_single h ?_ ?_
  · rcases bil_spinSg_eq s p with h | h <;> simp [h]
  · rcases bil_spinSg_eq s k with h | h <;> simp [h]

theorem bil_castW_spinRoot_apply (N : ℕ) (s : Finset (Fin 4)) (p k i : Fin 4) :
    castW N (bilSpinRoot s p k) i =
      (if i = p then -(bilSpinSg s p : ZMod N) else 0) +
        (if i = k then -(bilSpinSg s k : ZMod N) else 0) := by
  simp only [castW, bilSpinRoot, Pi.add_apply, Pi.single_apply, Int.cast_add]
  split_ifs <;> simp

theorem bil_spinW_add_spinRoot (b₀ : ZMod N) (s : Finset (Fin 4)) {p k : Fin 4} (h : p ≠ k) :
    bilSpinW b₀ s + (2 * b₀) • castW N (bilSpinRoot s p k) = bilSpinW b₀ (s ∆ {p, k}) := by
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, bil_castW_spinRoot_apply,
    bil_spinW_apply_eq]
  by_cases hip : i = p
  · subst hip
    rw [if_pos rfl, if_neg h, bil_spinSg_symmDiff_pair_left s h]
    push_cast
    ring
  · by_cases hik : i = k
    · subst hik
      rw [if_neg hip, if_pos rfl, bil_spinSg_symmDiff_pair_right s h]
      push_cast
      ring
    · rw [if_neg hip, if_neg hik, bil_spinSg_symmDiff_pair_other s hip hik]
      ring

theorem bil_spinW_add_spinW_compl (b₀ : ZMod N) (s : Finset (Fin 4)) (p : Fin 4) :
    bilSpinW b₀ s + bilSpinW b₀ ((s ∆ {p})ᶜ) =
      Pi.single p (2 * b₀ * (bilSpinSg s p : ZMod N)) := by
  funext i
  simp only [Pi.add_apply, bil_spinW_apply_eq, Pi.single_apply]
  by_cases hip : i = p
  · subst hip
    rw [if_pos rfl, bil_spinSg_compl_symmDiff_self]
    ring
  · rw [if_neg hip, bil_spinSg_compl_symmDiff_other s hip]
    push_cast
    ring

theorem bil_spinW_add_spinW_compl_add_spinRoot (b₀ : ZMod N) (s : Finset (Fin 4)) {p k : Fin 4}
    (h : p ≠ k) :
    bilSpinW b₀ s + bilSpinW b₀ ((s ∆ {p})ᶜ) + (2 * b₀) • castW N (bilSpinRoot s p k) =
      Pi.single k (-(2 * b₀ * (bilSpinSg s k : ZMod N))) := by
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, bil_castW_spinRoot_apply,
    bil_spinW_apply_eq, Pi.single_apply]
  by_cases hip : i = p
  · subst hip
    rw [if_pos rfl, if_neg h, if_neg h, bil_spinSg_compl_symmDiff_self]
    ring
  · by_cases hik : i = k
    · subst hik
      rw [if_neg hip, if_pos rfl, if_pos rfl, bil_spinSg_compl_symmDiff_other s h.symm]
      push_cast
      ring
    · rw [if_neg hip, if_neg hik, if_neg hik, bil_spinSg_compl_symmDiff_other s hip]
      push_cast
      ring

theorem bil_spinW_compl_sub_spinRoot_apply (b₀ : ZMod N) (s : Finset (Fin 4)) {p k : Fin 4}
    (h : p ≠ k) :
    (bilSpinW b₀ ((s ∆ {p})ᶜ) - (2 * b₀) • castW N (bilSpinRoot s p k)) p =
      (bilSpinSg s p : ZMod N) * (3 * b₀) := by
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, bil_castW_spinRoot_apply,
    bil_spinW_apply_eq, if_true, if_neg h, add_zero, bil_spinSg_compl_symmDiff_self]
  ring

theorem bil_spinW_compl_add_spinRoot_apply (b₀ : ZMod N) (s : Finset (Fin 4)) {p k : Fin 4}
    (h : p ≠ k) :
    (bilSpinW b₀ ((s ∆ {p})ᶜ) + (2 * b₀) • castW N (bilSpinRoot s p k)) k =
      -((bilSpinSg s k : ZMod N) * (3 * b₀)) := by
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, bil_castW_spinRoot_apply,
    bil_spinW_apply_eq, if_true, if_neg h.symm, zero_add, bil_spinSg_compl_symmDiff_other s h.symm]
  push_cast
  ring

theorem bil_isUnit_two_pow (hN : Odd N) (j : ℕ) : IsUnit ((2 : ZMod N) ^ j) :=
  (bil_isUnit_two hN).pow j

theorem bil_castW_single_add_single (N : ℕ) (i k : Fin 4) (a b : ℤ) (m : Fin 4) :
    castW N (Pi.single i a + Pi.single k b) m =
      (if m = i then (a : ZMod N) else 0) + (if m = k then (b : ZMod N) else 0) := by
  simp only [castW, Pi.add_apply, Pi.single_apply, Int.cast_add]
  split_ifs <;> simp

theorem bil_not_isNatWt_of_two {σ : ZMod N} {w : Fin 4 → ZMod N} {k m : Fin 4} (hkm : k ≠ m)
    (hk : w k ≠ 0) (hm : w m ≠ 0) : ¬ IsNatWt σ w := by
  intro h
  obtain ⟨i, u, -, rfl⟩ := bil_natWt_eq h
  rw [Pi.single_apply] at hk hm
  have h1 : k = i := by
    by_contra h'
    exact hk (if_neg h')
  have h2 : m = i := by
    by_contra h'
    exact hm (if_neg h')
  exact hkm (h1.trans h2.symm)

theorem bil_natWt_step {σ : ZMod N} {w : Fin 4 → ZMod N} (h : IsNatWt σ w) :
    ∃ w', IsNatWt σ w' ∧ ∃ γ : Fin 4 → ℤ, IsD4Root γ ∧ w = w' + σ • castW N γ := by
  obtain ⟨i, u, hu, rfl⟩ := bil_natWt_eq h
  obtain ⟨k, hki⟩ := exists_ne i
  refine ⟨Pi.single k u, bil_isNatWt_single hu k, ?_⟩
  rcases hu with rfl | rfl
  · refine ⟨Pi.single i 1 + Pi.single k (-1),
      isD4Root_single_add_single hki.symm (Or.inl rfl) (Or.inr rfl), ?_⟩
    funext m
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, bil_castW_single_add_single,
      Pi.single_apply]
    by_cases hmi : m = i
    · subst hmi
      simp [hki.symm]
    · by_cases hmk : m = k
      · subst hmk
        simp [hki]
      · simp [hmi, hmk]
  · refine ⟨Pi.single i (-1) + Pi.single k 1,
      isD4Root_single_add_single hki.symm (Or.inr rfl) (Or.inl rfl), ?_⟩
    funext m
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, bil_castW_single_add_single,
      Pi.single_apply]
    by_cases hmi : m = i
    · subst hmi
      simp [hki.symm]
    · by_cases hmk : m = k
      · subst hmk
        simp [hki]
      · simp [hmi, hmk]

theorem bil_reach (hN : Odd N) (h3 : 3 ≤ N) {j : ℕ} {C : Finset (Fin 4 → ZMod N)}
    (hC : NFType j C) {b' : Fin 4 → ZMod N} (hb' : b' ∈ C) :
    ∃ b ∈ C, ∃ γ : Fin 4 → ℤ, IsD4Root γ ∧ b' = b + (2 : ZMod N) ^ j • castW N γ := by
  rcases hC with hC | ⟨b₀, e, hb₀, he, hC⟩
  · obtain ⟨w', hw', γ, hγ, h⟩ := bil_natWt_step ((hC b').mp hb')
    exact ⟨w', (hC w').mpr hw', γ, hγ, h⟩
  · have hu : IsUnit (2 * b₀) := by rw [hb₀]; exact bil_isUnit_two_pow hN j
    obtain ⟨s, hs, rfl⟩ := bil_exists_spinW_of_isSpinWt (bil_ne_neg h3 hu) ((hC b').mp hb')
    have h01 : (0 : Fin 4) ≠ 1 := by decide
    refine ⟨bilSpinW b₀ (s ∆ {0, 1}), (hC _).mpr ((bil_isSpinWt_spinW (bil_ne_neg h3 hu)).mpr ?_),
      -bilSpinRoot s 0 1, (bil_isD4Root_spinRoot s h01).neg, ?_⟩
    · rw [bil_card_symmDiff_pair s h01]
      exact hs
    · rw [castW_neg, smul_neg, ← hb₀, ← bil_spinW_add_spinRoot b₀ s h01]
      abel

theorem bil_natWt_add_step {w : Fin 4 → ZMod N} (h : IsNatWt (1 : ZMod N) w) :
    ∃ γ : Fin 4 → ℤ, IsD4Root γ ∧ IsNatWt (1 : ZMod N) (w + castW N γ) := by
  obtain ⟨w', hw', γ, hγ, rfl⟩ := bil_natWt_step h
  refine ⟨-γ, hγ.neg, ?_⟩
  rw [castW_neg, one_smul, add_neg_cancel_right]
  exact hw'

theorem bil_nat_step_out (hN : Odd N) (h3 : 3 ≤ N) {σ : ZMod N} (hσ : σ ≠ 0) {k : Fin 4}
    {u : ZMod N} (hu : u = σ ∨ u = -σ) :
    ∃ γ : Fin 4 → ℤ, IsD4Root γ ∧ IsNatWt σ (Pi.single k u - σ • castW N γ) ∧
      ¬ IsNatWt σ (Pi.single k u + σ • castW N γ) := by
  haveI := bil_nontrivial h3
  obtain ⟨m, hmk⟩ := exists_ne k
  have h2σ : 2 * σ ≠ 0 := ((bil_isUnit_two hN).mul_right_eq_zero).not.mpr hσ
  rcases hu with rfl | rfl
  · refine ⟨Pi.single k 1 + Pi.single m (-1),
      isD4Root_single_add_single hmk.symm (Or.inl rfl) (Or.inr rfl), ?_, ?_⟩
    · have hv : Pi.single k u - u • castW N (Pi.single k 1 + Pi.single m (-1)) =
          Pi.single m u := by
        funext i
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, bil_castW_single_add_single,
          Pi.single_apply]
        by_cases hik : i = k
        · subst hik
          simp [hmk.symm]
        · by_cases him : i = m
          · subst him
            simp [hmk]
          · simp [hik, him]
      rw [hv]
      exact bil_isNatWt_single (Or.inl rfl) m
    · refine bil_not_isNatWt_of_two (k := k) (m := m) hmk.symm ?_ ?_
      · have hk : ((Pi.single k u : Fin 4 → ZMod N) +
            u • castW N (Pi.single k 1 + Pi.single m (-1))) k = 2 * u := by
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, bil_castW_single_add_single,
            Pi.single_apply]
          simp [hmk.symm]
          ring
        rw [hk]
        exact h2σ
      · have hm : ((Pi.single k u : Fin 4 → ZMod N) +
            u • castW N (Pi.single k 1 + Pi.single m (-1))) m = -u := by
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, bil_castW_single_add_single,
            Pi.single_apply]
          simp [hmk]
        rw [hm]
        exact neg_ne_zero.mpr hσ
  · refine ⟨Pi.single k (-1) + Pi.single m 1,
      isD4Root_single_add_single hmk.symm (Or.inr rfl) (Or.inl rfl), ?_, ?_⟩
    · have hv : Pi.single k (-σ) - σ • castW N (Pi.single k (-1) + Pi.single m 1) =
          Pi.single m (-σ) := by
        funext i
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, bil_castW_single_add_single,
          Pi.single_apply]
        by_cases hik : i = k
        · subst hik
          simp [hmk.symm]
        · by_cases him : i = m
          · subst him
            simp [hmk]
          · simp [hik, him]
      rw [hv]
      exact bil_isNatWt_single (Or.inr rfl) m
    · refine bil_not_isNatWt_of_two (k := k) (m := m) hmk.symm ?_ ?_
      · have hk : ((Pi.single k (-σ) : Fin 4 → ZMod N) +
            σ • castW N (Pi.single k (-1) + Pi.single m 1)) k = -(2 * σ) := by
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, bil_castW_single_add_single,
            Pi.single_apply]
          simp [hmk.symm]
          ring
        rw [hk]
        exact neg_ne_zero.mpr h2σ
      · have hm : ((Pi.single k (-σ) : Fin 4 → ZMod N) +
            σ • castW N (Pi.single k (-1) + Pi.single m 1)) m = σ := by
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, bil_castW_single_add_single,
            Pi.single_apply]
          simp [hmk]
        rw [hm]
        exact hσ

theorem bil_nat_pair_step (hN : Odd N) (h3 : 3 ≤ N) {σ c : ZMod N} (hσ : σ ≠ 0) (hc : c ≠ 0)
    {CX CY : Finset (Fin 4 → ZMod N)} (hX : ∀ a, a ∈ CX ↔ IsNatWt σ a)
    (hY : ∀ a, a ∈ CY ↔ IsNatWt σ a) {a b : Fin 4 → ZMod N} (ha : a ∈ CX) (hb : b ∈ CY)
    (hab : IsNatWt c (a + b)) :
    ∃ γ : Fin 4 → ℤ, IsD4Root γ ∧ a - σ • castW N γ ∈ CX ∧ b - σ • castW N γ ∈ CY ∧
      b + σ • castW N γ ∉ CY := by
  have hanat := (hX a).mp ha
  have hbnat := (hY b).mp hb
  have hab' : a = b := bil_nat_add_nat hσ hc hanat hbnat hab
  subst hab'
  obtain ⟨k, u, hu, rfl⟩ := bil_natWt_eq hanat
  obtain ⟨γ, hγ, h1, h2⟩ := bil_nat_step_out hN h3 hσ hu (k := k)
  exact ⟨γ, hγ, (hX _).mpr h1, (hY _).mpr h1, fun h => h2 ((hY _).mp h)⟩

theorem bil_not_isSpinWt_of_three (hN : Odd N) (h3 : 3 ≤ N) {b₀ : ZMod N}
    (hb : IsUnit (2 * b₀)) {t : ℤ} (ht : t = 1 ∨ t = -1) {e : ℕ} {w : Fin 4 → ZMod N}
    {i : Fin 4} (hw : w i = (t : ZMod N) * (3 * b₀)) : ¬ IsSpinWt b₀ e w := by
  intro h
  obtain ⟨h1, h2⟩ := bil_three_mul_ne hN h3 hb
  rcases h.1 i with h' | h' <;> rw [hw] at h' <;> rcases ht with rfl | rfl <;> simp at h' <;>
    first | exact h1 h' | exact h2 h' | (apply h2; linear_combination -h') |
      (apply h1; linear_combination -h')

theorem bil_pair_step_out {j : ℕ} (hN : Odd N) (h3 : 3 ≤ N) {CX CY : Finset (Fin 4 → ZMod N)}
    (hX : NFType j CX) (hY : NFType j CY) {a b : Fin 4 → ZMod N} (ha : a ∈ CX) (hb : b ∈ CY)
    (hab : IsNatWt 1 (a + b)) :
    ∃ γ : Fin 4 → ℤ, IsD4Root γ ∧ a - (2 : ZMod N) ^ j • castW N γ ∈ CX ∧
      b + (2 : ZMod N) ^ j • castW N γ ∉ CY := by
  haveI := bil_nontrivial h3
  have hσu : IsUnit ((2 : ZMod N) ^ j) := bil_isUnit_two_pow hN j
  have hσ0 : (2 : ZMod N) ^ j ≠ 0 := hσu.ne_zero
  rcases hX with hX | ⟨b₀, e, hb₀, he, hX⟩ <;> rcases hY with hY | ⟨b₀', e', hb₀', he', hY⟩
  · obtain ⟨γ, hγ, h1, -, h3'⟩ := bil_nat_pair_step hN h3 hσ0 one_ne_zero hX hY ha hb hab
    exact ⟨γ, hγ, h1, h3'⟩
  · exact absurd hab (bil_not_natWt_add_spin
      (bil_ne_zero_of_isUnit_two_mul h3 (by rw [hb₀']; exact hσu)) ((hX a).mp ha) ((hY b).mp hb))
  · exact absurd hab (bil_not_natWt_spin_add
      (bil_ne_zero_of_isUnit_two_mul h3 (by rw [hb₀]; exact hσu)) ((hX a).mp ha) ((hY b).mp hb))
  · have hu : IsUnit (2 * b₀) := by rw [hb₀]; exact hσu
    have hbb : b₀ = b₀' := (bil_isUnit_two hN).mul_left_cancel (hb₀.trans hb₀'.symm)
    subst hbb
    obtain ⟨s, hs, rfl⟩ := bil_exists_spinW_of_isSpinWt (bil_ne_neg h3 hu) ((hX a).mp ha)
    obtain ⟨s', hs', rfl⟩ := bil_exists_spinW_of_isSpinWt (bil_ne_neg h3 hu) ((hY b).mp hb)
    obtain ⟨p, rfl⟩ := bil_spin_add_spin (bil_two_mul_ne_zero h3 hu) one_ne_zero hab
    obtain ⟨k, hkp⟩ := exists_ne p
    refine ⟨-bilSpinRoot s p k, (bil_isD4Root_spinRoot s hkp.symm).neg, ?_, ?_⟩
    · rw [castW_neg, smul_neg, sub_neg_eq_add, ← hb₀, bil_spinW_add_spinRoot b₀ s hkp.symm]
      exact (hX _).mpr ((bil_isSpinWt_spinW (bil_ne_neg h3 hu)).mpr
        (by rw [bil_card_symmDiff_pair s hkp.symm]; exact hs))
    · rw [castW_neg, smul_neg, ← sub_eq_add_neg, ← hb₀]
      intro hmem
      exact bil_not_isSpinWt_of_three hN h3 hu (bil_spinSg_eq s p)
        (bil_spinW_compl_sub_spinRoot_apply b₀ s hkp.symm) ((hY _).mp hmem)

theorem bil_spin_spin_parity (hN : Odd N) (h3 : 3 ≤ N) {b₀ b₀' : ZMod N} {e e' : ℕ}
    (hb₀ : 2 * b₀ = 1) (hb₀' : 2 * b₀' = 1) (he : e < 2) (he' : e' < 2)
    {a b : Fin 4 → ZMod N} (ha : IsSpinWt b₀ e a) (hb : IsSpinWt b₀' e' b)
    (hab : IsNatWt 1 (a + b)) : b₀' = b₀ ∧ e' = 1 - e := by
  haveI := bil_nontrivial h3
  have hu : IsUnit (2 * b₀) := by rw [hb₀]; exact isUnit_one
  have hbb : b₀' = b₀ := (bil_isUnit_two hN).mul_left_cancel (hb₀'.trans hb₀.symm)
  subst hbb
  obtain ⟨s, hs, rfl⟩ := bil_exists_spinW_of_isSpinWt (bil_ne_neg h3 hu) ha
  obtain ⟨s', hs', rfl⟩ := bil_exists_spinW_of_isSpinWt (bil_ne_neg h3 hu) hb
  obtain ⟨p, rfl⟩ := bil_spin_add_spin (bil_two_mul_ne_zero h3 hu) one_ne_zero hab
  refine ⟨rfl, ?_⟩
  have := bil_card_compl_symmDiff_single s p
  omega

theorem bil_conn {R : Type*} [AddCommGroup R] (hN : Odd N) (h3 : 3 ≤ N) {b₀ : ZMod N}
    (hb₀ : 2 * b₀ = 1) {e e' : ℕ} (he : e' % 2 = (e + 1) % 2)
    {CX CY CV : Finset (Fin 4 → ZMod N)} (hX : ∀ a, a ∈ CX ↔ IsSpinWt b₀ e a)
    (hY : ∀ a, a ∈ CY ↔ IsSpinWt b₀ e' a) (hV : ∀ a, a ∈ CV ↔ IsNatWt 1 a)
    (l : (Fin 4 → ZMod N) → (Fin 4 → ZMod N) → R)
    (hE : ∀ a ∈ CX, ∀ b ∈ CY, ∀ γ : Fin 4 → ℤ, IsD4Root γ → a + b ∈ CV →
      a + b + castW N γ ∈ CV →
      (if a + castW N γ ∈ CX then l (a + castW N γ) b else 0) +
        (if b + castW N γ ∈ CY then l a (b + castW N γ) else 0) = l a b)
    {a b a' b' : Fin 4 → ZMod N} (ha : a ∈ CX) (hb : b ∈ CY) (hab : a + b ∈ CV)
    (ha' : a' ∈ CX) (hb' : b' ∈ CY) (hab' : a' + b' ∈ CV) : l a b = l a' b' := by
  haveI := bil_nontrivial h3
  have hu : IsUnit (2 * b₀) := by rw [hb₀]; exact isUnit_one
  have hne := bil_ne_neg h3 hu
  have h2ne := bil_two_mul_ne_zero h3 hu
  have hshift : ∀ x : Fin 4 → ZMod N, (2 * b₀) • x = x := by
    intro x
    rw [hb₀, one_smul]
  have hXs : ∀ s : Finset (Fin 4), bilSpinW b₀ s ∈ CX ↔ s.card % 2 = e % 2 :=
    fun s => (hX _).trans (bil_isSpinWt_spinW hne)
  have hYs : ∀ s : Finset (Fin 4), bilSpinW b₀ s ∈ CY ↔ s.card % 2 = e' % 2 :=
    fun s => (hY _).trans (bil_isSpinWt_spinW hne)
  have hVsg : ∀ (i : Fin 4) (t : ℤ), (t = 1 ∨ t = -1) →
      (Pi.single i (2 * b₀ * (t : ZMod N)) : Fin 4 → ZMod N) ∈ CV ∧
      (Pi.single i (-(2 * b₀ * (t : ZMod N))) : Fin 4 → ZMod N) ∈ CV := by
    intro i t ht
    rcases ht with rfl | rfl
    · refine ⟨(hV _).mpr (bil_isNatWt_single ?_ i), (hV _).mpr (bil_isNatWt_single ?_ i)⟩ <;>
        simp [hb₀]
    · refine ⟨(hV _).mpr (bil_isNatWt_single ?_ i), (hV _).mpr (bil_isNatWt_single ?_ i)⟩ <;>
        simp [hb₀]
  let F : Finset (Fin 4) → Fin 4 → R := fun s p => l (bilSpinW b₀ s) (bilSpinW b₀ ((s ∆ {p})ᶜ))
  have hM1 : ∀ s p k, s.card % 2 = e % 2 → p ≠ k → F s p = F (s ∆ {p, k}) k := by
    intro s p k hs hpk
    have hsx : bilSpinW b₀ s ∈ CX := (hXs s).mpr hs
    have hsy : bilSpinW b₀ ((s ∆ {p})ᶜ) ∈ CY :=
      (hYs _).mpr (by rw [bil_card_compl_symmDiff_single]; omega)
    have hsum : bilSpinW b₀ s + bilSpinW b₀ ((s ∆ {p})ᶜ) ∈ CV := by
      rw [bil_spinW_add_spinW_compl]
      exact (hVsg p _ (bil_spinSg_eq s p)).1
    have hsum' : bilSpinW b₀ s + bilSpinW b₀ ((s ∆ {p})ᶜ) + castW N (bilSpinRoot s p k) ∈ CV := by
      rw [← hshift (castW N (bilSpinRoot s p k)), bil_spinW_add_spinW_compl_add_spinRoot b₀ s hpk]
      exact (hVsg k _ (bil_spinSg_eq s k)).2
    have key := hE _ hsx _ hsy (bilSpinRoot s p k) (bil_isD4Root_spinRoot s hpk) hsum hsum'
    have hA : bilSpinW b₀ s + castW N (bilSpinRoot s p k) = bilSpinW b₀ (s ∆ {p, k}) := by
      rw [← hshift (castW N (bilSpinRoot s p k))]
      exact bil_spinW_add_spinRoot b₀ s hpk
    have hAmem : bilSpinW b₀ (s ∆ {p, k}) ∈ CX :=
      (hXs _).mpr (by rw [bil_card_symmDiff_pair s hpk]; exact hs)
    have hBnot : bilSpinW b₀ ((s ∆ {p})ᶜ) + castW N (bilSpinRoot s p k) ∉ CY := by
      intro hmem
      refine bil_not_isSpinWt_of_three hN h3 hu (t := -bilSpinSg s k)
        (by rcases bil_spinSg_eq s k with h | h <;> simp [h]) (i := k) ?_ ((hY _).mp hmem)
      rw [← hshift (castW N (bilSpinRoot s p k)), bil_spinW_compl_add_spinRoot_apply b₀ s hpk]
      push_cast
      ring
    rw [hA, if_pos hAmem, if_neg hBnot, add_zero] at key
    show l (bilSpinW b₀ s) (bilSpinW b₀ ((s ∆ {p})ᶜ)) =
      l (bilSpinW b₀ (s ∆ {p, k})) (bilSpinW b₀ ((s ∆ {p, k} ∆ {k})ᶜ))
    rw [bil_symmDiff_pair_single s hpk]
    exact key.symm
  have hM2' : ∀ t p k, t.card % 2 = e' % 2 → p ≠ k →
      l (bilSpinW b₀ ((t ∆ {p})ᶜ)) (bilSpinW b₀ t) =
        l (bilSpinW b₀ ((t ∆ {p})ᶜ)) (bilSpinW b₀ (t ∆ {p, k})) := by
    intro t p k ht hpk
    have hx : bilSpinW b₀ t ∈ CY := (hYs t).mpr ht
    have hy : bilSpinW b₀ ((t ∆ {p})ᶜ) ∈ CX :=
      (hXs _).mpr (by rw [bil_card_compl_symmDiff_single]; omega)
    have hsum : bilSpinW b₀ ((t ∆ {p})ᶜ) + bilSpinW b₀ t ∈ CV := by
      rw [add_comm, bil_spinW_add_spinW_compl]
      exact (hVsg p _ (bil_spinSg_eq t p)).1
    have hsum' : bilSpinW b₀ ((t ∆ {p})ᶜ) + bilSpinW b₀ t + castW N (bilSpinRoot t p k) ∈ CV := by
      rw [add_comm (bilSpinW b₀ ((t ∆ {p})ᶜ)), ← hshift (castW N (bilSpinRoot t p k)),
        bil_spinW_add_spinW_compl_add_spinRoot b₀ t hpk]
      exact (hVsg k _ (bil_spinSg_eq t k)).2
    have key := hE _ hy _ hx (bilSpinRoot t p k) (bil_isD4Root_spinRoot t hpk) hsum hsum'
    have hB : bilSpinW b₀ t + castW N (bilSpinRoot t p k) = bilSpinW b₀ (t ∆ {p, k}) := by
      rw [← hshift (castW N (bilSpinRoot t p k))]
      exact bil_spinW_add_spinRoot b₀ t hpk
    have hBmem : bilSpinW b₀ (t ∆ {p, k}) ∈ CY :=
      (hYs _).mpr (by rw [bil_card_symmDiff_pair t hpk]; exact ht)
    have hAnot : bilSpinW b₀ ((t ∆ {p})ᶜ) + castW N (bilSpinRoot t p k) ∉ CX := by
      intro hmem
      refine bil_not_isSpinWt_of_three hN h3 hu (t := -bilSpinSg t k)
        (by rcases bil_spinSg_eq t k with h | h <;> simp [h]) (i := k) ?_ ((hX _).mp hmem)
      rw [← hshift (castW N (bilSpinRoot t p k)), bil_spinW_compl_add_spinRoot_apply b₀ t hpk]
      push_cast
      ring
    rw [hB, if_neg hAnot, if_pos hBmem, zero_add] at key
    exact key.symm
  have hM2 : ∀ s p k, s.card % 2 = e % 2 → p ≠ k → F s p = F s k := by
    intro s p k hs hpk
    have htcard : ((s ∆ {p})ᶜ).card % 2 = e' % 2 := by
      rw [bil_card_compl_symmDiff_single]
      omega
    have := hM2' ((s ∆ {p})ᶜ) p k htcard hpk
    rw [bil_compl_symmDiff_compl_symmDiff, bil_compl_symmDiff_pair s hpk] at this
    exact this.symm.symm
  obtain ⟨s, hs, rfl⟩ := bil_exists_spinW_of_isSpinWt hne ((hX a).mp ha)
  obtain ⟨t, ht, rfl⟩ := bil_exists_spinW_of_isSpinWt hne ((hY b).mp hb)
  obtain ⟨p, rfl⟩ := bil_spin_add_spin h2ne one_ne_zero ((hV _).mp hab)
  obtain ⟨s2, hs2, rfl⟩ := bil_exists_spinW_of_isSpinWt hne ((hX a').mp ha')
  obtain ⟨t2, ht2, rfl⟩ := bil_exists_spinW_of_isSpinWt hne ((hY b').mp hb')
  obtain ⟨p2, rfl⟩ := bil_spin_add_spin h2ne one_ne_zero ((hV _).mp hab')
  exact bil_conn_aux F (r := e % 2) hM2 hM1 hs hs2 p p2

end CFSG.RankThree.GF2n.Stroth80.Tri

end
