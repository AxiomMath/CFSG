module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86TutteCalcChain
public import CFSG.Quasithin.Recognition.GoldschmidtFan86TutteCalcDefs

public section

namespace CFSG.Quasithin.Fan86.Tutte

variable {H : Type*} [Group H] {s : ℕ} {r l ξ : H} {Hs : ℕ → Subgroup H}

theorem tx_int_mem (h : IsTutteSys s r l ξ Hs) {c : ℕ} (hc : c ≤ s) {t : ℤ} (ht1 : 1 ≤ t)
    (htc : t ≤ c) : tx r l t ∈ Hs c := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ t)
  exact tx_mem_of_le h (by omega) hc

theorem tx_zpow_not_mem (h : IsTutteSys s r l ξ Hs) {n : ℕ} (hn : 1 ≤ n) (hns : n ≤ s) {e : ℤ}
    (he : e = 1 ∨ e = -1) : tx r l n ^ e ∉ Hs (n - 1) := by
  have hxn := h.x_not_mem n hn hns
  rcases he with rfl | rfl
  · simpa using hxn
  · intro hmem
    apply hxn
    simpa using (Hs (n - 1)).inv_mem hmem

theorem nfw_mem (h : IsTutteSys s r l ξ Hs) {c : ℕ} (hc : c ≤ s) (e : ℤ) {L : List ℤ}
    (hL : ∀ t ∈ L, 1 ≤ t ∧ t ≤ c) : nfw r l e L ∈ Hs c := by
  induction L generalizing e with
  | nil => exact (Hs c).one_mem
  | cons t L ih =>
    have ht := hL t List.mem_cons_self
    exact (Hs c).mul_mem (zpow_mem (tx_int_mem h hc ht.1 ht.2) e)
      (ih (-e) fun u hu => hL u (List.mem_cons_of_mem _ hu))

theorem nfw_head (h : IsTutteSys s r l ξ Hs) {n : ℕ} (hn1 : 1 ≤ n) (hns : n < s) (e : ℤ)
    (he : e = 1 ∨ e = -1) {L : List ℤ} (hL : ∀ t ∈ L, 1 ≤ t ∧ t < n) :
    nfw r l e ((n : ℤ) :: L) ∈ Hs n ∧ nfw r l e ((n : ℤ) :: L) ∉ Hs (n - 1) := by
  have hw : nfw r l (-e) L ∈ Hs (n - 1) :=
    nfw_mem h (by omega) (-e) fun t ht => ⟨(hL t ht).1, by have := (hL t ht).2; omega⟩
  have hw' : nfw r l (-e) L ∈ Hs n := Hs_mono h (by omega) hns.le hw
  constructor
  · exact (Hs n).mul_mem (zpow_mem (h.x_mem n hns.le) e) hw'
  · intro hmem
    apply tx_zpow_not_mem h hn1 hns.le he
    have := (Hs (n - 1)).mul_mem hmem ((Hs (n - 1)).inv_mem hw)
    simpa [nfw] using this

theorem nf_exists (h : IsTutteSys s r l ξ Hs) {k : ℕ} (hks : k < s) (e : ℤ)
    (he : e = 1 ∨ e = -1) {g : H} (hg : g ∈ Hs k) :
    ∃ L : List ℤ, L.Pairwise (· > ·) ∧ (∀ t ∈ L, 1 ≤ t ∧ t ≤ k) ∧ nfw r l e L = g := by
  induction k generalizing e g with
  | zero =>
    have hg1 : g = 1 := by simpa [h.zero] using hg
    exact ⟨[], List.Pairwise.nil, by simp, by simp [nfw, hg1]⟩
  | succ k ih =>
    by_cases hgk : g ∈ Hs k
    · obtain ⟨L, h1, h2, h3⟩ := ih (by omega) e he hgk
      exact ⟨L, h1, fun t ht => ⟨(h2 t ht).1, by have := (h2 t ht).2; push_cast; omega⟩, h3⟩
    · have hx : tx r l ((k + 1 : ℕ) : ℤ) ∈ Hs (k + 1) := h.x_mem (k + 1) hks.le
      have hxn : tx r l ((k + 1 : ℕ) : ℤ) ∉ Hs k := by
        simpa using h.x_not_mem (k + 1) (by omega) hks.le
      have hy : tx r l ((k + 1 : ℕ) : ℤ) ^ e ∈ Hs (k + 1) := zpow_mem hx e
      have hyn : tx r l ((k + 1 : ℕ) : ℤ) ^ e ∉ Hs k := by
        simpa using tx_zpow_not_mem h (n := k + 1) (by omega) hks.le he
      have hz := inv_mul_mem_of_not_mem h hks hy (hg) hyn hgk
      have he' : -e = 1 ∨ -e = -1 := by rcases he with rfl | rfl <;> simp
      obtain ⟨L', h1, h2, h3⟩ := ih (by omega) (-e) he' hz
      refine ⟨((k + 1 : ℕ) : ℤ) :: L', ?_, ?_, ?_⟩
      · rw [List.pairwise_cons]
        refine ⟨fun a ha => ?_, h1⟩
        have := (h2 a ha).2
        push_cast
        omega
      · intro t ht
        rcases List.mem_cons.mp ht with rfl | ht
        · push_cast
          omega
        · have := h2 t ht
          push_cast
          omega
      · simp only [nfw, h3]
        simp

theorem nf_unique (h : IsTutteSys s r l ξ Hs) (e : ℤ) (he : e = 1 ∨ e = -1) {L L' : List ℤ}
    (hL : L.Pairwise (· > ·)) (hL' : L'.Pairwise (· > ·))
    (h1 : ∀ t ∈ L, 1 ≤ t ∧ t < s) (h2 : ∀ t ∈ L', 1 ≤ t ∧ t < s)
    (heq : nfw r l e L = nfw r l e L') : L = L' := by
  have key : ∀ (L L' : List ℤ) (e : ℤ), (e = 1 ∨ e = -1) → L.Pairwise (· > ·) →
      L'.Pairwise (· > ·) → (∀ t ∈ L, 1 ≤ t ∧ t < s) → (∀ t ∈ L', 1 ≤ t ∧ t < s) →
      nfw r l e L = nfw r l e L' → L = L' := by
    intro L
    induction L with
    | nil =>
      intro L' e he _ hL' _ h2 heq
      cases L' with
      | nil => rfl
      | cons t' L₀' =>
        exfalso
        have ht' := h2 t' List.mem_cons_self
        obtain ⟨n', rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ t')
        have hp' := List.pairwise_cons.mp hL'
        have K' := nfw_head h (n := n') (by omega) (by omega) e he (L := L₀') fun u hu =>
          ⟨(h2 u (List.mem_cons_of_mem _ hu)).1, hp'.1 u hu⟩
        apply K'.2
        rw [← heq]
        exact (Hs _).one_mem
    | cons t L₀ ih =>
      intro L' e he hL hL' h1 h2 heq
      have ht := h1 t List.mem_cons_self
      obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ t)
      have hp := List.pairwise_cons.mp hL
      have K := nfw_head h (n := n) (by omega) (by omega) e he (L := L₀) fun u hu =>
        ⟨(h1 u (List.mem_cons_of_mem _ hu)).1, hp.1 u hu⟩
      cases L' with
      | nil =>
        exfalso
        apply K.2
        rw [heq]
        exact (Hs _).one_mem
      | cons t' L₀' =>
        have ht' := h2 t' List.mem_cons_self
        obtain ⟨n', rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ t')
        have hp' := List.pairwise_cons.mp hL'
        have K' := nfw_head h (n := n') (by omega) (by omega) e he (L := L₀') fun u hu =>
          ⟨(h2 u (List.mem_cons_of_mem _ hu)).1, hp'.1 u hu⟩
        rcases lt_trichotomy n n' with hlt | rfl | hgt
        · exfalso
          apply K'.2
          rw [← heq]
          exact Hs_mono h (by omega) (by omega) K.1
        · have hxe : tx r l (n : ℤ) ^ e * nfw r l (-e) L₀ = tx r l (n : ℤ) ^ e * nfw r l (-e) L₀' :=
            heq
          have he' : -e = 1 ∨ -e = -1 := by rcases he with rfl | rfl <;> simp
          rw [ih L₀' (-e) he' hp.2 hp'.2 (fun u hu => h1 u (List.mem_cons_of_mem _ hu))
            (fun u hu => h2 u (List.mem_cons_of_mem _ hu)) (mul_left_cancel hxe)]
        · exfalso
          apply K.2
          rw [heq]
          exact Hs_mono h (by omega) (by omega) K'.1
  exact key L L' e he hL hL' h1 h2 heq

end CFSG.Quasithin.Fan86.Tutte
