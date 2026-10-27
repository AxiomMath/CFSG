module

public import CFSG.HardMathSupport.U4FF.ClassComb

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6.McClurg

open CFSG.HardMathSupport.U4FF

theorem sixteen_mul_add_two_pow_lt_four_pow (k : ℕ) (hk : 3 ≤ k) : 16 * k + 2 ^ k < 4 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    rw [pow_succ, pow_succ]
    have h2k : 0 ≤ 2 ^ k := Nat.zero_le _
    nlinarith [ih, hk]

private lemma locM_pair_sub_eq_thirtytwo (x y x' y' : Bool)
    (h : locM x y x * locM x' y' x' - locF1 x y x * locF1 x' y' x' = 32) :
    x = false ∧ y = true ∧ x' = false ∧ y' = true := by
  cases x <;> cases y <;> cases x' <;> cases y' <;> revert h <;> decide

theorem lbl_cases {n : ℕ} [NeZero n] (hn : 2 ≤ n) (l : Lbl n) (hl : ¬ l.IsZero) {d : ℕ}
    (hd : 0 < d) (hinv : l.RotInv d) (hN : ¬ l.SingleN) (hO : ¬ l.SingleO)
    (hrk : d * l.rk1 ≤ 6 * n + 4) :
    (d = n ∧ ∃ i₀ : Fin n, (∀ i, i ≠ i₀ → l.ZeroAt i) ∧
      l.a i₀ = true ∧ l.b i₀ = false ∧ l.c i₀ = true) ∨
    (n = 2 ∧ d = 1 ∧ ∀ i, l.a i = false ∧ l.b i = true ∧ l.c i = false) := by
  classical
  obtain ⟨P, hPmem⟩ : ∃ P : Finset (Fin n), ∀ i, i ∈ P ↔ ¬ l.ZeroAt i :=
    ⟨Finset.univ.filter (fun i => ¬ l.ZeroAt i), fun i => by simp⟩
  obtain ⟨i₁, hi₁⟩ : ∃ i, ¬ l.ZeroAt i := by
    by_contra h
    push Not at h
    exact hl h
  have hk : 0 < P.card := Finset.card_pos.2 ⟨i₁, (hPmem i₁).2 hi₁⟩
  obtain ⟨y, hy0, hyk, hydvd⟩ := exists_orbit_card P i₁
    (fun t => (hPmem _).2 (Lbl.orbit_nz l hinv i₁ hi₁ t))
  have hyle : n ≤ y * d := Nat.le_of_dvd (Nat.mul_pos hy0 hd) hydvd
  rcases (show P.card = 1 ∨ P.card = 2 ∨ 3 ≤ P.card by omega) with h1 | h2 | h3
  ·
    obtain ⟨i₀, hP1⟩ := Finset.card_eq_one.1 h1
    have hmem : ∀ i, i ∈ P ↔ i = i₀ := fun i => by rw [hP1, Finset.mem_singleton]
    have hz : ∀ i, i ≠ i₀ → l.ZeroAt i := fun i hne => by
      by_contra h
      exact hne ((hmem i).1 ((hPmem i).2 h))
    have hnz : ¬ l.ZeroAt i₀ := (hPmem i₀).1 ((hmem i₀).2 rfl)
    have hdvd : n ∣ d := by
      rw [show y = 1 by omega, one_mul] at hydvd
      exact hydvd
    have hdim : l.dim = locM (l.a i₀) (l.b i₀) (l.c i₀) := by
      unfold Lbl.dim
      apply Finset.prod_eq_single i₀
      · intro i _ hi
        obtain ⟨h1, h2, h3⟩ := hz i hi
        rw [h1, h2, h3]
        decide
      · intro h'
        exact absurd (Finset.mem_univ i₀) h'
    have hfix : l.fix1 = locF1 (l.a i₀) (l.b i₀) (l.c i₀) := by
      unfold Lbl.fix1
      apply Finset.prod_eq_single i₀
      · intro i _ hi
        obtain ⟨h1, h2, h3⟩ := hz i hi
        rw [h1, h2, h3]
        decide
      · intro h'
        exact absurd (Finset.mem_univ i₀) h'
    obtain ⟨x, hx⟩ : ∃ x, l.a i₀ = x := ⟨_, rfl⟩
    obtain ⟨b, hb⟩ : ∃ b, l.b i₀ = b := ⟨_, rfl⟩
    obtain ⟨c, hc⟩ : ∃ c, l.c i₀ = c := ⟨_, rfl⟩
    rw [hx, hb, hc] at hdim hfix
    cases x <;> cases b <;> cases c
    · exact absurd (by unfold Lbl.ZeroAt; exact ⟨hx, hb, hc⟩) hnz
    · exact absurd ⟨i₀, hz, hb, Or.inr ⟨hx, hc⟩⟩ hN
    · exact absurd ⟨i₀, hz, hx, hb, hc⟩ hO
    · exfalso
      have h9 : l.rk1 = 9 := by
        unfold Lbl.rk1
        rw [hdim, hfix] <;> decide
      have hle : n ≤ d := Nat.le_of_dvd hd hdvd
      rw [h9] at hrk
      omega
    · exact absurd ⟨i₀, hz, hb, Or.inl ⟨hx, hc⟩⟩ hN
    · left
      have h6 : l.rk1 = 6 := by
        unfold Lbl.rk1
        rw [hdim, hfix] <;> decide
      have hdn : d = n := by
        by_contra hne
        obtain ⟨q, hq⟩ := hdvd
        have hq2 : 2 ≤ q := by
          rcases q with _ | _ | q
          · simp at hq
            omega
          · simp at hq
            exact absurd hq hne
          · omega
        have h2n : 2 * n ≤ d := by
          rw [hq]
          calc 2 * n = n * 2 := by ring
            _ ≤ n * q := Nat.mul_le_mul_left n hq2
        have h12 : 12 * n ≤ d * 6 := by
          have h := Nat.mul_le_mul_right 6 h2n
          calc 12 * n = 2 * n * 6 := by ring
            _ ≤ d * 6 := h
        rw [h6] at hrk
        omega
      exact ⟨hdn, i₀, hz, hx, hb, hc⟩
    · exfalso
      have h9 : l.rk1 = 9 := by
        unfold Lbl.rk1
        rw [hdim, hfix] <;> decide
      have hle : n ≤ d := Nat.le_of_dvd hd hdvd
      rw [h9] at hrk
      omega
    · exfalso
      have h32 : l.rk1 = 32 := by
        unfold Lbl.rk1
        rw [hdim, hfix] <;> decide
      have hle : n ≤ d := Nat.le_of_dvd hd hdvd
      rw [h32] at hrk
      omega
  ·
    obtain ⟨i₀, i₁, hne, hP2⟩ := Finset.card_eq_two.1 h2
    have hz : ∀ i, i ≠ i₀ → i ≠ i₁ → l.ZeroAt i := by
      intro i h0 h1
      by_contra h
      have hi : i ∈ P := (hPmem i).2 h
      rw [hP2] at hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      exact hi.elim h0 h1
    have hnz0 : ¬ l.ZeroAt i₀ := (hPmem i₀).1 (by rw [hP2]; simp)
    have hnz1 : ¬ l.ZeroAt i₁ := (hPmem i₁).1 (by rw [hP2]; simp)
    have hzero : ∀ i, i ∉ ({i₀, i₁} : Finset (Fin n)) →
        locM (l.a i) (l.b i) (l.c i) = 1 := by
      intro i hi
      have h0 : i ≠ i₀ := fun h => hi (by rw [h]; simp)
      have h1 : i ≠ i₁ := fun h => hi (by rw [h]; simp)
      obtain ⟨ha, hb, hc⟩ := hz i h0 h1
      rw [ha, hb, hc]
      decide
    have hdim : l.dim = locM (l.a i₀) (l.b i₀) (l.c i₀) *
        locM (l.a i₁) (l.b i₁) (l.c i₁) := by
      unfold Lbl.dim
      have hmain := Finset.prod_subset (s₁ := ({i₀, i₁} : Finset (Fin n)))
        (s₂ := (Finset.univ : Finset (Fin n))) (Finset.subset_univ _)
        (fun i _ hi => hzero i hi)
      rw [← hmain, Finset.prod_pair hne]
    have hfix : l.fix1 = locF1 (l.a i₀) (l.b i₀) (l.c i₀) *
        locF1 (l.a i₁) (l.b i₁) (l.c i₁) := by
      unfold Lbl.fix1
      have hzero' : ∀ i, i ∉ ({i₀, i₁} : Finset (Fin n)) →
          locF1 (l.a i) (l.b i) (l.c i) = 1 := by
        intro i hi
        have h0 : i ≠ i₀ := fun h => hi (by rw [h]; simp)
        have h1 : i ≠ i₁ := fun h => hi (by rw [h]; simp)
        obtain ⟨ha, hb, hc⟩ := hz i h0 h1
        rw [ha, hb, hc]
        decide
      have hmain := Finset.prod_subset (s₁ := ({i₀, i₁} : Finset (Fin n)))
        (s₂ := (Finset.univ : Finset (Fin n))) (Finset.subset_univ _)
        (fun i _ hi => hzero' i hi)
      rw [← hmain, Finset.prod_pair hne]
    by_cases hnd : n ∣ d
    ·
      exfalso
      obtain ⟨q, hq⟩ := hnd
      rcases q with _ | _ | q
      · omega
      · have hdn : d = n := by omega
        have hinv' : l.RotInv n := hdn ▸ hinv
        have hper : ∀ j : ℕ, l.bitA (j + n) = l.bitA j := fun j => (hinv' j).1
        have hac : ∀ i, l.a i = l.c i := by
          intro i
          rw [← l.bitA_lo i, ← l.bitA_hi i]
          exact (hper i.val).symm
        have h6a : 6 ≤ locM (l.a i₀) (l.b i₀) (l.a i₀) := by
          apply locM_ge_six
          · rfl
          · intro h
            exact hnz0 ⟨h.1, h.2.1, (hac i₀).symm.trans h.2.2⟩
        have h6b : 6 ≤ locM (l.a i₁) (l.b i₁) (l.a i₁) := by
          apply locM_ge_six
          · rfl
          · intro h
            exact hnz1 ⟨h.1, h.2.1, (hac i₁).symm.trans h.2.2⟩
        rw [← hac i₀, ← hac i₁] at hdim hfix
        have hD : 36 ≤ l.dim := by
          rw [hdim]
          calc 36 = 6 * 6 := by norm_num
            _ ≤ _ := Nat.mul_le_mul h6a h6b
        have hF : l.fix1 ≤ 4 := by
          rw [hfix]
          calc _ ≤ 2 * 2 :=
                Nat.mul_le_mul (locF1_le_two _ _ _) (locF1_le_two _ _ _)
            _ = 4 := by norm_num
        have hge : 16 ≤ l.rk1 := by
          have h2rk := Lbl.two_mul_rk1 l
          omega
        have h16 : 16 * n ≤ d * l.rk1 := by
          rw [hdn]
          calc 16 * n = n * 16 := by ring
            _ ≤ n * l.rk1 := Nat.mul_le_mul_left n hge
        omega
      · have h2n : 2 * n ≤ d := by
          rw [hq]
          calc 2 * n = n * 2 := by ring
            _ ≤ n * (q + 2) := Nat.mul_le_mul_left n (by omega)
        have hD : 16 ≤ l.dim := by
          have h := Lbl.dim_ge_pow l P hPmem 4
            (fun i hi => locM_ge_four _ _ _ ((hPmem i).1 hi))
          rw [h2] at h
          norm_num at h
          exact h
        have hF : l.fix1 ≤ 4 := by
          have h := Lbl.fix1_le_pow l P hPmem 2 (fun i _ => locF1_le_two _ _ _)
          rw [h2] at h
          norm_num at h
          exact h
        have hge : 6 ≤ l.rk1 := by
          have h2rk := Lbl.two_mul_rk1 l
          omega
        have h6d : 6 * d ≤ d * l.rk1 := by
          rw [Nat.mul_comm 6 d]
          exact Nat.mul_le_mul_left d hge
        have h12 : 12 * n ≤ d * l.rk1 := by
          calc 12 * n = 6 * (2 * n) := by ring
            _ ≤ 6 * d := Nat.mul_le_mul_left 6 h2n
            _ ≤ d * l.rk1 := h6d
        omega
    ·
      have hy2 : y = 2 := by
        rcases (show y = 1 ∨ y = 2 by omega) with e | e
        · exfalso
          apply hnd
          rwa [e, one_mul] at hydvd
        · exact e
      have h2dvd : n ∣ 2 * d := by
        rw [hy2] at hydvd
        exact hydvd
      have hnd2 : n ≤ 2 * d := Nat.le_of_dvd (by omega) h2dvd
      have hac : ∀ i, l.a i = l.c i := Lbl.a_eq_c_of_two_mul l hinv h2dvd hnd
      have h6a : 6 ≤ locM (l.a i₀) (l.b i₀) (l.a i₀) := by
        apply locM_ge_six
        · rfl
        · intro h
          exact hnz0 ⟨h.1, h.2.1, (hac i₀).symm.trans h.2.2⟩
      have h6b : 6 ≤ locM (l.a i₁) (l.b i₁) (l.a i₁) := by
        apply locM_ge_six
        · rfl
        · intro h
          exact hnz1 ⟨h.1, h.2.1, (hac i₁).symm.trans h.2.2⟩
      rw [← hac i₀, ← hac i₁] at hdim hfix
      have hD : 36 ≤ l.dim := by
        rw [hdim]
        calc 36 = 6 * 6 := by norm_num
          _ ≤ _ := Nat.mul_le_mul h6a h6b
      have hF : l.fix1 ≤ 4 := by
        rw [hfix]
        calc _ ≤ 2 * 2 :=
              Nat.mul_le_mul (locF1_le_two _ _ _) (locF1_le_two _ _ _)
          _ = 4 := by norm_num
      have hge16 : 16 ≤ l.rk1 := by
        have h2rk := Lbl.two_mul_rk1 l
        omega
      have hd1 : d = 1 := by
        have h16d : 16 * d ≤ d * l.rk1 := by
          rw [Nat.mul_comm 16 d]
          exact Nat.mul_le_mul_left d hge16
        omega
      have hn2 : n = 2 := by omega
      have hle16 : l.rk1 ≤ 16 := by
        rw [hd1] at hrk
        omega
      have hrk16 : l.rk1 = 16 := le_antisymm hle16 hge16
      have h32 : l.dim - l.fix1 = 32 := by
        have h2rk := Lbl.two_mul_rk1 l
        omega
      have hPuniv : ({i₀, i₁} : Finset (Fin n)) = Finset.univ := by
        apply Finset.eq_univ_of_card
        rw [Finset.card_pair hne, Fintype.card_fin, hn2]
      obtain ⟨x, hx⟩ : ∃ x, l.a i₀ = x := ⟨_, rfl⟩
      obtain ⟨b, hb⟩ : ∃ b, l.b i₀ = b := ⟨_, rfl⟩
      obtain ⟨x', hx'⟩ : ∃ x', l.a i₁ = x' := ⟨_, rfl⟩
      obtain ⟨b', hb'⟩ : ∃ b', l.b i₁ = b' := ⟨_, rfl⟩
      have hdim' : l.dim = locM x b x * locM x' b' x' := by
        rw [hdim, hx, hb, hx', hb']
      have hfix' : l.fix1 = locF1 x b x * locF1 x' b' x' := by
        rw [hfix, hx, hb, hx', hb']
      have hbools := locM_pair_sub_eq_thirtytwo x b x' b'
        (by rw [← hdim', ← hfix']; exact h32)
      obtain ⟨hxf, hbt, hx'f, hb't⟩ := hbools
      right
      refine ⟨hn2, hd1, fun i => ?_⟩
      have hi : i ∈ ({i₀, i₁} : Finset (Fin n)) := by
        rw [hPuniv]
        exact Finset.mem_univ i
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with h0 | h1
      · rw [h0]
        exact ⟨by rw [hx, hxf], by rw [hb, hbt], by rw [← hac i₀, hx, hxf]⟩
      · rw [h1]
        exact ⟨by rw [hx', hx'f], by rw [hb', hb't], by rw [← hac i₁, hx', hx'f]⟩
  ·
    have hD : 4 ^ P.card ≤ l.dim :=
      Lbl.dim_ge_pow l P hPmem 4 (fun i hi => locM_ge_four _ _ _ ((hPmem i).1 hi))
    have hF : l.fix1 ≤ 2 ^ P.card :=
      Lbl.fix1_le_pow l P hPmem 2 (fun i _ => locF1_le_two _ _ _)
    have hbnd : 12 * P.card + 2 ^ P.card ≤ 4 ^ P.card := four_pow_ge P.card h3
    have hrkP : 6 * P.card ≤ l.rk1 := by
      have h2rk := Lbl.two_mul_rk1 l
      generalize 4 ^ P.card = A at hD hbnd
      generalize 2 ^ P.card = B at hF hbnd
      omega
    have hyle' : n ≤ P.card * d := le_trans hyle (Nat.mul_le_mul_right d hyk)
    have hstep1 : n * l.rk1 ≤ (P.card * d) * l.rk1 := Nat.mul_le_mul_right l.rk1 hyle'
    have hstep2 : (P.card * d) * l.rk1 ≤ P.card * (6 * n + 4) := by
      rw [mul_assoc]
      exact Nat.mul_le_mul_left P.card hrk
    have h1 : n * (4 ^ P.card - 2 ^ P.card) ≤ 2 * P.card * (6 * n + 4) := by
      have hdiff : 4 ^ P.card - 2 ^ P.card ≤ 2 * l.rk1 := by
        have h2rk := Lbl.two_mul_rk1 l
        calc 4 ^ P.card - 2 ^ P.card ≤ l.dim - 2 ^ P.card :=
              Nat.sub_le_sub_right hD _
          _ ≤ l.dim - l.fix1 := Nat.sub_le_sub_left hF _
          _ = 2 * l.rk1 := h2rk.symm
      calc n * (4 ^ P.card - 2 ^ P.card) ≤ n * (2 * l.rk1) :=
            Nat.mul_le_mul_left n hdiff
        _ = 2 * (n * l.rk1) := by ring
        _ ≤ 2 * (P.card * (6 * n + 4)) :=
            Nat.mul_le_mul_left 2 (le_trans hstep1 hstep2)
        _ = 2 * P.card * (6 * n + 4) := by ring
    have h2 : 2 * P.card * (6 * n + 4) ≤ 16 * P.card * n := by
      have hle : 12 * n + 8 ≤ 16 * n := by omega
      calc 2 * P.card * (6 * n + 4) = P.card * (12 * n + 8) := by ring
        _ ≤ P.card * (16 * n) := Nat.mul_le_mul_left P.card hle
        _ = 16 * P.card * n := by ring
    have hmul : n * (4 ^ P.card - 2 ^ P.card) ≤ n * (16 * P.card) := by
      calc n * (4 ^ P.card - 2 ^ P.card) ≤ 16 * P.card * n := le_trans h1 h2
        _ = n * (16 * P.card) := by ring
    have hmul2 : n * 4 ^ P.card ≤ n * (16 * P.card + 2 ^ P.card) := by
      have h2le : 2 ^ P.card ≤ 4 ^ P.card := Nat.pow_le_pow_left (by norm_num) P.card
      have hsum : 4 ^ P.card = (4 ^ P.card - 2 ^ P.card) + 2 ^ P.card :=
        (Nat.sub_add_cancel h2le).symm
      calc n * 4 ^ P.card = n * ((4 ^ P.card - 2 ^ P.card) + 2 ^ P.card) := by
            conv_lhs => rw [hsum]
        _ = n * (4 ^ P.card - 2 ^ P.card) + n * 2 ^ P.card := by ring
        _ ≤ n * (16 * P.card) + n * 2 ^ P.card := Nat.add_le_add_right hmul _
        _ = n * (16 * P.card + 2 ^ P.card) := by ring
    have h4 : 4 ^ P.card ≤ 16 * P.card + 2 ^ P.card :=
      Nat.le_of_mul_le_mul_left hmul2 (show 0 < n by omega)
    have hlt := sixteen_mul_add_two_pow_lt_four_pow P.card h3
    omega

theorem dim_eq_fourteen_of_single101 {n : ℕ} {l : Lbl n} {i₀ : Fin n}
    (hz : ∀ i, i ≠ i₀ → l.ZeroAt i) (ha : l.a i₀ = true) (hb : l.b i₀ = false)
    (hc : l.c i₀ = true) : l.dim = 14 := by
  have h14 : locM (l.a i₀) (l.b i₀) (l.c i₀) = 14 := by
    rw [ha, hb, hc]
    decide
  have key : ∏ i, locM (l.a i) (l.b i) (l.c i) = locM (l.a i₀) (l.b i₀) (l.c i₀) := by
    apply Finset.prod_eq_single i₀
    · intro i _ hi
      obtain ⟨h1, h2, h3⟩ := hz i hi
      rw [h1, h2, h3]
      decide
    · intro h'
      exact absurd (Finset.mem_univ i₀) h'
  unfold Lbl.dim
  exact key.trans h14

private lemma locM_eq_one_iff_aux (x y z : Bool) :
    locM x y z = 1 ↔ x = false ∧ y = false ∧ z = false := by
  cases x <;> cases y <;> cases z <;> decide

private lemma locM_eq_fourteen_iff (x y z : Bool) :
    locM x y z = 14 ↔ x = true ∧ y = false ∧ z = true := by
  cases x <;> cases y <;> cases z <;> decide

private lemma locM_dvd_fourteen (x y z : Bool) (h : locM x y z ∣ 14) :
    locM x y z = 1 ∨ locM x y z = 14 := by
  cases x <;> cases y <;> cases z <;> revert h <;> decide

theorem single101_of_dim_eq_fourteen {n : ℕ} {l : Lbl n} (h : l.dim = 14) :
    ∃ i₀ : Fin n, (∀ i, i ≠ i₀ → l.ZeroAt i) ∧ l.a i₀ = true ∧ l.b i₀ = false ∧
      l.c i₀ = true := by
  unfold Lbl.dim at h
  have hex : ∃ i₀, locM (l.a i₀) (l.b i₀) (l.c i₀) ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact absurd (h.symm.trans (Finset.prod_eq_one (fun i _ => hcon i))) (by decide)
  obtain ⟨i₀, hi₀⟩ := hex
  have hdvd : locM (l.a i₀) (l.b i₀) (l.c i₀) ∣ ∏ i, locM (l.a i) (l.b i) (l.c i) :=
    Finset.dvd_prod_of_mem (fun i => locM (l.a i) (l.b i) (l.c i)) (Finset.mem_univ i₀)
  rw [h] at hdvd
  have h14 : locM (l.a i₀) (l.b i₀) (l.c i₀) = 14 := by
    rcases locM_dvd_fourteen _ _ _ hdvd with h1 | h1
    · exact absurd h1 hi₀
    · exact h1
  have hprod : locM (l.a i₀) (l.b i₀) (l.c i₀) *
      (∏ i ∈ Finset.univ.erase i₀, locM (l.a i) (l.b i) (l.c i)) =
      ∏ i, locM (l.a i) (l.b i) (l.c i) :=
    Finset.mul_prod_erase Finset.univ (fun i => locM (l.a i) (l.b i) (l.c i))
      (Finset.mem_univ i₀)
  rw [h14, h] at hprod
  have hR : ∏ i ∈ Finset.univ.erase i₀, locM (l.a i) (l.b i) (l.c i) = 1 := by
    omega
  have hone : ∀ i, i ≠ i₀ → locM (l.a i) (l.b i) (l.c i) = 1 := by
    intro i hi
    have hdvd' : locM (l.a i) (l.b i) (l.c i) ∣
        ∏ j ∈ Finset.univ.erase i₀, locM (l.a j) (l.b j) (l.c j) :=
      Finset.dvd_prod_of_mem (fun j => locM (l.a j) (l.b j) (l.c j))
        (Finset.mem_erase.2 ⟨hi, Finset.mem_univ i⟩)
    rw [hR] at hdvd'
    exact Nat.dvd_one.1 hdvd'
  obtain ⟨ha, hb, hc⟩ := (locM_eq_fourteen_iff _ _ _).1 h14
  exact ⟨i₀, fun i hi => (locM_eq_one_iff_aux _ _ _).1 (hone i hi), ha, hb, hc⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6.McClurg
