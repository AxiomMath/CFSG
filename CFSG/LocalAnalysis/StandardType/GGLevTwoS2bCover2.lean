module

public import CFSG.LocalAnalysis.StandardType.GGLevTwoS2bCover

public section

namespace CFSG.StandardType.LevTwo

open CFSG.LieType.RootSystem CFSG.LieType.Universal.Spin

theorem levTwoS2b_rRefl_apply_sum (n : ℕ) (hn : 1 ≤ n) {β v : Fin n → ℤ}
    (hβ : IsRt (isFiniteType_cartanB n) β) {k₀ : ℤ}
    (hk : (k₀ : ℚ) * (∑ c : Fin n, ((levTwoS2b_coord n β c : ℤ) : ℚ) *
        ((levTwoS2b_coord n β c : ℤ) : ℚ)) =
      2 * (∑ c : Fin n, ((levTwoS2b_coord n β c : ℤ) : ℚ) *
        ((levTwoS2b_coord n v c : ℤ) : ℚ))) :
    weylAction (isFiniteType_cartanB n) (rRefl (isFiniteType_cartanB n) β) v = v - k₀ • β := by
  apply levTwoS2b_rRefl_apply n hn hβ
  rw [levTwoS2b_form_coord_kappa n hn, levTwoS2b_form_coord_kappa n hn]
  linear_combination (levTwoS2b_kappa n hn) * hk

theorem levTwoS2b_coord_rRefl_sub (n : ℕ) (hn : 1 ≤ n) {a b : Fin n} (hab : a ≠ b)
    (v : Fin n → ℤ) :
    levTwoS2b_coord n
        (weylAction (isFiniteType_cartanB n)
          (rRefl (isFiniteType_cartanB n)
            (levTwoS2b_ofCoord n (Pi.single a 1 - Pi.single b 1))) v) =
      levTwoS2b_coord n v -
        (levTwoS2b_coord n v a - levTwoS2b_coord n v b) •
          (Pi.single a 1 - Pi.single b 1) := by
  have hβ : IsRt (isFiniteType_cartanB n)
      (levTwoS2b_ofCoord n (Pi.single a 1 - Pi.single b 1)) :=
    levTwoS2b_isRt_ofCoord_sub n hab
  have hk : ((levTwoS2b_coord n v a - levTwoS2b_coord n v b : ℤ) : ℚ) *
      (∑ c : Fin n,
        ((levTwoS2b_coord n (levTwoS2b_ofCoord n (Pi.single a 1 - Pi.single b 1)) c : ℤ) : ℚ) *
        ((levTwoS2b_coord n (levTwoS2b_ofCoord n (Pi.single a 1 - Pi.single b 1)) c : ℤ) : ℚ)) =
      2 * (∑ c : Fin n,
        ((levTwoS2b_coord n (levTwoS2b_ofCoord n (Pi.single a 1 - Pi.single b 1)) c : ℤ) : ℚ) *
        ((levTwoS2b_coord n v c : ℤ) : ℚ)) := by
    rw [levTwoS2b_coord_ofCoord]
    rw [show (Pi.single a 1 - Pi.single b 1 : Fin n → ℤ) =
      Pi.single a 1 + Pi.single b (-1) by rw [sub_eq_add_neg, Pi.single_neg]]
    rw [levTwoS2b_dot_add_self n hab 1 (-1)]
    have hdot : ∑ c : Fin n,
        ((Pi.single a 1 + Pi.single b (-1) : Fin n → ℤ) c : ℚ) *
          ((levTwoS2b_coord n v c : ℤ) : ℚ) =
        (levTwoS2b_coord n v a : ℚ) - (levTwoS2b_coord n v b : ℚ) := by
      rw [show (Pi.single a 1 + Pi.single b (-1) : Fin n → ℤ) =
        Pi.single a 1 - Pi.single b 1 by rw [sub_eq_add_neg, Pi.single_neg]]
      simp only [Pi.sub_apply, Int.cast_sub, sub_mul, Finset.sum_sub_distrib]
      rw [show ∑ c : Fin n, ((Pi.single a 1 : Fin n → ℤ) c : ℚ) *
            ((levTwoS2b_coord n v c : ℤ) : ℚ) = (levTwoS2b_coord n v a : ℚ) from by
          rw [Fintype.sum_eq_single a]
          · simp
          · intro c hc; simp [hc]]
      rw [show ∑ c : Fin n, ((Pi.single b 1 : Fin n → ℤ) c : ℚ) *
            ((levTwoS2b_coord n v c : ℤ) : ℚ) = (levTwoS2b_coord n v b : ℚ) from by
          rw [Fintype.sum_eq_single b]
          · simp
          · intro c hc; simp [hc]]
    rw [hdot]
    push_cast
    ring
  rw [levTwoS2b_rRefl_apply_sum n hn hβ hk]
  rw [levTwoS2b_coord_sub, levTwoS2b_coord_smul, levTwoS2b_coord_ofCoord]

theorem levTwoS2b_dot_add_coord (n : ℕ) {a b : Fin n} (_hab : a ≠ b) (v : Fin n → ℤ) :
    ∑ c : Fin n, ((Pi.single a 1 + Pi.single b 1 : Fin n → ℤ) c : ℚ) *
        ((levTwoS2b_coord n v c : ℤ) : ℚ) =
      (levTwoS2b_coord n v a : ℚ) + (levTwoS2b_coord n v b : ℚ) := by
  simp only [Pi.add_apply, Int.cast_add, add_mul, Finset.sum_add_distrib]
  rw [show ∑ c : Fin n, ((Pi.single a 1 : Fin n → ℤ) c : ℚ) *
        ((levTwoS2b_coord n v c : ℤ) : ℚ) = (levTwoS2b_coord n v a : ℚ) from by
      rw [Fintype.sum_eq_single a]
      · simp
      · intro c hc; simp [hc]]
  rw [show ∑ c : Fin n, ((Pi.single b 1 : Fin n → ℤ) c : ℚ) *
        ((levTwoS2b_coord n v c : ℤ) : ℚ) = (levTwoS2b_coord n v b : ℚ) from by
      rw [Fintype.sum_eq_single b]
      · simp
      · intro c hc; simp [hc]]

theorem levTwoS2b_coord_rRefl_add (n : ℕ) (hn : 1 ≤ n) {a b : Fin n} (hab : a ≠ b)
    (v : Fin n → ℤ) :
    levTwoS2b_coord n
        (weylAction (isFiniteType_cartanB n)
          (rRefl (isFiniteType_cartanB n)
            (levTwoS2b_ofCoord n (Pi.single a 1 + Pi.single b 1))) v) =
      levTwoS2b_coord n v -
        (levTwoS2b_coord n v a + levTwoS2b_coord n v b) •
          (Pi.single a 1 + Pi.single b 1) := by
  have hβ : IsRt (isFiniteType_cartanB n)
      (levTwoS2b_ofCoord n (Pi.single a 1 + Pi.single b 1)) :=
    levTwoS2b_isRt_ofCoord_long n hab (Or.inl rfl) (Or.inl rfl)
  have hk : ((levTwoS2b_coord n v a + levTwoS2b_coord n v b : ℤ) : ℚ) *
      (∑ c : Fin n,
        ((levTwoS2b_coord n (levTwoS2b_ofCoord n (Pi.single a 1 + Pi.single b 1)) c : ℤ) : ℚ) *
        ((levTwoS2b_coord n (levTwoS2b_ofCoord n (Pi.single a 1 + Pi.single b 1)) c : ℤ) : ℚ)) =
      2 * (∑ c : Fin n,
        ((levTwoS2b_coord n (levTwoS2b_ofCoord n (Pi.single a 1 + Pi.single b 1)) c : ℤ) : ℚ) *
        ((levTwoS2b_coord n v c : ℤ) : ℚ)) := by
    rw [levTwoS2b_coord_ofCoord, levTwoS2b_dot_add_self n hab 1 1,
      levTwoS2b_dot_add_coord n hab v]
    push_cast
    ring
  rw [levTwoS2b_rRefl_apply_sum n hn hβ hk]
  rw [levTwoS2b_coord_sub, levTwoS2b_coord_smul, levTwoS2b_coord_ofCoord]

theorem levTwoS2b_rRefl_self (n : ℕ) (hn : 1 ≤ n) {β : Fin n → ℤ}
    (hβ : IsRt (isFiniteType_cartanB n) β) :
    weylAction (isFiniteType_cartanB n) (rRefl (isFiniteType_cartanB n) β) β = -β := by
  have hk : (2 : ℚ) * (∑ c : Fin n, ((levTwoS2b_coord n β c : ℤ) : ℚ) *
        ((levTwoS2b_coord n β c : ℤ) : ℚ)) =
      2 * (∑ c : Fin n, ((levTwoS2b_coord n β c : ℤ) : ℚ) *
        ((levTwoS2b_coord n β c : ℤ) : ℚ)) := by ring
  rw [levTwoS2b_rRefl_apply_sum n hn hβ hk]
  rw [show ((2 : ℕ) : ℤ) = (2 : ℤ) by norm_num, two_zsmul]
  abel

theorem levTwoS2b_isRt_ofCoord_short (n : ℕ) {a : Fin n} {s : ℤ}
    (hs : s = 1 ∨ s = -1) :
    IsRt (isFiniteType_cartanB n) (levTwoS2b_ofCoord n (Pi.single a s)) := by
  rw [levTwoS2b_isRt_iff_coord, levTwoS2b_coord_ofCoord]
  exact Or.inr ⟨a, s, hs, rfl⟩

theorem levTwoS2b_coord_sub_apply_of_ne (n : ℕ) {a b k : Fin n} (hak : a ≠ k) (hbk : b ≠ k) :
    levTwoS2b_coord n (levTwoS2b_ofCoord n (Pi.single a 1 - Pi.single b 1)) k = 0 := by
  rw [levTwoS2b_coord_ofCoord]
  simp [Pi.sub_apply, hak, hbk]

theorem levTwoS2b_mem_PhiCase2_sub (n : ℕ) {a b k : Fin n} (hab : a ≠ b) (hak : a ≠ k)
    (hbk : b ≠ k) :
    levTwoS2b_ofCoord n (Pi.single a 1 - Pi.single b 1) ∈ levTwoS2b_PhiCase2 n k :=
  ⟨levTwoS2b_isRt_ofCoord_sub n hab, levTwoS2b_isLong_ofCoord_sub n hab,
    levTwoS2b_coord_sub_apply_of_ne n hak hbk⟩

theorem levTwoS2b_case2_C2_all (n : ℕ) (hn : 1 ≤ n) (k : Fin n) {t u : ℤ}
    (ht : t = 1 ∨ t = -1) (hu : u = 1 ∨ u = -1) :
    Cl (isFiniteType_cartanB n) (levTwoS2b_PhiCase2 n k ∪
      {levTwoS2b_ofCoord n (Pi.single k t)}) (levTwoS2b_ofCoord n (Pi.single k u)) := by
  have hrep : Cl (isFiniteType_cartanB n) (levTwoS2b_PhiCase2 n k ∪
      {levTwoS2b_ofCoord n (Pi.single k t)}) (levTwoS2b_ofCoord n (Pi.single k t)) :=
    Cl.base (Or.inr (Set.mem_singleton _))
  rcases ht with rfl | rfl <;> rcases hu with rfl | rfl
  · exact hrep
  · have hself := levTwoS2b_rRefl_self n hn
        (β := levTwoS2b_ofCoord n (Pi.single k 1))
        (levTwoS2b_isRt_ofCoord_short n (a := k) (Or.inl rfl))
    have hcl := Cl.refl hrep hrep
    rw [hself] at hcl
    rwa [show (-levTwoS2b_ofCoord n (Pi.single k 1) : Fin n → ℤ) =
      levTwoS2b_ofCoord n (Pi.single k (-1)) by
        rw [← levTwoS2b_ofCoord_neg, Pi.single_neg]] at hcl
  · have hself := levTwoS2b_rRefl_self n hn
        (β := levTwoS2b_ofCoord n (Pi.single k (-1)))
        (levTwoS2b_isRt_ofCoord_short n (a := k) (Or.inr rfl))
    have hcl := Cl.refl hrep hrep
    rw [hself] at hcl
    rwa [show (-levTwoS2b_ofCoord n (Pi.single k (-1)) : Fin n → ℤ) =
      levTwoS2b_ofCoord n (Pi.single k 1) by
        rw [← levTwoS2b_ofCoord_neg, Pi.single_neg, neg_neg]] at hcl
  · exact hrep

theorem levTwoS2b_mem_PhiCase2_sub' (n : ℕ) {a b k : Fin n} (hab : a ≠ b) (hak : a ≠ k)
    (hbk : b ≠ k) {s : ℤ} (hs : s = 1 ∨ s = -1) :
    levTwoS2b_ofCoord n (Pi.single a s - Pi.single b s) ∈ levTwoS2b_PhiCase2 n k :=
  ⟨levTwoS2b_isRt_ofCoord_sub' n hab hs, levTwoS2b_isLong_ofCoord_sub' n hab hs,
    by rw [levTwoS2b_coord_ofCoord]; simp [Pi.sub_apply, hak, hbk]⟩

theorem levTwoS2b_case2_C1_all' (n : ℕ) (hn : 1 ≤ n) (k : Fin n) {a : Fin n} (hak : a ≠ k)
    {s : ℤ} (hs : s = 1 ∨ s = -1) {b : Fin n} (hbk : b ≠ k) {t : ℤ} (ht : t = 1 ∨ t = -1) :
    Cl (isFiniteType_cartanB n) (levTwoS2b_PhiCase2 n k ∪
      {levTwoS2b_ofCoord n (Pi.single a s)}) (levTwoS2b_ofCoord n (Pi.single b t)) := by
  rcases eq_or_ne a b with rfl | hab
  · rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
    · exact Cl.base (Or.inr (Set.mem_singleton _))
    · have hself := levTwoS2b_rRefl_self n hn
          (β := levTwoS2b_ofCoord n (Pi.single a 1))
          (levTwoS2b_isRt_ofCoord_short n (a := a) (Or.inl rfl))
      have hcl : Cl (isFiniteType_cartanB n) (levTwoS2b_PhiCase2 n k ∪
          {levTwoS2b_ofCoord n (Pi.single a 1)}) _ :=
        Cl.refl (Cl.base (Or.inr (Set.mem_singleton _)))
          (Cl.base (Or.inr (Set.mem_singleton _)))
      rw [hself] at hcl
      rwa [show (-levTwoS2b_ofCoord n (Pi.single a 1) : Fin n → ℤ) =
        levTwoS2b_ofCoord n (Pi.single a (-1)) by
          rw [← levTwoS2b_ofCoord_neg, Pi.single_neg]] at hcl
    · have hself := levTwoS2b_rRefl_self n hn
          (β := levTwoS2b_ofCoord n (Pi.single a (-1)))
          (levTwoS2b_isRt_ofCoord_short n (a := a) (Or.inr rfl))
      have hcl : Cl (isFiniteType_cartanB n) (levTwoS2b_PhiCase2 n k ∪
          {levTwoS2b_ofCoord n (Pi.single a (-1))}) _ :=
        Cl.refl (Cl.base (Or.inr (Set.mem_singleton _)))
          (Cl.base (Or.inr (Set.mem_singleton _)))
      rw [hself] at hcl
      rwa [show (-levTwoS2b_ofCoord n (Pi.single a (-1)) : Fin n → ℤ) =
        levTwoS2b_ofCoord n (Pi.single a 1) by
          rw [← levTwoS2b_ofCoord_neg, Pi.single_neg, neg_neg]] at hcl
    · exact Cl.base (Or.inr (Set.mem_singleton _))
  · rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
    · have hstep : Cl (isFiniteType_cartanB n) (levTwoS2b_PhiCase2 n k ∪
          {levTwoS2b_ofCoord n (Pi.single a 1)}) (levTwoS2b_ofCoord n (Pi.single b 1)) := by
        have hcl : Cl (isFiniteType_cartanB n) (levTwoS2b_PhiCase2 n k ∪
            {levTwoS2b_ofCoord n (Pi.single a 1)}) _ :=
          Cl.refl (Cl.base (Or.inl (levTwoS2b_mem_PhiCase2_sub' n hab hak hbk
            (Or.inl rfl)))) (Cl.base (Or.inr (Set.mem_singleton _)))
        rwa [levTwoS2b_rRefl_sub n hn hab (Or.inl rfl)] at hcl
      exact hstep
    · have hstep : Cl (isFiniteType_cartanB n) (levTwoS2b_PhiCase2 n k ∪
          {levTwoS2b_ofCoord n (Pi.single a 1)}) (levTwoS2b_ofCoord n (Pi.single b 1)) := by
        have hcl : Cl (isFiniteType_cartanB n) (levTwoS2b_PhiCase2 n k ∪
            {levTwoS2b_ofCoord n (Pi.single a 1)}) _ :=
          Cl.refl (Cl.base (Or.inl (levTwoS2b_mem_PhiCase2_sub' n hab hak hbk
            (Or.inl rfl)))) (Cl.base (Or.inr (Set.mem_singleton _)))
        rwa [levTwoS2b_rRefl_sub n hn hab (Or.inl rfl)] at hcl
      have hself := levTwoS2b_rRefl_self n hn
          (β := levTwoS2b_ofCoord n (Pi.single b 1))
          (levTwoS2b_isRt_ofCoord_short n (a := b) (Or.inl rfl))
      have hcl := Cl.refl hstep hstep
      rw [hself] at hcl
      rwa [show (-levTwoS2b_ofCoord n (Pi.single b 1) : Fin n → ℤ) =
        levTwoS2b_ofCoord n (Pi.single b (-1)) by
          rw [← levTwoS2b_ofCoord_neg, Pi.single_neg]] at hcl
    · have hstep : Cl (isFiniteType_cartanB n) (levTwoS2b_PhiCase2 n k ∪
          {levTwoS2b_ofCoord n (Pi.single a (-1))}) (levTwoS2b_ofCoord n (Pi.single b (-1))) := by
        have hcl : Cl (isFiniteType_cartanB n) (levTwoS2b_PhiCase2 n k ∪
            {levTwoS2b_ofCoord n (Pi.single a (-1))}) _ :=
          Cl.refl (Cl.base (Or.inl (levTwoS2b_mem_PhiCase2_sub' n hab hak hbk
            (Or.inr rfl)))) (Cl.base (Or.inr (Set.mem_singleton _)))
        rwa [levTwoS2b_rRefl_sub n hn hab (Or.inr rfl)] at hcl
      have hself := levTwoS2b_rRefl_self n hn
          (β := levTwoS2b_ofCoord n (Pi.single b (-1)))
          (levTwoS2b_isRt_ofCoord_short n (a := b) (Or.inr rfl))
      have hcl := Cl.refl hstep hstep
      rw [hself] at hcl
      rwa [show (-levTwoS2b_ofCoord n (Pi.single b (-1)) : Fin n → ℤ) =
        levTwoS2b_ofCoord n (Pi.single b 1) by
          rw [← levTwoS2b_ofCoord_neg, Pi.single_neg, neg_neg]] at hcl
    · have hstep : Cl (isFiniteType_cartanB n) (levTwoS2b_PhiCase2 n k ∪
          {levTwoS2b_ofCoord n (Pi.single a (-1))}) (levTwoS2b_ofCoord n (Pi.single b (-1))) := by
        have hcl : Cl (isFiniteType_cartanB n) (levTwoS2b_PhiCase2 n k ∪
            {levTwoS2b_ofCoord n (Pi.single a (-1))}) _ :=
          Cl.refl (Cl.base (Or.inl (levTwoS2b_mem_PhiCase2_sub' n hab hak hbk
            (Or.inr rfl)))) (Cl.base (Or.inr (Set.mem_singleton _)))
        rwa [levTwoS2b_rRefl_sub n hn hab (Or.inr rfl)] at hcl
      exact hstep

theorem levTwoS2b_rRefl_sub_C3 (n : ℕ) (hn : 1 ≤ n) {a b k : Fin n} (hab : a ≠ b)
    (hak : a ≠ k) (hbk : b ≠ k) {s t : ℤ} (_hs : s = 1 ∨ s = -1) (_ht : t = 1 ∨ t = -1) :
    weylAction (isFiniteType_cartanB n)
        (rRefl (isFiniteType_cartanB n)
          (levTwoS2b_ofCoord n (Pi.single a 1 - Pi.single b 1)))
        (levTwoS2b_ofCoord n (Pi.single a s + Pi.single k t)) =
      levTwoS2b_ofCoord n (Pi.single b s + Pi.single k t) := by
  apply levTwoS2b_coord_injective n
  rw [levTwoS2b_coord_rRefl_sub n hn hab, levTwoS2b_coord_ofCoord, levTwoS2b_coord_ofCoord]
  funext x
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  split_ifs <;> simp_all

theorem levTwoS2b_rRefl_add_C3' (n : ℕ) (hn : 1 ≤ n) {a c k : Fin n} (hac : a ≠ c)
    (hak : a ≠ k) (hck : c ≠ k) {s t : ℤ} (_hs : s = 1 ∨ s = -1) (_ht : t = 1 ∨ t = -1) :
    weylAction (isFiniteType_cartanB n)
        (rRefl (isFiniteType_cartanB n)
          (levTwoS2b_ofCoord n (Pi.single a 1 + Pi.single c 1)))
        (levTwoS2b_ofCoord n (Pi.single c s + Pi.single k t)) =
      levTwoS2b_ofCoord n (Pi.single a (-s) + Pi.single k t) := by
  apply levTwoS2b_coord_injective n
  rw [levTwoS2b_coord_rRefl_add n hn hac, levTwoS2b_coord_ofCoord, levTwoS2b_coord_ofCoord]
  funext x
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  split_ifs <;> simp_all

theorem levTwoS2b_case2_C3_all' (n : ℕ) (hn : 1 ≤ n) (k : Fin n) {a : Fin n} (hak : a ≠ k)
    {c : Fin n} (hca : c ≠ a) (hck : c ≠ k) {b : Fin n} (hbk : b ≠ k) {s₀ t₀ : ℤ}
    (hs₀ : s₀ = 1 ∨ s₀ = -1) (ht₀ : t₀ = 1 ∨ t₀ = -1) {s t : ℤ}
    (hs : s = 1 ∨ s = -1) (ht : t = 1 ∨ t = -1) :
    Cl (isFiniteType_cartanB n) (levTwoS2b_PhiCase2 n k ∪
      {levTwoS2b_ofCoord n (Pi.single a s₀ + Pi.single k t₀)})
      (levTwoS2b_ofCoord n (Pi.single b s + Pi.single k t)) := by
  set S : Set (Fin n → ℤ) := levTwoS2b_PhiCase2 n k ∪
    {levTwoS2b_ofCoord n (Pi.single a s₀ + Pi.single k t₀)} with hSdef
  have hbase : Cl (isFiniteType_cartanB n) S
      (levTwoS2b_ofCoord n (Pi.single a s₀ + Pi.single k t₀)) :=
    Cl.base (Or.inr (Set.mem_singleton _))
  have hβ1 : levTwoS2b_ofCoord n (Pi.single a 1 - Pi.single c 1) ∈ levTwoS2b_PhiCase2 n k :=
    levTwoS2b_mem_PhiCase2_sub n (Ne.symm hca) hak hck
  have hβ2 : levTwoS2b_ofCoord n (Pi.single a 1 + Pi.single c 1) ∈ levTwoS2b_PhiCase2 n k :=
    ⟨levTwoS2b_isRt_ofCoord_long n (Ne.symm hca) (Or.inl rfl) (Or.inl rfl),
      levTwoS2b_isLong_ofCoord_long n (Ne.symm hca) (Or.inl rfl) (Or.inl rfl),
      by rw [levTwoS2b_coord_ofCoord]; simp [Pi.add_apply, hak, hck]⟩
  have h2 : Cl (isFiniteType_cartanB n) S
      (levTwoS2b_ofCoord n (Pi.single a (-s₀) + Pi.single k t₀)) := by
    have hA1 : Cl (isFiniteType_cartanB n) S
        (levTwoS2b_ofCoord n (Pi.single c s₀ + Pi.single k t₀)) := by
      have hcl := Cl.refl (Cl.base (Or.inl hβ1)) hbase
      rwa [levTwoS2b_rRefl_sub_C3 n hn (Ne.symm hca) hak hck hs₀ ht₀] at hcl
    have hcl := Cl.refl (Cl.base (Or.inl hβ2)) hA1
    rwa [levTwoS2b_rRefl_add_C3' n hn (Ne.symm hca) hak hck hs₀ ht₀] at hcl
  have h3 : Cl (isFiniteType_cartanB n) S
      (levTwoS2b_ofCoord n (Pi.single a s₀ + Pi.single k (-t₀))) := by
    have hself := levTwoS2b_rRefl_self n hn
        (β := levTwoS2b_ofCoord n (Pi.single a (-s₀) + Pi.single k t₀))
        (levTwoS2b_isRt_ofCoord_long n hak (by rcases hs₀ with h | h <;> simp [h]) ht₀)
    have hcl := Cl.refl h2 h2
    rw [hself] at hcl
    rwa [show (-levTwoS2b_ofCoord n (Pi.single a (-s₀) + Pi.single k t₀) : Fin n → ℤ) =
      levTwoS2b_ofCoord n (Pi.single a s₀ + Pi.single k (-t₀)) by
        rw [← levTwoS2b_ofCoord_neg]
        congr 1
        ext x
        simp only [Pi.add_apply, Pi.neg_apply, Pi.single_apply]
        split_ifs <;> ring] at hcl
  have h4 : Cl (isFiniteType_cartanB n) S
      (levTwoS2b_ofCoord n (Pi.single a (-s₀) + Pi.single k (-t₀))) := by
    have hself := levTwoS2b_rRefl_self n hn
        (β := levTwoS2b_ofCoord n (Pi.single a s₀ + Pi.single k t₀))
        (levTwoS2b_isRt_ofCoord_long n hak hs₀ ht₀)
    have hcl := Cl.refl hbase hbase
    rw [hself] at hcl
    rwa [show (-levTwoS2b_ofCoord n (Pi.single a s₀ + Pi.single k t₀) : Fin n → ℤ) =
      levTwoS2b_ofCoord n (Pi.single a (-s₀) + Pi.single k (-t₀)) by
        rw [← levTwoS2b_ofCoord_neg]
        congr 1
        ext x
        simp only [Pi.add_apply, Pi.neg_apply, Pi.single_apply]
        split_ifs <;> ring] at hcl
  have move : ∀ {u v : ℤ}, (u = 1 ∨ u = -1) → (v = 1 ∨ v = -1) →
      Cl (isFiniteType_cartanB n) S (levTwoS2b_ofCoord n (Pi.single a u + Pi.single k v)) →
      Cl (isFiniteType_cartanB n) S (levTwoS2b_ofCoord n (Pi.single b u + Pi.single k v)) := by
    intro u v hu hv hcl
    rcases eq_or_ne a b with rfl | hab
    · exact hcl
    · have hcl' := Cl.refl
        (Cl.base (Or.inl (levTwoS2b_mem_PhiCase2_sub n hab hak hbk))) hcl
      rwa [levTwoS2b_rRefl_sub_C3 n hn hab hak hbk hu hv] at hcl'
  have hB1 := move hs₀ ht₀ hbase
  have hB2 := move (by rcases hs₀ with h | h <;> simp [h]) ht₀ h2
  have hB3 := move hs₀ (by rcases ht₀ with h | h <;> simp [h]) h3
  have hB4 := move (by rcases hs₀ with h | h <;> simp [h])
    (by rcases ht₀ with h | h <;> simp [h]) h4
  rcases hs₀ with rfl | rfl <;> rcases ht₀ with rfl | rfl <;>
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;>
    first | exact hB1 | exact hB2 | exact hB3 | exact hB4

end CFSG.StandardType.LevTwo
