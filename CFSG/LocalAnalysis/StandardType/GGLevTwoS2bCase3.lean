module

public import CFSG.LocalAnalysis.StandardType.GGLevTwoS2bCase2

public section

namespace CFSG.StandardType.LevTwo

open CFSG.LieType.RootSystem CFSG.LieType.Universal.Spin

theorem levTwoS2b_dot_sub_coord (n : ℕ) {a b : Fin n} (_hab : a ≠ b) (s t : ℤ)
    (v : Fin n → ℤ) :
    ∑ c : Fin n, ((Pi.single a s - Pi.single b t : Fin n → ℤ) c : ℚ) *
        ((levTwoS2b_coord n v c : ℤ) : ℚ) =
      (s : ℚ) * (levTwoS2b_coord n v a : ℚ) -
        (t : ℚ) * (levTwoS2b_coord n v b : ℚ) := by
  simp only [Pi.sub_apply, Int.cast_sub, sub_mul, Finset.sum_sub_distrib]
  rw [show ∑ c : Fin n, ((Pi.single a s : Fin n → ℤ) c : ℚ) *
        ((levTwoS2b_coord n v c : ℤ) : ℚ) =
      (s : ℚ) * (levTwoS2b_coord n v a : ℚ) from by
      rw [Fintype.sum_eq_single a]
      · simp
      · intro c hc; simp [hc]]
  rw [show ∑ c : Fin n, ((Pi.single b t : Fin n → ℤ) c : ℚ) *
        ((levTwoS2b_coord n v c : ℤ) : ℚ) =
      (t : ℚ) * (levTwoS2b_coord n v b : ℚ) from by
      rw [Fintype.sum_eq_single b]
      · simp
      · intro c hc; simp [hc]]

theorem levTwoS2b_dot_sub_self (n : ℕ) {a b : Fin n} (hab : a ≠ b) (s t : ℤ) :
    ∑ c : Fin n, ((Pi.single a s - Pi.single b t : Fin n → ℤ) c : ℚ) *
        ((Pi.single a s - Pi.single b t : Fin n → ℤ) c : ℚ) =
      (s : ℚ) * (s : ℚ) + (t : ℚ) * (t : ℚ) := by
  simp only [Pi.sub_apply, Int.cast_sub, sub_mul, mul_sub, Finset.sum_sub_distrib]
  rw [levTwoS2b_dot_single_self n a s, levTwoS2b_dot_single_self n b t,
    levTwoS2b_dot_single_ne n hab s t, levTwoS2b_dot_single_ne n (Ne.symm hab) t s]
  ring

theorem levTwoS2b_coord_rRefl_gen (n : ℕ) (hn : 1 ≤ n) {a b : Fin n} (hab : a ≠ b)
    {s t : ℤ} (hs : s = 1 ∨ s = -1) (ht : t = 1 ∨ t = -1) (v : Fin n → ℤ) :
    levTwoS2b_coord n
        (weylAction (isFiniteType_cartanB n)
          (rRefl (isFiniteType_cartanB n)
            (levTwoS2b_ofCoord n (Pi.single a s - Pi.single b t))) v) =
      levTwoS2b_coord n v -
        (s * levTwoS2b_coord n v a - t * levTwoS2b_coord n v b) •
          (Pi.single a s - Pi.single b t) := by
  have hβ : IsRt (isFiniteType_cartanB n)
      (levTwoS2b_ofCoord n (Pi.single a s - Pi.single b t)) := by
    rw [show (Pi.single a s - Pi.single b t : Fin n → ℤ) =
        Pi.single a s + Pi.single b (-t) by rw [sub_eq_add_neg, ← Pi.single_neg]]
    exact levTwoS2b_isRt_ofCoord_long n hab hs (by rcases ht with h | h <;> simp [h])
  have hk : ((s * levTwoS2b_coord n v a - t * levTwoS2b_coord n v b : ℤ) : ℚ) *
      (∑ c : Fin n,
        ((levTwoS2b_coord n (levTwoS2b_ofCoord n (Pi.single a s - Pi.single b t)) c : ℤ) : ℚ) *
        ((levTwoS2b_coord n (levTwoS2b_ofCoord n (Pi.single a s - Pi.single b t)) c : ℤ) : ℚ)) =
      2 * (∑ c : Fin n,
        ((levTwoS2b_coord n (levTwoS2b_ofCoord n (Pi.single a s - Pi.single b t)) c : ℤ) : ℚ) *
        ((levTwoS2b_coord n v c : ℤ) : ℚ)) := by
    rw [levTwoS2b_coord_ofCoord, levTwoS2b_dot_sub_self n hab s t,
      levTwoS2b_dot_sub_coord n hab s t v]
    have hs2 : (s : ℚ) * (s : ℚ) = 1 := by rcases hs with h | h <;> simp [h]
    have ht2 : (t : ℚ) * (t : ℚ) = 1 := by rcases ht with h | h <;> simp [h]
    rw [hs2, ht2]
    push_cast
    ring
  rw [levTwoS2b_rRefl_apply_sum n hn hβ hk]
  rw [levTwoS2b_coord_sub, levTwoS2b_coord_smul, levTwoS2b_coord_ofCoord]

theorem levTwoS2b_rRefl_gen_fix (n : ℕ) (hn : 1 ≤ n) {a b : Fin n} (hab : a ≠ b)
    {s t : ℤ} (hs : s = 1 ∨ s = -1) (ht : t = 1 ∨ t = -1) {v : Fin n → ℤ}
    (hva : levTwoS2b_coord n v a = 0) (hvb : levTwoS2b_coord n v b = 0) :
    weylAction (isFiniteType_cartanB n)
        (rRefl (isFiniteType_cartanB n)
          (levTwoS2b_ofCoord n (Pi.single a s - Pi.single b t))) v = v := by
  apply levTwoS2b_coord_injective n
  rw [levTwoS2b_coord_rRefl_gen n hn hab hs ht v, hva, hvb]
  simp

theorem levTwoS2b_rRefl_gen_swap (n : ℕ) (hn : 1 ≤ n) {a b : Fin n} (hab : a ≠ b)
    {s t : ℤ} (hs : s = 1 ∨ s = -1) (ht : t = 1 ∨ t = -1) :
    weylAction (isFiniteType_cartanB n)
        (rRefl (isFiniteType_cartanB n)
          (levTwoS2b_ofCoord n (Pi.single a s - Pi.single b t)))
        (levTwoS2b_ofCoord n (Pi.single a s)) =
      levTwoS2b_ofCoord n (Pi.single b t) := by
  apply levTwoS2b_coord_injective n
  rw [levTwoS2b_coord_rRefl_gen n hn hab hs ht (levTwoS2b_ofCoord n (Pi.single a s))]
  rw [levTwoS2b_coord_ofCoord]
  simp only [Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hab), mul_zero, sub_zero]
  rw [show s * s = 1 by rcases hs with h | h <;> simp [h], one_zsmul]
  rw [levTwoS2b_coord_ofCoord]
  abel

theorem levTwoS2b_dot_single_coord (n : ℕ) (c : Fin n) (v : Fin n → ℤ) :
    ∑ k : Fin n, ((Pi.single c 1 : Fin n → ℤ) k : ℚ) *
        ((levTwoS2b_coord n v k : ℤ) : ℚ) = (levTwoS2b_coord n v c : ℚ) := by
  rw [Fintype.sum_eq_single c]
  · simp
  · intro k hk; simp [hk]

theorem levTwoS2b_coord_rRefl_short (n : ℕ) (hn : 1 ≤ n) (c : Fin n) (v : Fin n → ℤ) :
    levTwoS2b_coord n
        (weylAction (isFiniteType_cartanB n)
          (rRefl (isFiniteType_cartanB n) (levTwoS2b_ofCoord n (Pi.single c 1))) v) =
      levTwoS2b_coord n v - (2 * levTwoS2b_coord n v c) • Pi.single c 1 := by
  have hβ : IsRt (isFiniteType_cartanB n) (levTwoS2b_ofCoord n (Pi.single c 1)) :=
    levTwoS2b_isRt_ofCoord_short n (Or.inl rfl)
  have hk : ((2 * levTwoS2b_coord n v c : ℤ) : ℚ) *
      (∑ k : Fin n,
        ((levTwoS2b_coord n (levTwoS2b_ofCoord n (Pi.single c 1)) k : ℤ) : ℚ) *
        ((levTwoS2b_coord n (levTwoS2b_ofCoord n (Pi.single c 1)) k : ℤ) : ℚ)) =
      2 * (∑ k : Fin n,
        ((levTwoS2b_coord n (levTwoS2b_ofCoord n (Pi.single c 1)) k : ℤ) : ℚ) *
        ((levTwoS2b_coord n v k : ℤ) : ℚ)) := by
    rw [levTwoS2b_coord_ofCoord, levTwoS2b_dot_single_self n c 1,
      levTwoS2b_dot_single_coord n c v]
    push_cast
    ring
  rw [levTwoS2b_rRefl_apply_sum n hn hβ hk]
  rw [levTwoS2b_coord_sub, levTwoS2b_coord_smul, levTwoS2b_coord_ofCoord]

theorem levTwoS2b_rRefl_single_eq (n : ℕ) {c : Fin n} {s : ℤ} (hs : s = 1 ∨ s = -1) :
    rRefl (isFiniteType_cartanB n) (levTwoS2b_ofCoord n (Pi.single c s)) =
      rRefl (isFiniteType_cartanB n) (levTwoS2b_ofCoord n (Pi.single c 1)) := by
  rcases hs with rfl | rfl
  · rfl
  · rw [show (levTwoS2b_ofCoord n (Pi.single c (-1)) : Fin n → ℤ) =
        -levTwoS2b_ofCoord n (Pi.single c 1) by
      rw [← levTwoS2b_ofCoord_neg, Pi.single_neg]]
    exact rRefl_neg (isFiniteType_cartanB n) (levTwoS2b_isRt_ofCoord_short n (Or.inl rfl))

theorem levTwoS2b_lam_eta_sub (n : ℕ) (p : ℕ) (c : Fin n → ZMod p) (a₀ : Fin n)
    (η : Fin n → ℤ) (hη : ∀ a : Fin n, η a = 1 ∨ η a = -1)
    (hD : ∀ a : Fin n, levTwoS2b_D c a = η a * levTwoS2b_D c a₀) {a b : Fin n} :
    lam c (levTwoS2b_ofCoord n (Pi.single a (η a) - Pi.single b (η b))) = 0 := by
  rw [levTwoS2b_lam_ofCoord]
  rw [show (∑ k : Fin n, (((Pi.single a (η a) - Pi.single b (η b) : Fin n → ℤ) k : ℤ) : ZMod p) *
      levTwoS2b_D c k) =
      (η a : ZMod p) * levTwoS2b_D c a - (η b : ZMod p) * levTwoS2b_D c b from by
    simp only [Pi.sub_apply, Int.cast_sub, sub_mul, Finset.sum_sub_distrib]
    congr 1
    · rw [Fintype.sum_eq_single a]
      · simp
      · intro k hk; simp [hk]
    · rw [Fintype.sum_eq_single b]
      · simp
      · intro k hk; simp [hk]]
  rw [hD a, hD b]
  have ha2 : (η a : ZMod p) * (η a : ZMod p) = 1 := by rcases hη a with h | h <;> simp [h]
  have hb2 : (η b : ZMod p) * (η b : ZMod p) = 1 := by rcases hη b with h | h <;> simp [h]
  linear_combination (levTwoS2b_D c a₀) * ha2 - (levTwoS2b_D c a₀) * hb2

theorem levTwoS2b_mem_PhiCase3_sub (n : ℕ) (p : ℕ) (c : Fin n → ZMod p) (a₀ : Fin n)
    (η : Fin n → ℤ) (hη : ∀ a : Fin n, η a = 1 ∨ η a = -1)
    (hD : ∀ a : Fin n, levTwoS2b_D c a = η a * levTwoS2b_D c a₀) {a b : Fin n} (hab : a ≠ b) :
    levTwoS2b_ofCoord n (Pi.single a (η a) - Pi.single b (η b)) ∈ levTwoS2b_PhiCase3 n p c := by
  have hshape : (levTwoS2b_ofCoord n (Pi.single a (η a) - Pi.single b (η b)) : Fin n → ℤ) =
      levTwoS2b_ofCoord n (Pi.single a (η a) + Pi.single b (-(η b))) := by
    rw [sub_eq_add_neg, Pi.single_neg]
  refine ⟨?_, ?_, levTwoS2b_lam_eta_sub n p c a₀ η hη hD⟩
  · rw [hshape]
    exact levTwoS2b_isRt_ofCoord_long n hab (hη a)
      (by rcases hη b with h | h <;> simp [h])
  · rw [hshape]
    exact levTwoS2b_isLong_ofCoord_long n hab (hη a)
      (by rcases hη b with h | h <;> simp [h])

theorem levTwoS2b_pm_eq_of_ne_zero {u v e f : ℤ} (hu : u = 1 ∨ u = -1)
    (hv : v = 1 ∨ v = -1) (he : e = 1 ∨ e = -1) (hf : f = 1 ∨ f = -1)
    (h : u * e + v * f ≠ 0) : u * e = v * f := by
  rcases hu with rfl | rfl <;> rcases he with h1 | h1 <;> rcases hv with rfl | rfl <;>
    rcases hf with h2 | h2 <;> simp_all

theorem levTwoS2b_lam_add_eta (n : ℕ) (p : ℕ) (c : Fin n → ZMod p) (a₀ : Fin n)
    (η : Fin n → ℤ) (hD : ∀ a : Fin n, levTwoS2b_D c a = η a * levTwoS2b_D c a₀)
    {b d : Fin n} (_hbd : b ≠ d) (u v : ℤ) :
    lam c (levTwoS2b_ofCoord n (Pi.single b u + Pi.single d v)) =
      ((u * η b + v * η d : ℤ) : ZMod p) * levTwoS2b_D c a₀ := by
  rw [levTwoS2b_lam_ofCoord]
  rw [show (∑ k : Fin n, (((Pi.single b u + Pi.single d v : Fin n → ℤ) k : ℤ) : ZMod p) *
      levTwoS2b_D c k) =
      (u : ZMod p) * levTwoS2b_D c b + (v : ZMod p) * levTwoS2b_D c d from by
    simp only [Pi.add_apply, Int.cast_add, add_mul, Finset.sum_add_distrib]
    congr 1
    · rw [Fintype.sum_eq_single b]
      · simp
      · intro k hk; simp [hk]
    · rw [Fintype.sum_eq_single d]
      · simp
      · intro k hk; simp [hk]]
  rw [hD b, hD d]
  push_cast
  ring

theorem levTwoS2b_case3_all_of_xa (n : ℕ) (hn : 2 ≤ n) (p : ℕ) (_hp : p.Prime) (_hp2 : p ≠ 2)
    (c : Fin n → ZMod p) (a₀ : Fin n) (η : Fin n → ℤ)
    (hη : ∀ a : Fin n, η a = 1 ∨ η a = -1) (_h0 : levTwoS2b_D c a₀ ≠ 0)
    (hD : ∀ a : Fin n, levTwoS2b_D c a = η a * levTwoS2b_D c a₀)
    {S : Set (Fin n → ℤ)} {a : Fin n}
    (hPhi : levTwoS2b_PhiCase3 n p c ⊆ S)
    (hxa : Cl (isFiniteType_cartanB n) S (levTwoS2b_ofCoord n (Pi.single a (η a)))) :
    ∀ x : Fin n → ℤ, IsRt (isFiniteType_cartanB n) x →
      Cl (isFiniteType_cartanB n) S x := by
  have hxb_all : ∀ b : Fin n, Cl (isFiniteType_cartanB n) S
      (levTwoS2b_ofCoord n (Pi.single b (η b))) := by
    intro b
    rcases eq_or_ne a b with rfl | hab
    · exact hxa
    · have hcl := Cl.refl
        (Cl.base (hPhi (levTwoS2b_mem_PhiCase3_sub n p c a₀ η hη hD hab))) hxa
      rwa [levTwoS2b_rRefl_gen_swap n (by omega) hab (hη a) (hη b)] at hcl
  have hneg : ∀ b d : Fin n, b ≠ d → Cl (isFiniteType_cartanB n) S
      (levTwoS2b_ofCoord n (Pi.single b (η b) + Pi.single d (η d))) := by
    intro b d hbd
    have hnegmem : levTwoS2b_ofCoord n (Pi.single d (η d) - Pi.single b (η b)) ∈
        levTwoS2b_PhiCase3 n p c :=
      levTwoS2b_mem_PhiCase3_sub n p c a₀ η hη hD (Ne.symm hbd)
    have hcl := Cl.refl (hxb_all b) (Cl.base (hPhi hnegmem))
    rw [show (levTwoS2b_ofCoord n (Pi.single d (η d) - Pi.single b (η b)) : Fin n → ℤ) =
        -(levTwoS2b_ofCoord n (Pi.single b (η b) - Pi.single d (η d))) by
      rw [← levTwoS2b_ofCoord_neg]
      congr 1
      ext k; simp only [Pi.sub_apply, Pi.neg_apply]; ring] at hcl
    rw [levTwoS2b_rRefl_single_eq (c := b) n (hη b)] at hcl
    have hgoal : weylAction (isFiniteType_cartanB n)
        (rRefl (isFiniteType_cartanB n) (levTwoS2b_ofCoord n (Pi.single b 1)))
        (-(levTwoS2b_ofCoord n (Pi.single b (η b) - Pi.single d (η d)))) =
        levTwoS2b_ofCoord n (Pi.single b (η b) + Pi.single d (η d)) := by
      apply levTwoS2b_coord_injective n
      have hcoord := levTwoS2b_coord_rRefl_short n (by omega) b
        (-(levTwoS2b_ofCoord n (Pi.single b (η b) - Pi.single d (η d))))
      rw [hcoord, levTwoS2b_coord_neg, levTwoS2b_coord_ofCoord,
        levTwoS2b_coord_ofCoord]
      funext k
      simp only [Pi.sub_apply, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul,
        Pi.single_apply]
      by_cases hkb : k = b
      · subst hkb; simp [hbd]; ring
      · by_cases hkd : k = d
        · subst hkd; simp [hkb]
        · simp [hkb, hkd]
    rw [hgoal] at hcl
    exact hcl
  intro x hx
  rcases levTwoS2b_isShort_or_isLong n hx with hxs | hxl
  · obtain ⟨b, t, ht, hcx⟩ := hxs
    have hx_eq : x = levTwoS2b_ofCoord n (Pi.single b t) := by
      apply levTwoS2b_coord_injective n; rw [levTwoS2b_coord_ofCoord, hcx]
    rw [hx_eq]
    rcases ht with rfl | rfl
    · rcases hη b with h1 | h1
      · simpa [h1] using hxb_all b
      · have hself := levTwoS2b_rRefl_self n (by omega)
          (β := levTwoS2b_ofCoord n (Pi.single b (η b)))
          (levTwoS2b_isRt_ofCoord_short n (hη b))
        have hcl := Cl.refl (hxb_all b) (hxb_all b)
        rw [hself] at hcl
        rwa [show (-levTwoS2b_ofCoord n (Pi.single b (η b)) : Fin n → ℤ) =
          levTwoS2b_ofCoord n (Pi.single b 1) by
            rw [h1, ← levTwoS2b_ofCoord_neg, Pi.single_neg, neg_neg]] at hcl
    · rcases hη b with h1 | h1
      · have hself := levTwoS2b_rRefl_self n (by omega)
          (β := levTwoS2b_ofCoord n (Pi.single b (η b)))
          (levTwoS2b_isRt_ofCoord_short n (hη b))
        have hcl := Cl.refl (hxb_all b) (hxb_all b)
        rw [hself] at hcl
        rwa [show (-levTwoS2b_ofCoord n (Pi.single b (η b)) : Fin n → ℤ) =
          levTwoS2b_ofCoord n (Pi.single b (-1)) by
            rw [h1, ← levTwoS2b_ofCoord_neg, Pi.single_neg]] at hcl
      · simpa [h1] using hxb_all b
  · by_cases hlam : lam c x = 0
    · exact Cl.base (hPhi ⟨hx, hxl, hlam⟩)
    · obtain ⟨b, d, u, v, hbd, hu, hv, hcx⟩ := hxl
      have hx_eq : x = levTwoS2b_ofCoord n (Pi.single b u + Pi.single d v) := by
        apply levTwoS2b_coord_injective n; rw [levTwoS2b_coord_ofCoord, hcx]
      rw [hx_eq]
      have hne : u * η b + v * η d ≠ 0 := by
        intro hzero
        apply hlam
        rw [hx_eq, levTwoS2b_lam_add_eta n p c a₀ η hD hbd u v, hzero]
        simp
      have hrel : u * η b = v * η d :=
        levTwoS2b_pm_eq_of_ne_zero hu hv (hη b) (hη d) hne
      by_cases hub : u = η b
      · have hvd : v = η d := by
          have h1 : u * η b = 1 := by rw [hub]; rcases hη b with h | h <;> simp [h]
          rw [h1] at hrel
          rcases hv with rfl | rfl <;> rcases hη d with h2 | h2 <;> omega
        rw [hub, hvd]
        exact hneg b d hbd
      · have hud : u = -η b := by
          rcases hu with rfl | rfl <;> rcases hη b with h | h <;> omega
        have hvd : v = -η d := by
          have h1 : u * η b = -1 := by rw [hud]; rcases hη b with h | h <;> simp [h]
          rw [h1] at hrel
          rcases hv with rfl | rfl <;> rcases hη d with h2 | h2 <;> omega
        rw [hud, hvd]
        have hself := levTwoS2b_rRefl_self n (by omega)
          (β := levTwoS2b_ofCoord n (Pi.single b (η b) + Pi.single d (η d)))
          (levTwoS2b_isRt_ofCoord_long n hbd (hη b) (hη d))
        have hcl := Cl.refl (hneg b d hbd) (hneg b d hbd)
        rw [hself] at hcl
        rwa [show (-levTwoS2b_ofCoord n (Pi.single b (η b) + Pi.single d (η d)) : Fin n → ℤ) =
          levTwoS2b_ofCoord n (Pi.single b (-η b) + Pi.single d (-η d)) by
            rw [← levTwoS2b_ofCoord_neg]
            congr 1
            ext k; simp only [Pi.add_apply, Pi.neg_apply, Pi.single_neg]; ring_nf] at hcl

theorem levTwoS2b_rRefl_gen_add_gen (n : ℕ) (hn : 1 ≤ n) {b b' d : Fin n} (hbb' : b ≠ b')
    (hdb' : d ≠ b') (hdb : d ≠ b) {η : Fin n → ℤ} (hηb : η b = 1 ∨ η b = -1)
    (hηb' : η b' = 1 ∨ η b' = -1) (hηd : η d = 1 ∨ η d = -1) :
    weylAction (isFiniteType_cartanB n)
        (rRefl (isFiniteType_cartanB n)
          (levTwoS2b_ofCoord n (Pi.single b (η b) - Pi.single b' (η b'))))
        (levTwoS2b_ofCoord n (Pi.single b (η b) + Pi.single d (η d))) =
      levTwoS2b_ofCoord n (Pi.single b' (η b') + Pi.single d (η d)) := by
  apply levTwoS2b_coord_injective n
  have hcoord := levTwoS2b_coord_rRefl_gen n hn hbb' hηb hηb'
    (levTwoS2b_ofCoord n (Pi.single b (η b) + Pi.single d (η d)))
  rw [hcoord]
  rw [levTwoS2b_coord_ofCoord, levTwoS2b_coord_ofCoord]
  have hb2 : η b * η b = 1 := by rcases hηb with h | h <;> simp [h]
  have hb'2 : η b' * η b' = 1 := by rcases hηb' with h | h <;> simp [h]
  have hd2 : η d * η d = 1 := by rcases hηd with h | h <;> simp [h]
  funext k
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  split_ifs <;> simp_all





end CFSG.StandardType.LevTwo
