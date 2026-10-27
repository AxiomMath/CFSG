module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListL3Block
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListFlag4
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple

public section

namespace CFSG.Quasithin.H13.NQCat.SLk

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Vol2Native.A312L

theorem eq_one_of_pow_seven {s : ℕ} (hs : s ≤ 2) {M : Matrix (Fin s) (Fin s) (ZMod 2)}
    (h : M ^ 7 = 1) : M = 1 := by
  interval_cases s
  · exact Subsingleton.elim _ _
  · revert M h
    decide
  · revert M h
    decide

section Unitri

variable {k : ℕ}

theorem entry_of_blkAt_eq_one {a m : ℕ} (h : a + m ≤ k) {A : Matrix (Fin k) (Fin k) (ZMod 2)}
    (hA : blkAt a m h A = 1) {r c : Fin k} (hr : a ≤ (r : ℕ)) (hr' : (r : ℕ) < a + m)
    (hc : a ≤ (c : ℕ)) (hc' : (c : ℕ) < a + m) :
    A r c = (1 : Matrix (Fin k) (Fin k) (ZMod 2)) r c := by
  have h1 := congrFun (congrFun hA ⟨(r : ℕ) - a, by omega⟩) ⟨(c : ℕ) - a, by omega⟩
  rw [blkAt_apply] at h1
  have er : (⟨a + ((r : ℕ) - a), by omega⟩ : Fin k) = r := Fin.ext (by simp; omega)
  have ec : (⟨a + ((c : ℕ) - a), by omega⟩ : Fin k) = c := Fin.ext (by simp; omega)
  rw [er, ec] at h1
  rw [h1]
  by_cases hrc : r = c
  · subst hrc
    rw [Matrix.one_apply_eq, Matrix.one_apply_eq]
  · have : (⟨(r : ℕ) - a, by omega⟩ : Fin m) ≠ ⟨(c : ℕ) - a, by omega⟩ := by
      intro h'
      apply hrc
      have := congrArg Fin.val h'
      simp at this
      exact Fin.ext (by omega)
    rw [Matrix.one_apply_ne this, Matrix.one_apply_ne hrc]

theorem mem_unitriangular_of_blocks {a b : ℕ} (hab : a ≤ b) (hbk : b ≤ k)
    {g : SpecialLinearGroup (Fin k) (ZMod 2)} (ha : g ∈ stabilizer (flagSpace k (ZMod 2) a))
    (hb : g ∈ stabilizer (flagSpace k (ZMod 2) b))
    (h1 : blkAt 0 a (by omega) (g : Matrix (Fin k) (Fin k) (ZMod 2)) = 1)
    (h2 : blkAt a (b - a) (by omega) (g : Matrix (Fin k) (Fin k) (ZMod 2)) = 1)
    (h3 : blkAt b (k - b) (by omega) (g : Matrix (Fin k) (Fin k) (ZMod 2)) = 1) :
    g ∈ unitriangular k (ZMod 2) := by
  have key : ∀ r c : Fin k, (c : ℕ) ≤ r →
      (g : Matrix (Fin k) (Fin k) (ZMod 2)) r c = (1 : Matrix (Fin k) (Fin k) (ZMod 2)) r c := by
    intro r c hcr
    by_cases hra : (r : ℕ) < a
    · exact entry_of_blkAt_eq_one (by omega) h1 (by omega) (by omega) (by omega) (by omega)
    by_cases hrb : (r : ℕ) < b
    · by_cases hca : (c : ℕ) < a
      · rw [stabilizer_entries ha hca (by omega), Matrix.one_apply_ne (fun h => by subst h; omega)]
      · exact entry_of_blkAt_eq_one (by omega) h2 (by omega) (by omega) (by omega) (by omega)
    · by_cases hcb : (c : ℕ) < b
      · rw [stabilizer_entries hb hcb (by omega), Matrix.one_apply_ne (fun h => by subst h; omega)]
      · exact entry_of_blkAt_eq_one (by omega) h3 (by omega) (by omega) (by omega) (by omega)
  refine ⟨fun r c hcr => ?_, fun r => ?_⟩
  · rw [key r c (le_of_lt hcr), Matrix.one_apply_ne (fun h => by subst h; exact lt_irrefl _ hcr)]
  · rw [key r r le_rfl, Matrix.one_apply_eq]

end Unitri

section Seven

variable {k : ℕ}

theorem eq_one_of_pow_seven_of_blocks {a b : ℕ} (hab : a ≤ b) (hbk : b ≤ k)
    {H : Subgroup (SpecialLinearGroup (Fin k) (ZMod 2))}
    (hHa : ∀ g ∈ H, g ∈ stabilizer (flagSpace k (ZMod 2) a))
    (hHb : ∀ g ∈ H, g ∈ stabilizer (flagSpace k (ZMod 2) b)) {g : ↥H} (hg7 : g ^ 7 = 1)
    (h1 : a ≤ 2 ∨ blkAt 0 a (by omega) ((g : SpecialLinearGroup (Fin k) (ZMod 2)) :
      Matrix (Fin k) (Fin k) (ZMod 2)) = 1)
    (h2 : b - a ≤ 2 ∨ blkAt a (b - a) (by omega) ((g : SpecialLinearGroup (Fin k) (ZMod 2)) :
      Matrix (Fin k) (Fin k) (ZMod 2)) = 1)
    (h3 : k - b ≤ 2 ∨ blkAt b (k - b) (by omega) ((g : SpecialLinearGroup (Fin k) (ZMod 2)) :
      Matrix (Fin k) (Fin k) (ZMod 2)) = 1) : g = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL1 : BlockLeft H 0 a := blockLeft_zero H a
  have hR1 : BlockRight H 0 a := blockRight_of_stabilizer fun g hg => by
    rw [zero_add]
    exact hHa g hg
  have hL2 : BlockLeft H a (b - a) := blockLeft_of_stabilizer hHa
  have hR2 : BlockRight H a (b - a) := blockRight_of_stabilizer fun g hg => by
    rw [Nat.add_sub_cancel' hab]
    exact hHb g hg
  have hL3 : BlockLeft H b (k - b) := blockLeft_of_stabilizer hHb
  have hR3 : BlockRight H b (k - b) := blockRight_top H (by omega)
  have hpow : ∀ (c m : ℕ) (h : c + m ≤ k) (hL : BlockLeft H c m) (hR : BlockRight H c m),
      m ≤ 2 → blkAt c m h ((g : SpecialLinearGroup (Fin k) (ZMod 2)) :
        Matrix (Fin k) (Fin k) (ZMod 2)) = 1 := by
    intro c m h hL hR hm
    have e := congrArg (blkMon H c m h hL hR) hg7
    rw [map_pow, map_one, blkMon_apply] at e
    exact eq_one_of_pow_seven hm e
  have b1 := h1.elim (fun h => hpow 0 a (by omega) hL1 hR1 h) id
  have b2 := h2.elim (fun h => hpow a (b - a) (by omega) hL2 hR2 h) id
  have b3 := h3.elim (fun h => hpow b (k - b) (by omega) hL3 hR3 h) id
  have hu := mem_unitriangular_of_blocks hab hbk (hHa _ g.2) (hHb _ g.2) b1 b2 b3
  by_cases hk : k = 0
  · subst hk
    exact Subtype.ext (Subsingleton.elim _ _)
  obtain ⟨r, hr⟩ := isPGroup_unitriangular_charTwo (K := ZMod 2) (n := k) (by omega) ⟨_, hu⟩
  have hr' : g ^ 2 ^ r = 1 := Subtype.ext (by simpa using congrArg Subtype.val hr)
  have hgcd := (pow_gcd_eq_one).2 ⟨hg7, hr'⟩
  rwa [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right r (by norm_num)), pow_one] at hgcd

end Seven

section Emb

variable {k : ℕ} {R : Type*} [CommRing R]

@[expose] def embAt (a n : ℕ) (M : Matrix (Fin n) (Fin n) R) : Matrix (Fin k) (Fin k) R :=
  Matrix.of fun r c => if hr : a ≤ (r : ℕ) ∧ (r : ℕ) < a + n then
    (if hc : a ≤ (c : ℕ) ∧ (c : ℕ) < a + n then M ⟨r - a, by omega⟩ ⟨c - a, by omega⟩ else 0)
    else (1 : Matrix (Fin k) (Fin k) R) r c

theorem embAt_apply_of_not {a n : ℕ} (M : Matrix (Fin n) (Fin n) R) {r c : Fin k}
    (hr : ¬ (a ≤ (r : ℕ) ∧ (r : ℕ) < a + n)) :
    embAt a n M r c = (1 : Matrix (Fin k) (Fin k) R) r c := by
  simp [embAt, hr]

theorem embAt_apply_of_not' {a n : ℕ} (M : Matrix (Fin n) (Fin n) R) {r c : Fin k}
    (hr : a ≤ (r : ℕ) ∧ (r : ℕ) < a + n) (hc : ¬ (a ≤ (c : ℕ) ∧ (c : ℕ) < a + n)) :
    embAt a n M r c = 0 := by
  simp [embAt, hr, hc]

theorem embAt_apply_block {a n : ℕ} (M : Matrix (Fin n) (Fin n) R) {r c : Fin k}
    (hr : a ≤ (r : ℕ) ∧ (r : ℕ) < a + n) (hc : a ≤ (c : ℕ) ∧ (c : ℕ) < a + n) :
    embAt a n M r c = M ⟨r - a, by omega⟩ ⟨c - a, by omega⟩ := by
  simp [embAt, hr, hc]

theorem embAt_one {a n : ℕ} : embAt (k := k) a n (1 : Matrix (Fin n) (Fin n) R) = 1 := by
  ext r c
  by_cases hr : a ≤ (r : ℕ) ∧ (r : ℕ) < a + n
  · by_cases hc : a ≤ (c : ℕ) ∧ (c : ℕ) < a + n
    · rw [embAt_apply_block _ hr hc]
      by_cases hrc : r = c
      · subst hrc
        rw [Matrix.one_apply_eq, Matrix.one_apply_eq]
      · have : (⟨(r : ℕ) - a, by omega⟩ : Fin n) ≠ ⟨(c : ℕ) - a, by omega⟩ := by
          intro h'
          apply hrc
          have := congrArg Fin.val h'
          simp at this
          exact Fin.ext (by omega)
        rw [Matrix.one_apply_ne this, Matrix.one_apply_ne hrc]
    · rw [embAt_apply_of_not' _ hr hc, Matrix.one_apply_ne (fun h => hc (by subst h; exact hr))]
  · rw [embAt_apply_of_not _ hr]

theorem embAt_mul {a n : ℕ} (h : a + n ≤ k) (M N : Matrix (Fin n) (Fin n) R) :
    embAt (k := k) a n (M * N) = embAt a n M * embAt a n N := by
  ext r c
  rw [Matrix.mul_apply]
  by_cases hr : a ≤ (r : ℕ) ∧ (r : ℕ) < a + n
  · rw [sum_block h (fun l => embAt a n M r l * embAt a n N l c) (fun l hl => by
      have hl' : ¬ (a ≤ (l : ℕ) ∧ (l : ℕ) < a + n) := by omega
      rw [embAt_apply_of_not' _ hr hl', zero_mul])]
    by_cases hc : a ≤ (c : ℕ) ∧ (c : ℕ) < a + n
    · rw [embAt_apply_block _ hr hc, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hi : a ≤ a + (i : ℕ) ∧ a + (i : ℕ) < a + n := ⟨by omega, by have := i.isLt; omega⟩
      rw [embAt_apply_block _ hr hi, embAt_apply_block _ hi hc]
      congr 2 <;> exact Fin.ext (by simp)
    · rw [embAt_apply_of_not' _ hr hc]
      refine (Finset.sum_eq_zero fun i _ => ?_).symm
      have hi : a ≤ a + (i : ℕ) ∧ a + (i : ℕ) < a + n := ⟨by omega, by have := i.isLt; omega⟩
      rw [embAt_apply_of_not' _ hi hc, mul_zero]
  · rw [embAt_apply_of_not _ hr]
    rw [Finset.sum_eq_single r (fun l _ hlr => by
        rw [embAt_apply_of_not _ hr, Matrix.one_apply_ne (Ne.symm hlr), zero_mul])
      (by simp)]
    rw [embAt_apply_of_not _ hr, Matrix.one_apply_eq, one_mul, embAt_apply_of_not _ hr]

theorem blkAt_embAt {a n : ℕ} (h : a + n ≤ k) (M : Matrix (Fin n) (Fin n) R) :
    blkAt a n h (embAt (k := k) a n M) = M := by
  ext i j
  have hi : a ≤ a + (i : ℕ) ∧ a + (i : ℕ) < a + n := ⟨by omega, by have := i.isLt; omega⟩
  have hj : a ≤ a + (j : ℕ) ∧ a + (j : ℕ) < a + n := ⟨by omega, by have := j.isLt; omega⟩
  rw [blkAt_apply, embAt_apply_block _ hi hj]
  congr 1 <;> exact Fin.ext (by simp)

theorem embAt_entries {a n : ℕ} (M : Matrix (Fin n) (Fin n) R) {i : ℕ}
    (hi : i ≤ a ∨ a + n ≤ i) {r c : Fin k} (hr : i ≤ (r : ℕ)) (hc : (c : ℕ) < i) :
    embAt a n M r c = 0 := by
  by_cases hr' : a ≤ (r : ℕ) ∧ (r : ℕ) < a + n
  · have hc' : ¬ (a ≤ (c : ℕ) ∧ (c : ℕ) < a + n) := by omega
    exact embAt_apply_of_not' _ hr' hc'
  · rw [embAt_apply_of_not _ hr', Matrix.one_apply_ne (fun h => by subst h; omega)]

end Emb

section SL

variable {k : ℕ}

theorem det_eq_one_of_mul_eq_one {n : ℕ} {M N : Matrix (Fin n) (Fin n) (ZMod 2)}
    (h : M * N = 1) : M.det = 1 := by
  have h1 : M.det * N.det = 1 := by rw [← Matrix.det_mul, h, Matrix.det_one]
  have h2 : M.det ≠ 0 := left_ne_zero_of_mul_eq_one h1
  revert h2
  generalize M.det = x
  revert x
  decide

@[expose] def embSL (a n : ℕ) (h : a + n ≤ k) :
    SpecialLinearGroup (Fin n) (ZMod 2) →* SpecialLinearGroup (Fin k) (ZMod 2) where
  toFun M := ⟨embAt a n (M : Matrix (Fin n) (Fin n) (ZMod 2)), det_eq_one_of_mul_eq_one
    (N := embAt a n ((M⁻¹ : SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)))
    (by rw [← embAt_mul h, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, embAt_one])⟩
  map_one' := Subtype.ext (by
    show embAt a n ((1 : SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) = 1
    rw [Matrix.SpecialLinearGroup.coe_one, embAt_one])
  map_mul' M N := Subtype.ext (by
    show embAt a n ((M * N : SpecialLinearGroup (Fin n) (ZMod 2)) :
        Matrix (Fin n) (Fin n) (ZMod 2)) =
      embAt a n (M : Matrix (Fin n) (Fin n) (ZMod 2)) *
        embAt a n (N : Matrix (Fin n) (Fin n) (ZMod 2))
    rw [Matrix.SpecialLinearGroup.coe_mul, embAt_mul h])

theorem embSL_mem_stabilizer (a n : ℕ) (h : a + n ≤ k) (M : SpecialLinearGroup (Fin n) (ZMod 2))
    {i : ℕ} (hi : i ≤ a ∨ a + n ≤ i) :
    embSL a n h M ∈ stabilizer (flagSpace k (ZMod 2) i) :=
  mem_stabilizer_of_entries fun _ _ hr hc => embAt_entries _ hi hr hc

@[expose] noncomputable def blkSL2 (H : Subgroup (SpecialLinearGroup (Fin k) (ZMod 2))) (a n : ℕ)
    (h : a + n ≤ k) (hL : BlockLeft H a n) (hR : BlockRight H a n) :
    ↥H →* SpecialLinearGroup (Fin n) (ZMod 2) where
  toFun g := ⟨blkMon H a n h hL hR g, det_eq_one_of_mul_eq_one
    (N := blkMon H a n h hL hR g⁻¹) (by rw [← map_mul, mul_inv_cancel, map_one])⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' g g' := Subtype.ext (map_mul _ g g')

theorem coe_blkSL2 (H : Subgroup (SpecialLinearGroup (Fin k) (ZMod 2))) (a n : ℕ)
    (h : a + n ≤ k) (hL : BlockLeft H a n) (hR : BlockRight H a n) (g : ↥H) :
    ((blkSL2 H a n h hL hR g : SpecialLinearGroup (Fin n) (ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2)) =
      blkAt a n h ((g : SpecialLinearGroup (Fin k) (ZMod 2)) : Matrix (Fin k) (Fin k) (ZMod 2)) :=
  rfl

theorem isSimpleGroup_sl {n : ℕ} (hn : 3 ≤ n) :
    IsSimpleGroup (SpecialLinearGroup (Fin n) (ZMod 2)) := by
  have hc : Subgroup.center (SpecialLinearGroup (Fin n) (ZMod 2)) = ⊥ := by
    rw [eq_bot_iff]
    intro A hA
    obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
    have hr1 : r = 1 := by
      have hr0 : r ≠ 0 := by
        rintro rfl
        rw [zero_pow (by simp; omega)] at hr
        exact zero_ne_one hr
      have key : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
      exact key r hr0
    rw [Subgroup.mem_bot]
    exact Subtype.ext (by rw [← hrA, hr1, map_one, Matrix.SpecialLinearGroup.coe_one])
  have hs := (CFSG.LinearGroups.linear_projective_simple (K := ZMod 2) (n := n) (by omega)
    (Or.inl hn)).2.1
  let e : SpecialLinearGroup (Fin n) (ZMod 2) ≃* ProjectiveSpecialLinearGroup (Fin n) (ZMod 2) :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hc.symm)
  exact e.isSimpleGroup

theorem card_sl {n : ℕ} (hn : 0 < n) :
    Nat.card (SpecialLinearGroup (Fin n) (ZMod 2)) = ∏ i : Fin n, (2 ^ n - 2 ^ (i : ℕ)) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have h := card_SL_mul_card_units (n := Fin n) (R := ZMod 2)
  rw [Matrix.card_GL_field, ZMod.card] at h
  have hu : Nat.card (ZMod 2)ˣ = 1 := by rw [Nat.card_eq_fintype_card]; rfl
  rw [hu, mul_one] at h
  exact h

end SL

section SevenElt

@[expose] def y3 : SpecialLinearGroup (Fin 3) (ZMod 2) := ⟨!![0, 0, 1; 1, 0, 1; 0, 1, 0], by decide⟩

@[expose] def y4 : SpecialLinearGroup (Fin 4) (ZMod 2) :=
  ⟨!![0, 0, 1, 0; 1, 0, 1, 0; 0, 1, 0, 0; 0, 0, 0, 1], by decide⟩

theorem exists_seven {m : ℕ} (hm : m = 3 ∨ m = 4) :
    ∃ y : SpecialLinearGroup (Fin m) (ZMod 2), y ^ 7 = 1 ∧ y ≠ 1 := by
  rcases hm with rfl | rfl
  · refine ⟨y3, Subtype.ext ?_, fun h => ?_⟩
    · decide
    · have := congrArg Subtype.val h
      revert this
      decide
  · refine ⟨y4, Subtype.ext ?_, fun h => ?_⟩
    · decide
    · have := congrArg Subtype.val h
      revert this
      decide

theorem exists_pow_seven_of_map {G G' : Type*} [Group G] [Group G'] [Finite G] (π : G →* G')
    {S : Subgroup G} {s : G} (hs : s ∈ S) {y : G'} (hy : π s = y) (hy7 : y ^ 7 = 1)
    (hy1 : y ≠ 1) : ∃ t ∈ S, t ^ 7 = 1 ∧ t ≠ 1 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hoy : orderOf y = 7 := orderOf_eq_prime hy7 hy1
  have ho : 0 < orderOf s := orderOf_pos s
  have h7 : 7 ∣ orderOf s := by
    rw [← hoy]
    apply orderOf_dvd_of_pow_eq_one
    rw [← hy, ← map_pow, pow_orderOf_eq_one, map_one]
  obtain ⟨q, hq⟩ := h7
  refine ⟨s ^ q, S.pow_mem hs q, ?_, fun h => ?_⟩
  · rw [← pow_mul, mul_comm, ← hq, pow_orderOf_eq_one]
  · have h1 := orderOf_dvd_of_pow_eq_one h
    have hq0 : 0 < q := by
      rcases Nat.eq_zero_or_pos q with h0 | h0
      · rw [h0, mul_zero] at hq
        omega
      · exact h0
    have := Nat.le_of_dvd hq0 h1
    omega

end SevenElt

section Cuts

@[expose] def CutAlt (k : ℕ) (C : Finset ℕ) : Prop :=
  (∃ a ∈ Finset.range 6, ∃ b ∈ Finset.range 6, a ≤ b ∧ b ≤ k ∧ (a = 0 ∨ a ∈ C) ∧
      (b = k ∨ b ∈ C) ∧ a ≤ 2 ∧ b - a ≤ 2 ∧ k - b ≤ 2) ∨
    (∃ a ∈ Finset.range 6, ∃ n ∈ Finset.range 6, 3 ≤ n ∧ a + n ≤ k ∧ (a = 0 ∨ a ∈ C) ∧
      (a + n = k ∨ a + n ∈ C) ∧ ∀ i ∈ C, i ≤ a ∨ a + n ≤ i)

instance (k : ℕ) (C : Finset ℕ) : Decidable (CutAlt k C) := by
  unfold CutAlt
  infer_instance

theorem cutAlt_four : ∀ C ∈ (Finset.Icc 1 3).powerset, CutAlt 4 C := by decide

theorem cutAlt_five : ∀ C ∈ (Finset.Icc 1 4).powerset, CutAlt 5 C := by decide

theorem cuts_alt {k : ℕ} (hk : k = 4 ∨ k = 5) {J : Set ℕ} (hJ : ∀ i ∈ J, 1 ≤ i ∧ i < k) :
    (∃ a b : ℕ, a ≤ b ∧ b ≤ k ∧ (a = 0 ∨ a ∈ J) ∧ (b = k ∨ b ∈ J) ∧ a ≤ 2 ∧ b - a ≤ 2 ∧
      k - b ≤ 2) ∨
    (∃ a n : ℕ, 3 ≤ n ∧ a + n ≤ k ∧ (a = 0 ∨ a ∈ J) ∧ (a + n = k ∨ a + n ∈ J) ∧
      ∀ i ∈ J, i ≤ a ∨ a + n ≤ i) := by
  classical
  set C := (Finset.Icc 1 (k - 1)).filter (· ∈ J) with hC
  have hmem : ∀ i, i ∈ C ↔ i ∈ J := fun i => by
    rw [hC, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · exact fun h => h.2
    · intro h
      have := hJ i h
      exact ⟨⟨this.1, by omega⟩, h⟩
  have hCsub : C ∈ (Finset.Icc 1 (k - 1)).powerset :=
    Finset.mem_powerset.2 (Finset.filter_subset _ _)
  have halt : CutAlt k C := by
    rcases hk with rfl | rfl
    · exact cutAlt_four C hCsub
    · exact cutAlt_five C hCsub
  rcases halt with ⟨a, -, b, -, h1, h2, h3, h4, h5, h6, h7⟩ | ⟨a, -, n, -, h1, h2, h3, h4, h5⟩
  · refine Or.inl ⟨a, b, h1, h2, ?_, ?_, h5, h6, h7⟩
    · rwa [← hmem]
    · rwa [← hmem]
  · refine Or.inr ⟨a, n, h1, h2, ?_, ?_, fun i hi => h5 i ((hmem i).2 hi)⟩
    · rwa [← hmem]
    · rwa [← hmem]

end Cuts

section Block

variable {k : ℕ}

theorem mem_stabilizer_zero (g : SpecialLinearGroup (Fin k) (ZMod 2)) :
    g ∈ stabilizer (flagSpace k (ZMod 2) 0) :=
  mem_stabilizer_of_entries fun _ _ _ hc => absurd hc (Nat.not_lt_zero _)

theorem mem_stabilizer_top (g : SpecialLinearGroup (Fin k) (ZMod 2)) :
    g ∈ stabilizer (flagSpace k (ZMod 2) k) :=
  mem_stabilizer_of_entries fun r _ hr _ => absurd r.isLt (by omega)

theorem mem_stabilizer_of_cut {J : Set ℕ} {g : SpecialLinearGroup (Fin k) (ZMod 2)}
    (hg : g ∈ flagStabilizer k (ZMod 2) J) {a : ℕ} (ha : a = 0 ∨ a = k ∨ a ∈ J) :
    g ∈ stabilizer (flagSpace k (ZMod 2) a) := by
  rcases ha with rfl | rfl | ha
  · exact mem_stabilizer_zero g
  · exact mem_stabilizer_top g
  · exact mem_flagStabilizer.1 hg a ha

theorem exists_block (hk : k = 4 ∨ k = 5) {J : Set ℕ} (hJ : ∀ i ∈ J, 1 ≤ i ∧ i < k)
    {D : Subgroup (SpecialLinearGroup (Fin k) (ZMod 2))}
    (hDQ : D ≤ flagStabilizer k (ZMod 2) J)
    (hQD : flagStabilizer k (ZMod 2) J ≤
      Subgroup.normalizer (D : Set (SpecialLinearGroup (Fin k) (ZMod 2))))
    {m : ℕ} (hm : m = 3 ∨ m = 4) (π : ↥D →* SpecialLinearGroup (Fin m) (ZMod 2))
    (hπ : Function.Surjective π) :
    ∃ a : ℕ, a + m ≤ k ∧ (a = 0 ∨ a ∈ J) ∧ (a + m = k ∨ a + m ∈ J) ∧
      (∀ i ∈ J, i ≤ a ∨ a + m ≤ i) ∧
      ∀ (x : SpecialLinearGroup (Fin k) (ZMod 2)) (hx : x ∈ flagStabilizer k (ZMod 2) J),
        ∃ z : SpecialLinearGroup (Fin m) (ZMod 2),
        ∀ d : ↥D, π ⟨x * d * x⁻¹, (Subgroup.mem_normalizer_iff.mp (hQD hx) d).mp d.2⟩ =
          z * π d * z⁻¹ := by
  set Q := flagStabilizer k (ZMod 2) J with hQdef
  obtain ⟨y, hy7, hy1⟩ := exists_seven hm
  obtain ⟨d₀, hd₀⟩ := hπ y
  rcases cuts_alt hk hJ with ⟨a, b, hab, hbk, ha, hb, h1, h2, h3⟩ | ⟨a, n, hn, hank, ha, han, hJa⟩
  ·
    exfalso
    obtain ⟨t, -, ht7, ht1⟩ := exists_pow_seven_of_map π (Subgroup.mem_top d₀) hd₀ hy7 hy1
    have hHa : ∀ g ∈ Q, g ∈ stabilizer (flagSpace k (ZMod 2) a) := fun g hg =>
      mem_stabilizer_of_cut hg (ha.elim Or.inl fun h => Or.inr (Or.inr h))
    have hHb : ∀ g ∈ Q, g ∈ stabilizer (flagSpace k (ZMod 2) b) := fun g hg =>
      mem_stabilizer_of_cut hg (hb.elim (fun h => Or.inr (Or.inl h)) fun h => Or.inr (Or.inr h))
    have := eq_one_of_pow_seven_of_blocks hab hbk hHa hHb (g := ⟨t, hDQ t.2⟩)
      (Subtype.ext (by simpa using congrArg Subtype.val ht7)) (Or.inl h1) (Or.inl h2) (Or.inl h3)
    have h' : (t : SpecialLinearGroup (Fin k) (ZMod 2)) = 1 := by
      simpa using congrArg Subtype.val this
    exact ht1 (Subtype.ext h')
  ·
    have hHa : ∀ g ∈ Q, g ∈ stabilizer (flagSpace k (ZMod 2) a) := fun g hg =>
      mem_stabilizer_of_cut hg (ha.elim Or.inl fun h => Or.inr (Or.inr h))
    have hHb : ∀ g ∈ Q, g ∈ stabilizer (flagSpace k (ZMod 2) (a + n)) := fun g hg =>
      mem_stabilizer_of_cut hg (han.elim (fun h => Or.inr (Or.inl h)) fun h => Or.inr (Or.inr h))
    have hL : BlockLeft Q a n := blockLeft_of_stabilizer hHa
    have hR : BlockRight Q a n := blockRight_of_stabilizer hHb
    set ℓ := blkSL2 Q a n hank hL hR with hℓ
    have hℓs : Function.Surjective ℓ := by
      intro M
      have hM : embSL a n hank M ∈ Q := mem_flagStabilizer.2 fun i hi =>
        embSL_mem_stabilizer a n hank M (hJa i hi)
      refine ⟨⟨_, hM⟩, Subtype.ext ?_⟩
      rw [coe_blkSL2]
      exact blkAt_embAt hank _
    set ℓD := ℓ.comp (Subgroup.inclusion hDQ) with hℓD
    have hn' : ¬ ∃ t : ↥D, t ∈ ℓD.ker ∧ t ^ 7 = 1 ∧ t ≠ 1 := by
      rintro ⟨t, ht, ht7, ht1⟩
      have h2 : blkAt a n hank ((t : SpecialLinearGroup (Fin k) (ZMod 2)) :
          Matrix (Fin k) (Fin k) (ZMod 2)) = 1 := by
        have h1 : ℓD t = 1 := ht
        have h2 := congrArg (fun A : SpecialLinearGroup (Fin n) (ZMod 2) =>
          (A : Matrix (Fin n) (Fin n) (ZMod 2))) h1
        simpa [hℓD, hℓ, coe_blkSL2, MonoidHom.comp_apply, Matrix.SpecialLinearGroup.coe_one]
          using h2
      have hb2 : blkAt a (a + n - a) (by omega) ((t : SpecialLinearGroup (Fin k) (ZMod 2)) :
          Matrix (Fin k) (Fin k) (ZMod 2)) = 1 := by
        ext i j
        have e := congrFun (congrFun h2 ⟨i, by omega⟩) ⟨j, by omega⟩
        rw [blkAt_apply] at e ⊢
        rw [e, Matrix.one_apply, Matrix.one_apply]
        simp [Fin.ext_iff]
      have := eq_one_of_pow_seven_of_blocks (by omega) hank hHa hHb (g := ⟨t, hDQ t.2⟩)
        (Subtype.ext (by simpa using congrArg Subtype.val ht7)) (Or.inl (by omega))
        (Or.inr hb2) (Or.inl (by omega))
      have h' : (t : SpecialLinearGroup (Fin k) (ZMod 2)) = 1 := by
        simpa using congrArg Subtype.val this
      exact ht1 (Subtype.ext h')
    have hsm := isSimpleGroup_sl (by rcases hm with rfl | rfl <;> norm_num : 3 ≤ m)
    have hker : ℓD.ker ≤ π.ker := by
      have hN : (ℓD.ker.map π).Normal := (MonoidHom.normal_ker ℓD).map π hπ
      rcases hN.eq_bot_or_eq_top with h0 | htop
      · intro t ht
        have : π t ∈ ℓD.ker.map π := ⟨t, ht, rfl⟩
        rwa [h0, Subgroup.mem_bot] at this
      · exfalso
        have : y ∈ ℓD.ker.map π := htop ▸ Subgroup.mem_top y
        obtain ⟨s, hs, hsy⟩ := this
        obtain ⟨t, ht, ht7, ht1⟩ := exists_pow_seven_of_map π hs hsy hy7 hy1
        exact hn' ⟨t, ht, ht7, ht1⟩
    have hsn := isSimpleGroup_sl hn
    have hℓDs : Function.Surjective ℓD := by
      have hnorm : (D.subgroupOf Q).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hDQ).2 hQD
      have hN := hnorm.map ℓ hℓs
      have hrange : (D.subgroupOf Q).map ℓ = ℓD.range := by
        ext M
        constructor
        · rintro ⟨q, hq, rfl⟩
          exact ⟨⟨q, hq⟩, rfl⟩
        · rintro ⟨d, rfl⟩
          exact ⟨Subgroup.inclusion hDQ d, d.2, rfl⟩
      rw [hrange] at hN
      rcases hN.eq_bot_or_eq_top with h0 | htop
      · exfalso
        apply hy1
        rw [← hd₀]
        exact hker (show d₀ ∈ ℓD.ker from (MonoidHom.range_eq_bot_iff.1 h0) ▸ rfl)
      · exact MonoidHom.range_eq_top.1 htop
    set φ := (MonoidHom.liftOfSurjective ℓD hℓDs) ⟨π, hker⟩ with hφ
    have hφℓ : ∀ d : ↥D, φ (ℓD d) = π d := fun d =>
      MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ d
    have hφs : Function.Surjective φ := fun z => by
      obtain ⟨d, rfl⟩ := hπ z
      exact ⟨ℓD d, hφℓ d⟩
    have hφi : Function.Injective φ := by
      rw [← MonoidHom.ker_eq_bot_iff]
      rcases (MonoidHom.normal_ker φ).eq_bot_or_eq_top with h0 | htop
      · exact h0
      · exfalso
        apply hy1
        rw [← hd₀, ← hφℓ]
        exact (MonoidHom.mem_ker).1 (htop ▸ Subgroup.mem_top _)
    have hnm : n = m := by
      have hc := Nat.card_congr (Equiv.ofBijective φ ⟨hφi, hφs⟩)
      rw [card_sl (by omega), card_sl (by rcases hm with rfl | rfl <;> norm_num)] at hc
      have hn5 : n ≤ 5 := by omega
      rcases hm with rfl | rfl <;> interval_cases n <;> simp [Fin.prod_univ_succ] at hc ⊢
    subst hnm
    refine ⟨a, hank, ha, han, hJa, fun x hx => ⟨φ (ℓ ⟨x, hx⟩), fun d => ?_⟩⟩
    rw [← hφℓ, ← hφℓ, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    simp only [hℓD, MonoidHom.comp_apply]
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1

end Block

end CFSG.Quasithin.H13.NQCat.SLk
