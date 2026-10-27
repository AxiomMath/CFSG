module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11OrthFrOddC1

public section

set_option maxRecDepth 100000

open scoped Matrix Pointwise

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup

private theorem getD_eq_ofDigits_div_pow_mod {b : ℕ} (hb : 0 < b) {l : List ℕ}
    (hl : ∀ x ∈ l, x < b) (m : ℕ) : l.getD m 0 = Nat.ofDigits b l / b ^ m % b := by
  rw [Nat.ofDigits_div_pow_eq_ofDigits_drop m hb l hl, Nat.ofDigits_mod_eq_head!,
    List.getD_eq_getElem?_getD, ← List.head?_drop]
  cases h : l.drop m with
  | nil => simp
  | cons x t =>
    have hx : x ∈ l := List.mem_of_mem_drop (h ▸ List.mem_cons_self)
    simp [Nat.mod_eq_of_lt (hl x hx)]

private theorem s16c11_fr_tcodes4_lt : ∀ x ∈ s16c11_fr_tcodes4, x < 256 := by
  decide +kernel

private theorem s16c11_fr_tcode4_eq_ofDigits (i : Fin 8) (n : ℕ) :
    s16c11_fr_tcode4 i n = Nat.ofDigits 256 s16c11_fr_tcodes4 / 256 ^ (i.1 * 256 + n) % 256 :=
  getD_eq_ofDigits_div_pow_mod (by norm_num) s16c11_fr_tcodes4_lt _

private theorem s16c11_fr_ofNat_xor (m a b : ℕ) :
    s16c11_fr_ofNat m (a ^^^ b) = s16c11_fr_ofNat m a + s16c11_fr_ofNat m b := by
  funext c
  simp only [s16c11_fr_ofNat, Pi.add_apply, Nat.testBit_xor]
  cases a.testBit (s16c11_fr_bit m c) <;> cases b.testBit (s16c11_fr_bit m c) <;> decide

private theorem s16c11_fr_mulVec_ofNat4_of_basis
    (M : Matrix (S16C11FrIdx 4) (S16C11FrIdx 4) (ZMod 2)) (T : ℕ → ℕ)
    (h : T 0 = 0 ∧
      (∀ b : Fin 8, M *ᵥ s16c11_fr_ofNat 4 (2 ^ b.1) = s16c11_fr_ofNat 4 (T (2 ^ b.1))) ∧
      ∀ n : Fin 256, 0 < n.1 → (n.1 - 2 ^ n.1.log2) ^^^ 2 ^ n.1.log2 = n.1 ∧
        T n.1 = T (n.1 - 2 ^ n.1.log2) ^^^ T (2 ^ n.1.log2)) :
    ∀ n : Fin 256, M *ᵥ s16c11_fr_ofNat 4 n.1 = s16c11_fr_ofNat 4 (T n.1) := by
  obtain ⟨h0, hbasis, hsplit⟩ := h
  intro ⟨n, hn⟩
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    show M *ᵥ s16c11_fr_ofNat 4 n = s16c11_fr_ofNat 4 (T n)
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · have hz : s16c11_fr_ofNat 4 0 = 0 := by
        funext c
        simp [s16c11_fr_ofNat]
      rw [h0, hz, Matrix.mulVec_zero]
    · obtain ⟨hxor, hT⟩ : (n - 2 ^ n.log2) ^^^ 2 ^ n.log2 = n ∧
          T n = T (n - 2 ^ n.log2) ^^^ T (2 ^ n.log2) := hsplit ⟨n, hn⟩ hpos
      have hlog : n.log2 < 8 := (Nat.log2_lt (Nat.pos_iff_ne_zero.1 hpos)).2 hn
      have hlt : n - 2 ^ n.log2 < n := Nat.sub_lt hpos (Nat.two_pow_pos _)
      have ih' : M *ᵥ s16c11_fr_ofNat 4 (n - 2 ^ n.log2) =
          s16c11_fr_ofNat 4 (T (n - 2 ^ n.log2)) :=
        ih _ hlt (lt_of_le_of_lt (Nat.sub_le _ _) hn)
      have hb : M *ᵥ s16c11_fr_ofNat 4 (2 ^ n.log2) = s16c11_fr_ofNat 4 (T (2 ^ n.log2)) :=
        hbasis ⟨n.log2, hlog⟩
      calc M *ᵥ s16c11_fr_ofNat 4 n
          = M *ᵥ (s16c11_fr_ofNat 4 (n - 2 ^ n.log2) + s16c11_fr_ofNat 4 (2 ^ n.log2)) := by
            rw [← s16c11_fr_ofNat_xor, hxor]
        _ = s16c11_fr_ofNat 4 (T (n - 2 ^ n.log2)) + s16c11_fr_ofNat 4 (T (2 ^ n.log2)) := by
            rw [Matrix.mulVec_add, ih', hb]
        _ = s16c11_fr_ofNat 4 (T n) := by rw [hT, s16c11_fr_ofNat_xor]

theorem s16c11_fr_tcode_Q4 : ∀ (i : Fin 8) (n : Fin 256),
    S16C11FrQ 4 (s16c11_fr_ofNat 4 (s16c11_fr_tcode4 i n.1)) =
      S16C11FrQ 4 (s16c11_fr_ofNat 4 n.1) := by
  simp only [s16c11_fr_tcode4_eq_ofDigits]
  decide +kernel

theorem s16c11_fr_tcode_invol4 : ∀ (i : Fin 8) (n : Fin 256),
    s16c11_fr_tcode4 i (s16c11_fr_tcode4 i n.1) = n.1 := by
  simp only [s16c11_fr_tcode4_eq_ofDigits]
  decide +kernel

theorem s16c11_fr_mat_mulVec_code4_0 : ∀ n : Fin 256,
    Matrix.of (s16c11_fr_mat4 0) *ᵥ s16c11_fr_ofNat 4 n.1 =
      s16c11_fr_ofNat 4 (s16c11_fr_tcode4 0 n.1) :=
  s16c11_fr_mulVec_ofNat4_of_basis _ _ (by
    simp only [s16c11_fr_tcode4_eq_ofDigits]
    decide +kernel)

theorem s16c11_fr_mat_mulVec_code4_1 : ∀ n : Fin 256,
    Matrix.of (s16c11_fr_mat4 1) *ᵥ s16c11_fr_ofNat 4 n.1 =
      s16c11_fr_ofNat 4 (s16c11_fr_tcode4 1 n.1) :=
  s16c11_fr_mulVec_ofNat4_of_basis _ _ (by
    simp only [s16c11_fr_tcode4_eq_ofDigits]
    decide +kernel)

theorem s16c11_fr_mat_mulVec_code4_2 : ∀ n : Fin 256,
    Matrix.of (s16c11_fr_mat4 2) *ᵥ s16c11_fr_ofNat 4 n.1 =
      s16c11_fr_ofNat 4 (s16c11_fr_tcode4 2 n.1) :=
  s16c11_fr_mulVec_ofNat4_of_basis _ _ (by
    simp only [s16c11_fr_tcode4_eq_ofDigits]
    decide +kernel)

theorem s16c11_fr_mat_mulVec_code4_3 : ∀ n : Fin 256,
    Matrix.of (s16c11_fr_mat4 3) *ᵥ s16c11_fr_ofNat 4 n.1 =
      s16c11_fr_ofNat 4 (s16c11_fr_tcode4 3 n.1) :=
  s16c11_fr_mulVec_ofNat4_of_basis _ _ (by
    simp only [s16c11_fr_tcode4_eq_ofDigits]
    decide +kernel)

theorem s16c11_fr_mat_mulVec_code4_4 : ∀ n : Fin 256,
    Matrix.of (s16c11_fr_mat4 4) *ᵥ s16c11_fr_ofNat 4 n.1 =
      s16c11_fr_ofNat 4 (s16c11_fr_tcode4 4 n.1) :=
  s16c11_fr_mulVec_ofNat4_of_basis _ _ (by
    simp only [s16c11_fr_tcode4_eq_ofDigits]
    decide +kernel)

theorem s16c11_fr_mat_mulVec_code4_5 : ∀ n : Fin 256,
    Matrix.of (s16c11_fr_mat4 5) *ᵥ s16c11_fr_ofNat 4 n.1 =
      s16c11_fr_ofNat 4 (s16c11_fr_tcode4 5 n.1) :=
  s16c11_fr_mulVec_ofNat4_of_basis _ _ (by
    simp only [s16c11_fr_tcode4_eq_ofDigits]
    decide +kernel)

theorem s16c11_fr_mat_mulVec_code4_6 : ∀ n : Fin 256,
    Matrix.of (s16c11_fr_mat4 6) *ᵥ s16c11_fr_ofNat 4 n.1 =
      s16c11_fr_ofNat 4 (s16c11_fr_tcode4 6 n.1) :=
  s16c11_fr_mulVec_ofNat4_of_basis _ _ (by
    simp only [s16c11_fr_tcode4_eq_ofDigits]
    decide +kernel)

theorem s16c11_fr_mat_mulVec_code4_7 : ∀ n : Fin 256,
    Matrix.of (s16c11_fr_mat4 7) *ᵥ s16c11_fr_ofNat 4 n.1 =
      s16c11_fr_ofNat 4 (s16c11_fr_tcode4 7 n.1) :=
  s16c11_fr_mulVec_ofNat4_of_basis _ _ (by
    simp only [s16c11_fr_tcode4_eq_ofDigits]
    decide +kernel)

theorem s16c11_fr_mat_mulVec_code4 : ∀ (i : Fin 8) (n : Fin 256),
    Matrix.of (s16c11_fr_mat4 i) *ᵥ s16c11_fr_ofNat 4 n.1 =
      s16c11_fr_ofNat 4 (s16c11_fr_tcode4 i n.1) := by
  intro i n
  fin_cases i
  · exact s16c11_fr_mat_mulVec_code4_0 n
  · exact s16c11_fr_mat_mulVec_code4_1 n
  · exact s16c11_fr_mat_mulVec_code4_2 n
  · exact s16c11_fr_mat_mulVec_code4_3 n
  · exact s16c11_fr_mat_mulVec_code4_4 n
  · exact s16c11_fr_mat_mulVec_code4_5 n
  · exact s16c11_fr_mat_mulVec_code4_6 n
  · exact s16c11_fr_mat_mulVec_code4_7 n

theorem s16c11_fr_ofNat_basis4 : ∀ c : S16C11FrIdx 4,
    s16c11_fr_ofNat 4 (2 ^ s16c11_fr_bit 4 c) = Pi.single c 1 := by
  intro c
  revert c
  decide +kernel

theorem s16c11_fr_basis_lt4 : ∀ c : S16C11FrIdx 4,
    2 ^ s16c11_fr_bit 4 c < 256 := by
  intro c
  revert c
  decide +kernel

theorem s16c11_fr_tcode_lt4 : ∀ (i : Fin 8) (n : Fin 256),
    s16c11_fr_tcode4 i n.1 < 256 := by
  intro i n
  rw [s16c11_fr_tcode4_eq_ofDigits]
  exact Nat.mod_lt _ (by norm_num)

theorem s16c11_fr_mat_self4 : ∀ i : Fin 8,
    Matrix.of (s16c11_fr_mat4 i) * Matrix.of (s16c11_fr_mat4 i) = 1 := by
  intro i
  apply Matrix.ext_of_mulVec_single
  intro c
  have hc : s16c11_fr_ofNat 4 (2 ^ s16c11_fr_bit 4 c) = Pi.single c 1 :=
    s16c11_fr_ofNat_basis4 c
  have hbc : 2 ^ s16c11_fr_bit 4 c < 256 := s16c11_fr_basis_lt4 c
  rw [← hc, ← Matrix.mulVec_mulVec,
    s16c11_fr_mat_mulVec_code4 i ⟨_, hbc⟩,
    s16c11_fr_mat_mulVec_code4 i ⟨_, s16c11_fr_tcode_lt4 i ⟨_, hbc⟩⟩,
    s16c11_fr_tcode_invol4 i ⟨_, hbc⟩, Matrix.one_mulVec]

theorem s16c11_fr_mat_iso4 : ∀ i : Fin 8, ∀ v : S16C11FrVec 4,
    S16C11FrQ 4 (Matrix.of (s16c11_fr_mat4 i) *ᵥ v) = S16C11FrQ 4 v := by
  intro i v
  have hv : s16c11_fr_ofNat 4 (s16c11_fr_nat 4 v) = v :=
    s16c11_fr_ofNat_nat (show (4 : ℕ) = 3 ∨ (4 : ℕ) = 4 from Or.inr rfl) v
  have hlt : s16c11_fr_nat 4 v < 256 :=
    s16c11_fr_nat_lt (show (4 : ℕ) = 3 ∨ (4 : ℕ) = 4 from Or.inr rfl) v
  calc S16C11FrQ 4 (Matrix.of (s16c11_fr_mat4 i) *ᵥ v)
      = S16C11FrQ 4 (Matrix.of (s16c11_fr_mat4 i) *ᵥ
          s16c11_fr_ofNat 4 (s16c11_fr_nat 4 v)) := by rw [hv]
    _ = S16C11FrQ 4 (s16c11_fr_ofNat 4 (s16c11_fr_tcode4 i
          (s16c11_fr_nat 4 v))) := by
        rw [s16c11_fr_mat_mulVec_code4 i ⟨_, hlt⟩]
    _ = S16C11FrQ 4 (s16c11_fr_ofNat 4 (s16c11_fr_nat 4 v)) :=
        s16c11_fr_tcode_Q4 i ⟨_, hlt⟩
    _ = S16C11FrQ 4 v := by rw [hv]

theorem s16c11_fr_codeTriple_lt4 : ∀ k : Fin 1071,
    (s16c11_fr_codeTriple4 k).1 < 256 ∧
      (s16c11_fr_codeTriple4 k).2.1 < 256 ∧
      (s16c11_fr_codeTriple4 k).2.2 < 256 :=
  s16c11_fr_codeTriple4_lt4

theorem s16c11_fr_image_decode4 (i : Fin 8) (t : ℕ × ℕ × ℕ) (h1 : t.1 < 256)
    (h2 : t.2.1 < 256) (h3 : t.2.2 < 256) :
    (s16c11_fr_decode 4 t).image (fun x => Matrix.of (s16c11_fr_mat4 i) *ᵥ x) =
      s16c11_fr_decode 4 (s16c11_fr_sort3 (s16c11_fr_tcode4 i t.1)
        (s16c11_fr_tcode4 i t.2.1) (s16c11_fr_tcode4 i t.2.2)) := by
  have e1 := s16c11_fr_mat_mulVec_code4 i ⟨t.1, h1⟩
  have e2 := s16c11_fr_mat_mulVec_code4 i ⟨t.2.1, h2⟩
  have e3 := s16c11_fr_mat_mulVec_code4 i ⟨t.2.2, h3⟩
  rw [s16c11_fr_decode_sort3]
  simp only [s16c11_fr_decode, Finset.image_insert, Finset.image_singleton, e1, e2, e3]

private theorem s16c11_fr_pars4_lt : ∀ x ∈ s16c11_fr_pars4, x < 2048 := by
  decide +kernel

private theorem s16c11_fr_gis4_lt : ∀ x ∈ s16c11_fr_gis4, x < 8 := by
  decide +kernel

private theorem s16c11_fr_trips4_fst_lt : ∀ x ∈ s16c11_fr_trips4.map (·.1), x < 256 := by
  decide +kernel

private theorem s16c11_fr_trips4_snd_lt : ∀ x ∈ s16c11_fr_trips4.map (·.2.1), x < 256 := by
  decide +kernel

private theorem s16c11_fr_trips4_thd_lt : ∀ x ∈ s16c11_fr_trips4.map (·.2.2), x < 256 := by
  decide +kernel

private theorem s16c11_fr_trips4_getD (k : ℕ) : s16c11_fr_trips4.getD k (0, 0, 0) =
    ((s16c11_fr_trips4.map (·.1)).getD k 0, (s16c11_fr_trips4.map (·.2.1)).getD k 0,
      (s16c11_fr_trips4.map (·.2.2)).getD k 0) := by
  rw [List.getD_map _ (0, 0, 0) (·.1), List.getD_map _ (0, 0, 0) (·.2.1),
    List.getD_map _ (0, 0, 0) (·.2.2)]

theorem s16c11_fr_stepNat4 : ∀ k : Fin 1071,
    s16c11_fr_codeTriple4 k = s16c11_fr_codeTriple4 0 ∨
      (s16c11_fr_par4 k < k ∧
        s16c11_fr_imgTriple4 k = s16c11_fr_codeTriple4 k) := by
  simp only [s16c11_fr_imgTriple4, s16c11_fr_codeTriple4, s16c11_fr_par4, s16c11_fr_genIdx4,
    s16c11_fr_tcode4, s16c11_fr_trips4_getD,
    getD_eq_ofDigits_div_pow_mod (by norm_num) s16c11_fr_tcodes4_lt,
    getD_eq_ofDigits_div_pow_mod (by norm_num) s16c11_fr_pars4_lt,
    getD_eq_ofDigits_div_pow_mod (by norm_num) s16c11_fr_gis4_lt,
    getD_eq_ofDigits_div_pow_mod (by norm_num) s16c11_fr_trips4_fst_lt,
    getD_eq_ofDigits_div_pow_mod (by norm_num) s16c11_fr_trips4_snd_lt,
    getD_eq_ofDigits_div_pow_mod (by norm_num) s16c11_fr_trips4_thd_lt]
  decide +kernel

@[expose] def s16c11_fr_tau4 (i : Fin 8) : ↥(S16C11FrO 4) where
  val := ⟨Matrix.of (s16c11_fr_mat4 i), Matrix.of (s16c11_fr_mat4 i),
    s16c11_fr_mat_self4 i, s16c11_fr_mat_self4 i⟩
  property := by
    apply Subgroup.subset_closure
    intro v
    exact s16c11_fr_mat_iso4 i v

theorem s16c11_fr_line_zero4 : s16c11_fr_line4 0 = s16c11FrLine 4 := by
  decide +kernel

theorem s16c11_fr_step4 : ∀ k : Fin 1071,
    s16c11_fr_line4 k = s16c11_fr_line4 0 ∨
      (s16c11_fr_par4 k < k ∧
        (s16c11_fr_line4 (s16c11_fr_par4 k)).image
          (fun x => Matrix.of (s16c11_fr_mat4 (s16c11_fr_genIdx4 k)) *ᵥ x) =
        s16c11_fr_line4 k) := by
  intro k
  obtain ⟨h1, h2, h3⟩ := s16c11_fr_codeTriple_lt4 (s16c11_fr_par4 k)
  rcases s16c11_fr_stepNat4 k with h | ⟨hp, himg⟩
  · left
    rw [s16c11_fr_line4, s16c11_fr_line4, h]
  · right
    refine ⟨hp, ?_⟩
    unfold s16c11_fr_line4
    rw [s16c11_fr_image_decode4 (s16c11_fr_genIdx4 k)
      (s16c11_fr_codeTriple4 (s16c11_fr_par4 k)) h1 h2 h3]
    change s16c11_fr_decode 4 (s16c11_fr_imgTriple4 k) =
      s16c11_fr_decode 4 (s16c11_fr_codeTriple4 k)
    rw [himg]

theorem s16c11_fr_table_orbit4 :
    ∀ k : Fin 1071,
      s16c11_fr_line4 k ∈ MulAction.orbit ↥(S16C11FrO 4) (s16c11FrLine 4) := by
  intro k
  refine Fin.strong_induction_on (motive := fun k =>
    s16c11_fr_line4 k ∈ MulAction.orbit ↥(S16C11FrO 4) (s16c11FrLine 4)) ?_ k
  intro j ih
  rcases s16c11_fr_step4 j with h | ⟨hlt, himg⟩
  · rw [h, s16c11_fr_line_zero4]
    exact MulAction.mem_orbit_self _
  · have hprev := ih (s16c11_fr_par4 j) hlt
    have hact : s16c11_fr_tau4 (s16c11_fr_genIdx4 j) • s16c11_fr_line4 (s16c11_fr_par4 j) =
        s16c11_fr_line4 j := by
      show (s16c11_fr_line4 (s16c11_fr_par4 j)).image
        (fun x => Matrix.of (s16c11_fr_mat4 (s16c11_fr_genIdx4 j)) *ᵥ x) =
        s16c11_fr_line4 j
      exact himg
    rw [← hact]
    exact MulAction.mem_orbit_of_mem_orbit _ hprev

theorem s16c11_fr_tableSet_subset_orbit4 :
    (s16c11_fr_tableSet4 : Set (Finset (S16C11FrVec 4))) ⊆
      MulAction.orbit ↥(S16C11FrO 4) (s16c11FrLine 4) := by
  intro L hL
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hL
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 ht
  exact s16c11_fr_table_orbit4 k

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
