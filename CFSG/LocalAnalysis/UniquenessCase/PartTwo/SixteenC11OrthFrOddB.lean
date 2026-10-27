module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11OrthFrOddA

public section

set_option maxRecDepth 100000

open scoped Matrix Pointwise

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup

@[expose] def s16c11_fr_rows3 (i : Fin 6) : List ℕ :=
  if i.1 = 0 then
    [      1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0,
      0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1]
  else if i.1 = 1 then
    [      0, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1,
      1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1]
  else if i.1 = 2 then
    [      1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 1, 0, 0, 1, 1, 1,
      0, 1, 0, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1]
  else if i.1 = 3 then
    [      0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1,
      1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1]
  else if i.1 = 4 then
    [      1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0,
      0, 1, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 1]
  else if i.1 = 5 then
    [      1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0,
      0, 1, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1]
  else []

@[expose] def s16c11_fr_mat3 (i : Fin 6) (c d : S16C11FrIdx 3) : ZMod 2 :=
  if (s16c11_fr_rows3 i).getD (s16c11_fr_bit 3 c * 6 + s16c11_fr_bit 3 d) 0 = 1
    then 1 else 0

@[expose] def s16c11_fr_tcodes3 : List ℕ :=
  [
  0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14,
  15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29,
  30, 31, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60,
  61, 62, 63, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43,
  44, 45, 46, 47, 0, 46, 45, 3, 43, 5, 6, 40, 39, 9, 10,
  36, 12, 34, 33, 15, 63, 17, 18, 60, 20, 58, 57, 23, 24, 54,
  53, 27, 51, 29, 30, 48, 32, 14, 13, 35, 11, 37, 38, 8, 7,
  41, 42, 4, 44, 2, 1, 47, 31, 49, 50, 28, 52, 26, 25, 55,
  56, 22, 21, 59, 19, 61, 62, 16, 0, 29, 30, 3, 4, 25, 26,
  7, 8, 21, 22, 11, 12, 17, 18, 15, 16, 13, 14, 19, 20, 9,
  10, 23, 24, 5, 6, 27, 28, 1, 2, 31, 60, 33, 34, 63, 56,
  37, 38, 59, 52, 41, 42, 55, 48, 45, 46, 51, 44, 49, 50, 47,
  40, 53, 54, 43, 36, 57, 58, 39, 32, 61, 62, 35, 0, 12, 15,
  3, 9, 5, 6, 10, 8, 4, 7, 11, 1, 13, 14, 2, 16, 28,
  31, 19, 25, 21, 22, 26, 24, 20, 23, 27, 17, 29, 30, 18, 32,
  44, 47, 35, 41, 37, 38, 42, 40, 36, 39, 43, 33, 45, 46, 34,
  48, 60, 63, 51, 57, 53, 54, 58, 56, 52, 55, 59, 49, 61, 62,
  50, 0, 1, 2, 3, 4, 5, 6, 7, 26, 27, 24, 25, 30, 31,
  28, 29, 16, 17, 18, 19, 20, 21, 22, 23, 10, 11, 8, 9, 14,
  15, 12, 13, 50, 51, 48, 49, 54, 55, 52, 53, 40, 41, 42, 43,
  44, 45, 46, 47, 34, 35, 32, 33, 38, 39, 36, 37, 56, 57, 58,
  59, 60, 61, 62, 63, 0, 21, 2, 23, 4, 17, 6, 19, 8, 29,
  10, 31, 12, 25, 14, 27, 16, 5, 18, 7, 20, 1, 22, 3, 24,
  13, 26, 15, 28, 9, 30, 11, 52, 33, 54, 35, 48, 37, 50, 39,
  60, 41, 62, 43, 56, 45, 58, 47, 36, 49, 38, 51, 32, 53, 34,
  55, 44, 57, 46, 59, 40, 61, 42, 63]

@[expose] def s16c11_fr_tcode3 (i : Fin 6) (n : ℕ) : ℕ :=
  s16c11_fr_tcodes3.getD (i.1 * 64 + n) 0

theorem s16c11_fr_mat_mulVec_code3_0 : ∀ n : Fin 64,
    Matrix.of (s16c11_fr_mat3 0) *ᵥ s16c11_fr_ofNat 3 n.1 =
      s16c11_fr_ofNat 3 (s16c11_fr_tcode3 0 n.1) := by
  decide +kernel

theorem s16c11_fr_tcode_Q3_0 : ∀ n : Fin 64,
    S16C11FrQ 3 (s16c11_fr_ofNat 3 (s16c11_fr_tcode3 0 n.1)) =
      S16C11FrQ 3 (s16c11_fr_ofNat 3 n.1) := by
  decide +kernel

theorem s16c11_fr_tcode_invol3_0 : ∀ n : Fin 64,
    s16c11_fr_tcode3 0 (s16c11_fr_tcode3 0 n.1) = n.1 := by
  decide +kernel

theorem s16c11_fr_mat_mulVec_code3_1 : ∀ n : Fin 64,
    Matrix.of (s16c11_fr_mat3 1) *ᵥ s16c11_fr_ofNat 3 n.1 =
      s16c11_fr_ofNat 3 (s16c11_fr_tcode3 1 n.1) := by
  decide +kernel

theorem s16c11_fr_tcode_Q3_1 : ∀ n : Fin 64,
    S16C11FrQ 3 (s16c11_fr_ofNat 3 (s16c11_fr_tcode3 1 n.1)) =
      S16C11FrQ 3 (s16c11_fr_ofNat 3 n.1) := by
  decide +kernel

theorem s16c11_fr_tcode_invol3_1 : ∀ n : Fin 64,
    s16c11_fr_tcode3 1 (s16c11_fr_tcode3 1 n.1) = n.1 := by
  decide +kernel

theorem s16c11_fr_mat_mulVec_code3_2 : ∀ n : Fin 64,
    Matrix.of (s16c11_fr_mat3 2) *ᵥ s16c11_fr_ofNat 3 n.1 =
      s16c11_fr_ofNat 3 (s16c11_fr_tcode3 2 n.1) := by
  decide +kernel

theorem s16c11_fr_tcode_Q3_2 : ∀ n : Fin 64,
    S16C11FrQ 3 (s16c11_fr_ofNat 3 (s16c11_fr_tcode3 2 n.1)) =
      S16C11FrQ 3 (s16c11_fr_ofNat 3 n.1) := by
  decide +kernel

theorem s16c11_fr_tcode_invol3_2 : ∀ n : Fin 64,
    s16c11_fr_tcode3 2 (s16c11_fr_tcode3 2 n.1) = n.1 := by
  decide +kernel

theorem s16c11_fr_mat_mulVec_code3_3 : ∀ n : Fin 64,
    Matrix.of (s16c11_fr_mat3 3) *ᵥ s16c11_fr_ofNat 3 n.1 =
      s16c11_fr_ofNat 3 (s16c11_fr_tcode3 3 n.1) := by
  decide +kernel

theorem s16c11_fr_tcode_Q3_3 : ∀ n : Fin 64,
    S16C11FrQ 3 (s16c11_fr_ofNat 3 (s16c11_fr_tcode3 3 n.1)) =
      S16C11FrQ 3 (s16c11_fr_ofNat 3 n.1) := by
  decide +kernel

theorem s16c11_fr_tcode_invol3_3 : ∀ n : Fin 64,
    s16c11_fr_tcode3 3 (s16c11_fr_tcode3 3 n.1) = n.1 := by
  decide +kernel

theorem s16c11_fr_mat_mulVec_code3_4 : ∀ n : Fin 64,
    Matrix.of (s16c11_fr_mat3 4) *ᵥ s16c11_fr_ofNat 3 n.1 =
      s16c11_fr_ofNat 3 (s16c11_fr_tcode3 4 n.1) := by
  decide +kernel

theorem s16c11_fr_tcode_Q3_4 : ∀ n : Fin 64,
    S16C11FrQ 3 (s16c11_fr_ofNat 3 (s16c11_fr_tcode3 4 n.1)) =
      S16C11FrQ 3 (s16c11_fr_ofNat 3 n.1) := by
  decide +kernel

theorem s16c11_fr_tcode_invol3_4 : ∀ n : Fin 64,
    s16c11_fr_tcode3 4 (s16c11_fr_tcode3 4 n.1) = n.1 := by
  decide +kernel

theorem s16c11_fr_mat_mulVec_code3_5 : ∀ n : Fin 64,
    Matrix.of (s16c11_fr_mat3 5) *ᵥ s16c11_fr_ofNat 3 n.1 =
      s16c11_fr_ofNat 3 (s16c11_fr_tcode3 5 n.1) := by
  decide +kernel

theorem s16c11_fr_tcode_Q3_5 : ∀ n : Fin 64,
    S16C11FrQ 3 (s16c11_fr_ofNat 3 (s16c11_fr_tcode3 5 n.1)) =
      S16C11FrQ 3 (s16c11_fr_ofNat 3 n.1) := by
  decide +kernel

theorem s16c11_fr_tcode_invol3_5 : ∀ n : Fin 64,
    s16c11_fr_tcode3 5 (s16c11_fr_tcode3 5 n.1) = n.1 := by
  decide +kernel

@[expose] def s16c11_fr_trips3 : List (ℕ × ℕ × ℕ) :=
  [  (1, 2, 3), (3, 45, 46), (3, 29, 30), (3, 12, 15),
  (2, 21, 23), (3, 61, 62), (23, 45, 58), (9, 23, 30),
  (12, 23, 27), (15, 21, 26), (23, 42, 61), (26, 45, 55),
  (4, 26, 30), (1, 26, 27), (15, 53, 58), (6, 9, 15),
  (8, 21, 29), (26, 39, 61), (2, 53, 55), (6, 43, 45),
  (8, 37, 45), (30, 43, 53), (2, 4, 6), (4, 8, 12),
  (27, 46, 53), (6, 27, 29), (1, 8, 9), (15, 37, 42),
  (29, 39, 58), (8, 53, 61), (6, 59, 61), (2, 37, 39),
  (30, 37, 59), (12, 39, 43), (27, 37, 62), (9, 39, 46),
  (29, 42, 55), (1, 58, 59), (12, 55, 59), (1, 42, 43),
  (9, 55, 62), (21, 46, 59), (4, 42, 46), (21, 43, 62),
  (4, 58, 62)]

@[expose] def s16c11_fr_pars3 : List ℕ :=
  [  0, 0, 0, 0, 0, 1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 9,
  9, 10, 11, 11, 11, 12, 12, 12, 13, 13, 13, 14, 14, 17, 17, 18,
  21, 21, 24, 24, 27, 28, 32, 33, 34, 35, 35, 39, 40]

@[expose] def s16c11_fr_gis3 : List ℕ :=
  [  0, 1, 2, 3, 5, 0, 5, 5, 5, 3, 5, 3, 3, 3, 1, 2,
  4, 3, 1, 2, 4, 1, 2, 4, 1, 2, 4, 0, 4, 1, 2, 0,
  0, 4, 0, 4, 4, 2, 4, 3, 4, 2, 3, 5, 3]

@[expose] def s16c11_fr_codeTriple3 (k : Fin 45) : ℕ × ℕ × ℕ :=
  s16c11_fr_trips3.getD k.1 (0, 0, 0)

@[expose] def s16c11_fr_line3 (k : Fin 45) : Finset (S16C11FrVec 3) :=
  s16c11_fr_decode 3 (s16c11_fr_codeTriple3 k)

@[expose] def s16c11_fr_par3 (k : Fin 45) : Fin 45 :=
  ⟨s16c11_fr_pars3.getD k.1 0 % 45, Nat.mod_lt _ (by norm_num)⟩

@[expose] def s16c11_fr_genIdx3 (k : Fin 45) : Fin 6 :=
  ⟨s16c11_fr_gis3.getD k.1 0 % 6, Nat.mod_lt _ (by norm_num)⟩

@[expose] def s16c11_fr_imgTriple3 (k : Fin 45) : ℕ × ℕ × ℕ :=
  let t := s16c11_fr_codeTriple3 (s16c11_fr_par3 k)
  let g := s16c11_fr_genIdx3 k
  s16c11_fr_sort3 (s16c11_fr_tcode3 g t.1) (s16c11_fr_tcode3 g t.2.1)
    (s16c11_fr_tcode3 g t.2.2)

@[expose] def s16c11_fr_tableCodes3 : Finset (ℕ × ℕ × ℕ) :=
  Finset.univ.image s16c11_fr_codeTriple3

@[expose] def s16c11_fr_tableSet3 : Finset (Finset (S16C11FrVec 3)) :=
  s16c11_fr_tableCodes3.image (s16c11_fr_decode 3)

theorem s16c11_fr_mat_mulVec_code3 : ∀ (i : Fin 6) (n : Fin 64),
    Matrix.of (s16c11_fr_mat3 i) *ᵥ s16c11_fr_ofNat 3 n.1 =
      s16c11_fr_ofNat 3 (s16c11_fr_tcode3 i n.1) := by
  intro i n
  fin_cases i
  · exact s16c11_fr_mat_mulVec_code3_0 n
  · exact s16c11_fr_mat_mulVec_code3_1 n
  · exact s16c11_fr_mat_mulVec_code3_2 n
  · exact s16c11_fr_mat_mulVec_code3_3 n
  · exact s16c11_fr_mat_mulVec_code3_4 n
  · exact s16c11_fr_mat_mulVec_code3_5 n

theorem s16c11_fr_ofNat_basis3 : ∀ c : S16C11FrIdx 3,
    s16c11_fr_ofNat 3 (2 ^ s16c11_fr_bit 3 c) = Pi.single c 1 := by
  intro c
  revert c
  decide +kernel

theorem s16c11_fr_basis_lt3 : ∀ c : S16C11FrIdx 3,
    2 ^ s16c11_fr_bit 3 c < 64 := by
  intro c
  revert c
  decide +kernel

theorem s16c11_fr_tcode_lt3 : ∀ (i : Fin 6) (n : Fin 64),
    s16c11_fr_tcode3 i n.1 < 64 := by
  decide +kernel

theorem s16c11_fr_tcode_invol3 : ∀ (i : Fin 6) (n : Fin 64),
    s16c11_fr_tcode3 i (s16c11_fr_tcode3 i n.1) = n.1 := by
  intro i n
  fin_cases i
  · exact s16c11_fr_tcode_invol3_0 n
  · exact s16c11_fr_tcode_invol3_1 n
  · exact s16c11_fr_tcode_invol3_2 n
  · exact s16c11_fr_tcode_invol3_3 n
  · exact s16c11_fr_tcode_invol3_4 n
  · exact s16c11_fr_tcode_invol3_5 n

theorem s16c11_fr_mat_self3 : ∀ i : Fin 6,
    Matrix.of (s16c11_fr_mat3 i) * Matrix.of (s16c11_fr_mat3 i) = 1 := by
  intro i
  apply Matrix.ext_of_mulVec_single
  intro c
  have hc : s16c11_fr_ofNat 3 (2 ^ s16c11_fr_bit 3 c) = Pi.single c 1 :=
    s16c11_fr_ofNat_basis3 c
  have hbc : 2 ^ s16c11_fr_bit 3 c < 64 := s16c11_fr_basis_lt3 c
  rw [← hc, ← Matrix.mulVec_mulVec,
    s16c11_fr_mat_mulVec_code3 i ⟨_, hbc⟩,
    s16c11_fr_mat_mulVec_code3 i ⟨_, s16c11_fr_tcode_lt3 i ⟨_, hbc⟩⟩,
    s16c11_fr_tcode_invol3 i ⟨_, hbc⟩, Matrix.one_mulVec]

theorem s16c11_fr_tcode_Q3 : ∀ (i : Fin 6) (n : Fin 64),
    S16C11FrQ 3 (s16c11_fr_ofNat 3 (s16c11_fr_tcode3 i n.1)) =
      S16C11FrQ 3 (s16c11_fr_ofNat 3 n.1) := by
  intro i n
  fin_cases i
  · exact s16c11_fr_tcode_Q3_0 n
  · exact s16c11_fr_tcode_Q3_1 n
  · exact s16c11_fr_tcode_Q3_2 n
  · exact s16c11_fr_tcode_Q3_3 n
  · exact s16c11_fr_tcode_Q3_4 n
  · exact s16c11_fr_tcode_Q3_5 n

theorem s16c11_fr_mat_iso3 : ∀ i : Fin 6, ∀ v : S16C11FrVec 3,
    S16C11FrQ 3 (Matrix.of (s16c11_fr_mat3 i) *ᵥ v) = S16C11FrQ 3 v := by
  intro i v
  have hv : s16c11_fr_ofNat 3 (s16c11_fr_nat 3 v) = v :=
    s16c11_fr_ofNat_nat (show (3 : ℕ) = 3 ∨ (3 : ℕ) = 4 from Or.inl rfl) v
  have hlt : s16c11_fr_nat 3 v < 64 :=
    s16c11_fr_nat_lt (show (3 : ℕ) = 3 ∨ (3 : ℕ) = 4 from Or.inl rfl) v
  calc S16C11FrQ 3 (Matrix.of (s16c11_fr_mat3 i) *ᵥ v)
      = S16C11FrQ 3 (Matrix.of (s16c11_fr_mat3 i) *ᵥ
          s16c11_fr_ofNat 3 (s16c11_fr_nat 3 v)) := by rw [hv]
    _ = S16C11FrQ 3 (s16c11_fr_ofNat 3 (s16c11_fr_tcode3 i
          (s16c11_fr_nat 3 v))) := by
        rw [s16c11_fr_mat_mulVec_code3 i ⟨_, hlt⟩]
    _ = S16C11FrQ 3 (s16c11_fr_ofNat 3 (s16c11_fr_nat 3 v)) :=
        s16c11_fr_tcode_Q3 i ⟨_, hlt⟩
    _ = S16C11FrQ 3 v := by rw [hv]

theorem s16c11_fr_codeTriple_lt3 : ∀ k : Fin 45,
    (s16c11_fr_codeTriple3 k).1 < 64 ∧
      (s16c11_fr_codeTriple3 k).2.1 < 64 ∧
      (s16c11_fr_codeTriple3 k).2.2 < 64 := by
  decide +kernel

theorem s16c11_fr_image_decode3 (i : Fin 6) (t : ℕ × ℕ × ℕ) (h1 : t.1 < 64)
    (h2 : t.2.1 < 64) (h3 : t.2.2 < 64) :
    (s16c11_fr_decode 3 t).image (fun x => Matrix.of (s16c11_fr_mat3 i) *ᵥ x) =
      s16c11_fr_decode 3 (s16c11_fr_sort3 (s16c11_fr_tcode3 i t.1)
        (s16c11_fr_tcode3 i t.2.1) (s16c11_fr_tcode3 i t.2.2)) := by
  have e1 := s16c11_fr_mat_mulVec_code3 i ⟨t.1, h1⟩
  have e2 := s16c11_fr_mat_mulVec_code3 i ⟨t.2.1, h2⟩
  have e3 := s16c11_fr_mat_mulVec_code3 i ⟨t.2.2, h3⟩
  rw [s16c11_fr_decode_sort3]
  simp only [s16c11_fr_decode, Finset.image_insert, Finset.image_singleton, e1, e2, e3]

theorem s16c11_fr_stepNat3 : ∀ k : Fin 45,
    s16c11_fr_codeTriple3 k = s16c11_fr_codeTriple3 0 ∨
      (s16c11_fr_par3 k < k ∧
        s16c11_fr_imgTriple3 k = s16c11_fr_codeTriple3 k) := by
  decide +kernel

@[expose] def s16c11_fr_tau3 (i : Fin 6) : ↥(S16C11FrO 3) where
  val := ⟨Matrix.of (s16c11_fr_mat3 i), Matrix.of (s16c11_fr_mat3 i),
    s16c11_fr_mat_self3 i, s16c11_fr_mat_self3 i⟩
  property := by
    apply Subgroup.subset_closure
    intro v
    exact s16c11_fr_mat_iso3 i v

theorem s16c11_fr_line_zero3 : s16c11_fr_line3 0 = s16c11FrLine 3 := by
  decide +kernel

theorem s16c11_fr_step3 : ∀ k : Fin 45,
    s16c11_fr_line3 k = s16c11_fr_line3 0 ∨
      (s16c11_fr_par3 k < k ∧
        (s16c11_fr_line3 (s16c11_fr_par3 k)).image
          (fun x => Matrix.of (s16c11_fr_mat3 (s16c11_fr_genIdx3 k)) *ᵥ x) =
        s16c11_fr_line3 k) := by
  intro k
  obtain ⟨h1, h2, h3⟩ := s16c11_fr_codeTriple_lt3 (s16c11_fr_par3 k)
  rcases s16c11_fr_stepNat3 k with h | ⟨hp, himg⟩
  · left
    rw [s16c11_fr_line3, s16c11_fr_line3, h]
  · right
    refine ⟨hp, ?_⟩
    unfold s16c11_fr_line3
    rw [s16c11_fr_image_decode3 (s16c11_fr_genIdx3 k)
      (s16c11_fr_codeTriple3 (s16c11_fr_par3 k)) h1 h2 h3]
    change s16c11_fr_decode 3 (s16c11_fr_imgTriple3 k) =
      s16c11_fr_decode 3 (s16c11_fr_codeTriple3 k)
    rw [himg]

theorem s16c11_fr_tableCodes_card3 : s16c11_fr_tableCodes3.card = 45 := by
  decide +kernel

theorem s16c11_fr_decode_inj3 :
    Set.InjOn (s16c11_fr_decode 3) (s16c11_fr_tableCodes3 : Set (ℕ × ℕ × ℕ)) := by
  decide +kernel

theorem s16c11_fr_tableSet_card3 : s16c11_fr_tableSet3.card = 45 := by
  unfold s16c11_fr_tableSet3
  rw [Finset.card_image_iff.mpr s16c11_fr_decode_inj3, s16c11_fr_tableCodes_card3]

theorem s16c11_fr_complete3 :
    ∀ i j : Fin 64, s16c11_fr_validCode 3 i.1 j.1 →
      s16c11_fr_sort3 i.1 j.1 (i.1 ^^^ j.1) ∈ s16c11_fr_tableCodes3 := by
  decide +kernel

theorem s16c11_fr_table_orbit3 :
    ∀ k : Fin 45,
      s16c11_fr_line3 k ∈ MulAction.orbit ↥(S16C11FrO 3) (s16c11FrLine 3) := by
  intro k
  refine Fin.strong_induction_on (motive := fun k =>
    s16c11_fr_line3 k ∈ MulAction.orbit ↥(S16C11FrO 3) (s16c11FrLine 3)) ?_ k
  intro j ih
  rcases s16c11_fr_step3 j with h | ⟨hlt, himg⟩
  · rw [h, s16c11_fr_line_zero3]
    exact MulAction.mem_orbit_self _
  · have hprev := ih (s16c11_fr_par3 j) hlt
    have hact : s16c11_fr_tau3 (s16c11_fr_genIdx3 j) • s16c11_fr_line3 (s16c11_fr_par3 j) =
        s16c11_fr_line3 j := by
      show (s16c11_fr_line3 (s16c11_fr_par3 j)).image
        (fun x => Matrix.of (s16c11_fr_mat3 (s16c11_fr_genIdx3 j)) *ᵥ x) =
        s16c11_fr_line3 j
      exact himg
    rw [← hact]
    exact MulAction.mem_orbit_of_mem_orbit _ hprev

theorem s16c11_fr_tableSet_subset_orbit3 :
    (s16c11_fr_tableSet3 : Set (Finset (S16C11FrVec 3))) ⊆
      MulAction.orbit ↥(S16C11FrO 3) (s16c11FrLine 3) := by
  intro L hL
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hL
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 ht
  exact s16c11_fr_table_orbit3 k

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
