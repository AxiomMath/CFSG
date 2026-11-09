module

public import CFSG.RankThree.GF2n.Smith81.S81E7Basic

public section

namespace CFSG.RankThree.GF2n.Smith81.E7Fast

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.RankThree.GF2n.Smith81.E7Model

abbrev wd (w i : ℕ) : ℕ := w / 4 ^ i % 4
abbrev rd (r i : ℕ) : ℕ := r / 16 ^ i % 16

@[expose] def prP (w r : ℕ) : ℕ :=
  wd w 0 * rd r 0 + wd w 1 * rd r 1 + wd w 2 * rd r 2 + wd w 3 * rd r 3 + wd w 4 * rd r 4 +
    wd w 5 * rd r 5 + wd w 6 * rd r 6 + 56

@[expose] def prN (w r : ℕ) : ℕ :=
  8 * (wd w 0 + wd w 1 + wd w 2 + wd w 3 + wd w 4 + wd w 5 + wd w 6) +
    (rd r 0 + rd r 1 + rd r 2 + rd r 3 + rd r 4 + rd r 5 + rd r 6)

@[expose] def prC (w r : ℕ) : ℤ := (prP w r : ℤ) - (prN w r : ℤ)

theorem pr_decodeVec (a : Fin e7Data.d) (r : ℕ) :
    pr a (decodeVec r) = prC (e7Data.weights.getD a 0) r := by
  show (∑ i : Fin 7, e7Data.wt a i * decodeVec (τ := .E7) r i) = _
  rw [Fin.sum_univ_seven]
  simp only [MinData.wt, decodeVec, prC, prP, prN]
  push_cast
  simp
  ring

@[expose] def twP (j r : ℕ) : ℕ :=
  match j with
  | 0 => 2 * rd r 0 + 8
  | 1 => 2 * rd r 1 + 8
  | 2 => 2 * rd r 2 + 16
  | 3 => 2 * rd r 3 + 24
  | 4 => 2 * rd r 4 + 16
  | 5 => 2 * rd r 5 + 16
  | _ => 2 * rd r 6 + 8

@[expose] def twN (j r : ℕ) : ℕ :=
  match j with
  | 0 => rd r 2 + 16
  | 1 => rd r 3 + 16
  | 2 => rd r 0 + rd r 3 + 16
  | 3 => rd r 1 + rd r 2 + rd r 4 + 16
  | 4 => rd r 3 + rd r 5 + 16
  | 5 => rd r 4 + rd r 6 + 16
  | _ => rd r 5 + 16

theorem toWeight_decodeVec (r : ℕ) (j : Fin 7) :
    MinData.toWeight (decodeVec (τ := .E7) r) j = (twP j r : ℤ) - (twN j r : ℤ) := by
  show (∑ i : Fin 7, Tag.cartanE 7 j i * decodeVec (τ := .E7) r i) = _
  rw [Fin.sum_univ_seven]
  fin_cases j <;> simp [Tag.cartanE, decodeVec, twP, twN] <;> ring

theorem wt_apply (a : ℕ) (j : Fin 7) :
    e7Data.wt a j = ((wd (e7Data.weights.getD a 0) j : ℕ) : ℤ) - 1 := rfl

@[expose] def shC (wb wa r : ℕ) : Bool :=
  (wd wb 0 + twN 0 r == wd wa 0 + twP 0 r) &&
  (wd wb 1 + twN 1 r == wd wa 1 + twP 1 r) &&
  (wd wb 2 + twN 2 r == wd wa 2 + twP 2 r) &&
  (wd wb 3 + twN 3 r == wd wa 3 + twP 3 r) &&
  (wd wb 4 + twN 4 r == wd wa 4 + twP 4 r) &&
  (wd wb 5 + twN 5 r == wd wa 5 + twP 5 r) &&
  (wd wb 6 + twN 6 r == wd wa 6 + twP 6 r)

theorem coord_iff (x y P N : ℕ) :
    ((x : ℤ) - 1 = (y : ℤ) - 1 + ((P : ℤ) - (N : ℤ))) ↔ (x + N == y + P) = true := by
  rw [beq_iff_eq]
  omega

theorem coord_eq_iff (a b r : ℕ) (j : Fin 7) :
    e7Data.wt b j = (e7Data.wt a + MinData.toWeight (decodeVec (τ := .E7) r)) j ↔
      (wd (e7Data.weights.getD b 0) j + twN j r ==
        wd (e7Data.weights.getD a 0) j + twP j r) = true := by
  show e7Data.wt b j = e7Data.wt a j + MinData.toWeight (decodeVec (τ := .E7) r) j ↔ _
  rw [wt_apply, wt_apply, toWeight_decodeVec, coord_iff]

theorem wt_eq_add_iff (a b : ℕ) (r : ℕ) :
    e7Data.wt b = e7Data.wt a + MinData.toWeight (decodeVec (τ := .E7) r) ↔
      shC (e7Data.weights.getD b 0) (e7Data.weights.getD a 0) r = true := by
  rw [funext_iff]
  simp only [shC, Bool.and_eq_true]
  constructor
  · intro h
    exact ⟨⟨⟨⟨⟨⟨(coord_eq_iff a b r 0).1 (h (0 : Fin 7)), (coord_eq_iff a b r 1).1 (h (1 : Fin 7))⟩,
      (coord_eq_iff a b r 2).1 (h (2 : Fin 7))⟩, (coord_eq_iff a b r 3).1 (h (3 : Fin 7))⟩,
      (coord_eq_iff a b r 4).1 (h (4 : Fin 7))⟩, (coord_eq_iff a b r 5).1 (h (5 : Fin 7))⟩,
      (coord_eq_iff a b r 6).1 (h (6 : Fin 7))⟩
  · rintro ⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ (j : Fin 7)
    rw [coord_eq_iff]
    fin_cases j
    exacts [h0, h1, h2, h3, h4, h5, h6]

@[expose] def WE (w : ℕ) : ℕ :=
  wd w 0 + wd w 1 * 512 + wd w 2 * 512 ^ 2 + wd w 3 * 512 ^ 3 + wd w 4 * 512 ^ 4 +
    wd w 5 * 512 ^ 5 + wd w 6 * 512 ^ 6

@[expose] def RE (r : ℕ) : ℕ :=
  rd r 6 + rd r 5 * 512 + rd r 4 * 512 ^ 2 + rd r 3 * 512 ^ 3 + rd r 2 * 512 ^ 4 +
    rd r 1 * 512 ^ 5 + rd r 0 * 512 ^ 6

theorem extract7 (x0 x1 x2 x3 x4 x5 x6 y0 y1 y2 y3 y4 y5 y6 : ℕ)
    (hx0 : x0 < 4) (hx1 : x1 < 4) (hx2 : x2 < 4) (hx3 : x3 < 4) (hx4 : x4 < 4) (hx5 : x5 < 4)
    (hx6 : x6 < 4) (hy0 : y0 < 16) (hy1 : y1 < 16) (hy2 : y2 < 16) (hy3 : y3 < 16)
    (hy4 : y4 < 16) (hy5 : y5 < 16) (hy6 : y6 < 16) :
    (x0 + x1 * 512 + x2 * 512 ^ 2 + x3 * 512 ^ 3 + x4 * 512 ^ 4 + x5 * 512 ^ 5 + x6 * 512 ^ 6) *
      (y6 + y5 * 512 + y4 * 512 ^ 2 + y3 * 512 ^ 3 + y2 * 512 ^ 4 + y1 * 512 ^ 5 + y0 * 512 ^ 6)
      / 512 ^ 6 % 512 =
    x0 * y0 + x1 * y1 + x2 * y2 + x3 * y3 + x4 * y4 + x5 * y5 + x6 * y6 := by
  have b : ∀ {x y : ℕ}, x < 4 → y < 16 → x * y ≤ 45 := fun hx hy =>
    Nat.mul_le_mul (Nat.le_of_lt_succ hx) (Nat.le_of_lt_succ hy)
  have e : (x0 + x1 * 512 + x2 * 512 ^ 2 + x3 * 512 ^ 3 + x4 * 512 ^ 4 + x5 * 512 ^ 5 +
      x6 * 512 ^ 6) *
      (y6 + y5 * 512 + y4 * 512 ^ 2 + y3 * 512 ^ 3 + y2 * 512 ^ 4 + y1 * 512 ^ 5 + y0 * 512 ^ 6) =
      (x0 * y6 + (x0 * y5 + x1 * y6) * 512 + (x0 * y4 + x1 * y5 + x2 * y6) * 512 ^ 2 +
        (x0 * y3 + x1 * y4 + x2 * y5 + x3 * y6) * 512 ^ 3 +
        (x0 * y2 + x1 * y3 + x2 * y4 + x3 * y5 + x4 * y6) * 512 ^ 4 +
        (x0 * y1 + x1 * y2 + x2 * y3 + x3 * y4 + x4 * y5 + x5 * y6) * 512 ^ 5) +
      (x0 * y0 + x1 * y1 + x2 * y2 + x3 * y3 + x4 * y4 + x5 * y5 + x6 * y6) * 512 ^ 6 +
      ((x1 * y0 + x2 * y1 + x3 * y2 + x4 * y3 + x5 * y4 + x6 * y5) +
        (x2 * y0 + x3 * y1 + x4 * y2 + x5 * y3 + x6 * y4) * 512 +
        (x3 * y0 + x4 * y1 + x5 * y2 + x6 * y3) * 512 ^ 2 + (x4 * y0 + x5 * y1 + x6 * y2) * 512 ^ 3 +
        (x5 * y0 + x6 * y1) * 512 ^ 4 + x6 * y0 * 512 ^ 5) * 512 ^ 7 := by ring
  rw [e]
  have := b hx0 hy0; have := b hx0 hy1; have := b hx0 hy2; have := b hx0 hy3; have := b hx0 hy4
  have := b hx0 hy5; have := b hx0 hy6
  have := b hx1 hy1; have := b hx1 hy2; have := b hx1 hy3; have := b hx1 hy4; have := b hx1 hy5
  have := b hx1 hy6
  have := b hx2 hy2; have := b hx2 hy3; have := b hx2 hy4; have := b hx2 hy5; have := b hx2 hy6
  have := b hx3 hy3; have := b hx3 hy4; have := b hx3 hy5; have := b hx3 hy6
  have := b hx4 hy4; have := b hx4 hy5; have := b hx4 hy6
  have := b hx5 hy5; have := b hx5 hy6; have := b hx6 hy6
  have := b hx1 hy0; have := b hx2 hy1; have := b hx3 hy2; have := b hx4 hy3; have := b hx5 hy4
  have := b hx6 hy5
  omega

@[expose] def SW (w : ℕ) : ℕ := 8 * (wd w 0 + wd w 1 + wd w 2 + wd w 3 + wd w 4 + wd w 5 + wd w 6)

@[expose] def SR (r : ℕ) : ℕ := rd r 0 + rd r 1 + rd r 2 + rd r 3 + rd r 4 + rd r 5 + rd r 6

@[expose] def prS (w r : ℕ) : ℕ := WE w * RE r / 512 ^ 6 % 512 + 56

theorem prS_eq (w r : ℕ) : prS w r = prP w r := by
  unfold prS prP WE RE
  rw [extract7 _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))
    (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))
    (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))
    (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))
    (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))]

theorem pr_eq (a : Fin e7Data.d) (r : ℕ) :
    pr a (decodeVec r) = (prS (e7Data.weights.getD a 0) r : ℤ) -
      ((SW (e7Data.weights.getD a 0) + SR r : ℕ) : ℤ) := by
  rw [pr_decodeVec, prC, prS_eq]
  rfl

theorem pr_eq_neg_one_iff (a : Fin e7Data.d) (r : ℕ) :
    pr a (decodeVec r) = -1 ↔
      prS (e7Data.weights.getD a 0) r + 1 = SW (e7Data.weights.getD a 0) + SR r := by
  rw [pr_eq]; omega

theorem pr_eq_zero_iff (a : Fin e7Data.d) (r : ℕ) :
    pr a (decodeVec r) = 0 ↔
      prS (e7Data.weights.getD a 0) r = SW (e7Data.weights.getD a 0) + SR r := by
  rw [pr_eq]; omega

theorem pr_eq_one_iff (a : Fin e7Data.d) (r : ℕ) :
    pr a (decodeVec r) = 1 ↔
      prS (e7Data.weights.getD a 0) r = SW (e7Data.weights.getD a 0) + SR r + 1 := by
  rw [pr_eq]; omega

theorem root_eq (k : ℕ) :
    (Tag.rootCertificate .E7).root k = decodeVec ((Tag.rootCertificate .E7).roots.getD k 0) := rfl

@[expose] def prOne (w r : ℕ) : Bool := prS w r == SW w + SR r + 1
@[expose] def prNeg (w r : ℕ) : Bool := prS w r + 1 == SW w + SR r
@[expose] def prZero (w r : ℕ) : Bool := prS w r == SW w + SR r

theorem pr_one_iff (a : Fin e7Data.d) (r : ℕ) :
    pr a (decodeVec r) = 1 ↔ prOne (e7Data.weights.getD a 0) r = true := by
  rw [pr_eq_one_iff, prOne, beq_iff_eq]

theorem pr_neg_iff (a : Fin e7Data.d) (r : ℕ) :
    pr a (decodeVec r) = -1 ↔ prNeg (e7Data.weights.getD a 0) r = true := by
  rw [pr_eq_neg_one_iff, prNeg, beq_iff_eq]

theorem pr_zero_iff (a : Fin e7Data.d) (r : ℕ) :
    pr a (decodeVec r) = 0 ↔ prZero (e7Data.weights.getD a 0) r = true := by
  rw [pr_eq_zero_iff, prZero, beq_iff_eq]

@[expose] def thetaCode : ℕ := 10 + 10 * 16 + 11 * 16 ^ 2 + 12 * 16 ^ 3 + 11 * 16 ^ 4 + 10 * 16 ^ 5 +
  9 * 16 ^ 6

theorem theta_eq : theta = decodeVec (τ := .E7) thetaCode := by
  funext i
  fin_cases i <;> rfl

theorem pr_theta_zero_iff (a : Fin e7Data.d) :
    pr a theta = 0 ↔ prZero (e7Data.weights.getD a 0) thetaCode = true := by
  rw [theta_eq, pr_zero_iff]

@[expose] def negC (wb wa : ℕ) : Bool :=
  (wd wb 0 + wd wa 0 == 2) && (wd wb 1 + wd wa 1 == 2) && (wd wb 2 + wd wa 2 == 2) &&
  (wd wb 3 + wd wa 3 == 2) && (wd wb 4 + wd wa 4 == 2) && (wd wb 5 + wd wa 5 == 2) &&
  (wd wb 6 + wd wa 6 == 2)

theorem neg_coord_iff (a b : ℕ) (j : Fin 7) :
    e7Data.wt b j = (-e7Data.wt a) j ↔
      (wd (e7Data.weights.getD b 0) j + wd (e7Data.weights.getD a 0) j == 2) = true := by
  show e7Data.wt b j = -e7Data.wt a j ↔ _
  rw [wt_apply, wt_apply, beq_iff_eq]
  omega

theorem wt_eq_neg_iff (a b : ℕ) :
    e7Data.wt b = -e7Data.wt a ↔
      negC (e7Data.weights.getD b 0) (e7Data.weights.getD a 0) = true := by
  rw [funext_iff]
  simp only [negC, Bool.and_eq_true]
  constructor
  · intro h
    exact ⟨⟨⟨⟨⟨⟨(neg_coord_iff a b 0).1 (h (0 : Fin 7)), (neg_coord_iff a b 1).1 (h (1 : Fin 7))⟩,
      (neg_coord_iff a b 2).1 (h (2 : Fin 7))⟩, (neg_coord_iff a b 3).1 (h (3 : Fin 7))⟩,
      (neg_coord_iff a b 4).1 (h (4 : Fin 7))⟩, (neg_coord_iff a b 5).1 (h (5 : Fin 7))⟩,
      (neg_coord_iff a b 6).1 (h (6 : Fin 7))⟩
  · rintro ⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ (j : Fin 7)
    rw [neg_coord_iff]
    fin_cases j
    exacts [h0, h1, h2, h3, h4, h5, h6]

theorem roots_length : (Tag.rootCertificate .E7).roots.length = 126 :=
  Tag.rootCertificate_length .E7

theorem weights_length_eq : e7Data.weights.length = e7Data.d := rfl

theorem getD_root_eq (k : Fin 126) :
    (Tag.rootCertificate .E7).roots.getD k 0 =
      (Tag.rootCertificate .E7).roots[(k : ℕ)]'(by rw [roots_length]; exact k.2) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem, Option.getD_some]

theorem getD_weight_eq (a : Fin e7Data.d) :
    e7Data.weights.getD a 0 = e7Data.weights[(a : ℕ)]'(by rw [weights_length_eq]; exact a.2) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem, Option.getD_some]

theorem getD_root_mem (k : Fin 126) :
    (Tag.rootCertificate .E7).roots.getD k 0 ∈ (Tag.rootCertificate .E7).roots := by
  rw [getD_root_eq]
  exact List.getElem_mem _

theorem getD_weight_mem (a : Fin e7Data.d) : e7Data.weights.getD a 0 ∈ e7Data.weights := by
  rw [getD_weight_eq]
  exact List.getElem_mem _

theorem exists_root_of_mem {r : ℕ} (h : r ∈ (Tag.rootCertificate .E7).roots) :
    ∃ k : Fin 126, (Tag.rootCertificate .E7).roots.getD k 0 = r := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 h
  exact ⟨⟨i, by rwa [roots_length] at hi⟩, by rw [getD_root_eq]⟩

theorem exists_weight_of_mem {w : ℕ} (h : w ∈ e7Data.weights) :
    ∃ a : Fin e7Data.d, e7Data.weights.getD a 0 = w := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 h
  exact ⟨⟨i, by rwa [weights_length_eq] at hi⟩, by rw [getD_weight_eq]⟩

@[expose] def wrec (w : ℕ) : ℕ × ℕ × ℕ := (w, WE w, SW w)
@[expose] def rrec (r : ℕ) : ℕ × ℕ × ℕ := (r, RE r, SR r)

@[expose] def wRecs : List (ℕ × ℕ × ℕ) := [
    (9557, 36064050245009921, 64), (2389, 70437598134785, 56), (4693, 18014536082915841, 56),
    (5269, 18049583150268929, 56), (5417, 18049651601572865, 64), (5473, 18049651735789569, 56),
    (5450, 18049651735266306, 64), (5506, 18049651869483010, 56), (5464, 18049651735528448, 56),
    (5520, 18049651869745152, 48), (5654, 18049720320786946, 64), (5668, 18049720321049088, 56),
    (6230, 18084767388140034, 64), (5701, 18049720454742529, 56), (6244, 18084767388402176, 56),
    (8534, 36028865872921090, 64), (6277, 18084767522095617, 56), (8548, 36028865873183232, 56),
    (1366, 35253226045954, 56), (6425, 18084835973399553, 64), (8581, 36028866006876673, 56),
    (1380, 35253226308096, 48), (6481, 18084836107616257, 56), (8729, 36028934458180609, 64),
    (1413, 35253360001537, 48), (8785, 36028934592397313, 56), (9305, 36063981525533697, 64),
    (1561, 35321811305473, 56), (9361, 36063981659750401, 56), (1617, 35321945522177, 48),
    (2137, 70368878658561, 56), (9509, 36064050111054337, 64), (2193, 70369012875265, 48),
    (4441, 18014467363439617, 56), (9542, 36064050244747778, 64), (2341, 70437464179201, 56),
    (4497, 18014467497656321, 48), (9556, 36064050245009920, 56), (2374, 70437597872642, 56),
    (4645, 18014535948960257, 56), (2388, 70437598134784, 48), (4678, 18014536082653698, 56),
    (5221, 18049583016313345, 56), (4692, 18014536082915840, 48), (5254, 18049583150006786, 56),
    (5268, 18049583150268928, 48), (5402, 18049651601310722, 64), (5416, 18049651601572864, 56),
    (5458, 18049651735527426, 56), (5472, 18049651735789568, 48), (5449, 18049651735266305, 56),
    (5505, 18049651869483009, 48), (5653, 18049720320786945, 56), (6229, 18084767388140033, 56),
    (8533, 36028865872921089, 56), (1365, 35253226045953, 48)]

@[expose] def rRecs : List (ℕ × ℕ × ℕ) := [
    (143165577, 162411612393705480, 57), (143165592, 144432398256312328, 57),
    (143165832, 144397282603700232, 57), (143169672, 144397214018441224, 57),
    (143231112, 144397213884485640, 57), (144214152, 144397213884224008, 57),
    (159942792, 144397213884223497, 57), (143165575, 126382815374741512, 55),
    (143165833, 162411681113182216, 58), (143165560, 144362029512134664, 55),
    (143169688, 144432398390530056, 58), (143165320, 144397145164746760, 55),
    (143169928, 144397282737917960, 58), (143161480, 144397213750005768, 55),
    (143235208, 144397214018703368, 58), (143100040, 144397213883961352, 55),
    (144279688, 144397213884486152, 58), (142117000, 144397213884222984, 55),
    (160991368, 144397213884224009, 58), (126388360, 144397213884223495, 55),
    (143165319, 126382746655264776, 54), (143169929, 162411681247399944, 59),
    (143161464, 144362029377916936, 54), (143169944, 144432467110006792, 59),
    (143235224, 144432398390792200, 59), (143161224, 144397145030529032, 54),
    (143235464, 144397282738180104, 59), (143095944, 144397213749743624, 54),
    (144283784, 144397214018703880, 59), (142051464, 144397213883960840, 54),
    (161056904, 144397213884486153, 59), (125339784, 144397213884222983, 54),
    (143161223, 126382746521047048, 53), (143169945, 162446865619488776, 60),
    (143235465, 162411681247662088, 60), (143161208, 144361960658440200, 53),
    (143095928, 144362029377654792, 53), (143235480, 144432467110268936, 60),
    (144283800, 144432398390792712, 60), (143095688, 144397145030266888, 53),
    (144284040, 144397282738180616, 60), (142047368, 144397213749743112, 53),
    (161061000, 144397214018703881, 60), (125274248, 144397213883960839, 53),
    (143161207, 126347562148958216, 52), (143095687, 126382746520784904, 52),
    (143235481, 162446865619750920, 61), (144284041, 162411681247662600, 61),
    (143095672, 144361960658178056, 52), (142047352, 144362029377654280, 52),
    (143239576, 144432467244486664, 61), (144284056, 144432467110269448, 61),
    (161061016, 144432398390792713, 61), (142047112, 144397145030266376, 52),
    (161061256, 144397282738180617, 61), (125270152, 144397213749743111, 52),
    (143095671, 126347562148696072, 51), (142047111, 126382746520784392, 51),
    (143239577, 162446865753968648, 62), (144284057, 162446865619751432, 62),
    (161061257, 162411681247662601, 62), (143091576, 144361960523960328, 51),
    (142047096, 144361960658177544, 51), (125270136, 144362029377654279, 51),
    (144288152, 144432467244487176, 62), (161061272, 144432467110269449, 62),
    (125269896, 144397145030266375, 51), (143091575, 126347562014478344, 50),
    (142047095, 126347562148695560, 50), (125269895, 126382746520784391, 50),
    (143239833, 162446934473445384, 63), (144288153, 162446865753969160, 63),
    (161061273, 162446865619751433, 63), (142043000, 144361960523959816, 50),
    (125269880, 144361960658177543, 50), (144353688, 144432467244749320, 63),
    (161065368, 144432467244487177, 63), (143091319, 126347493295001608, 49),
    (142042999, 126347562014477832, 49), (125269879, 126347562148695559, 49),
    (144288409, 162446934473445896, 64), (144353689, 162446865754231304, 64),
    (161065369, 162446865753969161, 64), (141977464, 144361960523697672, 49),
    (125265784, 144361960523959815, 49), (161130904, 144432467244749321, 64),
    (142042743, 126347493295001096, 48), (141977463, 126347562014215688, 48),
    (125265783, 126347562014477831, 48), (144353945, 162446934473708040, 65),
    (161065625, 162446934473445897, 65), (161130905, 162446865754231305, 65),
    (125200248, 144361960523697671, 48), (162179480, 144432467244749833, 65),
    (141977207, 126347493294738952, 47), (125265527, 126347493295001095, 47),
    (125200247, 126347562014215687, 47), (144358041, 162446934607925768, 66),
    (161131161, 162446934473708041, 66), (162179481, 162446865754231817, 66),
    (124151672, 144361960523697159, 47), (141973111, 126347493160521224, 46),
    (125199991, 126347493294738951, 46), (124151671, 126347562014215175, 46),
    (144358057, 162482118980014600, 67), (161135257, 162446934607925769, 67),
    (162179737, 162446934473708553, 67), (141973095, 126312308788432392, 45),
    (125195895, 126347493160521223, 45), (124151415, 126347493294738439, 45),
    (161135273, 162482118980014601, 68), (162183833, 162446934607926281, 68),
    (125195879, 126312308788432391, 44), (124147319, 126347493160520711, 44),
    (162183849, 162482118980015113, 69), (162249369, 162446934608188425, 69),
    (124147303, 126312308788431879, 43), (124081783, 126347493160258567, 43),
    (162249385, 162482118980277257, 70), (124081767, 126312308788169735, 42),
    (162253481, 162482119114494985, 71), (124077671, 126312308653952007, 41),
    (162253737, 162482187833971721, 72), (124077415, 126312239934475271, 40),
    (162253738, 180496586343453705, 73), (124077414, 108297841424993287, 39)]

theorem wRecs_eq : wRecs = e7Data.weights.map wrec := by
  decide +kernel

theorem rRecs_eq : rRecs = (Tag.rootCertificate .E7).roots.map rrec := by
  decide +kernel

@[expose] def pOne (x y : ℕ × ℕ × ℕ) : Bool := x.2.1 * y.2.1 / 512 ^ 6 % 512 + 56 == x.2.2 + y.2.2 + 1
@[expose] def pNeg (x y : ℕ × ℕ × ℕ) : Bool := x.2.1 * y.2.1 / 512 ^ 6 % 512 + 57 == x.2.2 + y.2.2
@[expose] def pZero (x y : ℕ × ℕ × ℕ) : Bool := x.2.1 * y.2.1 / 512 ^ 6 % 512 + 56 == x.2.2 + y.2.2

theorem pOne_rec (w r : ℕ) : pOne (wrec w) (rrec r) = prOne w r := rfl
theorem pNeg_rec (w r : ℕ) : pNeg (wrec w) (rrec r) = prNeg w r := rfl
theorem pZero_rec (w r : ℕ) : pZero (wrec w) (rrec r) = prZero w r := rfl

theorem wrec_mem (a : Fin e7Data.d) : wrec (e7Data.weights.getD a 0) ∈ wRecs := by
  rw [wRecs_eq]
  exact List.mem_map_of_mem (getD_weight_mem a)

theorem rrec_mem (k : Fin 126) : rrec ((Tag.rootCertificate .E7).roots.getD k 0) ∈ rRecs := by
  rw [rRecs_eq]
  exact List.mem_map_of_mem (getD_root_mem k)

theorem exists_of_mem_rRecs {y : ℕ × ℕ × ℕ} (h : y ∈ rRecs) :
    ∃ k : Fin 126, y = rrec ((Tag.rootCertificate .E7).roots.getD k 0) := by
  rw [rRecs_eq, List.mem_map] at h
  obtain ⟨r, hr, rfl⟩ := h
  obtain ⟨k, rfl⟩ := exists_root_of_mem hr
  exact ⟨k, rfl⟩

theorem exists_of_mem_wRecs {x : ℕ × ℕ × ℕ} (h : x ∈ wRecs) :
    ∃ a : Fin e7Data.d, x = wrec (e7Data.weights.getD a 0) := by
  rw [wRecs_eq, List.mem_map] at h
  obtain ⟨w, hw, rfl⟩ := h
  obtain ⟨a, rfl⟩ := exists_weight_of_mem hw
  exact ⟨a, rfl⟩

@[expose] def NWc (x x' : ℕ × ℕ × ℕ) : Bool :=
  rRecs.all fun y => !(pOne x y && pNeg x' y) || shC x.1 x'.1 y.1

theorem nw_of_NWc {a b : Fin e7Data.d}
    (h : NWc (wrec (e7Data.weights.getD a 0)) (wrec (e7Data.weights.getD b 0)) = true) :
    ∀ k : Fin 126, pr a ((Tag.rootCertificate .E7).root k) = 1 →
      pr b ((Tag.rootCertificate .E7).root k) = -1 →
        e7Data.wt a = e7Data.wt b + MinData.toWeight ((Tag.rootCertificate .E7).root k) := by
  intro k h1 h2
  rw [root_eq] at h1 h2 ⊢
  rw [pr_one_iff, ← pOne_rec] at h1
  rw [pr_neg_iff, ← pNeg_rec] at h2
  rw [wt_eq_add_iff]
  have := List.all_eq_true.1 h _ (rrec_mem k)
  rw [h1, h2] at this
  exact this

theorem eq_of_mem_of_length_le_one {α : Type*} {l : List α} (h : l.length ≤ 1) {y y' : α}
    (hy : y ∈ l) (hy' : y' ∈ l) : y = y' := by
  match l, h with
  | [], _ => simp at hy
  | [z], _ =>
    rw [List.mem_singleton] at hy hy'
    rw [hy, hy']
  | _ :: _ :: _, h => simp at h

@[expose] def keyUniq (x0 : ℕ × ℕ × ℕ) (filt : ℕ × ℕ × ℕ → Bool) : Bool :=
  wRecs.all fun x => !(filt x) || Nat.ble (rRecs.countP fun y => pOne x0 y && pOne x y) 1 ||
    NWc x0 x || negC x.1 x0.1

theorem keyUniq_spec {a0 : Fin e7Data.d} {filt : ℕ × ℕ × ℕ → Bool}
    (h : keyUniq (wrec (e7Data.weights.getD a0 0)) filt = true) (b : Fin e7Data.d)
    (hb : filt (wrec (e7Data.weights.getD b 0)) = true)
    (hnw : ¬ ∀ k : Fin 126, pr a0 ((Tag.rootCertificate .E7).root k) = 1 →
      pr b ((Tag.rootCertificate .E7).root k) = -1 →
        e7Data.wt a0 = e7Data.wt b + MinData.toWeight ((Tag.rootCertificate .E7).root k))
    (hneg : e7Data.wt b ≠ -e7Data.wt a0) (k k' : Fin 126)
    (h1 : pr a0 ((Tag.rootCertificate .E7).root k) = 1)
    (h2 : pr b ((Tag.rootCertificate .E7).root k) = 1)
    (h3 : pr a0 ((Tag.rootCertificate .E7).root k') = 1)
    (h4 : pr b ((Tag.rootCertificate .E7).root k') = 1) :
    (Tag.rootCertificate .E7).root k = (Tag.rootCertificate .E7).root k' := by
  have hw := List.all_eq_true.1 h _ (wrec_mem b)
  have hnw' : NWc (wrec (e7Data.weights.getD a0 0)) (wrec (e7Data.weights.getD b 0)) = false := by
    by_contra hc
    exact hnw (nw_of_NWc (Bool.eq_true_of_not_eq_false hc))
  have hneg' : negC (wrec (e7Data.weights.getD b 0)).1 (wrec (e7Data.weights.getD a0 0)).1 =
      false := by
    by_contra hc
    exact hneg ((wt_eq_neg_iff a0 b).2 (Bool.eq_true_of_not_eq_false hc))
  rw [hb, hnw', hneg', Bool.not_true, Bool.false_or, Bool.or_false, Bool.or_false,
    Nat.ble_eq, List.countP_eq_length_filter] at hw
  rw [root_eq] at h1 h2 h3 h4
  rw [pr_one_iff, ← pOne_rec] at h1 h2 h3 h4
  have e := eq_of_mem_of_length_le_one hw
    (List.mem_filter.2 ⟨rrec_mem k, by rw [h1, h2]; rfl⟩)
    (List.mem_filter.2 ⟨rrec_mem k', by rw [h3, h4]; rfl⟩)
  rw [root_eq, root_eq]
  exact congrArg (fun y : ℕ × ℕ × ℕ => decodeVec (τ := .E7) y.1) e

end CFSG.RankThree.GF2n.Smith81.E7Fast
