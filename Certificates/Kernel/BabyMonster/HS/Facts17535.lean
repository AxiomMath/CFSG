module

public import CFSG.Certificates.Kernel.BabyMonster.HSFacts
public import CFSG.Certificates.Kernel.BabyMonster.HS.Check0
public import CFSG.Certificates.Kernel.BabyMonster.HS.Check1
public import CFSG.Certificates.Kernel.BabyMonster.HS.Check2
public import CFSG.Certificates.Kernel.BabyMonster.HS.Check3
public import CFSG.Certificates.Kernel.BabyMonster.HS.Check4
public import CFSG.Certificates.Kernel.BabyMonster.HS.Check5
public import CFSG.Certificates.Kernel.BabyMonster.HS.Check6
public import CFSG.Certificates.Kernel.BabyMonster.HS.Check7
public import CFSG.Certificates.Kernel.BabyMonster.HS.Wf
public import CFSG.Certificates.Kernel.BabyMonster.Chain4Pair
public import CFSG.Certificates.Kernel.BabyMonster.PairSound
public import CFSG.Certificates.Kernel.Bounds.HSAlt.RelsTC
public import Certificates.Kernel.BabyMonster.FiveM.Basic

public section

namespace CertificateChecks.KernelBM.HS

open CFSG.KC.BM CertificateChecks.KernelBM.FiveA

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)
local notation "MG1" => stripMat CFSG.KC.BM.Max15.g1
local notation "MG2" => stripMat CFSG.KC.BM.Max15.g2
local notation "MA" => stripMat CFSG.KC.BM.HS.a
local notation "MB" => stripMat CFSG.KC.BM.HS.b

set_option maxRecDepth 100000

section Words

variable {M : Type*} [Monoid M]

@[expose] def ev (A B : M) (w : List Bool) : M := (w.map fun c => if c then B else A).prod

theorem ev_append (A B : M) (u v : List Bool) : ev A B (u ++ v) = ev A B u * ev A B v := by
  simp [ev]

theorem ev_replicate (A B : M) (k : ℕ) : ev A B (List.replicate k true) = B ^ k := by
  simp [ev, List.map_replicate, List.prod_replicate]

theorem ev_nil (A B : M) : ev A B [] = 1 := by simp [ev]

theorem ev_ff (A B : M) : ev A B [false, false] = A * A := by simp [ev]

theorem ev_ft (A B : M) : ev A B [false, true] = A * B := by simp [ev]

theorem ev_snoc (A B : M) (w : List Bool) : ev A B (w ++ [true]) = ev A B w * B := by
  simp [ev]

theorem ev_n1 (A B : M) :
    ev A B ([false, true] ++ [true] ++ [true] ++ [true]) = A * B ^ 4 := by
  simp [ev, pow_succ, mul_assoc]

@[expose] def red : ℕ → List Bool → List Bool
  | k, [] => List.replicate k true
  | k, true :: w => if k = 4 then red 0 w else red (k + 1) w
  | k, false :: w => List.replicate k true ++ false :: red 0 w

theorem ev_red {A B : M} (hB : B ^ 5 = 1) :
    ∀ (w : List Bool) (k : ℕ), ev A B (red k w) = B ^ k * ev A B w
  | [], k => by
    rw [red, ev_replicate]
    simp [ev]
  | true :: w, k => by
    have e : ev A B (true :: w) = B * ev A B w := by simp [ev]
    rw [e]
    by_cases hk : k = 4
    · subst hk
      have h5 : B ^ 4 * B = 1 := by
        rw [← pow_succ]
        exact hB
      rw [red, if_pos rfl, ev_red hB w 0, ← mul_assoc, h5, pow_zero]
    · rw [red, if_neg hk, ev_red hB w (k + 1), pow_succ, mul_assoc]
  | false :: w, k => by
    have e : ∀ u, ev A B (false :: u) = A * ev A B u := fun u => by simp [ev]
    rw [red, ev_append, ev_replicate, e, e, ev_red hB w 0, pow_zero, one_mul]

theorem ev_red0 {A B : M} (hB : B ^ 5 = 1) (w : List Bool) : ev A B (red 0 w) = ev A B w := by
  rw [ev_red hB w 0, pow_zero, one_mul]

theorem isUnit_ev {A B : M} (hA : A * A = 1) (hB : B ^ 5 = 1) : ∀ w, IsUnit (ev A B w)
  | [] => by
    rw [ev_nil]
    exact isUnit_one
  | false :: w => by
    have e : ev A B (false :: w) = A * ev A B w := by simp [ev]
    rw [e]
    exact IsUnit.mul ⟨⟨A, A, hA, hA⟩, rfl⟩ (isUnit_ev hA hB w)
  | true :: w => by
    have e : ev A B (true :: w) = B * ev A B w := by simp [ev]
    have h4 : B * B ^ 4 = 1 := by
      rw [← pow_succ']
      exact hB
    have h4' : B ^ 4 * B = 1 := by
      rw [← pow_succ]
      exact hB
    rw [e]
    exact IsUnit.mul ⟨⟨B, B ^ 4, h4, h4'⟩, rfl⟩ (isUnit_ev hA hB w)

theorem comm_of_isUnit {x y : M} (hu : IsUnit x) (h : x * y = 1) : y * x = 1 := by
  obtain ⟨u, rfl⟩ := hu
  have e : y = ↑u⁻¹ := by
    calc y = ↑u⁻¹ * (↑u * y) := by rw [← mul_assoc, Units.inv_mul, one_mul]
      _ = ↑u⁻¹ := by rw [h, mul_one]
  rw [e, Units.inv_mul]

theorem ev_of_rotate {A B : M} (hA : A * A = 1) (hB : B ^ 5 = 1) {w : List Bool} (m : ℕ)
    (h : ev A B (w.rotate m) = 1) : ev A B w = 1 := by
  rw [List.rotate_eq_drop_append_take_mod, ev_append] at h
  rw [← List.take_append_drop (m % w.length) w, ev_append]
  exact comm_of_isUnit (isUnit_ev hA hB _) h

@[expose] def RotOf (R C : List Bool) : Bool :=
  (List.range ((red 0 R).length + 1)).any fun m => (red 0 R).rotate m == C

theorem ev_of_rotOf {A B : M} (hA : A * A = 1) (hB : B ^ 5 = 1)
    {R C : List Bool} (h : RotOf R C = true) (hC : ev A B C = 1) : ev A B R = 1 := by
  obtain ⟨m, -, hm⟩ := List.any_eq_true.1 h
  rw [beq_iff_eq] at hm
  rw [← ev_red0 hB R]
  exact ev_of_rotate hA hB m (by rw [hm]; exact hC)

@[expose] def code (l : ℕ × Bool) : List Bool :=
  if l.1 = 0 then [false] else if l.2 then [true] else [true, true, true, true]

theorem letter_eq (A B : M) (l : ℕ × Bool) :
    CFSG.KC.BM.HS.letter A B l = ev A B (code l) := by
  unfold CFSG.KC.BM.HS.letter code
  split_ifs <;> simp [ev, pow_succ, mul_assoc]

theorem prod_letters (A B : M) (v : List (ℕ × Bool)) :
    (v.map (CFSG.KC.BM.HS.letter A B)).prod = ev A B (v.flatMap code) := by
  induction v with
  | nil => simp [ev]
  | cons l v ih => rw [List.map_cons, List.prod_cons, ih, letter_eq, List.flatMap_cons, ev_append]

theorem comm_a (G1 G2 : M) (h : Commute (G1 * G2 ^ 15 * G1 ^ 3) (G2 ^ 14)) :
    G2 ^ 15 * G2 ^ 15 * (G1 * G2 ^ 15 * G1 ^ 3) ^ 12 * G2 ^ 14 =
      G2 ^ 14 * (G2 ^ 15 * G2 ^ 15 * (G1 * G2 ^ 15 * G1 ^ 3) ^ 12) :=
  (((Commute.pow_pow_self G2 15 14).mul_left (Commute.pow_pow_self G2 15 14)).mul_left
    (h.pow_left 12)).eq

theorem comm_b (G1 G2 : M) (h : Commute (G1 * G2 ^ 15 * G1 ^ 3) (G2 ^ 14)) :
    G2 ^ 15 * (G1 * G2 ^ 15 * G1 ^ 3) ^ 9 * G2 ^ 14 =
      G2 ^ 14 * (G2 ^ 15 * (G1 * G2 ^ 15 * G1 ^ 3) ^ 9) :=
  ((Commute.pow_pow_self G2 15 14).mul_left (h.pow_left 9)).eq

end Words

section Stage

open CFSG.KC.BM.HS

theorem y1_s : stripMat FiveM.y1 * stripMat FiveM.s = stripMat FiveM.s * stripMat FiveM.y1 :=
  eq1 FiveM.wf_y1 FiveM.wf_s FiveM.wf_s FiveM.wf_y1 (by bm_strips2_4 CFSG.KC.BM.HS.cm_y1s 69)

theorem ey1 : stripMat FiveM.y1 = MG1 * MG2 ^ 15 * MG1 ^ 3 := FiveM.y1_eq

theorem e_y1p2 : stripMat y1p2 = (MG1 * MG2 ^ 15 * MG1 ^ 3) ^ 2 := by
  rw [← mul1 FiveM.wf_y1 FiveM.wf_y1 (by bm_strips4 CFSG.KC.BM.HS.c_y1p2 69), ey1, sq]

theorem e_y1p3 : stripMat y1p3 = (MG1 * MG2 ^ 15 * MG1 ^ 3) ^ 3 := by
  rw [← mul1 wf_y1p2 FiveM.wf_y1 (by bm_strips4 CFSG.KC.BM.HS.c_y1p3 69), e_y1p2, ey1,
    ← pow_succ]

theorem e_y1p6 : stripMat y1p6 = (MG1 * MG2 ^ 15 * MG1 ^ 3) ^ 6 := by
  rw [← mul1 wf_y1p3 wf_y1p3 (by bm_strips4 CFSG.KC.BM.HS.c_y1p6 69), e_y1p3, ← pow_add]

theorem e_y1p9 : stripMat y1p9 = (MG1 * MG2 ^ 15 * MG1 ^ 3) ^ 9 := by
  rw [← mul1 wf_y1p6 wf_y1p3 (by bm_strips4 CFSG.KC.BM.HS.c_y1p9 69), e_y1p6, e_y1p3,
    ← pow_add]

theorem e_y1p12 : stripMat y1p12 = (MG1 * MG2 ^ 15 * MG1 ^ 3) ^ 12 := by
  rw [← mul1 wf_y1p6 wf_y1p6 (by bm_strips4 CFSG.KC.BM.HS.c_y1p12 69), e_y1p6, ← pow_add]

theorem a_eq : MA = hsA MG1 MG2 := by
  rw [← mul1 wf_y2 wf_y1p12 (by bm_strips4 CFSG.KC.BM.HS.c_a 69),
    ← mul1 FiveM.wf_y FiveM.wf_y (by bm_strips4 CFSG.KC.BM.HS.c_y2 69), FiveM.y_eq, e_y1p12, hsA]

theorem b_eq : MB = hsB MG1 MG2 := by
  rw [← mul1 FiveM.wf_y wf_y1p9 (by bm_strips4 CFSG.KC.BM.HS.c_b 69), FiveM.y_eq, e_y1p9, hsB]

theorem a_ne : MA ≠ 1 := notId_sound wf_a ne_a1

theorem comm_s : Commute (MG1 * MG2 ^ 15 * MG1 ^ 3) (MG2 ^ 14) := by
  have e := y1_s
  rw [ey1, FiveM.s_eq] at e
  exact e

theorem a_s : hsA MG1 MG2 * MG2 ^ 14 = MG2 ^ 14 * hsA MG1 MG2 := by
  rw [hsA]
  exact @comm_a MatB _ MG1 MG2 comm_s

theorem b_s : hsB MG1 MG2 * MG2 ^ 14 = MG2 ^ 14 * hsB MG1 MG2 := by
  rw [hsB]
  exact @comm_b MatB _ MG1 MG2 comm_s

end Stage

section Nodes

open CFSG.KC.BM.HS

@[expose] def wx1 : List Bool := [false, true]
@[expose] def wx2 : List Bool := wx1 ++ [true]
@[expose] def wn2 : List Bool := wx2 ++ [true]
@[expose] def wn1 : List Bool := wn2 ++ [true]

@[expose] def w4 : List Bool := wx1 ++ wx1
@[expose] def w5 : List Bool := w4 ++ w4
@[expose] def w6 : List Bool := w5 ++ w5
@[expose] def w7 : List Bool := wx2 ++ wx2
@[expose] def w8 : List Bool := w7 ++ w7
@[expose] def w9 : List Bool := wn1 ++ wx1
@[expose] def w10 : List Bool := w9 ++ w9
@[expose] def w11 : List Bool := w10 ++ w10
@[expose] def w12 : List Bool := wn1 ++ wn1
@[expose] def w13 : List Bool := w12 ++ w4
@[expose] def w14 : List Bool := w13 ++ w13
@[expose] def w15 : List Bool := wn2 ++ wx2
@[expose] def w16 : List Bool := w15 ++ w15
@[expose] def w17 : List Bool := w16 ++ w15
@[expose] def w18 : List Bool := w4 ++ wx2
@[expose] def w19 : List Bool := wx2 ++ wx1
@[expose] def w20 : List Bool := wn1 ++ wn2
@[expose] def w21 : List Bool := wn1 ++ w18
@[expose] def w22 : List Bool := w4 ++ w21
@[expose] def w23 : List Bool := wn2 ++ wn2
@[expose] def w24 : List Bool := wn1 ++ wx2
@[expose] def w25 : List Bool := w19 ++ wx2
@[expose] def w26 : List Bool := w22 ++ w20
@[expose] def w27 : List Bool := w24 ++ w4
@[expose] def wab11 : List Bool := (List.replicate 11 wx1).flatten

theorem e_x1 : stripMat x1 = ev MA MB wx1 := by
  rw [wx1, ev_ft]
  exact (mul1 wf_a wf_b (by bm_strips4 CFSG.KC.BM.HS.c_x1 69)).symm

theorem e_x2 : stripMat x2 = ev MA MB wx2 := by
  rw [wx2, ev_snoc, ← e_x1]
  exact (mul1 wf_x1 wf_b (by bm_strips4 CFSG.KC.BM.HS.c_x2 69)).symm

theorem e_n2 : stripMat n2 = ev MA MB wn2 := by
  rw [wn2, ev_snoc, ← e_x2]
  exact (mul1 wf_x2 wf_b (by bm_strips4 CFSG.KC.BM.HS.c_n2 69)).symm

theorem e_n1 : stripMat n1 = ev MA MB wn1 := by
  rw [wn1, ev_snoc, ← e_n2]
  exact (mul1 wf_n2 wf_b (by bm_strips4 CFSG.KC.BM.HS.c_n1 69)).symm

theorem e_h4 : stripMat h4 = ev MA MB w4 := by
  rw [w4, ev_append, ← e_x1]
  exact (mul1 wf_x1 wf_x1 (by bm_strips4 CFSG.KC.BM.HS.c_h4 69)).symm

theorem e_h5 : stripMat h5 = ev MA MB w5 := by
  rw [w5, ev_append, ← e_h4]
  exact (mul1 wf_h4 wf_h4 (by bm_strips4 CFSG.KC.BM.HS.c_h5 69)).symm

theorem e_h6 : stripMat h6 = ev MA MB w6 := by
  rw [w6, ev_append, ← e_h5]
  exact (mul1 wf_h5 wf_h5 (by bm_strips4 CFSG.KC.BM.HS.c_h6 69)).symm

theorem e_h7 : stripMat h7 = ev MA MB w7 := by
  rw [w7, ev_append, ← e_x2]
  exact (mul1 wf_x2 wf_x2 (by bm_strips4 CFSG.KC.BM.HS.c_h7 69)).symm

theorem e_h8 : stripMat h8 = ev MA MB w8 := by
  rw [w8, ev_append, ← e_h7]
  exact (mul1 wf_h7 wf_h7 (by bm_strips4 CFSG.KC.BM.HS.c_h8 69)).symm

theorem e_h9 : stripMat h9 = ev MA MB w9 := by
  rw [w9, ev_append, ← e_n1, ← e_x1]
  exact (mul1 wf_n1 wf_x1 (by bm_strips4 CFSG.KC.BM.HS.c_h9 69)).symm

theorem e_h10 : stripMat h10 = ev MA MB w10 := by
  rw [w10, ev_append, ← e_h9]
  exact (mul1 wf_h9 wf_h9 (by bm_strips4 CFSG.KC.BM.HS.c_h10 69)).symm

theorem e_h11 : stripMat h11 = ev MA MB w11 := by
  rw [w11, ev_append, ← e_h10]
  exact (mul1 wf_h10 wf_h10 (by bm_strips4 CFSG.KC.BM.HS.c_h11 69)).symm

theorem e_h12 : stripMat h12 = ev MA MB w12 := by
  rw [w12, ev_append, ← e_n1]
  exact (mul1 wf_n1 wf_n1 (by bm_strips4 CFSG.KC.BM.HS.c_h12 69)).symm

theorem e_h13 : stripMat h13 = ev MA MB w13 := by
  rw [w13, ev_append, ← e_h12, ← e_h4]
  exact (mul1 wf_h12 wf_h4 (by bm_strips4 CFSG.KC.BM.HS.c_h13 69)).symm

theorem e_h14 : stripMat h14 = ev MA MB w14 := by
  rw [w14, ev_append, ← e_h13]
  exact (mul1 wf_h13 wf_h13 (by bm_strips4 CFSG.KC.BM.HS.c_h14 69)).symm

theorem e_h15 : stripMat h15 = ev MA MB w15 := by
  rw [w15, ev_append, ← e_n2, ← e_x2]
  exact (mul1 wf_n2 wf_x2 (by bm_strips4 CFSG.KC.BM.HS.c_h15 69)).symm

theorem e_h16 : stripMat h16 = ev MA MB w16 := by
  rw [w16, ev_append, ← e_h15]
  exact (mul1 wf_h15 wf_h15 (by bm_strips4 CFSG.KC.BM.HS.c_h16 69)).symm

theorem e_h17 : stripMat h17 = ev MA MB w17 := by
  rw [w17, ev_append, ← e_h16, ← e_h15]
  exact (mul1 wf_h16 wf_h15 (by bm_strips4 CFSG.KC.BM.HS.c_h17 69)).symm

theorem e_h18 : stripMat h18 = ev MA MB w18 := by
  rw [w18, ev_append, ← e_h4, ← e_x2]
  exact (mul1 wf_h4 wf_x2 (by bm_strips4 CFSG.KC.BM.HS.c_h18 69)).symm

theorem e_h19 : stripMat h19 = ev MA MB w19 := by
  rw [w19, ev_append, ← e_x2, ← e_x1]
  exact (mul1 wf_x2 wf_x1 (by bm_strips4 CFSG.KC.BM.HS.c_h19 69)).symm

theorem e_h20 : stripMat h20 = ev MA MB w20 := by
  rw [w20, ev_append, ← e_n1, ← e_n2]
  exact (mul1 wf_n1 wf_n2 (by bm_strips4 CFSG.KC.BM.HS.c_h20 69)).symm

theorem e_h21 : stripMat h21 = ev MA MB w21 := by
  rw [w21, ev_append, ← e_n1, ← e_h18]
  exact (mul1 wf_n1 wf_h18 (by bm_strips4 CFSG.KC.BM.HS.c_h21 69)).symm

theorem e_h22 : stripMat h22 = ev MA MB w22 := by
  rw [w22, ev_append, ← e_h4, ← e_h21]
  exact (mul1 wf_h4 wf_h21 (by bm_strips4 CFSG.KC.BM.HS.c_h22 69)).symm

theorem e_h23 : stripMat h23 = ev MA MB w23 := by
  rw [w23, ev_append, ← e_n2]
  exact (mul1 wf_n2 wf_n2 (by bm_strips4 CFSG.KC.BM.HS.c_h23 69)).symm

theorem e_h24 : stripMat h24 = ev MA MB w24 := by
  rw [w24, ev_append, ← e_n1, ← e_x2]
  exact (mul1 wf_n1 wf_x2 (by bm_strips4 CFSG.KC.BM.HS.c_h24 69)).symm

theorem e_h25 : stripMat h25 = ev MA MB w25 := by
  rw [w25, ev_append, ← e_h19, ← e_x2]
  exact (mul1 wf_h19 wf_x2 (by bm_strips4 CFSG.KC.BM.HS.c_h25 69)).symm

theorem e_h26 : stripMat h26 = ev MA MB w26 := by
  rw [w26, ev_append, ← e_h22, ← e_h20]
  exact (mul1 wf_h22 wf_h20 (by bm_strips4 CFSG.KC.BM.HS.c_h26 69)).symm

theorem e_h27 : stripMat h27 = ev MA MB w27 := by
  rw [w27, ev_append, ← e_h24, ← e_h4]
  exact (mul1 wf_h24 wf_h4 (by bm_strips4 CFSG.KC.BM.HS.c_h27 69)).symm

end Nodes

theorem rels_of {M : Type*} [Monoid M] {A B : M} (hB : B ^ 5 = 1) (r0 : ev A B [false, false] = 1) (r2 : ev A B wab11 = 1)
    (r3 : ev A B (w8 ++ w8 ++ w7) = 1) (r4 : ev A B (w11 ++ w9) = 1)
    (r5 : ev A B (w14 ++ w13) = 1) (r6 : ev A B (w17 ++ w17) = 1)
    (r7 : ev A B (w20 ++ w27 ++ w23 ++ w23 ++ w18) = 1)
    (r8 : ev A B (w25 ++ w23 ++ wx2 ++ w23 ++ w25 ++ w24 ++ wn1) = 1)
    (r9 : ev A B (w7 ++ w4 ++ wn2 ++ w20 ++ w18 ++ w19 ++ wn1 ++ w9) = 1)
    (r10 : ev A B (w26 ++ w26) = 1) (r11 : ev A B (w18 ++ w22 ++ w7 ++ w22) = 1)
    (r12 : ev A B (w19 ++ w25 ++ w18 ++ w9 ++ wn2 ++ wx1 ++ w27) = 1) :
    ∀ v ∈ TauCeti.Sporadic.hsPresentation.relatorLetters, CFSG.KC.BM.HS.relVal A B v = 1 := by
  have hA : A * A = 1 := by rwa [ev_ff] at r0
  have rot := @ev_of_rotOf M _ A B hA hB
  intro v hv
  rw [CFSG.KC.BM.HS.relVal, prod_letters]
  rw [CFSG.KC.HSK.rels_eq] at hv
  simp only [CFSG.KC.HSK.relsLit, List.mem_cons, List.mem_nil_iff, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rot (by decide +kernel) r0
  · exact rot (by decide +kernel) (ev_nil A B)
  · exact rot (by decide +kernel) r2
  · exact rot (by decide +kernel) r3
  · exact rot (by decide +kernel) r4
  · exact rot (by decide +kernel) r5
  · exact rot (by decide +kernel) r6
  · exact rot (by decide +kernel) r7
  · exact rot (by decide +kernel) r8
  · exact rot (by decide +kernel) r9
  · exact rot (by decide +kernel) r10
  · exact rot (by decide +kernel) r11
  · exact rot (by decide +kernel) r12

section Rels

open CFSG.KC.BM.HS

theorem a_sq : MA * MA = 1 := one1 wf_a wf_a (by bm_strips4 CFSG.KC.BM.HS.rel0 69)

theorem b_five : MB ^ 5 = 1 := by
  have e := mul1 (C := a) wf_n1 wf_b (by bm_strips4 CFSG.KC.BM.HS.rel1 69)
  have hn : stripMat n1 = MA * MB ^ 4 := by
    rw [e_n1, wn1, wn2, wx2, wx1, ev_n1]
  rw [hn, mul_assoc, ← pow_succ] at e
  have e5 : MA * MB ^ 5 = MA := e
  calc MB ^ 5 = MA * MA * MB ^ 5 := by rw [a_sq, one_mul]
    _ = 1 := by rw [mul_assoc, e5, a_sq]

theorem ab11 : ev MA MB wab11 = 1 := by
  have e := mul1 (C := x1) wf_h6 wf_h5 (by bm_strips4 CFSG.KC.BM.HS.rel2 69)
  rw [e_h6, e_h5, e_x1, ← ev_append] at e
  have hw : w6 ++ w5 = wab11 ++ wx1 := by decide +kernel
  rw [hw, ev_append] at e
  have hinv : ev MA MB wx1 * ev MA MB [true, true, true, true, false] = 1 := by
    rw [← ev_append, ← ev_red0 b_five]
    have hr : red 0 (wx1 ++ [true, true, true, true, false]) = [false, false] := by decide +kernel
    rw [hr, ev_ff]
    exact a_sq
  calc ev MA MB wab11 = ev MA MB wab11 * (ev MA MB wx1 * ev MA MB [true, true, true, true, false]) :=
        by rw [hinv, mul_one]
    _ = 1 := by rw [← mul_assoc, e, hinv]

theorem c0 : ev MA MB [false, false] = 1 := by
  rw [ev_ff]
  exact a_sq

theorem c3 : ev MA MB (w8 ++ w8 ++ w7) = 1 := by
  have e := stripMat_mul_eq_one (Ws := [h8, h7]) (by simp [wf_h8, wf_h7]) wf_h8
    (by bm_strips4 CFSG.KC.BM.HS.rel3 69)
  simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil] at e
  rw [e_h8, e_h7, ← ev_append, ← ev_append] at e
  exact e

theorem c4 : ev MA MB (w11 ++ w9) = 1 := by
  have e := stripMat_mul_eq_one (Ws := [h9]) (by simp [wf_h9]) wf_h11
    (by bm_strips4 CFSG.KC.BM.HS.rel4 69)
  simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil] at e
  rw [e_h11, e_h9, ← ev_append] at e
  exact e

theorem c5 : ev MA MB (w14 ++ w13) = 1 := by
  have e := stripMat_mul_eq_one (Ws := [h13]) (by simp [wf_h13]) wf_h14
    (by bm_strips4 CFSG.KC.BM.HS.rel5 69)
  simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil] at e
  rw [e_h14, e_h13, ← ev_append] at e
  exact e

theorem c6 : ev MA MB (w17 ++ w17) = 1 := by
  have e := stripMat_mul_eq_one (Ws := [h17]) (by simp [wf_h17]) wf_h17
    (by bm_strips4 CFSG.KC.BM.HS.rel6 69)
  simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil] at e
  rw [e_h17, ← ev_append] at e
  exact e

theorem c7 : ev MA MB (w20 ++ w27 ++ w23 ++ w23 ++ w18) = 1 := by
  have e := stripMat_mul_eq_one (Ws := [h27, h23, h23, h18])
    (by simp [wf_h27, wf_h23, wf_h18]) wf_h20 (by bm_strips4 CFSG.KC.BM.HS.rel7 69)
  simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil] at e
  rw [e_h20, e_h27, e_h23, e_h18] at e
  simp only [← ev_append] at e
  exact e

theorem c8 : ev MA MB (w25 ++ w23 ++ wx2 ++ w23 ++ w25 ++ w24 ++ wn1) = 1 := by
  have e := stripMat_mul_eq_one (Ws := [h23, x2, h23, h25, h24, n1])
    (by simp [wf_h23, wf_x2, wf_h25, wf_h24, wf_n1]) wf_h25 (by bm_strips4 CFSG.KC.BM.HS.rel8 69)
  simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil] at e
  rw [e_h25, e_h23, e_x2, e_h24, e_n1] at e
  simp only [← ev_append] at e
  exact e

theorem c9 : ev MA MB (w7 ++ w4 ++ wn2 ++ w20 ++ w18 ++ w19 ++ wn1 ++ w9) = 1 := by
  have e := stripMat_mul_eq_one (Ws := [h4, n2, h20, h18, h19, n1, h9])
    (by simp [wf_h4, wf_n2, wf_h20, wf_h18, wf_h19, wf_n1, wf_h9]) wf_h7
    (by bm_strips4 CFSG.KC.BM.HS.rel9 69)
  simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil] at e
  rw [e_h7, e_h4, e_n2, e_h20, e_h18, e_h19, e_n1, e_h9] at e
  simp only [← ev_append] at e
  exact e

theorem c10 : ev MA MB (w26 ++ w26) = 1 := by
  have e := stripMat_mul_eq_one (Ws := [h26]) (by simp [wf_h26]) wf_h26
    (by bm_strips4 CFSG.KC.BM.HS.rel10 69)
  simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil] at e
  rw [e_h26, ← ev_append] at e
  exact e

theorem c11 : ev MA MB (w18 ++ w22 ++ w7 ++ w22) = 1 := by
  have e := stripMat_mul_eq_one (Ws := [h22, h7, h22]) (by simp [wf_h22, wf_h7]) wf_h18
    (by bm_strips4 CFSG.KC.BM.HS.rel11 69)
  simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil] at e
  rw [e_h18, e_h22, e_h7] at e
  simp only [← ev_append] at e
  exact e

theorem c12 : ev MA MB (w19 ++ w25 ++ w18 ++ w9 ++ wn2 ++ wx1 ++ w27) = 1 := by
  have e := stripMat_mul_eq_one (Ws := [h25, h18, h9, n2, x1, h27])
    (by simp [wf_h25, wf_h18, wf_h9, wf_n2, wf_x1, wf_h27]) wf_h19
    (by bm_strips4 CFSG.KC.BM.HS.rel12 69)
  simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil] at e
  rw [e_h19, e_h25, e_h18, e_h9, e_n2, e_x1, e_h27] at e
  simp only [← ev_append] at e
  exact e

theorem rels : ∀ v ∈ TauCeti.Sporadic.hsPresentation.relatorLetters, relVal MA MB v = 1 :=
  @rels_of MatB _ MA MB b_five c0 ab11 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12

end Rels

theorem fact17535 : CFSG.KC.BM.HS.Fact17535 MG1 MG2 := by
  unfold CFSG.KC.BM.HS.Fact17535
  refine ⟨?_, ?_, ?_, a_s, b_s, ?_⟩
  · rw [← a_eq]
    exact a_sq
  · rw [← a_eq]
    exact a_ne
  · rw [← b_eq]
    exact b_five
  · rw [← a_eq, ← b_eq]
    exact rels

end CertificateChecks.KernelBM.HS

end
