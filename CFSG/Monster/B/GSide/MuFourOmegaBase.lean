
module

public import CFSG.Monster.B.GSide.MuFourOmegaInputs
public import CFSG.Monster.B.TwoA.Amalgam.CoFiberGraphAdjBase

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.GSide

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.VisCert CFSG.Monster.SpinLattice
  CFSG.Monster.B.Short CFSG.Monster.B.Co2 CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Unitary

theorem gramArr_spec : ∀ i < 24, gramArr[i]! = gramRow i := by decide +kernel

theorem bL_dec_dec (r r' : ℕ) :
    QuadraticMap.polarBilin qL (dec r) (dec r') =
      (popc 24 (r &&& Native.actD 24 gramArr r') : ZMod 2) := by
  have hF : ∀ a b, ((popc 24 (r &&& (a ^^^ b)) : ℕ) : ZMod 2) =
      (popc 24 (r &&& a) : ZMod 2) + (popc 24 (r &&& b) : ZMod 2) := by
    intro a b
    rw [← bvec_dotProduct, ← bvec_dotProduct, ← bvec_dotProduct, bvec_xor, dotProduct_add]
  rw [Native.actD, xorHom_actGo (fun x => (popc 24 (r &&& x) : ZMod 2)) hF, Nat.and_zero,
    show popc 24 0 = 0 from rfl, Nat.cast_zero, zero_add, Finset.sum_range]
  show QuadraticMap.polarBilin qL (dec r) (∑ i : Fin 24, bvec 24 r' i • ellCls i) = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, bL_dec, gramArr_spec i i.2, bvec_apply, smul_eq_mul, ite_mul, one_mul, zero_mul]

theorem bW_decW (a b : ℕ) : Unitary.bW (decW a) (decW b) = (bWcode a b : ZMod 2) := by
  obtain ⟨ha, hea⟩ := decW_eq_mk a
  obtain ⟨hb, heb⟩ := decW_eq_mk b
  rw [hea, heb, bWcode, ZMod.natCast_mod]
  exact (polarBilin_qW_mk v0 _ _ _).trans (bL_dec_dec _ _)

def muIdx : Array ℕ :=
  #[15, 33, 34, 38, 43, 44, 57, 58, 67, 69, 76, 77, 78, 85, 86, 91, 106, 108, 121, 122, 132, 150,
    157, 162, 167, 170, 171, 172, 179, 183, 186, 187, 192, 207, 208, 211, 214, 229, 242, 263, 264,
    266, 269, 271, 297, 304, 307, 315, 317, 320, 325, 333, 336, 337, 339, 340, 341, 360, 362, 364,
    365, 368, 369, 372, 376, 379, 401, 427, 439, 445, 446, 453, 454, 455, 460, 469, 470, 474, 483,
    489, 502, 531, 539, 541, 547, 562, 566, 573, 590, 600, 604, 605, 608, 610, 622, 625, 634, 635,
    643, 645, 654, 661, 662, 663, 664, 665, 671, 673, 674, 685, 686, 689, 692, 699, 708, 711, 715,
    716, 719, 724, 742, 749, 756, 757, 760, 771, 772, 779, 785, 787, 794, 800, 803, 818, 821, 832,
    834, 835, 839, 843, 845, 849, 852, 862, 866, 873, 878, 879, 68, 90, 107, 126, 127, 128, 129,
    152, 156, 163, 166, 173, 175, 177, 178, 198, 213, 221, 246, 253, 255, 256, 259, 262, 265, 275,
    301, 306, 331, 342, 353, 370, 371, 374, 384, 409, 418, 468, 472, 505, 528, 546, 556, 567, 570,
    601, 611, 616, 639, 659, 668, 691, 714, 737, 741, 765, 767, 773, 774, 777, 788, 823, 831, 882,
    70, 84, 109, 131, 133, 136, 144, 145, 146, 147, 159, 164, 165, 184, 215, 217, 249, 274, 324,
    347, 363, 383, 389, 412, 413, 415, 443, 464, 517, 536, 575, 613, 631, 678, 696, 751, 758, 768,
    806, 840, 181, 222, 251, 258, 298, 299, 309, 334, 344, 348, 350, 352, 356, 357, 373, 397, 398,
    426, 431, 444, 466, 495, 509, 548, 549, 550, 572, 603, 606, 627, 644, 657, 670, 672, 676, 677,
    680, 690, 712, 723, 754, 755, 783, 805, 812, 847, 881, 884, 311, 351, 382, 430, 465, 554, 557,
    565, 624, 697, 702, 709, 753, 780, 844, 856, 285, 577, 588, 740, 286, 326, 576, 587]

def muPar : Array ℕ :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3,
    3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
    4, 4, 4, 4, 4, 4, 5, 5, 5, 5, 6, 6, 6, 6]

def muTreeCheck : Bool :=
  (List.range 324).all fun i => decide (muIdx[i]! < 891) &&
    bWcode 60 (6144 ^^^ n6VecArr[muIdx[i]!]!) == 0 &&
    (i == 0 || (decide (muPar[i]! < i) &&
      bWcode (6144 ^^^ n6VecArr[muIdx[i]!]!) (6144 ^^^ n6VecArr[muIdx[muPar[i]!]!]!) == 0))

def nodupMask : List ℕ → ℕ → Bool
  | [], _ => true
  | j :: l, m => !m.testBit j && nodupMask l (m ||| (1 <<< j))

theorem nodupMask_spec : ∀ (l : List ℕ) (m : ℕ), nodupMask l m = true →
    (∀ j ∈ l, m.testBit j = false) ∧ l.Nodup
  | [], _, _ => ⟨fun _ h => absurd h List.not_mem_nil, List.nodup_nil⟩
  | j :: l, m, h => by
    rw [nodupMask, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨hj, hl⟩ := nodupMask_spec l _ h.2
    have hbit : ∀ j' ∈ l, j' ≠ j ∧ m.testBit j' = false := fun j' hj' => by
      have h' := hj j' hj'
      rw [Nat.testBit_or, Bool.or_eq_false_iff, Nat.one_shiftLeft, Nat.testBit_two_pow] at h'
      exact ⟨fun e => by simp [e] at h', h'.1⟩
    refine ⟨fun j' hj' => ?_, List.nodup_cons.2 ⟨fun hm => (hbit j hm).1 rfl, hl⟩⟩
    rcases List.mem_cons.1 hj' with rfl | hj'
    · exact h.1
    · exact (hbit j' hj').2

theorem muTreeCheck_eq : muTreeCheck = true := by decide +kernel

attribute [local irreducible] muIdx muPar

theorem nodupMask_muIdx : nodupMask muIdx.toList 0 = true := by decide +kernel

theorem muIdx_size : muIdx.size = 324 := by decide +kernel

theorem muTree_spec (i : ℕ) (hi : i < 324) :
    muIdx[i]! < 891 ∧ bWcode 60 (6144 ^^^ n6VecArr[muIdx[i]!]!) = 0 ∧
      (i ≠ 0 → muPar[i]! < i ∧
        bWcode (6144 ^^^ n6VecArr[muIdx[i]!]!) (6144 ^^^ n6VecArr[muIdx[muPar[i]!]!]!) = 0) := by
  have h := List.all_eq_true.1 muTreeCheck_eq i (List.mem_range.2 hi)
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.or_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, h2, fun hi0 => ?_⟩
  rcases h3 with h3 | h3
  · exact absurd h3 hi0
  · exact h3

theorem muIdx_inj {i i' : ℕ} (hi : i < 324) (hi' : i' < 324) (h : muIdx[i]! = muIdx[i']!) :
    i = i' := by
  have hn := (nodupMask_spec _ _ nodupMask_muIdx).2
  rw [getElem!_pos muIdx i (by rw [muIdx_size]; exact hi),
    getElem!_pos muIdx i' (by rw [muIdx_size]; exact hi'), ← Array.getElem_toList,
    ← Array.getElem_toList] at h
  exact (hn.getElem_inj_iff).1 h

def muJ (i : Fin 324) : Fin 891 := ⟨muIdx[(i : ℕ)]!, (muTree_spec i i.2).1⟩

theorem muJ_val (i : Fin 324) : (muJ i : ℕ) = muIdx[(i : ℕ)]! := rfl

theorem muJ_injective : Function.Injective muJ := by
  intro i i' h
  have h' := congrArg Fin.val h
  rw [muJ_val, muJ_val] at h'
  exact Fin.ext (muIdx_inj i.2 i'.2 h')

def omegaSMulHom
    (k : Kstab v0) : omegaGraph →g omegaGraph where
  toFun x := k • x
  map_rel' h := (Amalgam.omegaGraph_adj_smul k _ _).2 h

end CFSG.Monster.B.GSide
