module

public import CFSG.Quasithin.Vol2.Ch3Sec3Sp4ZFox
public import CFSG.Fischer.F4
public import CFSG.RankThree.SubgroupLists.SymplecticTransvections
import all CFSG.Fischer.F4

public section

namespace CFSG.Quasithin.H13.Sp4Z

open Matrix CFSG.Fischer CFSG.Assembly.LowTwoRank CFSG.RankThree.SubgroupLists

abbrev Idx : Type := Fin 2 ⊕ Fin 2

@[expose] def w1 : F4 := ⟨2⟩

@[expose] def w2 : F4 := ⟨3⟩

@[expose] def vec4 (x y z t : F4) : Idx → F4
  | Sum.inl 0 => x
  | Sum.inl 1 => y
  | Sum.inr 0 => z
  | Sum.inr 1 => t

theorem eq_vec4 (v : Idx → F4) :
    v = vec4 (v (Sum.inl 0)) (v (Sum.inl 1)) (v (Sum.inr 0)) (v (Sum.inr 1)) := by
  funext i
  rcases i with i | i <;> fin_cases i <;> rfl

@[expose] def e0 : Idx → F4 := vec4 1 0 0 0

@[expose] def matA : Matrix Idx Idx F4 := fromBlocks 1 !![1, 0; 0, 0] 0 1

@[expose] def matB : Matrix Idx Idx F4 :=
  fromBlocks !![1, 1; w1, 0] !![w1, 1; w2, 0] !![1, 0; 0, w2] !![w1, 1; w2, 0]

@[expose] def matBinv : Matrix Idx Idx F4 :=
  fromBlocks !![w1, w2; 1, 0] !![w1, w2; 1, 0] !![1, 0; 0, w2] !![1, w1; 1, 0]

theorem matB_mul_matBinv : matB * matBinv = 1 := by decide +kernel

theorem matBinv_mul_matB : matBinv * matB = 1 := by decide +kernel

@[expose] noncomputable def genA : GL Idx F4 := spTrans e0 1

@[expose] def genB : GL Idx F4 := ⟨matB, matBinv, matB_mul_matBinv, matBinv_mul_matB⟩

theorem coe_genA : (genA : Matrix Idx Idx F4) = matA := by
  rw [genA, coe_spTrans]
  decide +kernel

theorem coe_genB : (genB : Matrix Idx Idx F4) = matB := rfl

theorem genA_mem : genA ∈ StatedSp 2 F4 := spTrans_mem_statedSp _ _

theorem genB_mem : genB ∈ StatedSp 2 F4 := by
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff, coe_genB]
  decide +kernel

@[expose] noncomputable def rhoA : (Idx → F4) →+ (Idx → F4) :=
  (Matrix.mulVecLin matA).toAddMonoidHom

@[expose] noncomputable def rhoB : (Idx → F4) →+ (Idx → F4) :=
  (Matrix.mulVecLin matB).toAddMonoidHom

@[expose] def matW : List Bool → Matrix Idx Idx F4
  | [] => 1
  | s :: w => (if s then matB else matA) * matW w

theorem coe_evalW (w : List Bool) :
    ((evalW genA genB w : GL Idx F4) : Matrix Idx Idx F4) = matW w := by
  induction w with
  | nil => rfl
  | cons s w ih =>
    cases s
    · rw [show evalW genA genB (false :: w) = genA * evalW genA genB w from rfl, Units.val_mul,
        ih, coe_genA]
      rfl
    · rw [show evalW genA genB (true :: w) = genB * evalW genA genB w from rfl, Units.val_mul,
        ih, coe_genB]
      rfl

theorem matW_mulVec (w : List Bool) (v : Idx → F4) : matW w *ᵥ v = actV rhoA rhoB w v := by
  induction w with
  | nil => exact Matrix.one_mulVec v
  | cons s w ih =>
    cases s
    · show (matA * matW w) *ᵥ v = matA *ᵥ actV rhoA rhoB w v
      rw [← Matrix.mulVec_mulVec, ih]
    · show (matB * matW w) *ᵥ v = matB *ᵥ actV rhoA rhoB w v
      rw [← Matrix.mulVec_mulVec, ih]

theorem evalW_mem_closure (w : List Bool) :
    evalW genA genB w ∈ Subgroup.closure ({genA, genB} : Set (GL Idx F4)) := by
  induction w with
  | nil => exact Subgroup.one_mem _
  | cons s w ih =>
    cases s
    · exact Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inl rfl)) ih
    · exact Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inr rfl)) ih

@[expose] def decodeW : ℕ → ℕ → List Bool
  | 0, _ => []
  | fuel + 1, m => if m ≤ 1 then [] else (m % 2 == 1) :: decodeW fuel (m / 2)

@[expose] def code4 (x y z t : F4) : ℕ :=
  x.code.val + 4 * y.code.val + 16 * z.code.val + 64 * t.code.val

@[expose] def orbitTable : List ℕ :=
  [1, 1, 219, 237, 3947, 30045, 215, 30719, 3439, 1791, 31675, 245, 991, 3831, 509, 6827, 3581,
   7162, 3418, 1709, 7661, 3967, 1917, 3834, 6, 3, 247, 494, 15023, 13823, 251, 502, 255, 959,
   443, 1918, 2014, 234, 1007, 117, 429, 218, 858, 109, 437, 493, 439, 986, 27350, 110, 55,
   13675, 119, 859, 1718, 238, 942, 3455, 6910, 471, 123, 118, 59, 246, 3837, 1719, 6879, 503,
   7919, 55285, 7679, 8125, 13661, 2045, 4091, 16253, 32479, 223, 8043, 13813, 62, 31, 8127,
   16254, 29, 58, 1790, 895, 239, 478, 1005, 2010, 3501, 1879, 4063, 8126, 3415, 30, 6830, 15,
   13662, 3759, 6831, 1965, 31674, 427, 15837, 854, 3838, 954, 1919, 477, 853, 55286, 27643,
   1706, 1022, 491, 982, 511, 14078, 890, 445, 7039, 122, 2046, 1023, 61, 221, 235, 495, 1983,
   8117, 253, 6839, 3755, 1707, 13663, 4021, 447, 8119, 55255, 4031, 8063, 3931, 7862, 4022,
   2011, 1915, 3830, 16122, 8061, 2015, 4030, 1978, 989, 6906, 3453, 27354, 13677, 3957, 16239,
   3519, 32478, 957, 27627, 1914, 27325, 3454, 254, 1727, 127, 13, 938, 26, 469, 8118, 1759,
   3518, 4059, 222, 7, 14, 111, 32474, 1979, 3829, 16237, 6826, 479, 958, 3413, 6837, 7895, 6911,
   1973, 32511, 3775, 1015, 1887, 32509, 110571, 28157, 3839, 7863, 13679, 32475, 1877, 15839,
   16255, 955, 1781, 7511, 15022, 27, 54, 6838, 3419, 879, 1758, 2031, 4062, 426, 213, 3959, 939,
   7918, 1878, 126, 7677, 63, 15354, 107, 3773, 214, 7546, 943, 862, 1886, 431, 863, 2029, 4058,
   1726, 875, 13821, 27642, 1750, 53, 1014, 507, 106, 250, 14079, 15359, 125]

theorem orbit_check : ∀ x y z t : F4, vec4 x y z t ≠ 0 →
    actV rhoA rhoB (decodeW 20 (orbitTable.getD (code4 x y z t) 1)) e0 = vec4 x y z t := by
  decide +kernel

theorem exists_eq_mulVec {v : Idx → F4} (hv : v ≠ 0) :
    ∃ h ∈ Subgroup.closure ({genA, genB} : Set (GL Idx F4)),
      (h : Matrix Idx Idx F4) *ᵥ e0 = v := by
  set w := decodeW 20 (orbitTable.getD (code4 (v (Sum.inl 0)) (v (Sum.inl 1)) (v (Sum.inr 0))
    (v (Sum.inr 1))) 1)
  refine ⟨evalW genA genB w, evalW_mem_closure w, ?_⟩
  rw [coe_evalW, matW_mulVec, eq_vec4 v]
  rw [eq_vec4 v] at hv
  exact orbit_check _ _ _ _ hv

theorem statedSp_eq_closure :
    StatedSp 2 F4 = Subgroup.closure ({genA, genB} : Set (GL Idx F4)) := by
  refine le_antisymm ?_ ((Subgroup.closure_le _).2 ?_)
  · rw [statedSp_eq_closure_spTrans, Subgroup.closure_le]
    rintro _ ⟨a, c, rfl⟩
    by_cases ha : a = 0
    · rw [ha, spTrans_zero_vec]
      exact Subgroup.one_mem _
    by_cases hc : c = 0
    · rw [hc, spTrans_zero]
      exact Subgroup.one_mem _
    have h1 : spTrans a c = spTrans ((c ^ 2) • a) 1 := by
      rw [spTrans_smul, F4.sq_sq, mul_one]
    have hca : (c ^ 2) • a ≠ 0 := smul_ne_zero (pow_ne_zero 2 hc) ha
    obtain ⟨h, hh, hhe⟩ := exists_eq_mulVec hca
    have hhS : h ∈ StatedSp 2 F4 := (Subgroup.closure_le _).2
      (by rintro _ (rfl | rfl); exacts [genA_mem, genB_mem]) hh
    rw [SetLike.mem_coe, h1, ← hhe, ← conj_spTrans hhS]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hh (Subgroup.subset_closure (Or.inl rfl)))
      (Subgroup.inv_mem _ hh)
  · rintro _ (rfl | rfl)
    exacts [genA_mem, genB_mem]

@[expose] def relW : Fin 3 → List Bool
  | 0 => [false, false]
  | 1 => List.flatten (List.replicate 3 ([false, true, false] ++ List.replicate 16 true))
  | 2 => List.flatten (List.replicate 5 ([false, true, true, false] ++ List.replicate 15 true))

theorem matW_relW : ∀ i : Fin 3, matW (relW i) = 1 := by decide +kernel

@[expose] def relIdx : Fin 6 → Fin 3
  | 0 => 0 | 1 => 0 | 2 => 1 | 3 => 1 | 4 => 2 | 5 => 2

@[expose] def relV : Fin 6 → Idx → F4
  | 0 => vec4 0 0 1 0 | 1 => vec4 0 0 w1 0 | 2 => vec4 0 1 0 0 | 3 => vec4 0 w1 0 0
  | 4 => vec4 0 1 0 0 | 5 => vec4 0 w1 0 0

@[expose] def relP : Fin 6 → Idx → F4
  | 0 => vec4 1 0 0 0 | 1 => vec4 w1 0 0 0 | 2 => vec4 w2 1 0 w2 | 3 => vec4 1 w1 0 1
  | 4 => vec4 1 0 0 1 | 5 => vec4 w1 0 0 w1

theorem foxV_rel : ∀ j : Fin 6, foxV rhoA rhoB (relW (relIdx j)) (relV j) = (relP j, 0) := by
  decide +kernel

theorem exists_sum_relP : ∀ x y t : F4, ∃ c : Fin 6 → Bool,
    vec4 x y 0 t = ∑ j, if c j then relP j else 0 := by
  decide +kernel

end CFSG.Quasithin.H13.Sp4Z
