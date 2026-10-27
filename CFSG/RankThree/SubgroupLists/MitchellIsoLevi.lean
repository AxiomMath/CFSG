module

public import CFSG.RankThree.SubgroupLists.MitchellIsotropic
import CFSG.RankThree.SubgroupLists.SymplecticInvolutionPairs
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.RankThree.SubgroupLists

open Matrix CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

local notation "V₄" => Fin 2 ⊕ Fin 2

variable {K : Type} [Field K]

@[expose] noncomputable def isoLeviImage (K : Type) [Field K] (G : Subgroup (GL V₄ K)) :
    Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) :=
  ((G.subgroupOf (isoCent K)).map (leviHom K)).map
    (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)))

@[expose] noncomputable def isoLeviBar {G : Subgroup (GL V₄ K)} {x : GL V₄ K} (hxG : x ∈ G)
    (hxC : x ∈ isoCent K) : isoLeviImage K G :=
  ⟨QuotientGroup.mk' _ (leviHom K ⟨x, hxC⟩),
    Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ (show (⟨x, hxC⟩ : isoCent K) ∈
      G.subgroupOf (isoCent K) from hxG))⟩

section Bar

variable {G : Subgroup (GL V₄ K)}

theorem isoLeviBar_mul {x y : GL V₄ K} (hxG : x ∈ G) (hxC : x ∈ isoCent K) (hyG : y ∈ G)
    (hyC : y ∈ isoCent K) :
    isoLeviBar hxG hxC * isoLeviBar hyG hyC = isoLeviBar (G.mul_mem hxG hyG) (mul_mem hxC hyC) := by
  apply Subtype.ext
  simp only [isoLeviBar, Subgroup.coe_mul, ← map_mul]
  rfl

theorem isoLeviBar_pow {x : GL V₄ K} (hxG : x ∈ G) (hxC : x ∈ isoCent K) (k : ℕ) :
    isoLeviBar hxG hxC ^ k = isoLeviBar (G.pow_mem hxG k) (pow_mem hxC k) := by
  apply Subtype.ext
  simp only [isoLeviBar, SubgroupClass.coe_pow, ← map_pow]
  rfl

theorem isoLeviBar_inv {x : GL V₄ K} (hxG : x ∈ G) (hxC : x ∈ isoCent K) :
    (isoLeviBar hxG hxC)⁻¹ = isoLeviBar (G.inv_mem hxG) (inv_mem hxC) := by
  apply Subtype.ext
  simp only [isoLeviBar, InvMemClass.coe_inv, ← map_inv]
  rfl

theorem exists_isoLeviBar_eq (y : isoLeviImage K G) :
    ∃ (x : GL V₄ K) (hxG : x ∈ G) (hxC : x ∈ isoCent K), isoLeviBar hxG hxC = y := by
  obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp y.2
  obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hz
  exact ⟨w, Subgroup.mem_subgroupOf.mp hw, w.2, Subtype.ext hzy⟩

theorem isoLeviBar_eq_one_iff {x : GL V₄ K} (hxG : x ∈ G) (hxC : x ∈ isoCent K) :
    isoLeviBar hxG hxC = 1 ↔ leviBlock (x : Matrix V₄ V₄ K) = 1 ∨
      leviBlock (x : Matrix V₄ V₄ K) = -1 := by
  have e1 : isoLeviBar hxG hxC = 1 ↔
      QuotientGroup.mk' (Subgroup.center SL(2, K)) (leviHom K ⟨x, hxC⟩) = 1 := by
    rw [Subtype.ext_iff]
    rfl
  rw [e1, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Matrix.SpecialLinearGroup.mem_center_iff]
  constructor
  · rintro ⟨r, hr, hrx⟩
    have hx : Matrix.scalar (Fin 2) r = leviBlock (x : Matrix V₄ V₄ K) := by
      rw [hrx, coe_leviHom]
    have hr2 : (r - 1) * (r + 1) = 0 := by
      simp only [Fintype.card_fin] at hr
      linear_combination hr
    rcases mul_eq_zero.mp hr2 with h | h
    · left
      rw [← hx, show r = 1 by linear_combination h]
      simp
    · right
      rw [← hx, show r = -1 by linear_combination h]
      ext i j; fin_cases i <;> fin_cases j <;> simp
  · rintro (h | h)
    · refine ⟨1, by simp, ?_⟩
      rw [coe_leviHom, h]
      simp
    · refine ⟨-1, by simp, ?_⟩
      rw [coe_leviHom, h]
      ext i j; fin_cases i <;> fin_cases j <;> simp

theorem leviBlock_val_mul (x : GL V₄ K) {y : GL V₄ K} (hy : y ∈ isoCent K) :
    leviBlock ((x * y : GL V₄ K) : Matrix V₄ V₄ K) =
      leviBlock (x : Matrix V₄ V₄ K) * leviBlock (y : Matrix V₄ V₄ K) := by
  rw [Units.val_mul]
  exact leviBlock_mul (entries_of_commute_isoStd hy.2).1

theorem leviBlock_val_pow {x : GL V₄ K} (hx : x ∈ isoCent K) (k : ℕ) :
    leviBlock ((x ^ k : GL V₄ K) : Matrix V₄ V₄ K) = leviBlock (x : Matrix V₄ V₄ K) ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, Units.val_one, leviBlock_one]
  | succ k ih => rw [pow_succ, leviBlock_val_mul _ hx, ih, pow_succ]

theorem eq_of_leviBlock_eq (hU0 : ∀ x ∈ G, IsSqZero x → x = 1) {x y : GL V₄ K} (hxG : x ∈ G)
    (hyG : y ∈ G) (hxC : x ∈ isoCent K) (hyC : y ∈ isoCent K)
    (h : leviBlock (x : Matrix V₄ V₄ K) = leviBlock (y : Matrix V₄ V₄ K)) : x = y := by
  have h1 : leviBlock ((x * y⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) = 1 := by
    rw [leviBlock_val_mul _ (inv_mem hyC), h, ← leviBlock_val_mul _ (inv_mem hyC), mul_inv_cancel,
      Units.val_one, leviBlock_one]
  exact mul_inv_eq_one.mp (hU0 _ (G.mul_mem hxG (G.inv_mem hyG))
    (isSqZero_of_leviBlock_eq_one (mul_mem hxC (inv_mem hyC)) h1))

theorem exists_leviBlock_eq_of_mem (hneg : (-1 : GL V₄ K) ∈ G) {A : SL(2, K)}
    (hA : QuotientGroup.mk' (Subgroup.center SL(2, K)) A ∈ isoLeviImage K G) :
    ∃ w ∈ G, w ∈ isoCent K ∧ leviBlock (w : Matrix V₄ V₄ K) = (A : Matrix (Fin 2) (Fin 2) K) := by
  obtain ⟨z, hz, hzA⟩ := Subgroup.mem_map.mp hA
  obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hz
  obtain ⟨c, hc, hwc⟩ := (QuotientGroup.mk'_eq_mk' _).mp hzA
  obtain ⟨r, hr, hrc⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
  have hA' : (A : Matrix (Fin 2) (Fin 2) K) = r • leviBlock ((w : GL V₄ K) : Matrix V₄ V₄ K) := by
    rw [← hwc, Matrix.SpecialLinearGroup.coe_mul, ← hrc, coe_leviHom]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]
  have hr2 : (r - 1) * (r + 1) = 0 := by
    simp only [Fintype.card_fin] at hr
    linear_combination hr
  rcases mul_eq_zero.mp hr2 with h | h
  · refine ⟨w, Subgroup.mem_subgroupOf.mp hw, w.2, ?_⟩
    rw [hA', show r = 1 by linear_combination h, one_smul]
  · have hmC : (-1 : GL V₄ K) ∈ isoCent K :=
      Subgroup.mem_inf.mpr ⟨neg_one_mem_statedSp_two, by rw [mem_matCent]; simp⟩
    refine ⟨-1 * w, G.mul_mem hneg (Subgroup.mem_subgroupOf.mp hw), mul_mem hmC w.2, ?_⟩
    rw [leviBlock_val_mul _ w.2, hA', show r = -1 by linear_combination h]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [leviBlock, Matrix.mul_apply, Fin.sum_univ_two]

end Bar

end CFSG.RankThree.SubgroupLists
