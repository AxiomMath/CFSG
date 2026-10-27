module

public import CFSG.Fischer.Classification.Orthogonal3.Model
public import CFSG.Fischer.Classification.PartIII.Beta.Forms
import CFSG.Fischer.Classification.Recognition.R3Order
import CFSG.GH74.Exceptional.UnitaryFourTwo
import CFSG.LocalAnalysis.StandardType.ZS.DThreeTernaryChain
public import CFSG.Fischer.Pairs
public import CFSG.Open.Defs
import CFSG.Assembly.Subnormal
import CFSG.Fischer.Uniq.CompTau
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82

public section

namespace CFSG.StandardType.ZS

open CFSG.Fischer.Classification
open CFSG.Fischer.Classification.Recognition.R3

local instance (priority := high) zodAddCommGroup : AddCommGroup (ZMod 3) :=
  Ring.toAddCommGroup

private noncomputable def zod_tailEquivDiagF3 (n : ℕ) :
    F3.perpOne (diagF3 (n + 1) 1) (Pi.single 0 1) ≃ₗ[ZMod 3] (Fin n → ZMod 3) where
  toFun x := fun i => (x : Fin (n + 1) → ZMod 3) i.succ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun y := ⟨Fin.cons 0 y, by
    rw [F3.mem_perpOne, diagF3_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hi : i = 0
    · subst hi
      simp
    · rw [Pi.single_eq_of_ne hi]
      ring⟩
  left_inv x := Subtype.ext (by
    have hx0 : (x : Fin (n + 1) → ZMod 3) 0 = 0 := by
      have h := F3.mem_perpOne.1 x.2
      rw [diagF3_apply, Finset.sum_eq_single 0] at h
      · have hentry : diagF3Entry (n + 1) 1 0 = 1 := by simp [diagF3Entry]
        rw [hentry, Pi.single_eq_same, mul_one, one_mul] at h
        exact h
      · intro i _ hi
        rw [Pi.single_eq_of_ne hi]
        ring
      · intro h
        exact absurd (Finset.mem_univ 0) h
    funext i
    cases i using Fin.cases with
    | zero => simp [hx0]
    | succ i => rfl)
  right_inv y := by
    funext i
    rfl

private theorem zod_norm_diagF3_single_zero (n : ℕ) :
    diagF3 (n + 1) 1 (Pi.single 0 1) (Pi.single 0 1) = 1 := by
  rw [diagF3_apply, Finset.sum_eq_single 0]
  · simp [diagF3Entry]
  · intro i _ hi
    rw [Pi.single_eq_of_ne hi]
    ring
  · intro h
    exact absurd (Finset.mem_univ 0) h

private theorem zod_tailEquivDiagF3_symm_apply (n : ℕ) (a : Fin n → ZMod 3) :
    (((zod_tailEquivDiagF3 n).symm a :
        F3.perpOne (diagF3 (n + 1) 1) (Pi.single 0 1)) :
      Fin (n + 1) → ZMod 3) = Fin.cons 0 a := by
  rw [LinearEquiv.coe_symm_mk]
  rfl

private theorem zod_restrictForm_diagF3_tail (n : ℕ) :
    restrictForm (diagF3 (n + 1) 1) (zod_tailEquivDiagF3 n) = diagF3 n 1 := by
  refine LinearMap.ext₂ fun a b => ?_
  rw [← (zod_tailEquivDiagF3 n).apply_symm_apply a,
    ← (zod_tailEquivDiagF3 n).apply_symm_apply b, restrictForm_apply,
    zod_tailEquivDiagF3_symm_apply, zod_tailEquivDiagF3_symm_apply,
    (zod_tailEquivDiagF3 n).apply_symm_apply,
    (zod_tailEquivDiagF3 n).apply_symm_apply]
  change diagF3 (n + 1) 1 (Fin.cons 0 a) (Fin.cons 0 b) = diagF3 n 1 a b
  rw [diagF3_apply, diagF3_apply, Fin.sum_univ_succ]
  simp [diagF3Entry]

private theorem zod_normTriple_diagF3_one_zero :
    (normCount (diagF3 1 1) 0, normCount (diagF3 1 1) 1, normCount (diagF3 1 1) 2) =
      (1, 2, 0) := by
  rcases normTriple_one (f := diagF3 1 1) (isF3Form_diagF3 one_ne_zero) with h | h
  · exact h
  · exfalso
    have hpos : 0 < normCount (diagF3 1 1) 1 := by
      rw [normCount_def, Nat.card_pos_iff]
      exact ⟨⟨Pi.single 0 1, zod_norm_diagF3_single_zero 0⟩, inferInstance⟩
    have h1 : normCount (diagF3 1 1) 1 = 0 := by
      simpa using congrArg (fun t : ℕ × ℕ × ℕ => t.2.1) h
    rw [h1] at hpos
    exact (Nat.lt_irrefl 0) hpos

private theorem zod_normTriple_diagF3_one (k : ℕ) :
    (normCount (diagF3 (k + 1) 1) 0, normCount (diagF3 (k + 1) 1) 1,
      normCount (diagF3 (k + 1) 1) 2) = T^[k] (1, 2, 0) := by
  induction k with
  | zero => exact zod_normTriple_diagF3_one_zero
  | succ k ih =>
    have hf : IsF3Form (diagF3 (k + 2) 1) := isF3Form_diagF3 one_ne_zero
    have hv : diagF3 (k + 2) 1 (Pi.single 0 1) (Pi.single 0 1) = 1 :=
      zod_norm_diagF3_single_zero (k + 1)
    have h0 := normCount_eq (f := diagF3 (k + 2) 1) (v := Pi.single 0 1) hf hv
      (zod_tailEquivDiagF3 (k + 1)) 0
    have h1 := normCount_eq (f := diagF3 (k + 2) 1) (v := Pi.single 0 1) hf hv
      (zod_tailEquivDiagF3 (k + 1)) 1
    have h2 := normCount_eq (f := diagF3 (k + 2) 1) (v := Pi.single 0 1) hf hv
      (zod_tailEquivDiagF3 (k + 1)) 2
    rw [zod_restrictForm_diagF3_tail (k + 1)] at h0 h1 h2
    have h01 : (0 : ZMod 3) - 1 = 2 := by decide
    have h21 : (2 : ZMod 3) - 1 = 1 := by decide
    have h0' : normCount (diagF3 (k + 2) 1) 0 =
        normCount (diagF3 (k + 1) 1) 0 + 2 * normCount (diagF3 (k + 1) 1) 2 := by
      simpa [h01] using h0
    have h1' : normCount (diagF3 (k + 2) 1) 1 =
        normCount (diagF3 (k + 1) 1) 1 + 2 * normCount (diagF3 (k + 1) 1) 0 := by
      simpa using h1
    have h2' : normCount (diagF3 (k + 2) 1) 2 =
        normCount (diagF3 (k + 1) 1) 2 + 2 * normCount (diagF3 (k + 1) 1) 1 := by
      simpa [h21] using h2
    rw [h0', h1', h2']
    rw [Function.iterate_succ_apply', ← ih]
    rfl

private theorem zod_normCount_diagF3_six_one : normCount (diagF3 6 1) 1 = 252 := by
  have h := congrArg (fun t : ℕ × ℕ × ℕ => t.2.1) (zod_normTriple_diagF3_one 5)
  have h5 : (T^[5] (1, 2, 0)).2.1 = 252 := by decide
  rw [h5] at h
  simpa using h

private theorem zod_card_center_reflGroup_diagF3_one {m : ℕ} (hm : 4 ≤ m) :
    Nat.card (Subgroup.center (F3.reflGroup (diagF3 m 1))) = 2 := by
  let p : F3.reflGroup (diagF3 m 1) :=
    (List.ofFn fun i : Fin m => reflElt (diagF3 m 1) (Pi.single i 1)).prod
  have hp : p ∈ Subgroup.center (F3.reflGroup (diagF3 m 1)) :=
    prod_ofFn_reflElt_single_mem_center m
  have hpcoe : (p : GL (Fin m) (ZMod 3)) = -1 := coe_prod_ofFn_reflElt_single m
  have hpne : (1 : F3.reflGroup (diagF3 m 1)) ≠ p := by
    intro h
    have hcoe : (1 : GL (Fin m) (ZMod 3)) = -1 := by
      rw [← hpcoe]
      exact congrArg (fun z : F3.reflGroup (diagF3 m 1) =>
        (z : GL (Fin m) (ZMod 3))) h
    have hm0 : 0 < m := by omega
    let i : Fin m := ⟨0, hm0⟩
    have hii := congrArg (fun g : GL (Fin m) (ZMod 3) =>
      ((g : Matrix (Fin m) (Fin m) (ZMod 3)) i i)) hcoe
    have hii' : (1 : ZMod 3) = -1 := by simpa using hii
    exact (by decide : (1 : ZMod 3) ≠ -1) hii'
  have hset : (Subgroup.center (F3.reflGroup (diagF3 m 1)) :
      Set (F3.reflGroup (diagF3 m 1))) = {1, p} := by
    ext z
    constructor
    · intro hz
      rcases F3.coe_eq_of_mem_center (isF3Form_diagF3 one_ne_zero) hm hz with h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext (by rw [h, hpcoe]))
    · rintro (rfl | rfl)
      · exact Subgroup.one_mem _
      · exact hp
  rw [← SetLike.coe_sort_coe (Subgroup.center (F3.reflGroup (diagF3 m 1))),
    Nat.card_coe_set_eq, hset, Set.ncard_pair hpne]

theorem natCard_R3_diagF3_five_one : Nat.card (R3 (diagF3 5 1)) = 25920 := by
  obtain ⟨ψ, -⟩ := exists_mulEquiv_U2_four_R3_I5
  rw [diagF3_five_one]
  rw [← Nat.card_congr ψ.toEquiv, CFSG.GH74.Exceptional.card_U2_four]

private theorem zod_natCard_reflGroup_diagF3_five_one :
    Nat.card (F3.reflGroup (diagF3 5 1)) = 51840 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.center (F3.reflGroup (diagF3 5 1)))
  rw [zod_card_center_reflGroup_diagF3_one (by norm_num),
    natCard_R3_diagF3_five_one] at h
  omega

theorem le_natCard_R3_diagF3_six_one : 6531840 ≤ Nat.card (R3 (diagF3 6 1)) := by
  have hf : IsF3Form (diagF3 6 1) := isF3Form_diagF3 one_ne_zero
  have hv : diagF3 6 1 (Pi.single 0 1) (Pi.single 0 1) = 1 :=
    zod_norm_diagF3_single_zero 5
  have hdvd := normCount_mul_card_dvd (f := diagF3 6 1) (v := Pi.single 0 1) (n := 5)
    hf (by norm_num) hv (zod_tailEquivDiagF3 5)
  rw [zod_restrictForm_diagF3_tail 5, zod_natCard_reflGroup_diagF3_five_one,
    zod_normCount_diagF3_six_one] at hdvd
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.center (F3.reflGroup (diagF3 6 1)))
  have hc : Nat.card (Subgroup.center (F3.reflGroup (diagF3 6 1))) ≤ 2 := by
    rw [zod_card_center_reflGroup_diagF3_one (by norm_num)]
  have hpos : 0 < Nat.card (F3.reflGroup (diagF3 6 1)) := Nat.card_pos
  have hdivle : 252 * 51840 ≤ Nat.card (F3.reflGroup (diagF3 6 1)) :=
    Nat.le_of_dvd hpos hdvd
  have hle : Nat.card (F3.reflGroup (diagF3 6 1)) ≤ Nat.card (R3 (diagF3 6 1)) * 2 := by
    rw [hcard]
    exact Nat.mul_le_mul_left _ hc
  have h2 : 2 * 6531840 ≤ Nat.card (R3 (diagF3 6 1)) * 2 := by
    have hM : 2 * 6531840 = 252 * 51840 := by norm_num
    rw [hM]
    exact le_trans hdivle hle
  omega

end CFSG.StandardType.ZS
