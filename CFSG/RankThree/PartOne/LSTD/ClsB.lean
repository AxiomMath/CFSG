module

public import CFSG.RankThree.PartOne.LSTD.ClsBlock
public import CFSG.RankThree.PartOne.LSTD.ClsN
public import CFSG.RankThree.PartOne.KF.ClsSUUpper
public import CFSG.RankThree.PartOne.KFOUT3.L12Levi
public import CFSG.RankThree.PartOne.CTP.Phan5Group
public import CFSG.RankThree.PartOne.LSTD.Lift
public import CFSG.RankThree.PartOne.LSTD.TorusFacts

public section

namespace CFSG.RankThree.PartOne.LSTD

open Matrix CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryCoord CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.CTP

variable {f : ℕ} {K : Type} [Field K]

section Card

theorem card_unitarySU_two (hU : UnitaryFieldData 2 f K) :
    (Nat.card ↥(unitarySU 2 f K 2) : ℤ) =
      ((2 ^ f : ℕ) : ℤ) * (((2 ^ f : ℕ) : ℤ) ^ 2 - 1) := by
  have : CharP K 2 := hU.charP
  have h := card_statedSU_eq hU (n := 2) (by norm_num)
  have h2 : Finset.Icc 2 2 = {2} := by decide
  rw [h2, Finset.prod_singleton] at h
  simpa using h

theorem card_unitarySU_three (hU : UnitaryFieldData 2 f K) :
    (Nat.card ↥(unitarySU 2 f K 3) : ℤ) =
      ((2 ^ f : ℕ) : ℤ) ^ 3 * (((2 ^ f : ℕ) : ℤ) ^ 2 - 1) * (((2 ^ f : ℕ) : ℤ) ^ 3 + 1) := by
  have : CharP K 2 := hU.charP
  have h := card_statedSU_eq hU (n := 3) (by norm_num)
  have h2 : Finset.Icc 2 3 = {2, 3} := by decide
  rw [h2, Finset.prod_pair (by norm_num)] at h
  simp at h
  simpa [mul_assoc] using h

theorem not_dvd_card_su (hU : UnitaryFieldData 2 f K) (hf2 : 2 ≤ f) :
    ¬ Nat.card ↥(unitarySU 2 f K 3) ∣
      Nat.card ↥(unitarySU 2 f K 2) * Nat.card ↥(unitarySU 2 f K 2) := by
  intro hd
  have hq : (4 : ℤ) ≤ ((2 ^ f : ℕ) : ℤ) := by
    have : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
    have : (4 : ℕ) ≤ 2 ^ f := by simpa using this
    exact_mod_cast this
  set q : ℤ := ((2 ^ f : ℕ) : ℤ) with hqdef
  have h3 := card_unitarySU_three hU
  have h2 := card_unitarySU_two hU
  have hd' : (Nat.card ↥(unitarySU 2 f K 3) : ℤ) ∣
      (Nat.card ↥(unitarySU 2 f K 2) : ℤ) * (Nat.card ↥(unitarySU 2 f K 2) : ℤ) := by
    exact_mod_cast hd
  have hpos : 0 < (Nat.card ↥(unitarySU 2 f K 2) : ℤ) * (Nat.card ↥(unitarySU 2 f K 2) : ℤ) := by
    rw [h2]
    have : 0 < q * (q ^ 2 - 1) := by
      apply mul_pos (by linarith)
      nlinarith
    positivity
  have hle := Int.le_of_dvd hpos hd'
  rw [h3, h2] at hle
  have key : q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1) - q * (q ^ 2 - 1) * (q * (q ^ 2 - 1)) =
      q ^ 2 * (q ^ 2 - 1) * (q ^ 4 - q ^ 2 + q + 1) := by ring
  have hpos2 : 0 < q ^ 2 * (q ^ 2 - 1) * (q ^ 4 - q ^ 2 + q + 1) := by
    apply mul_pos (mul_pos (by positivity) (by nlinarith))
    nlinarith [sq_nonneg (q ^ 2 - q)]
  linarith

end Card

section Sep

variable {w : Fin 5 → Kˣ}

theorem sep_first (hB : B5 w) :
    ∀ (a : Fin 2) (j : Fin 5), j ∉ Set.range (![0, 1] : Fin 2 → Fin 5) →
      w ((![0, 1] : Fin 2 → Fin 5) a) ≠ w j := by
  obtain ⟨h02, h03, h04, h12, h13, h14, h24, h34⟩ := hB
  intro a j hj
  have hj' : j = 2 ∨ j = 3 ∨ j = 4 := by
    fin_cases j
    · exact absurd ⟨0, rfl⟩ hj
    · exact absurd ⟨1, rfl⟩ hj
    · simp
    · simp
    · simp
  rcases hj' with rfl | rfl | rfl <;> fin_cases a <;> assumption

theorem sep_second (hB : B5 w) :
    ∀ (a : Fin 2) (j : Fin 5), j ∉ Set.range (![2, 3] : Fin 2 → Fin 5) →
      w ((![2, 3] : Fin 2 → Fin 5) a) ≠ w j := by
  obtain ⟨h02, h03, h04, h12, h13, h14, h24, h34⟩ := hB
  intro a j hj
  have hj' : j = 0 ∨ j = 1 ∨ j = 4 := by
    fin_cases j
    · simp
    · simp
    · exact absurd ⟨0, rfl⟩ hj
    · exact absurd ⟨1, rfl⟩ hj
    · simp
  rcases hj' with rfl | rfl | rfl <;> fin_cases a <;> first | assumption | exact Ne.symm ‹_›

theorem sep_third (hB : B5 w) :
    ∀ (a : Fin 1) (j : Fin 5), j ∉ Set.range (![4] : Fin 1 → Fin 5) →
      w ((![4] : Fin 1 → Fin 5) a) ≠ w j := by
  obtain ⟨h02, h03, h04, h12, h13, h14, h24, h34⟩ := hB
  intro a j hj
  have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by
    fin_cases j
    · simp
    · simp
    · simp
    · simp
    · exact absurd ⟨0, rfl⟩ hj
  rcases hj' with rfl | rfl | rfl | rfl <;> fin_cases a <;> first | assumption | exact Ne.symm ‹_›

end Sep

theorem false_of_B5 [Finite K] (hU : UnitaryFieldData 2 f K) (h5 : 5 ∣ 2 ^ f + 1)
    {w : Fin 5 → Kˣ} (hw : w ∈ torusVec 5 5 K) (hB : B5 w)
    (X : Subgroup (StatedProj (unitarySU 2 f K 5))) (hX : Group.IsPerfect ↥X)
    (hXc : X ≤ Subgroup.centralizer
      ({projU K f (tSU hU h5 w hw)} : Set (StatedProj (unitarySU 2 f K 5))))
    (hXcard : Nat.card ↥X = Nat.card ↥(unitarySU 2 f K 3)) : False := by
  obtain ⟨H, hHperf, hHmap, hHC⟩ := exists_lift_perfect_centralizer (projU K f)
    projU_surjective (by rw [ker_projU]; exact scalarsU_le_center) (tSU hU h5 w hw) X hX hXc
  have hvan : ∀ h ∈ H, ∀ i j, w i ≠ w j →
      ((h : ↥(unitarySU 2 f K 5)) : GL (Fin 5) K).val i j = 0 := by
    intro h hh i j hij
    have hc := Subgroup.mem_centralizer_singleton_iff.mp (hHC hh)
    have hc' : ((h : ↥(unitarySU 2 f K 5)) : GL (Fin 5) K) * diagU w =
        diagU w * ((h : ↥(unitarySU 2 f K 5)) : GL (Fin 5) K) := congrArg Subtype.val hc
    exact KFOUT3.apply_eq_zero_of_commute_diagU' hc' hij
  have hrow : ∀ {k : ℕ} (e : Fin k → Fin 5), (∀ a j, j ∉ Set.range e → w (e a) ≠ w j) →
      ∀ h ∈ H, ∀ a j, j ∉ Set.range e →
        ((h : ↥(unitarySU 2 f K 5)) : GL (Fin 5) K).val (e a) j = 0 :=
    fun e hsep h hh a j hj => hvan h hh _ _ (hsep a j hj)
  have hcol : ∀ {k : ℕ} (e : Fin k → Fin 5), (∀ a j, j ∉ Set.range e → w (e a) ≠ w j) →
      ∀ h ∈ H, ∀ l a, l ∉ Set.range e →
        ((h : ↥(unitarySU 2 f K 5)) : GL (Fin 5) K).val l (e a) = 0 :=
    fun e hsep h hh l a hl => hvan h hh _ _ (fun hlw => hsep a l hl hlw.symm)
  have he₁ : Function.Injective (![0, 1] : Fin 2 → Fin 5) := by decide
  have he₂ : Function.Injective (![2, 3] : Fin 2 → Fin 5) := by decide
  have he₃ : Function.Injective (![4] : Fin 1 → Fin 5) := by decide
  obtain ⟨φ₁, hφ₁⟩ := exists_block_hom hU (![0, 1] : Fin 2 → Fin 5) he₁ H hHperf
    (hrow _ (sep_first hB)) (hcol _ (sep_first hB))
  obtain ⟨φ₂, hφ₂⟩ := exists_block_hom hU (![2, 3] : Fin 2 → Fin 5) he₂ H hHperf
    (hrow _ (sep_second hB)) (hcol _ (sep_second hB))
  obtain ⟨φ₃, hφ₃⟩ := exists_block_hom hU (![4] : Fin 1 → Fin 5) he₃ H hHperf
    (hrow _ (sep_third hB)) (hcol _ (sep_third hB))
  let ψ : ↥H →* ↥(unitarySU 2 f K 2) × ↥(unitarySU 2 f K 2) := φ₁.prod φ₂
  have hψ : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro h hh
    have h1 : φ₁ h = 1 := congrArg Prod.fst hh
    have h2 : φ₂ h = 1 := congrArg Prod.snd hh
    set M : Matrix (Fin 5) (Fin 5) K := ((h : ↥(unitarySU 2 f K 5)) : GL (Fin 5) K).val with hM
    have m1 : M.submatrix (![0, 1] : Fin 2 → Fin 5) (![0, 1] : Fin 2 → Fin 5) = 1 := by
      rw [← hφ₁ h, h1]
      rfl
    have m2 : M.submatrix (![2, 3] : Fin 2 → Fin 5) (![2, 3] : Fin 2 → Fin 5) = 1 := by
      rw [← hφ₂ h, h2]
      rfl
    have m3 : M 4 4 = 1 := by
      have hd := ((mem_unitarySU_iff hU).mp (φ₃ h).2).1
      rw [hφ₃ h, Matrix.det_unique] at hd
      simpa using hd
    have hv : ∀ i j, w i ≠ w j → M i j = 0 := fun i j hij => hvan h h.2 i j hij
    obtain ⟨hB02, hB03, hB04, hB12, hB13, hB14, hB24, hB34⟩ := hB
    have a00 : M 0 0 = 1 := by simpa using congrFun (congrFun m1 0) 0
    have a01 : M 0 1 = 0 := by simpa using congrFun (congrFun m1 0) 1
    have a10 : M 1 0 = 0 := by simpa using congrFun (congrFun m1 1) 0
    have a11 : M 1 1 = 1 := by simpa using congrFun (congrFun m1 1) 1
    have b22 : M 2 2 = 1 := by simpa using congrFun (congrFun m2 0) 0
    have b23 : M 2 3 = 0 := by simpa using congrFun (congrFun m2 0) 1
    have b32 : M 3 2 = 0 := by simpa using congrFun (congrFun m2 1) 0
    have b33 : M 3 3 = 1 := by simpa using congrFun (congrFun m2 1) 1
    have hMone : M = 1 := by
      ext x y
      fin_cases x <;> fin_cases y <;>
        first
        | simpa using a00 | simpa using a01 | simpa using a10 | simpa using a11
        | simpa using b22 | simpa using b23 | simpa using b32 | simpa using b33
        | simpa using m3
        | simpa using hv _ _ hB02 | simpa using hv _ _ hB03 | simpa using hv _ _ hB04
        | simpa using hv _ _ hB12 | simpa using hv _ _ hB13 | simpa using hv _ _ hB14
        | simpa using hv _ _ hB24 | simpa using hv _ _ hB34
        | simpa using hv _ _ hB02.symm | simpa using hv _ _ hB03.symm
        | simpa using hv _ _ hB04.symm | simpa using hv _ _ hB12.symm
        | simpa using hv _ _ hB13.symm | simpa using hv _ _ hB14.symm
        | simpa using hv _ _ hB24.symm | simpa using hv _ _ hB34.symm
    exact Subtype.ext (Subtype.ext (Units.ext hMone))
  have hdvd1 : Nat.card ↥H ∣
      Nat.card ↥(unitarySU 2 f K 2) * Nat.card ↥(unitarySU 2 f K 2) := by
    have := Subgroup.card_dvd_of_injective ψ hψ
    rwa [Nat.card_prod] at this
  have hdvd2 : Nat.card ↥X ∣ Nat.card ↥H := by
    have := Subgroup.card_map_dvd (H := H) (projU K f)
    rwa [hHmap] at this
  exact not_dvd_card_su hU (two_le_of_five_dvd h5) (hXcard ▸ hdvd2.trans hdvd1)

end CFSG.RankThree.PartOne.LSTD
