module
public import CFSG.LocalAnalysis.StandardType.GGQTwoSixPointSu
public import CFSG.LocalAnalysis.StandardType.GGQTwoSU34
public import CFSG.Mathlib.Decide.Nodup
public import CFSG.Mathlib.Decide.Bounded
public import CFSG.RankThree.PartOne.KF.ClsSUUpper
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.RankThree.PartTwo.Census.Classical.EvenUnitary
public section
namespace CFSG.StandardType.QTwo.SixPoint
open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary
open CFSG.GH74.Uniqueness.SU.SU5 (F4c)
section Gen
@[expose] def qTwoSixGen_pattern : List (List Bool) := [
  [],
  [false],
  [true],
  [false,false],
  [false,true],
  [true,false],
  [true,true],
  [false,false,false],
  [false,false,true],
  [false,true,false],
  [false,true,true],
  [true,false,false],
  [true,false,true],
  [true,true,false],
  [true,true,true],
  [false,false,false,true],
  [false,false,true,false],
  [false,false,true,true],
  [false,true,false,false],
  [false,true,false,true],
  [false,true,true,false],
  [false,true,true,true],
  [true,false,false,false],
  [true,false,false,true],
  [true,false,true,false],
  [true,false,true,true],
  [true,true,false,false],
  [true,true,false,true],
  [true,true,true,false],
  [true,true,true,true],
  [false,false,false,true,false],
  [false,false,false,true,true],
  [false,false,true,false,false],
  [false,false,true,false,true],
  [false,false,true,true,false],
  [false,false,true,true,true],
  [false,true,false,false,false],
  [false,true,false,false,true],
  [false,true,false,true,false],
  [false,true,false,true,true],
  [false,true,true,false,false],
  [false,true,true,false,true],
  [false,true,true,true,false],
  [false,true,true,true,true],
  [true,false,false,false,true],
  [true,false,false,true,false],
  [true,false,false,true,true],
  [true,false,true,false,false],
  [true,false,true,false,true],
  [true,false,true,true,false],
  [true,false,true,true,true],
  [true,true,false,false,false],
  [true,true,false,false,true],
  [true,true,false,true,false],
  [true,true,false,true,true],
  [true,true,true,false,false],
  [true,true,true,false,true],
  [true,true,true,true,true],
  [false,false,false,true,false,false],
  [false,false,false,true,false,true],
  [false,false,false,true,true,false],
  [false,false,false,true,true,true],
  [false,false,true,false,false,false],
  [false,false,true,false,false,true],
  [false,false,true,false,true,false],
  [false,false,true,false,true,true],
  [false,false,true,true,false,false],
  [false,false,true,true,false,true],
  [false,false,true,true,true,false],
  [false,false,true,true,true,true],
  [false,true,false,false,false,true],
  [false,true,false,false,true,false],
  [false,true,false,true,false,false],
  [false,true,false,true,false,true],
  [false,true,false,true,true,false],
  [false,true,false,true,true,true],
  [false,true,true,false,false,false],
  [false,true,true,false,false,true],
  [false,true,true,true,false,false],
  [false,true,true,true,true,true],
  [true,false,false,false,true,false],
  [true,false,false,false,true,true],
  [true,false,false,true,false,false],
  [true,false,false,true,false,true],
  [true,false,false,true,true,true],
  [true,false,true,false,false,false],
  [true,false,true,false,false,true],
  [true,false,true,false,true,true],
  [true,false,true,true,false,false],
  [true,false,true,true,true,false],
  [true,false,true,true,true,true],
  [true,true,false,false,false,true],
  [true,true,false,false,true,true],
  [true,true,false,true,true,false],
  [true,true,false,true,true,true],
  [true,true,true,false,true,false],
  [true,true,true,false,true,true],
  [true,true,true,true,true,true],
  [false,false,false,true,false,false,true],
  [false,false,false,true,false,true,true],
  [false,false,false,true,true,true,false],
  [false,false,false,true,true,true,true],
  [false,false,true,false,false,false,true],
  [false,false,true,false,false,true,false],
  [false,false,true,false,true,false,false],
  [false,false,true,false,true,false,true],
  [false,false,true,false,true,true,false],
  [false,false,true,false,true,true,true],
  [false,false,true,true,false,false,false],
  [false,false,true,true,false,false,true],
  [false,false,true,true,true,false,false],
  [false,false,true,true,true,true,true],
  [false,true,false,false,false,true,false],
  [false,true,false,false,false,true,true],
  [false,true,false,false,true,false,false],
  [false,true,false,false,true,false,true],
  [false,true,false,true,false,false,false],
  [false,true,false,true,false,false,true],
  [false,true,false,true,false,true,true],
  [false,true,false,true,true,false,false],
  [false,true,false,true,true,true,false],
  [false,true,false,true,true,true,true],
  [false,true,true,false,false,false,true],
  [false,true,true,false,false,true,true],
  [false,true,true,true,true,true,true],
  [true,false,false,false,true,false,false],
  [true,false,false,false,true,true,false],
  [true,false,false,true,false,false,false],
  [true,false,false,true,false,false,true],
  [true,false,false,true,false,true,false],
  [true,false,false,true,true,true,false],
  [true,false,false,true,true,true,true],
  [true,false,true,false,true,true,false],
  [true,false,true,false,true,true,true],
  [true,false,true,true,true,false,false],
  [true,true,false,false,false,true,false],
  [true,true,false,false,false,true,true],
  [true,true,false,false,true,true,true],
  [true,true,false,true,true,false,false],
  [true,true,false,true,true,true,true],
  [true,true,true,false,true,true,true],
  [true,true,true,true,true,true,true],
  [false,false,false,true,false,false,true,false],
  [false,false,false,true,false,true,true,false],
  [false,false,false,true,false,true,true,true],
  [false,false,false,true,true,true,false,false],
  [false,false,false,true,true,true,true,true],
  [false,false,true,false,false,false,true,false],
  [false,false,true,false,false,false,true,true],
  [false,false,true,false,false,true,false,false],
  [false,false,true,false,false,true,false,true],
  [false,false,true,false,true,false,false,false],
  [false,false,true,false,true,false,false,true],
  [false,false,true,false,true,false,true,true],
  [false,false,true,false,true,true,false,false],
  [false,false,true,false,true,true,true,false],
  [false,false,true,false,true,true,true,true],
  [false,false,true,true,false,false,false,true],
  [false,false,true,true,false,false,true,true],
  [false,false,true,true,true,true,true,true],
  [false,true,false,false,false,true,false,false],
  [false,true,false,false,true,false,false,false],
  [false,true,false,false,true,false,false,true],
  [false,true,false,true,false,true,true,false],
  [false,true,false,true,false,true,true,true],
  [false,true,false,true,true,true,false,false],
  [false,true,true,false,false,false,true,false],
  [false,true,true,false,false,false,true,true],
  [false,true,true,false,false,true,true,true],
  [false,true,true,true,true,true,true,true],
  [true,false,false,false,true,false,false,true],
  [true,false,false,true,false,false,true,false],
  [true,false,false,true,false,true,false,false],
  [true,false,false,true,false,true,false,true],
  [true,false,false,true,true,true,false,false],
  [true,false,true,false,true,true,false,false],
  [true,false,true,false,true,true,true,false],
  [true,true,false,false,false,true,false,false],
  [true,true,false,false,true,true,true,false],
  [true,true,false,false,true,true,true,true],
  [true,true,true,false,true,true,true,true],
  [true,true,true,true,true,true,true,true],
  [false,false,false,true,false,false,true,false,false],
  [false,false,false,true,false,false,true,false,true],
  [false,false,false,true,false,true,true,false,false],
  [false,false,false,true,false,true,true,true,false],
  [false,false,false,true,false,true,true,true,true],
  [false,false,false,true,true,true,true,true,true],
  [false,false,true,false,false,false,true,false,false],
  [false,false,true,false,false,true,false,false,false],
  [false,false,true,false,false,true,false,false,true],
  [false,false,true,false,true,false,true,true,false],
  [false,false,true,false,true,false,true,true,true],
  [false,false,true,false,true,true,true,false,false],
  [false,false,true,true,false,false,false,true,false],
  [false,false,true,true,false,false,false,true,true],
  [false,false,true,true,false,false,true,true,true],
  [false,false,true,true,true,true,true,true,true],
  [false,true,false,false,false,true,false,false,true],
  [false,true,false,false,true,false,false,true,false],
  [false,true,false,true,false,true,true,false,false],
  [false,true,true,false,false,false,true,false,false],
  [false,true,true,true,true,true,true,true,true],
  [true,false,false,false,true,false,false,true,false],
  [true,false,false,true,false,true,false,false,false],
  [true,false,false,true,false,true,false,false,true],
  [true,true,false,false,true,true,true,false,false],
  [false,false,false,true,false,false,true,false,false,false],
  [false,false,false,true,false,true,true,true,false,false],
  [false,false,false,true,true,true,true,true,true,true],
  [false,false,true,false,false,false,true,false,false,true],
  [false,false,true,false,false,true,false,false,true,false],
  [false,false,true,false,true,false,true,true,false,false],
  [false,false,true,true,false,false,false,true,false,false],
  [false,false,true,true,true,true,true,true,true,true],
  [false,false,false,true,true,true,true,true,true,true,true]
]
@[expose] def qTwoSixGen_word (a b : Fin 18) (p : List Bool) : List (Fin 18 × Bool) :=
  p.map fun bit => (cond bit b a, true)
@[expose] def qTwoSixGen_f4cKey : F4c → ℕ
  | .z0 => 0
  | .z1 => 1
  | .w => 2
  | .w2 => 3
@[expose] def qTwoSixGen_matKey (i0 i1 i2 : Fin 6)
    (M : Matrix (Fin 6) (Fin 6) F4c) : ℕ :=
  CFSG.Decide.digitsKey 4 (fun t =>
    qTwoSixGen_f4cKey
      (([M i0 i0, M i0 i1, M i0 i2, M i1 i0, M i1 i1, M i1 i2, M i2 i0, M i2 i1,
        M i2 i2] : List F4c).getD t .z0)) 9
private theorem qTwoSixGen_pattern_length : qTwoSixGen_pattern.length = 216 := by decide +kernel
private theorem qTwoSixGen_evalG_mem {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 4) (a b : Fin 18) (p : List Bool) :
    evalG (nativeSu hK) (qTwoSixGen_word a b p) ∈
      Subgroup.closure ({nativeSu hK a, nativeSu hK b} : Set (Su K 2 1 6)) := by
  set S : Set (Su K 2 1 6) := {nativeSu hK a, nativeSu hK b} with hS
  induction p with
  | nil => simp [qTwoSixGen_word, evalG]
  | cons bit p ih =>
    simp only [qTwoSixGen_word, List.map_cons, evalG, List.prod_cons]
    refine Subgroup.mul_mem _ ?_ ih
    rcases bit with _ | _
    · exact Subgroup.subset_closure (by simp [hS])
    · exact Subgroup.subset_closure (by simp [hS])
private theorem qTwoSixGen_map_injective {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 4)
    {M N : Matrix (Fin 6) (Fin 6) F4c}
    (h : M.map (f4cEmb hK) = N.map (f4cEmb hK)) : M = N := by
  ext i j
  have := congrFun (congrFun h i) j
  rw [Matrix.map_apply, Matrix.map_apply] at this
  exact (f4cEmb hK).injective this

private theorem qTwoSixGen_bitset012 :
    CFSG.Decide.bitsetNodup (qTwoSixGen_pattern.map (fun p =>
      qTwoSixGen_matKey 0 1 2 (evalNative (qTwoSixGen_word 10 11 p)))) = true := by
  decide +kernel

theorem qTwoSixGen_nodup012 :
    (qTwoSixGen_pattern.map (fun p => evalNative (qTwoSixGen_word 10 11 p))).Nodup :=
  CFSG.Decide.nodup_of_bitsetNodup (qTwoSixGen_matKey 0 1 2) qTwoSixGen_bitset012

private theorem qTwoSixGen_bitset123 :
    CFSG.Decide.bitsetNodup (qTwoSixGen_pattern.map (fun p =>
      qTwoSixGen_matKey 1 2 3 (evalNative (qTwoSixGen_word 12 13 p)))) = true := by
  decide +kernel

theorem qTwoSixGen_nodup123 :
    (qTwoSixGen_pattern.map (fun p => evalNative (qTwoSixGen_word 12 13 p))).Nodup :=
  CFSG.Decide.nodup_of_bitsetNodup (qTwoSixGen_matKey 1 2 3) qTwoSixGen_bitset123

private theorem qTwoSixGen_bitset234 :
    CFSG.Decide.bitsetNodup (qTwoSixGen_pattern.map (fun p =>
      qTwoSixGen_matKey 2 3 4 (evalNative (qTwoSixGen_word 14 15 p)))) = true := by
  decide +kernel

theorem qTwoSixGen_nodup234 :
    (qTwoSixGen_pattern.map (fun p => evalNative (qTwoSixGen_word 14 15 p))).Nodup :=
  CFSG.Decide.nodup_of_bitsetNodup (qTwoSixGen_matKey 2 3 4) qTwoSixGen_bitset234

private theorem qTwoSixGen_card_le {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 4) (a b : Fin 18)
    (hnodup : (qTwoSixGen_pattern.map
      (fun p => evalNative (qTwoSixGen_word a b p))).Nodup) :
    216 ≤ Nat.card (Subgroup.closure ({nativeSu hK a, nativeSu hK b} :
      Set (Su K 2 1 6))) := by
  set H : Subgroup (Su K 2 1 6) := Subgroup.closure ({nativeSu hK a, nativeSu hK b} :
    Set (Su K 2 1 6)) with hH
  set mF : List (Matrix (Fin 6) (Fin 6) F4c) :=
    qTwoSixGen_pattern.map (fun p => evalNative (qTwoSixGen_word a b p)) with hmF
  have hnodupF : mF.Nodup := by rw [hmF]; exact hnodup
  have hmK : (qTwoSixGen_pattern.map
      (fun p => (evalNative (qTwoSixGen_word a b p)).map (f4cEmb hK))).Nodup := by
    have h1 : (mF.map (fun M : Matrix (Fin 6) (Fin 6) F4c => M.map (f4cEmb hK))).Nodup :=
      List.Nodup.map (l := mF) (f := fun M : Matrix (Fin 6) (Fin 6) F4c => M.map (f4cEmb hK))
        (fun M N h => qTwoSixGen_map_injective hK h) hnodupF
    simpa [hmF, List.map_map, Function.comp_def] using h1
  set l : List (Su K 2 1 6) :=
    qTwoSixGen_pattern.map (fun p => evalG (nativeSu hK) (qTwoSixGen_word a b p)) with hl
  have hmem : ∀ x ∈ l, x ∈ H := by
    intro x hx
    rw [hl, List.mem_map] at hx
    obtain ⟨p, -, rfl⟩ := hx
    exact qTwoSixGen_evalG_mem hK a b p
  have hl_nodup : l.Nodup := by
    apply List.Nodup.of_map (fun x : Su K 2 1 6 =>
      (((x : Su K 2 1 6) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K))
    have hmap : l.map (fun x : Su K 2 1 6 =>
        (((x : Su K 2 1 6) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) =
        qTwoSixGen_pattern.map (fun p => (evalNative (qTwoSixGen_word a b p)).map (f4cEmb hK)) := by
      rw [hl, List.map_map]
      refine List.map_congr_left fun p _ => ?_
      exact coe_evalG_nativeSu hK (qTwoSixGen_word a b p)
    rw [hmap]
    exact hmK
  have hinj : Function.Injective (fun i : Fin l.length =>
      (⟨l.get i, hmem (l.get i) (List.get_mem l i)⟩ : H)) := by
    intro i j hij
    apply hl_nodup.get_inj_iff.mp
    exact congrArg Subtype.val hij
  have hle := Nat.card_le_card_of_injective (fun i : Fin l.length =>
    (⟨l.get i, hmem (l.get i) (List.get_mem l i)⟩ : H)) hinj
  rwa [Nat.card_fin, hl, List.length_map, qTwoSixGen_pattern_length] at hle

private theorem qTwoSixGen_card_Su_three {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 4) :
    Nat.card (Su K 2 1 3) = 216 := by
  have hF : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  have hdata := CFSG.RankThree.PartOne.KFU.unitaryFieldData_two (K := K) (f := 1) hF (by norm_num)
  have hsu : Su K 2 1 3 = ↥(CFSG.Open.StatedSU 3 (2 ^ 1) K) := by
    dsimp only [Su]
    rw [CFSG.LieType.Universal.Unitary.SUid_eq_statedSU (F := K) (p := 2) (f := 1) hF 3]
  rw [hsu]
  have hval : (Nat.card ↥(CFSG.Open.StatedSU 3 (2 ^ 1) K) : ℤ) = 216 := by
    rw [CFSG.RankThree.PartOne.KFU.card_statedSU_eq (K := K) (f := 1) hdata (n := 3) (by norm_num)]
    decide
  exact_mod_cast hval

theorem qTwoSixGen_card_coordBlock {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 4) {J : Finset (Fin 6)} :
    Nat.card (coordBlockSU K 2 1 J) = Nat.card (Su K 2 1 J.card) := by
  have e := MonoidHom.ofInjective (blockSUOn_injective (K := K) (p := 2) (f := 1) J)
  change Nat.card (blockSUOn K 2 1 J).range = Nat.card (Su K 2 1 J.card)
  exact (Nat.card_congr e.toEquiv).symm

@[expose] def qTwoSixGen_J012 : Finset (Fin 6) := {0, 1, 2}

@[expose] def qTwoSixGen_J123 : Finset (Fin 6) := {1, 2, 3}

@[expose] def qTwoSixGen_J234 : Finset (Fin 6) := {2, 3, 4}

theorem qTwoSixGen_support012 (a : Fin 18) (ha : a = 10 ∨ a = 11) :
    ∀ x y : Fin 6, (x ∉ qTwoSixGen_J012 ∨ y ∉ qTwoSixGen_J012) →
      nativeGen a x y = if x = y then 1 else 0 := by
  rcases ha with rfl | rfl <;>
    intro x y hxy <;>
    fin_cases x <;> fin_cases y <;>
    (simp_all [nativeGen, qTwoSixGen_J012] <;> decide)

theorem qTwoSixGen_support123 (a : Fin 18) (ha : a = 12 ∨ a = 13) :
    ∀ x y : Fin 6, (x ∉ qTwoSixGen_J123 ∨ y ∉ qTwoSixGen_J123) →
      nativeGen a x y = if x = y then 1 else 0 := by
  rcases ha with rfl | rfl <;>
    intro x y hxy <;>
    fin_cases x <;> fin_cases y <;>
    (simp_all [nativeGen, qTwoSixGen_J123] <;> decide)

theorem qTwoSixGen_support234 (a : Fin 18) (ha : a = 14 ∨ a = 15) :
    ∀ x y : Fin 6, (x ∉ qTwoSixGen_J234 ∨ y ∉ qTwoSixGen_J234) →
      nativeGen a x y = if x = y then 1 else 0 := by
  rcases ha with rfl | rfl <;>
    intro x y hxy <;>
    fin_cases x <;> fin_cases y <;>
    (simp_all [nativeGen, qTwoSixGen_J234] <;> decide)

private theorem qTwoSixGen_coe_nativeSu {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 4) (a : Fin 18) :
    (((nativeSu hK a : Su K 2 1 6) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      (nativeGen a).map (f4cEmb hK) := by
  have h := coe_evalG_nativeSu hK ([(a, true)] : List (Fin 18 × Bool))
  simpa [evalG, evalNative] using h

theorem qTwoSixGen_nativeSu_mem {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 4) {J : Finset (Fin 6)}
    (a : Fin 18)
    (hsupp : ∀ x y : Fin 6, (x ∉ J ∨ y ∉ J) →
      nativeGen a x y = if x = y then 1 else 0) :
    nativeSu hK a ∈ coordBlockSU K 2 1 J := by
  rw [mem_coordBlockSU_iff]
  intro x y hxy
  rw [qTwoSixGen_coe_nativeSu, Matrix.map_apply, hsupp x y hxy]
  by_cases h : x = y <;> simp [h, map_one, map_zero]

private theorem qTwoSixGen_closure_eq_block {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 4) {J : Finset (Fin 6)}
    (hJ : J.card = 3) (a b : Fin 18)
    (hnodup : (qTwoSixGen_pattern.map
      (fun p => evalNative (qTwoSixGen_word a b p))).Nodup)
    (ha : nativeSu hK a ∈ coordBlockSU K 2 1 J)
    (hb : nativeSu hK b ∈ coordBlockSU K 2 1 J) :
    Subgroup.closure ({nativeSu hK a, nativeSu hK b} : Set (Su K 2 1 6)) =
      coordBlockSU K 2 1 J := by
  haveI : Finite ↥(coordBlockSU K 2 1 J) := Subtype.finite
  have hle : Subgroup.closure ({nativeSu hK a, nativeSu hK b} : Set (Su K 2 1 6)) ≤
      coordBlockSU K 2 1 J := by
    rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact ha
    · exact hb
  have hcardblock : Nat.card (coordBlockSU K 2 1 J) = 216 := by
    rw [qTwoSixGen_card_coordBlock hK, hJ, qTwoSixGen_card_Su_three hK]
  have hge := qTwoSixGen_card_le hK a b hnodup
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcardblock]; exact hge)

theorem qTwoSixGen_block_le_of_mem {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 4) {J : Finset (Fin 6)}
    (hJ : J.card = 3) (a b : Fin 18)
    (hnodup : (qTwoSixGen_pattern.map
      (fun p => evalNative (qTwoSixGen_word a b p))).Nodup)
    (haJ : nativeSu hK a ∈ coordBlockSU K 2 1 J)
    (hbJ : nativeSu hK b ∈ coordBlockSU K 2 1 J)
    {G : Subgroup (Su K 2 1 6)} (ha : nativeSu hK a ∈ G) (hb : nativeSu hK b ∈ G) :
    coordBlockSU K 2 1 J ≤ G := by
  have heq := qTwoSixGen_closure_eq_block hK hJ a b hnodup haJ hbJ
  rw [← heq]
  rw [Subgroup.closure_le]
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl
  · exact ha
  · exact hb

theorem qTwoSixGen_block012_le {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 4) :
    coordBlockSU K 2 1 qTwoSixGen_J012 ≤
      Subgroup.closure (Set.range (nativeSu hK)) :=
  qTwoSixGen_block_le_of_mem hK (by decide) 10 11 qTwoSixGen_nodup012
    (qTwoSixGen_nativeSu_mem hK 10 (qTwoSixGen_support012 10 (Or.inl rfl)))
    (qTwoSixGen_nativeSu_mem hK 11 (qTwoSixGen_support012 11 (Or.inr rfl)))
    (Subgroup.subset_closure ⟨_, rfl⟩) (Subgroup.subset_closure ⟨_, rfl⟩)

theorem qTwoSixGen_block123_le {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 4) :
    coordBlockSU K 2 1 qTwoSixGen_J123 ≤
      Subgroup.closure (Set.range (nativeSu hK)) :=
  qTwoSixGen_block_le_of_mem hK (by decide) 12 13 qTwoSixGen_nodup123
    (qTwoSixGen_nativeSu_mem hK 12 (qTwoSixGen_support123 12 (Or.inl rfl)))
    (qTwoSixGen_nativeSu_mem hK 13 (qTwoSixGen_support123 13 (Or.inr rfl)))
    (Subgroup.subset_closure ⟨_, rfl⟩) (Subgroup.subset_closure ⟨_, rfl⟩)

theorem qTwoSixGen_block234_le {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 4) :
    coordBlockSU K 2 1 qTwoSixGen_J234 ≤
      Subgroup.closure (Set.range (nativeSu hK)) :=
  qTwoSixGen_block_le_of_mem hK (by decide) 14 15 qTwoSixGen_nodup234
    (qTwoSixGen_nativeSu_mem hK 14 (qTwoSixGen_support234 14 (Or.inl rfl)))
    (qTwoSixGen_nativeSu_mem hK 15 (qTwoSixGen_support234 15 (Or.inr rfl)))
    (Subgroup.subset_closure ⟨_, rfl⟩) (Subgroup.subset_closure ⟨_, rfl⟩)

end Gen

end CFSG.StandardType.QTwo.SixPoint

end
