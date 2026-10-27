module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3V1SixFinBF
public import CFSG.Quasithin.Background.G6PGroup
public import CFSG.Quasithin.H13.Sp62Over

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.G6 Equiv

private theorem s1611e3_testBit_one_shiftLeft (k m : Nat) :
    (1 <<< k).testBit m = decide (m = k) := by
  rw [Nat.one_shiftLeft, Nat.testBit_two_pow]
  exact decide_eq_decide.mpr eq_comm

private theorem s1611e3_testBit_ite_shiftLeft (c : Bool) (a k m : Nat) :
    (if c then a ||| (1 <<< k) else a).testBit m =
      (a.testBit m || (c && decide (m = k))) := by
  cases c
  · simp
  · show (a ||| (1 <<< k)).testBit m = (a.testBit m || decide (m = k))
    rw [Nat.testBit_or, s1611e3_testBit_one_shiftLeft]

private theorem s1611e3_getD_map (f : Nat → Nat) (l : List Nat) (i : Nat)
    (hi : i < l.length) : (l.map f).getD i 0 = f (l.getD i 0) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  rw [List.getElem?_eq_getElem hi]
  simp

private theorem s1611e3_foldl_testBit (l : List Nat) (p : Nat → Bool) (acc m : Nat) :
    (l.foldl (fun a k => if p k then a ||| (1 <<< k) else a) acc).testBit m =
      (acc.testBit m || (decide (m ∈ l) && p m)) := by
  induction l generalizing acc with
  | nil => simp
  | cons k ks ih =>
    rw [List.foldl_cons, ih, s1611e3_testBit_ite_shiftLeft]
    by_cases hmk : m = k
    · rw [hmk]
      cases hp : p k <;> simp [hp]
    · simp [decide_eq_false hmk]

theorem s1611e3_testBit_sixProf (K : Bool) (t m : Nat) :
    (sixProf K t).testBit m = (decide (m ∈ sixVecs) && sixFixes K t m) := by
  rw [sixProf, s1611e3_foldl_testBit]
  simp

theorem s1611e3_testBit_sixInvAdj {i k : Nat} (hi : i < 111) (hk : k < 111) :
    (sixInvAdj.getD i 0).testBit k =
      sixComm (sixInvTabs.getD i 0) (sixInvTabs.getD k 0) := by
  have hlen : sixInvTabs.length = 111 := by decide +kernel
  have hi' : i < sixInvTabs.length := by rw [hlen]; exact hi
  have hget : sixInvAdj.getD i 0 =
      (List.range 111).foldl (fun acc k =>
        if sixComm (sixInvTabs.getD i 0) (sixInvTabs.getD k 0) then acc ||| (1 <<< k)
        else acc) 0 := by
    rw [sixInvAdj]
    exact s1611e3_getD_map _ sixInvTabs i hi'
  rw [hget, s1611e3_foldl_testBit]
  simp [List.mem_range, hk]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
