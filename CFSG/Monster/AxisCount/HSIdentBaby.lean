module

public import Certificates.Certificate6009
public import CFSG.Monster.AxisCount.AxisFacts

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.AxisCount.HS

open CFSG.Monster CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated
  CFSG.Monster.B CFSG.Monster.B.Short

theorem babyFix_ok : ∀ j, j < 10 → ∀ b ∈ babyBlocks[j]!,
    (∀ g ∈ b, g ≠ Native.Gen.tau) ∧ wordLin b aStar = aStar :=
  Certificates.certificate6009

theorem hs_baby :
    ∀ j, j < 10 → ∀ b ∈ babyBlocks[j]!,
    (∀ g ∈ b, g ≠ Native.Gen.tau) ∧ wordLin b aStar = aStar :=
  babyFix_ok

theorem wordLin_joinTau_mem_Cgen (bs : List (List Native.Gen))
    (hb : ∀ b ∈ bs, (∀ g ∈ b, g ≠ Native.Gen.tau) ∧ wordLin b aStar = aStar) :
    wordLin (joinTau bs) ∈ Cgen := by
  have hblock : ∀ b ∈ bs, wordLin b ∈ Cgen := fun b hb' =>
    Jstar_le_Cgen (mem_Jstar_of_fix (wordLin_mem_Gvis b (hb b hb').1) (hb b hb').2)
  have key : ∀ l : List (List Native.Gen), (∀ b ∈ l, wordLin b ∈ Cgen) →
      wordLin (l.flatMap fun b' => Native.Gen.tau :: b') ∈ Cgen := by
    intro l
    induction l with
    | nil =>
      intro _
      simp only [List.flatMap_nil, wordLin_nil]
      exact Cgen.one_mem
    | cons b l ih =>
      intro hl
      have e : ((b :: l).flatMap fun b' => Native.Gen.tau :: b') =
          (Native.Gen.tau :: b) ++ l.flatMap fun b' => Native.Gen.tau :: b' := rfl
      rw [e, wordLin_append, wordLin_cons]
      exact Cgen.mul_mem (ih fun b' hb' => hl b' (List.mem_cons_of_mem _ hb'))
        (Cgen.mul_mem (hl b List.mem_cons_self) tauB_mem_Cgen)
  cases bs with
  | nil =>
    simp only [joinTau, wordLin_nil]
    exact Cgen.one_mem
  | cons b bs =>
    simp only [joinTau]
    rw [wordLin_append]
    exact Cgen.mul_mem (key bs fun b' hb' => hblock b' (List.mem_cons_of_mem _ hb'))
      (hblock b List.mem_cons_self)

theorem babyW_mem_Cgen
    {j : Nat} (hj : j < 10) : wordLin (babyW j) ∈ Cgen :=
  wordLin_joinTau_mem_Cgen _ (hs_baby j hj)

end CFSG.Monster.AxisCount.HS
