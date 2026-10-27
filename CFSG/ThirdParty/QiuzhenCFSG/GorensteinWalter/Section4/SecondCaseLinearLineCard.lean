module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearEquationElevenProductFamily
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearEquationEightDefs
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The line count in equation (11)
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

public theorem secondCase_linearEquation11_line_card
    {G : Type u} [Group G] [Finite G]
    (P P0 A : Subgroup G) {p1 : ℕ}
    (hA : A = P ⊔ P0) (hPleA : P ≤ A) (hp1 : p1 = conjugateCount P A) :
    Nat.card (secondCase_linesIn G P P0) = p1 - 1 := by
  classical
  let C : Type u := {X : Subgroup G // X ≤ A ∧ IsConjugateSubgroup P X}
  let L : Type u := secondCase_linesIn G P P0
  let hPmem : C := ⟨P, hPleA, by
    refine ⟨1, ?_⟩
    change Subgroup.map (MulAut.conj (1 : G)).toMonoidHom P = P
    rw [show (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G by
      ext x
      simp, Subgroup.map_id]⟩
  let f : Option L → C := fun z => match z with
    | none => hPmem
    | some X => ⟨X.1, by
        refine ⟨?_, ?_⟩
        · simpa [L, hA] using X.2.1
        · rcases X.2.2.2 with ⟨g, hg⟩
          exact ⟨g, hg.symm⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      cases a with
      | none =>
          cases b with
          | none => rfl
          | some X =>
              exfalso
              have hXeq : P = X.1 := congrArg Subtype.val hab
              exact X.2.2.1 hXeq.symm
      | some X =>
          cases b with
          | none =>
              exfalso
              have hXeq : X.1 = P := congrArg Subtype.val hab
              exact X.2.2.1 hXeq
          | some Y =>
              have hv : X.1 = Y.1 := by
                change (f (some X)).val = (f (some Y)).val
                exact congrArg Subtype.val hab
              have hXY : X = Y := Subtype.ext hv
              exact congrArg some hXY
    · intro X
      by_cases hXP : X.1 = P
      · exact ⟨none, Subtype.ext hXP.symm⟩
      · let XL : L := ⟨X.1, by
          refine ⟨?_, hXP, ?_⟩
          · simpa [hA] using X.2.1
          · rcases X.2.2 with ⟨g, hg⟩
            exact ⟨g, hg.symm⟩⟩
        exact ⟨some XL, by rfl⟩
  have hcard : Nat.card (Option L) = Nat.card C := Nat.card_congr (Equiv.ofBijective f hf)
  have hopt : Nat.card (Option L) = Nat.card L + 1 := by simp
  have hp1' : Nat.card C = p1 := by simpa [C, conjugateCount] using hp1.symm
  rw [hopt, hp1'] at hcard
  have hL : Nat.card L + 1 = p1 := hcard
  change Nat.card L = p1 - 1
  omega

end CFSG.GorensteinWalter
