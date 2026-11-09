module

public import CFSG.LieType.Ree.G2PrimeFieldWords

public section

namespace CFSG.Walter.Ree.Model

open CFSG.Blueprint.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
open CFSG.LieType.Chevalley.RootOps

@[expose] def g2TWord : List (ℕ × ℤ) :=
  g2WeylWordInv ⟨0, by decide⟩ ++ g2WeylWordInv ⟨0, by decide⟩ ++ g2WeylWordInv ⟨1, by decide⟩ ++
    g2WeylWordInv ⟨1, by decide⟩

theorem constP_constProd (n : ℕ) :
    ∀ (fs : List (ℕ × ℤ)) (acc : List PEntry), ConstP acc → ConstP (constProd G2.tag n acc fs)
  | [], _, h => by rw [constProd]; exact h
  | _ :: fs, _, _ => by rw [constProd]; exact constP_constProd n fs _ (constP_normC n _)

theorem constP_constProd_nil (n : ℕ) (fs : List (ℕ × ℤ)) :
    ConstP (constProd G2.tag n [] fs) :=
  constP_constProd n fs [] fun _ hx => absurd hx List.not_mem_nil

theorem modEqCheck_of_constP {n : ℤ} {L L' : List PEntry} (hL : ConstP L) (hL' : ConstP L')
    (h : (canonE (coeffAt L (0, 0) ++ (coeffAt L' (0, 0)).map
      fun e => (e.1, e.2.1, -1 * e.2.2))).all (fun e => e.2.2 % n == 0) = true) :
    modEqCheck n L L' = true := by
  unfold modEqCheck
  rw [List.all_eq_true]
  intro x hx
  have hx0 : x.1 = (0, 0) := by
    rcases List.mem_append.1 hx with hx | hx
    · exact hL x hx
    · exact hL' x hx
  rw [hx0]
  exact h

theorem g2Check_fusion_n :
    constCheck G2.tag 3 (g2UWord 0 ++ g2UWord 1 ++ g2LongWord ++ g2UWord 1 ++ g2UWord 2 ++ g2TWord)
      (g2LongWord ++ (g2UWord 0 ++ g2UWord 1 ++ g2LongWord ++ g2UWord 1 ++ g2UWord 2)) = true := by
  unfold constCheck
  rw [Bool.and_eq_true]
  refine ⟨by decide +kernel,
    modEqCheck_of_constP (constP_constProd_nil _ _) (constP_constProd_nil _ _) ?_⟩
  decide +kernel

theorem g2Check_fusion_tn :
    constCheck G2.tag 3 (g2UWord 2 ++ g2UWord 1 ++ g2LongWord ++ g2UWord 0 ++ g2TWord)
      (g2TWord ++ g2LongWord ++ (g2UWord 2 ++ g2UWord 1 ++ g2LongWord ++ g2UWord 0)) = true := by
  unfold constCheck
  rw [Bool.and_eq_true]
  refine ⟨by decide +kernel,
    modEqCheck_of_constP (constP_constProd_nil _ _) (constP_constProd_nil _ _) ?_⟩
  decide +kernel

end CFSG.Walter.Ree.Model
