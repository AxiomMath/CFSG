module

public import CFSG.Sporadic.Ly.Primitive
public import CFSG.Sporadic.Ly.ThreeBOmega
public import CFSG.Sporadic.Schreier.LySevenProofBase

public section

namespace CFSG.Sporadic.Ly

open CFSG.Sporadic.LySchreier CFSG.Sporadic.Ly.Omega MulAction


theorem lyYB_mem_lyH : lyYB ∈ lyH := by
  have h2 := aStar_mem_lyH (j := 2) le_rfl
  have h3 := aStar_mem_lyH (j := 3) (by norm_num)
  have hl : ∀ l, lyLet l ∈ lyH := by
    intro l
    unfold lyLet
    rcases l with _ | _ | _ | _ | l
    · exact h2
    · exact h3
    · exact lyH.inv_mem h2
    · exact lyH.inv_mem h3
    · exact lyH.one_mem
  have hw : ∀ w : List ℕ, wordJ w ∈ lyH := by
    intro w
    unfold wordJ
    induction w with
    | nil => exact lyH.one_mem
    | cons l w ih =>
      rw [List.map_cons, List.prod_cons]
      exact lyH.mul_mem (hl l) ih
  exact hw _

theorem exists_threeB_element :
    ∃ y : J, orderOf y = 3 ∧ Nat.card ↥(Subgroup.centralizer ({y} : Set J)) ≤ 174960 := by
  classical
  have : Finite J := Nat.finite_of_card_ne_zero (by rw [card_J]; norm_num)
  have : Fintype (orbit J opE) := Fintype.ofFinite _
  obtain ⟨-, -, -, -, -, -, -, -, hfix, -, -, hord, hC⟩ := ly_certificate
  refine exists_threeB_element_of omegaE lyH stabilizer_omegaE lyYB_mem_lyH hord
    (Finset.univ.filter fun x : orbit J opE => lyYB • x = x)
    (fun x hx => Finset.mem_filter.2 ⟨Finset.mem_univ x, hx⟩) ?_ ?_
  · have e : (Finset.univ.filter fun x : orbit J opE => lyYB • x = x).card =
        Nat.card {x : orbit J opE // lyYB • x = x} := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [e]
    exact hfix
  · rw [← CFSG.RankThree.PartOne.card_centralizer_inf_eq lyH lyYB lyYB_mem_lyH]
    exact hC

end CFSG.Sporadic.Ly
