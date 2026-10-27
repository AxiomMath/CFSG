module

public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonClassification
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourExceptionTransport
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourCentralizerTransport
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section

namespace CFSG.GorensteinWalter

open BenderSuzuki.MatrixGroups

universe u

/-- After discharging elementary/cyclic/A₄/S₄/A₅ cases, the remaining
Dickson alternatives for a Klein-four centralizer are dihedral,
semidirect, `PSL₂`-subfield, and `PGL₂`-subfield. -/
public theorem psl2_no_kleinFour_of_dickson_finite_cases
    {F : Type u} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f) (hpodd : Odd p)
    (M A V : Subgroup (PSL2MatrixGroup F))
    (hAcyc : IsCyclic A) (hAne : A ≠ ⊥)
    (hAodd : Odd (Nat.card A))
    (hVK : IsKleinFour V)
    (hAM : A ≤ M) (hVM : V ≤ M)
    (hVleC : V ≤ Subgroup.centralizer (A : Set (PSL2MatrixGroup F)))
    (hDihedralOdd : ∀ z : ℕ,
      Nonempty (M ≃* DihedralGroup z) → Odd z) :
    False ∨
      (∃ m t : ℕ, True) ∨
      (∃ m : ℕ, True) ∨
      (∃ m : ℕ, True) := by
  let A0 : Subgroup M := A.subgroupOf M
  let V0 : Subgroup M := V.subgroupOf M
  have hA0cyc : IsCyclic A0 := isCyclic_subgroupOf hAM hAcyc
  have hA0ne : A0 ≠ ⊥ := subgroupOf_ne_bot hAM hAne
  have hA0odd : Odd (Nat.card A0) := subgroupOf_odd_card hAM hAodd
  have hV0K : IsKleinFour V0 := isKleinFour_subgroupOf hVM hVK
  have hV0leC : V0 ≤ Subgroup.centralizer (A0 : Set M) :=
    centralizer_subgroupOf_le hAM hVM hVleC
  rcases (Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification
      (F := F) hFcard M) with hElem | hCyc | hDihed | hA4 | hS4 | hA5 |
    hSemidirect | hPSL | hPGL
  · have hMp : IsPGroup p M := IsElementaryAbelian.isPGroup p M
    exact Or.inl (no_kleinFour_of_pGroup_subgroup M V hMp hpodd hVM hVK)
  · rcases hCyc with ⟨z, _hz, _hcard, hMcyc⟩
    exact Or.inl (no_kleinFour_subgroup_of_isCyclic M V hVK hVM hMcyc)
  · rcases hDihed with ⟨z, _hz, _hcard, _hdih⟩
    exact Or.inl (no_kleinFour_subgroup_of_dihedral_odd M V z hVK hVM _hdih
      (hDihedralOdd z _hdih))
  · rcases hA4 with ⟨_hp, ⟨e⟩⟩
    exact Or.inl (no_kleinFour_centralizes_odd_cyclic_of_mulEquiv_alternatingGroup_four
      e A0 V0 hA0cyc hA0ne hA0odd hV0K hV0leC)
  · rcases hS4 with ⟨_hp, ⟨e⟩⟩
    exact Or.inl (no_kleinFour_centralizes_odd_cyclic_of_mulEquiv_perm_four
      e A0 V0 hA0cyc hA0ne hA0odd hV0K hV0leC)
  · rcases hA5 with ⟨_hp, ⟨e⟩⟩
    exact Or.inl (no_kleinFour_centralizes_odd_cyclic_of_mulEquiv_alternatingGroup_five
      e A0 V0 hA0cyc hA0ne hA0odd hV0K hV0leC)
  · rcases hSemidirect with ⟨m, t, _hdiv, _hamb, N, C, _hN, _hE, _hcard,
      _hC, _hCcard, _hdisj, _hjoin⟩
    exact Or.inr (Or.inl ⟨m, t, trivial⟩)
  · rcases hPSL with ⟨m, _hm, _hdiv, ⟨_e⟩⟩
    exact Or.inr (Or.inr (Or.inl ⟨m, trivial⟩))
  · rcases hPGL with ⟨m, _hm, _hdiv, ⟨_e⟩⟩
    exact Or.inr (Or.inr (Or.inr ⟨m, trivial⟩))

end CFSG.GorensteinWalter
