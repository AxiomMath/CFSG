module

public import CFSG.LocalAnalysis.StandardType.FS81.RowElemAb
public import CFSG.LocalAnalysis.StandardType.GGFrameRouteE7Models
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoRank
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoTBFull

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly

theorem rowElemAb3_E7
    {G : Type} [Group G] [Finite G] {K A : Subgroup G}
    (hrow : IsRow Row.E7 K) (hZ : Subgroup.center K = ⊥) (hAK : A ≤ K)
    (hA : IsElemAbelian 3 A) (hAcard : Nat.card A = 3 ^ Row.E7.n) :
    (∀ A' : Subgroup G, A' ≤ K → IsElemAbelian 3 A' → Nat.card A' ≤ 3 ^ Row.E7.n) ∧
      (∀ A' : Subgroup G, A' ≤ K → IsElemAbelian 3 A' → Nat.card A' = 3 ^ Row.E7.n →
        ∃ k ∈ K, A'.map (MulAut.conj k).toMonoidHom = A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨t, rk, n⟩, hP, hlab⟩ := exists_glaLabel hrow
  obtain ⟨hn1, hcases⟩ := hP
  obtain rfl : n = 1 := hn1
  have ht : t = .E7 := by
    rcases hcases with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h, -⟩
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact h
  obtain ⟨φ⟩ := exists_mulEquiv_adjointGroup_of_isLabel_E7' (lab := ⟨t, rk, 1⟩) hlab ht hZ
  have hF : Nat.card (GaloisField 2 1) = 2 := by
    simpa using GaloisField.card 2 1 (by omega)
  refine rowElemAb3_of_mulEquiv φ (fun E hE => TableBExcTwo.card_le_adjoint_E7 hF hE)
    (fun E E' hE hE' hc hc' => ?_) hAK hA hAcard
  obtain ⟨c, rfl⟩ := TableBExcTwoTB.exists_conj_frame_of_card_E7 hF hE (le_of_eq hc.symm)
  obtain ⟨c', rfl⟩ := TableBExcTwoTB.exists_conj_frame_of_card_E7 hF hE' (le_of_eq hc'.symm)
  refine ⟨c * c'⁻¹, ?_⟩
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

end CFSG.StandardType.FrameRoute.FS81

end
