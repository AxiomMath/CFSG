module

public import CFSG.Quasithin.Vol2.Ch3E213MOL6

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6 Ch3E213M

namespace E217R1

variable {G : Type} [Group G] [Finite G] {H T M V K : Subgroup G}

theorem false_of_oddL3 (hA : OL.KFactL3U3OuterInv) (hB : OL.KFactL33NoQuadFour)
    (hS : Setting H T M V K) (hC2 : Case2 H T M K) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : (p % 4 = 1 ∧ IsPSU 3 p 1 ↥(E2.star M H K)) ∨
      (p % 4 = 3 ∧ IsPSL 3 p 1 ↥(E2.star M H K) ∧
        E2.InducesOuter (E2.star M H T) (E2.star M H K)))
    (hMK : E2.star M H (M ⊓ K) =
      E2.star M H K ⊓ Subgroup.centralizer (zStar H T M K : Set (E2.StarQuot M H))) : False := by
  by_cases hp3 : p = 3
  · subst hp3
    rcases hK with ⟨h1, -⟩ | ⟨-, hL, -⟩
    · norm_num at h1
    · exact OL.false_of_three hB hS hC2 hL hMK
  · have hp5 : 5 ≤ p := by
      have h2 := hp.two_le
      have h4 : p ≠ 4 := by
        rintro rfl
        norm_num at hp
      omega
    exact OL.false_of_ge5 hA hS hC2 hp hp5 (hK.imp (fun h => h) (fun h => ⟨h.1, h.2.1⟩)) hMK

end E217R1

end CFSG.Quasithin
