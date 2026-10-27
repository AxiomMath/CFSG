module

public import CFSG.Quasithin.Vol2.Ch3E213MP4A

public section

namespace CFSG.Quasithin.Ch3E213M

open CFSG.Open CFSG.QuasithinUnique B6

@[expose] def PkgBenderU3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H T M V K : Subgroup G), Setting H T M V K →
    Case2 H T M K → ∀ n : ℕ, 2 ≤ n → IsPSU 3 2 n ↥(E2.star M H K) →
    E2.IsBorelIn (E2.star M H K) (E2.star M H (M ⊓ K)) → E213Concl H T M V

theorem pkgBenderSingle_of
    (hU3 : PkgBenderU3) :
    PkgBenderSingle := by
  rintro G _ _ H T M V K hS h2 n ⟨hn, hL | hSz | hU⟩ hB
  · exact pkgBenderL2Sz G H T M V K hS h2 n hn (Or.inl hL) hB
  · exact pkgBenderL2Sz G H T M V K hS h2 n hn (Or.inr hSz) hB
  · exact hU3 G H T M V K hS h2 n hn hU hB

end CFSG.Quasithin.Ch3E213M
