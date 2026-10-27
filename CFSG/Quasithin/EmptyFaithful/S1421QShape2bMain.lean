module

public import CFSG.Quasithin.EmptyFaithful.S1421QShape2bC
public import CFSG.Quasithin.EmptyFaithful.S1421QShape2a

public section

namespace CFSG.Quasithin.F146Field.Case2b

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

theorem case2b_shape {T M H K : Subgroup G}
    (hmin : MinParabolic H T (H ⊓ M)) (hK : K ∈ cComp H) (hHK : H = K ⊔ T)
    (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hker : ∀ x : G, x ∈ kerIn (H ⊓ M) H ↔ x ∈ K ⊔ pCoreOf 2 H ∧
      ∀ y ∈ K ⊔ pCoreOf 2 H, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 H)
    {m : ℕ} (hm : 2 ≤ m)
    (hty : IsPSL 3 2 m ↥(E2.star (H ⊓ M) H K) ∨ E2.IsSp4Prime m ↥(E2.star (H ⊓ M) H K))
    (hdiag : E2.IsDiagramNontrivial (E2.star (H ⊓ M) H T) (E2.star (H ⊓ M) H K)
      (E2.star (H ⊓ M) H (T ⊓ K)))
    (hB : E2.IsBorelIn (E2.star (H ⊓ M) H K) (E2.star (H ⊓ M) H ((H ⊓ M) ⊓ K))) :
    ∃ K1 : Subgroup G, Notation1428 T M H K1 ∧ Shape1428 T H K1 := by
  have c : Case2a.Setting T M H K := ⟨hmin, hK, hHK, hTK, hker⟩
  exact case2b_shape_of_central hmin hK hHK hTK hker hm hty hdiag hB
    (isCentralL3Sp4_of_star c hm hty)

end CFSG.Quasithin.F146Field.Case2b
