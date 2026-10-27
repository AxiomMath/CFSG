module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4GOdd
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4GEven

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace S15223P4.G

theorem false_of_caseG_gt_one (hcover : AsA36NoOddCover) {G : Type} [Group G] [Finite G]
    {T Mc M H : Subgroup G} {B₀ : Subgroup (MulAut (V154 T Mc M))} {I X : Subgroup G}
    (c : P4Ctx T Mc M H B₀ I X) (n : ℕ) (F : Type) [Field F] [Fintype F] (hn : 1 < n)
    (hF : Fintype.card F = 2 ^ n)
    (e : Nonempty (↥(autOn X (P4V M I X)) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)))
    (hpar : IsMaxParabolic2 (autOn X (P4V M I X)) (autOn (M ⊓ I ⊓ X) (P4V M I X)))
    (hMS : IsMSPair (X ⊔ P4R M I) (P4R M I)) : False := by
  rcases Nat.even_or_odd n with hev | hodd
  · exact false_of_even hcover c hF hev e hpar hMS
  · exact false_of_odd hcover c hn hodd hF e

end S15223P4.G

end CFSG.Quasithin
