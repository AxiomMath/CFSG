module

public import CFSG.Quasithin.EmptyFaithful.SzN7Star
public import CFSG.Quasithin.EmptyFaithful.SzN6A5

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417

@[expose] def Lin2SetupNoStar : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15316 T Mc M V₁ V₂ Yp I L t → (∃ n : ℕ, 1 < n ∧ IsLin2Type L n) →
      Yp = YL153 Yp L ⊔ YC153 Yp L ∧ IsElemAbelianOfRank 3 2 (OTwoQuot Yp)

theorem lin2Setup_of_noStar (h37 : A37ForSQTK) (h38 : A38ForSQTK) (k : Lin2SetupNoStar) :
    Lin2Setup := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hn
  obtain ⟨h1, h2⟩ := k G T Mc M V₁ V₂ Yp I L t c hn
  refine ⟨h1, h2, fun v hv => ?_⟩
  obtain ⟨a, ha, w, hw, hvw⟩ := szN7_V_decomp c
    (lin2RLSylow_holds h37 h38 G T Mc M V₁ V₂ Yp I L t c hn) hv
  exact ⟨a, ha, w, hw.2, hvw⟩

@[expose] def A5SetupNoStar : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15316 T Mc M V₁ V₂ Yp I L t → IsAltType L 5 →
      Yp = YL153 Yp L ⊔ YC153 Yp L ∧ IsElemAbelianOfRank 3 2 (OTwoQuot Yp) ∧ blockZ L = ⊥

theorem a5Setup_of_noStar (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (k : A5SetupNoStar) : A5Setup := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hA
  obtain ⟨h1, h2, h3⟩ := k G T Mc M V₁ V₂ Yp I L t c hA
  have hRL := szN6_RL_sylow_of_alt5 h37 h38 c hA
  refine ⟨hRL, h1, h2, h3, fun v hv => ?_⟩
  obtain ⟨a, ha, w, hw, hvw⟩ := szN7_V_decomp c hRL hv
  exact ⟨a, ha, w, hw.2, hvw⟩

end CFSG.Quasithin
