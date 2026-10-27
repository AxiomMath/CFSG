module

public import CFSG.LocalAnalysis.StandardType.GGQTwoS5A
public import CFSG.LocalAnalysis.StandardType.GGQTwoS5Dodd
public import CFSG.LocalAnalysis.StandardType.GGQTwoS5E6
public import CFSG.LocalAnalysis.StandardType.GGQTwoS5BC
public import CFSG.LocalAnalysis.StandardType.GGQTwoS5E78
public import CFSG.LocalAnalysis.StandardType.GGQTwoS4Classical
public import CFSG.LocalAnalysis.StandardType.GGQTwoS4Exceptional

public section

namespace CFSG.StandardType

open Module

theorem ggQ2s4_leaf_models {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p) : D.LeafModels D.a := by
  rcases ggIntCartan_models D.isWeyl D.isCartan with ⟨n, e, hn, h⟩ | h | h | h | h | h
  · exact ggQ2s4_leaf_classical D e hn h
  · exact ggQ2s4_leaf_exceptional D (Or.inl h)
  · exact ggQ2s4_leaf_exceptional D (Or.inr (Or.inl h))
  · exact ggQ2s4_leaf_exceptional D (Or.inr (Or.inr (Or.inl h)))
  · exact ggQ2s4_leaf_exceptional D (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact ggQ2s4_leaf_exceptional D (Or.inr (Or.inr (Or.inr (Or.inr h))))

theorem ggQ2s5_classify (D : GGQ2Lin 3) (hcard : 3 ≤ Fintype.card {k // k ≠ D.a})
    {π : {k // k ≠ D.a} ≃ {k // k ≠ D.a}} {μ : {k // k ≠ D.a} → ZMod 3}
    (h : D.ScaledAut D.a π μ) : D.ScalarModW D.a π μ ∨ D.GraphList D.a := by
  rcases ggQ2s4_leaf_models D with
    ⟨n, f, hn, hA | ⟨hn2, hB | hC⟩ | ⟨hn4, hD⟩⟩ | ⟨f, hE6⟩ | ⟨f, hE7⟩ | ⟨f, hE8⟩ | ⟨f, hF⟩ |
      ⟨f, hG⟩
  · have hc : Fintype.card {k // k ≠ D.a} = n :=
      (Fintype.card_congr f).symm.trans (Fintype.card_fin n)
    exact Or.inl (ggQ2s5_of_A D (by omega) f hA h)
  · have hc : Fintype.card {k // k ≠ D.a} = n :=
      (Fintype.card_congr f).symm.trans (Fintype.card_fin n)
    exact Or.inl (ggQ2s5_of_BC D (by omega) f (Or.inl hB) h)
  · have hc : Fintype.card {k // k ≠ D.a} = n :=
      (Fintype.card_congr f).symm.trans (Fintype.card_fin n)
    exact Or.inl (ggQ2s5_of_BC D (by omega) f (Or.inr hC) h)
  · rcases Nat.even_or_odd n with ⟨k, hk⟩ | hodd
    · have hk2 : n = 2 * k := by omega
      subst hk2
      exact Or.inr (Or.inl ⟨k, by omega, f, hD⟩)
    · have h5 : 5 ≤ n := by
        obtain ⟨m, hm⟩ := hodd
        omega
      exact Or.inl (ggQ2s5_of_Dodd D h5 hodd f hD h)
  · exact Or.inl (ggQ2s5_of_E6 D f hE6 h)
  · exact Or.inl (ggQ2s5_of_E78 D (Or.inl ⟨f, hE7⟩) h)
  · exact Or.inl (ggQ2s5_of_E78 D (Or.inr ⟨f, hE8⟩) h)
  · exact Or.inr (Or.inr ⟨f, hF⟩)
  · exfalso
    have h2 : Fintype.card {k // k ≠ D.a} = 2 :=
      (Fintype.card_congr f).symm.trans (Fintype.card_fin 2)
    omega

end CFSG.StandardType

end
