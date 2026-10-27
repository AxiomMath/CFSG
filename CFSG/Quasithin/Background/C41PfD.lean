module

public import CFSG.Quasithin.Background.C41PfC

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

variable (G : Type) [Group G] [Finite G]

@[expose] def C41ProjStep : Prop :=
  ∀ H R M L V K : Subgroup G, HypC28 H R M L V → K ∈ cComp H → CharTwo K →
    CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) → ¬ K ≤ M →
    R ≤ Subgroup.normalizer (K : Set G) → ¬ ⁅conjClosure L M, K⁆ ≤ pCoreOf 2 K →
    conjClosure L M ≤ K

namespace C41Pf

variable {G}

theorem c41Post_of (h82 : Asc82Thm2)
    (hA37 : ∀ (Y : Type) [Group Y], SQTKHyp Y → A37Statement Y)
    (hA38 : ∀ (Y : Type) [Group Y], SQTKHyp Y → A38Part3 Y)
    (hS : ∀ (X : Type) [Group X], A38Types X → IsSimpleGroup X) (hC129 : ASC129Statement G)
    (hC111 : ASC111Statement G) (hC19 : ASC19Statement G) (hKG : C41KGBorel)
    (hProj : C41ProjStep G) {H R M L V K : Subgroup G} (h : HypC28 H R M L V)
    (hK : K ∈ cComp H) (hKc : CharTwo K) (hKq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (hKM : ¬ K ≤ M) : C41Post H R M L V K := by
  have hRN := le_normalizer h82 hA37 hA38 hS hC129 hC111 hC19 hKG h hK hKc hKq hKM
  have hnc := not_commutator_le_pCoreOf hC129 hC111 hC19 (a3Orbits_of_a37_a38 hA37 hA38) h hK hKM
  exact ⟨h, hK, hKc, hKq, hKM, hRN, hProj H R M L V K h hK hKc hKq hKM hRN hnc, hnc⟩

theorem asc41Statement_of (h82 : Asc82Thm2)
    (hA37 : ∀ (Y : Type) [Group Y], SQTKHyp Y → A37Statement Y)
    (hA38 : ∀ (Y : Type) [Group Y], SQTKHyp Y → A38Part3 Y)
    (hS : ∀ (X : Type) [Group X], A38Types X → IsSimpleGroup X) (hC129 : ASC129Statement G)
    (hC111 : ASC111Statement G) (hC19 : ASC19Statement G) (hC27 : ASC27Statement G)
    (hKG : C41KGBorel) (hProj : C41ProjStep G) (hElim : C41Elim G) (hB : C41InspB G)
    (hE : C41InspE G) (hGc : C41InspG G) (hH : C41InspH G) : ASC41Statement G := by
  intro H R M L V K h hK hKc hKq hKM
  have hP := c41Post_of h82 hA37 hA38 hS hC129 hC111 hC19 hKG hProj h hK hKc hKq hKM
  have h23 := c2_10_four h
  obtain ⟨h1, h2, -⟩ := hC27 H R M K _ h23 hK hKq hKc hKM hP.le_normalizer rfl
  rcases SBc17.asc27_cases hC27 h23 hK hKq hKc hKM hP.le_normalizer rfl with
    hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc
  · exact (hElim H R M L V K hP h1 h2 (Or.inl hc)).elim
  · exact (hElim H R M L V K hP h1 h2 (Or.inr (Or.inl hc))).elim
  · exact (hElim H R M L V K hP h1 h2 (Or.inr (Or.inr (Or.inl hc)))).elim
  · exact (hElim H R M L V K hP h1 h2 (Or.inr (Or.inr (Or.inr (Or.inl hc))))).elim
  · exact hB H R M L V K hP h1 h2 hc
  · exact (hElim H R M L V K hP h1 h2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hc)))))).elim
  · exact (hElim H R M L V K hP h1 h2
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hc))))))).elim
  · exact hE H R M L V K hP h1 h2 hc
  · exact (hElim H R M L V K hP h1 h2
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hc))))))).elim
  · exact hGc H R M L V K hP h1 h2 hc
  · exact hH H R M L V K hP h1 h2 hc

end C41Pf

end CFSG.Quasithin
