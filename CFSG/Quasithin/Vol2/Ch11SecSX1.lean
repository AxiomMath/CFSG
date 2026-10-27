module

public import CFSG.Quasithin.Vol2.Ch11SecSCartanL
public import CFSG.Quasithin.Vol2.Ch11SecSSetup

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 SecA

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem relIndex_sup_eq' {A B : Subgroup G} (h : A ≤ Subgroup.normalizer (B : Set G)) :
    B.relIndex (A ⊔ B) = B.relIndex A := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer h
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer h
  exact Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient A B h).toEquiv.symm

namespace StarHyp

variable {T L I V₁ V₂ X K : Subgroup G} {P₁ P₂ : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K)}

theorem cartan_le_normalizer_K (hN : NatFacts) (h1102 : Stmt11_0_2)
    (h : StarHyp G T L I V₁ V₂ X K) : X ≤ Subgroup.normalizer (K : Set G) :=
  (cartan_le_normalizer_Vi hN h1102 h.hyp (Or.inl rfl) h.v₁ h.cartan).trans h.normal

theorem isSylowTwoOf_inf_sup (hN : NatFacts) (h1102 : Stmt11_0_2)
    (h : StarHyp G T L I V₁ V₂ X K) (hc : CartanL L V₁ V₂ X) :
    QuasithinUnique.IsSylowTwoOf (T ⊓ K) (K ⊔ xOne X (LOf L V₁)) := by
  have hXK : xOne X (LOf L V₁) ≤ Subgroup.normalizer (K : Set G) :=
    inf_le_left.trans (h.cartan_le_normalizer_K hN h1102)
  have hS := h.isSylowTwoOf_inf
  refine ⟨inf_le_right.trans le_sup_left, hS.2.1, ?_⟩
  change ¬ 2 ∣ (T ⊓ K).relIndex (K ⊔ xOne X (LOf L V₁))
  rw [← Subgroup.relIndex_mul_relIndex _ _ _ inf_le_right le_sup_left, sup_comm,
    relIndex_sup_eq' hXK]
  have h3 : K.relIndex (xOne X (LOf L V₁)) ∣ 3 := hc.cardX₁ ▸ Subgroup.relIndex_dvd_card _ _
  have hodd : Odd (K.relIndex (xOne X (LOf L V₁))) := Odd.of_dvd_nat (by decide) h3
  have hodd' : Odd ((T ⊓ K).relIndex K) := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hS.2.2)
  exact Nat.not_even_iff_odd.mpr (hodd'.mul hodd) ∘ even_iff_two_dvd.mpr

end StarHyp

end CFSG.Quasithin.Vol2.Ch11.SecS
