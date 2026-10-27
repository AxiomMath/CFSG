module

public import CFSG.LocalAnalysis.SectionRank.NativeKGroup
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.Basic

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.CatalogBridge

theorem hypothesisB_of_isKGroupCat {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hA : CatalogHypothesisA p) {H : Subgroup G} (hcop : Nat.Coprime p (Nat.card H))
    (hK : CFSG.SectionRank.IsKGroupCat ↥H) : signalizerMcBrideHypothesisB p H := by
  refine ⟨hp, hcop, ?_⟩
  intro K L hKH hLK _ hsimple hnonab
  let e : K.subgroupOf H ≃* K := Subgroup.subgroupOfEquivOfLe hKH
  let φ : K.subgroupOf H →* K ⧸ L.subgroupOf K :=
    (QuotientGroup.mk' (L.subgroupOf K)).comp e.toMonoidHom
  have hφ : Function.Surjective φ := (QuotientGroup.mk'_surjective _).comp e.surjective
  have hcat : CFSG.Blueprint.Catalog (K ⧸ L.subgroupOf K) :=
    CFSG.SectionRank.catalog_of_isKGroupCat_of_surjective hK (K.subgroupOf H) φ hφ
  have hdvd : Nat.card (K ⧸ L.subgroupOf K) ∣ Nat.card H :=
    (Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_dvd_of_le hKH)
  exact hA _ hsimple hnonab hcat (Nat.Coprime.coprime_dvd_right hdvd hcop)

end CFSG.SignalizerFunctorTheorem.CatalogBridge
