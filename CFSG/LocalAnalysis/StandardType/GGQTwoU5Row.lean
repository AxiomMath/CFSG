module

public import CFSG.LocalAnalysis.StandardType.GGQTwoU5Closed
public import CFSG.LocalAnalysis.StandardType.GGQTwoChartDefs

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Assembly CFSG.Blueprint CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem qTwo_oddCenter_QTwoH
    {B Bs L D J : Subgroup G} {x : G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦)
    (hL : LieModel (L ⧸ Subgroup.center L) .PSU 5 2 1) (h5 : Nat.card Bs = 3 ^ 5) :
    Odd (Nat.card (Subgroup.center ↥(QTwoH L 𝒦))) := by
  obtain ⟨⟨⟨hyp, hbs, -⟩, -, hInnAll, -⟩, -, -, hMaxJoin⟩ := hcfg
  have hNbrSet : GGNbrSet 3 B x D J 𝒦 := hMaxJoin.1
  have hnormL : Bs ≤ Subgroup.normalizer (L : Set G) := GGInnerDiagOn.le_normalizer hInnAll.1
  have hnormS : Bs ≤ Subgroup.normalizer ((𝒦.sup (fun K => K) : Subgroup G) : Set G) := by
    apply U5.le_normalizer_finset_sup
    intro K hK
    obtain ⟨y, hy⟩ := hNbrSet.2 K hK
    exact GGInnerDiagOn.le_normalizer (hInnAll.2 y K hy)
  have hnorm : Bs ≤ Subgroup.normalizer ((L ⊔ (𝒦.sup (fun K => K) : Subgroup G) : Subgroup G) : Set G) :=
    U5.le_normalizer_sup hnormL hnormS
  have hsup : (𝒦.sup (fun K => K) : Subgroup G) = ⨆ k ∈ 𝒦, k := Finset.sup_eq_iSup 𝒦 (fun K => K)
  have hodd := U5.cor_9_4_closed hyp hbs h5
    (CFSG.Models.LieModel.of_blueprint_of_ne_zero (by norm_num) hL)
    (L ⊔ (𝒦.sup (fun K => K) : Subgroup G)) hnorm
  rw [hsup] at hodd
  exact hodd

end CFSG.StandardType.QTwo

end
