module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDegDefs
import CFSG.LocalAnalysis.StandardType.GGTDAutomizer

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Blueprint CFSG.Open

variable {G : Type} [Group G] [Finite G]

private theorem qTwoDegRM_card_coxA (n : ℕ) :
    Nat.card (CoxeterMatrix.A n).Group = (n + 1).factorial := by
  obtain ⟨e, -⟩ := ggCoxeterA_mulEquivPerm n
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]

theorem qTwoDeg_rm_of_equal_degree
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦)
    {k : QTwoRowKind} {m d c : ℕ} (hrow : QTwoRowData k m d c Bs L x) (hm : 5 ≤ m)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hP : GGCoxeterPres 3 (ggAutomizerJoin L Bs 𝒦) M e)
    {N : ℕ} (hN : 6 ≤ N) {e' : Fin (N - 1) ≃ ι}
    (hM : M = (CoxeterMatrix.A (N - 1)).reindex e')
    (hNm : N = m) :
    ∀ (y : G) (K' : Subgroup G), GGNbr 3 B x D J y K' →
      ggAutomizer K' Bs ≤ ggAutomizer L Bs := by
  classical
  obtain ⟨hrest, hwc, -, -, -, hbest⟩ := hcfg
  have hcardJoin : Nat.card ↥(ggAutomizerJoin L Bs 𝒦) = N.factorial := by
    subst hM
    calc Nat.card ↥(ggAutomizerJoin L Bs 𝒦)
        = Nat.card ((CoxeterMatrix.A (N - 1)).reindex e').Group := (Nat.card_congr e.toEquiv).symm
      _ = Nat.card (CoxeterMatrix.A (N - 1)).Group :=
          Nat.card_congr ((CoxeterMatrix.A (N - 1)).reindexGroupEquiv e').toEquiv
      _ = (N - 1 + 1).factorial := qTwoDegRM_card_coxA (N - 1)
      _ = N.factorial := by rw [Nat.sub_add_cancel (by omega : 1 ≤ N)]
  have hcardL : Nat.card ↥(ggAutomizer L Bs) = m.factorial := by
    obtain ⟨e0, -⟩ := hrow.weyl
    rw [← Nat.card_congr e0.toEquiv, qTwoDegRM_card_coxA, Nat.sub_add_cancel (by omega : 1 ≤ m)]
  have hle : ggAutomizer L Bs ≤ ggAutomizerJoin L Bs 𝒦 := le_sup_left
  have heq : ggAutomizer L Bs = ggAutomizerJoin L Bs 𝒦 :=
    Subgroup.eq_of_le_of_card_ge hle (le_of_eq (by rw [hcardJoin, hcardL, hNm]))
  intro y K' hK'
  have hrefl : GGReflGenerated 3 (ggAutomizer K' Bs) := hwc y K' hK'
  have hW0 := hrest.2.2.2.2.1 y K' hK' hrefl (Or.inr hwc)
  have hjoin : ggAutomizerJoin L Bs {K'} = ggAutomizer L Bs ⊔ ggAutomizer K' Bs := by
    simp [ggAutomizerJoin]
  have hW : GGWeylReflectionGroup 3 (ggAutomizerJoin L Bs {K'}) := by
    rw [hjoin]; exact hW0
  have hn : GGNbrSet 3 B x D J {K'} :=
    ⟨by simp, fun K hK => by rw [Finset.mem_singleton.mp hK]; exact ⟨y, hK'⟩⟩
  have hcard := hbest {K'} hn hW
  have hle2 : ggAutomizer L Bs ≤ ggAutomizerJoin L Bs {K'} := by
    rw [hjoin]; exact le_sup_left
  have heq2 : ggAutomizer L Bs = ggAutomizerJoin L Bs {K'} :=
    Subgroup.eq_of_le_of_card_ge hle2 (hcard.trans (le_of_eq (by rw [← heq])))
  have hK'le : ggAutomizer K' Bs ≤ ggAutomizerJoin L Bs {K'} := by
    rw [hjoin]; exact le_sup_right
  rwa [← heq2] at hK'le

end CFSG.StandardType.QTwo

end
