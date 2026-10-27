module

public import CFSG.Monster.GMS.TableVOfCenter
public import CFSG.Monster.GMS.Facts.Section4

public section

namespace CFSG.Monster.GMS

theorem tableVIn_of_model (hTB : TwoBabyUnique) {H : Type} [Group H] [Finite H]
    {a₀ b₀ z₀ u₀ : H} (ha₀ : IsTwoBabyCentralizer a₀) (hV : TableV a₀ b₀ z₀ u₀) {G : Type}
    [Group G] [Finite G] : TableVIn G := by
  intro a ha
  obtain ⟨φ⟩ := hTB H G a₀ a ha₀ ha
  exact TableV.exists_of_centralizerMulEquiv φ
    (fun c hc => TableV.centralizerMulEquiv_apply_eq hV ha.1 φ c hc) hV

theorem tableVStatement_of_model (hTB : TwoBabyUnique) {H : Type} [Group H] [Finite H]
    {a₀ b₀ z₀ u₀ : H} (ha₀ : IsTwoBabyCentralizer a₀) (hV : TableV a₀ b₀ z₀ u₀) :
    TableVStatement :=
  fun _ _ _ a ha => tableVIn_of_model hTB ha₀ hV a ha

end CFSG.Monster.GMS
