module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P71Glue
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P71Dih
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P71Sing
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P71Trip
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P71Fix

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem fan_7_1 (F : FanTree Γ G) (L : ZLab Γ G) (h40 : Fan40 F) (h62 : Fan62 F)
    (h63 : Fan63 F) (h65 : Fan65 F) (h517 : Fan517 F L) (hXi : ∃ T : Track Γ G, InXi T) :
    Fan71a F L ∧ Fan71b F ∧ Fan71c F L := by
  obtain ⟨T, hT⟩ := hXi
  obtain ⟨c, h5⟩ := P71.exists_valence_five F T
  have hA := P71.arcTrans_of_track F L h40 h62 h63 h65 T hT h5
  have hb : ∀ l, valence Γ l = 5 → L.z l ∈ ballStab Γ G 4 l := fun l hl => by
    have hc := L.isCentral l hl
    have := h63 h40 l (L.z l) ⟨hc.2.1, hc.2.2.1, hc.1, hc.2.2.2⟩ 1
    simpa using this
  have hR := P71.exists_moved_arc F L h40 h62 h63 T hT h5
  have hfix : ∀ l, valence Γ l = 5 → fixedPts (V := V) (L.z l) = {v | Γ.dist l v ≤ 4} :=
    fun l hl => P71.fixedPts_label F L hA hR hb hl
  have hD := P71.exists_dihedral_arc F L h40 h62 h63 T hT h5
  refine ⟨P71.fan71a_of F L h65 hb hA hD,
    ⟨P71.transGe_of_arcTrans F hA, P71.singGe_eight F L hA hb hfix⟩, hfix,
    fun a b ha hb' hab => P71.label_ne F L hfix ha hb' hab, ?_⟩
  intro a b c ha hb' hc hab hac hbc hnot hprod
  exact hnot (P71.exists_nbr_of_prod_one F L hfix (fun α hα => (h517 α hα).2) ha hb' hc hab hac
    hbc hprod)

end CFSG.Quasithin.Fan86
