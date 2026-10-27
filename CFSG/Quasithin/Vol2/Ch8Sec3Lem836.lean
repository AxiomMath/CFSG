module

public import CFSG.Quasithin.Vol2.Ch8Sec3Statements
public import CFSG.Quasithin.Background.E3Prop

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3
open scoped IsMulCommutative

@[expose] def Stmt8_3_6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I → Hyp7_3_1 T L I →
    ∀ _ : IsMulCommutative ↥(fsuV T I), Row711L3Wreath T L I →
    ∀ z : G, orderOf z = 2 →
      fsuV T I ⊓ Subgroup.centralizer (T : Set G) = Subgroup.zpowers z →
      ∀ H : Subgroup G, IsSylowIn 2 (ch83S T L z) H → E1.nParam H = 1 → H ≤ fsuM T L

theorem stmt8_3_6_of (hmod : StmtFSUModule) (h832 : Stmt8_3_2) (h835 : Stmt8_3_5) :
    Stmt8_3_6 := by
  intro G _ _ T L I hyp h731 hc hrow z hz2 hzV H hS hn
  obtain ⟨hV, -⟩ := hmod G T L I hyp.fsu
  have hs := h832 G T L I hyp h731 hc hrow hV
  obtain ⟨hW0, hC1⟩ := h835 G T L I hyp h731 hc hrow z hz2 hzV
  have h19 := e3_19 hV hS (i := 0) (j := 1) (by rw [hn]; rfl) (by rw [hs]; norm_num)
  rw [zero_add] at h19
  rw [← h19]
  exact sup_le (inf_le_right.trans hC1) (inf_le_right.trans hW0)

end CFSG.Quasithin.H13
