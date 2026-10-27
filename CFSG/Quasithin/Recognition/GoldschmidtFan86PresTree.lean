module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9Tail
public import CFSG.Quasithin.Recognition.GoldschmidtFan86PresIso
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4Loc2
public import CFSG.Quasithin.Recognition.CertSzZero
public import CFSG.Quasithin.Recognition.GoldschmidtFan86TreeMain

public section

namespace CFSG.Quasithin.Fan86

open CFSG.Quasithin SimpleGraph

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace FanTree

variable (F : FanTree Γ G)
include F

theorem edgeA_index {α β : V} (hαβ : Γ.Adj α β) :
    (GoldAmalgam.ofSubgroupPair (MulAction.stabilizer G α) (MulAction.stabilizer G β)).edgeA.index =
      Fan86.valence Γ α := by
  rw [GoldAmalgam.ofSubgroupPair_edgeA_index, Subgroup.inf_relIndex_left]
  exact F.relIndex_stabilizer_eq_valence hαβ le_rfl fun u w hu hw => by
    obtain ⟨g, hg, hgu⟩ := F.loc_trans α u w hu hw
    exact ⟨g, hg, hgu⟩

theorem edgeB_index {α β : V} (hαβ : Γ.Adj α β) :
    (GoldAmalgam.ofSubgroupPair (MulAction.stabilizer G α) (MulAction.stabilizer G β)).edgeB.index =
      Fan86.valence Γ β := by
  rw [GoldAmalgam.ofSubgroupPair_edgeB_index, Subgroup.inf_relIndex_right]
  exact F.relIndex_stabilizer_eq_valence hαβ.symm le_rfl fun u w hu hw => by
    obtain ⟨g, hg, hgu⟩ := F.loc_trans β u w hu hw
    exact ⟨g, hg, hgu⟩

theorem valence_three_of_five {α β : V} (hαβ : Γ.Adj α β) (hα : Fan86.valence Γ α = 5) :
    Fan86.valence Γ β = 3 := by
  have h1 := F.alternating α β hαβ
  have h2 := F.valence β
  simp only [Fan86.valence] at hα ⊢
  omega

end FanTree

theorem fanTreeNoD10_of_inputs (hI : FanTailInputs) : FanTreeNoD10 := by
  intro V G _ _ Γ F α β _ hα ⟨e'⟩
  obtain ⟨L, -, h65, -⟩ := hI V G Γ F
  obtain ⟨e⟩ := h65.2 α hα
  have h := Nat.card_congr (e.symm.trans e').toEquiv
  rw [card_sz_zero_eq_twenty, DihedralGroup.nat_card] at h
  omega

theorem fanTreeOrder_of_tail (hI : FanTailInputs) (hT : FanTail) : FanTreeOrder := by
  intro V G _ _ Γ F α β hαβ hα
  obtain ⟨L, h7, h65, h66, h517, h512⟩ := hI V G Γ F
  obtain ⟨n, hn, hcard, -⟩ := hT V G Γ F L h7 h65 h66 h517 h512 α β hαβ hα
  rcases hn with rfl | rfl
  · exact Or.inl hcard
  · exact Or.inr hcard

theorem fanTreeUnique_of_tail (hI : FanTailInputs) (hT : FanTail) (hIso : IsoOfAdmitsPres) :
    FanTreeUnique := by
  intro V G V' G' _ _ _ _ Γ Γ' F F' α β hαβ hα α' β' hαβ' hα' hc
  obtain ⟨L, h7, h65, h66, h517, h512⟩ := hI V G Γ F
  obtain ⟨L', h7', h65', h66', h517', h512'⟩ := hI V' G' Γ' F'
  obtain ⟨n, -, hcard, hpres⟩ := hT V G Γ F L h7 h65 h66 h517 h512 α β hαβ hα
  obtain ⟨n', -, hcard', hpres'⟩ := hT V' G' Γ' F' L' h7' h65' h66' h517' h512' α' β' hαβ' hα'
  have hnn : n = n' := Nat.pow_right_injective le_rfl (hcard.symm.trans (hc.trans hcard'))
  subst hnn
  have h3 := F.valence_three_of_five hαβ hα
  have h3' := F'.valence_three_of_five hαβ' hα'
  exact hIso n _ _ _ _ _ _ _ _ (F.edgeA_index hαβ ▸ hα) (F.edgeB_index hαβ ▸ h3)
    (F'.edgeA_index hαβ' ▸ hα') (F'.edgeB_index hαβ' ▸ h3') hcard hcard' hpres hpres'

theorem fanTreeMain_of_fanTail
    (hI : FanTailInputs) (hT : FanTail) : FanTreeMain :=
  fanTreeMain_iff.2 ⟨fanTreeNoD10_of_inputs hI, fanTreeOrder_of_tail hI hT,
    fanTreeUnique_of_tail hI hT iso_of_admitsPres⟩

end CFSG.Quasithin.Fan86
