module

public import CFSG.Quasithin.Vol2.Ch10SecQ4A16
public import CFSG.Quasithin.Vol2.Ch10SecQ4A14
public import CFSG.Quasithin.Vol2.Ch10SecQ4A15
public import CFSG.Quasithin.Vol2.Ch10SecQ4A5

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10E4

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.C1

variable {G : Type} [Group G] [Finite G] {K J X T : Subgroup G}

theorem a7_or_hat (hF2 : FactA314B45) (h113 : ASInputs.AS_C_1_13)
    (hXs : CFSG.SectionRank.IsSQTKCat ↥X) (hT : IsSylowTwoOf T X) (hJ : J ∈ cComp X)
    (hKJ : K < J) (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hQK : pCoreOf 2 J ≤ Subgroup.normalizer (K : Set G)) (hK : IsShort2 K) (h5 : IsAltType K 5)
    (hUQ : blockU K ≤ pCoreOf 2 J) (hq : CFSG.IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J)) :
    Nonempty (↥J ⧸ CFSG.pCore 2 ↥J ≃* alternatingGroup (Fin 7)) ∨
      (IsHat (↥J ⧸ CFSG.pCore 2 ↥J) ↥(alternatingGroup (Fin 7)) ∧
        ∀ j : ↥J, (QuotientGroup.mk j : ↥J ⧸ CFSG.pCore 2 ↥J) ∈ Subgroup.center _ →
          (j : G) ∈ Subgroup.centralizer (conjClosure (blockU K) J : Set G)) := by
  have hJX := le_of_mem_cComp hJ
  have hTs := isSylowTwoOf_sup hT (hKJ.le.trans hJX)
  have hZ := blockZ_eq_bot_of_c113 h113 hTs hTK hK h5
  obtain ⟨hQeq, -⟩ := blockQ_eq_sup_of_c113 h113 hTs hTK hK h5
  have hYc := sqtkHypCat_quot hJX hXs
  have hZQ := center_le_pCoreOf hK hKJ.le hQK hUQ hZ hq hYc.o2
  have hQQ : blockQ K ≤ pCoreOf 2 J := hQeq ▸ sup_le hUQ hZQ
  have hW := isElemAbelian_conjClosure hK hKJ.le hQK hUQ
  set ρ := rhoW hK hKJ.le hQK hW with hρ
  have hker : ρ.ker ≤ Subgroup.center _ := by
    intro y hy
    obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective y
    have hj := (rhoW_eq_one_iff hK hKJ.le hQK hW j).mp hy
    exact map_centralizer_le_center hK hKJ.le hQK hq ⟨j, ⟨j.2, hj⟩, rfl⟩
  obtain ⟨k, hk, hkQ, hk2, hcard⟩ := exists_inv_two_card_le h5 hZ
  set b := fK hKJ.le ⟨k, hk⟩ with hb
  have hb2 : orderOf b = 2 := by
    refine orderOf_eq_prime ?_ fun h => hkQ (fK_ker_le hKJ.le ⟨k, hk⟩ h)
    rw [hb, ← map_pow, (fK_eq_one_iff hKJ.le _).mpr]
    simpa using hQQ hk2
  have hbcard : Nat.card ↥(commV (Subgroup.zpowers (ρ b))) ≤ 4 :=
    (card_commV_le hK hKJ.le hQK hUQ hW hk (hQQ hk2)).trans hcard
  rcases hF2 _ hYc hq _ _ (isSylowTwoOf_quot hT hJ) (quotSylow_le_normalizer hKJ.le hTK)
      (range_fK_ne_top hJ hKJ hQK (perfect_of_isAltType_five hK h5)
        (ne_bot_of_isAltType_five h5)) (isAlt_range hKJ.le h5 hQQ) _ IntMod.sq_eq_one ρ hker
      b ⟨_, rfl⟩ hb2 hbcard with h | ⟨hhat, hZker⟩
  · exact Or.inl h
  · refine Or.inr ⟨hhat, fun j hj => ?_⟩
    exact (rhoW_eq_one_iff hK hKJ.le hQK hW j).mp (hZker hj)

end CFSG.Quasithin.Vol2.Ch10.SecF.C10E4
