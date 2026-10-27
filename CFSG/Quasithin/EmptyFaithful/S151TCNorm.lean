module

public import CFSG.Quasithin.EmptyFaithful.S151TCBlk
public import CFSG.Quasithin.EmptyFaithful.S151TCCh
public import CFSG.Quasithin.EmptyFaithful.S151TCOdd
public import CFSG.Quasithin.EmptyFaithful.S151TCOrd
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin.S151TC

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin
open CFSG.Quasithin.S151TB

variable {G : Type} [Group G] [Finite G] {T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G}

theorem q1_le_normalizer_of_nonnormal (h37 : A37ForSQTK)
    (hC129 : ∀ (G : Type) [Group G] [Finite G], ASC129Statement G)
    (hc : Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L) (hchar : CharTwo L) (hcomp : L ∈ cComp (g1_1516 Z₁))
    (hL3 : IsPSL 3 2 1 (LStar L ⧸ Subgroup.center (LStar L)))
    (hn2 : Set.ncard (conjSubgroupsBy (g1_1516 Z₁) L) = 2) :
    q1_1516 Mc Z₁ ≤ Subgroup.normalizer (L : Set G) := by
  by_contra hRL
  have hq : CFSG.IsQuasisimple (LStar L) := hc.hL.quasi
  have hperf : ⁅L, L⁆ = L := perfect_of_mem_cComp hcomp
  have hZ : Subgroup.center (LStar L) = ⊥ := lStar_center_eq_bot_of_psl32 hq hL3
  have hcard : Nat.card (LStar L) = 168 := card_lStar_of_psl32 hq hL3
  have hyp := hc.h18.five.2.2
  have hSR : s1516 T Z₁ ≤ Subgroup.normalizer (q1_1516 Mc Z₁ : Set G) :=
    (s1516_le T Z₁).trans hc.h18.three
  have hsyl : IsSylowTwoOf (q1_1516 Mc Z₁ ⊓ L) L :=
    C2Push.isSylowTwoOf_inf_of_not_le_normalizer hyp.radical hc.h18.four hSR hcomp hq hRL
  obtain ⟨ρ, hρR, hρL⟩ : ∃ ρ ∈ q1_1516 Mc Z₁, ρ ∉ Subgroup.normalizer (L : Set G) := by
    by_contra h
    push Not at h
    exact hRL h
  have hρG : ρ ∈ g1_1516 Z₁ := (mZ1516_le_g1 Mc Z₁) ((q1_1516_le Mc Z₁) hρR)
  have hne : L.map (MulAut.conj ρ).toMonoidHom ≠ L := fun h =>
    hρL (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h)
  have hset : conjSubgroupsBy (g1_1516 Z₁) L = {L, L.map (MulAut.conj ρ).toMonoidHom} := by
    have hsub : ({L, L.map (MulAut.conj ρ).toMonoidHom} : Set (Subgroup G)) ⊆
        conjSubgroupsBy (g1_1516 Z₁) L := by
      intro K hK
      rcases hK with rfl | rfl
      · exact ⟨1, Subgroup.one_mem _, by ext x; simp⟩
      · exact ⟨ρ, hρG, rfl⟩
    refine (Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)).symm
    rw [hn2, Set.ncard_pair hne.symm]
  have hconj : ∀ σ ∈ q1_1516 Mc Z₁, L.map (MulAut.conj σ).toMonoidHom = L ∨
      L.map (MulAut.conj σ).toMonoidHom = L.map (MulAut.conj ρ).toMonoidHom := by
    intro σ hσ
    have hσG : σ ∈ g1_1516 Z₁ := (mZ1516_le_g1 Mc Z₁) ((q1_1516_le Mc Z₁) hσ)
    have : L.map (MulAut.conj σ).toMonoidHom ∈ conjSubgroupsBy (g1_1516 Z₁) L := ⟨σ, hσG, rfl⟩
    rw [hset] at this
    exact this
  have hqf := hc.ctx.qtfe
  have hpc : pCoreOf 2 (g1_1516 Z₁) ≠ ⊥ := hc.ctx.setting.pCore_g1_ne_bot hqf hc.ctx.mf
  have hL' : L.map (MulAut.conj ρ).toMonoidHom ∈ cComp (g1_1516 Z₁) :=
    map_conj_mem_cComp hcomp hρG
  have hcomm :=
    (lemma_1_2_1_two hqf.qtke hqf.simple hqf.nonabelian h37 hpc hcomp hL' hne.symm).1
  have hR2 : IsPGroup 2 (q1_1516 Mc Z₁) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (mZ1516 Mc Z₁)
  have hYc := charTwo_conjClosure_sup_of_two ρ hρR hR2 hperf hchar hq hZ hconj hcomm
  obtain ⟨-, htype, -⟩ := exists_block_data_of_asc129_of_charTwo (hC129 G) hyp.sqtk hyp.radical
    hyp.cgs hcomp hq hsyl hYc hc.hL.not_le
  rcases htype with ⟨n, hn, hlin⟩ | h5
  · exact (sl2_card_ne hn).1 ((card_lStar_of_isLin2Type hlin).symm.trans hcard)
  · have h60 := (card_lStar_of_isAltType (by norm_num) h5).symm.trans hcard
    norm_num [Nat.factorial] at h60

end CFSG.Quasithin.S151TC
