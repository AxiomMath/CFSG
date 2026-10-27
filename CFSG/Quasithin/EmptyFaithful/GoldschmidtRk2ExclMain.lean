module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRk2ExclMem
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRk2ExclA38
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRk2ExclModel
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRk2ParMain
public import CFSG.Quasithin.EmptyFaithful.FLcL45
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRk2ExclDef

public section

namespace CFSG.Quasithin.Rk2

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank
open scoped commutatorElement

theorem input15120RankTwoExclF_of
    (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (hl2 : Input15120L2Block) (kS : Input15120RankTwoNoSwap) :
    Input15120RankTwoExclF := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hc hch hB
  obtain ⟨Y, _, _, ρ, n, hn, hY, hsurj, hq_le, hcent, hker⟩ := rkModel L hB
  have hloc : CFSG.Open.quasithinIsLocal (s1516 T Z₁) L := hc.hL.mem.2
  have hS4 : IsSylowTwoOf (s1516 T Z₁) (g1_1516 Z₁) := hc.h18.four
  have hSL : IsSylowTwoOf (s1516 T Z₁ ⊓ L) L := lemma_15_1_20_sylow hS4 hc.hL
  have hU : IsSylowTwoOf (((s1516 T Z₁ ⊓ L).subgroupOf L).map ρ) ⊤ :=
    isSylowTwoOf_top_map_of_surjective (isSylowTwoOf_top_subgroupOf hSL) ρ hsurj
  have hY' : IsPSL 3 2 n Y ∨ IsSL3 (2 ^ n) Y ∨ IsPSp4 2 n Y ∨ IsG2 2 n Y :=
    hY.elim Or.inl fun h => h.elim (fun h => Or.inr (Or.inr (Or.inl h)))
      fun h => Or.inr (Or.inr (Or.inr h))
  obtain ⟨P, hP⟩ := rank2Pkg_exists hn hY' hU
  have hdata : RkData L (s1516 T Z₁ ⊓ L) ρ _ P :=
    ⟨hsurj, hq_le, hcent, hSL, rfl, hP, hker _ P hP⟩
  have hSN : s1516 T Z₁ ≤ Subgroup.normalizer (L : Set G) := by
    have hq := hc.ctx.qtfe
    rcases lemma_1_2_1_three hq.qtke hq.simple hq.nonabelian h37 h38 hloc.2.2.2
      (cComp_of_isLocal hloc) with hnorm | ⟨-, hA⟩
    · exact le_sup_right.trans
        ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).1 hnorm)
    · exact (rankTwoNotA38Type_holds G L hB hA).elim
  have hSP : ∀ j, s1516 T Z₁ ≤ Subgroup.normalizer (parUp L ρ (P j) : Set G) := fun j =>
    kS G T Mc M Z₁ Z₂ V₁ V₂ L hc hch hB hSN _ (isMaxParabolic2_parUp hdata j)
      (inf_normalizer_le_parUp hdata j)
  have hMZ : ∀ j, levUp L ρ (P j) ≤ mZ1516 Mc Z₁ := by
    intro j
    by_contra hnot
    have hmem := levUp_mem_lFamilyOf hS4 hc.hL.mem.1 hdata hch hSN j (hSP j)
    obtain ⟨m, hm, hpsl, hqs⟩ := levUp_modO2 hdata j
    have hctx : Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ (levUp L ρ (P j)) :=
      ⟨hc.ctx, hc.h17, hc.h18, hc.h19, ⟨hmem, hqs, hnot⟩⟩
    have hcase := hl2 G T Mc M Z₁ Z₂ V₁ V₂ _ hctx (charTwo_levUp hdata hch j) ⟨m, hm, hpsl⟩
    exact not_isShort2_levUp hdata hch j hcase.1.1
  have hSle : s1516 T Z₁ ⊓ L ≤ mZ1516 Mc Z₁ := inf_le_left.trans (s1516_le_mZ1516 hc.h18)
  have hQ : pCoreOf 2 L ≤ s1516 T Z₁ ⊓ L := pCoreOf_two_le_of_sylowIn hSL.1 hSL.2.1 hSL.2.2
  apply hc.hL.not_le
  rw [← levUp_sup_eq hdata (perfect_sup_pCore_of_quasi hc.hL.quasi)]
  exact sup_le (sup_le (sup_le (hMZ 0) (hMZ 1)) hSle) (hQ.trans hSle)

end CFSG.Quasithin.Rk2
