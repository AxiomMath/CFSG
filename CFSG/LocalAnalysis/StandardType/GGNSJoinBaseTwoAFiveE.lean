module

public import CFSG.LocalAnalysis.StandardType.GGNSJoinBaseTwoE
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoBridgeDefs
public import CFSG.LocalAnalysis.StandardType.GGUSixTwoTorus
import CFSG.LocalAnalysis.StandardType.GGUSixTwoTorusTwoGroup
import CFSG.LocalAnalysis.StandardType.GGSecFiveNSQ2U62Setup
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge
import CFSG.LocalAnalysis.StandardType.GGSecFiveRest
import CFSG.LocalAnalysis.StandardType.GGFrameRouteLower
import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoUnitary
import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoUnitaryAux
import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoInnerQ
import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoAutLQAux
import CFSG.LocalAnalysis.StandardType.GGLtBstarOfInner
import CFSG.LocalAnalysis.StandardType.GGTableBBstar

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem eq_bot_of_isPGroup_two_of_map_eq_torU {G K : Type} [Group G] [Field K] [Finite K]
    (hK : Nat.card K = 4) {Bs L U : Subgroup G}
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hZ : Subgroup.center L = ⊥)
    (hmap : ((Bs ⊓ L).subgroupOf L).map
      (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))) = USixTwo.torU K)
    (hUL : U ≤ L) (hU : IsPGroup 2 U) (hBsU : Bs ≤ Subgroup.normalizer (U : Set G)) :
    U = ⊥ := by
  let π : ↥L →* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) :=
    θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
  have hπinj : Function.Injective π := by
    have hker : π.ker = ⊥ := by
      rw [show π.ker = (QuotientGroup.mk' (Subgroup.center L)).ker from
        MonoidHom.ker_comp_of_injective _ _ θ.injective, QuotientGroup.ker_mk', hZ]
    exact (MonoidHom.ker_eq_bot_iff π).mp hker
  let W : Subgroup (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) :=
    (U.subgroupOf L).map π
  have hU2' : IsPGroup 2 (U.subgroupOf L) := by
    rw [← Subgroup.comap_subtype]
    exact hU.comap_of_injective L.subtype L.subtype_injective
  have hW2 : IsPGroup 2 W := IsPGroup.map hU2' π
  have hmap' : ((Bs ⊓ L).subgroupOf L).map π = USixTwo.torU K := hmap
  have hnorm : (Bs ⊓ L).subgroupOf L ≤
      Subgroup.normalizer (U.subgroupOf L : Set ↥L) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro u
    have hbG : (b : G) ∈ Bs := (Subgroup.mem_subgroupOf.mp hb).1
    simpa [Subgroup.mem_subgroupOf] using
      Subgroup.mem_normalizer_iff.mp (hBsU hbG) (u : G)
  have hmapnorm : USixTwo.torU K ≤ Subgroup.normalizer (W : Set _) := by
    rw [← hmap']
    exact (Subgroup.map_mono hnorm).trans
      (Subgroup.le_normalizer_map (H := U.subgroupOf L) π)
  have hWbot : W = ⊥ :=
    USixTwo.eq_bot_of_isPGroup_two_of_torU_le_normalizer hK hW2 hmapnorm
  have hUbot : U.subgroupOf L = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective (H := U.subgroupOf L) (f := π) hπinj).mp hWbot
  rw [← Subgroup.map_subgroupOf_eq_of_le hUL, hUbot, Subgroup.map_bot]

theorem GGSecFiveRouteCfg.eq_three_and_E6_of_twA5_typeE
    {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hTB : GGTBFixInput) (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {ι : Type}
    {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (hE : GGIsWeylMatrixE M)
    (h : GGInnerDiagOnLabel (fun p lab => ggRowP_ESU p lab ∧ lab.n = 1 ∧ lab.rank = 5) p Bs L) :
    p = 3 ∧ ∃ σ : Fin 6 ≃ ι, M = CoxeterMatrix.E₆.reindex σ := by
  classical
  have hconf : GGConfig p B Bs x L D J := hcfg.1.1
  have hFix : ∀ b : ↥Bs, (∀ φ ∈ ggAutomizer L Bs, φ b = b) →
      (b : G) ∈ Subgroup.zpowers x := by
    obtain ⟨y, K', hN⟩ := exists_ggNbr hconf.1.2.2.2.2.2.2.2 hconf.2.2
    intro b hb
    exact hTB G p B Bs x L D J hconf hcfg.1.2.1 hcfg.1.2.2.1 hcfg.1.2.2.2.1 y K' hN
      (hcfg.2.1 y K' hN) (Or.inr hcfg.2.1) b hb
  obtain ⟨rfl, -, hle⟩ := nsQ2U62_weyl hconf hFix h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hBs : IsElemAbelian 3 Bs := ggRouteCfg_isElemAbelian hcfg
  refine ⟨rfl, ?_⟩
  rcases hE with hM | ⟨σ, hM⟩ | ⟨σ, hM⟩
  · exact hM
  ·
    have hW : GGWeylOfType 3 CoxeterMatrix.E₇ (ggAutomizerJoin L Bs 𝒦) := by
      subst hM
      exact GGWeylOfType.of_reindex ⟨e, hpres.2⟩
    have h7 : 3 ^ 7 ≤ Nat.card Bs := FrameRoute.pow_le_card_of_weylOfType_of_two
      Nat.prime_three (by norm_num) hBs hW FrameRoute.exists_elemAbelian_two_coxeterE7
    have := h7.trans hle
    norm_num at this
  ·
    have hW : GGWeylOfType 3 CoxeterMatrix.E₈ (ggAutomizerJoin L Bs 𝒦) := by
      subst hM
      exact GGWeylOfType.of_reindex ⟨e, hpres.2⟩
    have h8 : 3 ^ 8 ≤ Nat.card Bs := FrameRoute.pow_le_card_of_weylOfType_of_two
      Nat.prime_three (by norm_num) hBs hW FrameRoute.exists_elemAbelian_two_coxeterE8
    have := h8.trans hle
    norm_num at this

theorem GGConfig.lt_bstar_of_twA5_of_card_eq {G : Type} [Group G] [Finite G] {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hconf : GGConfig 3 B Bs x L D J)
    (hlab : GGInnerDiagOnLabel (fun _ lab => lab.tag = .twA ∧ lab.rank = 5 ∧ lab.n = 1) 3 Bs L)
    (hcard : Nat.card Bs = 3 ^ 5) (hZ : Subgroup.center L = ⊥) : B < Bs := by
  classical
  have hS : LargeEvenSStar 3 B x L := hconf.1.2.2.2.2.2.2.1
  obtain ⟨-, hBs, hxB, hLx, -⟩ := hconf.tableB_facts
  have hx1 : x ≠ 1 := hS.2.2.1
  have horderx : orderOf x = 3 := orderOf_eq_prime (hBs.2 x hxB) hx1
  have hstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs := hconf.2.1.2.2.2
  have hBL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x :=
    inf_centralizer_eq_zpowers_of_elemAbelian Nat.prime_three hBs hxB hx1 hLx
      (fun S hSL hSp => hconf.1.2.2.2.2.2.2.1.2.2.2.2 S hSL hSp)
  obtain ⟨hperf, K, hfieldK, hfiniteK, θ, hK4, hBsN, hI⟩ :=
    exists_unitaryDatum_of_innerDiagOnLabel_twA5 hlab
  have hZ2 : IsPGroup 2 (Subgroup.center L) := by
    rw [hZ]
    exact IsPGroup.of_bot
  obtain ⟨-, θ', hmap⟩ := E6QTwo.card_inf_eq_and_exists_map_eq_torU_of_isPGroup hK4 θ hperf hZ2
    hBs hcard hxB hx1 hBL hstar hBsN hI
  have hxL : x ∉ L := not_mem_of_isPGroup_two_center hZ2 horderx hLx
  refine hconf.lt_bstar_of_inner (by rw [hZ, Subgroup.card_bot]; exact Nat.coprime_one_left 3)
    (fun b hb => ?_) (fun U hUL hU2 hBsU => ?_)
  ·
    obtain ⟨z, hz, a, ha, rfl⟩ :=
      E6QTwo.exists_mul_zpowers hK4 θ' hZ2 hmap hBs hcard hxB hxL hLx hb
    refine ⟨⟨a, ha.2⟩, fun y hy => ?_⟩
    rcases Subgroup.mem_zpowers_iff.mp hz with ⟨n, rfl⟩
    have hcommxy : Commute x y :=
      (Subgroup.mem_centralizer_singleton_iff.mp (hLx hy)).symm
    have hcomm : Commute (x ^ n) y := hcommxy.zpow_left n
    change (x ^ n * a)⁻¹ * y * (x ^ n * a) = a⁻¹ * y * a
    calc
      (x ^ n * a)⁻¹ * y * (x ^ n * a)
          = a⁻¹ * ((x ^ n)⁻¹ * y * (x ^ n)) * a := by group
      _ = a⁻¹ * y * a := by rw [hcomm.inv_mul_cancel]
  · rw [eq_bot_of_isPGroup_two_of_map_eq_torU hK4 θ' hZ hmap hUL hU2 hBsU]
    exact bot_le

theorem GGSecFiveRouteCfg.lt_bstar_of_twA5_typeE
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hT : GGSecFiveE6QTwoTimmesfeldInput)
    (hTB : GGTBFixInput) (hU62 : GGU62OuterDiagInput)
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (hE : GGIsWeylMatrixE M)
    (hns : ¬ GGSplitLie p L)
    (h : GGInnerDiagOnLabel (fun p lab => ggRowP_ESU p lab ∧ lab.n = 1 ∧ lab.rank = 5) p Bs L) :
    B < Bs := by
  classical
  obtain ⟨rfl, σ, hM⟩ := hcfg.eq_three_and_E6_of_twA5_typeE hTB hpres hE h
  by_cases hsix : ∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card ↥(ggRankOneIn L Bs r) ≠ 6
  · exact (NSJoin.false_of_twA5_two_L_typeE hTB hU62 hcfg hpres hE hsix h).elim
  push Not at hsix
  obtain ⟨r, hrA, hrC, hr6⟩ := hsix
  have hC : GGSecFiveE6QTwoCfg 3 B Bs x L D J :=
    ⟨𝒦, hcfg, hns, ι, M, e, hpres, ⟨σ, hM⟩, r, hrA, hrC, hr6⟩
  have hlab : GGInnerDiagOnLabel (fun _ lab => lab.tag = .twA ∧ lab.rank = 5 ∧ lab.n = 1)
      3 Bs L := by
    refine h.mono' fun lab hl => ?_
    obtain ⟨hesu, hn, hr⟩ := hl
    refine ⟨?_, hr, hn⟩
    rcases hesu with ⟨⟨ht, -⟩ | ⟨-, hr3⟩, -⟩
    · exact ht
    · omega
  have hcard : Nat.card Bs = 3 ^ 5 := hC.card_bstar_eq_of_twA5 (hT G B Bs x L D J hC) hlab
  exact GGConfig.lt_bstar_of_twA5_of_card_eq hcfg.1.1 hlab hcard
    (hC.center_eq_bot_of_twA5 hlab hcard)

end CFSG.StandardType
