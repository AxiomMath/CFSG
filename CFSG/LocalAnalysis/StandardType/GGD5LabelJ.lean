module

public import CFSG.LocalAnalysis.StandardType.GGD5Defs
import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaLocal
import CFSG.LocalAnalysis.StandardType.GGTableBBstar
import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaNbr
import CFSG.LocalAnalysis.StandardType.GGQTwoU5Bridges
import CFSG.LocalAnalysis.GLTheoremA.CatB.Rank23
import CFSG.RankThree.PartOne.S11c.OuterInner
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172AGrp
import CFSG.LocalAnalysis.GLTheoremA.CatA.H81Orth.Types
import CFSG.LieType.Multipliers.U42
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CenterHopf

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module

private theorem lup10j_card_Bs {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G}
    {x y : G} {L H : Subgroup G} (M : GGQTwoAmbModel p Bs x y L H) (e : Fin 5 ≃ M.ι)
    (hbas : M.toLin.Basis) : Nat.card Bs = p ^ 5 := by
  have h1 : Nat.card Bs = Nat.card M.V := Nat.card_congr M.model.toEquiv
  have h3 : Fintype.card M.ι = Module.finrank (ZMod p) M.V := hbas.2
  have h2 : Module.finrank (ZMod p) M.V = 5 := by
    rw [← h3, Fintype.card_congr e.symm, Fintype.card_fin]
  haveI : Module.Finite (ZMod p) M.V := Module.finite_of_finrank_pos (by rw [h2]; norm_num)
  rw [h1, Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod, h2]

private theorem lup10j_lieModel_of_hasLabel_twA3 {R : Type} [Group R]
    (hR : GGHasLabel ⟨.twA, 3, 1⟩ R) : Blueprint.LieModel R .PSU 4 2 1 := by
  unfold GGHasLabel CFSG.StandardType.LargeEvenRawDatum at hR
  obtain ⟨K, hKfield, hKfinite, hKcard, ⟨e⟩⟩ := hR
  letI : Field K := hKfield
  letI : Finite K := hKfinite
  have hK' : Nat.card K = (2 ^ 1) ^ 2 := by simpa using hKcard
  refine Blueprint.LieModel.of_mulEquiv e.symm (Or.inl ⟨by decide, ?_⟩)
  exact statedClassicalModel_unitary 4 1 hK'
    ⟨Nat.prime_two, by norm_num, by norm_num, by decide⟩

private theorem lup10j_catalogIs_of_hasLabel_twA3 {R : Type} [Group R]
    (hR : GGHasLabel ⟨.twA, 3, 1⟩ R) :
    CFSG.Yardstones.Md0ec50421ce4.catalogIs R CFSG.LocalAnalysis.GLTheoremA.S9.isU4two := by
  unfold GGHasLabel CFSG.StandardType.LargeEvenRawDatum at hR
  obtain ⟨K, hKfield, hKfinite, hKcard, ⟨e⟩⟩ := hR
  letI : Field K := hKfield
  letI : Finite K := hKfinite
  have hK4 : Nat.card K = 4 := by simpa using hKcard
  exact CFSG.LocalAnalysis.GLTheoremA.CatB.catalogIs_u4two_of_statedProj hK4 e

theorem lup10d_omegaEnd
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting p B Bs x L D J)
    (hp : p = 3) {y : G} {H : Subgroup G} (M : GGQTwoAmbModel p Bs x y L H) (e : Fin 5 ≃ M.ι)
    (hbas : M.toLin.Basis)
    (hD4 : GGInnerDiagOnLabel (fun _ lab => lab.tag = .D ∧ lab.rank = 4 ∧ lab.n = 1) p Bs L) :
    GGHasLabel ⟨.twA, 3, 1⟩ (↥J ⧸ Subgroup.center ↥J) ∧
      ∀ ψ ∈ ggAutomizer L Bs, (∀ d : ↥Bs, (d : G) ∈ D → ψ d = d) → ψ ∈ ggAutomizer J Bs := by
  subst hp
  have hcfg : GGConfig 3 B Bs x L D J := hS.1.1
  obtain ⟨-, hBs, hxB, hLx, -⟩ := hcfg.tableB_facts
  have hSstar : LargeEvenSStar 3 B x L := hcfg.1.2.2.2.2.2.2.1
  have hx1 : x ≠ 1 := hSstar.2.2.1
  have hstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  have hcyc : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (L : Set G) → IsPGroup 3 S → IsCyclic S :=
    fun S hSL hSp => hSstar.2.2.2.2 S hSL hSp
  have hcard5 : Nat.card Bs = 3 ^ 5 := lup10j_card_Bs M e hbas
  obtain ⟨hperf, K, _, _, θ, hK2, hBsN, hI⟩ :=
    exists_omegaPlusDatum_of_innerDiagOnLabel_D4 hD4
  have hZ2 : IsPGroup 2 (Subgroup.center L) :=
    E6QTwo.isPGroup_two_center_of_omegaPlus hK2 θ hperf
  have hBL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x :=
    inf_centralizer_eq_zpowers_of_elemAbelian Nat.prime_three hBs hxB hx1 hLx hcyc
  have hcardE : Nat.card ↥(Bs ⊓ L) = 3 ^ 4 :=
    E6QTwo.card_inf_eq_of_omegaPlus hK2 θ hperf hZ2 hBs hcard5 hx1 hBL hstar hBsN hI
  obtain ⟨hDB, -, hDcard, hxD, -, hJ, -⟩ := hcfg.2.2.1
  obtain ⟨hlab, haut, -⟩ := E6QTwo.hasLabel_and_ggAutomizer_of_omegaPlus hK2 θ hperf hZ2 hBs
    hcard5 hcardE hx1 hLx hBL hstar hBsN hI (hDB.trans hcfg.2.1.1) hDcard hxD hJ
  exact ⟨hlab, haut⟩

theorem lup10d_labelCore_of_labelJ
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting p B Bs x L D J) (hp : p = 3)
    (hJ : GGHasLabel ⟨.twA, 3, 1⟩ (↥J ⧸ Subgroup.center ↥J)) :
    p ∣ Nat.card J ∧
      Nat.Coprime p (Nat.card (Subgroup.center (↥J ⧸ LargeEvenPPrimeCore p ↥J))) ∧
      (∀ b ∈ Bs, ∃ j ∈ J, ∀ k ∈ J, b * k * b⁻¹ = j * k * j⁻¹) := by
  subst hp
  have hcfg : GGConfig 3 B Bs x L D J := hS.1.1
  obtain ⟨-, hBs, -, -, -⟩ := hcfg.tableB_facts
  obtain ⟨-, -, -, -, -, hJcomp, -⟩ := hcfg.2.2.1
  obtain ⟨-, -, hJq⟩ := hJcomp
  have h3J : 3 ∣ Nat.card J := E6QTwo.three_dvd_card_of_hasLabel_twA3 hJ
  have hZ2 : Nat.card (Subgroup.center ↥J) ∣ 2 := by
    have hlie : Blueprint.LieModel (↥J ⧸ Subgroup.center ↥J) .PSU 4 2 1 :=
      lup10j_lieModel_of_hasLabel_twA3 hJ
    obtain ⟨-, ⟨eM⟩⟩ := CFSG.LieType.Multipliers.U42.multiplier_PSU_four_two _ hlie
    have hperf : Group.IsPerfect ↥J := ⟨hJq.1⟩
    have hdvd := CFSG.AGLEmbedding.card_center_dvd_card_griessHopfMultiplier hperf
      (MulEquiv.refl (↥J ⧸ Subgroup.center ↥J))
    rw [Nat.card_congr eM.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod] at hdvd
    exact hdvd
  have hOZ : LargeEvenPPrimeCore 3 ↥J ≤ Subgroup.center ↥J := by
    have hqOpen : CFSG.Open.IsQuasisimple ↥J := hJq
    exact CFSG.LocalAnalysis.GLTheoremA.H81Orth.glaPPrimeCore_le_center_of_dvd_card
      Nat.prime_three hqOpen h3J
  have hcenter : Subgroup.center (↥J ⧸ LargeEvenPPrimeCore 3 ↥J) =
      (Subgroup.center ↥J).map (QuotientGroup.mk' (LargeEvenPPrimeCore 3 ↥J)) := by
    haveI : Group.IsPerfect ↥J := ⟨hJq.1⟩
    exact CFSG.LocalAnalysis.GLTheoremA.S172A.center_quotient_eq_map hOZ
  have hdvd : Nat.card (Subgroup.center (↥J ⧸ LargeEvenPPrimeCore 3 ↥J)) ∣
      Nat.card (Subgroup.center ↥J) := by
    rw [hcenter]
    exact Subgroup.card_map_dvd _ _
  have hcop : Nat.Coprime 3
      (Nat.card (Subgroup.center (↥J ⧸ LargeEvenPPrimeCore 3 ↥J))) :=
    ((by norm_num : Nat.Coprime 3 2).of_dvd_right hZ2).of_dvd_right hdvd
  have hNL : Bs ≤ Subgroup.normalizer (L : Set G) :=
    GGDichotomy.le_normalizer_of_innerDiagOn hS.1.2.2.1.1
  have hcomm : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hBs.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hNJ : Bs ≤ Subgroup.normalizer (J : Set G) :=
    GGDichotomy.le_normalizer_stdSub hcomm hcfg.2.1.1 hcfg.2.2.1 hNL
  have hcat : CFSG.Yardstones.Md0ec50421ce4.catalogIs (↥J ⧸ Subgroup.center ↥J)
      CFSG.LocalAnalysis.GLTheoremA.S9.isU4two := lup10j_catalogIs_of_hasLabel_twA3 hJ
  have hout : ∀ φ : MulAut (↥J ⧸ Subgroup.center ↥J), φ ^ 3 = 1 →
      ∃ r, φ = MulAut.conj r := by
    intro φ hφ
    obtain ⟨b, hb⟩ := CFSG.RankThree.PartOne.exists_inner_of_pow_eq_one_of_not_dvd_card_outer
      Nat.prime_three (CFSG.LocalAnalysis.GLTheoremA.CatB.not_three_dvd_outer_u4two hcat) φ hφ
    exact ⟨b, hb.symm⟩
  have hinner : ∀ b ∈ Bs, ∃ j ∈ J, ∀ k ∈ J, b * k * b⁻¹ = j * k * j⁻¹ := by
    intro b hb
    obtain ⟨j, hj, hconj⟩ :=
      QTwo.U5.inner_of_normalizer_pow_three J hJq.1 hout (hNJ hb) (hBs.2 b hb)
    exact ⟨j, hj, fun k hk => hconj k hk⟩
  exact ⟨h3J, hcop, hinner⟩

end CFSG.StandardType

end

