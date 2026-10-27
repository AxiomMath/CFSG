module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenInfra
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem s16h_l3_ne_one_fixed_of_pgroup {A : Type*} [Group A] [Finite A] {p : ℕ}
    [hp : Fact p.Prime] (hA : IsPGroup p A) (hA1 : 1 < Nat.card A) {Y : Subgroup (MulAut A)}
    (hY : IsPGroup p Y) : ∃ a : A, a ≠ 1 ∧ ∀ y ∈ Y, (y : MulAut A) a = a := by
  classical
  have hmod := hY.card_modEq_card_fixedPoints A
  obtain ⟨n, hn⟩ := hA.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    omega
  have hpA : Nat.card A ≡ 0 [MOD p] := by
    rw [hn, Nat.modEq_zero_iff_dvd]
    exact dvd_pow_self p hn0
  have hfix : Nat.card (MulAction.fixedPoints Y A) ≡ 0 [MOD p] := hmod.symm.trans hpA
  have h1 : (1 : A) ∈ MulAction.fixedPoints Y A := fun y => map_one (y : MulAut A)
  have hcard : 1 < Nat.card (MulAction.fixedPoints Y A) := by
    have hpos : 0 < Nat.card (MulAction.fixedPoints Y A) :=
      Nat.card_pos_iff.mpr ⟨⟨⟨1, h1⟩⟩, inferInstance⟩
    have := Nat.modEq_zero_iff_dvd.mp hfix
    have := Nat.le_of_dvd hpos this
    have := hp.out.two_le
    omega
  have := Finite.one_lt_card_iff_nontrivial.mp hcard
  obtain ⟨⟨a, ha⟩, ha1⟩ := exists_ne (⟨1, h1⟩ : MulAction.fixedPoints Y A)
  exact ⟨a, fun h0 => ha1 (Subtype.ext h0), fun y hy => ha ⟨y, hy⟩⟩

theorem s16h_e3_l3_three_ne_bot_v1_fixed (D : Data G) {V L : Subgroup G}
    (h : Setting16 D ⊥ V L)
    (hZ : commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L) ≠ ⊥) :
    ∃ v : G, v ∈ v1Sub D.M ⊥ V h.hyp151.isElemAbelian L ∧ v ≠ 1 ∧
      (∀ t ∈ D.T, t * v = v * t) := by
  have hV := h.hyp151.isElemAbelian
  let V₁ : Subgroup G := v1Sub D.M ⊥ V hV L
  have hV1le : V₁ ≤ V := s15_Infra_v1Sub_le h.hyp151.hyp125 hV
  have hV1ne : V₁ ≠ ⊥ := by
    obtain ⟨q, hqne⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hZ
    have hqW : (q : Vtil ⊥ V hV) ∈ wTil ⊥ V hV L := (Subgroup.mem_inf.1 q.2).1
    have hqfix : (q : Vtil ⊥ V hV) ∈ fixV (lBar ⊥ V hV L) := (Subgroup.mem_inf.1 q.2).2
    have hqbar_ne : (q : Vtil ⊥ V hV) ≠ 1 := fun hq => hqne (Subtype.ext hq)
    have hqimg : (q : Vtil ⊥ V hV) ∈ imgTil ⊥ V hV (wSub ⊥ V hV L) := by
      unfold wSub
      rw [imgTil_preTil]
      exact hqW
    obtain ⟨y, hyw, hyq⟩ := (mem_imgTil ⊥ V hV (wSub ⊥ V hV L) _).1 hqimg
    have hycent : y.val ∈ Subgroup.centralizer (L : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have hlM : l ∈ D.M := h.hyp151.le hl
      have hlst : l ∈ stabTil ⊥ V :=
        le_stabTil h.hyp151.hyp125.pairFacts.le_normalizer
          h.hyp151.hyp125.pairFacts.le_normalizer₀ hlM
      have hφ : actTil ⊥ V hV ⟨l, hlst⟩ ∈ lBar ⊥ V hV L :=
        actTil_mem_barSub ⊥ V hV hl hlst
      have hfixl : actTil ⊥ V hV ⟨l, hlst⟩ (q : Vtil ⊥ V hV) =
          (q : Vtil ⊥ V hV) := mem_fixV.mp hqfix _ hφ
      have h1 : mkTil ⊥ V hV (actStab ⊥ V hV ⟨l, hlst⟩ y) = mkTil ⊥ V hV y := by
        rw [← actTil_mk, hyq, hfixl]
      rw [mkTil_eq_iff, Subgroup.mem_bot, actStab_apply_val] at h1
      have h2 : l * y.val * l⁻¹ = y.val := mul_inv_eq_one.mp h1
      calc l * y.val = (l * y.val * l⁻¹) * l := by group
        _ = y.val * l := by rw [h2]
    have hyZ : y.val ∈ wSub ⊥ V hV L ⊓ Subgroup.centralizer (L : Set G) := ⟨hyw, hycent⟩
    have hyV1 : y.val ∈ V₁ := by
      change y.val ∈ v1Sub D.M ⊥ V hV L
      rw [v1Sub_of_eq_bot D.M ⊥ V hV L rfl]
      refine le_iSup (fun m : D.M => conjSubgroup (wSub ⊥ V hV L ⊓
        Subgroup.centralizer (L : Set G)) (m : G)) 1 ?_
      have h1 : ((1 : D.M) : G) = 1 := rfl
      rw [h1, conjSubgroup_one]
      exact hyZ
    have hyne : y.val ≠ 1 := by
      intro hy1
      apply hqbar_ne
      rw [← hyq]
      have : y = 1 := IntMod.val_injective (show y.val = (1 : IntMod V hV).val by
        simpa using hy1)
      rw [this, map_one]
    intro hbot
    exact hyne (Subgroup.mem_bot.1 (hbot ▸ hyV1))
  have hV1p : IsPGroup 2 ↥V₁ := (hV.mono hV1le).isPGroup
  have hV1gt : 1 < Nat.card ↥V₁ := by
    obtain ⟨v, hvne⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hV1ne
    exact Finite.one_lt_card_iff_nontrivial.mpr ⟨v, 1, hvne⟩
  let N : Subgroup G := Subgroup.normalizer (V₁ : Set G)
  have hTN : D.T ≤ N :=
    D.sylowM.le.trans (s15_Infra_le_normalizer_v1Sub h.hyp151.hyp125 hV)
  let Y : Subgroup (MulAut ↥V₁) :=
    (D.T.subgroupOf N).map (Subgroup.normalizerMonoidHom (H := V₁))
  have hYp : IsPGroup 2 Y := (D.sylowM.isPGroup.comap_subtype).map _
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha1, hafix⟩ := s16h_l3_ne_one_fixed_of_pgroup hV1p hV1gt hYp
  let v : G := (a : G)
  have hvV1 : v ∈ V₁ := a.2
  refine ⟨v, hvV1, fun hv => ha1 (Subtype.ext hv), ?_⟩
  intro t ht
  have htN : t ∈ N := hTN ht
  have hmem : Subgroup.normalizerMonoidHom (H := V₁) ⟨t, htN⟩ ∈ Y :=
    ⟨⟨t, htN⟩, (Subgroup.mem_subgroupOf).2 ht, rfl⟩
  have hfixa :=
    hafix (⟨Subgroup.normalizerMonoidHom (H := V₁) ⟨t, htN⟩, hmem⟩ : Y) hmem
  have hconj : t * (a : G) * t⁻¹ = (a : G) := by
    have h' := congrArg (fun z : ↥V₁ => (z : G)) hfixa
    rwa [Subgroup.normalizerMonoidHom_apply_apply_coe] at h'
  calc t * v = (t * v * t⁻¹) * t := by group
    _ = v * t := by rw [hconj]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
