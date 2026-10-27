
module

public import CFSG.Monster.B.TwoA.Sp8.P0RankBridge
public import CFSG.Monster.B.TwoA.Sp8.P0RankWalk

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8.WordRel

open CFSG.Monster.Code CFSG.Monster.B CFSG.Monster.B.TwoA
  CFSG.ComponentClassification.RankTwoSporadic.B.TwoDFix CFSG.Open
open MonsterB.P0Rank CFSG.Monster.B.TwoA.Sp8.P0Rank
open CFSG.KC.BvecLoop
open scoped commutatorElement
attribute [local instance low] Classical.propDecidable

@[expose] def layerD (E : Subgroup Dfull) : Finset ℕ :=
  (Finset.range (2 ^ 16)).filter fun σ =>
    ∃ x : Lgrp, (x : Dfull) ∈ E ∧ sCoord x = Multiplicative.ofAdd (bvec 16 σ)

@[expose] def layerW (E : Subgroup Dfull) : Finset ℕ :=
  (Finset.range (2 ^ 10)).filter fun κ =>
    ∃ g : P0, (g : Dfull) ∈ E ∧ uCoord g = Multiplicative.ofAdd (bvec 10 κ)

@[expose] def layerY (E : Subgroup Dfull) : Finset ℕ :=
  (Finset.range (2 ^ 9)).filter fun τ => tD τ ∈ E

private noncomputable def kerUEquiv {E : Subgroup Dfull} (hE : E ≤ P0) :
    (uCoord.comp (Subgroup.inclusion hE)).ker ≃ ↥(E ⊓ Lgrp) where
  toFun x :=
    ⟨x.1.1, ⟨x.1.2, (uCoord_eq_one_iff ⟨x.1.1, hE x.1.2⟩).1 x.2⟩⟩
  invFun y :=
    ⟨⟨y.1, (Subgroup.mem_inf.1 y.2).1⟩,
      (uCoord_eq_one_iff ⟨y.1, hE (Subgroup.mem_inf.1 y.2).1⟩).2 (Subgroup.mem_inf.1 y.2).2⟩
  left_inv x := by ext; rfl
  right_inv y := by ext; rfl

private theorem card_rangeW {E : Subgroup Dfull} (hE : E ≤ P0) :
    Nat.card (uCoord.comp (Subgroup.inclusion hE)).range = (layerW E).card := by
  have h1 : Nat.card (uCoord.comp (Subgroup.inclusion hE)).range ≤ Nat.card ↥(layerW E) := by
    refine Nat.card_le_card_of_injective
      (fun v : (uCoord.comp (Subgroup.inclusion hE)).range => by
        let κ := Classical.choose (exists_bvec 10 v.1.toAdd)
        exact ⟨κ, by
          obtain ⟨hκ, hb⟩ := Classical.choose_spec (exists_bvec 10 v.1.toAdd)
          obtain ⟨g, hg⟩ := v.2
          refine Finset.mem_filter.2 ⟨Finset.mem_range.2 hκ, ⟨⟨g.1, hE g.2⟩, g.2, ?_⟩⟩
          exact hg.trans (by rw [hb, ofAdd_toAdd])⟩) ?_
    intro v w h
    have hmask : Classical.choose (exists_bvec 10 v.1.toAdd) =
        Classical.choose (exists_bvec 10 w.1.toAdd) := congrArg Subtype.val h
    obtain ⟨-, hbv⟩ := Classical.choose_spec (exists_bvec 10 v.1.toAdd)
    obtain ⟨-, hbw⟩ := Classical.choose_spec (exists_bvec 10 w.1.toAdd)
    apply Subtype.ext
    calc v.1 = Multiplicative.ofAdd v.1.toAdd := (ofAdd_toAdd v.1).symm
      _ = Multiplicative.ofAdd (bvec 10 (Classical.choose (exists_bvec 10 v.1.toAdd))) :=
        congrArg Multiplicative.ofAdd hbv.symm
      _ = Multiplicative.ofAdd (bvec 10 (Classical.choose (exists_bvec 10 w.1.toAdd))) :=
        congrArg (fun t => Multiplicative.ofAdd (bvec 10 t)) hmask
      _ = Multiplicative.ofAdd w.1.toAdd := congrArg Multiplicative.ofAdd hbw
      _ = w.1 := ofAdd_toAdd w.1
  have h2 : Nat.card ↥(layerW E) ≤ Nat.card (uCoord.comp (Subgroup.inclusion hE)).range := by
    refine Nat.card_le_card_of_injective
      (fun κ : ↥(layerW E) => by
        let g := Classical.choose ((Finset.mem_filter.1 κ.2).2)
        have hgspec := Classical.choose_spec ((Finset.mem_filter.1 κ.2).2)
        exact ⟨Multiplicative.ofAdd (bvec 10 (κ : ℕ)),
          ⟨⟨g.1, hgspec.1⟩, by
            show uCoord ⟨g.1, hE hgspec.1⟩ = Multiplicative.ofAdd (bvec 10 (κ : ℕ))
            rw [show (⟨g.1, hE hgspec.1⟩ : P0) = g from Subtype.ext rfl]
            exact hgspec.2⟩⟩) ?_
    intro κ κ' h
    have hmask : Multiplicative.ofAdd (bvec 10 (κ : ℕ)) =
        Multiplicative.ofAdd (bvec 10 (κ' : ℕ)) := congrArg Subtype.val h
    have hb : bvec 10 (κ : ℕ) = bvec 10 (κ' : ℕ) := Multiplicative.ofAdd.injective hmask
    apply Subtype.ext
    exact bvec_inj (Finset.mem_range.1 (Finset.mem_filter.1 κ.2).1)
      (Finset.mem_range.1 (Finset.mem_filter.1 κ'.2).1) hb
  have h3 : Nat.card ↥(layerW E) = (layerW E).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  exact (le_antisymm h1 h2).trans h3

private noncomputable def kerSEquiv {E : Subgroup Dfull} :
    (sCoord.comp (Subgroup.inclusion (inf_le_right : E ⊓ Lgrp ≤ Lgrp))).ker ≃ ↥(E ⊓ T9) where
  toFun x :=
    ⟨x.1.1, ⟨x.1.2.1, (sCoord_eq_one_iff ⟨x.1.1, x.1.2.2⟩).1 x.2⟩⟩
  invFun y :=
    ⟨⟨y.1, ⟨(Subgroup.mem_inf.1 y.2).1, T9_le_Lgrp (Subgroup.mem_inf.1 y.2).2⟩⟩,
      (sCoord_eq_one_iff ⟨y.1, T9_le_Lgrp (Subgroup.mem_inf.1 y.2).2⟩).2 (Subgroup.mem_inf.1 y.2).2⟩
  left_inv x := by ext; rfl
  right_inv y := by ext; rfl

private theorem card_rangeS {E : Subgroup Dfull} :
    Nat.card (sCoord.comp (Subgroup.inclusion (inf_le_right : E ⊓ Lgrp ≤ Lgrp))).range =
      (layerD E).card := by
  have h1 : Nat.card (sCoord.comp (Subgroup.inclusion
      (inf_le_right : E ⊓ Lgrp ≤ Lgrp))).range ≤ Nat.card ↥(layerD E) := by
    refine Nat.card_le_card_of_injective
      (fun v : (sCoord.comp (Subgroup.inclusion
          (inf_le_right : E ⊓ Lgrp ≤ Lgrp))).range =>
        let σ := Classical.choose (exists_bvec 16 v.1.toAdd)
        ⟨σ, by
          obtain ⟨hσ, hb⟩ := Classical.choose_spec (exists_bvec 16 v.1.toAdd)
          obtain ⟨x, hx⟩ := v.2
          refine Finset.mem_filter.2 ⟨Finset.mem_range.2 hσ,
            ⟨Subgroup.inclusion inf_le_right x, (Subgroup.mem_inf.1 x.2).1, ?_⟩⟩
          exact hx.trans (by rw [hb, ofAdd_toAdd])⟩) ?_
    intro v w h
    have hmask : Classical.choose (exists_bvec 16 v.1.toAdd) =
        Classical.choose (exists_bvec 16 w.1.toAdd) := congrArg Subtype.val h
    obtain ⟨-, hbv⟩ := Classical.choose_spec (exists_bvec 16 v.1.toAdd)
    obtain ⟨-, hbw⟩ := Classical.choose_spec (exists_bvec 16 w.1.toAdd)
    apply Subtype.ext
    calc v.1 = Multiplicative.ofAdd v.1.toAdd := (ofAdd_toAdd v.1).symm
      _ = Multiplicative.ofAdd (bvec 16 (Classical.choose (exists_bvec 16 v.1.toAdd))) :=
        congrArg Multiplicative.ofAdd hbv.symm
      _ = Multiplicative.ofAdd (bvec 16 (Classical.choose (exists_bvec 16 w.1.toAdd))) :=
        congrArg (fun t => Multiplicative.ofAdd (bvec 16 t)) hmask
      _ = Multiplicative.ofAdd w.1.toAdd := congrArg Multiplicative.ofAdd hbw
      _ = w.1 := ofAdd_toAdd w.1
  have h2 : Nat.card ↥(layerD E) ≤ Nat.card (sCoord.comp (Subgroup.inclusion
      (inf_le_right : E ⊓ Lgrp ≤ Lgrp))).range := by
    refine Nat.card_le_card_of_injective
      (fun σ : ↥(layerD E) => by
        let x := Classical.choose (Finset.mem_filter.1 σ.2).2
        have hxspec := Classical.choose_spec (Finset.mem_filter.1 σ.2).2
        exact ⟨Multiplicative.ofAdd (bvec 16 (σ : ℕ)), ⟨⟨x.1, ⟨hxspec.1, x.2⟩⟩, by
          show sCoord x = _
          exact hxspec.2⟩⟩) ?_
    intro σ τ h
    have hmask : Multiplicative.ofAdd (bvec 16 (σ : ℕ)) =
        Multiplicative.ofAdd (bvec 16 (τ : ℕ)) := congrArg Subtype.val h
    have hb : bvec 16 (σ : ℕ) = bvec 16 (τ : ℕ) := Multiplicative.ofAdd.injective hmask
    apply Subtype.ext
    exact bvec_inj (Finset.mem_range.1 (Finset.mem_filter.1 σ.2).1)
      (Finset.mem_range.1 (Finset.mem_filter.1 τ.2).1) hb
  have h3 : Nat.card ↥(layerD E) = (layerD E).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  exact (le_antisymm h1 h2).trans h3

private theorem card_T9 {E : Subgroup Dfull} :
    Nat.card ↥(E ⊓ T9) = (layerY E).card := by
  have h1 : Nat.card ↥(E ⊓ T9) ≤ Nat.card ↥(layerY E) := by
    refine Nat.card_le_card_of_injective
      (fun y : ↥(E ⊓ T9) => by
        let τ := Classical.choose (exists_bvec 9 (tVec y.1))
        exact ⟨τ, by
          obtain ⟨hτ, hb⟩ := Classical.choose_spec (exists_bvec 9 (tVec y.1))
          refine Finset.mem_filter.2 ⟨Finset.mem_range.2 hτ, ?_⟩
          rw [eq_of_tVec_eq (tD_mem_T9 _) (Subgroup.mem_inf.1 y.2).2 (by rw [tVec_tD, hb])]
          exact (Subgroup.mem_inf.1 y.2).1⟩) ?_
    intro y z h
    have hτ : Classical.choose (exists_bvec 9 (tVec y.1)) =
        Classical.choose (exists_bvec 9 (tVec z.1)) := congrArg Subtype.val h
    have hy : tD (Classical.choose (exists_bvec 9 (tVec y.1))) = y.1 :=
      eq_of_tVec_eq (tD_mem_T9 _) (Subgroup.mem_inf.1 y.2).2
        (by rw [tVec_tD, (Classical.choose_spec (exists_bvec 9 (tVec y.1))).2])
    have hz : tD (Classical.choose (exists_bvec 9 (tVec z.1))) = z.1 :=
      eq_of_tVec_eq (tD_mem_T9 _) (Subgroup.mem_inf.1 z.2).2
        (by rw [tVec_tD, (Classical.choose_spec (exists_bvec 9 (tVec z.1))).2])
    apply Subtype.ext
    calc y.1 = tD (Classical.choose (exists_bvec 9 (tVec y.1))) := hy.symm
      _ = tD (Classical.choose (exists_bvec 9 (tVec z.1))) := by rw [hτ]
      _ = z.1 := hz
  have h2 : Nat.card ↥(layerY E) ≤ Nat.card ↥(E ⊓ T9) := by
    refine Nat.card_le_card_of_injective
      (fun τ : ↥(layerY E) =>
        ⟨tD (τ : ℕ), Subgroup.mem_inf.2
          ⟨(Finset.mem_filter.1 τ.2).2, tD_mem_T9 (τ : ℕ)⟩⟩) ?_
    intro σ τ h
    have hb : tD (σ : ℕ) = tD (τ : ℕ) := congrArg Subtype.val h
    have ht : tVec (tD (σ : ℕ)) = tVec (tD (τ : ℕ)) := congrArg tVec hb
    rw [tVec_tD, tVec_tD] at ht
    apply Subtype.ext
    exact bvec_inj (Finset.mem_range.1 (Finset.mem_filter.1 σ.2).1)
      (Finset.mem_range.1 (Finset.mem_filter.1 τ.2).1) ht
  have h3 : Nat.card ↥(layerY E) = (layerY E).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  exact (le_antisymm h1 h2).trans h3

theorem natCard_eq_layers {E : Subgroup Dfull} (hE : E ≤ P0) :
    Nat.card E = (layerD E).card * (layerW E).card * (layerY E).card := by
  let fW : E →* Multiplicative (Fin 10 → ZMod 2) := uCoord.comp (Subgroup.inclusion hE)
  let fS : ↥(E ⊓ Lgrp) →* Multiplicative (Fin 16 → ZMod 2) :=
    sCoord.comp (Subgroup.inclusion (inf_le_right : E ⊓ Lgrp ≤ Lgrp))
  have hkerW : Nat.card fW.ker = Nat.card ↥(E ⊓ Lgrp) :=
    Nat.card_congr (kerUEquiv hE)
  have hrangeW : Nat.card fW.range = (layerW E).card := card_rangeW hE
  have hkerS : Nat.card fS.ker = Nat.card ↥(E ⊓ T9) := Nat.card_congr kerSEquiv
  have hrangeS : Nat.card fS.range = (layerD E).card := card_rangeS
  have hcardE : Nat.card E = Nat.card ↥(E ⊓ Lgrp) * (layerW E).card := by
    rw [← Subgroup.card_ker_mul_card_range fW, hkerW, hrangeW]
  have hcardL : Nat.card ↥(E ⊓ Lgrp) = (layerD E).card * Nat.card ↥(E ⊓ T9) := by
    rw [← Subgroup.card_ker_mul_card_range fS, hkerS, hrangeS, mul_comm]
  have hcardT : Nat.card ↥(E ⊓ T9) = (layerY E).card := card_T9
  rw [hcardE, hcardL, hcardT]
  ring

theorem xorClosed_layerD (E : Subgroup Dfull) : XorClosed (layerD E) := by
  constructor
  · simp only [layerD, Finset.mem_filter, Finset.mem_range, bvec_zero, ofAdd_zero]
    exact ⟨by norm_num, ⟨1, E.one_mem, map_one sCoord⟩⟩
  · intro a ha b hb
    simp only [layerD, Finset.mem_filter, Finset.mem_range] at ha hb ⊢
    obtain ⟨ha16, x, hxE, hx⟩ := ha
    obtain ⟨hb16, y, hyE, hy⟩ := hb
    refine ⟨Nat.xor_lt_two_pow ha16 hb16, ⟨x * y, E.mul_mem hxE hyE, ?_⟩⟩
    rw [map_mul, hx, hy, ← ofAdd_add, ← bvec_xor]

theorem xorClosed_layerW (E : Subgroup Dfull) : XorClosed (layerW E) := by
  constructor
  · simp only [layerW, Finset.mem_filter, Finset.mem_range, bvec_zero, ofAdd_zero]
    exact ⟨by norm_num, ⟨1, E.one_mem, map_one uCoord⟩⟩
  · intro a ha b hb
    simp only [layerW, Finset.mem_filter, Finset.mem_range] at ha hb ⊢
    obtain ⟨ha10, g, hgE, hg⟩ := ha
    obtain ⟨hb10, h, hhE, hh⟩ := hb
    refine ⟨Nat.xor_lt_two_pow ha10 hb10, ⟨g * h, E.mul_mem hgE hhE, ?_⟩⟩
    rw [map_mul, hg, hh, ← ofAdd_add, ← bvec_xor]

private theorem tVec_one_eq_zero : tVec (1 : Dfull) = 0 := by
  unfold tVec
  rw [dif_pos T9.one_mem]
  have h : (⟨(1 : Dfull), T9.one_mem⟩ : T9) = 1 := rfl
  rw [h, map_one, toAdd_one]

theorem qN_eq_zero_of_mem_layerD {E : Subgroup Dfull} (hE : IsElemAbelian 2 E) :
    ∀ x ∈ layerD E, MonsterB.P0Rank.qN p0Data.beta x = 0 := by
  intro σ hσ
  simp only [layerD, Finset.mem_filter, Finset.mem_range] at hσ
  obtain ⟨hσ16, x, hxE, hx⟩ := hσ
  have hsq : (x : Dfull) ^ 2 = 1 := hE.2 _ hxE
  have hmem : (x : Dfull) ^ 2 ∈ T9 := by rw [hsq]; exact T9.one_mem
  have hq : tVec ((x : Dfull) ^ 2) = lQuad (sCoord x).toAdd := tVec_sq x
  rw [hsq, tVec_one_eq_zero, hx, toAdd_ofAdd] at hq
  have hq0 : lQuad (bvec 16 σ) = 0 := hq.symm
  have hb : bvec 9 (MonsterB.P0Rank.qN p0Data.beta σ) = 0 := by
    rw [bvec_qN hσ16, hq0]
  have hz : bvec 9 (0 : ℕ) = 0 := bvec_zero 9
  rw [← hz] at hb
  exact bvec_inj (qN_lt σ) (by norm_num) hb

theorem betaN_eq_zero_of_mem_layerD {E : Subgroup Dfull} (hE : IsElemAbelian 2 E) :
    ∀ x ∈ layerD E, ∀ y ∈ layerD E, MonsterB.P0Rank.betaN p0Data.beta x y = 0 := by
  intro σ hσ δ hδ
  simp only [layerD, Finset.mem_filter, Finset.mem_range] at hσ hδ
  obtain ⟨hσ16, x, hxE, hx⟩ := hσ
  obtain ⟨hδ16, y, hyE, hy⟩ := hδ
  have hcomm : (x : Dfull) * (y : Dfull) = (y : Dfull) * (x : Dfull) :=
    congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hxE⟩ ⟨y, hyE⟩)
  have hc : ⁅(x : Dfull), (y : Dfull)⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.2 hcomm
  have hb : bvec 9 (MonsterB.P0Rank.betaN p0Data.beta σ δ) = 0 := by
    have h := tVec_commutator x y
    rw [hc, tVec_one_eq_zero, hx, hy, toAdd_ofAdd, toAdd_ofAdd] at h
    rw [bvec_betaN hσ16 hδ16]
    exact h.symm
  have hz : bvec 9 (0 : ℕ) = 0 := bvec_zero 9
  rw [← hz] at hb
  exact bvec_inj (betaN_lt σ δ) (by norm_num) hb

theorem actK_eq_of_mem_layerW {E : Subgroup Dfull} (hE : IsElemAbelian 2 E) :
    ∀ κ ∈ layerW E, ∀ x ∈ layerD E, actK p0Data.aCols κ x = x := by
  intro κ hκ σ hσ
  simp only [layerW, Finset.mem_filter, Finset.mem_range] at hκ
  simp only [layerD, Finset.mem_filter, Finset.mem_range] at hσ
  obtain ⟨hκ10, g, hgE, hg⟩ := hκ
  obtain ⟨hσ16, y, hyE, hy⟩ := hσ
  have hcomm : (g : Dfull) * (y : Dfull) = (y : Dfull) * (g : Dfull) :=
    congrArg Subtype.val (hE.1.is_comm.comm ⟨g, hgE⟩ ⟨y, hyE⟩)
  have hconj : (g : Dfull) * (y : Dfull) * (g : Dfull)⁻¹ = (y : Dfull) := by
    rw [hcomm]; group
  have hsy : sCoord ⟨(g : Dfull) * (y : Dfull) * (g : Dfull)⁻¹,
      conj_mem_Lgrp g.2 y.2⟩ = sCoord y :=
    congrArg sCoord (Subtype.ext hconj)
  rw [sCoord_conj, hg, hy, toAdd_ofAdd, toAdd_ofAdd] at hsy
  have hsy' : aAct (bvec 10 κ) (bvec 16 σ) = bvec 16 σ := Multiplicative.ofAdd.injective hsy
  have hb : bvec 16 (actK p0Data.aCols κ σ) = bvec 16 σ := by
    rw [bvec_actK_aCols κ hσ16]
    exact hsy'
  exact bvec_inj (actK_aCols_lt κ hσ16) hσ16 hb

theorem actK_eq_of_mem_layerY {E : Subgroup Dfull} (hE : IsElemAbelian 2 E) :
    ∀ τ ∈ layerY E, ∀ κ ∈ layerW E, actK p0Data.uConjT κ τ = τ := by
  intro τ hτ κ hκ
  simp only [layerY, Finset.mem_filter, Finset.mem_range] at hτ
  simp only [layerW, Finset.mem_filter, Finset.mem_range] at hκ
  obtain ⟨hτ9, htE⟩ := hτ
  obtain ⟨hκ10, g, hgE, hg⟩ := hκ
  have hcomm : (g : Dfull) * tD τ = tD τ * (g : Dfull) :=
    congrArg Subtype.val (hE.1.is_comm.comm ⟨g, hgE⟩ ⟨tD τ, htE⟩)
  have hconj : (g : Dfull) * tD τ * (g : Dfull)⁻¹ = tD τ := by
    rw [hcomm]; group
  have htv : tVec ((g : Dfull) * tD τ * (g : Dfull)⁻¹) = tVec (tD τ) :=
    congrArg tVec hconj
  rw [tVec_conj ⟨g, g.2⟩ (tD_mem_T9 τ), hg, tVec_tD, toAdd_ofAdd] at htv
  have hb : bvec 9 (actK p0Data.uConjT κ τ) = bvec 9 τ := by
    rw [bvec_actK_uConjT κ hτ9]
    exact htv
  exact bvec_inj (actK_uConjT_lt κ hτ9) hτ9 hb

theorem sq_coord_eq {E : Subgroup Dfull} (hE : IsElemAbelian 2 E)
    {g : P0} (hgE : (g : Dfull) ∈ E) {σ τ κ s t : ℕ} (hσ : σ < 2 ^ 16)
    (hs : s < 2 ^ 16) (hg : (g : Dfull) = lD σ * tD τ * uE κ)
    (hfact : uE κ * uE κ = lD s * tD t) :
    σ ^^^ actK p0Data.aCols κ σ = s := by
  let x : Lgrp := ⟨lD σ * tD τ,
    Lgrp.mul_mem (lD_mem_Lgrp σ) (T9_le_Lgrp (tD_mem_T9 τ))⟩
  let u : P0 := ⟨uE κ, uE_mem_P0 κ⟩
  have hxcoord : sCoord x = Multiplicative.ofAdd (bvec 16 σ) :=
    sCoord_lD_mul hσ (tD_mem_T9 τ) x.2
  have hucoord : uCoord u = Multiplicative.ofAdd (bvec 10 κ) := uCoord_uE κ
  have hu2L : uE κ * uE κ ∈ Lgrp := by
    rw [hfact]
    exact Lgrp.mul_mem (lD_mem_Lgrp s) (T9_le_Lgrp (tD_mem_T9 t))
  have hu2coord : sCoord ⟨uE κ * uE κ, hu2L⟩ = Multiplicative.ofAdd (bvec 16 s) := by
    have heq : (⟨uE κ * uE κ, hu2L⟩ : Lgrp) =
        ⟨lD s * tD t, Lgrp.mul_mem (lD_mem_Lgrp s) (T9_le_Lgrp (tD_mem_T9 t))⟩ :=
      Subtype.ext hfact
    rw [heq]
    exact sCoord_lD_mul hs (tD_mem_T9 t) _
  have hconj : sCoord ⟨(u : Dfull) * x * (u : Dfull)⁻¹, conj_mem_Lgrp u.2 x.2⟩ =
      Multiplicative.ofAdd (aAct (bvec 10 κ) (bvec 16 σ)) := by
    rw [sCoord_conj u x, hucoord, hxcoord, toAdd_ofAdd, toAdd_ofAdd]
  have hg2 : (g : Dfull) ^ 2 = 1 := hE.2 (g : Dfull) hgE
  have hg2L : (g : Dfull) ^ 2 ∈ Lgrp := by rw [hg2]; exact Lgrp.one_mem
  have hcoord : sCoord ⟨(g : Dfull) ^ 2, hg2L⟩ = 1 := by
    rw [show (⟨(g : Dfull) ^ 2, hg2L⟩ : Lgrp) = 1 from Subtype.ext hg2, map_one]
  have hmidL : (u : Dfull) * x * (u : Dfull)⁻¹ ∈ Lgrp := conj_mem_Lgrp u.2 x.2
  have hu2mem : uE κ * uE κ ∈ Lgrp := hu2L
  have hmem : (lD σ * tD τ) * ((u : Dfull) * x * (u : Dfull)⁻¹) * (uE κ * uE κ) ∈ Lgrp :=
    Lgrp.mul_mem (Lgrp.mul_mem x.2 hmidL) hu2mem
  have hdecomp : (g : Dfull) ^ 2 =
      (lD σ * tD τ) * ((u : Dfull) * x * (u : Dfull)⁻¹) * (uE κ * uE κ) := by
    have hxval : (x : Dfull) = lD σ * tD τ := rfl
    have huval : (u : Dfull) = uE κ := rfl
    rw [hg, pow_two, huval, hxval]
    group
  have hside : (⟨(g : Dfull) ^ 2, hg2L⟩ : Lgrp) =
      ⟨(lD σ * tD τ) * ((u : Dfull) * x * (u : Dfull)⁻¹) * (uE κ * uE κ), hmem⟩ :=
    Subtype.ext hdecomp
  have hsidecoord : sCoord
      ⟨(lD σ * tD τ) * ((u : Dfull) * x * (u : Dfull)⁻¹) * (uE κ * uE κ), hmem⟩ =
      Multiplicative.ofAdd (bvec 16 σ) *
        Multiplicative.ofAdd (aAct (bvec 10 κ) (bvec 16 σ)) *
        Multiplicative.ofAdd (bvec 16 s) := by
    rw [show (⟨(lD σ * tD τ) * ((u : Dfull) * x * (u : Dfull)⁻¹) * (uE κ * uE κ),
        hmem⟩ : Lgrp) = x * ⟨(u : Dfull) * x * (u : Dfull)⁻¹, hmidL⟩ *
        ⟨uE κ * uE κ, hu2L⟩ from Subtype.ext rfl, map_mul, map_mul, hxcoord, hconj, hu2coord]
  have hprod : Multiplicative.ofAdd (bvec 16 σ) *
      Multiplicative.ofAdd (aAct (bvec 10 κ) (bvec 16 σ)) *
      Multiplicative.ofAdd (bvec 16 s) = 1 := by
    rw [← hsidecoord, ← hside]
    exact hcoord
  have hadd : bvec 16 σ + aAct (bvec 10 κ) (bvec 16 σ) + bvec 16 s = 0 := by
    have := congrArg Multiplicative.toAdd hprod
    simpa [toAdd_mul, toAdd_one, toAdd_ofAdd] using this
  rw [← bvec_actK_aCols κ hσ] at hadd
  have hneg : bvec 16 s = -(bvec 16 σ + bvec 16 (actK p0Data.aCols κ σ)) := by
    rw [eq_neg_iff_add_eq_zero]
    calc bvec 16 s + (bvec 16 σ + bvec 16 (actK p0Data.aCols κ σ))
        = bvec 16 σ + bvec 16 (actK p0Data.aCols κ σ) + bvec 16 s := by abel
      _ = 0 := hadd
  have hchar : -(bvec 16 σ + bvec 16 (actK p0Data.aCols κ σ)) =
      bvec 16 σ + bvec 16 (actK p0Data.aCols κ σ) := by
    funext i
    exact CharTwo.neg_eq _
  rw [hchar] at hneg
  have hbvec : bvec 16 (σ ^^^ actK p0Data.aCols κ σ) = bvec 16 s := by
    rw [bvec_xor, hneg]
  exact bvec_inj (Nat.xor_lt_two_pow hσ (actK_aCols_lt κ hσ)) hs hbvec

theorem comm_coord_eq {E : Subgroup Dfull} (hE : IsElemAbelian 2 E)
    {g₁ g₂ : P0} (hg₁E : (g₁ : Dfull) ∈ E) (hg₂E : (g₂ : Dfull) ∈ E)
    {σ₁ τ₁ κ₁ σ₂ τ₂ κ₂ s t : ℕ} (hσ₁ : σ₁ < 2 ^ 16) (hσ₂ : σ₂ < 2 ^ 16)
    (hs : s < 2 ^ 16) (hg₁ : (g₁ : Dfull) = lD σ₁ * tD τ₁ * uE κ₁)
    (hg₂ : (g₂ : Dfull) = lD σ₂ * tD τ₂ * uE κ₂)
    (hfact : uE κ₁ * uE κ₂ = lD s * tD t * uE κ₂ * uE κ₁) :
    (σ₁ ^^^ actK p0Data.aCols κ₂ σ₁) ^^^ (σ₂ ^^^ actK p0Data.aCols κ₁ σ₂) = s := by
  let X₁ : Lgrp := ⟨lD σ₁ * tD τ₁,
    Lgrp.mul_mem (lD_mem_Lgrp σ₁) (T9_le_Lgrp (tD_mem_T9 τ₁))⟩
  let X₂ : Lgrp := ⟨lD σ₂ * tD τ₂,
    Lgrp.mul_mem (lD_mem_Lgrp σ₂) (T9_le_Lgrp (tD_mem_T9 τ₂))⟩
  let U₁ : P0 := ⟨uE κ₁, uE_mem_P0 κ₁⟩
  let U₂ : P0 := ⟨uE κ₂, uE_mem_P0 κ₂⟩
  have hX₁ : (X₁ : Dfull) = lD σ₁ * tD τ₁ := rfl
  have hX₂ : (X₂ : Dfull) = lD σ₂ * tD τ₂ := rfl
  have hU₁ : (U₁ : Dfull) = uE κ₁ := rfl
  have hU₂ : (U₂ : Dfull) = uE κ₂ := rfl
  have hx₁ : sCoord X₁ = Multiplicative.ofAdd (bvec 16 σ₁) :=
    sCoord_lD_mul hσ₁ (tD_mem_T9 τ₁) X₁.2
  have hx₂ : sCoord X₂ = Multiplicative.ofAdd (bvec 16 σ₂) :=
    sCoord_lD_mul hσ₂ (tD_mem_T9 τ₂) X₂.2
  have hu₁ : uCoord U₁ = Multiplicative.ofAdd (bvec 10 κ₁) := uCoord_uE κ₁
  have hu₂ : uCoord U₂ = Multiplicative.ofAdd (bvec 10 κ₂) := uCoord_uE κ₂
  have hmid₂L : (U₁ : Dfull) * X₂ * (U₁ : Dfull)⁻¹ ∈ Lgrp := conj_mem_Lgrp U₁.2 X₂.2
  have hmid₁L : (U₂ : Dfull) * X₁ * (U₂ : Dfull)⁻¹ ∈ Lgrp := conj_mem_Lgrp U₂.2 X₁.2
  have hLT : lD s * tD t ∈ Lgrp :=
    Lgrp.mul_mem (lD_mem_Lgrp s) (T9_le_Lgrp (tD_mem_T9 t))
  have hAL : (lD σ₁ * tD τ₁) * ((U₁ : Dfull) * X₂ * (U₁ : Dfull)⁻¹) * (lD s * tD t) ∈
      Lgrp := Lgrp.mul_mem (Lgrp.mul_mem X₁.2 hmid₂L) hLT
  have hBL : (lD σ₂ * tD τ₂) * ((U₂ : Dfull) * X₁ * (U₂ : Dfull)⁻¹) ∈ Lgrp :=
    Lgrp.mul_mem X₂.2 hmid₁L
  have hcomm : (g₁ : Dfull) * (g₂ : Dfull) = (g₂ : Dfull) * (g₁ : Dfull) :=
    congrArg Subtype.val (hE.1.is_comm.comm ⟨g₁, hg₁E⟩ ⟨g₂, hg₂E⟩)
  have hdecomp₁ : (g₁ : Dfull) * (g₂ : Dfull) =
      ((lD σ₁ * tD τ₁) * ((U₁ : Dfull) * X₂ * (U₁ : Dfull)⁻¹) * (lD s * tD t)) *
        ((U₂ : Dfull) * (U₁ : Dfull)) := by
    rw [hg₁, hg₂, hU₁, hU₂, hX₂]
    calc (lD σ₁ * tD τ₁ * uE κ₁) * (lD σ₂ * tD τ₂ * uE κ₂)
        = (lD σ₁ * tD τ₁) * (uE κ₁ * (lD σ₂ * tD τ₂) * (uE κ₁)⁻¹) *
            (uE κ₁ * uE κ₂) := by group
      _ = (lD σ₁ * tD τ₁) * (uE κ₁ * (lD σ₂ * tD τ₂) * (uE κ₁)⁻¹) *
            (lD s * tD t * uE κ₂ * uE κ₁) := by rw [hfact]
      _ = (lD σ₁ * tD τ₁) * (uE κ₁ * (lD σ₂ * tD τ₂) * (uE κ₁)⁻¹) *
            (lD s * tD t) * (uE κ₂ * uE κ₁) := by group
  have hdecomp₂ : (g₂ : Dfull) * (g₁ : Dfull) =
      ((lD σ₂ * tD τ₂) * ((U₂ : Dfull) * X₁ * (U₂ : Dfull)⁻¹)) *
        ((U₂ : Dfull) * (U₁ : Dfull)) := by
    rw [hg₂, hg₁, hU₁, hU₂, hX₁]
    group
  have hAB : (lD σ₁ * tD τ₁) * ((U₁ : Dfull) * X₂ * (U₁ : Dfull)⁻¹) * (lD s * tD t) =
      (lD σ₂ * tD τ₂) * ((U₂ : Dfull) * X₁ * (U₂ : Dfull)⁻¹) := by
    apply mul_right_cancel (b := ((U₂ : Dfull) * (U₁ : Dfull)))
    rw [← hdecomp₁, ← hdecomp₂]
    exact hcomm
  have hconj₁ : sCoord ⟨(U₁ : Dfull) * X₂ * (U₁ : Dfull)⁻¹, hmid₂L⟩ =
      Multiplicative.ofAdd (aAct (bvec 10 κ₁) (bvec 16 σ₂)) := by
    rw [sCoord_conj U₁ X₂, hu₁, hx₂, toAdd_ofAdd, toAdd_ofAdd]
  have hconj₂ : sCoord ⟨(U₂ : Dfull) * X₁ * (U₂ : Dfull)⁻¹, hmid₁L⟩ =
      Multiplicative.ofAdd (aAct (bvec 10 κ₂) (bvec 16 σ₁)) := by
    rw [sCoord_conj U₂ X₁, hu₂, hx₁, toAdd_ofAdd, toAdd_ofAdd]
  have hthird : sCoord ⟨lD s * tD t, hLT⟩ = Multiplicative.ofAdd (bvec 16 s) :=
    sCoord_lD_mul hs (tD_mem_T9 t) hLT
  have hcoordA : sCoord
      ⟨(lD σ₁ * tD τ₁) * ((U₁ : Dfull) * X₂ * (U₁ : Dfull)⁻¹) * (lD s * tD t), hAL⟩ =
      Multiplicative.ofAdd (bvec 16 σ₁) *
        Multiplicative.ofAdd (aAct (bvec 10 κ₁) (bvec 16 σ₂)) *
        Multiplicative.ofAdd (bvec 16 s) := by
    rw [show (⟨(lD σ₁ * tD τ₁) * ((U₁ : Dfull) * X₂ * (U₁ : Dfull)⁻¹) * (lD s * tD t),
        hAL⟩ : Lgrp) = X₁ * ⟨(U₁ : Dfull) * X₂ * (U₁ : Dfull)⁻¹, hmid₂L⟩ *
        ⟨lD s * tD t, hLT⟩ from Subtype.ext rfl, map_mul, map_mul, hx₁, hconj₁, hthird]
  have hcoordB : sCoord
      ⟨(lD σ₂ * tD τ₂) * ((U₂ : Dfull) * X₁ * (U₂ : Dfull)⁻¹), hBL⟩ =
      Multiplicative.ofAdd (bvec 16 σ₂) *
        Multiplicative.ofAdd (aAct (bvec 10 κ₂) (bvec 16 σ₁)) := by
    rw [show (⟨(lD σ₂ * tD τ₂) * ((U₂ : Dfull) * X₁ * (U₂ : Dfull)⁻¹),
        hBL⟩ : Lgrp) = X₂ * ⟨(U₂ : Dfull) * X₁ * (U₂ : Dfull)⁻¹, hmid₁L⟩ from Subtype.ext rfl,
      map_mul, hx₂, hconj₂]
  have hcoord : Multiplicative.ofAdd (bvec 16 σ₁) *
      Multiplicative.ofAdd (aAct (bvec 10 κ₁) (bvec 16 σ₂)) *
      Multiplicative.ofAdd (bvec 16 s) =
      Multiplicative.ofAdd (bvec 16 σ₂) *
        Multiplicative.ofAdd (aAct (bvec 10 κ₂) (bvec 16 σ₁)) := by
    rw [← hcoordA, ← hcoordB]
    exact congrArg sCoord (Subtype.ext hAB)
  have hadd : bvec 16 σ₁ + aAct (bvec 10 κ₁) (bvec 16 σ₂) + bvec 16 s =
      bvec 16 σ₂ + aAct (bvec 10 κ₂) (bvec 16 σ₁) := by
    have := congrArg Multiplicative.toAdd hcoord
    simpa [toAdd_mul, toAdd_ofAdd] using this
  rw [← bvec_actK_aCols κ₁ hσ₂, ← bvec_actK_aCols κ₂ hσ₁] at hadd
  have hsadd : bvec 16 s = bvec 16 σ₁ + bvec 16 (actK p0Data.aCols κ₂ σ₁) +
      bvec 16 σ₂ + bvec 16 (actK p0Data.aCols κ₁ σ₂) := by
    calc bvec 16 s = (bvec 16 σ₁ + bvec 16 (actK p0Data.aCols κ₁ σ₂) + bvec 16 s) +
          bvec 16 σ₁ + bvec 16 (actK p0Data.aCols κ₁ σ₂) := by
            abel_nf; simp [CharTwo.two_eq_zero]
      _ = (bvec 16 σ₂ + bvec 16 (actK p0Data.aCols κ₂ σ₁)) + bvec 16 σ₁ +
          bvec 16 (actK p0Data.aCols κ₁ σ₂) := by rw [hadd]
      _ = bvec 16 σ₁ + bvec 16 (actK p0Data.aCols κ₂ σ₁) + bvec 16 σ₂ +
          bvec 16 (actK p0Data.aCols κ₁ σ₂) := by abel
  have hbvec : bvec 16 ((σ₁ ^^^ actK p0Data.aCols κ₂ σ₁) ^^^
      (σ₂ ^^^ actK p0Data.aCols κ₁ σ₂)) = bvec 16 s := by
    simp only [bvec_xor]
    rw [hsadd]; abel
  exact bvec_inj (Nat.xor_lt_two_pow (Nat.xor_lt_two_pow hσ₁ (actK_aCols_lt κ₂ hσ₁))
    (Nat.xor_lt_two_pow hσ₂ (actK_aCols_lt κ₁ hσ₂))) hs hbvec

theorem conj_coord_eq {E : Subgroup Dfull} (hE : IsElemAbelian 2 E)
    {g : P0} (hgE : (g : Dfull) ∈ E) {x : Lgrp} (hxE : (x : Dfull) ∈ E)
    {σ τ κ δ ν c : ℕ} (hσ : σ < 2 ^ 16) (hδ : δ < 2 ^ 16) (hν : ν < 2 ^ 9)
    (hg : (g : Dfull) = lD σ * tD τ * uE κ) (hx : (x : Dfull) = lD δ * tD ν)
    (hfact : uE κ * lD δ = lD δ * tD c * uE κ) (hc : c < 2 ^ 9) :
    betaN p0Data.beta σ δ ^^^ (ν ^^^ actK p0Data.uConjT κ ν) = c := by
  let X : Lgrp := ⟨lD σ * tD τ,
    Lgrp.mul_mem (lD_mem_Lgrp σ) (T9_le_Lgrp (tD_mem_T9 τ))⟩
  let U : P0 := ⟨uE κ, uE_mem_P0 κ⟩
  let Y : Lgrp := ⟨lD δ, lD_mem_Lgrp δ⟩
  let Z : Dfull := (U : Dfull) * tD ν * (U : Dfull)⁻¹
  have hX : (X : Dfull) = lD σ * tD τ := rfl
  have hU : (U : Dfull) = uE κ := rfl
  have hY : (Y : Dfull) = lD δ := rfl
  have hZdef : Z = (U : Dfull) * tD ν * (U : Dfull)⁻¹ := rfl
  have hxcoord : sCoord X = Multiplicative.ofAdd (bvec 16 σ) :=
    sCoord_lD_mul hσ (tD_mem_T9 τ) X.2
  have hycoord : sCoord Y = Multiplicative.ofAdd (bvec 16 δ) := by
    have hmem : lD δ * (1 : Dfull) ∈ Lgrp := by
      rw [mul_one]
      exact lD_mem_Lgrp δ
    have h : sCoord (⟨lD δ * 1, hmem⟩ : Lgrp) = Multiplicative.ofAdd (bvec 16 δ) :=
      sCoord_lD_mul hδ T9.one_mem hmem
    rw [show (⟨lD δ * 1, hmem⟩ : Lgrp) = Y from Subtype.ext (mul_one _)] at h
    exact h
  have hucoord : uCoord U = Multiplicative.ofAdd (bvec 10 κ) := uCoord_uE κ
  have hZ_T9 : Z ∈ T9 := conj_mem_T9 U.2 (tD_mem_T9 ν)
  have hbar_T9 : ⁅(X : Dfull), (Y : Dfull)⁆ ∈ T9 := commutator_mem_T9 X Y
  have hW_T9 : tD c * Z ∈ T9 := T9.mul_mem (tD_mem_T9 c) hZ_T9
  have hYZ : (Y : Dfull) * (tD c * Z) = (tD c * Z) * (Y : Dfull) :=
    (Subgroup.mem_centralizer_iff.1 (Lgrp_le_centralizer_T9 Y.2) (tD c * Z) hW_T9).symm
  have hXZ : (X : Dfull) * (tD c * Z) = (tD c * Z) * (X : Dfull) :=
    (Subgroup.mem_centralizer_iff.1 (Lgrp_le_centralizer_T9 X.2) (tD c * Z) hW_T9).symm
  have hcomm : (g : Dfull) * (x : Dfull) * (g : Dfull)⁻¹ = (x : Dfull) := by
    have hc' : (g : Dfull) * (x : Dfull) = (x : Dfull) * (g : Dfull) :=
      congrArg Subtype.val (hE.1.is_comm.comm ⟨g, hgE⟩ ⟨x, hxE⟩)
    rw [hc']; group
  have hfactu : (U : Dfull) * (Y : Dfull) * (U : Dfull)⁻¹ = (Y : Dfull) * tD c := by
    rw [hU, hY, hfact]; group
  have hUx : (U : Dfull) * (x : Dfull) * (U : Dfull)⁻¹ = ((Y : Dfull) * tD c) * Z := by
    rw [hx]
    calc (U : Dfull) * (lD δ * tD ν) * (U : Dfull)⁻¹
        = ((U : Dfull) * lD δ * (U : Dfull)⁻¹) * Z := by
          rw [hZdef]; group
      _ = ((Y : Dfull) * tD c) * Z := by rw [hfactu]
  have hWcomm_inv : (tD c * Z) * (X : Dfull)⁻¹ = (X : Dfull)⁻¹ * (tD c * Z) := by
    calc (tD c * Z) * (X : Dfull)⁻¹
        = (X : Dfull)⁻¹ * ((X : Dfull) * (tD c * Z)) * (X : Dfull)⁻¹ := by group
      _ = (X : Dfull)⁻¹ * ((tD c * Z) * (X : Dfull)) * (X : Dfull)⁻¹ := by rw [hXZ]
      _ = (X : Dfull)⁻¹ * (tD c * Z) := by group
  have hconjY : (X : Dfull) * (Y : Dfull) * (X : Dfull)⁻¹ =
      ⁅(X : Dfull), (Y : Dfull)⁆ * (Y : Dfull) := by
    simpa using (conj_eq_commutatorElement_mul (g₁ := (X : Dfull)) (g₂ := (Y : Dfull)))
  have hbarY : ⁅(X : Dfull), (Y : Dfull)⁆ * (Y : Dfull) =
      (Y : Dfull) * ⁅(X : Dfull), (Y : Dfull)⁆ :=
    Subgroup.mem_centralizer_iff.1 (Lgrp_le_centralizer_T9 Y.2) _ hbar_T9
  have hfinal : (X : Dfull) * (((Y : Dfull) * tD c) * Z) * (X : Dfull)⁻¹ =
      (Y : Dfull) * (⁅(X : Dfull), (Y : Dfull)⁆ * tD c * Z) := by
    calc (X : Dfull) * (((Y : Dfull) * tD c) * Z) * (X : Dfull)⁻¹
        = (X : Dfull) * (Y : Dfull) * (tD c * Z) * (X : Dfull)⁻¹ := by group
      _ = (X : Dfull) * (Y : Dfull) * ((tD c * Z) * (X : Dfull)⁻¹) := by group
      _ = (X : Dfull) * (Y : Dfull) * ((X : Dfull)⁻¹ * (tD c * Z)) := by rw [hWcomm_inv]
      _ = (X : Dfull) * (Y : Dfull) * (X : Dfull)⁻¹ * (tD c * Z) := by group
      _ = (⁅(X : Dfull), (Y : Dfull)⁆ * (Y : Dfull)) * (tD c * Z) := by rw [hconjY]
      _ = (Y : Dfull) * (⁅(X : Dfull), (Y : Dfull)⁆ * tD c * Z) := by rw [hbarY]; group
  have hmain : (g : Dfull) * (x : Dfull) * (g : Dfull)⁻¹ =
      (Y : Dfull) * (⁅(X : Dfull), (Y : Dfull)⁆ * tD c * Z) := by
    calc (g : Dfull) * (x : Dfull) * (g : Dfull)⁻¹
        = (X : Dfull) * ((U : Dfull) * (x : Dfull) * (U : Dfull)⁻¹) * (X : Dfull)⁻¹ := by
          rw [hg, hX, hU]; group
      _ = (X : Dfull) * (((Y : Dfull) * tD c) * Z) * (X : Dfull)⁻¹ := by rw [hUx]
      _ = (Y : Dfull) * (⁅(X : Dfull), (Y : Dfull)⁆ * tD c * Z) := hfinal
  have hTm : ⁅(X : Dfull), (Y : Dfull)⁆ * tD c * Z = tD ν := by
    have h : (x : Dfull) = (Y : Dfull) * (⁅(X : Dfull), (Y : Dfull)⁆ * tD c * Z) :=
      hcomm.symm.trans hmain
    rw [hx] at h
    exact (mul_left_cancel h).symm
  have hZtv : tVec Z = bAct (bvec 10 κ) (bvec 9 ν) := by
    have h := tVec_conj U (tD_mem_T9 ν)
    rw [hucoord, toAdd_ofAdd, tVec_tD] at h
    exact h
  have htv : tVec (⁅(X : Dfull), (Y : Dfull)⁆ * tD c * Z) = tVec (tD ν) :=
    congrArg tVec hTm
  rw [tVec_mul (T9.mul_mem hbar_T9 (tD_mem_T9 c)) hZ_T9,
    tVec_mul hbar_T9 (tD_mem_T9 c), tVec_commutator X Y, hxcoord, hycoord,
    toAdd_ofAdd, toAdd_ofAdd, ← bvec_betaN hσ hδ, tVec_tD, hZtv,
    ← bvec_actK_uConjT κ hν, tVec_tD] at htv
  have hcvec : bvec 9 c = bvec 9 (betaN p0Data.beta σ δ) + bvec 9 ν +
      bvec 9 (actK p0Data.uConjT κ ν) := by
    calc bvec 9 c = (bvec 9 (betaN p0Data.beta σ δ) + bvec 9 c +
          bvec 9 (actK p0Data.uConjT κ ν)) + bvec 9 (betaN p0Data.beta σ δ) +
          bvec 9 (actK p0Data.uConjT κ ν) := by abel_nf; simp [CharTwo.two_eq_zero]
      _ = bvec 9 ν + bvec 9 (betaN p0Data.beta σ δ) +
          bvec 9 (actK p0Data.uConjT κ ν) := by rw [htv]
      _ = bvec 9 (betaN p0Data.beta σ δ) + bvec 9 ν +
          bvec 9 (actK p0Data.uConjT κ ν) := by abel
  have hbvec : bvec 9 (betaN p0Data.beta σ δ ^^^
      (ν ^^^ actK p0Data.uConjT κ ν)) = bvec 9 c := by
    simp only [bvec_xor]
    rw [hcvec]; abel
  exact bvec_inj (Nat.xor_lt_two_pow (betaN_lt σ δ)
    (Nat.xor_lt_two_pow hν (actK_uConjT_lt κ hν))) hc hbvec

private theorem uCoord_lD_mul_tD (σ τ : ℕ) :
    uCoord ⟨lD σ * tD τ, Lgrp_le_P0 (Lgrp.mul_mem (lD_mem_Lgrp σ) (T9_le_Lgrp (tD_mem_T9 τ)))⟩ =
      1 := by
  rw [uCoord_eq_one_iff]
  exact Lgrp.mul_mem (lD_mem_Lgrp σ) (T9_le_Lgrp (tD_mem_T9 τ))

theorem layer_liftSol {E : Subgroup Dfull} (hE : IsElemAbelian 2 E) {F : List Fact}
    (hF : factsCheck F = true) (ds ks : List ℕ) (hds : ∀ δ ∈ ds, δ ∈ layerD E)
    (hks : ∀ κ ∈ ks, κ ∈ layerW E) : ∃ X, LiftSol p0Data F ds ks X := by
  classical
  have hgetW : ∀ j (hj : j < ks.length), ks.getD j 0 ∈ ks := by
    intro j hj
    rw [List.getD_eq_getElem ks 0 hj]
    exact List.getElem_mem hj
  have hgetD : ∀ i (hi : i < ds.length), ds.getD i 0 ∈ ds := by
    intro i hi
    rw [List.getD_eq_getElem ds 0 hi]
    exact List.getElem_mem hi
  have hks_bound : ∀ j (hj : j < ks.length), ks.getD j 0 < 2 ^ 10 := by
    intro j hj
    exact Finset.mem_range.1 (Finset.mem_filter.1 (hks _ (hgetW j hj))).1
  have hds_bound : ∀ i (hi : i < ds.length), ds.getD i 0 < 2 ^ 16 := by
    intro i hi
    exact Finset.mem_range.1 (Finset.mem_filter.1 (hds _ (hgetD i hi))).1
  let g : ℕ → P0 := fun j =>
    if h : j < ks.length then
      Classical.choose ((Finset.mem_filter.1 (hks (ks.getD j 0) (hgetW j h))).2)
    else 1
  have hgE : ∀ j (hj : j < ks.length), (g j : Dfull) ∈ E := by
    intro j hj
    dsimp [g]
    rw [dif_pos hj]
    exact (Classical.choose_spec ((Finset.mem_filter.1 (hks (ks.getD j 0) (hgetW j hj))).2)).1
  have hgcoord : ∀ j (hj : j < ks.length),
      uCoord (g j) = Multiplicative.ofAdd (bvec 10 (ks.getD j 0)) := by
    intro j hj
    dsimp [g]
    rw [dif_pos hj]
    exact (Classical.choose_spec ((Finset.mem_filter.1 (hks (ks.getD j 0) (hgetW j hj))).2)).2
  have hexNF : ∀ j, ∃ p : ℕ × ℕ × ℕ, p.1 < 2 ^ 16 ∧ p.2.1 < 2 ^ 9 ∧ p.2.2 < 2 ^ 10 ∧
      (g j : Dfull) = lD p.1 * tD p.2.1 * uE p.2.2 := by
    intro j
    obtain ⟨σ, hσ, τ, hτ, κ, hκ, heq⟩ := exists_nf (g j).2
    exact ⟨(σ, τ, κ), hσ, hτ, hκ, heq⟩
  let p : ℕ → ℕ × ℕ × ℕ := fun j => Classical.choose (hexNF j)
  have hp : ∀ j, (p j).1 < 2 ^ 16 ∧ (p j).2.1 < 2 ^ 9 ∧ (p j).2.2 < 2 ^ 10 ∧
      (g j : Dfull) = lD (p j).1 * tD (p j).2.1 * uE (p j).2.2 :=
    fun j => Classical.choose_spec (hexNF j)
  have hκ_eq : ∀ j (hj : j < ks.length), (p j).2.2 = ks.getD j 0 := by
    intro j hj
    have hcoord := hgcoord j hj
    have hP0L : lD (p j).1 * tD (p j).2.1 ∈ Lgrp :=
      Lgrp.mul_mem (lD_mem_Lgrp (p j).1) (T9_le_Lgrp (tD_mem_T9 (p j).2.1))
    have hP : g j = (⟨lD (p j).1 * tD (p j).2.1, Lgrp_le_P0 hP0L⟩ : P0) *
        ⟨uE (p j).2.2, uE_mem_P0 (p j).2.2⟩ :=
      Subtype.ext (by rw [Subgroup.coe_mul]; exact (hp j).2.2.2)
    rw [hP, map_mul, uCoord_lD_mul_tD, uCoord_uE, one_mul] at hcoord
    have hb : bvec 10 (p j).2.2 = bvec 10 (ks.getD j 0) :=
      Multiplicative.ofAdd.injective hcoord
    exact bvec_inj (hp j).2.2.1 (hks_bound j hj) hb
  let y : ℕ → Lgrp := fun i =>
    if h : i < ds.length then
      Classical.choose ((Finset.mem_filter.1 (hds (ds.getD i 0) (hgetD i h))).2)
    else 1
  have hyE : ∀ i (hi : i < ds.length), (y i : Dfull) ∈ E := by
    intro i hi
    dsimp [y]
    rw [dif_pos hi]
    exact (Classical.choose_spec ((Finset.mem_filter.1 (hds (ds.getD i 0) (hgetD i hi))).2)).1
  have hysCoord : ∀ i (hi : i < ds.length),
      sCoord (y i) = Multiplicative.ofAdd (bvec 16 (ds.getD i 0)) := by
    intro i hi
    dsimp [y]
    rw [dif_pos hi]
    exact (Classical.choose_spec ((Finset.mem_filter.1 (hds (ds.getD i 0) (hgetD i hi))).2)).2
  have hexNFx : ∀ i, ∃ q : ℕ × ℕ, q.1 < 2 ^ 16 ∧ q.2 < 2 ^ 9 ∧
      (y i : Dfull) = lD q.1 * tD q.2 := by
    intro i
    obtain ⟨σ, hσ, τ, hτ, heq⟩ := exists_lD_mul_tD (y i).2
    exact ⟨(σ, τ), hσ, hτ, heq⟩
  let q : ℕ → ℕ × ℕ := fun i => Classical.choose (hexNFx i)
  have hq : ∀ i, (q i).1 < 2 ^ 16 ∧ (q i).2 < 2 ^ 9 ∧
      (y i : Dfull) = lD (q i).1 * tD (q i).2 :=
    fun i => Classical.choose_spec (hexNFx i)
  have hδ_eq : ∀ i (hi : i < ds.length), (q i).1 = ds.getD i 0 := by
    intro i hi
    have hcoord := hysCoord i hi
    have hmemL : lD (q i).1 * tD (q i).2 ∈ Lgrp :=
      Lgrp.mul_mem (lD_mem_Lgrp (q i).1) (T9_le_Lgrp (tD_mem_T9 (q i).2))
    have hP : y i = (⟨lD (q i).1 * tD (q i).2, hmemL⟩ : Lgrp) :=
      Subtype.ext (hq i).2.2
    rw [hP, sCoord_lD_mul (hq i).1 (tD_mem_T9 (q i).2) hmemL] at hcoord
    have hb : bvec 16 (q i).1 = bvec 16 (ds.getD i 0) :=
      Multiplicative.ofAdd.injective hcoord
    exact bvec_inj (hq i).1 (hds_bound i hi) hb
  let X : ℕ → ℕ := fun n =>
    if h : n < ks.length then (p n).1
    else if h' : n - ks.length < ds.length then (q (n - ks.length)).2 else 0
  have hX1 : ∀ j (hj : j < ks.length), X j = (p j).1 := by
    intro j hj
    dsimp [X]
    rw [if_pos hj]
  have hX2 : ∀ i (hi : i < ds.length), X (ks.length + i) = (q i).2 := by
    intro i hi
    dsimp [X]
    rw [if_neg (by omega), if_pos (by simpa [Nat.add_sub_cancel_left] using hi),
      Nat.add_sub_cancel_left]
  refine ⟨X, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    rw [hX1 j hj]
    exact (hp j).1
  · intro i hi
    rw [hX2 i hi]
    exact (hq i).2.1
  · intro j hj s hs
    rw [hX1 j hj, ← hκ_eq j hj]
    obtain ⟨t, htF⟩ := findSq_spec hs
    obtain ⟨hbounds, hfact⟩ := holds_of_factsCheck hF htF
    have hsb : s < 2 ^ 16 := by
      have := hbounds
      simp only [factBounds, Bool.and_eq_true, decide_eq_true_eq] at this
      exact this.1.2
    have hfact' : uE (p j).2.2 * uE (p j).2.2 = lD s * tD t := by
      rw [hκ_eq j hj]
      exact hfact
    exact sq_coord_eq hE (hgE j hj) (hp j).1 hsb (hp j).2.2.2 hfact'
  · intro j k hjk hk s hs
    rw [hX1 j (by omega), hX1 k hk, ← hκ_eq k hk, ← hκ_eq j (by omega)]
    obtain ⟨t, htF⟩ := findComm_spec hs
    obtain ⟨hbounds, hfact⟩ := holds_of_factsCheck hF htF
    have hsb : s < 2 ^ 16 := by
      have hb := hbounds
      simp only [factBounds, Bool.and_eq_true, decide_eq_true_eq] at hb
      omega
    have hfact' : uE (p j).2.2 * uE (p k).2.2 =
        lD s * tD t * uE (p k).2.2 * uE (p j).2.2 := by
      rw [hκ_eq j (by omega), hκ_eq k hk]
      exact hfact
    exact comm_coord_eq hE (hgE j (by omega)) (hgE k hk) (hp j).1 (hp k).1 hsb
      (hp j).2.2.2 (hp k).2.2.2 hfact'
  · intro i hi j hj c hc
    rw [hX1 j hj, hX2 i hi, ← hκ_eq j hj, ← hδ_eq i hi]
    obtain ⟨hbounds, hfact⟩ := holds_of_factsCheck hF (findConj_spec hc)
    have hcb : c < 2 ^ 9 := by
      have hb := hbounds
      simp only [factBounds, Bool.and_eq_true, decide_eq_true_eq] at hb
      omega
    have hfact' : uE (p j).2.2 * lD (q i).1 =
        lD (q i).1 * tD c * uE (p j).2.2 := by
      rw [hκ_eq j hj, hδ_eq i hi]
      exact hfact
    exact conj_coord_eq hE (hgE j hj) (hyE i hi) (hp j).1 (hq i).1 (hq i).2.1
      (hp j).2.2.2 (hq i).2.2 hfact' hcb

private theorem actK_uConjT_one (κ : ℕ) : actK p0Data.uConjT κ 1 = 1 := by
  have hrow : ∀ cs ∈ p0Data.uConjT, colsAct cs 1 = 1 := by
    decide +kernel
  have hfold : ∀ (l : List ℕ) (x : ℕ),
      (∀ k ∈ l, colsAct (p0Data.uConjT.getD k []) x = x) →
      l.foldr (fun k y =>
        if κ.testBit k then colsAct (p0Data.uConjT.getD k []) y else y) x = x := by
    intro l x hx
    induction l with
    | nil => rfl
    | cons a l ih =>
        rw [List.foldr_cons]
        by_cases hbit : κ.testBit a
        · rw [if_pos hbit, ih (fun k hk => hx k (by simp [hk]))]
          exact hx a (by simp)
        · rw [if_neg hbit]
          exact ih (fun k hk => hx k (by simp [hk]))
  rw [actK]
  exact hfold (List.range p0Data.uConjT.length) 1 (fun k hk => by
    have hklt : k < p0Data.uConjT.length := List.mem_range.1 hk
    rw [List.getD_eq_getElem p0Data.uConjT [] hklt]
    exact hrow _ (List.getElem_mem hklt))

theorem P0_le_Jhat : PLam lam0 ≤ Jhat := by
  rw [← centralizer_xhat]
  intro g hg
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  have hxhat : xhat = tD 1 := by
    symm
    simpa [tT] using tD_two_pow (0 : Fin 9)
  obtain ⟨σ, hσ, τ, hτ, κ, hκ, hg_eq⟩ := exists_nf hg
  let A : Dfull := lD σ * tD τ
  let U : P0 := ⟨uE κ, uE_mem_P0 κ⟩
  have hAL : A ∈ Lgrp := Lgrp.mul_mem (lD_mem_Lgrp σ) (T9_le_Lgrp (tD_mem_T9 τ))
  have hU : (U : Dfull) = uE κ := rfl
  have hAeq : A = lD σ * tD τ := rfl
  have hUconjT9 : (U : Dfull) * tD 1 * (U : Dfull)⁻¹ ∈ T9 :=
    conj_mem_T9 U.2 (tD_mem_T9 1)
  have hUt : tVec ((U : Dfull) * tD 1 * (U : Dfull)⁻¹) = tVec (tD 1) := by
    rw [tVec_conj U (tD_mem_T9 1), uCoord_uE, toAdd_ofAdd, tVec_tD,
      ← bvec_actK_uConjT κ (by norm_num : 1 < 2 ^ 9), actK_uConjT_one]
  have hUconj : (U : Dfull) * tD 1 * (U : Dfull)⁻¹ = tD 1 :=
    eq_of_tVec_eq hUconjT9 (tD_mem_T9 1) hUt
  have hAconj : A * tD 1 * A⁻¹ = tD 1 := by
    have hcomm := Subgroup.mem_centralizer_iff.1 (Lgrp_le_centralizer_T9 hAL) (tD 1)
      (tD_mem_T9 1)
    rw [← hcomm]
    group
  have hg_eq' : g = A * (U : Dfull) := by
    rw [hg_eq, hAeq, hU]
  have hconj : g * xhat * g⁻¹ = xhat := by
    rw [hxhat, hg_eq']
    calc A * (U : Dfull) * tD 1 * (A * (U : Dfull))⁻¹
        = A * ((U : Dfull) * tD 1 * (U : Dfull)⁻¹) * A⁻¹ := by group
      _ = A * tD 1 * A⁻¹ := by rw [hUconj]
      _ = tD 1 := hAconj
  have hcomm : g * xhat = xhat * g := mul_inv_eq_iff_eq_mul.1 hconj
  exact hcomm.symm

end CFSG.Monster.B.TwoA.Sp8.WordRel
