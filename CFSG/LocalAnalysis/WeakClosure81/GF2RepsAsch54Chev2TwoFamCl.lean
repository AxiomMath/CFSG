module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Chev2TwoDefs
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Chev2TwoOrder
public import CFSG.Timmesfeld.RankTwo.SimplyLaced

import CFSG.LieType.Universal.Unitary.RootGroupCardRankTwo
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbFamSU
import CFSG.ClassicalInvolution.WeakCT.TwistedSpinModel
import CFSG.RankThree.PartOne.CTP.SpinMinusEven
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.ShortRoot
import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCRecognition
import CFSG.Timmesfeld.ARS.LinearLevis
import CFSG.Timmesfeld.RankTwo.LevisSpin

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Chev2Orbit

open CFSG.Open CFSG.ComponentClassification.CatLeaf CFSG.Quasithin CFSG.LieType.Universal
  CFSG.LieType.CurtisTits CFSG.LieType.Steinberg
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (HasCompFactor)

theorem exists_sl3_range_of_simplyLacedLevis {K : Type} [Group K]
    {D : CFSG.LieType.Universal.UniversalRootDatum K} {F : Type} [Field F]
    {adj : Fin D.rank → Fin D.rank → Prop} {x : (Fin D.rank → ℤ) → F → K}
    (hL : CFSG.Timmesfeld.SimplyLacedLevis D F adj x) {u v : Fin D.rank} (huv : adj u v) :
    ∃ l : Matrix.SpecialLinearGroup (Fin 3) F →* K, Function.Injective l ∧
      l.range = CFSG.LieType.CurtisTits.rankOne D.rootGroup u ⊔
        CFSG.LieType.CurtisTits.rankOne D.rootGroup v := by
  obtain ⟨l, hl, hlt⟩ := hL.sl3 u v huv
  have hroot : ∀ k : Fin D.rank, (Pi.single k 1 : Fin D.rank → ℤ) ∈ D.roots ∧
      (-Pi.single k 1 : Fin D.rank → ℤ) ∈ D.roots := fun k =>
    ⟨(CFSG.LieType.Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible).single_mem k,
      (CFSG.LieType.Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible).neg_mem _
        ((CFSG.LieType.Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible).single_mem k)⟩
  have hX1 : D.rootGroup (Pi.single u 1) ≤ l.range := fun g hg => by
    obtain ⟨c, rfl⟩ := hL.surj _ (hroot u).1 g hg
    exact MonoidHom.mem_range.mpr ⟨CFSG.Timmesfeld.tv 0 1 c, (hlt c).1⟩
  have hX2 : D.rootGroup (-Pi.single u 1) ≤ l.range := fun g hg => by
    obtain ⟨c, rfl⟩ := hL.surj _ (hroot u).2 g hg
    exact MonoidHom.mem_range.mpr ⟨CFSG.Timmesfeld.tv 1 0 c, (hlt c).2.1⟩
  have hX3 : D.rootGroup (Pi.single v 1) ≤ l.range := fun g hg => by
    obtain ⟨c, rfl⟩ := hL.surj _ (hroot v).1 g hg
    exact MonoidHom.mem_range.mpr ⟨CFSG.Timmesfeld.tv 1 2 c, (hlt c).2.2.1⟩
  have hX4 : D.rootGroup (-Pi.single v 1) ≤ l.range := fun g hg => by
    obtain ⟨c, rfl⟩ := hL.surj _ (hroot v).2 g hg
    exact MonoidHom.mem_range.mpr ⟨CFSG.Timmesfeld.tv 2 1 c, (hlt c).2.2.2.1⟩
  have hle : l.range ≤ CFSG.LieType.CurtisTits.rankOne D.rootGroup u ⊔
      CFSG.LieType.CurtisTits.rankOne D.rootGroup v := by
    intro z hz
    obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp hz
    exact CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.Exceptional.range_le_of_sl3
      hL huv hlt g
  have hge : CFSG.LieType.CurtisTits.rankOne D.rootGroup u ⊔
      CFSG.LieType.CurtisTits.rankOne D.rootGroup v ≤ l.range :=
    sup_le (sup_le hX1 hX2) (sup_le hX3 hX4)
  exact ⟨l, hl, le_antisymm hle hge⟩


theorem smallEdge_comm {K : Type} [Group K] {D : UniversalRootDatum K} {u v : Fin D.rank}
    (h : SmallEdge D u v) : SmallEdge D v u := by
  unfold SmallEdge at h ⊢
  rcases h with h | h | h
  · refine Or.inl ?_
    rwa [sup_comm]
  · exact Or.inr (Or.inl h.symm)
  · exact Or.inr (Or.inr h.symm)

theorem not_hasCompFactor_of_sl2_range {K : Type} [Group K] [Finite K]
    {D : UniversalRootDatum K} {F : Type} [Field F] [Finite F]
    (hO : LieOrderFormulasInput) (hF : Nat.card F ≤ 4) {i : Fin D.rank}
    (l : Matrix.SpecialLinearGroup (Fin 2) F →* K)
    (hr : rankOne D.rootGroup i = l.range) :
    ¬ HasCompFactor (rankOne D.rootGroup i) IsCalL0 := by
  rw [hr]
  exact not_hasCompFactor_isCalL0_range_SL2 hO hF l

theorem not_hasCompFactor_of_mulEquiv_sl2 {K : Type} [Group K] [Finite K]
    {L : Subgroup K} {F : Type} [Field F] [Finite F]
    (hO : LieOrderFormulasInput) (hF : Nat.card F ≤ 4)
    (e : L ≃* Matrix.SpecialLinearGroup (Fin 2) F) :
    ¬ HasCompFactor L IsCalL0 := by
  let l : Matrix.SpecialLinearGroup (Fin 2) F →* K :=
    (Subgroup.subtype L).comp e.symm.toMonoidHom
  have hr : l.range = L := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨y, rfl⟩
      exact (e.symm y).2
    · intro x hx
      exact ⟨e ⟨x, hx⟩, by simp [l]⟩
  rw [← hr]
  exact not_hasCompFactor_isCalL0_range_SL2 hO hF l

theorem not_hasCompFactor_of_sl3_range {K : Type} [Group K] [Finite K]
    {D : UniversalRootDatum K} {F : Type} [Field F] [Finite F]
    (hO : LieOrderFormulasInput) (hF : Nat.card F = 2 ∨ Nat.card F = 4) {u v : Fin D.rank}
    (l : Matrix.SpecialLinearGroup (Fin 3) F →* K)
    (hr : l.range = rankOne D.rootGroup u ⊔ rankOne D.rootGroup v) :
    ¬ HasCompFactor (rankOne D.rootGroup u ⊔ rankOne D.rootGroup v) IsCalL0 := by
  rw [← hr]
  exact not_hasCompFactor_isCalL0_range_SL3 hO hF l

theorem not_hasCompFactor_edge_of_simplyLacedLevis {K : Type} [Group K] [Finite K]
    {D : UniversalRootDatum K} {F : Type} [Field F] [Finite F]
    {adj : Fin D.rank → Fin D.rank → Prop} {x : (Fin D.rank → ℤ) → F → K}
    (hO : LieOrderFormulasInput) (hF : Nat.card F = 2 ∨ Nat.card F = 4)
    (hL : CFSG.Timmesfeld.SimplyLacedLevis D F adj x) {u v : Fin D.rank} (huv : adj u v) :
    ¬ HasCompFactor (rankOne D.rootGroup u ⊔ rankOne D.rootGroup v) IsCalL0 := by
  obtain ⟨l, -, hr⟩ := exists_sl3_range_of_simplyLacedLevis hL huv
  exact not_hasCompFactor_of_sl3_range hO hF l hr

private theorem bqSmall_sl {m : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    (hO : LieOrderFormulasInput) (hF : Nat.card F = 2 ∨ Nat.card F = 4) :
    BQSmall (CFSG.LieType.Universal.SpecialLinear.rootDatum m F) := by
  have h4 : Nat.card F ≤ 4 := by rcases hF with h | h <;> omega
  constructor
  · intro i
    obtain ⟨φ, -, hx, hy⟩ := SL.rankOne (F := F) i
    exact not_hasCompFactor_of_sl2_range hO h4 φ
      (CFSG.AGLEmbedding.ParabPrime.rankOne_eq_range_of_sl2 SL.isParametrization hx hy)
  · intro _hrank u v hadj
    have hpath : (SimpleGraph.pathGraph m).Adj u v := by
      have h : (TauCeti.diagramGraph (CartanMatrix.A m)).Adj u v := by
        simpa only [CFSG.LieType.Universal.SpecialLinear.rootDatum] using hadj
      rwa [TauCeti.DynkinType.diagramGraph_cartanMatrix_A] at h
    rcases SimpleGraph.pathGraph_adj.1 hpath with h | h
    · exact Or.inl (not_hasCompFactor_edge_of_simplyLacedLevis hO hF
        (CFSG.Timmesfeld.ARS.simplyLacedLevis_specialLinear m F) h.symm)
    · refine Or.inl ?_
      rw [sup_comm]
      exact not_hasCompFactor_edge_of_simplyLacedLevis hO hF
        (CFSG.Timmesfeld.ARS.simplyLacedLevis_specialLinear m F) h.symm

section SmallSp

open CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.LieType.Universal.Symplectic

private theorem bqSmall_sp {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    (hO : LieOrderFormulasInput) (hF : Nat.card F = 2 ∨ Nat.card F = 4) :
    BQSmall (CFSG.LieType.Universal.Symplectic.rootDatum n F) := by
  have h4 : Nat.card F ≤ 4 := by rcases hF with h | h <;> omega
  constructor
  · intro i
    obtain ⟨φ, -, hx, hy⟩ := Sp.rankOne (F := F) i
    exact not_hasCompFactor_of_sl2_range hO h4 φ
      (CFSG.AGLEmbedding.ParabPrime.rankOne_eq_range_of_sl2 Sp.isParametrization hx hy)
  · intro hrank u v hadj
    have hpath : ∀ i j : Fin n, i ≠ j →
        (CFSG.LieType.Universal.Symplectic.cartanC n i j ≠ 0 ↔
          i.val + 1 = j.val ∨ j.val + 1 = i.val) :=
      fun i j hij => CFSG.AGLEmbeddingD2.Tits.GN516.Fam.cartanC_ne_zero_iff (m := n) hij
    have hne := ((CFSG.LieType.Universal.Symplectic.rootDatum n F).isFiniteType
      ).diagramGraph_adj_iff.1 hadj
    have key : ∀ x y : Fin n, x.val + 1 = y.val →
        SmallEdge (CFSG.LieType.Universal.Symplectic.rootDatum n F) x y := by
      intro x y hxy
      have hxlt : x.val + 1 < n := by omega
      obtain rfl : y = ⟨x.val + 1, hxlt⟩ := Fin.ext hxy.symm
      by_cases hy : (⟨x.val + 1, hxlt⟩ : Fin n).val + 1 < n
      · have hk : x.val + 1 < n := hxlt
        have hk2 : (⟨x.val + 1, hk⟩ : Fin n).val + 1 < n := hy
        have hij : x ≠ (⟨x.val + 1, hk⟩ : Fin n) := SpExtras.ne_succ' hk
        have hjk : (⟨x.val + 1, hk⟩ : Fin n) ≠
            (⟨(⟨x.val + 1, hk⟩ : Fin n).val + 1, hk2⟩ : Fin n) := SpExtras.ne_succ' hk2
        have hik : x ≠ (⟨(⟨x.val + 1, hk⟩ : Fin n).val + 1, hk2⟩ : Fin n) :=
          Fin.ne_of_val_ne (by show x.val ≠ x.val + 1 + 1; omega)
        have h1 : (shortBlock F hij).range =
            rankOne (rootGroup n F) x := range_shortBlock_eq_rankOne (K := F) hk
        have h2 : (shortBlock F hjk).range =
            rankOne (rootGroup n F) (⟨x.val + 1, hk⟩ : Fin n) :=
          range_shortBlock_eq_rankOne (K := F) hk2
        have hr : (leviSL3 F hij hjk hik).range =
            rankOne (rootGroup n F) x ⊔
              rankOne (rootGroup n F) (⟨x.val + 1, hk⟩ : Fin n) := by
          apply le_antisymm
          · have h := linearBlockStandardPair_le_sup
              (linearBlockStandardPair_shortBlock (K := F) hij hjk hik)
            rw [h1, h2] at h
            exact h
          · refine sup_le ?_ ?_
            · rw [← h1, ← leviSL3_comp_blockSL_zero (K := F) hij hjk hik]
              intro z hz
              obtain ⟨a, rfl⟩ := MonoidHom.mem_range.1 hz
              exact MonoidHom.mem_range.2 ⟨_, rfl⟩
            · rw [← h2, ← leviSL3_comp_blockSL_one (K := F) hij hjk hik]
              intro z hz
              obtain ⟨a, rfl⟩ := MonoidHom.mem_range.1 hz
              exact MonoidHom.mem_range.2 ⟨_, rfl⟩
        exact Or.inl (not_hasCompFactor_of_sl3_range hO hF
          (leviSL3 F hij hjk hik) hr)
      · have hyt : (⟨x.val + 1, hxlt⟩ : Fin n).val + 1 = n := by
          have := (⟨x.val + 1, hxlt⟩ : Fin n).isLt
          omega
        have hxt : x.val + 2 = n := by omega
        have hdeg := CFSG.AGLEmbeddingD2.Tits.GN516.EdgeLev.degree_ne_of_path hrank
          (CFSG.LieType.Universal.Symplectic.rootDatum n F).isFiniteType hpath hyt hxt
        exact Or.inr (Or.inl hdeg.symm)
    rcases (CFSG.AGLEmbeddingD2.Tits.GN516.Fam.cartanC_ne_zero_iff (m := n) hne.1).1
      hne.2 with h | h
    · exact key u v h
    · exact smallEdge_comm (key v u h)

end SmallSp

private theorem bqSmall_spinPlus {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n) (hO : LieOrderFormulasInput) (hF : Nat.card F = 2 ∨ Nat.card F = 4) :
    BQSmall (CFSG.LieType.Universal.Spin.plusDatum n F hn) := by
  have : NeZero n := ⟨by omega⟩
  have : Finite (spinGroup
      (CFSG.LieType.Universal.Spin.quadPlus n F)) :=
    CFSG.LieType.Steinberg.finite_spinGroup_of_ker _
      (CFSG.LieType.Universal.Spin.coe_ker_spinMatrix_quadPlus (n := n) (K := F))
  have h4 : Nat.card F ≤ 4 := by rcases hF with h | h <;> omega
  constructor
  · intro i
    obtain ⟨φ, -, hx, hy⟩ := SpinPlus.rankOne (K := F) hn i
    exact not_hasCompFactor_of_sl2_range hO h4 φ
      (CFSG.AGLEmbedding.ParabPrime.rankOne_eq_range_of_sl2
        (SpinPlus.isParametrization (K := F) hn) hx hy)
  · intro _hrank u v hadj
    have hne := ((CFSG.LieType.Universal.Spin.plusDatum n F hn).isFiniteType
      ).diagramGraph_adj_iff.1 hadj
    have hedge : CFSG.Timmesfeld.edgeD n u v ∨ CFSG.Timmesfeld.edgeD n v u := by
      by_contra h
      obtain ⟨h1, h2⟩ := not_or.1 h
      exact hne.2 (CFSG.Timmesfeld.LevisSpin.cartanD_of_not_edgeD hne.1 h1 h2).1
    rcases hedge with h | h
    · exact Or.inl (not_hasCompFactor_edge_of_simplyLacedLevis hO hF
        (CFSG.Timmesfeld.simplyLacedLevis_spinPlus F hn) h)
    · refine Or.inl ?_
      rw [sup_comm]
      exact not_hasCompFactor_edge_of_simplyLacedLevis hO hF
        (CFSG.Timmesfeld.simplyLacedLevis_spinPlus F hn) h


section SmallSU

open CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary

private theorem not_hasCompFactor_su_node {F : Type} [Field F] [Finite F] [CharP F 2]
    [Fact (Nat.Prime 2)] {n : ℕ} (hO : LieOrderFormulasInput)
    (hcard : Nat.card F = (2 ^ 1) ^ 2) (i : Fin (n / 2)) :
    ¬ HasCompFactor (rankOne (rootDatum hcard n).rootGroup i) IsCalL0 := by
  change ¬ HasCompFactor (rankOne (rootGroup (unitaryInvolution F 2 1)
    (unitaryInvolution_involutive hcard) n) i) IsCalL0
  have hF4 : Nat.card F = 4 := by simpa using hcard
  by_cases hk : i.val + 1 < n / 2
  · exact not_hasCompFactor_of_mulEquiv_sl2 hO (by omega)
      (rankOneShortEquiv (hσ := unitaryInvolution_involutive hcard) hk)
  · by_cases he : Even n
    · obtain ⟨z, hz0, hz⟩ := exists_unitaryInvolution_eq_neg hcard
      have hsub : Nat.card (fixedSubfield F 2 1) ≤ 4 := by
        rw [card_fixedSubfield (p := 2) (f := 1) hcard]
        norm_num
      exact not_hasCompFactor_of_mulEquiv_sl2 hO hsub
        ((rankOneLastEvenEquiv (p := 2) (f := 1) hcard he hk).trans
          (hypEquiv (p := 2) (f := 1) hz0 hz).symm)
    · have h3 : Nat.card ↥(rankOne (rootGroup (unitaryInvolution F 2 1)
          (unitaryInvolution_involutive hcard) n) i) < 504 := by
        rw [Nat.card_congr
          (rankOneLastOddEquiv (p := 2) (f := 1) hcard he hk).toEquiv,
          card_SU_three (p := 2) (f := 1) hcard]
        norm_num
      exact not_hasCompFactor_isCalL0_of_natCard_lt hO h3

private theorem smallEdge_su_of_adj {F : Type} [Field F] [Finite F] [CharP F 2]
    [Fact (Nat.Prime 2)] {n : ℕ} (hO : LieOrderFormulasInput)
    (hcard : Nat.card F = (2 ^ 1) ^ 2) {a b : Fin (n / 2)} (hb : b.val = a.val + 1)
    (hm : b.val + 1 < n / 2) : SmallEdge (rootDatum hcard n) a b := by
  have hF4 : Nat.card F = 4 := by simpa using hcard
  obtain ⟨l, -, hr⟩ :=
    CFSG.AGLEmbeddingD2.Tits.GN516.Fam.edgeRange_su_of_adj hcard (n := n) hb hm
  exact Or.inl (not_hasCompFactor_of_sl3_range hO (Or.inr hF4) l hr)

private theorem bqSmall_su {F : Type} [Field F] [Finite F] [CharP F 2]
    [Fact (Nat.Prime 2)] {n : ℕ} (hO : LieOrderFormulasInput)
    (hcard : Nat.card F = (2 ^ 1) ^ 2) : BQSmall (rootDatum hcard n) := by
  refine ⟨fun i => not_hasCompFactor_su_node hO hcard i, ?_⟩
  intro hrank u v hadj
  have hpath : ∀ i j : Fin (n / 2), i ≠ j →
      ((rootDatum hcard n).cartan i j ≠ 0 ↔ i.val + 1 = j.val ∨ j.val + 1 = i.val) :=
    fun i j hij => CFSG.AGLEmbeddingD2.Tits.GN516.Fam.cartan_ne_zero_iff (n := n) hij
  have hne := ((rootDatum hcard n).isFiniteType.diagramGraph_adj_iff).1 hadj
  have key : ∀ x y : Fin (n / 2), x.val + 1 = y.val →
      SmallEdge (rootDatum hcard n) x y := by
    intro x y hxy
    by_cases hy : y.val + 1 < n / 2
    · exact smallEdge_su_of_adj hO hcard hxy.symm hy
    · have hyt : y.val + 1 = n / 2 := by have := y.isLt; omega
      have hxt : x.val + 2 = n / 2 := by omega
      have hdeg := CFSG.AGLEmbeddingD2.Tits.GN516.EdgeLev.degree_ne_of_path hrank
        (rootDatum hcard n).isFiniteType hpath hyt hxt
      exact Or.inr (Or.inl hdeg.symm)
  rcases (CFSG.AGLEmbeddingD2.Tits.GN516.Fam.cartan_ne_zero_iff (n := n) hne.1).1
    hne.2 with h | h
  · exact key u v h
  · exact smallEdge_comm (key v u h)

end SmallSU


section SmallSpinMinus

open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.ClassicalInvolution.Models.TwistedPairs CFSG.ClassicalInvolution.WeakCT
  CFSG.LieType.Steinberg.CentralExt CFSG.RankThree.PartOne.CTP

private theorem minusDatum_cartan_ne_zero_iff {n : ℕ} {F : Type} [Field F] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {i j : Fin (n - 1)} (hij : i ≠ j) :
    (minusDatum n hirr).cartan i j ≠ 0 ↔ i.val + 1 = j.val ∨ j.val + 1 = i.val := by
  change cartanB (n - 1) i j ≠ 0 ↔ i.val + 1 = j.val ∨ j.val + 1 = i.val
  constructor
  · intro h
    by_contra hc
    exact h (OddCT.cartanB_of_far hij (fun h1 => hc (Or.inl h1))
      (fun h2 => hc (Or.inr h2)))
  · rintro (h | h)
    · rw [OddCT.cartanB_of_succ h]
      norm_num
    · rw [OddCT.cartanB_of_pred h]
      split_ifs <;> norm_num

private theorem not_hasCompFactor_spinMinus_node
    {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (hO : LieOrderFormulasInput) (hF2 : Nat.card F = 2) (k : Fin (n - 1)) :
    ¬ HasCompFactor (rankOne (minusDatum n hirr).rootGroup k) IsCalL0 := by
  have : Finite (spinGroup (quadMinus n F b c)) :=
    CFSG.LieType.Steinberg.finite_spinGroup_of_ker _
      (CFSG.LieType.Universal.Spin.coe_ker_spinMatrix_quadMinus hirr)
  by_cases hk : k.val + 1 < n - 1
  · exact not_hasCompFactor_of_sl2_range (F := F) hO (by rw [hF2]; norm_num)
      (rLong n b c hk) (rankOne_minusDatum_long hirr hk)
  · have : Fact (∀ r : F, r ^ 2 ≠ -c + b * r) := fact_shortField hirr
    have : Finite (ShortField b c) := finite_shortField (b := b) (c := c)
    have h4 : Nat.card (ShortField b c) ≤ 4 := by
      rw [SpinMinusClosed.card_shortField, hF2]
      norm_num
    exact not_hasCompFactor_of_sl2_range hO h4 (shortBlock hirr n k)
      (rankOne_minusDatum_short hirr hk)

private theorem smallEdge_spinMinus_of_succ {n : ℕ} {F : Type} [Field F] [Finite F]
    [CharP F 2] {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (hn : 4 ≤ n) (hO : LieOrderFormulasInput) (hF2 : Nat.card F = 2)
    {u v : Fin (n - 1)} (huv : u.val + 1 = v.val) :
    SmallEdge (minusDatum n hirr) u v := by
  have : Finite (spinGroup (quadMinus n F b c)) :=
    CFSG.LieType.Steinberg.finite_spinGroup_of_ker _
      (CFSG.LieType.Universal.Spin.coe_ker_spinMatrix_quadMinus hirr)
  have hu : u.val + 1 < n - 1 := by have := v.isLt; omega
  by_cases hv : v.val + 1 < n - 1
  · obtain ⟨emb, -, h0, h1⟩ := exists_sl3_minus_even (n := n) b c huv hu hv
    have hgen : (blk F 0).range ⊔ (blk F 1).range = ⊤ := B12_sup_B23 (K := F)
    have hkey : emb.range =
        (emb.comp (blk F 0)).range ⊔ (emb.comp (blk F 1)).range := by
      rw [MonoidHom.range_comp, MonoidHom.range_comp, ← Subgroup.map_sup, hgen,
        MonoidHom.range_eq_map]
    have hr : emb.range = rankOne (minusDatum n hirr).rootGroup u ⊔
        rankOne (minusDatum n hirr).rootGroup v := by
      rw [hkey, h0, h1, rankOne_minusDatum_long hirr hu, rankOne_minusDatum_long hirr hv]
    exact Or.inl (not_hasCompFactor_of_sl3_range hO (Or.inl hF2) emb hr)
  · have hvt : v.val + 1 = n - 1 := by have := v.isLt; omega
    have hut : u.val + 2 = n - 1 := by omega
    have hpath : ∀ i j : Fin (n - 1), i ≠ j →
        ((minusDatum n hirr).cartan i j ≠ 0 ↔
          i.val + 1 = j.val ∨ j.val + 1 = i.val) :=
      fun i j hij => minusDatum_cartan_ne_zero_iff hirr hij
    have hdeg := CFSG.AGLEmbeddingD2.Tits.GN516.EdgeLev.degree_ne_of_path
      (by show 3 ≤ n - 1; omega) (minusDatum n hirr).isFiniteType hpath hvt hut
    exact Or.inr (Or.inl hdeg.symm)

private theorem bqSmall_spinMinus
    {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (hn : 4 ≤ n)
    (hO : LieOrderFormulasInput) (hF2 : Nat.card F = 2) :
    BQSmall (minusDatum n hirr) := by
  have : Finite (spinGroup (quadMinus n F b c)) :=
    CFSG.LieType.Steinberg.finite_spinGroup_of_ker _
      (CFSG.LieType.Universal.Spin.coe_ker_spinMatrix_quadMinus hirr)
  constructor
  · intro k
    exact not_hasCompFactor_spinMinus_node hirr hO hF2 k
  · intro _hrank u v hadj
    have hpath : ∀ i j : Fin (n - 1), i ≠ j →
        ((minusDatum n hirr).cartan i j ≠ 0 ↔
          i.val + 1 = j.val ∨ j.val + 1 = i.val) :=
      fun i j hij => minusDatum_cartan_ne_zero_iff hirr hij
    have hne := ((minusDatum n hirr).isFiniteType.diagramGraph_adj_iff).1 hadj
    have key : ∀ x y : Fin (n - 1), x.val + 1 = y.val →
        SmallEdge (minusDatum n hirr) x y :=
      fun x y hxy => smallEdge_spinMinus_of_succ hirr hn hO hF2 hxy
    rcases (minusDatum_cartan_ne_zero_iff hirr hne.1).1 hne.2 with h | h
    · exact key u v h
    · exact smallEdge_comm (key v u h)

end SmallSpinMinus

variable {X : Type} [Group X] {n f : ℕ}

theorem hasBQSmall_psl (hO : LieOrderFormulasInput) (hm : CFSG.Models.LieModel X .PSL n 2 f)
    (h : f = 1 ∧ 4 ≤ n ∨ f = 2 ∧ n = 4) : HasBQSmall X := by
  obtain ⟨⟨-, -, -, -, -⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ :=
    CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide)
      (CFSG.StandardType.ChevTwo.blueprintLieModel_of_modelsLieModel (by decide) hm)
  let : Field F := hF
  let : Finite F := hFfin
  let : Fintype F := Fintype.ofFinite F
  have hf : f = 1 ∨ f = 2 := h.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
  have hn4 : 4 ≤ n := h.elim (fun h => h.2) (fun h => by omega)
  have hFle : Nat.card F = 2 ∨ Nat.card F = 4 := by
    rcases hf with rfl | rfl
    · exact Or.inl (by simpa using hcard)
    · exact Or.inr (by simpa using hcard)
  have : CharP F 2 := charP_of_card_eq_prime_pow (f := f)
    (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 :=
    ⟨n - 1, (Nat.sub_add_cancel (by omega)).symm⟩
  let e' : Matrix.ProjectiveSpecialLinearGroup (Fin (m + 1)) F ≃* X :=
    (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj (m + 1) F).trans
      e.symm
  have hBQ := CFSG.AGLEmbedding.ParabHub.borelQuotient_sl e'
  exact ⟨_, inferInstance, inferInstance, _, _, _, _, _, hBQ,
    bqSmall_sl (m := m) (F := F) hO hFle, Or.inl (by show 3 ≤ m; omega)⟩

theorem hasBQSmall_psu (hO : LieOrderFormulasInput) (hm : CFSG.Models.LieModel X .PSU n 2 1)
    (hn : 4 ≤ n) : HasBQSmall X := by
  obtain ⟨⟨-, -, -, -⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ :=
    CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide)
      (CFSG.StandardType.ChevTwo.blueprintLieModel_of_modelsLieModel (by decide) hm)
  let : Field F := hF
  let : Finite F := hFfin
  let : Fintype F := Fintype.ofFinite F
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := charP_of_card_eq_prime_pow (f := 2)
    (by rw [← Nat.card_eq_fintype_card, hcard]; norm_num)
  obtain ⟨ζ, hζ⟩ := CFSG.LieType.Universal.Unitary.exists_traceZero_ne_zero hcard
  have hBQ := CFSG.AGLEmbedding.ParabHub.borelQuotient_su hcard (by omega) ζ hζ e
  by_cases hn6 : 6 ≤ n
  · exact ⟨_, inferInstance, inferInstance, _, _, _, _, _, hBQ,
      bqSmall_su (F := F) (n := n) hO hcard,
      Or.inl (by change 3 ≤ n / 2; omega)⟩
  · have hn45 : n = 4 ∨ n = 5 := by omega
    rcases hn45 with rfl | rfl
    · exact ⟨_, inferInstance, inferInstance, _, _, _, _, _, hBQ,
        bqSmall_su (F := F) hO hcard,
        Or.inr ⟨(0 : Fin 2), (1 : Fin 2),
          CFSG.LieType.Universal.Unitary.card_rootGroup_four_zero_ne_one (f := 1) hcard⟩⟩
    · exact ⟨_, inferInstance, inferInstance, _, _, _, _, _, hBQ,
        bqSmall_su (F := F) hO hcard,
        Or.inr ⟨(0 : Fin 2), (1 : Fin 2),
          CFSG.LieType.Universal.Unitary.card_rootGroup_five_zero_ne_one (f := 1) hcard⟩⟩

theorem hasBQSmall_psp (hO : LieOrderFormulasInput) (hm : CFSG.Models.LieModel X .PSp n 2 f)
    (h : f = 1 ∧ 3 ≤ n ∨ f = 2 ∧ n = 3) : HasBQSmall X := by
  obtain ⟨⟨-, -, hn, -⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ :=
    CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide)
      (CFSG.StandardType.ChevTwo.blueprintLieModel_of_modelsLieModel (by decide) hm)
  let : Field F := hF
  let : Finite F := hFfin
  let : Fintype F := Fintype.ofFinite F
  have hf : f = 1 ∨ f = 2 := h.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
  have hn3 : 3 ≤ n := h.elim (fun h => h.2) (fun h => by omega)
  have hFle : Nat.card F = 2 ∨ Nat.card F = 4 := by
    rcases hf with rfl | rfl
    · exact Or.inl (by simpa using hcard)
    · exact Or.inr (by simpa using hcard)
  have : CharP F 2 := charP_of_card_eq_prime_pow (f := f)
    (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  have hBQ := CFSG.AGLEmbedding.ParabHub.borelQuotient_sp e
  exact ⟨_, inferInstance, inferInstance, _, _, _, _, _, hBQ,
    bqSmall_sp (n := n) (F := F) hO hFle, Or.inl hn3⟩

theorem hasBQSmall_pomegaPlus (hO : LieOrderFormulasInput)
    (hm : CFSG.Models.LieModel X .POmegaPlus n 2 1) : HasBQSmall X := by
  obtain ⟨⟨-, -, hn⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ :=
    CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide)
      (CFSG.StandardType.ChevTwo.blueprintLieModel_of_modelsLieModel (by decide) hm)
  let : Field F := hF
  let : Finite F := hFfin
  let : Fintype F := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime_pow (f := 1)
    (by rw [← Nat.card_eq_fintype_card]; simpa using hcard)
  have hn3 : 3 ≤ n := by omega
  have : NeZero n := ⟨by omega⟩
  have : Finite (spinGroup (CFSG.LieType.Universal.Spin.quadPlus n F)) :=
    CFSG.LieType.Steinberg.finite_spinGroup_of_ker _
      (CFSG.LieType.Universal.Spin.coe_ker_spinMatrix_quadPlus (n := n) (K := F))
  have hFle : Nat.card F = 2 ∨ Nat.card F = 4 := Or.inl (by simpa using hcard)
  have hBQ := CFSG.AGLEmbedding.ParabHub.borelQuotient_spinPlus hn3 e
  exact ⟨_, inferInstance, inferInstance, _, _, _, _, _, hBQ,
    bqSmall_spinPlus (n := n) (F := F) hn3 hO hFle,
    Or.inl (by change 3 ≤ n; exact hn3)⟩

theorem hasBQSmall_pomegaMinus
    (hO : LieOrderFormulasInput)
    (hm : CFSG.Models.LieModel X .POmegaMinus n 2 1) : HasBQSmall X := by
  obtain ⟨⟨-, -, hn⟩, F, hF, hFfin, hcard, b, c, hirr, ⟨e⟩⟩ :=
    CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide)
      (CFSG.StandardType.ChevTwo.blueprintLieModel_of_modelsLieModel (by decide) hm)
  let : Field F := hF
  let : Finite F := hFfin
  let : Fintype F := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime_pow (f := 1)
    (by rw [← Nat.card_eq_fintype_card]; simpa using hcard)
  have hn4 : 4 ≤ n := by omega
  have : Finite (spinGroup (CFSG.LieType.Universal.Spin.quadMinus n F b c)) :=
    CFSG.LieType.Steinberg.finite_spinGroup_of_ker _
      (CFSG.LieType.Universal.Spin.coe_ker_spinMatrix_quadMinus hirr)
  have hF2 : Nat.card F = 2 := by simpa using hcard
  have hBQ := CFSG.AGLEmbedding.ParabHub.borelQuotient_spinMinus hirr hn4 e
  exact ⟨_, inferInstance, inferInstance, _, _, _, _, _, hBQ,
    bqSmall_spinMinus (n := n) (F := F) (b := b) (c := c) hirr hn4 hO hF2,
    Or.inl (by change 3 ≤ n - 1; omega)⟩

end CFSG.LocalAnalysis.WeakClosure81.Chev2Orbit
