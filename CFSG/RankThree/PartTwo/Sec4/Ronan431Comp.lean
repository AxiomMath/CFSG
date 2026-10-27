module

public import CFSG.RankThree.PartTwo.Sec4.Ronan431Cfg
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieDefs
import CFSG.GroupTheory.QuotientCoreFacts

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan431

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open scoped commutatorElement

theorem fixSubgroup_eq_autFix {S : Type*} [Group S] (σ : MulAut S) :
    fixSubgroup σ = autFix σ := by
  ext x
  exact Iff.rfl

theorem three_dvd_card_alt6 : 3 ∣ Nat.card (alternatingGroup (Fin 6)) := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem pPrimeCore_three_eq_pCore_two {K : Type} [Group K] [Finite K]
    (h : IsType431 (K ⧸ CFSG.pCore 2 K)) : CFSG.pPrimeCore 3 K = CFSG.pCore 2 K := by
  obtain ⟨e⟩ := h
  refine le_antisymm ?_
    (CFSG.GroupTheory.pCore_le_pPrimeCore Nat.prime_two Nat.prime_three (by norm_num) K)
  set N : Subgroup (alternatingGroup (Fin 6)) := (CFSG.pPrimeCore 3 K).map (coverHom e) with hN
  have hNn : N.Normal := Subgroup.Normal.map inferInstance _ (coverHom_surjective e)
  haveI : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h0 | h0
  · intro x hx
    rw [← coverHom_ker e, MonoidHom.mem_ker]
    have hxN : coverHom e x ∈ N := ⟨x, hx, rfl⟩
    rw [h0, Subgroup.mem_bot] at hxN
    exact hxN
  · exfalso
    have hdvd : Nat.card N ∣ Nat.card (CFSG.pPrimeCore 3 K) := Subgroup.card_map_dvd _ _
    rw [h0, Subgroup.card_top] at hdvd
    have hcop : Nat.Coprime 3 (Nat.card (CFSG.pPrimeCore 3 K)) := CFSG.pPrimeCore_coprime_card
    exact absurd (Nat.Coprime.coprime_dvd_right (three_dvd_card_alt6.trans hdvd) hcop)
      (by norm_num)

noncomputable def pQuotThreeEquivOfType {K : Type} [Group K] [Finite K]
    (h : IsType431 (K ⧸ CFSG.pCore 2 K)) (e : K ⧸ CFSG.pCore 2 K ≃* alternatingGroup (Fin 6)) :
    K ⧸ GLAPPrimeCore 3 K ≃* alternatingGroup (Fin 6) :=
  (QuotientGroup.quotientMulEquivOfEq (pPrimeCore_three_eq_pCore_two h)).trans e

theorem card_alt6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem alt6_nonabelian' : ∃ a b : alternatingGroup (Fin 6), a * b ≠ b * a := by
  by_contra hc
  push Not at hc
  have hZ := alternatingGroup.center_eq_bot (α := Fin 6) (by simp)
  have htop : Subgroup.center (alternatingGroup (Fin 6)) = ⊤ :=
    eq_top_iff.mpr fun g _ => Subgroup.mem_center_iff.mpr fun h => hc h g
  have h1 := Subgroup.card_top (G := alternatingGroup (Fin 6))
  rw [← htop, hZ, Subgroup.card_bot, card_alt6] at h1
  omega

theorem isQuasisimple_of_equiv_alt6 {Q : Type*} [Group Q] (e : Q ≃* alternatingGroup (Fin 6)) :
    CFSG.Open.IsQuasisimple Q := by
  haveI hs : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  haveI : IsSimpleGroup Q := (MulEquiv.isSimpleGroup_congr e).mpr hs
  have hna : ∃ a b : Q, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := alt6_nonabelian'
    exact ⟨e.symm a, e.symm b, fun h => hab (e.symm.injective (by simpa using h))⟩
  have hZ : Subgroup.center Q = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with h | h
    · exact h
    · obtain ⟨a, b, hab⟩ := hna
      exact absurd (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top a) b).symm hab
  refine ⟨?_, ?_⟩
  · rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator Q) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hna
      apply hab
      have hc : ⁅a, b⁆ ∈ commutator Q := Subgroup.commutator_mem_commutator (Subgroup.mem_top a)
        (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
      exact hc
    · exact h
  · exact (MulEquiv.isSimpleGroup_congr
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)).mpr inferInstance

variable {S : Type} [Group S] [Finite S]

theorem compOfType_of_cfgS431 {A : Subgroup (MulAut S)} {σ : MulAut S} {K : Subgroup S}
    (hc : CfgS431 S A σ K) :
    CFSG.LocalAnalysis.GLTheoremA.H1431c.CompOfType S σ CFSG.LocalAnalysis.GLTheoremA.S8.isA6 := by
  classical
  set X : Subgroup S := fixSubgroup σ with hXdef
  have hXeq : X = autFix σ := fixSubgroup_eq_autFix σ
  have hKX : K ≤ X := hXeq ▸ hc.le_autFix
  have hsnK : CFSG.Open.IsSubnormal K X :=
    (CFSG.Open.IsSubnormal.iff_subgroupOf hKX).2 (hXeq ▸ hc.isSubnormal)
  obtain ⟨e2⟩ := hc.isType
  let eK : ↥K ⧸ GLAPPrimeCore 3 ↥K ≃* alternatingGroup (Fin 6) :=
    pQuotThreeEquivOfType hc.isType e2
  let eB : ↥K ⧸ GLAPPrimeCore 3 ↥K ≃* ↥(barX 3 X K) := quotEquivBarX Nat.prime_three hKX hsnK
  have hcomp : IsComponentOf (barX 3 X K) ⊤ := by
    refine ⟨le_top, ?_, isQuasisimple_of_equiv_alt6 (eB.symm.trans eK)⟩
    have h1 : ((K.subgroupOf X).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥X))).IsSubnormal :=
      (CFSG.Open.IsSubnormal.subgroupOf hsnK).map (QuotientGroup.mk'_surjective _)
    exact CFSG.Open.IsSubnormal.of_mathlib h1
  let T : Set (Subgroup S) := {J | CFSG.Open.IsSubnormal J X ∧ barX 3 X J = barX 3 X K}
  have hT : T.Nonempty := ⟨K, hsnK, rfl⟩
  obtain ⟨J, hJ⟩ := (Set.toFinite T).exists_minimal hT
  have hJX : J ≤ X := hJ.1.1.le
  have hGLA : GLAPComponent 3 X J := by
    refine ⟨hJX, hJ.1.1, ?_, fun J' hJ' hsn' heq => ?_⟩
    · change IsComponentOf (barX 3 X J) ⊤
      rw [hJ.1.2]
      exact hcomp
    · change barX 3 X J' = barX 3 X J at heq
      exact absurd (hJ.2 ⟨hsn', heq.trans hJ.1.2⟩ hJ'.le) (not_le_of_gt hJ')
  refine ⟨J, hGLA, ?_⟩
  let eJ : PQuot 3 J ≃* alternatingGroup (Fin 6) :=
    ((quotEquivBarX Nat.prime_three hJX hJ.1.1).trans (MulEquiv.subgroupCongr hJ.1.2)).trans
      (eB.symm.trans eK)
  have hZ : Subgroup.center (PQuot 3 J) = ⊥ := by
    have h0 := alternatingGroup.center_eq_bot (α := Fin 6) (by simp)
    rw [eq_bot_iff]
    intro z hz
    have : eJ z ∈ Subgroup.center (alternatingGroup (Fin 6)) :=
      Subgroup.mem_center_iff.mpr fun g => by
        obtain ⟨y, rfl⟩ := eJ.surjective g
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz y]
    rw [h0, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    exact eJ.injective (by rw [this, map_one])
  refine ⟨.alternating 6 (by norm_num), Or.inl rfl, ⟨?_⟩⟩
  exact ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans eJ

end CFSG.RankThree.PartTwo.Sec4.Ronan431
