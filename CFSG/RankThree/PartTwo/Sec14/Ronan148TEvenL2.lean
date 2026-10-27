module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148TOddL2
import CFSG.RankThree.PartTwo.Sec14.Ronan148TLocTheta
import CFSG.RankThree.PartTwo.KFacts.K72FixL2
import CFSG.RankThree.PartTwo.KFacts.K72FieldKind
import CFSG.RankThree.PartTwo.KFacts.K72Centralizer
import CFSG.RankThree.PartTwo.KFacts.K72List
import CFSG.RankThree.SubgroupLists.LinearTwoFamily
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Center
import CFSG.GroupTheory.ABGLocalTools.PStabilityQSL2
import CFSG.GroupTheory.PCore.SubgroupCore
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore
import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148T

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.LocalRank CFSG.GorensteinWalter
  CFSG.GH74.GLS
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.RankThree.PartTwo.KFacts (IsInnerAut)

theorem le_center_of_normal_of_card_eq_two {G : Type*} [Group G] {N : Subgroup G} (hN : N.Normal)
    (h2 : Nat.card N = 2) : N ≤ Subgroup.center G := by
  intro n hn
  rw [Subgroup.mem_center_iff]
  intro g
  by_cases hn1 : n = 1
  · rw [hn1, mul_one, one_mul]
  have hc : g * n * g⁻¹ ∈ N := hN.conj_mem n hn g
  have hc1 : g * n * g⁻¹ ≠ 1 := by
    intro h
    apply hn1
    calc n = g⁻¹ * (g * n * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  have hcn : g * n * g⁻¹ = n := by
    by_contra hne
    have h3 : 3 ≤ Nat.card N := by
      have hfin : Finite N := Nat.finite_of_card_ne_zero (by rw [h2]; norm_num)
      have := Fintype.ofFinite N
      classical
      have hsub : ({1, ⟨n, hn⟩, ⟨_, hc⟩} : Finset N).card = 3 := by
        rw [Finset.card_insert_of_notMem, Finset.card_pair]
        · intro h
          exact hne (congrArg Subtype.val h).symm
        · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨fun h => hn1 (congrArg Subtype.val h).symm,
            fun h => hc1 (congrArg Subtype.val h).symm⟩
      rw [Nat.card_eq_fintype_card, ← hsub]
      exact Finset.card_le_univ _
    omega
  calc g * n = g * n * g⁻¹ * g := by group
    _ = n * g := by rw [hcn]

theorem pPrimeCore_psl2_of_card_eq_two {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2) :
    CFSG.pPrimeCore 3 (PSL2 F) = ⊥ := by
  set N := CFSG.pPrimeCore 3 (PSL2 F) with hNdef
  have hc := CFSG.coprime_card_pPrimeCore 3 (PSL2 F)
  have hN : N.Normal := CFSG.pPrimeCore_normal
  have h6 : Nat.card (PSL2 F) ∣ 6 := by
    have h1 : Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) = 6 := by
      rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num), hF]
      decide
    rw [← h1]
    exact Subgroup.card_quotient_dvd_card _
  have hd : Nat.card N ∣ 2 := by
    have h1 : Nat.card N ∣ 3 * 2 := (Subgroup.card_subgroup_dvd_card N).trans h6
    exact hc.symm.dvd_of_dvd_mul_left h1
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
  · exact Subgroup.card_eq_one.mp h
  · have hle := le_center_of_normal_of_card_eq_two hN h
    rw [psl2_center_eq_bot F] at hle
    exact eq_bot_iff.mpr hle

section Model

variable {S : Type} [Group S] [Finite S] {F : Type} [Field F] [Finite F]

theorem pPrimeCoreOf_autFix_eq_bot_of_outer_two (e : S ≃* PSL2 F) {j : ℕ}
    (hF : Nat.card F = 2 ^ j) {α : MulAut S} (hα3 : α ^ 3 = 1) (hout : ¬ IsInnerAut α) :
    pPrimeCoreOf 3 (Sec4.autFix α) = ⊥ := by
  set β := MulAut.congr e α with hβ
  have hβ3 : β ^ 3 = 1 := by rw [hβ, ← map_pow, hα3, map_one]
  have hβout : ¬ IsInnerAut β := by rwa [hβ, KFacts.isInnerAut_congr]
  obtain ⟨σ, hσ3, ⟨ψ⟩⟩ := KFacts.exists_eqLocus_mulEquiv_psl2 hβ3 hβout
  set q₀ := Nat.card (GH74.GLS.IVK.fixedField σ) with hq₀def
  have hK : Nat.card F = q₀ ^ 3 := by
    have h := GH74.GLS.IVK.fixedField_card_pow σ
    rw [hσ3] at h
    exact h.symm
  have hdvd : q₀ ∣ 2 ^ j := by
    rw [← hF, hK]
    exact dvd_pow_self q₀ (by norm_num)
  obtain ⟨k, -, hq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  rcases k with _ | _ | k
  · exfalso
    rw [pow_zero] at hq
    rw [hq, one_pow] at hK
    have : 1 < Nat.card F := Finite.one_lt_card
    omega
  ·
    rw [pow_one] at hq
    have hmap : (α.toMonoidHom.eqLocus (MonoidHom.id S)).map e.toMonoidHom =
        β.toMonoidHom.eqLocus (MonoidHom.id (PSL2 F)) := by
      ext z
      constructor
      · rintro ⟨y, hy, rfl⟩
        have hy' : α y = y := hy
        show e (α (e.symm (e y))) = e y
        rw [MulEquiv.symm_apply_apply, hy']
      · intro hz
        refine ⟨e.symm z, ?_, by simp⟩
        have hz' : e (α (e.symm z)) = z := hz
        show α (e.symm z) = e.symm z
        have h2 := congrArg e.symm hz'
        rwa [MulEquiv.symm_apply_apply] at h2
    let χ : Sec4.autFix α ≃* PSL2 (GH74.GLS.IVK.fixedField σ) :=
      (MulEquiv.subgroupCongr (autFix_eq_eqLocus α)).trans
        (((Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).trans
          (MulEquiv.subgroupCongr hmap)).trans ψ)
    have h0 := pPrimeCore_psl2_of_card_eq_two (F := GH74.GLS.IVK.fixedField σ) hq
    have h1 := CFSG.pPrimeCore_map_iso 3 χ
    rw [h0, Subgroup.map_eq_bot_iff_of_injective _ χ.injective] at h1
    unfold pPrimeCoreOf
    rw [h1, Subgroup.map_bot]
  ·
    have hq₀ : 4 ≤ q₀ := by
      rw [hq]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (k + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    obtain ⟨hZ, hQ, h3, -⟩ := KFacts.fixedPoints_facts_of_mulEquiv_psl2 e hq₀ hK hα3 hout
    rw [autFix_eq_eqLocus]
    have : IsSimpleGroup (α.toMonoidHom.eqLocus (MonoidHom.id S) ⧸
        Subgroup.center (α.toMonoidHom.eqLocus (MonoidHom.id S))) := hQ.2.1
    haveI : IsSimpleGroup (α.toMonoidHom.eqLocus (MonoidHom.id S)) := MulEquiv.isSimpleGroup
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
    exact pPrimeCoreOf_eq_bot_of_isSimpleGroup h3

end Model

theorem evenL2Excl {S : Type} [Group S] [Finite S] {j : ℕ} (hj : 2 ≤ j) (hS : IsSimpleGroup S)
    (hM : StatedClassicalModel S .PSL 2 2 j) {E : Subgroup (MulAut S)} (hE9 : Nat.card E = 9)
    (hE3 : ∀ ε ∈ E, ε ^ 3 = 1)
    (hgen : (⊤ : Subgroup S) ≤ ⨆ (ε : MulAut S) (_ : ε ∈ E) (_ : ε ≠ 1),
      pPrimeCoreOf 3 (Sec4.autFix ε)) : False := by
  obtain ⟨-, F, _, _, hF, ⟨e₀⟩⟩ := hM
  set e : S ≃* PSL2 F := SubgroupLists.toPSL2 e₀ with he
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow Nat.prime_two hF
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3dvd : 3 ∣ Nat.card S := by
    rw [Nat.card_congr e.toEquiv]
    exact KFacts.three_dvd_card_psl2 F
  have hnt : Nontrivial S := hS.toNontrivial
  have h3F : ringChar F ≠ 3 := by
    rw [ringChar.eq F 2]
    norm_num
  have h4F : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj
  set W : MulAut S → Subgroup S := fun ε => pPrimeCoreOf 3 (Sec4.autFix ε) with hW
  by_cases hinner : ∃ ε₀ ∈ E, ε₀ ≠ 1 ∧ IsInnerAut ε₀
  · obtain ⟨ε₀, hε₀, hε₀1, hε₀i⟩ := hinner
    have hle : (⊤ : Subgroup S) ≤ W ε₀ := by
      refine hgen.trans (iSup_le fun ε => iSup_le fun hε => iSup_le fun hε1 => ?_)
      by_cases hεi : IsInnerAut ε
      · have hz := mem_zpowers_of_isInnerAut e h3F h4F hE9 hE3 hε₀ hε₀1 hε₀i hε hεi
        change pPrimeCoreOf 3 (Sec4.autFix ε) ≤ pPrimeCoreOf 3 (Sec4.autFix ε₀)
        rw [autFix_eq_of_mem_zpowers (hE3 ε₀ hε₀) hz hε1]
      · change pPrimeCoreOf 3 (Sec4.autFix ε) ≤ _
        rw [pPrimeCoreOf_autFix_eq_bot_of_outer_two e hF (hE3 ε hε) hεi]
        exact bot_le
    have hc := coprime_card_pPrimeCoreOf 3 (Sec4.autFix ε₀)
    have h1 : Nat.card (⊤ : Subgroup S) ∣ Nat.card (W ε₀) := Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_top] at h1
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hc (h3dvd.trans h1)
  · push Not at hinner
    have hle : (⊤ : Subgroup S) ≤ ⊥ :=
      hgen.trans (iSup_le fun ε => iSup_le fun hε => iSup_le fun hε1 => le_of_eq
        (pPrimeCoreOf_autFix_eq_bot_of_outer_two e hF (hE3 ε hε) (hinner ε hε hε1)))
    obtain ⟨a, b, hab⟩ := exists_pair_ne S
    apply hab
    have ha := hle (Subgroup.mem_top a)
    have hb := hle (Subgroup.mem_top b)
    rw [Subgroup.mem_bot] at ha hb
    rw [ha, hb]

end CFSG.RankThree.PartTwo.Sec14.Ronan148T
