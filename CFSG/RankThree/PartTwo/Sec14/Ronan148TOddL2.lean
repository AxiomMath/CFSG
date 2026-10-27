module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148TOddDefs
import CFSG.RankThree.PartTwo.Sec14.Ronan148TLocTheta
import CFSG.RankThree.PartTwo.KFacts.K72FixL2
import CFSG.RankThree.PartTwo.KFacts.K72FieldKind
import CFSG.RankThree.PartTwo.KFacts.K72Centralizer
import CFSG.RankThree.PartTwo.KFacts.K72List
import CFSG.RankThree.PartOne.K133.UnipPSL2
import CFSG.RankThree.SubgroupLists.LinearTwoFamily
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Center
import CFSG.GroupTheory.ABGLocalTools.PStabilityQSL2
import CFSG.GroupTheory.PCore.SubgroupCore
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore
public import CFSG.Certificates.CosetTableShort
public import CFSG.ClassicalGroups.Symplectic.Simple
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig.Transport
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.RankThree.Asc83Table.PermTables
public import CFSG.RankThree.PartTwo.Sec11.Data
public import CFSG.RankThree.PartTwo.Sec14.Item148StepCases
public import CFSG.RankThree.PartTwo.Sec14.Item148StepOne
public import CFSG.RankThree.PartTwo.Sec16.Item164Proof
public import CFSG.RankThree.PartTwo.Sec16.Item169HJ
public import CFSG.RankThree.PartTwo.Sec4.Item47Bridges
public import CFSG.RankThree.PartTwo.Sec4.Item47Diag
public import CFSG.RankThree.PartTwo.Sec4.Item47LThree
public import CFSG.RankThree.PartTwo.Sec4.Item47SpFour
public import CFSG.RankThree.PartTwo.Sec4.Item47Statement
public import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
public import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
public import CFSG.RankThree.PartTwo.Sec6.Statements
public import CFSG.RankThree.S4Free.SuzukiEight
public import Certificates.Certificate2201
public import Certificates.Certificate2202
public import Certificates.Certificate2326
public import Certificates.Certificate3171
public import Certificates.Certificate3171Base
public import Certificates.Certificate43
public import Certificates.Certificate8166
public import Certificates.Certificate8169

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148T

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.LocalRank CFSG.GorensteinWalter
  CFSG.GH74.GLS
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.RankThree.PartTwo.KFacts (IsInnerAut)

theorem pPrimeCoreOf_eq_bot_of_isPGroup {G : Type*} [Group G] [Finite G] {H : Subgroup G}
    (hH : IsPGroup 3 H) : pPrimeCoreOf 3 H = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc := CFSG.coprime_card_pPrimeCore 3 H
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hH
  have hdvd : Nat.card (CFSG.pPrimeCore 3 H) ∣ 3 ^ k := hk ▸ Subgroup.card_subgroup_dvd_card _
  have h1 : Nat.card (CFSG.pPrimeCore 3 H) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right k hc.symm) hdvd
  unfold pPrimeCoreOf
  rw [Subgroup.card_eq_one.mp h1, Subgroup.map_bot]

theorem pPrimeCoreOf_eq_bot_of_isSimpleGroup {G : Type*} [Group G] [Finite G] {H : Subgroup G}
    [IsSimpleGroup H] (h3 : 3 ∣ Nat.card H) : pPrimeCoreOf 3 H = ⊥ := by
  have hc := CFSG.coprime_card_pPrimeCore 3 H
  haveI := CFSG.pPrimeCore_normal (p := 3) (G := H)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.pPrimeCore 3 H) with h | h
  · unfold pPrimeCoreOf
    rw [h, Subgroup.map_bot]
  · rw [h, Subgroup.card_top] at hc
    exact absurd h3 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hc)

theorem autFix_eq_eqLocus {X : Type*} [Group X] (α : MulAut X) :
    Sec4.autFix α = α.toMonoidHom.eqLocus (MonoidHom.id X) :=
  Subgroup.ext fun _ => Iff.rfl

theorem sup_zpowers_eq_of_not_mem {G : Type*} [Group G] [Finite G] {E : Subgroup G}
    (hE9 : Nat.card E = 9) (hE3 : ∀ ε ∈ E, ε ^ 3 = 1) {ε₀ ε₁ : G} (h₀ : ε₀ ∈ E) (h₀1 : ε₀ ≠ 1)
    (h₁ : ε₁ ∈ E) (h₁0 : ε₁ ∉ Subgroup.zpowers ε₀) :
    Subgroup.zpowers ε₀ ⊔ Subgroup.zpowers ε₁ = E := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set F := Subgroup.zpowers ε₀ ⊔ Subgroup.zpowers ε₁ with hF
  have hFE : F ≤ E := sup_le (Subgroup.zpowers_le.mpr h₀) (Subgroup.zpowers_le.mpr h₁)
  have hz₀ : Nat.card (Subgroup.zpowers ε₀) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (hE3 ε₀ h₀) h₀1
  have hlt : Subgroup.zpowers ε₀ < F := by
    refine lt_of_le_of_ne le_sup_left fun h => h₁0 ?_
    rw [h]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers ε₁)
  have hFcard : Nat.card F = 9 := by
    have hdvd : Nat.card F ∣ 9 := hE9 ▸ Subgroup.card_dvd_of_le hFE
    have h3 : 3 ∣ Nat.card F := hz₀ ▸ Subgroup.card_dvd_of_le hlt.le
    have hne : Nat.card F ≠ 3 := fun h3' => by
      have := Subgroup.eq_of_le_of_card_ge hlt.le (by rw [h3', hz₀])
      exact hlt.ne this
    have h9 : Nat.card F ≠ 1 := fun h1 => by
      rw [h1] at h3
      norm_num at h3
    obtain ⟨i, hi, hiF⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
      (show Nat.card F ∣ 3 ^ 2 by norm_num [hdvd])
    interval_cases i
    · exact absurd (by simpa using hiF) h9
    · exact absurd (by simpa using hiF) hne
    · simpa using hiF
  exact Subgroup.eq_of_le_of_card_ge hFE (by rw [hFcard, hE9])

section Model

variable {S : Type} [Group S] [Finite S] {F : Type} [Field F] [Finite F]

theorem conj_injective_of_psl2 (e : S ≃* PSL2 F) :
    Function.Injective (MulAut.conj : S →* MulAut S) := by
  rw [injective_iff_map_eq_one]
  intro s hs
  have hsZ : e s ∈ Subgroup.center (PSL2 F) := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h := congrArg (fun σ : MulAut S => σ (e.symm g)) hs
    simp only [MulAut.conj_apply, MulAut.one_apply] at h
    have h' : s * e.symm g = e.symm g * s := by
      calc s * e.symm g = s * e.symm g * s⁻¹ * s := by group
        _ = e.symm g * s := by rw [h]
    have := congrArg e h'
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at this
    exact this.symm
  rw [psl2_center_eq_bot F, Subgroup.mem_bot] at hsZ
  exact e.injective (hsZ.trans (map_one e).symm)

theorem pPrimeCoreOf_autFix_eq_bot_of_outer (e : S ≃* PSL2 F) {r f : ℕ} (hr : r.Prime)
    (hr5 : 5 ≤ r) (hF : Nat.card F = r ^ f) {α : MulAut S} (hα3 : α ^ 3 = 1)
    (hout : ¬ IsInnerAut α) : pPrimeCoreOf 3 (Sec4.autFix α) = ⊥ := by
  set β := MulAut.congr e α with hβ
  have hβ3 : β ^ 3 = 1 := by rw [hβ, ← map_pow, hα3, map_one]
  have hβout : ¬ IsInnerAut β := by rwa [hβ, KFacts.isInnerAut_congr]
  obtain ⟨σ, hσ3, -⟩ := KFacts.exists_fixed_iff_of_isField
    (KFacts.isField_of_pow_three_of_not_inner hβ3 hβout) hβ3
  set q₀ := Nat.card (GH74.GLS.IVK.fixedField σ) with hq₀def
  have hK : Nat.card F = q₀ ^ 3 := by
    have h := GH74.GLS.IVK.fixedField_card_pow σ
    rw [hσ3] at h
    exact h.symm
  have hq₀ : 4 ≤ q₀ := by
    have hdvd : q₀ ∣ r ^ f := by
      rw [← hF, hK]
      exact dvd_pow_self q₀ (by norm_num)
    obtain ⟨k, -, hq⟩ := (Nat.dvd_prime_pow hr).mp hdvd
    rcases k with _ | k
    · exfalso
      rw [pow_zero] at hq
      rw [hq, one_pow] at hK
      have : 1 < Nat.card F := Finite.one_lt_card
      omega
    · rw [hq]
      calc 4 ≤ r := by omega
        _ ≤ r ^ (k + 1) := Nat.le_self_pow (by omega) r
  obtain ⟨hZ, hQ, h3, -⟩ := KFacts.fixedPoints_facts_of_mulEquiv_psl2 e hq₀ hK hα3 hout
  rw [autFix_eq_eqLocus]
  have : IsSimpleGroup (α.toMonoidHom.eqLocus (MonoidHom.id S) ⧸
      Subgroup.center (α.toMonoidHom.eqLocus (MonoidHom.id S))) := hQ.2.1
  haveI : IsSimpleGroup (α.toMonoidHom.eqLocus (MonoidHom.id S)) := MulEquiv.isSimpleGroup
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
  exact pPrimeCoreOf_eq_bot_of_isSimpleGroup h3

theorem mem_zpowers_of_isInnerAut (e : S ≃* PSL2 F) (h3 : ringChar F ≠ 3) (h4 : 4 ≤ Nat.card F)
    {E : Subgroup (MulAut S)} (hE9 : Nat.card E = 9) (hE3 : ∀ ε ∈ E, ε ^ 3 = 1)
    {ε₀ ε₁ : MulAut S} (h₀ : ε₀ ∈ E) (h₀1 : ε₀ ≠ 1) (h₀i : IsInnerAut ε₀) (h₁ : ε₁ ∈ E)
    (h₁i : IsInnerAut ε₁) : ε₁ ∈ Subgroup.zpowers ε₀ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (MulAut S) := finite_mulAut
  by_contra h₁0
  have hEeq := sup_zpowers_eq_of_not_mem hE9 hE3 h₀ h₀1 h₁ h₁0
  have hEI : E ≤ (MulAut.conj : S →* MulAut S).range := by
    rw [← hEeq]
    exact sup_le (Subgroup.zpowers_le.mpr h₀i) (Subgroup.zpowers_le.mpr h₁i)
  have hinj := conj_injective_of_psl2 e
  set P : Subgroup S := E.comap (MulAut.conj : S →* MulAut S) with hP
  have hPcard : Nat.card P = 9 := by
    rw [← hE9]
    have hmap : P.map (MulAut.conj : S →* MulAut S) = E := by
      rw [hP, Subgroup.map_comap_eq, inf_of_le_right hEI]
    rw [← hmap, Subgroup.card_map_of_injective hinj]
  have hP3 : ∀ s ∈ P, s ^ 3 = 1 := by
    intro s hs
    apply hinj
    rw [map_pow, map_one]
    exact hE3 _ hs
  set P' : Subgroup (PSL2 F) := P.map e.toMonoidHom with hP'
  have hP'card : Nat.card P' = 9 := by
    rw [hP', Subgroup.card_map_of_injective e.injective, hPcard]
  have hP'p : IsPGroup 3 P' := IsPGroup.of_card (n := 2) (by rw [hP'card]; norm_num)
  obtain ⟨Q, hQ⟩ := hP'p.exists_le_sylow
  have hQc := KFacts.isCyclic_sylow_three_psl2 h3 h4 Q
  have hP'c : IsCyclic P' := Subgroup.isCyclic_of_le hQ
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := P')
  have hg3 : g ^ 3 = 1 := by
    obtain ⟨_, ⟨s, hs, rfl⟩⟩ := g
    apply Subtype.ext
    change (e s) ^ 3 = 1
    rw [← map_pow, hP3 s hs, map_one]
  have := orderOf_dvd_of_pow_eq_one hg3
  rw [hg, hP'card] at this
  norm_num at this

theorem pPrimeCoreOf_autFix_eq_bot_of_inner_char_three (e : S ≃* PSL2 F) [CharP F 3]
    {ε : MulAut S} (hε1 : ε ≠ 1) (hε3 : ε ^ 3 = 1) (hεi : IsInnerAut ε) :
    pPrimeCoreOf 3 (Sec4.autFix ε) = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨s, rfl⟩ := hεi
  have hinj := conj_injective_of_psl2 e
  have hs1 : s ≠ 1 := fun h => hε1 (by rw [h, map_one])
  have hs3 : s ^ 3 = 1 := hinj (by rw [map_pow, hε3, map_one])
  refine pPrimeCoreOf_eq_bot_of_isPGroup fun x => ⟨1, Subtype.ext ?_⟩
  have hx : s * (x : S) * s⁻¹ = x := Sec4.mem_autFix.mp x.2
  have hxs : s * (x : S) = x * s := by
    calc s * (x : S) = s * x * s⁻¹ * s := by group
      _ = x * s := by rw [hx]
  have hes1 : e s ≠ 1 := fun h => hs1 (e.injective (h.trans (map_one e).symm))
  have hes3 : e s ^ 3 = 1 := by rw [← map_pow, hs3, map_one]
  have hexs : e s * e x = e x * e s := by rw [← map_mul, ← map_mul, hxs]
  have h := CFSG.RankThree.PartOne.K133.psl2_centralizer_pow (by norm_num) (e s) (e x) hes1 hes3
    hexs
  rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
  apply e.injective
  rw [map_pow, h, map_one]

end Model

theorem oddL2Excl : OddL2Excl := by
  intro S _ _ r f hr hr2 hf hS hM h3S E hE9 hE3 hgen
  obtain ⟨-, F, _, _, hF, ⟨e₀⟩⟩ := hM
  set e : S ≃* PSL2 F := SubgroupLists.toPSL2 e₀ with he
  have : Fact r.Prime := ⟨hr⟩
  have : CharP F r := CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow hr hF
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3dvd : 3 ∣ Nat.card S := by
    rw [Nat.card_congr e.toEquiv]
    exact KFacts.three_dvd_card_psl2 F
  have hnt : Nontrivial S := hS.toNontrivial
  set W : MulAut S → Subgroup S := fun ε => pPrimeCoreOf 3 (Sec4.autFix ε) with hW
  have hbot : (∀ ε ∈ E, ε ≠ 1 → W ε = ⊥) → False := by
    intro h
    have hle : (⊤ : Subgroup S) ≤ ⊥ :=
      hgen.trans (iSup_le fun ε => iSup_le fun hε => iSup_le fun hε1 => le_of_eq (h ε hε hε1))
    obtain ⟨a, b, hab⟩ := exists_pair_ne S
    apply hab
    have ha := hle (Subgroup.mem_top a)
    have hb := hle (Subgroup.mem_top b)
    rw [Subgroup.mem_bot] at ha hb
    rw [ha, hb]
  by_cases hr3 : r = 3
  · subst hr3
    by_cases hf3 : 3 ≤ f
    ·
      have hP := h3S ((SubgroupLists.rootGroupPSL2 F).map e.symm.toMonoidHom) ?_
      · rw [Subgroup.card_map_of_injective e.symm.injective, SubgroupLists.card_rootGroupPSL2,
          hF] at hP
        have : 3 ^ 3 ≤ 3 ^ f := Nat.pow_le_pow_right (by norm_num) hf3
        omega
      · refine ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩
        · obtain ⟨_, a, ha, rfl⟩ := x
          obtain ⟨_, b, hb, rfl⟩ := y
          apply Subtype.ext
          change e.symm a * e.symm b = e.symm b * e.symm a
          rw [← map_mul, ← map_mul, SubgroupLists.rootGroupPSL2_comm ha hb]
        · rintro _ ⟨a, ha, rfl⟩
          change (e.symm a) ^ 3 = 1
          rw [← map_pow, SubgroupLists.rootGroupPSL2_pow ha, map_one]
    ·
      refine hbot fun ε hε hε1 => ?_
      have hεi : IsInnerAut ε := by
        by_contra hout
        set β := MulAut.congr e ε with hβ
        have hβ3 : β ^ 3 = 1 := by rw [hβ, ← map_pow, hE3 ε hε, map_one]
        have hβout : ¬ IsInnerAut β := by rwa [hβ, KFacts.isInnerAut_congr]
        obtain ⟨σ, hσ3, -⟩ := KFacts.exists_fixed_iff_of_isField
          (KFacts.isField_of_pow_three_of_not_inner hβ3 hβout) hβ3
        have hK := GH74.GLS.IVK.fixedField_card_pow σ
        rw [hσ3, hF] at hK
        have hdvd : Nat.card (GH74.GLS.IVK.fixedField σ) ∣ 3 ^ f :=
          hK ▸ dvd_pow_self _ (by norm_num)
        obtain ⟨k, -, hq⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
        rw [hq, ← pow_mul] at hK
        have := Nat.pow_right_injective (by norm_num : 2 ≤ 3) hK
        omega
      exact pPrimeCoreOf_autFix_eq_bot_of_inner_char_three e hε1 (hE3 ε hε) hεi
  ·
    have hr5 : 5 ≤ r := by
      have h2 := hr.two_le
      have h4 : r ≠ 4 := by
        rintro rfl
        norm_num at hr
      omega
    have h3F : ringChar F ≠ 3 := by
      rw [ringChar.eq F r]
      exact hr3
    have h4F : 4 ≤ Nat.card F := by
      rw [hF]
      calc 4 ≤ r := by omega
        _ ≤ r ^ f := Nat.le_self_pow (by omega) r
    by_cases hinner : ∃ ε₀ ∈ E, ε₀ ≠ 1 ∧ IsInnerAut ε₀
    · obtain ⟨ε₀, hε₀, hε₀1, hε₀i⟩ := hinner
      have hle : (⊤ : Subgroup S) ≤ W ε₀ := by
        refine hgen.trans (iSup_le fun ε => iSup_le fun hε => iSup_le fun hε1 => ?_)
        by_cases hεi : IsInnerAut ε
        · have hz := mem_zpowers_of_isInnerAut e h3F h4F hE9 hE3 hε₀ hε₀1 hε₀i hε hεi
          change pPrimeCoreOf 3 (Sec4.autFix ε) ≤ pPrimeCoreOf 3 (Sec4.autFix ε₀)
          rw [autFix_eq_of_mem_zpowers (hE3 ε₀ hε₀) hz hε1]
        · change pPrimeCoreOf 3 (Sec4.autFix ε) ≤ _
          rw [pPrimeCoreOf_autFix_eq_bot_of_outer e hr hr5 hF (hE3 ε hε) hεi]
          exact bot_le
      have hc := coprime_card_pPrimeCoreOf 3 (Sec4.autFix ε₀)
      have h1 : Nat.card (⊤ : Subgroup S) ∣ Nat.card (W ε₀) := Subgroup.card_dvd_of_le hle
      rw [Subgroup.card_top] at h1
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hc (h3dvd.trans h1)
    · push Not at hinner
      exact hbot fun ε hε hε1 =>
        pPrimeCoreOf_autFix_eq_bot_of_outer e hr hr5 hF (hE3 ε hε) (hinner ε hε hε1)

end CFSG.RankThree.PartTwo.Sec14.Ronan148T
