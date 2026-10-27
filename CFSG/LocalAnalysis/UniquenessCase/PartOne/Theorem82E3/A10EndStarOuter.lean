module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank618Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC1K327Setup

import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndZWr
import CFSG.GH74.Generic.BProg.B3.S1ThreeSplit
import CFSG.HardMathSupport.Solomon.Coordinator.B3Local
import CFSG.LocalAnalysis.GLTheoremB.PGroupBasics
import CFSG.GroupTheory.CyclicSylowNormalOddComplement
import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentStepFour
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Fischer.Classification.Unitary.Coords
public import CFSG.Fischer.Classification.Unitary.Model
public import CFSG.GH74.GLS.Basic
public import CFSG.LargeExtraspecial.AS35QThModel
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.Helpers
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614PrimeDefs
public import CFSG.Open.GeneralizedFittingSelfCentralizingMilestoneDefs
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.GroupTheory.SteinbergCEQuaternionDihedral
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27
import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28
import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPPrimeCoreBasics
import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
import CFSG.LocalAnalysis.GLTheoremB.SchreierTools

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

@[expose] def KFactAutThreeRankTwo : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X), CFSG.Open.IsKGroup X → L.Normal →
    IsSimpleGroup ↥L → (∃ a b : ↥L, a * b ≠ b * a) →
    Subgroup.centralizer (L : Set X) = ⊥ → CFSG.Open.pRank 3 L = 2 →
    ¬ 81 ∣ Nat.card L → ¬ 81 ∣ Nat.card X

namespace A10Gen

open CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326

variable {X : Type} [Group X] [Finite X]

private lemma isSimpleGroup_of_isComponent_of_center_eq_bot {L : Subgroup X}
    (hL : CFSG.IsComponent L) (hZ : Subgroup.center ↥L = ⊥) : IsSimpleGroup ↥L :=
  (MulEquiv.isSimpleGroup_congr
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)).mp hL.1.2.1

private lemma exists_noncomm_of_isComponent {L : Subgroup X} (hL : CFSG.IsComponent L) :
    ∃ a b : ↥L, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := hL.1.2.2
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  refine ⟨a, b, fun h => hab ?_⟩
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h]

private lemma eq_of_isElemAbelian_card27 {P : Subgroup X}
    (hPZ : Nonempty (↥P ≃* ZWr 1)) {E F : Subgroup X} (hEP : E ≤ P) (hFP : F ≤ P)
    (hE : IsElemAbelian 3 E) (hF : IsElemAbelian 3 F) (hEcard : Nat.card E = 27)
    (hFcard : Nat.card F = 27) : E = F := by
  obtain ⟨e⟩ := hPZ
  have hcard : ∀ S : Subgroup X, S ≤ P →
      Nat.card ((S.subgroupOf P).map e.toMonoidHom) = Nat.card S := by
    intro S hS
    rw [Subgroup.card_map_of_injective (K := S.subgroupOf P) (f := e.toMonoidHom) e.injective]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS).toEquiv
  have hEeq : (E.subgroupOf P).map e.toMonoidHom = omegaBase 1 :=
    unique_omegaBase (n := 1) le_rfl ((hE.subgroupOf P).map e.toMonoidHom)
      (by rw [hcard E hEP, hEcard])
  have hFeq : (F.subgroupOf P).map e.toMonoidHom = omegaBase 1 :=
    unique_omegaBase (n := 1) le_rfl ((hF.subgroupOf P).map e.toMonoidHom)
      (by rw [hcard F hFP, hFcard])
  have hsub : E.subgroupOf P = F.subgroupOf P :=
    Subgroup.map_injective e.injective (hEeq.trans hFeq.symm)
  calc E = (E.subgroupOf P).map P.subtype := (Subgroup.map_subgroupOf_eq_of_le hEP).symm
    _ = (F.subgroupOf P).map P.subtype := by rw [hsub]
    _ = F := Subgroup.map_subgroupOf_eq_of_le hFP

private lemma not_isCyclic_inf_of_zwr {P A T : Subgroup X}
    (hPZ : Nonempty (↥P ≃* ZWr 1)) (hA : IsElemAbelian 3 A) (hA27 : Nat.card A = 27)
    (hAP : A ≤ P) (hTP : T ≤ P) (hTN : P ≤ Subgroup.normalizer (T : Set X))
    (hZPcard : Nat.card (Subgroup.center ↥P) = 3) (hT9 : 9 ≤ Nat.card T) :
    ¬ IsCyclic ↥(T ⊓ A) := by
  intro hcyc
  have hcent : T ≤ Subgroup.centralizer (P : Set X) :=
    le_centralizer_of_isCyclic_inf_of_zwr hPZ hA hA27 hAP hTP hTN hcyc
  have hTZP : T.subgroupOf P ≤ Subgroup.center ↥P := by
    intro t ht
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have hcomm : (t : X) ∈ Subgroup.centralizer (P : Set X) :=
      hcent (Subgroup.mem_subgroupOf.mp ht)
    rw [Subgroup.mem_centralizer_iff] at hcomm
    simpa using hcomm (y : X) y.2
  have hlt : Nat.card ↥T ≤ 3 := by
    calc Nat.card ↥T = Nat.card ↥(T.subgroupOf P) :=
          (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTP).toEquiv).symm
      _ ≤ Nat.card (Subgroup.center ↥P) := Subgroup.card_le_of_le hTZP
      _ = 3 := hZPcard
  omega

private lemma pRank_le_two_of_isSylow {P A T : Subgroup X} {L : Subgroup X}
    (hPZ : Nonempty (↥P ≃* ZWr 1)) (hA : IsElemAbelian 3 A) (hA27 : Nat.card A = 27)
    (hAP : A ≤ P) (hTP : T ≤ P) (hTsyl : CFSG.ABGLocalTools.IsSylowOf 3 T L)
    (hnotA : ¬ A ≤ L) : CFSG.Open.pRank 3 L ≤ 2 := by
  have hprankT : CFSG.Open.pRank 3 T ≤ 2 := by
    refine CFSG.SectionRank.pRank_le (p := 3) (by norm_num) (H := T) (k := 2) ?_
    intro E hET hE
    by_contra hgt
    push Not at hgt
    have hEdvd : 3 ^ 3 ∣ Nat.card E := by
      obtain ⟨m, hm⟩ := hE.isPGroup.exists_card_eq
      have hm3 : 3 ≤ m := by
        rw [hm] at hgt
        have h23 : 2 < m := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).mp hgt
        omega
      rw [hm]
      exact Nat.pow_dvd_pow 3 hm3
    obtain ⟨K, hKE, hKea, hKcard⟩ :=
      CFSG.LocalAnalysis.GLTheoremB.exists_le_isElemAbelian_card (p := 3) hE hEdvd
    have hKP : K ≤ P := hKE.trans (hET.trans hTP)
    have hKA : K = A := eq_of_isElemAbelian_card27 hPZ hKP hAP hKea hA hKcard hA27
    exact hnotA (hKA ▸ (hKE.trans (hET.trans hTsyl.le)))
  rw [← CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent.pRank_eq_of_isSylowOf hTsyl]
  exact hprankT

private lemma two_le_pRank_of_not_isCyclic {A T L : Subgroup X}
    (hA : IsElemAbelian 3 A) (hTL : T ≤ L) (hZnot : ¬ IsCyclic ↥(T ⊓ A)) :
    2 ≤ CFSG.Open.pRank 3 L := by
  have hZea : IsElemAbelian 3 (T ⊓ A) := hA.mono inf_le_right
  obtain ⟨m, hm⟩ := hZea.isPGroup.exists_card_eq
  have hm2 : 2 ≤ m := by
    by_contra h
    have hm1 : m ≤ 1 := by omega
    apply hZnot
    refine isCyclic_of_card_dvd_prime (p := 3) ?_
    rw [hm]
    exact Nat.pow_dvd_pow 3 hm1
  have hZdvd : 3 ^ 2 ∣ Nat.card ↥(T ⊓ A) := by
    rw [hm]
    exact Nat.pow_dvd_pow 3 hm2
  obtain ⟨E, hEZ, hEea, hEcard⟩ :=
    CFSG.LocalAnalysis.GLTheoremB.exists_le_isElemAbelian_card (p := 3) hZea hZdvd
  exact CFSG.SectionRank.le_pRank (p := 3) (by norm_num)
    (hEZ.trans (inf_le_left.trans hTL)) hEea hEcard

private lemma not_eightyone_dvd_card_of_isSylow {L T : Subgroup X}
    (hTsyl : CFSG.ABGLocalTools.IsSylowOf 3 T L)
    (hTcard : Nat.card T = 9 ∨ Nat.card T = 27) : ¬ 81 ∣ Nat.card L := by
  intro h81
  have hfac := hTsyl.card_eq
  have h81' : 3 ^ 4 ∣ Nat.card ↥L := by
    rw [show (3 : ℕ) ^ 4 = 81 by norm_num]
    exact h81
  have h4 : 4 ≤ (Nat.card ↥L).factorization 3 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three
      (Nat.card_pos (α := ↥L)).ne').mp h81'
  have hdvdT : 3 ^ 4 ∣ Nat.card ↥T := by
    rw [hfac]
    exact Nat.pow_dvd_pow 3 h4
  rcases hTcard with h | h <;> rw [h] at hdvdT <;> norm_num at hdvdT

private lemma le_of_card_inf_eq_three (hO3 : RankThreeTheoremC.KFactOutThreePrimeSimple)
    {P L T : Subgroup X} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P ⊤)
    (hKg : CFSG.Open.IsKGroup X) (hLn : L.Normal) (hLsimple : IsSimpleGroup ↥L)
    (hLnonab : ∃ a b : ↥L, a * b ≠ b * a)
    (hC : Subgroup.centralizer (L : Set X) = ⊥)
    (hTsyl : CFSG.ABGLocalTools.IsSylowOf 3 T L) (hTP : T ≤ P)
    (hPcard : Nat.card ↥P = 81) (hTcard : Nat.card T = 3) : P ≤ L := by
  haveI : L.Normal := hLn
  intro x hx
  have hK : CFSG.IsKGroup ↥L :=
    CFSG.IsKGroup.subgroup
      (CFSG.HardMathSupport.Solomon.Coordinator.isKGroup_of_openIsKGroup hKg) L
  obtain ⟨Q, hQ⟩ := hTsyl.exists_sylow_eq_subgroupOf
  have hQcard : Nat.card ↥Q = 3 := by
    change Nat.card ↥(Q : Subgroup ↥L) = 3
    rw [hQ]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTsyl.le).toEquiv]
    exact hTcard
  have hx81 : x ^ (3 ^ 4) = 1 := by
    have h1 : (⟨x, hx⟩ : ↥P) ^ (3 ^ 4) = 1 := by
      have h := pow_card_eq_one' (x := (⟨x, hx⟩ : ↥P))
      rw [hPcard] at h
      simpa using h
    simpa using congrArg Subtype.val h1
  have hφ : ∃ n : ℕ, (MulAut.conjNormal (H := L) x) ^ (3 ^ n) = 1 := by
    refine ⟨4, ?_⟩
    rw [← map_pow, hx81, map_one]
  obtain ⟨k, hk⟩ := hO3 ↥L hK hLsimple hLnonab ⟨Q, hQcard, Q.not_dvd_index⟩
    (MulAut.conjNormal (H := L) x) hφ
  have hxk : x = (k : X) := by
    have hmem : (k : X)⁻¹ * x ∈ Subgroup.centralizer (L : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hconj : ((MulAut.conjNormal (H := L) x) ⟨y, hy⟩ : ↥L) = (MulAut.conj k) ⟨y, hy⟩ := by
        rw [hk]
      have h1 : x * y * x⁻¹ = (k : X) * y * (k : X)⁻¹ := by
        have := congrArg Subtype.val hconj
        simpa [MulAut.conjNormal_apply, MulAut.conj_apply] using this
      calc y * ((k : X)⁻¹ * x) = (k : X)⁻¹ * ((k : X) * y * (k : X)⁻¹) * x := by group
        _ = (k : X)⁻¹ * (x * y * x⁻¹) * x := by rw [h1]
        _ = ((k : X)⁻¹ * x) * y := by group
    rw [hC, Subgroup.mem_bot] at hmem
    calc x = (k : X) * ((k : X)⁻¹ * x) := by group
      _ = (k : X) := by rw [hmem, mul_one]
  rw [hxk]
  exact k.2

private lemma false_of_card_inf_eq_nine_or_twentyseven (hA3 : KFactAutThreeRankTwo)
    {P A L T : Subgroup X} (hX : UC22.InS3.UC327.Hyp327 X P A)
    (hPZ : Nonempty (↥P ≃* ZWr 1)) (hLn : L.Normal) (hLsimple : IsSimpleGroup ↥L)
    (hLnonab : ∃ a b : ↥L, a * b ≠ b * a)
    (hC : Subgroup.centralizer (L : Set X) = ⊥) (hAP : A ≤ P)
    (hTsyl : CFSG.ABGLocalTools.IsSylowOf 3 T L) (hTP : T ≤ P)
    (hTN : P ≤ Subgroup.normalizer (T : Set X))
    (hPcard : Nat.card ↥P = 81) (hZPcard : Nat.card (Subgroup.center ↥P) = 3)
    (hTcard : Nat.card T = 9 ∨ Nat.card T = 27) (hnotA : ¬ A ≤ L) : False := by
  have hT9 : 9 ≤ Nat.card T := by rcases hTcard with h | h <;> omega
  have hZnot : ¬ IsCyclic ↥(T ⊓ A) :=
    not_isCyclic_inf_of_zwr hPZ hX.elem hX.card hAP hTP hTN hZPcard hT9
  have hle2 : CFSG.Open.pRank 3 L ≤ 2 :=
    pRank_le_two_of_isSylow hPZ hX.elem hX.card hAP hTP hTsyl hnotA
  have hge2 : 2 ≤ CFSG.Open.pRank 3 L := two_le_pRank_of_not_isCyclic hX.elem hTsyl.le hZnot
  have hprank : CFSG.Open.pRank 3 L = 2 := le_antisymm hle2 hge2
  have hnot81L := not_eightyone_dvd_card_of_isSylow hTsyl hTcard
  have hnot81X := hA3 X L hX.kgroup hLn hLsimple hLnonab hC hprank hnot81L
  apply hnot81X
  have hdvd := Subgroup.card_dvd_of_le (le_top : P ≤ (⊤ : Subgroup X))
  rw [hPcard, Subgroup.card_top] at hdvd
  exact hdvd

private lemma isSylow_inf_of_normal {P L : Subgroup X}
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P ⊤) (hLn : L.Normal) :
    CFSG.ABGLocalTools.IsSylowOf 3 (P ⊓ L) L ∧
      P ≤ Subgroup.normalizer ((P ⊓ L : Subgroup X) : Set X) := by
  refine ⟨?_, ?_⟩
  · exact hP.inf_of_le_normalizer le_top
      (le_of_eq (Subgroup.normalizer_eq_top_iff.mpr hLn).symm)
  · have hTP : P ⊓ L ≤ P := inf_le_left
    have hsub : (P ⊓ L).subgroupOf P = L.subgroupOf P := by
      ext x
      simp [Subgroup.mem_inf, and_comm]
    have hN : ((P ⊓ L).subgroupOf P).Normal := by
      rw [hsub]
      exact hLn.subgroupOf P
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hTP).mp hN

private lemma card_inf_ne_bot {P L : Subgroup X} (h3' : CFSG.pPrimeCore 3 X = ⊥)
    (hLn : L.Normal) (hL : CFSG.IsComponent L)
    (hTsyl : CFSG.ABGLocalTools.IsSylowOf 3 (P ⊓ L) L) : P ⊓ L ≠ ⊥ := by
  intro hbot
  have hfac := hTsyl.card_eq
  rw [hbot, Subgroup.card_bot] at hfac
  have hf0 : (Nat.card ↥L).factorization 3 = 0 := by
    rcases (Nat.pow_eq_one.mp hfac.symm) with h | h
    · norm_num at h
    · exact h
  have hcop : Nat.Coprime 3 (Nat.card ↥L) := by
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    intro hdvd
    have hpos : 0 < (Nat.card ↥L).factorization 3 :=
      Nat.Prime.factorization_pos_of_dvd Nat.prime_three (Nat.card_pos (α := ↥L)).ne' hdvd
    omega
  have hLbot : L = ⊥ := by
    have hle := CFSG.le_pPrimeCore_of_normal_coprime (p := 3) hLn hcop
    rw [h3'] at hle
    exact le_bot_iff.mp hle
  exact (Subgroup.nontrivial_iff_ne_bot L).mp
    (CFSG.LocalCores.isQuasisimple_nontrivial hL.1) hLbot

private lemma card_inf_eq_three_or_nine_or_twentyseven {P L : Subgroup X}
    (hTP : P ⊓ L ≤ P) (hPcard : Nat.card ↥P = 81) (hne : P ⊓ L ≠ ⊥)
    (hneP : P ⊓ L ≠ P) :
    Nat.card ↥(P ⊓ L) = 3 ∨ Nat.card ↥(P ⊓ L) = 9 ∨ Nat.card ↥(P ⊓ L) = 27 := by
  have hdvd81 : Nat.card ↥(P ⊓ L) ∣ 81 := by
    have h := Subgroup.card_dvd_of_le hTP
    rwa [hPcard] at h
  have hdvd : Nat.card ↥(P ⊓ L) ∣ 3 ^ 4 := by
    rw [show (3 : ℕ) ^ 4 = 81 by norm_num]
    exact hdvd81
  obtain ⟨k, hk4, hkcard⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  have hk0 : k ≠ 0 := by
    intro hk
    apply hne
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hcard1 : Nat.card ↥(P ⊓ L) = 1 := by rw [hkcard, hk]; simp
    have hsub : Subsingleton ↥(P ⊓ L) := (Nat.card_eq_one_iff_unique.mp hcard1).1
    exact congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : ↥(P ⊓ L)) 1)
  have hk4' : k ≠ 4 := by
    intro hk
    apply hneP
    refine Subgroup.eq_of_le_of_card_ge hTP ?_
    rw [hPcard, hkcard, hk]
    norm_num
  have hk13 : k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hk13 with hk | hk | hk
  · left; rw [hkcard, hk]; norm_num
  · right; left; rw [hkcard, hk]; norm_num
  · right; right; rw [hkcard, hk]; norm_num

theorem le_of_centralizer_eq_bot (hO3 : RankThreeTheoremC.KFactOutThreePrimeSimple)
    (hA3 : KFactAutThreeRankTwo) {P A L : Subgroup X} (hX : UC22.InS3.UC327.Hyp327 X P A)
    (hPZ : Nonempty (↥P ≃* UC22.InS3.UC326.ZWr 1)) (h3' : CFSG.pPrimeCore 3 X = ⊥)
    (hL : CFSG.IsComponent L) (hC : Subgroup.centralizer (L : Set X) = ⊥) : A ≤ L := by
  classical
  obtain ⟨e⟩ := hPZ
  have hPZ' : Nonempty (↥P ≃* UC22.InS3.UC326.ZWr 1) := ⟨e⟩
  have hPcard : Nat.card ↥P = 81 := by
    have h := (zwr_card_center (n := 1) le_rfl e).1
    simpa using h
  have hZPcard : Nat.card (Subgroup.center ↥P) = 3 := by
    have h := (zwr_card_center (n := 1) le_rfl e).2.2
    simpa using h
  have hAP : A ≤ P := hX.jA ▸ Subgroup.map_subtype_le _
  have hLn : L.Normal :=
    CFSG.GH74.Generic.BProg.B3.S1Three.normal_of_centralizer_le hL (z := 1) fun w hw => by
      rw [hC, Subgroup.mem_bot] at hw
      exact Or.inl hw
  have hLZ : Subgroup.center ↥L = ⊥ := by
    have h := CFSG.GroupTheory.inf_centralizer_eq_map_center L
    rw [hC, inf_bot_eq] at h
    exact (Subgroup.map_eq_bot_iff_of_injective (Subgroup.center ↥L) (f := L.subtype)
      L.subtype_injective).mp h.symm
  have hLsimple : IsSimpleGroup ↥L := isSimpleGroup_of_isComponent_of_center_eq_bot hL hLZ
  have hLnonab : ∃ a b : ↥L, a * b ≠ b * a := exists_noncomm_of_isComponent hL
  set T : Subgroup X := P ⊓ L with hTdef
  have hTP : T ≤ P := inf_le_left
  have hTL : T ≤ L := inf_le_right
  obtain ⟨hTsyl, hTN⟩ := isSylow_inf_of_normal (P := P) (L := L) hX.sylow hLn
  have hTne : T ≠ ⊥ := card_inf_ne_bot (P := P) (L := L) h3' hLn hL hTsyl
  by_contra hnotA
  have hTneP : T ≠ P := by
    intro hTPeq
    exact hnotA (hAP.trans (by rw [← hTPeq]; exact hTL))
  have hcases : Nat.card ↥T = 3 ∨ Nat.card ↥T = 9 ∨ Nat.card ↥T = 27 :=
    card_inf_eq_three_or_nine_or_twentyseven (P := P) (L := L) hTP hPcard hTne hTneP
  rcases hcases with h3 | h9 | h27
  · exact hnotA (hAP.trans (le_of_card_inf_eq_three hO3 hX.sylow hX.kgroup hLn hLsimple
      hLnonab hC hTsyl hTP hPcard h3))
  · exact false_of_card_inf_eq_nine_or_twentyseven hA3 hX hPZ' hLn hLsimple hLnonab hC hAP
      hTsyl hTP hTN hPcard hZPcard (Or.inl h9) hnotA
  · exact false_of_card_inf_eq_nine_or_twentyseven hA3 hX hPZ' hLn hLsimple hLnonab hC hAP
      hTsyl hTP hTN hPcard hZPcard (Or.inr h27) hnotA

end A10Gen

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
