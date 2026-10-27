module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermLabelDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBRes
public import Certificates.Certificate13657
import CFSG.LocalAnalysis.StandardType.GGTPNThmRACore
import CFSG.LocalAnalysis.StandardType.GGTPNNarrowC6
import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylInputHolds
import CFSG.GH74.Generic.S1.RCard
import CFSG.LinearAlgebra.LinearGroups.UnitaryScalarKernel
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldUnitary

public section

namespace CFSG.StandardType

open CFSG.Assembly
open CFSG.Open

private theorem prime_three_le {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : 3 ≤ p := by
  have := hp.two_le
  omega

private theorem prime_dvd_pow_sub_one_of_not_dvd {p q : ℕ} (hp : p.Prime) (hq0 : 1 ≤ q)
    (hpq : ¬ p ∣ q) : p ∣ q ^ (p - 1) - 1 := by
  have hcop : Nat.Coprime q p := Nat.Coprime.symm ((hp.coprime_iff_not_dvd).mpr hpq)
  have hmod := Nat.ModEq.pow_card_sub_one_eq_one hp hcop
  have h' := hmod.dvd
  have hcast : ((q ^ (p - 1) : ℕ) : ℤ) = (q : ℤ) ^ (p - 1) := by
    rw [Nat.cast_pow]
  rw [hcast] at h'
  norm_num at h'
  have hz : (p : ℤ) ∣ ((q : ℤ) ^ (p - 1) - 1) := by
    have hneg : (p : ℤ) ∣ -((q : ℤ) ^ (p - 1) - 1) := by
      have hh : (1 : ℤ) - (q : ℤ) ^ (p - 1) = -((q : ℤ) ^ (p - 1) - 1) := by ring
      rw [hh] at h'
      exact h'
    exact (dvd_neg).mp hneg
  have hpos : 1 ≤ q ^ (p - 1) := Nat.one_le_pow _ _ (by omega)
  have hnat : ((q ^ (p - 1) - 1 : ℕ) : ℤ) = (q : ℤ) ^ (p - 1) - 1 := by
    rw [Nat.cast_sub hpos, Nat.cast_pow, Nat.cast_one]
  rw [← hnat] at hz
  exact Int.natCast_dvd_natCast.mp hz

private theorem ggLabelIso_eq_of_tagA_or_twA {lab lab' : LargeEvenLabel}
    (h : GGLabelIso lab lab') (ht : lab.tag = .A ∨ lab.tag = .twA)
    (ht' : lab'.tag = .A ∨ lab'.tag = .twA) : lab = lab' := by
  obtain ⟨t, r, m⟩ := lab
  obtain ⟨t', r', m'⟩ := lab'
  simp only [GGLabelIso, LargeEvenLabel.tag, LargeEvenLabel.rank,
    LargeEvenLabel.n] at h ht ht' ⊢
  rcases h with h | ⟨hBC, -, -, -⟩ | h | h | h | h | h | h
  · exact h
  · rcases ht with rfl | rfl <;> simp at hBC
  · rcases ht with rfl | rfl <;> simp at h
  · rcases ht' with rfl | rfl <;> simp at h
  · rcases ht with rfl | rfl <;> simp at h
  · rcases ht' with rfl | rfl <;> simp at h
  · rcases ht with rfl | rfl <;> simp at h
  · rcases ht' with rfl | rfl <;> simp at h

private theorem prime_dvd_card_projectiveSL_of_rank_le {F : Type} [Field F] [Finite F]
    {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 3 ≤ n) (hle : p ≤ n + 1)
    (hpF : ¬ p ∣ Nat.card F) :
    p ∣ Nat.card (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL n F) := by
  refine CFSG.HardMathSupport.Timmesfeld.LocalTwo.dvd_card_projectiveSL_of_dvd_pow_sub_one
    hp hn ?_ ?_ (prime_dvd_pow_sub_one_of_not_dvd hp ?_ hpF)
  · exact Nat.le_sub_one_of_lt hp.one_lt
  · simpa using Nat.sub_le_sub_right hle 1
  · exact Nat.succ_le_of_lt Nat.card_pos

private theorem prime_dvd_card_of_hasLabel_linear_le {H : Type} [Group H] {p r e : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hr : 2 ≤ r) (hle : p ≤ r + 2)
    (hpnd : ¬ p ∣ r + 1) (hH : GGHasLabel ⟨.A, r, e⟩ H) : p ∣ Nat.card H := by
  obtain ⟨F, hField, hFinite, hF, ⟨eH⟩⟩ := hH
  let : Field F := hField
  let : Finite F := hFinite
  have : CharP F 2 := charP_two_of_card hF
  have hpF : ¬ p ∣ Nat.card F := by
    rw [hF]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
  have hdiv := prime_dvd_card_projectiveSL_of_rank_le hp hp2 (n := r + 1) (by omega)
    (by omega) hpF
  rw [Nat.card_congr eH.toEquiv, CFSG.Assembly.largeEvenSLGroup_eq_statedSL,
    ← Nat.card_congr
      (CFSG.CGT.Timmesfeld75.projectiveSLMulEquivStatedProj (r + 1) F).toEquiv]
  exact hdiv

private theorem prime_dvd_card_of_hasLabel_unitary_le {H : Type} [Group H] {p r e : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hr : 2 ≤ r) (hle : p ≤ r + 2)
    (hpnd : ¬ p ∣ r + 1) (he : 1 ≤ e)
    (hH : GGHasLabel ⟨.twA, r, e⟩ H) : p ∣ Nat.card H := by
  dsimp only [GGHasLabel, LargeEvenRawDatum] at hH
  obtain ⟨F, hField, hFinite, hF, ⟨eH⟩⟩ := hH
  let : Field F := hField
  let : Finite F := hFinite
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 e F :=
    unitaryFieldData_of_card he hF
  have hp2e : ¬ p ∣ 2 ^ e := by
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
  have hq : p ∣ (2 ^ e) ^ (p - 1) - 1 :=
    prime_dvd_pow_sub_one_of_not_dvd hp Nat.one_le_two_pow hp2e
  have hcardSU := CFSG.GH74.Generic.S1.rcard_card_statedSU hU (n := r + 1)
    (by exact Nat.succ_le_succ (Nat.zero_le r))
  have hqZ : (p : ℤ) ∣ (((2 ^ e : ℕ) : ℤ) ^ (p - 1) - 1) := by
    have hpos2 : 1 ≤ (2 ^ e) ^ (p - 1) := Nat.one_le_pow _ _ (Nat.two_pow_pos e)
    have hcast : (((2 ^ e) ^ (p - 1) - 1 : ℕ) : ℤ) =
        ((2 ^ e : ℕ) : ℤ) ^ (p - 1) - 1 := by
      rw [Nat.cast_sub hpos2, Nat.cast_pow, Nat.cast_one]
    rw [← hcast]
    exact_mod_cast hq
  have hpSU : p ∣ Nat.card (StatedSU (r + 1) (2 ^ e) F) := by
    have hp3 : 3 ≤ p := prime_three_le hp hp2
    have hmem : p - 1 ∈ Finset.Icc 2 (r + 1) :=
      Finset.mem_Icc.2 ⟨Nat.le_sub_one_of_lt (Nat.lt_of_succ_le hp3),
        by simpa using Nat.sub_le_sub_right hle 1⟩
    have hInt : (p : ℤ) ∣
        ∏ i ∈ Finset.Icc 2 (r + 1), (((2 ^ e : ℕ) : ℤ) ^ i - (-1) ^ i) := by
      refine (show (p : ℤ) ∣
        (((2 ^ e : ℕ) : ℤ) ^ (p - 1) - (-1 : ℤ) ^ (p - 1)) from ?_).trans
        (Finset.dvd_prod_of_mem _ hmem)
      have h1 : (-1 : ℤ) ^ (p - 1) = 1 := by
        obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
        have hk' : p - 1 = 2 * k := by omega
        rw [hk', pow_mul]
        norm_num
      rw [h1]
      exact hqZ
    have hInt2 : (p : ℤ) ∣ (Nat.card (StatedSU (r + 1) (2 ^ e) F) : ℤ) := by
      rw [hcardSU]
      exact dvd_mul_of_dvd_right hInt _
    exact_mod_cast hInt2
  have hquot : Nat.card (StatedSU (r + 1) (2 ^ e) F) =
      Nat.card (StatedProj (StatedSU (r + 1) (2 ^ e) F)) *
        Nat.card ((StatedScalars (Fin (r + 1)) F).subgroupOf
          (StatedSU (r + 1) (2 ^ e) F)) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hscal : ¬ p ∣ Nat.card ((StatedScalars (Fin (r + 1)) F).subgroupOf
      (StatedSU (r + 1) (2 ^ e) F)) := by
    refine CFSG.Open.StatedAPI.not_dvd_card_statedScalars_subgroupOf
      (StatedSU (r + 1) (2 ^ e) F) hp hpnd ?_
    intro c hc
    exact ((CFSG.LinearGroups.scalar_mem_statedSU_iff (p := 2) (f := e) Nat.prime_two hF
      (n := r + 1) (by omega) c).mp hc).1
  have hproj : p ∣ Nat.card (StatedProj (StatedSU (r + 1) (2 ^ e) F)) := by
    rw [hquot] at hpSU
    exact (hp.dvd_mul.mp hpSU).resolve_right hscal
  rw [Nat.card_congr eH.toEquiv, CFSG.Assembly.largeEvenSUGroup_eq_statedSU]
  exact hproj

private theorem prime_dvd_card_of_hasLabel_perm {H : Type} [Group H] {p N e : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hN : 4 ≤ N) (hpN : p ∣ N)
    {t : LargeEvenLieTag} (ht : t = .A ∨ t = .twA)
    (hΛJ : LargeEvenInLambda2 ⟨t, N - 2, e⟩)
    (hH : GGHasLabel ⟨t, N - 2, e⟩ H) : p ∣ Nat.card H := by
  have hr : 2 ≤ N - 2 := by omega
  have hle : p ≤ (N - 2) + 2 := by
    have hpos : 0 < N := by omega
    have := Nat.le_of_dvd hpos hpN
    omega
  have hpnd : ¬ p ∣ (N - 2) + 1 := by
    intro h
    have h1 : p ∣ N - ((N - 2) + 1) := Nat.dvd_sub hpN h
    have h2 : N - ((N - 2) + 1) = 1 := by omega
    rw [h2] at h1
    exact hp.not_dvd_one h1
  rcases ht with hA | htwA
  · subst hA
    exact prime_dvd_card_of_hasLabel_linear_le hp hp2 hr hle hpnd hH
  · subst htwA
    exact prime_dvd_card_of_hasLabel_unitary_le hp hp2 hr hle hpnd hΛJ.1 hH

private theorem not_div_sub_one_eq_sub_two {p N : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hN : 4 ≤ N) (h : N / p - 1 = N - 2) : False := by
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hNp : N / p = N - 1 := by omega
  have hmul : p * (N / p) ≤ N := by
    rw [mul_comm]
    exact Nat.div_mul_le_self N p
  rw [hNp] at hmul
  have h3 : 3 * (N - 1) ≤ N := by
    calc 3 * (N - 1) ≤ p * (N - 1) := Nat.mul_le_mul_right _ hp3
      _ ≤ N := hmul
  omega

private theorem perm_label_eq_of_split {J : Type} [Group J] {n e a q : ℕ}
    {tK t : LargeEvenLieTag} (hrig : GGLabelRigidInput)
    (htK : tK = .A ∨ tK = .twA) (ht : t = .A ∨ t = .twA)
    (hΛO : LargeEvenInLambda2 ⟨tK, a - 1, q⟩)
    (hΛJ : LargeEvenInLambda2 ⟨t, n - 2, e⟩)
    (hhasO : GGHasLabel ⟨tK, a - 1, q⟩ (J ⧸ Subgroup.center J))
    (hJ : GGHasLabel ⟨t, n - 2, e⟩ (J ⧸ Subgroup.center J)) : tK = t ∧ q = e := by
  have hiso := hrig _ _ _ hΛO hΛJ hhasO hJ
  have heq := ggLabelIso_eq_of_tagA_or_twA hiso htK ht
  exact ⟨by simpa using congrArg LargeEvenLabel.tag heq,
    by simpa using congrArg LargeEvenLabel.n heq⟩

private theorem false_of_label_iso_rank_one {J : Type} [Group J] {n e q : ℕ}
    {t : LargeEvenLieTag} (hrig : GGLabelRigidInput) (hn : 4 ≤ n)
    (ht : t = .A ∨ t = .twA)
    (hΛO : LargeEvenInLambda2 (⟨.A, 1, q⟩ : LargeEvenLabel))
    (hΛJ : LargeEvenInLambda2 ⟨t, n - 2, e⟩)
    (hhasO : GGHasLabel (⟨.A, 1, q⟩ : LargeEvenLabel) (J ⧸ Subgroup.center J))
    (hJ : GGHasLabel ⟨t, n - 2, e⟩ (J ⧸ Subgroup.center J)) : False := by
  have hiso := hrig _ _ _ hΛO hΛJ hhasO hJ
  have heq := ggLabelIso_eq_of_tagA_or_twA hiso (Or.inl rfl) ht
  have hrank : (1 : ℕ) = n - 2 := by
    simpa using congrArg LargeEvenLabel.rank heq
  exact absurd hrank (by omega)

private theorem false_of_label_iso_nonSplit {J : Type} [Group J] {p n e N q : ℕ}
    {tO t : LargeEvenLieTag} (hrig : GGLabelRigidInput) (hp : p.Prime) (hp2 : p ≠ 2)
    (hn : 4 ≤ n) (hN : N = n) (htO : tO = .A ∨ tO = .twA)
    (ht : t = .A ∨ t = .twA)
    (hΛO : LargeEvenInLambda2 ⟨tO, N / p - 1, p * q⟩)
    (hΛJ : LargeEvenInLambda2 ⟨t, n - 2, e⟩)
    (hhasO : GGHasLabel ⟨tO, N / p - 1, p * q⟩ (J ⧸ Subgroup.center J))
    (hJ : GGHasLabel ⟨t, n - 2, e⟩ (J ⧸ Subgroup.center J)) : False := by
  have hiso := hrig _ _ _ hΛO hΛJ hhasO hJ
  have heq := ggLabelIso_eq_of_tagA_or_twA hiso htO ht
  have hrank : N / p - 1 = n - 2 := by
    simpa using congrArg LargeEvenLabel.rank heq
  rw [hN] at hrank
  exact not_div_sub_one_eq_sub_two hp hp2 hn hrank


section Label


theorem GGSecFiveRouteCfg.permNbr_field_of_RA {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {n : ℕ} (hn : 4 ≤ n) {K : Subgroup G}
    (hK𝒦 : K ∈ 𝒦) {labK : LargeEvenLabel} (hΛK : LargeEvenInLambda2 labK)
    (hhasK : GGHasLabel labK (↥K ⧸ Subgroup.center ↥K)) (hpermK : GGSecFiveBPermLabel n p labK)
    (hRA : p ∣ n) {t : LargeEvenLieTag} {e : ℕ} (ht : t = .A ∨ t = .twA)
    (hΛJ : LargeEvenInLambda2 ⟨t, n - 2, e⟩)
    (hJ : GGHasLabel ⟨t, n - 2, e⟩ (↥J ⧸ Subgroup.center ↥J)) :
    labK.tag = t ∧ labK.n = e := by
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hR
  have hc : GGConfig p B Bs x L D J := hR.1.1
  have hL : GGInnerDiagOn Bs L := hR.1.2.2.1.1
  obtain ⟨y, hnb⟩ := hR.2.2.2.1.2 K hK𝒦
  have hK : GGInnerDiagOn Bs K := hR.1.2.2.1.2 y K hnb
  have hJZ : p ∣ Nat.card (↥J ⧸ Subgroup.center ↥J) :=
    prime_dvd_card_of_hasLabel_perm hp hp2 hn hRA ht hΛJ hJ
  have hpJ : p ∣ Nat.card J := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥J)]
    exact dvd_mul_of_dvd_left hJZ _
  have hJK : J ≤ K :=
    le_of_ggNbr ggLBalanceInput_holds hc.1 hc.2.2 hpJ hnb
  obtain ⟨hN, hx, hBasic⟩ :=
    ggTPNBasicB_of_config hc hL hK hnb hJK hpJ ggLBalanceInput_holds
  obtain ⟨hLoc, -, -, -, -, -, hOnly, hMark⟩ := hBasic
  have hlabKN : labK.rank + 1 = n := by
    rcases hpermK with ⟨-, hrank, -⟩ | ⟨-, hrank, -⟩ <;> omega
  have hkac : GGKacRA labK p := by
    rcases hpermK with ⟨htag, -, hq⟩ | ⟨htag, -, hq⟩
    · exact Or.inl ⟨htag, by rwa [hlabKN], hq⟩
    · exact Or.inr ⟨htag, by rwa [hlabKN], hq⟩
  have hMark' : GGTPNMarked p (fun _ lab => lab = labK) (ggAutsOf K Bs hN) :=
    ggTPNMarked_eq_of_ggKacRA ggLabelRigidInput_holds hp hMark hΛK hkac hhasK
  have hRA' := split_or_fieldType_of_ggKacRA hp hLoc hOnly hkac hMark'
  have htransport : ∀ {lab : LargeEvenLabel},
      GGHasLabel lab (↥(J.subgroupOf K) ⧸ Subgroup.center ↥(J.subgroupOf K)) →
      GGHasLabel lab (↥J ⧸ Subgroup.center ↥J) := fun h =>
    ggHasLabel_of_mulEquiv
      (QuotientGroup.congr _ _ (Subgroup.subgroupOfEquivOfLe hJK)
        (Subgroup.map_center_eq _)) h
  rcases hRA' with ⟨a, ds, hsum, hne, hlen, hmem, hbr⟩ | ⟨hge2, hcardA, hbr⟩
  · rcases hbr with ⟨hΛO, hhasO⟩ | ⟨-, -, hΛO, hhasO⟩
    · have htO : (⟨labK.tag, a - 1, labK.n⟩ : LargeEvenLabel).tag = .A ∨
          (⟨labK.tag, a - 1, labK.n⟩ : LargeEvenLabel).tag = .twA := by
        rcases hpermK with ⟨htag, -, -⟩ | ⟨htag, -, -⟩ <;> rw [htag] <;> simp
      exact perm_label_eq_of_split ggLabelRigidInput_holds htO ht hΛO hΛJ
        (htransport hhasO) hJ
    · exact (false_of_label_iso_rank_one ggLabelRigidInput_holds hn ht hΛO hΛJ
        (htransport hhasO) hJ).elim
  · rcases hbr with ⟨-, hΛO, hhasO⟩ | ⟨-, -, hΛO, hhasO⟩
    · exact (false_of_label_iso_nonSplit ggLabelRigidInput_holds hp hp2 hn hlabKN
        (Or.inl rfl) ht hΛO hΛJ (htransport hhasO) hJ).elim
    · exact (false_of_label_iso_nonSplit ggLabelRigidInput_holds hp hp2 hn hlabKN
        (Or.inr rfl) ht hΛO hΛJ (htransport hhasO) hJ).elim


end Label

end CFSG.StandardType

end
