module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront07
public import CFSG.LocalAnalysis.UniquenessCase.UC6R
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.OddCore
import CFSG.LocalAnalysis.UniquenessCase.UC6S19
import CFSG.LocalAnalysis.UniquenessCase.UC22P22p
import CFSG.LocalAnalysis.UniquenessCase.UC22P22uh
import CFSG.LocalAnalysis.UniquenessCase.UC22P22n
import CFSG.LocalAnalysis.UniquenessCase.UC22S13xj
import CFSG.LocalAnalysis.StronglyEmbedded.PSubgroups
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.EscapingCaseOneQuotient
import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Reduced
import CFSG.LocalAnalysis.RankThreeUC.AGL81S16Setup
import CFSG.GroupTheory.PElementSubgroup
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryInvolutionTop
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.OddKernelNormalizerTransferLift
public import CFSG.RankThree.PartOne.CTP.StrongPGlue

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.ShultStronglyClosedTI.OddKernelNormalizerTransfer
  (involution_lift_normalizing_prime_subgroup)

variable {G : Type} [Group G] [Finite G]

theorem normalizer_le_of_r6_3 (D : Data G) (h63 : UC6.R6_3 D) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hM : IsStronglyPEmbedded p D.M) {T : Subgroup G} (hT : T ≠ ⊥)
    (hT2 : IsPGroup 2 T) (hrank : 2 ≤ CFSG.Open.pRank p (normalizer (T : Set G) ⊓ D.M)) :
    normalizer (T : Set G) ≤ D.M := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨E₀, hE₀, hE₀el, hE₀card⟩ :=
    CFSG.SectionRank.exists_pRank hp.one_lt (normalizer (T : Set G) ⊓ D.M)
  have hE₀nc : ¬ IsCyclic ↥E₀ :=
    uc22p22n_not_isCyclic_of_card hp hE₀el
      (by rw [hE₀card]; exact Nat.pow_le_pow_right hp.pos hrank)
  obtain ⟨E, hEE₀, hEel, hEcard⟩ := uc22p22u_exists_elemAbelian_sq hp hp2 hE₀el.isPGroup hE₀nc
  have hEM : E ≤ D.M := hEE₀.trans (hE₀.trans inf_le_right)
  have hEN : E ≤ normalizer (T : Set G) := hEE₀.trans (hE₀.trans inf_le_left)
  exact uc22p22p_le_of_uniqueMax
    (h63 p hp hp2 E hEM hEel hEcard (hM.rankThreeGamma_one_le_of_le hp hEel.isPGroup hEM))
    ⟨T, hT, hT2, rfl⟩ hEN

theorem exists_involution_of_lieModel_psu_subgroup {X : Type} [Group X] [Finite X] {p f : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) {Y U : Subgroup X}
    (hY : CFSG.Blueprint.LieModel ↥Y .PSU 3 p f) (hf : 2 ≤ f)
    (hU : CFSG.ABGLocalTools.IsSylowOf p U Y) :
    ∃ y : X, y ∈ normalizer (U : Set X) ∧ orderOf y = 2 ∧
      ¬ IsCyclic ↥(U ⊓ centralizer ({y} : Set X)) ∧ Y ≤ U ⊔ centralizer ({y} : Set X) := by
  classical
  obtain ⟨Q, rfl⟩ := hU
  obtain ⟨j, hjN, hj2, hjel, hjcard, hjtop⟩ :=
    CFSG.AGLEmbedding.UnitaryModel.exists_involution_sup_eq_top_of_lieModel hp2 hY Q
  refine ⟨(j : X), Subgroup.le_normalizer_map Y.subtype ⟨j, hjN, rfl⟩,
    (Subgroup.orderOf_coe j).trans hj2, fun hcyc => ?_, ?_⟩
  · have hW : ((Q : Subgroup Y) ⊓ centralizer ({j} : Set Y)).map Y.subtype ≤
        (Q : Subgroup Y).map Y.subtype ⊓ centralizer ({(j : X)} : Set X) := by
      rintro _ ⟨x, hx, rfl⟩
      have hx' := Subgroup.mem_inf.mp hx
      refine Subgroup.mem_inf.mpr ⟨⟨x, hx'.1, rfl⟩, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hx'.2)
    haveI := Subgroup.isCyclic_of_le hW
    have hcyc' : IsCyclic ↥((Q : Subgroup Y) ⊓ centralizer ({j} : Set Y)) :=
      isCyclic_of_surjective
        (Subgroup.equivMapOfInjective _ Y.subtype Y.subtype_injective).symm.toMonoidHom
        (MulEquiv.surjective _)
    exact uc22p22n_not_isCyclic_of_card Fact.out hjel
      (by rw [hjcard]; exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos hf) hcyc'
  · have h := congrArg (Subgroup.map Y.subtype) hjtop
    rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
    refine h.symm.le.trans (sup_le_sup le_rfl ?_)
    rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hx))

theorem le_sup_of_lieModel_psu_quotient {X : Type} [Group X] [Finite X] {p n : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) (N : Subgroup X) [N.Normal] (hNodd : Odd (Nat.card N))
    (hNp : Nat.Coprime p (Nat.card N)) {A Lx B : Subgroup X} (hA : IsPGroup p A)
    (hAL : CFSG.ABGLocalTools.IsSylowOf p A Lx) (hAB : A ≤ B)
    (hY : CFSG.Blueprint.LieModel ↥(Lx.map (QuotientGroup.mk' N)) .PSU 3 p n) (hn : 2 ≤ n)
    (hC : ∀ t : X, orderOf t = 2 → ¬ IsCyclic ↥(A ⊓ centralizer ({t} : Set X)) →
      centralizer ({t} : Set X) ≤ B) :
    Lx ≤ B ⊔ N := by
  classical
  have hker : (QuotientGroup.mk' N).ker = N := QuotientGroup.ker_mk' N
  obtain ⟨y, hyN, hy2, hync, hYle⟩ :=
    exists_involution_of_lieModel_psu_subgroup hp2 hY hn (hAL.map (QuotientGroup.mk' N))
  have hyinv : CFSG.BenderSuzuki.PFAppendixIII.IsInvolution y := by
    refine ⟨fun h => ?_, ?_⟩
    · rw [h, orderOf_one] at hy2
      exact absurd hy2 (by decide)
    · rw [← hy2]
      exact pow_orderOf_eq_one y
  obtain ⟨t, htN, htinv, hty⟩ :=
    involution_lift_normalizing_prime_subgroup
      (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) p Fact.out
      (by rw [hker]; exact hNodd) (by rw [hker]; exact hNp) A hA hyinv hyN
  have ht2 : orderOf t = 2 := orderOf_eq_prime htinv.2 htinv.1
  have hinj : Function.Injective ((QuotientGroup.mk' N).subgroupMap A) :=
    CFSG.OrderReductions.ThompsonQuotient.prime_subgroup_injective_of_coprime_kernel p
      (QuotientGroup.mk' N)
      (by rw [hker]; exact (Nat.Prime.coprime_iff_not_dvd Fact.out).1 hNp) A hA
  have hle : A.map (QuotientGroup.mk' N) ⊓ centralizer ({y} : Set (X ⧸ N)) ≤
      (A ⊓ centralizer ({t} : Set X)).map (QuotientGroup.mk' N) := by
    intro z hz
    obtain ⟨⟨a, haA, rfl⟩, hac'⟩ := Subgroup.mem_inf.mp hz
    have hac := Subgroup.mem_centralizer_singleton_iff.mp hac'
    have hta : t * a * t⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp htN a).mp haA
    have hpi : QuotientGroup.mk' N (t * a * t⁻¹) = QuotientGroup.mk' N a := by
      rw [map_mul, map_mul, map_inv, hty, ← hac]
      group
    have heq : t * a * t⁻¹ = a :=
      congrArg Subtype.val (hinj (a₁ := ⟨_, hta⟩) (a₂ := ⟨a, haA⟩) (Subtype.ext hpi))
    refine ⟨a, ⟨haA, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩, rfl⟩
    calc a * t = (t * a * t⁻¹) * t := by rw [heq]
      _ = t * a := by group
  have hnc : ¬ IsCyclic ↥(A ⊓ centralizer ({t} : Set X)) := by
    intro hcyc
    haveI : IsCyclic ↥((A ⊓ centralizer ({t} : Set X)).map (QuotientGroup.mk' N)) :=
      isCyclic_of_surjective ((QuotientGroup.mk' N).subgroupMap _)
        ((QuotientGroup.mk' N).subgroupMap_surjective _)
    exact hync (Subgroup.isCyclic_of_le hle)
  have hCy : centralizer ({y} : Set (X ⧸ N)) ≤ B.map (QuotientGroup.mk' N) := by
    rw [← hty, ← CFSG.ProperTwoGeneratedCore.Assembly.map_centralizer_eq hNodd ht2]
    exact Subgroup.map_mono (hC t ht2 hnc)
  have hYB : Lx.map (QuotientGroup.mk' N) ≤ B.map (QuotientGroup.mk' N) :=
    hYle.trans (sup_le (Subgroup.map_mono hAB) hCy)
  have h := Subgroup.map_le_iff_le_comap.mp hYB
  rwa [Subgroup.comap_map_eq, hker] at h

theorem eq_one_of_lieModel_psu (D : Data G) (h63 : UC6.R6_3 D) {p : ℕ} {H : Subgroup G}
    (h7 : F07.Sec7Hyp D p H) {n : ℕ}
    (hPSU : CFSG.Blueprint.LieModel (F07.LKQuot7 p H) .PSU 3 p n) : n = 1 := by
  classical
  obtain ⟨hp, hp2, hM, -, hHM, hrank1⟩ := h7
  haveI : Fact p.Prime := ⟨hp⟩
  have hrank : 2 ≤ CFSG.Open.pRank p (H ⊓ D.M) := hrank1
  have hn1 : 1 ≤ n := hPSU.admissible.2.1
  by_contra hn
  have hn2 : 2 ≤ n := by omega
  have hKM : (CFSG.pPrimeCore p ↥H).map H.subtype ≤ D.M := pPrimeCore_le hM hp hrank
  have hKodd : Odd (Nat.card ↥(CFSG.pPrimeCore p ↥H)) :=
    odd_card_pPrimeCore hM hp
      (fun T hT hT2 hTr => normalizer_le_of_r6_3 D h63 hp hp2 hM hT hT2 hTr) hHM hrank
  obtain ⟨E₀, hE₀, hE₀el, hE₀card⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (H ⊓ D.M)
  obtain ⟨P, hPsyl, hE₀P⟩ := UC6.exists_isSylowOf_ge hE₀ hE₀el.isPGroup
  have hP5 : IsPGroup p ↥P := hPsyl.isPGroup
  have hPH : P ≤ H := hPsyl.le.trans inf_le_left
  have hPM : P ≤ D.M := hPsyl.le.trans inf_le_right
  have hP1 : P ≠ ⊥ := by
    rintro rfl
    have h1 : Nat.card ↥E₀ = 1 := Subgroup.card_eq_one.mpr (le_bot_iff.mp hE₀P)
    have h2 : 1 < p ^ CFSG.Open.pRank p (H ⊓ D.M) := Nat.one_lt_pow (by omega) hp.one_lt
    rw [hE₀card] at h1
    exact h2.ne' h1
  have hPHsyl : CFSG.ABGLocalTools.IsSylowOf p P H := uc22s13xj_isSylowOf_of_inf hM hPsyl hP1
  have hLH : Opp p H ≤ H := CFSG.LocalAnalysis.RankThreeUC.pElementSubgroup_le p H
  have hHnL : H ≤ normalizer ((Opp p H : Subgroup G) : Set G) :=
    CFSG.LocalAnalysis.RankThreeUC.le_normalizer_pElementSubgroup p H
  have hPL : P ≤ Opp p H := CFSG.le_pElementSubgroup_of_isPGroup hp hP5 hPH
  have hPLsyl : CFSG.ABGLocalTools.IsSylowOf p P (Opp p H) := hPHsyl.of_le hPL hLH
  have hsub : (Opp p H).subgroupOf H ≤ (H ⊓ D.M).subgroupOf H ⊔ CFSG.pPrimeCore p ↥H := by
    refine le_sup_of_lieModel_psu_quotient hp2 (CFSG.pPrimeCore p ↥H) hKodd
      CFSG.pPrimeCore_coprime_card (A := P.subgroupOf H) (Lx := (Opp p H).subgroupOf H)
      (B := (H ⊓ D.M).subgroupOf H) (hP5.comap_subtype (K := H)) ?_ ?_ hPSU hn2 ?_
    · rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff H, Subgroup.map_subgroupOf_eq_of_le hPH,
        Subgroup.map_subgroupOf_eq_of_le hLH]
      exact hPLsyl
    · intro a ha
      exact Subgroup.mem_subgroupOf.mpr (hPsyl.le (Subgroup.mem_subgroupOf.mp ha))
    ·
      intro t ht2 hnc
      have hRp : IsPGroup p
          ↥((P.subgroupOf H ⊓ centralizer ({t} : Set ↥H)).map H.subtype) :=
        ((hP5.comap_subtype (K := H)).to_le inf_le_left).map H.subtype
      have hRnc : ¬ IsCyclic
          ↥((P.subgroupOf H ⊓ centralizer ({t} : Set ↥H)).map H.subtype) := by
        intro hcyc
        exact hnc (isCyclic_of_surjective
          (Subgroup.equivMapOfInjective _ H.subtype H.subtype_injective).symm.toMonoidHom
          (MulEquiv.surjective _))
      obtain ⟨E, hER, hEel, hEcard⟩ := uc22p22u_exists_elemAbelian_sq hp hp2 hRp hRnc
      have hRP : (P.subgroupOf H ⊓ centralizer ({t} : Set ↥H)).map H.subtype ≤ P := by
        rintro _ ⟨a, ⟨haP, -⟩, rfl⟩
        exact Subgroup.mem_subgroupOf.mp haP
      have hRC : (P.subgroupOf H ⊓ centralizer ({t} : Set ↥H)).map H.subtype ≤
          centralizer ({(t : G)} : Set G) := by
        rintro _ ⟨a, ha, rfl⟩
        exact Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val
          (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp ha).2))
      have ht1 : t ≠ 1 := by
        rintro rfl
        rw [orderOf_one] at ht2
        exact absurd ht2 (by decide)
      have htG1 : (t : G) ≠ 1 := fun h => ht1 (Subtype.ext h)
      have htG2 : (t : G) ^ 2 = 1 := by
        have h := pow_orderOf_eq_one t
        rw [ht2] at h
        simpa using congrArg Subtype.val h
      have hNT : normalizer ((zpowers (t : G) : Subgroup G) : Set G) ≤ D.M :=
        normalizer_le_of_r6_3 D h63 hp hp2 hM (Subgroup.zpowers_ne_bot.2 htG1)
          (CFSG.RankThree.PartOne.StrongP.isPGroup_zpowers_of_pow_eq_one htG2)
          (CFSG.SectionRank.le_pRank hp.one_lt
            (le_inf (hER.trans (hRC.trans
              (CFSG.RankThree.PartOne.StrongP.centralizer_singleton_le_normalizer_zpowers _)))
              (hER.trans (hRP.trans hPM))) hEel hEcard)
      intro c hc
      refine Subgroup.mem_subgroupOf.mpr ⟨c.2, hNT ?_⟩
      apply CFSG.RankThree.PartOne.StrongP.centralizer_singleton_le_normalizer_zpowers
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hc))
  have hLM : Opp p H ≤ D.M :=
    calc Opp p H = ((Opp p H).subgroupOf H).map H.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hLH).symm
      _ ≤ ((H ⊓ D.M).subgroupOf H ⊔ CFSG.pPrimeCore p ↥H).map H.subtype :=
          Subgroup.map_mono hsub
      _ = (H ⊓ D.M) ⊔ (CFSG.pPrimeCore p ↥H).map H.subtype := by
          rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le inf_le_left]
      _ ≤ D.M := sup_le inf_le_right hKM
  exact hHM ((UC6.frattini_of_isSylowOf hLH hHnL hPLsyl).le.trans
    (sup_le hLM (inf_le_right.trans (hM.normalizer_le hP1 hP5 hPM))))

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
