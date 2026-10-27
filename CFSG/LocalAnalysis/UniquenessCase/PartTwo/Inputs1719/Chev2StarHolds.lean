module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Chev2StarDef
public import CFSG.Open.SplitBNPair
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate2261
public import Certificates.Certificate2262
public import Certificates.Certificate2263
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate2268
public import Certificates.Certificate2269
public import Certificates.Certificate2270
public import Certificates.Certificate8033
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Chev2GlueHolds
import CFSG.LocalAnalysis.UniquenessCase.UC22K108BigRow
import CFSG.Milestones.ASVolI.I2
import CFSG.RankThree.PartOne.FOCD.LyFive
import CFSG.Sporadic.Schreier.TitsOuter
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.Foundations
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.RankThreeUC.Asc1930
public import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsGen
public import CFSG.Perm.ChainSpec
public import CFSG.Quasithin.Background.A1bGroups
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
import CFSG.ClassicalInvolution.SmallCases.Sporadic.QuasiAssembly
import CFSG.LinearAlgebra.SelfAdjointRankFactorization
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAntiunitaryDescent
import CFSG.RankThree.Native.LyCertifiedOrder
import CFSG.RankThree.Native.LySeedCheckBase
import CFSG.RankThree.Native.LySeedOperatorBase
import CFSG.RankThree.PartOne.Census3.Assembly
import CFSG.RankThree.PartOne.FOCD.CycSylow
import CFSG.RankThree.PartOne.FOCD.OrdLemma
import CFSG.RankThree.PartOne.KC.OrthogonalHighWittFixedSpace
import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldFixed
import CFSG.RankThree.PartOne.KC.UnitaryDefining
import CFSG.RankThree.PartOne.RF4.Basic
import CFSG.RankThree.PartOne.S11c.LyPlaneCore
import CFSG.RankThree.PartOne.S11d.PSLDescent
import CFSG.Sporadic.Schreier.LyFixedSet
import Certificates.Certificate8160

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ABGLocalTools (IsSylowOf isSylowOf_iff isSylowOf_map_subtype_iff)

open CFSG.ASVolI.ChIJK (IsSplitBNPair)

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)


theorem chev2star_mem_of_isPGroup_outer {Y : Type} [Group Y] {K : Subgroup Y} [K.Normal]
    (hcent : centralizer (K : Set Y) = ⊥) (hout : IsPGroup 2 (Outer ↥K)) {e : Y}
    (he : Odd (orderOf e)) : e ∈ K := by
  let q : Y →* Outer ↥K := (QuotientGroup.mk' (inner ↥K)).comp MulAut.conjNormal
  obtain ⟨k, hk⟩ := hout (q e)
  have h1 : orderOf (q e) = 1 := by
    have hcop : Nat.Coprime (orderOf e) (2 ^ k) := (Nat.coprime_two_right.2 he).pow_right k
    exact Nat.eq_one_of_dvd_one (hcop.gcd_eq_one ▸
      Nat.dvd_gcd (orderOf_map_dvd q e) (orderOf_dvd_of_pow_eq_one hk))
  obtain ⟨c, hc⟩ : MulAut.conjNormal e ∈ inner ↥K :=
    (QuotientGroup.eq_one_iff _).1 (orderOf_eq_one_iff.1 h1)
  have hmem : (c : Y)⁻¹ * e ∈ centralizer (K : Set Y) := by
    rw [mem_centralizer_iff]
    intro h hh
    have hch : (c : Y) * h * (c : Y)⁻¹ = e * h * e⁻¹ := by
      have := congrArg (fun φ : MulAut ↥K => ((φ ⟨h, hh⟩ : ↥K) : Y)) hc
      simpa only [MulAut.conj_apply, MulAut.conjNormal_apply, Subgroup.coe_mul,
        Subgroup.coe_inv] using this
    calc h * ((c : Y)⁻¹ * e) = (c : Y)⁻¹ * ((c : Y) * h * (c : Y)⁻¹) * e := by group
      _ = (c : Y)⁻¹ * (e * h * e⁻¹) * e := by rw [hch]
      _ = (c : Y)⁻¹ * e * h := by group
  rw [hcent, Subgroup.mem_bot, inv_mul_eq_one] at hmem
  rw [← hmem]
  exact c.2

theorem chev2star_ne_top_of_dvd_card {S : Type} [Group S] {p : ℕ} {B N : Subgroup S}
    (hBN : IsSplitBNPair p B N) (hp : p ∣ Nat.card S) : B ≠ ⊤ := by
  rintro rfl
  obtain ⟨U, -, -, -, hUi, hUN, -, hsat⟩ := hBN.split
  have hconj : ∀ g : S, CFSG.conjugate (⊤ : Subgroup S) g = ⊤ := fun g =>
    Subgroup.map_top_of_surjective _ (MulAut.conj g⁻¹).surjective
  simp only [hconj, iInf_top, top_inf_eq] at hsat
  rw [← hsat, inf_top_eq] at hUN
  rw [hUN, Subgroup.index_bot] at hUi
  exact hUi hp

theorem chev2star_isSylowOf_sup {Y : Type} [Group Y] [Finite Y] {p : ℕ} [Fact p.Prime]
    {P K E : Subgroup Y} [K.Normal] (hP : IsSylowOf p P K) (hE : ¬ p ∣ Nat.card E) :
    IsSylowOf p P (K ⊔ E) := by
  rw [isSylowOf_iff] at hP ⊢
  obtain ⟨hPK, hPp, hPi⟩ := hP
  refine ⟨hPK.trans le_sup_left, hPp, fun h => ?_⟩
  rw [← Subgroup.relIndex_mul_relIndex P K (K ⊔ E) hPK le_sup_left,
    Subgroup.relIndex_sup_left] at h
  rcases (Nat.Prime.dvd_mul Fact.out).1 h with h | h
  · exact hPi h
  · exact hE (h.trans (Subgroup.relIndex_dvd_card K E))

section Main


theorem chev2StarGen_holds : Chev2StarGen := by
  intro Y _ _ Kb Eb Tb M r hKn hsimple hchev hcent hTb hr hr7 hr13 hferm hcard hperm hTM hEM
    hstar
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hrodd : Odd r := hr.odd_of_ne_two (by omega)
  obtain ⟨t, n, f, hadm, hmod⟩ := hchev
  by_cases ht : t = .Tits
  · subst ht
    have hout := (CFSG.Sporadic.Schreier.Tits.AT_Tits_model_Schreier ↥Kb 2 f
      (hmod.reeTitsModel (by decide)).2).1
    have hEK : Eb ≤ Kb := fun e he => chev2star_mem_of_isPGroup_outer hcent hout
      (hrodd.of_dvd_nat (hcard ▸ Subgroup.orderOf_dvd_natCard Eb he))
    exact absurd (hcard ▸ Subgroup.card_dvd_of_le hEK)
      (not_dvd_card_of_lieModel_tits hmod hr hr7 hr13)
  obtain ⟨B, N, hBN⟩ := CFSG.ASVolI.ChIJK.lieModel_has_splitBNPair Nat.prime_two ht hmod
  have hU : IsSylowOf 2 (Tb ⊓ Kb) Kb :=
    hTb.inf_of_le_normalizer le_top (by rw [normalizer_eq_top_iff.mpr hKn])
  have hEN : Eb ≤ normalizer ((Tb ⊓ Kb : Subgroup Y) : Set Y) := by
    have hdvd : Nat.card ↥(Eb ⊓ Kb) ∣ r := hcard ▸ Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime hr).1 hdvd with h1 | h1
    · exact le_normalizer_inf_of_permutes hKn hTb.isPGroup hr (by omega) hcard
        (Subgroup.card_eq_one.mp h1) hperm
    have hEK : Eb ≤ Kb :=
      inf_eq_left.mp (Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h1, hcard]))
    obtain ⟨Q, hQ⟩ := hU
    have hQ' : (Q : Subgroup ↥Kb) = (Tb ⊓ Kb).subgroupOf Kb := by
      rw [← hQ, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective Kb.subtype_injective]
    have hEcard : Nat.card ↥(Eb.subgroupOf Kb) = r := by
      rw [← hcard]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEK).toEquiv
    have hEQ : Permutes (Eb.subgroupOf Kb) (Q : Subgroup ↥Kb) := by
      rw [hQ']
      exact CFSG.Quasithin.H.Tri.subgroupOf_mul_comm hEK inf_le_right
        (CFSG.GroupTheory.permutes_inf_of_le hEK hperm)
    rcases le_normalizer_or_fermat_of_splitBN hBN Q hr (by omega) hEcard hEQ with h | ⟨k, hk⟩
    · have h1 := Subgroup.map_mono (f := Kb.subtype) h
      rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hEK] at h1
      calc Eb ≤ (normalizer ((Q : Subgroup ↥Kb) : Set ↥Kb)).map Kb.subtype := h1
        _ ≤ normalizer (((Q : Subgroup ↥Kb).map Kb.subtype : Subgroup Y) : Set Y) :=
          Subgroup.le_normalizer_map _
        _ = normalizer ((Tb ⊓ Kb : Subgroup Y) : Set Y) := by rw [hQ]
    · exact absurd hk (hferm k)
  have hS : (Kb.subgroupOf (Kb ⊔ Eb)).Normal := hKn.subgroupOf _
  let eS : ↥(Kb.subgroupOf (Kb ⊔ Eb)) ≃* ↥Kb := Subgroup.subgroupOfEquivOfLe le_sup_left
  have : IsSimpleGroup ↥(Kb.subgroupOf (Kb ⊔ Eb)) := eS.isSimpleGroup
  obtain ⟨B', N', hBN'⟩ := CFSG.ASVolI.ChIJK.burnsideI2BN_exists_of_mulEquiv eS.symm ⟨B, N, hBN⟩
  have h2 : 2 ∣ Nat.card ↥(Kb.subgroupOf (Kb ⊔ Eb)) := by
    rw [Nat.card_congr eS.toEquiv]
    exact (dvd_pow_self 2 (Nat.one_le_iff_ne_zero.mp hadm.2.1)).trans
      (CFSG.RankThree.PartOne.FOCD.two_pow_dvd_card_lieModel_two hmod hadm.2.1)
  have hT : IsSylowOf 2 ((Tb ⊓ Kb).subgroupOf (Kb ⊔ Eb)) ⊤ := by
    rw [← isSylowOf_map_subtype_iff (Kb ⊔ Eb), Subgroup.subgroupOf_map_subtype,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype,
      inf_of_le_left (inf_le_right.trans le_sup_left)]
    exact chev2star_isSylowOf_sup hU (by rw [hcard]; exact hrodd.not_two_dvd_nat)
  have hX : Nat.card ↥(Eb.subgroupOf (Kb ⊔ Eb)) = r := by
    rw [← hcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  have hle := UC22.F10.k108big_rowX_strong (Kb.subgroupOf (Kb ⊔ Eb)) hBN'
    (chev2star_ne_top_of_dvd_card hBN' h2) hT (hX ▸ hr) (hX ▸ hrodd)
    (fun x hx => Subgroup.le_normalizer_comap (Kb ⊔ Eb).subtype (hEN hx))
    (M := M.subgroupOf (Kb ⊔ Eb)) (fun x hx => hTM hx) (fun x hx => hEM hx)
    (fun g hg => hstar g.1 g.2 fun x hx => hg ⟨x, Subgroup.mem_sup_right hx⟩ hx)
  intro k hk
  exact hle (show (⟨k, Subgroup.mem_sup_left hk⟩ : ↥(Kb ⊔ Eb)) ∈ Kb.subgroupOf (Kb ⊔ Eb) from hk)

end Main

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
