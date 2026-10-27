module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFactsNineteenLevi
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21d
import CFSG.LocalAnalysis.UniquenessCase.UC22S2113
import CFSG.LocalAnalysis.OddStandard.SwapPartner.L44Centralizer
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrQuot
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.BNGenerationReduction
import CFSG.ClassicalGroups.PCoreSection
public import CFSG.RankThree.SteinbergR3ELinearUnitaryOuterOrder

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily.LeviUniq

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_of_centralizesBar {x : G} {L A : Subgroup G} (hx : CentralizesBar x L)
    (hOA : pCoreOf 2 L ≤ A) (hAL : A ≤ L) : x ∈ normalizer (A : Set G) := by
  refine Subgroup.mem_normalizer_fintype fun a ha => ?_
  have h := hx.2 a (hAL ha)
  have e : x * a * x⁻¹ = (x * a * x⁻¹ * a⁻¹) * a := by group
  rw [e]
  exact A.mul_mem (hOA h) ha

theorem mem_of_mem_normalizer_inf {M D : Subgroup G}
    (hP : ∃ S : Sylow 2 (Bar2 D),
      normalizer ((S : Subgroup (Bar2 D)) : Set (Bar2 D)) ≤ S19.barOfInter M D)
    (hO : pCoreOf 2 D ≤ M) {y : G} (hyD : y ∈ D)
    (hy : y ∈ normalizer ((D ⊓ M : Subgroup G) : Set G)) : y ∈ M := by
  obtain ⟨S, hS⟩ := hP
  have hyQ : (⟨y, hyD⟩ : ↥D) ∈
      normalizer (((D ⊓ M).subgroupOf D : Subgroup ↥D) : Set ↥D) := by
    refine Subgroup.mem_normalizer_fintype fun z hz => ?_
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hz ⊢
    have h := (Subgroup.mem_normalizer_iff.1 hy (z : G)).1 hz
    simpa using h
  have hybar : QuotientGroup.mk' (CFSG.pCore 2 ↥D) ⟨y, hyD⟩ ∈
      normalizer (S19.barOfInter M D : Set (Bar2 D)) := by
    simpa [S19.barOfInter] using
      Subgroup.le_normalizer_map (QuotientGroup.mk' (CFSG.pCore 2 ↥D))
        (Subgroup.mem_map_of_mem _ hyQ)
  have hSJ : (S : Subgroup (Bar2 D)) ≤ S19.barOfInter M D :=
    Subgroup.le_normalizer.trans hS
  have hmem : QuotientGroup.mk' (CFSG.pCore 2 ↥D) ⟨y, hyD⟩ ∈ S19.barOfInter M D :=
    CFSG.AGLEmbedding.ParabAutIrr.mem_of_mem_normalizer S hSJ hS hybar
  have h := CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.mem_of_mk_mem_barOfInter
    (M := M) (D := D) hO (x := ⟨y, hyD⟩) hmem
  simpa using h

theorem mem_inner_of_odd_orderOf_of_lieModel_psl_two {T : Type} [Group T] [Finite T] {n : ℕ}
    (hn : 3 ≤ n) (hT : CFSG.Blueprint.LieModel T .PSL n 2 1) {α : MulAut T}
    (hα : Odd (orderOf α)) : α ∈ inner T := by
  have hT' := CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by omega) hT
  have hout := (CFSG.RankThree.OuterOrder.higher_linear_unitary_outer_order_determinant_bound
    (Or.inl rfl) hn Nat.prime_two le_rfl hT').1
  have hout2 : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer T) ∣ 2 := by
    simpa [CFSG.RankThree.OuterOrder.determinantParameter] using hout
  exact CFSG.OddStandard.AltStdSec.SwapPartner.mem_inner_of_coprime_orderOf_outer
    (Nat.Coprime.of_dvd_right hout2 hα.coprime_two_right)

theorem le_normalizer_of_odd_of_inner {M D A X : Subgroup G} (hq : IsQuasisimple (Bar2 D))
    (hP : ∃ S : Sylow 2 (Bar2 D),
      normalizer ((S : Subgroup (Bar2 D)) : Set (Bar2 D)) ≤ S19.barOfInter M D)
    (hO : pCoreOf 2 D ≤ M)
    (hinn : ∀ α : MulAut (BarInf D), Odd (orderOf α) → α ∈ inner (BarInf D))
    (hOA : pCoreOf 2 D ≤ A) (hAD : A ≤ D ⊓ M) (hA : (A.subgroupOf (D ⊓ M)).Normal)
    (hXD : X ≤ normalizer (D : Set G)) (hXDM : X ≤ normalizer ((D ⊓ M : Subgroup G) : Set G))
    (hXo : Odd (Nat.card X)) : X ≤ normalizer (A : Set G) := by
  intro x hx
  have hxN : x ∈ normalizer (D : Set G) := hXD hx
  set α : MulAut (BarInf D) := inducedBarInfAutHom D ⟨x, hxN⟩ with hαdef
  have hαdvd : orderOf α ∣ orderOf x := by
    have h := orderOf_map_dvd (inducedBarInfAutHom D) ⟨x, hxN⟩
    rwa [Subgroup.orderOf_mk] at h
  have hαodd : Odd (orderOf α) :=
    Odd.of_dvd_nat (Odd.of_dvd_nat hXo (Subgroup.orderOf_dvd_natCard X hx)) hαdvd
  have hinner : α ∈ (MulAut.conj : BarInf D →* MulAut (BarInf D)).range := by
    simpa only [CFSG.ComponentClassification.OuterAutomorphisms.inner] using hinn α hαodd
  obtain ⟨z, hz⟩ := MonoidHom.mem_range.mp hinner
  obtain ⟨w, hw⟩ := QuotientGroup.mk_surjective (s := CFSG.solvableRadical ↥D) z
  have hyα : inducedBarInfAutHom D ⟨(w : G), Subgroup.le_normalizer w.2⟩ = α := by
    rw [uc22s2113_inducedBarInfAutHom_of_mem (L := D) w.2]
    rw [show ((⟨(w : G), w.2⟩ : ↥D) : BarInf D) = z from by rw [← hw]]
    exact hz
  have hbN : (w : G)⁻¹ * x ∈ normalizer (D : Set G) :=
    (normalizer (D : Set G)).mul_mem
      ((normalizer (D : Set G)).inv_mem (Subgroup.le_normalizer w.2)) hxN
  have hb1 : inducedBarInfAutHom D ⟨(w : G)⁻¹ * x, hbN⟩ = 1 := by
    have hmul : inducedBarInfAutHom D ⟨(w : G)⁻¹ * x, hbN⟩ =
        (inducedBarInfAutHom D ⟨(w : G), Subgroup.le_normalizer w.2⟩)⁻¹ *
          inducedBarInfAutHom D ⟨x, hxN⟩ := by
      rw [← map_inv, ← map_mul]
      congr 1
    rw [hmul, hyα, hαdef]
    exact inv_mul_cancel _
  have hcb : CentralizesBar ((w : G)⁻¹ * x) D :=
    uc22s2113_centralizesBar_of_inducedBarInfAutHom_eq_one (L := D)
      (CFSG.Quasithin.A3.isQuasisimple_iff_open.1 hq) hbN hb1
  have hODM : pCoreOf 2 D ≤ D ⊓ M :=
    le_inf (CFSG.ClassicalGroups.PCoreSection.pCoreOf_le 2 D) hO
  have hbDM : (w : G)⁻¹ * x ∈ normalizer ((D ⊓ M : Subgroup G) : Set G) :=
    mem_normalizer_of_centralizesBar hcb hODM inf_le_left
  have hbA : (w : G)⁻¹ * x ∈ normalizer (A : Set G) :=
    mem_normalizer_of_centralizesBar hcb hOA (hAD.trans inf_le_left)
  have hwDM : (w : G) ∈ normalizer ((D ⊓ M : Subgroup G) : Set G) := by
    have h : x * ((w : G)⁻¹ * x)⁻¹ = (w : G) := by group
    rw [← h]
    exact (normalizer ((D ⊓ M : Subgroup G) : Set G)).mul_mem (hXDM hx)
      ((normalizer ((D ⊓ M : Subgroup G) : Set G)).inv_mem hbDM)
  have hwM : (w : G) ∈ M :=
    mem_of_mem_normalizer_inf (D := D) (M := M) hP hO w.2 hwDM
  have hwDMsub : (w : G) ∈ D ⊓ M := ⟨w.2, hwM⟩
  have hDMnormA : D ⊓ M ≤ normalizer (A : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAD).mp hA
  have hxeq : x = (w : G) * ((w : G)⁻¹ * x) := by group
  rw [hxeq]
  exact (normalizer (A : Set G)).mul_mem (hDMnormA hwDMsub) hbA

theorem le_normalizer_of_odd_of_lieModel_psl_two {M Dsub : Subgroup G}
    (hq : IsQuasisimple (Bar2 Dsub))
    (hP : S19.IsNontrivialParabolic (Bar2 Dsub) (S19.barOfInter M Dsub))
    (hO : pCoreOf 2 Dsub ≤ M) {s : ℕ} (hs : 3 ≤ s)
    (hL : CFSG.Blueprint.LieModel (BarInf Dsub) .PSL s 2 1)
    {d : ℕ} {K J : Fin d → Subgroup G} (hKJ : S19.IsDynkinFamilyIn M Dsub d K J)
    {X : Subgroup G} (hXD : X ≤ normalizer (Dsub : Set G))
    (hX : X ≤ normalizer ((Dsub ⊓ M : Subgroup G) : Set G)) (hXo : Odd (Nat.card X))
    (k : Fin d) : X ≤ normalizer (K k : Set G) := by
  obtain ⟨S, hS⟩ := hP.2.2
  have hP' : ∃ S : Sylow 2 (Bar2 Dsub),
      normalizer ((S : Subgroup (Bar2 Dsub)) : Set (Bar2 Dsub)) ≤ S19.barOfInter M Dsub :=
    ⟨S, le_of_lt hS⟩
  have hO2 : pCoreOf 2 Dsub ≤ pCoreOf 2 (Dsub ⊓ M) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (le_inf (CFSG.ClassicalGroups.PCoreSection.pCoreOf_le 2 Dsub) hO)
      (inf_le_left.trans
        (CFSG.PreuniquenessRankFour.Helpers.subgroup_normalizes_pCoreOf 2 Dsub))
      (CFSG.ClassicalGroups.PCoreSection.isPGroup_pCoreOf 2 Dsub)
  have hk := hKJ.1 k
  obtain ⟨hOK, hKDM, hKnorm, -⟩ := hk
  refine le_normalizer_of_odd_of_inner hq hP' hO (fun α hα => ?_) (hO2.trans hOK) hKDM hKnorm
    hXD hX hXo
  exact mem_inner_of_odd_orderOf_of_lieModel_psl_two hs hL hα

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily.LeviUniq
