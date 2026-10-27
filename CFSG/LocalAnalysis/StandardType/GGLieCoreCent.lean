module

public import CFSG.LocalAnalysis.StandardType.GGLieCoreDefs
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyBruhat
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyClosedLang
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Subnormal
public import CFSG.LocalAnalysis.StandardType.GGL45NtLattice
public import CFSG.Certificates.WordSubgroupRel
public import CFSG.LieType.Multipliers.ProductKernel
public import CFSG.LieType.Multipliers.U42Bridge
public import CFSG.LieType.Multipliers.U43Action
public import CFSG.LieType.Multipliers.U43BridgeInputs
public import CFSG.LieType.Multipliers.U62Action
public import CFSG.LieType.Multipliers.U62Bridge
public import CFSG.LieType.Multipliers.U62Kernel
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
public import CFSG.LocalAnalysis.EvenSmallLie.Sp6JCondition
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.Milestones.CL_LIT_Griess_Schur_multipliers_Lie_type
public import CFSG.Monster.B.Classical.PlaneAut
public import CFSG.Monster.B.TwoA.Amalgam.Data
public import CFSG.Monster.B.TwoA.Sp8.Par1
public import CFSG.Monster.B.TwoA.Unitary.LinThree
public import CFSG.RankThree.PartOne.KF.F128Cyclic
public import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
public import CFSG.RankThree.PerfectCover.HopfCentralCoversFinite
public import CFSG.RankThree.Theta.ThreeComponentOrbitCover
public import CFSG.Sporadic.Presentation.Common
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.Sporadic.SmallOddCore.CheckSpec
public import CFSG.YGroups.Y322Central
public import Certificates.Certificate10005
public import Certificates.Certificate10006
public import Certificates.Certificate10007
public import Certificates.Certificate10008
public import Certificates.Certificate10009
public import Certificates.Certificate10010
public import Certificates.Certificate10012
public import Certificates.Certificate10013
public import Certificates.Certificate10014
public import Certificates.Certificate10016
public import Certificates.Certificate10018
public import Certificates.Certificate12041
public import Certificates.Certificate12042
public import Certificates.Certificate12043
public import Certificates.Certificate12044
public import Certificates.Certificate12045
public import Certificates.Certificate12046
public import Certificates.Certificate16015
public import Certificates.Certificate16040
public import Certificates.Certificate2154
public import Certificates.Certificate2157
public import Certificates.Certificate2326
public import Certificates.Certificate3006
public import Certificates.Certificate3007
public import Certificates.Certificate3008
public import Certificates.Certificate3063
public import Certificates.Certificate3077
public import Certificates.Certificate3082
public import Certificates.Certificate3083
public import Certificates.Certificate9130

public section

namespace CFSG.StandardType.LieCore

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.C14Lattice
  CFSG.RankThree.PartOne.KE CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open Matrix

private theorem ggLieCent_jointChar_apply {τ : Tag} {L : Type} [Field L]
    (a₁ a₂ : Fin τ.rank → Lˣ) (v : Multiplicative (Fin τ.rank → ℤ)) :
    jointChar a₁ a₂ v = (rootChar a₁ (Multiplicative.toAdd v),
      rootChar a₂ (Multiplicative.toAdd v)) := rfl

private theorem ggLieCent_familyKernel_pair {τ : Tag} {L : Type} [Field L]
    (a₁ a₂ : Fin τ.rank → Lˣ) :
    familyKernel ![a₁, a₂] = kernelRoots (jointChar a₁ a₂) := by
  ext α
  simp only [familyKernel, kernelRoots, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hroot, hα⟩
    have h0 := hα 0
    have h1 := hα 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    refine ⟨hroot, ?_⟩
    rw [ggLieCent_jointChar_apply, Prod.mk_eq_one]
    exact ⟨h0, h1⟩
  · rintro ⟨hroot, hα⟩
    refine ⟨hroot, fun i => ?_⟩
    have hα' := (Prod.mk_eq_one.1 ((ggLieCent_jointChar_apply a₁ a₂
      (Multiplicative.ofAdd α)).symm.trans hα))
    fin_cases i
    · show rootChar a₁ (Multiplicative.toAdd (Multiplicative.ofAdd α)) = 1
      exact hα'.1
    · show rootChar a₂ (Multiplicative.toAdd (Multiplicative.ofAdd α)) = 1
      exact hα'.2

private theorem ggLieCent_familyCentralizer_pair {τ : Tag} {L : Type} [Field L]
    (a₁ a₂ : Fin τ.rank → Lˣ) :
    familyCentralizer τ L ![a₁, a₂] = adjointGroup τ L ⊓
      Subgroup.centralizer ((Subgroup.closure {rootDiagUnit τ a₁, rootDiagUnit τ a₂} :
        Subgroup (ModGL τ L)) : Set (ModGL τ L)) := by
  ext g
  rw [mem_familyCentralizer]
  simp only [Subgroup.mem_inf, Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [Subgroup.centralizer_closure]
  constructor
  · rintro ⟨hg, h1, h2⟩
    refine ⟨hg, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact (Subgroup.mem_centralizer_iff.1 (conj_eq_iff_mem_centralizer.1 h1)) _ (by simp)
    · exact (Subgroup.mem_centralizer_iff.1 (conj_eq_iff_mem_centralizer.1 h2)) _ (by simp)
  · rintro ⟨hg, hc⟩
    refine ⟨hg, ?_, ?_⟩
    · exact conj_eq_iff_mem_centralizer.2
        (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (by simp)) hc)
    · exact conj_eq_iff_mem_centralizer.2
        (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (by simp)) hc)

private theorem ggLieCent_rootsTrivialOn_pair {τ : Tag} {L : Type} [Field L]
    (a₁ a₂ : Fin τ.rank → Lˣ) :
    rootsTrivialOn (Subgroup.closure {rootDiagUnit τ a₁, rootDiagUnit τ a₂}) =
      kernelRoots (jointChar a₁ a₂) := by
  ext γ
  rw [rootsTrivialOn, kernelRoots]
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    rw [ggLieCent_jointChar_apply, Prod.mk_eq_one]
    exact ⟨h.2 a₁ (Subgroup.subset_closure (by simp)),
           h.2 a₂ (Subgroup.subset_closure (by simp))⟩
  · rintro ⟨hroot, hχ⟩
    rw [ggLieCent_jointChar_apply, Prod.mk_eq_one] at hχ
    obtain ⟨h1, h2⟩ := hχ
    refine ⟨hroot, ?_⟩
    intro a ha
    have hmap : (Subgroup.closure {rootDiagUnit τ a₁, rootDiagUnit τ a₂} :
        Subgroup (ModGL τ L)) = (Subgroup.closure {a₁, a₂}).map (rootDiagUnitHom τ L) := by
      rw [MonoidHom.map_closure]
      congr 1
      rw [Set.image_insert_eq, Set.image_singleton]
      rfl
    have hmem : rootDiagUnit τ a ∈ (Subgroup.closure {a₁, a₂}).map (rootDiagUnitHom τ L) :=
      hmap ▸ ha
    obtain ⟨b, hb, hba⟩ := hmem
    have hba' : b = a := rootDiagUnit_injective hba
    subst hba'
    let ψ : (Fin τ.rank → Lˣ) →* Lˣ :=
      { toFun := fun x => rootChar x γ
        map_one' := by simp [rootChar]
        map_mul' := fun x y => by
          simp only [Pi.mul_apply, rootChar]
          rw [← Finset.prod_mul_distrib]
          exact Finset.prod_congr rfl fun i _ => by rw [mul_zpow] }
    have hker : Subgroup.closure ({a₁, a₂} : Set (Fin τ.rank → Lˣ)) ≤ ψ.ker := by
      refine (Subgroup.closure_le _).2 ?_
      rintro x (rfl | rfl)
      · simpa [ψ] using h1
      · simpa [ψ] using h2
    simpa [ψ] using hker hb

private theorem ggLieCent_conj_pow_mem {G : Type*} [Group G] {M : Subgroup G} {m n : G}
    (hm : m ∈ M) (hn : n ∈ Subgroup.normalizer (M : Set G)) (k : ℕ) :
    n ^ k * m * (n ^ k)⁻¹ ∈ M := by
  induction k with
  | zero => simpa using hm
  | succ k ih =>
    have hstep : n * (n ^ k * m * (n ^ k)⁻¹) * n⁻¹ ∈ M :=
      (Subgroup.mem_normalizer_iff.1 hn (n ^ k * m * (n ^ k)⁻¹)).1 ih
    convert hstep using 1
    group

private theorem ggLieCent_exists_mul_pow_of_mem_normalizer {G : Type*} [Group G]
    {M : Subgroup G} {m n : G} (hm : m ∈ M)
    (hn : n ∈ Subgroup.normalizer (M : Set G)) (k : ℕ) :
    ∃ a ∈ M, (m * n) ^ k = a * n ^ k := by
  induction k with
  | zero => exact ⟨1, M.one_mem, by simp⟩
  | succ k ih =>
    obtain ⟨a, ha, hk⟩ := ih
    refine ⟨a * (n ^ k * m * (n ^ k)⁻¹), mul_mem ha ?_, ?_⟩
    · exact ggLieCent_conj_pow_mem hm hn k
    · rw [pow_succ, hk, pow_succ]
      group

private theorem ggLieCent_canonicalRep_pow_mem {τ : Tag} {L : Type} [Field L]
    (w : WeylGroup τ) (k : ℕ) :
    ∃ h ∈ torusGroup τ L, (canonicalRep (coxeterSystem τ) L w) ^ k =
      h * canonicalRep (coxeterSystem τ) L (w ^ k) := by
  induction k with
  | zero => exact ⟨1, Subgroup.one_mem _, by simp [canonicalRep_one]⟩
  | succ k ih =>
    obtain ⟨h, hh, hk⟩ := ih
    obtain ⟨h', hh', hmul⟩ := canonicalRep_mul_mem (R := L) (w ^ k) w
    refine ⟨h * h', mul_mem hh hh', ?_⟩
    calc (canonicalRep (coxeterSystem τ) L w) ^ (k + 1)
        = (canonicalRep (coxeterSystem τ) L w) ^ k *
            canonicalRep (coxeterSystem τ) L w := pow_succ _ _
      _ = (h * canonicalRep (coxeterSystem τ) L (w ^ k)) *
            canonicalRep (coxeterSystem τ) L w := by rw [hk]
      _ = h * (canonicalRep (coxeterSystem τ) L (w ^ k) *
            canonicalRep (coxeterSystem τ) L w) := by group
      _ = h * (h' * canonicalRep (coxeterSystem τ) L (w ^ k * w)) := by rw [hmul]
      _ = (h * h') * canonicalRep (coxeterSystem τ) L (w ^ (k + 1)) := by
            rw [pow_succ]; group

theorem ggLieCentStructure_pow_mem
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (a₁ a₂ : Fin τ.rank → Lˣ)
    (h₁ : rootDiagUnit τ a₁ ^ p = 1) (h₂ : rootDiagUnit τ a₂ ^ p = 1) :
    ∀ x ∈ adjointGroup τ L ⊓ Subgroup.centralizer
        ((Subgroup.closure {rootDiagUnit τ a₁, rootDiagUnit τ a₂} : Subgroup (ModGL τ L)) :
          Set (ModGL τ L)),
      ∃ k : ℕ, x ^ (p ^ k) ∈ centConn
        (Subgroup.closure {rootDiagUnit τ a₁, rootDiagUnit τ a₂}) := by
  intro x hx
  have ha₁ : ∀ i, a₁ i ^ p = 1 := by
    have h : a₁ ^ p = 1 := rootDiagUnit_injective (by rw [← rootDiagUnit_pow, h₁, rootDiagUnit_one])
    intro i
    simpa using congrFun h i
  have ha₂ : ∀ i, a₂ i ^ p = 1 := by
    have h : a₂ ^ p = 1 := rootDiagUnit_injective (by rw [← rootDiagUnit_pow, h₂, rootDiagUnit_one])
    intro i
    simpa using congrFun h i
  have ha : ∀ i j, ![a₁, a₂] i j ^ p = 1 := by
    intro i j
    fin_cases i
    · simpa using ha₁ j
    · simpa using ha₂ j
  have hx' : x ∈ familyCentralizer τ L ![a₁, a₂] := by
    rw [ggLieCent_familyCentralizer_pair]
    exact ⟨hx.1, hx.2⟩
  obtain ⟨w, hw, m, hm, rfl⟩ := familyCentralizer_le_mul τ L ![a₁, a₂] hx'
  refine ⟨(orderOf w).factorization p, ?_⟩
  have hnorm : canonicalRep (coxeterSystem τ) L w ∈
      Subgroup.normalizer (familyGroup (K := L) ![a₁, a₂] : Set (ModGL τ L)) :=
    canonicalRep_mem_normalizer_familyGroup (K := L) hw
  have hcop : Nat.Coprime (orderOf (w ^ p ^ (orderOf w).factorization p)) p := by
    rw [orderOf_pow_of_dvd (pow_ne_zero _ hp.ne_zero) (Nat.ordProj_dvd _ _)]
    exact (Nat.coprime_ordCompl hp (orderOf_pos w).ne').symm
  have hw_sub : w ^ p ^ (orderOf w).factorization p ∈
      familyStabilizerSubgroup ![a₁, a₂] :=
    Subgroup.pow_mem _ (mem_familyStabilizerSubgroup.2 hw) _
  have hwrefl : w ^ p ^ (orderOf w).factorization p ∈ familyReflectionGroup ![a₁, a₂] :=
    mem_familyReflectionGroup_of_coprime hp ha hw_sub hcop
  have hnpow : canonicalRep (coxeterSystem τ) L (w ^ p ^ (orderOf w).factorization p) ∈
      familyGroup (K := L) ![a₁, a₂] :=
    canonicalRep_mem_familyGroup hwrefl
  have hconv := ggLieCent_canonicalRep_pow_mem (L := L) w (p ^ (orderOf w).factorization p)
  obtain ⟨hf, hfmem, hfpow⟩ := hconv
  have haux := ggLieCent_exists_mul_pow_of_mem_normalizer hm hnorm
    (p ^ (orderOf w).factorization p)
  obtain ⟨a, haa, haux'⟩ := haux
  have hgoal : (m * canonicalRep (coxeterSystem τ) L w) ^ p ^ (orderOf w).factorization p ∈
      familyGroup (K := L) ![a₁, a₂] := by
    rw [haux', hfpow]
    exact mul_mem haa (mul_mem (le_sup_left (a := torusGroup τ L) hfmem) hnpow)
  have hconn : centConn (Subgroup.closure {rootDiagUnit τ a₁, rootDiagUnit τ a₂}) =
      familyGroup (K := L) ![a₁, a₂] := by
    rw [centConn, ggLieCent_rootsTrivialOn_pair, ← ggLieCent_familyKernel_pair]
    rfl
  rw [hconn]
  exact hgoal

end CFSG.StandardType.LieCore
