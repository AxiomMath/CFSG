module

public import CFSG.OddTranspositions.HypothesisC
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
import CFSG.GroupTheory.OddConjInvCommute
import TauCeti.GroupTheory.PGroup
import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.Timmesfeld.Bridge.Asc72Triangle
public import CFSG.Timmesfeld.Moufang.Three
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Special.TwoCore
public import Certificates.Certificate43

public section

namespace CFSG.OddTranspositions.PartThree.ElevenThree

open CFSG.Timmesfeld.Bridge
open scoped commutatorElement

private theorem conj_mem_DalphaStar_of_mem_closure {X : Type*} [Group X] [Finite X]
    {E : Set X}
    (hY : HypothesisC E) {n t : X} (hn : n ∈ Subgroup.closure (commSet E hY.d))
    (ht : t ∈ DalphaStar E hY.alpha) : n * t * n⁻¹ ∈ DalphaStar E hY.alpha := by
  obtain ⟨e, -, hEeq, -⟩ := hY.hE
  have hnormE : n ∈ Subgroup.normalizer (orbitIn E hY.d e) :=
    CFSG.Timmesfeld.Bridge.OddLocal.closure_commSet_le_normalizer_orbitIn hY.d e hn
  have htE : t ∈ orbitIn E hY.d e := by
    rw [← hEeq, ← hY.DalphaStar_alpha]
    exact ht
  have hmem := (Subgroup.mem_set_normalizer_iff.mp hnormE t).mp htE
  simpa [hY.DalphaStar_alpha, hEeq] using hmem

private theorem Halpha_le_normalizer_of_forall_conj_mem {X : Type*} [Group X] [Finite X]
    {E : Set X}
    (hY : HypothesisC E) {N : Subgroup X}
    (hnorm : ∀ t ∈ DalphaStar E hY.alpha, ∀ n ∈ N, t * n * t⁻¹ ∈ N) :
    Halpha E hY.alpha ≤ Subgroup.normalizer (N : Set X) := by
  rw [show Halpha E hY.alpha = Subgroup.closure (DalphaStar E hY.alpha) from rfl,
    Subgroup.closure_le]
  intro x hx y
  have hxD : x ∈ E := DalphaStar_subset hY.isBlock_alpha hx
  have hx2 : x * x = 1 := hY.setup.oddT.mul_self_eq_one hxD
  have hxinv : x⁻¹ = x := hY.setup.oddT.inv_eq hxD
  constructor
  · intro hy
    exact hnorm x hx y hy
  · intro hxy
    rw [hxinv] at hxy
    have hyeq : y = x * (x * y * x) * x := by
      calc y = (x * x) * y * (x * x) := by rw [hx2, one_mul, mul_one]
        _ = x * (x * y * x) * x := by group
    rw [hyeq]
    simpa [hxinv] using hnorm x hx (x * y * x) hxy

private theorem commutator_mem_pCore_of_map_solvableRadical_eq_center {X : Type*} [Group X]
    [Finite X]
    {A : Subgroup X}
    (h113 : (CFSG.solvableRadical A).map (QuotientGroup.mk' (CFSG.pCore 2 A)) =
      Subgroup.center (A ⧸ CFSG.pCore 2 A))
    {m t : X} (hmA : m ∈ A) (htA : t ∈ A)
    (hmR : (⟨m, hmA⟩ : A) ∈ CFSG.solvableRadical A) :
    ⁅(⟨m, hmA⟩ : A), (⟨t, htA⟩ : A)⁆ ∈ CFSG.pCore 2 A := by
  let P : Subgroup A := CFSG.pCore 2 A
  have hz : QuotientGroup.mk' P (⟨m, hmA⟩ : A) ∈ Subgroup.center (A ⧸ P) := by
    rw [← h113]
    exact ⟨⟨m, hmA⟩, hmR, rfl⟩
  rw [commutatorElement_def]
  have hq : ((⟨m, hmA⟩ : A) * (⟨t, htA⟩ : A) : A ⧸ P) =
      ((⟨t, htA⟩ : A) * (⟨m, hmA⟩ : A)) := by
    have hmt := (Subgroup.mem_center_iff.mp hz) (QuotientGroup.mk' P (⟨t, htA⟩ : A))
    simpa [map_mul] using hmt.symm
  have hdiv := (QuotientGroup.eq_iff_div_mem (N := P)).mp hq
  convert hdiv using 1
  rw [div_eq_mul_inv, mul_inv_rev]
  group

private theorem commutator_eq_one_of_mem_pCore_of_odd {X : Type*} [Group X] [Finite X]
    {A N : Subgroup X} (hN : Odd (Nat.card N)) (hNnormal : (N.subgroupOf A).Normal)
    {m t : X} (hmA : m ∈ A) (htA : t ∈ A) (hmN : m ∈ N)
    (hcommP : ⁅(⟨m, hmA⟩ : A), (⟨t, htA⟩ : A)⁆ ∈ CFSG.pCore 2 A) :
    ⁅(⟨m, hmA⟩ : A), (⟨t, htA⟩ : A)⁆ = 1 := by
  let N' : Subgroup A := N.subgroupOf A
  have : N'.Normal := hNnormal
  have hmN' : (⟨m, hmA⟩ : A) ∈ N' := by
    rw [Subgroup.mem_subgroupOf]
    exact hmN
  have hcommN' : ⁅(⟨m, hmA⟩ : A), (⟨t, htA⟩ : A)⁆ ∈ N' :=
    Subgroup.commutator_le_left (H₁ := N') (H₂ := ⊤)
      (Subgroup.commutator_mem_commutator hmN' (Subgroup.mem_top _))
  have hN'odd : Odd (Nat.card N') := by
    have hN'eq : N' = N.subgroupOf A := rfl
    rw [hN'eq]
    exact hN.of_dvd_nat (N.card_comap_dvd_of_injective A.subtype A.subtype_injective)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdisj : Disjoint N' (CFSG.pCore 2 A) :=
    TauCeti.disjoint_of_not_dvd_natCard_of_isPGroup (p := 2) (C := N') (Q := CFSG.pCore 2 A)
      hN'odd.not_two_dvd_nat (CFSG.pCore_isPGroup (p := 2) (G := A))
  exact Subgroup.disjoint_def.mp hdisj hcommN' hcommP

private theorem commute_of_commutator_eq_one {X : Type*} [Group X] {A N : Subgroup X}
    {m n t : X} (hN : Odd (Nat.card N)) (hmN : m ∈ N) (hmA : m ∈ A) (htA : t ∈ A)
    (hm : m = n * t * n⁻¹ * t⁻¹) (ht2 : t * t = 1) (htinv : t⁻¹ = t)
    (hcomm : ⁅(⟨m, hmA⟩ : A), (⟨t, htA⟩ : A)⁆ = 1) : Commute t n := by
  have hmtA : (⟨m, hmA⟩ : A) * (⟨t, htA⟩ : A) = (⟨t, htA⟩ : A) * (⟨m, hmA⟩ : A) :=
    commutatorElement_eq_one_iff_mul_comm.mp hcomm
  have htmA : (⟨t, htA⟩ : A) * (⟨m, hmA⟩ : A) * (⟨t, htA⟩ : A)⁻¹ = (⟨m, hmA⟩ : A) := by
    rw [← hmtA]
    group
  have htmInvX : t * m * t⁻¹ = m⁻¹ := by
    rw [hm, htinv]
    rw [show t * (n * t * n⁻¹ * t) * t = (t * n * t * n⁻¹) * (t * t) by group,
      ht2, mul_one]
    rw [show (n * t * n⁻¹ * t)⁻¹ = t⁻¹ * n * t⁻¹ * n⁻¹ by group, htinv]
  have hcomm_tm : t * m = m * t := by
    have h : t * m * t⁻¹ = m := by
      simpa using congrArg (fun z : A => (z : X)) htmA
    calc t * m = (t * m * t⁻¹) * t := by group
      _ = m * t := by rw [h]
  have hodd : Odd (orderOf m) := Odd.of_dvd_nat hN (Subgroup.orderOf_dvd_natCard N hmN)
  have hm1 : m = 1 :=
    CFSG.GroupTheory.eq_one_of_odd_of_conj_eq_inv_of_commute hodd htmInvX hcomm_tm
  rw [hm] at hm1
  have hnt' : n * t * n⁻¹ = t := by
    have := congrArg (fun z => z * t) hm1
    simpa [mul_assoc] using this
  have hnt'' : n * t = t * n := by
    have := congrArg (fun z => z * n) hnt'
    simpa [mul_assoc] using this
  exact hnt''.symm

theorem commute_of_mem_DalphaStar_of_odd {X : Type*} [Group X] [Finite X] {E : Set X}
    (hY : HypothesisC E)
    (h113 : (CFSG.solvableRadical (Halpha E hY.alpha)).map
        (QuotientGroup.mk' (CFSG.pCore 2 (Halpha E hY.alpha))) =
      Subgroup.center (Halpha E hY.alpha ⧸ CFSG.pCore 2 (Halpha E hY.alpha)))
    {N : Subgroup X} (hN : Odd (Nat.card N)) (hle : N ≤ Subgroup.closure (commSet E hY.d))
    (hnorm : ∀ t ∈ DalphaStar E hY.alpha, ∀ n ∈ N, t * n * t⁻¹ ∈ N)
    {t : X} (ht : t ∈ DalphaStar E hY.alpha) : ∀ n ∈ N, Commute t n := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let A : Subgroup X := Halpha E hY.alpha
  let R : Subgroup A := CFSG.solvableRadical A
  let N' : Subgroup A := N.subgroupOf A
  have htA : t ∈ A := Subgroup.subset_closure ht
  have hAnorm : A ≤ Subgroup.normalizer (N : Set X) :=
    Halpha_le_normalizer_of_forall_conj_mem hY hnorm
  have hN'normal : N'.Normal := Subgroup.normal_subgroupOf_of_le_normalizer hAnorm
  have hN'odd : Odd (Nat.card N') :=
    hN.of_dvd_nat (N.card_comap_dvd_of_injective A.subtype A.subtype_injective)
  have hN'solv : Group.IsSolvable N' := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hN'odd
  have hN'leR : N' ≤ R := le_sSup ⟨hN'normal, hN'solv⟩
  intro n hn
  set m : X := n * t * n⁻¹ * t⁻¹ with hmdef
  have hmN : m ∈ N := by
    rw [hmdef]
    have h2 : t * n⁻¹ * t⁻¹ ∈ N := hnorm t ht n⁻¹ (N.inv_mem hn)
    rw [show n * t * n⁻¹ * t⁻¹ = n * (t * n⁻¹ * t⁻¹) by group]
    exact N.mul_mem hn h2
  have hmA : m ∈ A := by
    rw [hmdef]
    exact A.mul_mem (Subgroup.subset_closure (conj_mem_DalphaStar_of_mem_closure hY (hle hn) ht))
      (A.inv_mem (Subgroup.subset_closure ht))
  have hmN' : (⟨m, hmA⟩ : A) ∈ N' := by
    rw [Subgroup.mem_subgroupOf]
    exact hmN
  have hmR : (⟨m, hmA⟩ : A) ∈ R := hN'leR hmN'
  have hcommP : ⁅(⟨m, hmA⟩ : A), (⟨t, htA⟩ : A)⁆ ∈ CFSG.pCore 2 A :=
    commutator_mem_pCore_of_map_solvableRadical_eq_center h113 hmA htA hmR
  have hcommOne : ⁅(⟨m, hmA⟩ : A), (⟨t, htA⟩ : A)⁆ = 1 :=
    commutator_eq_one_of_mem_pCore_of_odd hN hN'normal hmA htA hmN hcommP
  exact commute_of_commutator_eq_one hN hmN hmA htA hmdef
    (hY.setup.oddT.mul_self_eq_one (DalphaStar_subset hY.isBlock_alpha ht))
    (hY.setup.oddT.inv_eq (DalphaStar_subset hY.isBlock_alpha ht)) hcommOne

end CFSG.OddTranspositions.PartThree.ElevenThree
