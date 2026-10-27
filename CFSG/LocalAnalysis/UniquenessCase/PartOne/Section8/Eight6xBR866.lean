module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.InnerActionOut
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.InnerBarDecomp
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight65X0CardG2General
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.SupDecomposition
public import CFSG.LocalAnalysis.UniquenessCase.UCFront08
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open scoped commutatorElement
open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data Bar2 IsSpor)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F08 (IsA6Z3 IsA7Z3 IsM22Z3)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

@[expose] def SylowNoncyclicCentralizers (Y : Type) [Group Y] [Finite Y] : Prop :=
  ∀ S : Sylow 3 Y, ∀ q ∈ (S : Subgroup Y),
    ¬ IsCyclic ↥((S : Subgroup Y) ⊓ Subgroup.centralizer ({q} : Set Y))

@[expose] def SylowNoncyclicOfG2 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (p f : ℕ), p.Prime → p ≠ 3 → (p = 2 → 2 ≤ f) →
    LieModel Y .G2 0 p f → SylowNoncyclicCentralizers Y

private theorem inf_centralizer_mul_eq {G : Type} [Group G] {Q : Subgroup G} {q c : G}
    (hc : ∀ x ∈ Q, c * x = x * c) :
    Q ⊓ Subgroup.centralizer ({q * c} : Set G) = Q ⊓ Subgroup.centralizer ({q} : Set G) := by
  ext x
  constructor
  · rintro ⟨hxQ, hxc⟩
    refine ⟨hxQ, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have hxc' : x * (q * c) = (q * c) * x := Subgroup.mem_centralizer_singleton_iff.mp hxc
    have hx' : x * q * c = q * x * c := by
      calc x * q * c = x * (q * c) := by rw [mul_assoc]
        _ = (q * c) * x := hxc'
        _ = q * (c * x) := by rw [mul_assoc]
        _ = q * (x * c) := by rw [hc x hxQ]
        _ = q * x * c := by rw [mul_assoc]
    exact mul_right_cancel hx'
  · rintro ⟨hxQ, hxc⟩
    refine ⟨hxQ, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have hxc' : x * q = q * x := Subgroup.mem_centralizer_singleton_iff.mp hxc
    calc x * (q * c) = x * q * c := by rw [mul_assoc]
      _ = q * x * c := by rw [hxc']
      _ = q * (x * c) := by rw [mul_assoc]
      _ = q * (c * x) := by rw [← hc x hxQ]
      _ = (q * c) * x := by rw [mul_assoc]

private theorem not_isCyclic_inf_centralizer_of_sylowNoncyclic {G : Type} [Group G] [Finite G]
    {L Q : Subgroup G} (hQ : IsSylowOf 3 Q L) (hNC : SylowNoncyclicCentralizers (Bar2 L))
    {q : G} (hq : q ∈ Q) : ¬ IsCyclic ↥(Q ⊓ Subgroup.centralizer ({q} : Set G)) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQL : Q ≤ L := hQ.le
  have hQO2 : Q ⊓ CFSG.Open.pCoreOf 2 L = ⊥ :=
    (IsPGroup.disjoint_of_ne 3 2 (by norm_num) Q (CFSG.Open.pCoreOf 2 L)
      hQ.isPGroup (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)).eq_bot
  obtain ⟨S, hS⟩ := exists_sylow_map_subgroupOf_mk' hQ.exists_sylow_eq_subgroupOf
  let f : ↥Q →* Bar2 L := (QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp (Subgroup.inclusion hQL)
  have hf : Function.Injective f := injective_comp_subgroupOf_mk' hQL hQO2
  have hr : f.range = (Q.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) :=
    range_comp_subgroupOf_mk' hQL
  have hSf : ∀ s : Bar2 L, s ∈ (S : Subgroup (Bar2 L)) ↔ ∃ x : ↥Q, f x = s := by
    intro s
    rw [hS, ← hr]
    exact MonoidHom.mem_range
  let qq : ↥Q := ⟨q, hq⟩
  intro hcyc
  apply hNC S (f qq) ((hSf _).2 ⟨qq, rfl⟩)
  let ι : Q ⊓ Subgroup.centralizer ({q} : Set G) ≤ Q := inf_le_left
  let g : ↥(Q ⊓ Subgroup.centralizer ({q} : Set G)) →*
      ↥((S : Subgroup (Bar2 L)) ⊓ Subgroup.centralizer ({f qq} : Set (Bar2 L))) :=
    (f.comp (Subgroup.inclusion ι)).codRestrict
      ((S : Subgroup (Bar2 L)) ⊓ Subgroup.centralizer ({f qq} : Set (Bar2 L))) (by
        intro x
        refine ⟨(hSf _).2 ⟨_, rfl⟩, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
        have hx : (x : G) * q = q * (x : G) := Subgroup.mem_centralizer_singleton_iff.mp x.2.2
        have : f (qq * Subgroup.inclusion ι x) = f (Subgroup.inclusion ι x * qq) := by
          congr 1
          exact Subtype.ext hx.symm
        simpa using this.symm)
  have hg : Function.Surjective g := by
    rintro ⟨s, hsS, hsC⟩
    obtain ⟨x, rfl⟩ := (hSf s).1 hsS
    have hxc : f x * f qq = f qq * f x := Subgroup.mem_centralizer_singleton_iff.mp hsC
    have hxq : x * qq = qq * x := hf (by simpa using hxc)
    have hxq' : (x : G) * q = q * (x : G) := congrArg Subtype.val hxq
    exact ⟨⟨(x : G), x.2, Subgroup.mem_centralizer_singleton_iff.mpr hxq'⟩, Subtype.ext rfl⟩
  exact isCyclic_of_surjective g hg

theorem not_isCyclic_inf_centralizer_of_bar {G : Type} [Group G] [Finite G] {L Q P : Subgroup G}
    (hQ : IsSylowOf 3 Q L) (hQP : Q ≤ P) (hP3 : IsPGroup 3 P)
    (hPNL : P ≤ Subgroup.normalizer (L : Set G))
    (hOut : ¬ 3 ∣ Nat.card (Outer (Bar2 L))) (hNC : SylowNoncyclicCentralizers (Bar2 L))
    {y : G} (hy : y ∈ P) : ¬ IsCyclic ↥(Q ⊓ Subgroup.centralizer ({y} : Set G)) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQL : Q ≤ L := hQ.le
  have hQeq : Q = P ⊓ L :=
    (hQ.eq_of_le (le_inf hQP hQL) inf_le_right (hP3.to_le inf_le_left)).symm
  have hPQ : P ≤ Subgroup.normalizer (Q : Set G) := by
    rw [hQeq, Subgroup.le_normalizer_iff]
    intro p hp x hx
    exact ⟨P.mul_mem (P.mul_mem hp hx.1) (P.inv_mem hp),
      (Subgroup.mem_normalizer_iff.mp (hPNL hp) x).1 hx.2⟩
  have hQnormP : (Q.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQP).mpr hPQ
  have hQO2 : Q ⊓ CFSG.Open.pCoreOf 2 L = ⊥ :=
    (IsPGroup.disjoint_of_ne 3 2 (by norm_num) Q (CFSG.Open.pCoreOf 2 L)
      hQ.isPGroup (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)).eq_bot
  have hQC : ⁅Q, centralizerBar P L⁆ = ⊥ := commutator_eq_bot_centralizerBar hQL hQO2 hPQ
  have hCQ : ∀ c ∈ centralizerBar P L, ∀ q ∈ Q, c * q = q * c := by
    intro c hc q hq
    have hmem : ⁅q, c⁆ ∈ ⁅Q, centralizerBar P L⁆ := Subgroup.commutator_mem_commutator hq hc
    rw [hQC, Subgroup.mem_bot] at hmem
    exact (commutatorElement_eq_one_iff_mul_comm.mp hmem).symm
  have hPC : P ≤ Q ⊔ centralizerBar P L :=
    le_sup_centralizerBar_of_inner hQP hQL hQeq hQnormP hQ hP3 hPNL le_rfl
      (inner_action_of_not_three_dvd_outer hOut hP3 hPNL)
  obtain ⟨q, hq, c, hc, rfl⟩ := exists_mul_mem_sup_of_commute hCQ (hPC hy)
  rw [inf_centralizer_mul_eq (fun x hx => hCQ c hc x hx)]
  exact not_isCyclic_inf_centralizer_of_sylowNoncyclic hQ hNC hq

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
