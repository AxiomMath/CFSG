module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Core
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer
public import CFSG.Open.LocalVocabulary
import CFSG.Assembly.Defs

public section

namespace CFSG.Quasithin.SzQ

private theorem mulAut_mul_comm_of_isCyclic (N : Type*) [Group N] [IsCyclic N]
    (a b : MulAut N) : a * b = b * a := by
  apply (IsCyclic.mulAutMulEquiv N).injective
  rw [map_mul, map_mul, mul_comm]

theorem commutator_le_centralizer_of_normal_isCyclic {G : Type*} [Group G]
    (N : Subgroup G) [N.Normal] [IsCyclic N] :
    commutator G ≤ Subgroup.centralizer (N : Set G) := by
  have : IsMulCommutative (MulAut N) := IsMulCommutative.of_comm (mulAut_mul_comm_of_isCyclic N)
  intro x hx
  have hker := Abelianization.commutator_subset_ker (MulAut.conjNormal (H := N)) hx
  rw [MonoidHom.mem_ker] at hker
  rw [Subgroup.mem_centralizer_iff]
  intro n hn
  have h := congrArg (fun φ : MulAut N => (φ ⟨n, hn⟩ : G)) hker
  simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h
  calc n * x = x * n * x⁻¹ * x := by rw [h]
    _ = x * n := by group

theorem commutator_le_centralizer_pCore_of_cyclic_sylow
    {K : Type*} [Group K] [Finite K] (A : Subgroup K) (q : ℕ) [Fact q.Prime]
    (hcyc : ∀ R : Sylow q K, IsCyclic ↥(R : Subgroup K)) :
    commutator ↥A ≤ Subgroup.centralizer (CFSG.pCore q ↥A : Set ↥A) := by
  have hNnormal : (CFSG.pCore q ↥A).Normal := CFSG.pCore_normal
  have hNp : IsPGroup q (CFSG.pCore q ↥A) := CFSG.pCore_isPGroup
  obtain ⟨R, hR⟩ := (hNp.map A.subtype).exists_le_sylow
  have hRcyc : IsCyclic ↥(R : Subgroup K) := hcyc R
  have hmapcyc : IsCyclic ↥((CFSG.pCore q ↥A).map A.subtype) := Subgroup.isCyclic_of_le hR
  have hNcyc : IsCyclic ↥(CFSG.pCore q ↥A) :=
    (MulEquiv.isCyclic
      (Subgroup.equivMapOfInjective (CFSG.pCore q ↥A) A.subtype A.subtype_injective)).mpr hmapcyc
  exact commutator_le_centralizer_of_normal_isCyclic (CFSG.pCore q ↥A)

theorem eq_bot_of_isPGroup_two_of_le_fitting {G : Type*} [Group G] [Finite G]
    (hcore : CFSG.pCore 2 G = ⊥) {D : Subgroup G} (hD : IsPGroup 2 D)
    (hDF : D ≤ CFSG.fittingSubgroup G) : D = ⊥ := by
  have hDF' : IsPGroup 2 (D.subgroupOf (CFSG.fittingSubgroup G)) :=
    hD.of_equiv (Subgroup.subgroupOfEquivOfLe hDF).symm
  obtain ⟨P, hP⟩ := hDF'.exists_le_sylow
  have hPcore : P.map (CFSG.fittingSubgroup G).subtype ≤ CFSG.pCore 2 G :=
    Sylow.map_le_pCore inferInstance inferInstance 2 P
  rw [hcore, le_bot_iff] at hPcore
  rw [eq_bot_iff, ← Subgroup.map_subgroupOf_eq_of_le hDF]
  exact (Subgroup.map_mono hP).trans hPcore.le

theorem pCoreOf_two_ne_bot_of_solvable_of_nonabelian_sylow
    {K : Type*} [Group K] [Finite K]
    (hcyc : ∀ (r : ℕ) [Fact r.Prime], r ≠ 2 → ∀ R : Sylow r K, IsCyclic ↥(R : Subgroup K))
    (S : Sylow 2 K) (hS : ¬ IsMulCommutative ↥(S : Subgroup K))
    {A : Subgroup K} (hSA : (S : Subgroup K) ≤ A) (hA : Group.IsSolvable ↥A) :
    CFSG.Open.pCoreOf 2 A ≠ ⊥ := by
  intro hbot
  apply hS
  have hcore : CFSG.pCore 2 ↥A = ⊥ := by
    have h1 : CFSG.Open.pCore 2 ↥A = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective _ A.subtype_injective).mp hbot
    rw [h1]
  have hcent : ∀ q : (Nat.card ↥A).primeFactors.attach,
      commutator ↥A ≤ Subgroup.centralizer (CFSG.pCore q.1.1 ↥A : Set ↥A) := by
    intro q
    by_cases hq : q.1.1 = 2
    · rw [hq, hcore]
      intro x _
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [SetLike.mem_coe, Subgroup.mem_bot] at hh
      rw [hh, one_mul, mul_one]
    · exact commutator_le_centralizer_pCore_of_cyclic_sylow A q.1.1 (hcyc q.1.1 hq)
  have hfit : commutator ↥A ≤ CFSG.fittingSubgroup ↥A :=
    (CFSG.subgroup_le_centralizer_fitting_of_le_centralizer_pCores hcent).trans
      (CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hA)
  let T : Subgroup ↥A := (S : Subgroup K).subgroupOf A
  have hT : IsPGroup 2 T := S.isPGroup'.of_equiv (Subgroup.subgroupOfEquivOfLe hSA).symm
  have hTT : ⁅T, T⁆ ≤ T := Subgroup.commutator_le.mpr fun x hx y hy => by
    rw [commutatorElement_def]
    exact T.mul_mem (T.mul_mem (T.mul_mem hx hy) (T.inv_mem hx)) (T.inv_mem hy)
  have hD : ⁅T, T⁆ = ⊥ :=
    eq_bot_of_isPGroup_two_of_le_fitting hcore (hT.to_le hTT)
      ((Subgroup.commutator_mono le_top le_top).trans hfit)
  refine IsMulCommutative.of_comm fun a b => ?_
  have hx : (⟨a, hSA a.2⟩ : ↥A) ∈ T := a.2
  have hy : (⟨b, hSA b.2⟩ : ↥A) ∈ T := b.2
  have h1 := Subgroup.commutator_mem_commutator hx hy
  rw [hD, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
  exact Subtype.ext (congrArg (Subtype.val : ↥A → K) h1)

end CFSG.Quasithin.SzQ
