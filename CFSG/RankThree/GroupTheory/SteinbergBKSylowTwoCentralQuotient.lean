module

public import CFSG.Foundations.Basic
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas
import CFSG.LocalAnalysis.ComponentInitial.SelfCentralizingCoreAutomorphisms
public import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting

public section

namespace CFSG.RankThree.GroupTheory.SteinbergBK

open Subgroup CFSG
open CFSG.Semidihedral.Principal.CoprimeFixedPoint (quotientAction quotientAction_mk)
open CFSG.LocalAnalysis.ComponentInitial (pointwiseFixingAut)
open scoped commutatorElement

instance inSubgroup_pPrimeCore_normal (p : ℕ) {L : Type*} [Group L] (N : Subgroup L)
    [N.Normal] : (inSubgroup (pPrimeCore p) N).Normal :=
  ConjAct.normal_of_characteristic_of_normal

theorem generated_action_centralized_sylow_two_solvable_core_central_quotient
    {L A : Type*} [Group L] [Finite L] [Group A] [MulDistribMulAction A L]
    (N : Subgroup L) [N.Normal] (hNsolv : Group.IsSolvable N)
    (hNinv : ∀ a : A, ∀ x ∈ N, a • x ∈ N) (hLA : commutatorSubgroup A L ⊤ = ⊤)
    (hT : ∃ T : Sylow 2 N, ∀ a : A, ∀ x ∈ (T : Subgroup N), a • (x : L) = x) :
    (∃ k : ℕ, Nat.card (N ⧸ pPrimeCore 2 N) = 2 ^ k) ∧ ⁅N, ⊤⁆ ≤ inSubgroup (pPrimeCore 2) N ∧
      IsPGroup 2 (N.map (QuotientGroup.mk' (inSubgroup (pPrimeCore 2) N))) ∧
      N.map (QuotientGroup.mk' (inSubgroup (pPrimeCore 2) N)) ≤
        center (L ⧸ inSubgroup (pPrimeCore 2) N) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT⟩ := hT
  set O' := pPrimeCore 2 N with hO'
  let q : N →* N ⧸ O' := QuotientGroup.mk' O'
  have : IsInvariant A L N :=
    ⟨fun a g => ⟨hNinv a g, fun h => by simpa using hNinv a⁻¹ _ h⟩⟩
  let α : A →* MulAut N := MulDistribMulAction.toMulAut A N
  have hO'α : ∀ a : A, ∀ n ∈ O', α a n ∈ O' := fun a n hn =>
    (characteristic_iff_map_le.mp inferInstance (α a)) ⟨n, hn, rfl⟩
  let γ0 : L →* MulAut N := MulAut.conjNormal
  have hO'γ : ∀ x : L, ∀ n ∈ O', γ0 x n ∈ O' := fun x n hn =>
    (characteristic_iff_map_le.mp inferInstance (γ0 x)) ⟨n, hn, rfl⟩
  let β := quotientAction α O' hO'α
  let γ := quotientAction γ0 O' hO'γ
  have hXsolv : Group.IsSolvable (N ⧸ O') := by
    have := hNsolv
    infer_instance
  set U := pCore 2 (N ⧸ O') with hU
  have hF : fittingSubgroup (N ⧸ O') = U :=
    Fitting_eq_pcore (N ⧸ O') 2 (pPrimeCore_quotient_pPrimeCore_eq_bot 2)
  have hUT : U ≤ ((T.mapSurjective (QuotientGroup.mk'_surjective O')) : Subgroup (N ⧸ O')) :=
    IsPGroup.le_sylow_of_normal pCore_isPGroup _
  have hβU : ∀ a : A, ∀ u ∈ U, β a u = u := by
    intro a u hu
    obtain ⟨t, ht, rfl⟩ := hUT hu
    change β a (t : N ⧸ O') = (t : N ⧸ O')
    rw [quotientAction_mk]
    exact congrArg _ (Subtype.ext (hT a t ht))
  have hγU : ∀ x : L, ∀ u ∈ U, γ x u ∈ U := fun x u hu =>
    (characteristic_iff_map_le.mp inferInstance (γ x)) ⟨u, hu, rfl⟩
  have hcompat : ∀ a : A, ∀ x : L, ∀ u : N ⧸ O', β a (γ x u) = γ (a • x) (β a u) := by
    intro a x u
    induction u using QuotientGroup.induction_on with
    | H n =>
      simp only [β, γ, quotientAction_mk]
      congr 1
      apply Subtype.ext
      change a • ((x : L) * (n : L) * x⁻¹) = (a • x) * (a • (n : L)) * (a • x)⁻¹
      rw [smul_mul', smul_mul', smul_inv']
  have hγ1 : ∀ x : L, ∀ u ∈ U, γ x u = u := by
    have hK : commutatorSubgroup A L ⊤ ≤ (pointwiseFixingAut U).comap γ := by
      refine (closure_le _).mpr ?_
      rintro _ ⟨a, x, -, rfl⟩ u hu
      have h1 := hβU a _ (hγU x u hu)
      rw [hcompat, hβU a u hu] at h1
      change γ (x⁻¹ * (a • x)) u = u
      rw [map_mul, MulAut.mul_apply, h1, ← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        MulAut.one_apply]
    intro x u hu
    exact hK (by rw [hLA]; exact mem_top x) u hu
  have hcent : ∀ y : N ⧸ O', y ∈ centralizer (U : Set (N ⧸ O')) := by
    intro y
    obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective y
    rw [mem_centralizer_iff]
    intro u hu
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective u
    have h := hγ1 n _ hu
    simp only [γ, quotientAction_mk] at h
    have h' : ((n * m * n⁻¹ : N) : N ⧸ O') = (m : N ⧸ O') := by
      rw [← h]
      exact congrArg _ (Subtype.ext (by simp [γ0, MulAut.conjNormal_apply]))
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      mul_inv_eq_iff_eq_mul] at h'
    exact h'.symm
  have hUtop : U = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have h := centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hXsolv
      (by rw [hF]; exact hcent y)
    rwa [hF] at h
  have hX2 : IsPGroup 2 (N ⧸ O') := by
    have h := pCore_isPGroup (p := 2) (G := N ⧸ O')
    rw [← hU, hUtop] at h
    exact h.of_equiv Subgroup.topEquiv
  have hcomm : ⁅N, ⊤⁆ ≤ inSubgroup (pPrimeCore 2) N := by
    rw [Subgroup.commutator_le]
    intro g hg x _
    have h := hγ1 x ((⟨g⁻¹, inv_mem hg⟩ : N) : N ⧸ O') (hUtop ▸ mem_top _)
    simp only [γ, quotientAction_mk] at h
    have h2 := QuotientGroup.eq.mp h.symm
    refine ⟨_, h2, ?_⟩
    simp [commutatorElement_def, γ0, MulAut.conjNormal_apply, mul_assoc]
  set O := inSubgroup (pPrimeCore 2) N with hO
  refine ⟨IsPGroup.iff_card.mp hX2, hcomm, ?_, ?_⟩
  · rintro ⟨_, n, hn, rfl⟩
    obtain ⟨k, hk⟩ := hX2 ((⟨n, hn⟩ : N) : N ⧸ O')
    refine ⟨k, Subtype.ext ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hk
    change (QuotientGroup.mk' O n) ^ 2 ^ k = 1
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact ⟨_, hk, rfl⟩
  · rintro _ ⟨n, hn, rfl⟩
    rw [mem_center_iff]
    intro z
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
    have h := hcomm (Subgroup.commutator_mem_commutator (inv_mem hn) (mem_top x⁻¹))
    rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    convert h using 1
    simp only [commutatorElement_def, mul_inv_rev, inv_inv, mul_assoc]

end CFSG.RankThree.GroupTheory.SteinbergBK
