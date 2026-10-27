module

public import CFSG.RankThree.PartTwo.Sec13.Notation
import CFSG.RankThree.PartTwo.Sec13.Ronan138WOutAbPSL
import CFSG.RankThree.PartTwo.Sec13.Ronan138WOutAbPSU
import CFSG.RankThree.PartTwo.KFacts.K72L3Linear
import CFSG.RankThree.PartTwo.KFacts.K72L3Unitary
import CFSG.RankThree.PartTwo.Sec13.Item13Models

public section

namespace CFSG.RankThree.PartTwo.Sec13.Ronan138W

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.RankThreeEven (projSL projSU)

theorem comm_mem_range_conj_of_congr {X M : Type*} [Group X] [Group M] (ψ : X ≃* M)
    {σ τ : MulAut X}
    (h : MulAut.congr ψ σ * MulAut.congr ψ τ * (MulAut.congr ψ σ)⁻¹ * (MulAut.congr ψ τ)⁻¹ ∈
      (MulAut.conj : M →* MulAut M).range) :
    σ * τ * σ⁻¹ * τ⁻¹ ∈ (MulAut.conj : X →* MulAut X).range := by
  obtain ⟨m, hm⟩ := h
  refine ⟨ψ.symm m, ?_⟩
  apply (MulAut.congr ψ).injective
  rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, MulEquiv.apply_symm_apply, hm,
    map_mul, map_mul, map_mul, map_inv, map_inv]

theorem outAbelian_holds :
    ∀ (X : Type) [Group X] [Finite X], IsLThreePi X → IsQuasisimple X →
      ∀ σ τ : MulAut X, (∃ k : ℕ, σ ^ 3 ^ k = 1) → (∃ k : ℕ, τ ^ 3 ^ k = 1) →
        σ * τ * σ⁻¹ * τ⁻¹ ∈ (MulAut.conj : X →* MulAut X).range := by
  intro X _ _ hL hq σ τ ⟨a, ha⟩ ⟨b, hb⟩
  obtain ⟨p, e, hp, he, hiso⟩ := hL
  rcases hiso with ⟨hq3, ⟨φ⟩⟩ | ⟨hq3, ⟨φ⟩⟩
  ·
    obtain ⟨φ₀⟩ := nonempty_projSL_mulEquiv 3 (GaloisField p e)
    set ψ : X ≃* projectiveSL 3 (GaloisField p e) := φ.trans φ₀ with hψ
    refine comm_mem_range_conj_of_congr ψ ?_
    exact comm_mem_range_conj_of_pow (a := a) (b := b)
      (by rw [← map_pow, ha, map_one]) (by rw [← map_pow, hb, map_one])
  ·
    have hq2 : 2 < p ^ e := by
      have h2 : 2 ≤ p ^ e := le_trans hp.out.two_le (Nat.le_self_pow (by omega) _)
      by_contra hle
      have heq : p ^ e = 2 := by omega
      obtain ⟨rfl, rfl⟩ := Sec13.eq_two_one_of_pow_eq_two hp.out heq
      haveI := Sec13.isSolvable_projSU_two
      have hsol : Group.IsSolvable X :=
        Group.isSolvable_of_isSolvable_injective (f := φ.toMonoidHom) φ.injective
      haveI : Group.IsPerfect X := hq.1
      haveI : Nontrivial X := CFSG.LocalCores.isQuasisimple_nontrivial hq
      exact Group.IsPerfect.not_isSolvable X hsol
    have hG : Nat.card (GaloisField p (2 * e)) = p ^ (2 * e) :=
      GaloisField.card p (2 * e) (by omega)
    have h : UnitaryFieldData p e (GaloisField p (2 * e)) := ⟨hp.out, he, hG⟩
    obtain ⟨φ₀⟩ := nonempty_unitaryPSU_mulEquiv_projSU h
    set ψ : X ≃* unitaryPSU h 3 := φ.trans φ₀.symm with hψ
    refine comm_mem_range_conj_of_congr ψ ?_
    have := h.finite
    exact comm_mem_range_conj_of_pow_psu hq2 (a := a) (b := b)
      (by rw [← map_pow, ha, map_one]) (by rw [← map_pow, hb, map_one])

end CFSG.RankThree.PartTwo.Sec13.Ronan138W
