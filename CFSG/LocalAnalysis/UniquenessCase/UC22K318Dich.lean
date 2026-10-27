module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K318Four

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.K318

open Subgroup CFSG.RepresentationTheory
open CFSG.RankThree.SubgroupLists (IsIrreducibleOn)
open CFSG.LocalAnalysis.UniquenessCase.UC6.K318 (le_center_of_irreducible le_center_of_pCores
  le_or_eq_top_of_normal not_comm_of_simple)
open scoped Matrix

theorem le_center_or_not_twoCore_le {q : ℕ} [Fact q.Prime] {P : Subgroup (GL (Fin 4) (ZMod q))}
    [Group.IsPerfect P] (hirr : IsIrreducibleMatrixRep P.subtype) (R : Subgroup P) [R.Normal]
    (hRs : Group.IsSolvable R) :
    R ≤ center P ∨ ¬ (CFSG.pCore 2 R).map R.subtype ≤ center P := by
  by_cases h2 : (CFSG.pCore 2 R).map R.subtype ≤ center P
  · left
    refine le_center_of_pCores hRs fun s hs => ?_
    have hsp : s.Prime := Nat.prime_of_mem_primeFactors hs
    by_cases hs2 : s = 2
    · subst hs2
      exact h2
    haveI : Fact s.Prime := ⟨hsp⟩
    haveI : ((CFSG.pCore s R).map R.subtype).Normal := ConjAct.normal_of_characteristic_of_normal
    have hSp : IsPGroup s ((CFSG.pCore s R).map R.subtype) :=
      (CFSG.pCore_isPGroup (p := s) (G := R)).map R.subtype
    have hSs : Group.IsSolvable ((CFSG.pCore s R).map R.subtype) := by
      haveI := hSp.isNilpotent
      infer_instance
    have hSodd : Odd (Nat.card ((CFSG.pCore s R).map R.subtype)) := by
      obtain ⟨k, hk⟩ := hSp.exists_card_eq
      rw [hk]
      exact (hsp.odd_of_ne_two hs2).pow
    refine le_center_of_irreducible le_rfl (fun t ht ht4 => ?_) hirr _ hSs hSodd
    exact (Nat.prime_dvd_prime_iff_eq ht Nat.prime_two).1
      (ht.dvd_of_dvd_pow (show t ∣ 2 ^ 2 by norm_num; exact ht4))
  · exact Or.inr h2

theorem eq_center_of_le_center {P : Type} [Group P] [Finite P] [Group.IsPerfect P]
    {R : Subgroup P} [R.Normal] (hRs : Group.IsSolvable R) (hs : IsSimpleGroup (P ⧸ R))
    (hR : R ≤ center P) : R = center P ∧ CFSG.IsQuasisimple P := by
  have hZR : center P ≤ R := by
    rcases le_or_eq_top_of_normal hRs hs (center P) with h | h
    · exact h
    · exfalso
      exact not_comm_of_simple hs fun a b => (mem_center_iff.1 (h ▸ mem_top b) a)
  have hRZ : R = center P := le_antisymm hR hZR
  have hsZ : IsSimpleGroup (P ⧸ center P) :=
    (MulEquiv.isSimpleGroup_congr (QuotientGroup.quotientMulEquivOfEq hRZ)).1 hs
  refine ⟨hRZ, inferInstance, hsZ, ?_⟩
  by_contra h
  push Not at h
  have : Nontrivial (P ⧸ center P) := IsSimpleGroup.toNontrivial
  exact Group.IsPerfect.not_isMulCommutative (P ⧸ center P) ⟨⟨h⟩⟩

variable {L : Type} [Group L] [Finite L]

theorem isIrreducibleOn_comp {q : ℕ} [Fact q.Prime] {σ : Type} [Fintype σ] [DecidableEq σ]
    {τ : GL (Fin 4) (ZMod q) ≃* GL σ (ZMod q)} {c : (Fin 4 → ZMod q) ≃ₗ[ZMod q] (σ → ZMod q)}
    (hτc : ∀ (M : GL (Fin 4) (ZMod q)) (v : Fin 4 → ZMod q),
      (τ M : Matrix σ σ (ZMod q)) *ᵥ c v = c ((M : Matrix (Fin 4) (Fin 4) (ZMod q)) *ᵥ v))
    {φ : L →* GL (Fin 4) (ZMod q)} (hirr : IsIrreducibleMatrixRep φ) :
    IsIrreducibleOn (τ.toMonoidHom.comp φ).range := by
  intro W hW
  have hW' : ∀ g, ∀ w ∈ W.comap c.toLinearMap,
      (φ g : Matrix (Fin 4) (Fin 4) (ZMod q)) *ᵥ w ∈ W.comap c.toLinearMap := by
    intro g w hw
    rw [Submodule.mem_comap, LinearEquiv.coe_coe] at hw ⊢
    rw [← hτc]
    exact hW _ ⟨g, rfl⟩ _ hw
  rcases hirr _ hW' with h | h
  · left
    rw [eq_bot_iff]
    intro w hw
    have h1 : c.symm w ∈ W.comap c.toLinearMap := by
      rw [Submodule.mem_comap, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
      exact hw
    rw [h, Submodule.mem_bot] at h1
    rw [Submodule.mem_bot, ← c.apply_symm_apply w, h1, map_zero]
  · right
    rw [eq_top_iff]
    intro w _
    have h1 : c.symm w ∈ W.comap c.toLinearMap := h ▸ Submodule.mem_top
    rw [Submodule.mem_comap, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at h1
    exact h1

theorem range_comp_equiv {G H : Type*} [Group G] [Group H] (τ : G ≃* H) (φ : L →* G) :
    ∃ e : φ.range ≃* (τ.toMonoidHom.comp φ).range,
      ∀ g : L, e (φ.rangeRestrict g) = (τ.toMonoidHom.comp φ).rangeRestrict g := by
  refine ⟨(φ.range.equivMapOfInjective τ.toMonoidHom τ.injective).trans
    (MulEquiv.subgroupCongr (MonoidHom.range_comp τ.toMonoidHom φ).symm), fun g => ?_⟩
  apply Subtype.ext
  rfl

end CFSG.LocalAnalysis.UniquenessCase.UC22.K318
