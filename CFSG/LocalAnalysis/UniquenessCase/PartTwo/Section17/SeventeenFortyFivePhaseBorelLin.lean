module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagData
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperUnitriangular.Basic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFivePhaseBorelBruhat
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFivePhaseBorelTorus
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrLin
import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossOutBase
import CFSG.RankThree.PartTwo.KFacts.K72L3Group

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive

open Subgroup CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped commutatorElement Pointwise

theorem congr_conjNormal_mem_linearAutGroup {X : Type*} [Group X] {L A B : Subgroup X} [L.Normal]
    {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 3 ≤ n) (e : ↥L ≃* projectiveSL n K)
    (hAB : ⁅A, B⁆ = A) {a : X} (ha : a ∈ A) :
    MulAut.congr e (MulAut.conjNormal a) ∈ linearAutGroup n K := by
  set Ψ : X →* MulAut (projectiveSL n K) :=
    (MulAut.congr e).toMonoidHom.comp MulAut.conjNormal with hΨ
  have hle : A ≤ (linearAutGroup n K).comap Ψ := by
    rw [← hAB, Subgroup.commutator_le]
    intro x hx y hy
    rw [Subgroup.mem_comap, commutatorElement_def]
    simp only [map_mul, map_inv]
    exact CFSG.LocalAnalysis.ComponentInitial.OuterDerived.commutator_mem_linearAutGroup
      (K := K) hn (Ψ x) (Ψ y)
  exact hle ha

theorem exists_abelian_of_congr_conjNormal_mem {X : Type} [Group X] [Finite X]
    {L A S : Subgroup X} [L.Normal] (hcen : centralizer (L : Set X) = ⊥)
    {K : Type*} [Field K] {n : ℕ} (e : ↥L ≃* projectiveSL n K) (hSL : S ≤ L)
    (hS : ∀ s : ↥L, (s : X) ∈ S ↔ e s ∈ projUnitriangular n K)
    (hA : ∀ a ∈ A, MulAut.congr e (MulAut.conjNormal a) ∈
      (TauCeti.diagonalTorus K n).map (conjAut n K)) :
    ∃ C : Subgroup X, IsMulCommutative C ∧ A ≤ C ∧ L ≤ S ⊔ (L ⊓ normalizer (C : Set X)) := by
  set Ψ : X →* MulAut (projectiveSL n K) :=
    (MulAut.congr e).toMonoidHom.comp MulAut.conjNormal with hΨ
  set D : Subgroup (MulAut (projectiveSL n K)) :=
    (TauCeti.diagonalTorus K n).map (conjAut n K)
  set N : Subgroup (projectiveSL n K) :=
    (normalizer (D : Set (MulAut (projectiveSL n K)))).comap
      (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K))
  have hinj : Function.Injective Ψ :=
    (MulAut.congr e).injective.comp
      (CFSG.LocalAnalysis.RankFourTheoremC.conjNormal_injective L hcen)
  have hΨy : ∀ y : ↥L, Ψ ((y : ↥L) : X) = MulAut.conj (e y) := by
    intro y
    rw [hΨ, MonoidHom.comp_apply, MulAut.conjNormal_val, MulEquiv.coe_toMonoidHom]
    ext w
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulAut.conj_apply, map_mul, map_inv,
      MulEquiv.apply_symm_apply]
  refine ⟨D.comap Ψ, Subgroup.comap_injective_isMulCommutative D hinj,
    fun a ha => hA a ha, ?_⟩
  have htop : projUnitriangular n K ⊔ N = ⊤ :=
    projUnitriangular_sup_comap_normalizer_eq_top
  have hS_eq : ((projUnitriangular n K).comap e.toMonoidHom).map L.subtype = S := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩; exact (hS y).mpr hy
    · intro hx; exact ⟨⟨x, hSL hx⟩, (hS ⟨x, hSL hx⟩).mp hx, rfl⟩
  have hN_le : (N.comap e.toMonoidHom).map L.subtype ≤ L ⊓ normalizer (D.comap Ψ : Set X) := by
    rintro x ⟨y, hy, rfl⟩
    exact Subgroup.mem_inf.mpr ⟨y.2, Subgroup.le_normalizer_comap (H := D) Ψ (by
      show Ψ ((y : ↥L) : X) ∈ normalizer (D : Set (MulAut (projectiveSL n K)))
      rw [hΨy y]
      exact Subgroup.mem_comap.mp hy)⟩
  have htop' : (projUnitriangular n K).comap e.toMonoidHom ⊔ N.comap e.toMonoidHom = ⊤ := by
    rw [Subgroup.comap_equiv_eq_map_symm', Subgroup.comap_equiv_eq_map_symm',
      ← Subgroup.map_sup, htop, Subgroup.map_top_of_surjective _ e.symm.surjective]
  have hsup : S ⊔ (N.comap e.toMonoidHom).map L.subtype = L := by
    rw [← hS_eq, ← Subgroup.map_sup, htop', Subgroup.map_top, Subgroup.range_subtype]
  exact hsup.symm.trans_le (sup_le le_sup_left (le_trans hN_le le_sup_right))

theorem exists_trans_conj_mem_projUnitriangular {X : Type} [Group X] [Finite X]
    {L S : Subgroup X} [L.Normal] {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hn : 1 ≤ n) (e : ↥L ≃* projectiveSL n K) (hS : CFSG.ABGLocalTools.IsSylowOf 2 S L) :
    ∃ g : projectiveSL n K, ∀ s : ↥L,
      (s : X) ∈ S ↔ (e.trans (MulAut.conj g)) s ∈ projUnitriangular n K := by
  obtain ⟨Q, hQ⟩ := hS
  have hSl : S.subgroupOf L = (Q : Subgroup ↥L) := by
    rw [← hQ, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective L.subtype_injective]
  obtain ⟨U₀, hU₀⟩ := exists_sylow_projUnitriangular (K := K) 2 hn
  set Q' : Sylow 2 (projectiveSL n K) :=
    Sylow.mapSurjective (f := e.toMonoidHom) e.surjective Q with hQ'def
  have hQ'coe : (Q' : Subgroup (projectiveSL n K)) =
      (Q : Subgroup ↥L).map e.toMonoidHom :=
    Sylow.coe_mapSurjective (f := e.toMonoidHom) e.surjective Q
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (projectiveSL n K) U₀ Q'
  have hg' : MulAut.conj g • (U₀ : Subgroup (projectiveSL n K)) =
      (Q' : Subgroup (projectiveSL n K)) := by
    rw [← Sylow.coe_subgroup_smul, hg]
  have hmemQ' : ∀ s : ↥L, (s : X) ∈ S ↔ e s ∈ (Q' : Subgroup (projectiveSL n K)) := by
    intro s
    have h1 : (s : X) ∈ S ↔ (s : ↥L) ∈ (Q : Subgroup ↥L) := by
      rw [← hSl]
      exact Subgroup.mem_subgroupOf.symm
    have h2 : (s : ↥L) ∈ (Q : Subgroup ↥L) ↔
        e s ∈ (Q' : Subgroup (projectiveSL n K)) := by
      rw [hQ'coe, Subgroup.mem_map]
      exact ⟨fun h => ⟨s, h, rfl⟩, fun ⟨x, hx, hxs⟩ => (e.injective hxs).symm ▸ hx⟩
    exact h1.trans h2
  have h3 : ∀ s : ↥L, e s ∈ (Q' : Subgroup (projectiveSL n K)) ↔
      MulAut.conj g⁻¹ (e s) ∈ projUnitriangular n K := by
    intro s
    rw [← hg', Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv,
      MulAut.smul_def, hU₀]
  refine ⟨g⁻¹, fun s => ?_⟩
  rw [MulEquiv.trans_apply]
  exact (hmemQ' s).trans (h3 s)

theorem congr_conjNormal_mem_sup_of_mem_normalizer {X : Type} [Group X]
    {L A B S : Subgroup X} [L.Normal] {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hn : 3 ≤ n) (e : ↥L ≃* projectiveSL n K) (hAB : ⁅A, B⁆ = A)
    (hS : ∀ s : ↥L, (s : X) ∈ S ↔ e s ∈ projUnitriangular n K)
    {a : X} (ha : a ∈ A) (hSa : a ∈ normalizer (S : Set X)) :
    MulAut.congr e (MulAut.conjNormal a) ∈
      (TauCeti.upperUnitriangularGroup (Fin n) K).map (conjAut n K) ⊔
        (TauCeti.diagonalTorus K n).map (conjAut n K) := by
  obtain ⟨A₀, hA₀⟩ := mem_linearAutGroup_iff.mp
    (congr_conjNormal_mem_linearAutGroup (K := K) hn e hAB ha)
  have hnorm : ∀ w : projectiveSL n K, w ∈ projUnitriangular n K ↔
      conjAut n K A₀ w ∈ projUnitriangular n K := by
    intro w
    obtain ⟨y, rfl⟩ : ∃ y : ↥L, e y = w := ⟨e.symm w, e.apply_symm_apply w⟩
    have hstep : conjAut n K A₀ (e y) = e (MulAut.conjNormal a y) := by
      rw [hA₀, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
        MulEquiv.symm_apply_apply]
    rw [hstep, ← hS y, ← hS (MulAut.conjNormal a y), MulAut.conjNormal_apply]
    exact Subgroup.mem_normalizer_iff.mp hSa ((y : ↥L) : X)
  have htri : (A₀ : Matrix (Fin n) (Fin n) K).IsUpperTriangular :=
    CFSG.AGLEmbedding.ParabAutIrr.isUpperTriangular_of_normalizes (by omega) hnorm
  rw [← hA₀]
  exact conjAut_mem_sup_of_isUpperTriangular htri

theorem congr_trans_conjAut_mem_diagonalTorus {X : Type} [Group X]
    {L A : Subgroup X} [L.Normal] {K : Type} [Field K] {n : ℕ}
    (e : ↥L ≃* projectiveSL n K) (u : GL (Fin n) K)
    (hA : ∀ a ∈ A, MulAut.congr e (MulAut.conjNormal a) ∈
      ((TauCeti.diagonalTorus K n).map (conjAut n K)).map
        (MulAut.conj (conjAut n K u)).toMonoidHom) :
    ∀ a ∈ A, MulAut.congr (e.trans (conjAut n K u⁻¹)) (MulAut.conjNormal a) ∈
      (TauCeti.diagonalTorus K n).map (conjAut n K) := by
  intro a ha
  obtain ⟨d, hd, hdval⟩ := Subgroup.mem_map.mp (hA a ha)
  rw [MulEquiv.coe_toMonoidHom] at hdval
  have hconj := CFSG.RankThree.PartTwo.KFacts.congr_trans_mulAut e (conjAut n K u⁻¹)
    (MulAut.conjNormal a)
  have hcoe : conjAut n K u⁻¹ = (conjAut n K u)⁻¹ := map_inv (conjAut n K) u
  have hd' : (conjAut n K u)⁻¹ * MulAut.conj (conjAut n K u) d *
      ((conjAut n K u)⁻¹)⁻¹ = d := by
    rw [MulAut.conj_apply]
    group
  rw [hconj, hdval.symm, hcoe, hd']
  exact hd

theorem exists_abelian_of_projectiveSL {X : Type} [Group X] [Finite X]
    {L A B S : Subgroup X} [L.Normal] (hcen : centralizer (L : Set X) = ⊥)
    {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} (hn : 3 ≤ n)
    (e : ↥L ≃* projectiveSL n K) (hA : Odd (Nat.card A)) (hAB : ⁅A, B⁆ = A)
    (hS : CFSG.ABGLocalTools.IsSylowOf 2 S L) (hAS : A ≤ normalizer (S : Set X)) :
    ∃ C : Subgroup X, IsMulCommutative C ∧ A ≤ C ∧ L ≤ S ⊔ (L ⊓ normalizer (C : Set X)) := by
  obtain ⟨g, hg⟩ := exists_trans_conj_mem_projUnitriangular (K := K) (by omega) e hS
  set e₁ : ↥L ≃* projectiveSL n K := e.trans (MulAut.conj g) with he₁
  set Ψ₁ : X →* MulAut (projectiveSL n K) :=
    (MulAut.congr e₁).toMonoidHom.comp MulAut.conjNormal with hΨ₁
  have hS₁ : ∀ s : ↥L, (s : X) ∈ S ↔ e₁ s ∈ projUnitriangular n K := by
    intro s
    rw [he₁]
    exact hg s
  have hmem : ∀ a ∈ A, Ψ₁ a ∈
      (TauCeti.upperUnitriangularGroup (Fin n) K).map (conjAut n K) ⊔
        (TauCeti.diagonalTorus K n).map (conjAut n K) := fun a ha =>
    congr_conjNormal_mem_sup_of_mem_normalizer (K := K) hn e₁ hAB hS₁ ha (hAS ha)
  have hE : A.map Ψ₁ ≤ (TauCeti.upperUnitriangularGroup (Fin n) K).map (conjAut n K) ⊔
      (TauCeti.diagonalTorus K n).map (conjAut n K) := by
    rintro _ ⟨a, ha, rfl⟩
    exact hmem a ha
  have hinjΨ₁ : Function.Injective Ψ₁ := by
    intro x y hxy
    exact CFSG.LocalAnalysis.RankFourTheoremC.conjNormal_injective L hcen
      ((MulAut.congr e₁).injective hxy)
  have hEo : Odd (Nat.card (A.map Ψ₁)) := by
    rw [Subgroup.card_map_of_injective hinjΨ₁]
    exact hA
  obtain ⟨u, hu, hEu⟩ := exists_le_map_conj_map_diagonalTorus hE hEo
  have hA₂ : ∀ a ∈ A, MulAut.congr (e₁.trans (conjAut n K u⁻¹)) (MulAut.conjNormal a) ∈
      (TauCeti.diagonalTorus K n).map (conjAut n K) := fun a ha =>
    congr_trans_conjAut_mem_diagonalTorus e₁ u
      (fun b hb => hEu (Subgroup.mem_map_of_mem Ψ₁ hb)) a ha
  exact exists_abelian_of_congr_conjNormal_mem hcen (e₁.trans (conjAut n K u⁻¹)) hS.le
    (fun s => by
      rw [hS₁ s, MulEquiv.trans_apply]
      exact (conjAut_mem_projUnitriangular_iff
        ((TauCeti.upperUnitriangularGroup (Fin n) K).inv_mem hu) (e₁ s)).symm)
    hA₂

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive
