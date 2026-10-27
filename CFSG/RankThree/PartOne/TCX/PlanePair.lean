module

public import CFSG.RankThree.PartOne.TCX.Plane
public import CFSG.RankThree.PartOne.K1214.OmegaAlg

public section

namespace CFSG.RankThree.PartOne.TCX

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.PartOne CFSG.LieType.Steinberg.Adjoint

section Pair

variable {τ : Tag} {K : Type} [Field K]

theorem plane_of_torus_pair [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (σ : K ≃+* K)
    (hrank : 0 < τ.rank) {a b : adjointGroup τ K}
    (ha : (a : ModGL τ K) ∈ torusGroup τ K) (hb : (b : ModGL τ K) ∈ torusGroup τ K)
    (hind : b ∉ Subgroup.zpowers a) (hab : Commute a b) (hao : orderOf a = p)
    (hbo : orderOf b = p) (hfa : entrywiseAdjointAut τ σ a = a)
    (hfb : entrywiseAdjointAut τ σ b = b) :
    ∃ R U : Subgroup (adjointGroup τ K),
      IsElementaryAbelian p ↥R ∧ Nat.card ↥R = p ^ 2 ∧
        (∀ r ∈ R, entrywiseAdjointAut τ σ r = r) ∧ U ≠ ⊥ ∧ IsPGroup 2 ↥U ∧
        (∀ u ∈ U, entrywiseAdjointAut τ σ u ∈ U) ∧
        R ≤ Subgroup.normalizer (U : Set (adjointGroup τ K)) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set J : Set (Fin τ.rank) := ∅ with hJdef
  have hJ : J ≠ Set.univ := by
    intro h
    have : (⟨0, hrank⟩ : Fin τ.rank) ∈ J := by rw [h]; trivial
    exact this
  have hLevi : ∀ t : ModGL τ K, t ∈ torusGroup τ K → t ∈ parabolicLevi τ K J := fun t ht =>
    (le_sup_left : torusGroup τ K ≤ torusGroup τ K ⊔ _) ht
  refine ⟨Subgroup.closure ({a, b} : Set (adjointGroup τ K)), parabolicRadicalIn τ K J, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · refine CFSG.RankThree.PartOne.K1214.isElementaryAbelian_closure (fun x hx y hy => ?_)
      (fun x hx => ?_)
    · rcases hx with hx | hx <;> rcases hy with hy | hy <;> rw [hx, hy]
      · exact hab.eq
      · exact hab.eq.symm
    · rcases hx with hx | hx <;> rw [hx]
      · rw [← hao]; exact pow_orderOf_eq_one _
      · rw [← hbo]; exact pow_orderOf_eq_one _
  · exact card_closure_pair hp hab hao hbo hind
  · intro r hr
    have hle : Subgroup.closure ({a, b} : Set (adjointGroup τ K)) ≤
        ((entrywiseAdjointAutHom (τ := τ) (K := K)) σ).toMonoidHom.eqLocus (MonoidHom.id _) := by
      rw [Subgroup.closure_le]
      rintro x (hx | hx) <;> rw [hx]
      · exact hfa
      · exact hfb
    exact hle hr
  · intro hU
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hQ⟩ :=
      parabolic_root_radical_Levi_factors (τ := τ) (K := K) J
    obtain ⟨-, -, hne⟩ := hQ 2
    apply hne hJ
    rw [eq_bot_iff]
    intro y hy
    have hyC : y ∈ adjointGroup τ K := parabolicRadical_le_adjointGroup J hy
    have : (⟨y, hyC⟩ : adjointGroup τ K) ∈ parabolicRadicalIn τ K J :=
      (mem_parabolicRadicalIn).2 hy
    rw [hU, Subgroup.mem_bot] at this
    exact (Subgroup.mem_bot).2 (congrArg Subtype.val this)
  · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hQ⟩ :=
      parabolic_root_radical_Levi_factors (τ := τ) (K := K) J
    obtain ⟨-, hQ2, -⟩ := hQ 2
    exact hQ2.comap_subtype
  · intro u hu
    rw [mem_parabolicRadicalIn] at hu ⊢
    rw [coe_entrywiseAdjointAut]
    exact entrywise_mem_radical J σ hu
  · rw [Subgroup.closure_le]
    rintro x (hx | hx) <;> rw [hx]
    · exact mem_normalizer_radicalIn J (hLevi _ ha)
    · exact mem_normalizer_radicalIn J (hLevi _ hb)

end Pair

end CFSG.RankThree.PartOne.TCX
