module

public import Mathlib.GroupTheory.Sylow

public section

open scoped Pointwise

namespace CFSG.RankThree.Co2

@[expose] noncomputable def sqrtCount {K : Type*} [Group K] (P : Subgroup K) (c : K) : ℕ :=
  Nat.card {y : P // (y : K) ^ 2 = c}

@[expose] def ExConjMul {K : Type*} [Group K] (P : Subgroup K) (c : K) : Prop :=
  ∃ u ∈ P, u * u = 1 ∧ u ≠ 1 ∧ ∃ w ∈ P, w * u * w⁻¹ = u * c

theorem sqrtCount_map {K L : Type*} [Group K] [Group L] (e : K ≃* L) (P : Subgroup K) (c : K) :
    sqrtCount (P.map e.toMonoidHom) (e c) = sqrtCount P c := by
  unfold sqrtCount
  symm
  refine Nat.card_congr ((e.subgroupMap P).toEquiv.subtypeEquiv fun y => ?_)
  change (y : K) ^ 2 = c ↔ (e (y : K)) ^ 2 = e c
  rw [← map_pow, e.injective.eq_iff]

theorem exConjMul_map {K L : Type*} [Group K] [Group L] (e : K ≃* L) (P : Subgroup K) (c : K) :
    ExConjMul (P.map e.toMonoidHom) (e c) ↔ ExConjMul P c := by
  constructor
  · rintro ⟨_, ⟨u, hu, rfl⟩, h2, h1, _, ⟨w, hw, rfl⟩, hc⟩
    refine ⟨u, hu, e.injective ?_, fun h => h1 (by simp [h]), w, hw, e.injective ?_⟩
    · simpa using h2
    · simpa using hc
  · rintro ⟨u, hu, h2, h1, w, hw, hc⟩
    refine ⟨e u, ⟨u, hu, rfl⟩, by rw [← map_mul, h2, map_one], fun h => h1 (e.injective
      (by rw [h, map_one])), e w, ⟨w, hw, rfl⟩, by rw [← map_inv, ← map_mul, ← map_mul, hc,
      map_mul]⟩

variable {X Y : Type*} [Group X] [Group Y] [Finite X] [Finite Y] {p : ℕ} [Fact p.Prime]

theorem exists_conj_map_sylow (Ψ : X ≃* Y) (P : Sylow p X) (Q : Sylow p Y) :
    ∃ g : Y, (Q : Subgroup Y) =
      ((P : Subgroup X).map Ψ.toMonoidHom).map (MulAut.conj g).toMonoidHom := by
  have hcard : Nat.card ((P : Subgroup X).map Ψ.toMonoidHom) =
      p ^ (Nat.card Y).factorization p := by
    rw [Subgroup.card_map_of_injective Ψ.injective, Sylow.card_eq_multiplicity,
      Nat.card_congr Ψ.toEquiv]
  set P' : Sylow p Y := Sylow.ofCard _ hcard
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Y P' Q
  refine ⟨g, ?_⟩
  rw [← hg, Sylow.coe_subgroup_smul]
  ext x
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, Subgroup.mem_map_equiv]
  simp [MulAut.smul_def, P']

theorem sqrtCount_sylow (Ψ : X ≃* Y) (P : Sylow p X) (Q : Sylow p Y) {c : X} {d : Y}
    (hd : ∀ y : Y, y * d = d * y) (hcd : Ψ c = d) :
    sqrtCount (Q : Subgroup Y) d = sqrtCount (P : Subgroup X) c := by
  obtain ⟨g, hQ⟩ := exists_conj_map_sylow Ψ P Q
  have hdg : (MulAut.conj g) d = d := by
    rw [MulAut.conj_apply, hd g, mul_inv_cancel_right]
  rw [hQ, ← hdg, sqrtCount_map, ← hcd, sqrtCount_map]

theorem exConjMul_sylow (Ψ : X ≃* Y) (P : Sylow p X) (Q : Sylow p Y) {c : X} {d : Y}
    (hd : ∀ y : Y, y * d = d * y) (hcd : Ψ c = d) :
    ExConjMul (Q : Subgroup Y) d ↔ ExConjMul (P : Subgroup X) c := by
  obtain ⟨g, hQ⟩ := exists_conj_map_sylow Ψ P Q
  have hdg : (MulAut.conj g) d = d := by
    rw [MulAut.conj_apply, hd g, mul_inv_cancel_right]
  rw [hQ, ← hdg, exConjMul_map, ← hcd, exConjMul_map]

end CFSG.RankThree.Co2
