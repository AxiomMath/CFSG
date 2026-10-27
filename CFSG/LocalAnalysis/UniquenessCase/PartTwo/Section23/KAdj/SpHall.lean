module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagTriangular
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.Hall
import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial
open SymplecticFlag (borelSubgroup unipotent diagHom)

private theorem diagHom_torusHom_C02 {K : Type} [Field K] {r : ℕ} (s : Fin r → Kˣ)
    (h : SymplecticTorusWeyl.torusHom s ∈ SymplecticFlag.borelSubgroup r K) :
    SymplecticFlag.diagHom r K ⟨SymplecticTorusWeyl.torusHom s, h⟩ = s := by
  funext i
  apply Units.ext
  rw [SymplecticFlag.coe_diagHom_apply]
  simp [SymplecticTorusWeyl.coe_torusHom]

private theorem isPGroup_unipotent_C02 {K : Type} [Field K] [Finite K] [CharP K 2] (r : ℕ) :
    IsPGroup 2 (SymplecticFlag.unipotent r K) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := SymplecticFlag.exists_sylow_unipotent (K := K) 2 r
  rw [← hP]
  exact P.isPGroup'

private theorem not_two_dvd_card_units_C02 {K : Type} [Field K] [Finite K] [CharP K 2] :
    ¬ 2 ∣ Nat.card Kˣ := by
  intro h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 2 h
  have hu2 : u ^ 2 = 1 := by
    rw [← hu]
    exact pow_orderOf_eq_one u
  have hK2 : (u : K) ^ 2 = 1 := by
    have := congrArg (fun x : Kˣ => (x : K)) hu2
    simpa using this
  have hc : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have h2 : ((u : K) - 1) ^ 2 = (u : K) ^ 2 + 1 := by
    rw [sub_sq, hc]
    ring
  have hsq : ((u : K) - 1) ^ 2 = 0 := by
    rw [h2, hK2, one_add_one_eq_two]
    exact hc
  have hu1 : (u : K) = 1 := sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp hsq)
  have hu1' : u = 1 := Units.ext (by simpa using hu1)
  have hone : orderOf u = 1 := by
    rw [hu1']
    exact orderOf_one
  omega

private theorem not_dvd_card_torus_C02 {K : Type} [Field K] [Finite K] [CharP K 2] (r : ℕ) :
    ¬ 2 ∣ Nat.card (SymplecticTorusWeyl.torus r K) := by
  intro h
  let e := MonoidHom.ofInjective (f := SymplecticTorusWeyl.torusHom (r := r) (k := K))
    (SymplecticTorusWeyl.torusHom_injective (r := r) (k := K))
  have hcard : Nat.card (SymplecticTorusWeyl.torus r K) = Nat.card (Fin r → Kˣ) :=
    (Nat.card_congr e.toEquiv).symm
  rw [hcard, Nat.card_pi] at h
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  exact not_two_dvd_card_units_C02 (Nat.Prime.dvd_of_dvd_pow Nat.prime_two h)

private theorem torus_le_normalizer_unipotent_C02 {K : Type} [Field K] (r : ℕ) :
    SymplecticTorusWeyl.torus r K ≤
      Subgroup.normalizer (SymplecticFlag.unipotent r K : Set (StatedSp r K)) := by
  have hconjU : ∀ x ∈ SymplecticFlag.borelSubgroup r K, ∀ y ∈ SymplecticFlag.unipotent r K,
      x * y * x⁻¹ ∈ SymplecticFlag.unipotent r K := by
    intro x hx y hy
    have hN := SymplecticFlag.unipotent_subgroupOf_borelSubgroup_normal (r := r) (K := K)
    have hmem := hN.conj_mem ⟨y, SymplecticFlag.unipotent_le_borelSubgroup hy⟩
      (Subgroup.mem_subgroupOf.mpr hy) ⟨x, hx⟩
    simpa using Subgroup.mem_subgroupOf.mp hmem
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    exact hconjU x (SymplecticFlag.torus_le_borelSubgroup hx) y hy
  · intro hy
    have hxin : x⁻¹ ∈ SymplecticFlag.borelSubgroup r K :=
      Subgroup.inv_mem _ (SymplecticFlag.torus_le_borelSubgroup hx)
    have hthis := hconjU x⁻¹ hxin (x * y * x⁻¹) hy
    rwa [show x⁻¹ * (x * y * x⁻¹) * (x⁻¹)⁻¹ = y by group] at hthis

private theorem mul_inv_torusHom_mem_unipotent_C02 {K : Type} [Field K] {r : ℕ}
    {t : StatedSp r K} (ht : t ∈ SymplecticFlag.borelSubgroup r K) :
    t * (SymplecticTorusWeyl.torusHom (SymplecticFlag.diagHom r K ⟨t, ht⟩))⁻¹ ∈
      SymplecticFlag.unipotent r K := by
  have hτB : SymplecticTorusWeyl.torusHom (SymplecticFlag.diagHom r K ⟨t, ht⟩) ∈
      SymplecticFlag.borelSubgroup r K :=
    SymplecticFlag.torus_le_borelSubgroup
      (SymplecticTorusWeyl.torusHom_mem_torus (SymplecticFlag.diagHom r K ⟨t, ht⟩))
  have hker : (⟨t, ht⟩ * ⟨SymplecticTorusWeyl.torusHom (SymplecticFlag.diagHom r K ⟨t, ht⟩),
      hτB⟩⁻¹ : ↥(SymplecticFlag.borelSubgroup r K)) ∈ (SymplecticFlag.diagHom r K).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv,
      diagHom_torusHom_C02 (SymplecticFlag.diagHom r K ⟨t, ht⟩) hτB, mul_inv_cancel]
  rw [SymplecticFlag.ker_diagHom, Subgroup.mem_subgroupOf] at hker
  simpa using hker

theorem exists_conj_eq_torusHom_diagHom_sp {K : Type} [Field K] [Finite K] [CharP K 2] {r : ℕ}
    {t : StatedSp r K} (ht : t ∈ borelSubgroup r K) (hodd : ¬ 2 ∣ orderOf t) :
    ∃ e ∈ unipotent r K,
      e * t * e⁻¹ = SymplecticTorusWeyl.torusHom (diagHom r K ⟨t, ht⟩) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htsup : t ∈ SymplecticFlag.unipotent r K ⊔ SymplecticTorusWeyl.torus r K := by
    have hsplit : t =
        (t * (SymplecticTorusWeyl.torusHom (SymplecticFlag.diagHom r K ⟨t, ht⟩))⁻¹) *
          SymplecticTorusWeyl.torusHom (SymplecticFlag.diagHom r K ⟨t, ht⟩) := by group
    rw [hsplit]
    exact Subgroup.mul_mem_sup (mul_inv_torusHom_mem_unipotent_C02 ht)
      (SymplecticTorusWeyl.torusHom_mem_torus (SymplecticFlag.diagHom r K ⟨t, ht⟩))
  obtain ⟨e, he, hconj⟩ := exists_conj_mem_of_mem_sup (torus_le_normalizer_unipotent_C02 r)
    (isPGroup_unipotent_C02 r) (not_dvd_card_torus_C02 r) htsup hodd
  obtain ⟨s', hs'⟩ := MonoidHom.mem_range.mp hconj
  have heB : e ∈ SymplecticFlag.borelSubgroup r K := SymplecticFlag.unipotent_le_borelSubgroup he
  have heteB : e * t * e⁻¹ ∈ SymplecticFlag.borelSubgroup r K :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ heB ht) (Subgroup.inv_mem _ heB)
  have he1 : SymplecticFlag.diagHom r K ⟨e, heB⟩ = 1 := by
    have hker : (⟨e, heB⟩ : ↥(SymplecticFlag.borelSubgroup r K)) ∈
        (SymplecticFlag.diagHom r K).ker := by
      rw [SymplecticFlag.ker_diagHom, Subgroup.mem_subgroupOf]
      exact he
    simpa only [MonoidHom.mem_ker] using hker
  have h3 : SymplecticFlag.diagHom r K ⟨e * t * e⁻¹, heteB⟩ =
      SymplecticFlag.diagHom r K ⟨e, heB⟩ * SymplecticFlag.diagHom r K ⟨t, ht⟩ *
        (SymplecticFlag.diagHom r K ⟨e, heB⟩)⁻¹ := by
    rw [show (⟨e * t * e⁻¹, heteB⟩ : ↥(SymplecticFlag.borelSubgroup r K)) =
        ⟨e, heB⟩ * ⟨t, ht⟩ * ⟨e, heB⟩⁻¹ from Subtype.ext rfl]
    simp only [map_mul, map_inv]
  have hs'_eq : s' = SymplecticFlag.diagHom r K ⟨t, ht⟩ := by
    calc s' = SymplecticFlag.diagHom r K ⟨SymplecticTorusWeyl.torusHom s',
          SymplecticFlag.torus_le_borelSubgroup
            (SymplecticTorusWeyl.torusHom_mem_torus s')⟩ :=
          (diagHom_torusHom_C02 s' _).symm
      _ = SymplecticFlag.diagHom r K ⟨e * t * e⁻¹, heteB⟩ :=
            congrArg (SymplecticFlag.diagHom r K) (Subtype.ext hs')
      _ = SymplecticFlag.diagHom r K ⟨e, heB⟩ * SymplecticFlag.diagHom r K ⟨t, ht⟩ *
            (SymplecticFlag.diagHom r K ⟨e, heB⟩)⁻¹ := h3
      _ = SymplecticFlag.diagHom r K ⟨t, ht⟩ := by simp [he1]
  refine ⟨e, he, ?_⟩
  calc e * t * e⁻¹ = SymplecticTorusWeyl.torusHom s' := hs'.symm
    _ = SymplecticTorusWeyl.torusHom (SymplecticFlag.diagHom r K ⟨t, ht⟩) :=
        congrArg SymplecticTorusWeyl.torusHom hs'_eq

end CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE
