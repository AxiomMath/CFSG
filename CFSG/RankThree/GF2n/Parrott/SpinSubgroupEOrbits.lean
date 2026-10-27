module

public import CFSG.RankThree.GF2n.Parrott.SpinSubgroupE
public import CFSG.RankThree.GF2n.Parrott.SpinOrbitFacts

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open Subgroup
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open scoped Matrix commutatorElement

set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
set_option quotPrecheck false in
local notation "GL8" => Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)
set_option quotPrecheck false in
local notation "Mat8" => Matrix (Fin 8) (Fin 8) (ZMod 2)

variable {G : Type} [Group G] [Finite G] {z : G}
variable {κ : G → V}

section Orbit

variable (D : QuotientData (z := z) (J_subgroupOf_normal z))

theorem twenty_le_ncard_orbit_of_mem_spinFixE (h : Tim79a.ParrottHypA z)
    (hκ : IsSpinCoord (qH D) κ) {e : G} (he : e ∈ spinFixE hκ) (heJ : e ∉ J z) :
    20 ≤ Set.ncard {y : G | ∃ m ∈ Subgroup.normalizer (spinFixE hκ : Set G) ⊓ H z,
      y = m * e * m⁻¹} := by
  classical
  have heH : e ∈ H z := spinFixE_le_H hκ he
  have hsS : qH D ⟨e, heH⟩ ∈ sQA45 := qH_mem_sQA45_of_mem_spinFixE hκ heH he
  have hs1 : qH D ⟨e, heH⟩ ≠ 1 := fun h1 => heJ ((hκ.eq_one_iff ⟨e, heH⟩).mp h1)
  have hLam := twenty_le_ncard_orbit_mul_ncard_rangeRho hsS hs1
  set s : A45 := qH D ⟨e, heH⟩ with hs
  set O : Set G := {y : G | ∃ m ∈ Subgroup.normalizer (spinFixE hκ : Set G) ⊓ H z,
    y = m * e * m⁻¹} with hO
  let π : G → A45 := fun y => if hy : y ∈ H z then qH D ⟨y, hy⟩ else 1
  have hπ : ∀ (y : G) (hy : y ∈ H z), π y = qH D ⟨y, hy⟩ := fun y hy => by simp [π, hy]
  have hconjπ : ∀ (m : G) (hm : m ∈ H z),
      π (m * e * m⁻¹) = qH D ⟨m, hm⟩ * s * (qH D ⟨m, hm⟩)⁻¹ := by
    intro m hm
    have hy : m * e * m⁻¹ ∈ H z := mul_mem (mul_mem hm heH) (inv_mem hm)
    rw [hπ _ hy]
    have : (⟨m * e * m⁻¹, hy⟩ : ↥(H z)) = ⟨m, hm⟩ * ⟨e, heH⟩ * ⟨m, hm⟩⁻¹ := rfl
    rw [this, map_mul, map_mul, map_inv]
  have hmaps : ∀ y ∈ (Set.toFinite O).toFinset,
      π y ∈ (Set.toFinite (normalizerOrbit s)).toFinset := by
    intro y hy
    rw [Set.Finite.mem_toFinset] at hy ⊢
    obtain ⟨m, hm, rfl⟩ := hy
    obtain ⟨hmN, hmH⟩ := Subgroup.mem_inf.mp hm
    refine ⟨qH D ⟨m, hmH⟩, (mem_normalizer_spinFixE_iff h hκ hmH).mp hmN, ?_⟩
    exact hconjπ m hmH
  have hfib : ∀ b ∈ (Set.toFinite (normalizerOrbit s)).toFinset,
      (rangeRho s).ncard ≤ ((Set.toFinite O).toFinset.filter fun y => π y = b).card := by
    intro b hb
    rw [Set.Finite.mem_toFinset] at hb
    obtain ⟨a, haN, rfl⟩ := hb
    obtain ⟨m₀, hm₀⟩ := hκ.surjective a
    have hm₀N : (m₀ : G) ∈ Subgroup.normalizer (spinFixE hκ : Set G) :=
      (mem_normalizer_spinFixE_iff h hκ m₀.2).mpr (by
        have : qH D ⟨(m₀ : G), m₀.2⟩ = a := hm₀
        rw [this]
        exact haN)
    have hm₀a : qH D ⟨(m₀ : G), m₀.2⟩ = a := hm₀
    set e' : G := (m₀ : G) * e * (m₀ : G)⁻¹ with he'
    have he'H : e' ∈ H z := mul_mem (mul_mem m₀.2 heH) (inv_mem m₀.2)
    have hπe' : π e' = a * s * a⁻¹ := by
      rw [he', hconjπ _ m₀.2, hm₀a]
    set Jorb : Set G := {y : G | ∃ j ∈ J z, y = j * e' * j⁻¹} with hJorb
    have hJsub : Jorb ⊆ ↑((Set.toFinite O).toFinset.filter fun y => π y = a * s * a⁻¹) := by
      rintro _ ⟨j, hj, rfl⟩
      rw [Finset.coe_filter, Set.mem_setOf_eq, Set.Finite.mem_toFinset]
      have hjH : j ∈ H z := J_le_H hj
      have hjN : j * (m₀ : G) ∈ Subgroup.normalizer (spinFixE hκ : Set G) ⊓ H z :=
        Subgroup.mem_inf.mpr ⟨mul_mem (J_le_normalizer_spinFixE h hκ hj) hm₀N, mul_mem hjH m₀.2⟩
      refine ⟨⟨j * (m₀ : G), hjN, ?_⟩, ?_⟩
      · rw [he']
        group
      · have h1 : j * e' * j⁻¹ ∈ H z := mul_mem (mul_mem hjH he'H) (inv_mem hjH)
        rw [hπ _ h1]
        have : (⟨j * e' * j⁻¹, h1⟩ : ↥(H z)) = ⟨j, hjH⟩ * ⟨e', he'H⟩ * ⟨j, hjH⟩⁻¹ := rfl
        rw [this, map_mul, map_mul, map_inv, (hκ.eq_one_iff ⟨j, hjH⟩).mpr hj, one_mul, inv_one,
          mul_one, ← hπ _ he'H, hπe']
    have hrange : rangeRho (a * s * a⁻¹) ⊆ (fun y : G => κ (y * e'⁻¹)) '' Jorb := by
      rintro _ ⟨v, rfl⟩
      obtain ⟨j, hj, hjv⟩ := hκ.surj v
      refine ⟨j * e' * j⁻¹, ⟨j, hj, rfl⟩, ?_⟩
      show κ (j * e' * j⁻¹ * e'⁻¹) = _
      have hJn : e' * j⁻¹ * e'⁻¹ ∈ J z :=
        (mem_normalizer_iff.mp (J_le_normalizer_A he'H) j⁻¹).mp (inv_mem hj)
      have : j * e' * j⁻¹ * e'⁻¹ = j * (e' * j⁻¹ * e'⁻¹) := by group
      rw [this, hκ.add j hj _ hJn, hκ.act e' he'H j⁻¹ (inv_mem hj), hκ.kappa_inv hj, hjv]
      have h2 : qH D ⟨e', he'H⟩ = a * s * a⁻¹ := by rw [← hπ _ he'H, hπe']
      rw [h2, add_comm]
    have hr1 := Set.ncard_le_ncard hrange ((Set.toFinite Jorb).image _)
    have hr2 := Set.ncard_image_le (f := fun y : G => κ (y * e'⁻¹)) (Set.toFinite Jorb)
    have hr3 := Set.ncard_le_ncard hJsub (Finset.finite_toSet _)
    rw [Set.ncard_coe_finset] at hr3
    rw [ncard_rangeRho_conj] at hr1
    omega
  have hmul := Finset.mul_card_image_le_card_of_maps_to hmaps (rangeRho s).ncard hfib
  rw [← Set.ncard_eq_toFinset_card _ (Set.toFinite _),
    ← Set.ncard_eq_toFinset_card _ (Set.toFinite _)] at hmul
  have := Nat.mul_comm (normalizerOrbit s).ncard (rangeRho s).ncard
  omega

end Orbit

end CFSG.RankThree.GF2n.Parrott
