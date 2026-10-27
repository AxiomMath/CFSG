module

public import CFSG.SignalizerFunctorTheorem.Glauberman.Basic
public import CFSG.LocalAnalysis.SignalizerFunctor.InvariantSylowAmbient

public section

open CFSG.Open CFSG.SignalizerFunctor.Helpers

namespace CFSG.SignalizerFunctorTheorem.Glauberman

variable {G : Type*} [Group G]

theorem primeCoreIn_le (π : Set ℕ) (U : Subgroup G) : primeCoreIn π U ≤ U :=
  Subgroup.map_subtype_le _

theorem le_normalizer_primeCoreIn [Finite G] (π : Set ℕ) (U : Subgroup G) :
    U ≤ Subgroup.normalizer (primeCoreIn π U : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  rintro u hu _ ⟨y, hy, rfl⟩
  exact ⟨⟨u, hu⟩ * y * ⟨u, hu⟩⁻¹, (prime_set_core_normal π).conj_mem y hy ⟨u, hu⟩, rfl⟩

private theorem primeSetCore_map_mulEquiv_le {H K : Type*} [Group H] [Group K] [Finite H]
    (π : Set ℕ) (e : H ≃* K) :
    (primeSetCore (GroupType := H) π).map e.toMonoidHom ≤ primeSetCore (GroupType := K) π := by
  apply prime_set_core_contains
  · exact (prime_set_core_normal π).map e.toMonoidHom e.surjective
  · rw [Subgroup.card_map_of_injective e.injective]
    exact prime_set_core_supported π

private theorem primeSetCore_map_mulEquiv {H K : Type*} [Group H] [Group K] [Finite H] [Finite K]
    (π : Set ℕ) (e : H ≃* K) :
    (primeSetCore (GroupType := H) π).map e.toMonoidHom = primeSetCore (GroupType := K) π := by
  refine le_antisymm (primeSetCore_map_mulEquiv_le π e) ?_
  have h := Subgroup.map_mono (f := e.toMonoidHom) (primeSetCore_map_mulEquiv_le π e.symm)
  rw [Subgroup.map_map] at h
  have comp : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id K := by
    ext x
    exact e.apply_symm_apply x
  rwa [comp, Subgroup.map_id] at h

theorem primeCoreIn_conj [Finite G] (π : Set ℕ) (U : Subgroup G) (g : G) :
    conjugateSubgroup g (primeCoreIn π U) = primeCoreIn π (conjugateSubgroup g U) := by
  let e : U ≃* conjugateSubgroup g U := (MulAut.conj g).subgroupMap U
  have h := primeSetCore_map_mulEquiv π e
  have hcomp : (conjugateSubgroup g U).subtype.comp e.toMonoidHom =
      (MulAut.conj g).toMonoidHom.comp U.subtype := by
    ext x
    rfl
  rw [primeCoreIn, primeCoreIn, ← h, Subgroup.map_map, hcomp, conjugateSubgroup, Subgroup.map_map]

theorem le_normalizer_primeCoreIn_of_le [Finite G] (π : Set ℕ) {B U : Subgroup G}
    (h : B ≤ Subgroup.normalizer (U : Set G)) :
    B ≤ Subgroup.normalizer (primeCoreIn π U : Set G) := by
  have : (primeSetCore (GroupType := U) π).Characteristic := prime_set_core_characteristic π
  exact characteristic_subgroup_map_normalized B U h (primeSetCore (GroupType := U) π)

theorem disjoint_primeCoreIn [Finite G] {q : ℕ} (hq : q.Prime) (U : Subgroup G)
    {P : Subgroup G} (hP : IsPGroup q P) : Disjoint (primeCoreIn ({q}ᶜ : Set ℕ) U) P := by
  obtain ⟨n, hn⟩ := isPGroup_iff_card_dvd_pow.mp hP
  apply Subgroup.disjoint_of_coprime_natCard
  have hcard : Nat.card (primeCoreIn ({q}ᶜ : Set ℕ) U) =
      Nat.card (primeSetCore (GroupType := U) ({q}ᶜ : Set ℕ)) :=
    Subgroup.card_map_of_injective U.subtype_injective
  have hcop : Nat.Coprime q (Nat.card (primeCoreIn ({q}ᶜ : Set ℕ) U)) := by
    rw [hcard, Nat.Prime.coprime_iff_not_dvd hq]
    intro hdvd
    exact prime_set_core_supported _ q hq hdvd rfl
  exact (Nat.Coprime.pow_left n hcop).symm.coprime_dvd_right hn

theorem primeCoreIn_le_centralizer [Finite G] {q : ℕ} (hq : q.Prime) {U J : Subgroup G}
    (hJU : J ≤ U) (hJ : IsPGroup q J) (hN : U ≤ Subgroup.normalizer (J : Set G)) :
    primeCoreIn ({q}ᶜ : Set ℕ) U ≤ Subgroup.centralizer (J : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hxU : x ∈ U := primeCoreIn_le _ U hx
  have hyU : y ∈ U := hJU hy
  have h1 : y * x * y⁻¹ * x⁻¹ ∈ primeCoreIn ({q}ᶜ : Set ℕ) U :=
    Subgroup.mul_mem _ (Subgroup.le_normalizer_iff.mp (le_normalizer_primeCoreIn _ U) y hyU x hx)
      (Subgroup.inv_mem _ hx)
  have h2 : y * x * y⁻¹ * x⁻¹ ∈ J := by
    have hmem : x * y⁻¹ * x⁻¹ ∈ J :=
      Subgroup.le_normalizer_iff.mp hN x hxU y⁻¹ (J.inv_mem hy)
    have : y * x * y⁻¹ * x⁻¹ = y * (x * y⁻¹ * x⁻¹) := by group
    rw [this]
    exact J.mul_mem hy hmem
  have h3 := Subgroup.disjoint_def.mp (disjoint_primeCoreIn hq U hJ) h1 h2
  calc y * x = (y * x * y⁻¹ * x⁻¹) * (x * y) := by group
    _ = x * y := by rw [h3, one_mul]

theorem le_normalizer_centralizer_of_le_normalizer {B X : Subgroup G}
    (h : B ≤ Subgroup.normalizer (X : Set G)) :
    B ≤ Subgroup.normalizer (Subgroup.centralizer (X : Set G) : Set G) := by
  rw [Subgroup.le_normalizer_iff] at h ⊢
  intro b hb c hc
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro x hx
  have hx' : b⁻¹ * x * b ∈ X := by simpa using h b⁻¹ (B.inv_mem hb) x hx
  have hxc := hc _ hx'
  calc x * (b * c * b⁻¹) = b * ((b⁻¹ * x * b) * c) * b⁻¹ := by group
    _ = b * (c * (b⁻¹ * x * b)) * b⁻¹ := by rw [hxc]
    _ = (b * c * b⁻¹) * x := by group

theorem le_normalizer_conj_of_mem_centralizer {B X : Subgroup G} {c : G}
    (hc : c ∈ Subgroup.centralizer (B : Set G)) (h : B ≤ Subgroup.normalizer (X : Set G)) :
    B ≤ Subgroup.normalizer (conjugateSubgroup c X : Set G) := by
  rw [Subgroup.le_normalizer_iff] at h ⊢
  rw [Subgroup.mem_centralizer_iff] at hc
  rintro b hb _ ⟨x, hx, rfl⟩
  refine ⟨b * x * b⁻¹, h b hb x hx, ?_⟩
  have hcb : b * c = c * b := hc b hb
  change c * (b * x * b⁻¹) * c⁻¹ = b * (c * x * c⁻¹) * b⁻¹
  calc c * (b * x * b⁻¹) * c⁻¹ = (c * b) * x * (c * b)⁻¹ := by group
    _ = (b * c) * x * (b * c)⁻¹ := by rw [hcb]
    _ = b * (c * x * c⁻¹) * b⁻¹ := by group

end CFSG.SignalizerFunctorTheorem.Glauberman
