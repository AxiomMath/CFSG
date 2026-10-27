module

public import CFSG.GH74.GLS.IVK.Proofs2.Perm4Facts
public import Mathlib.GroupTheory.SpecificGroups.KleinFour
import CFSG.Dihedral.PerfectDihedralFourgroupAction

public section

namespace CFSG.Quasithin.E22L2

open CFSG.GH74.GLS.IVK.Proofs2

theorem e22pl2sevb_perm4_prod_conj (σ : Equiv.Perm (Fin 4)) (hσ : σ ∉ kleinFour) :
    ∃ c : Equiv.Perm (Fin 4), (σ * (c * σ * c⁻¹)) ^ 3 = 1 ∧ σ * (c * σ * c⁻¹) ≠ 1 := by
  have h : ∀ σ : Equiv.Perm (Fin 4),
      ¬ (σ = 1 ∨ σ = kleinA ∨ σ = kleinB ∨ σ = kleinB * kleinA) →
      ∃ c : Equiv.Perm (Fin 4), (σ * (c * σ * c⁻¹)) ^ 3 = 1 ∧ σ * (c * σ * c⁻¹) ≠ 1 := by
    decide +kernel
  exact h σ fun hh => hσ (mem_kleinFour_iff.mpr hh)

theorem e22pl2sevb_kleinFour_sq {σ : Equiv.Perm (Fin 4)} (hσ : σ ∈ kleinFour) : σ * σ = 1 := by
  have h : ∀ σ : Equiv.Perm (Fin 4),
      (σ = 1 ∨ σ = kleinA ∨ σ = kleinB ∨ σ = kleinB * kleinA) → σ * σ = 1 := by
    decide +kernel
  exact h σ (mem_kleinFour_iff.mp hσ)

theorem e22pl2sevb_perm4_normal_eq (N : Subgroup (Equiv.Perm (Fin 4))) (hn : N.Normal)
    (hN : Nat.card N = 4) : N = kleinFour := by
  have hle : N ≤ kleinFour := by
    intro σ hσ
    by_contra hσ'
    obtain ⟨c, h3, h1⟩ := e22pl2sevb_perm4_prod_conj σ hσ'
    have hy : σ * (c * σ * c⁻¹) ∈ N := N.mul_mem hσ (hn.conj_mem σ hσ c)
    have h4 : (σ * (c * σ * c⁻¹)) ^ 4 = 1 := by
      have h := pow_card_eq_one' (G := N) (x := ⟨_, hy⟩)
      rw [hN] at h
      exact congrArg Subtype.val h
    apply h1
    calc σ * (c * σ * c⁻¹) = (σ * (c * σ * c⁻¹)) ^ 4 * ((σ * (c * σ * c⁻¹)) ^ 3)⁻¹ := by group
      _ = 1 := by rw [h4, h3]; simp
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_kleinFour, hN])

theorem e22pl2sevb_perm4_aut_mem (α : MulAut (Equiv.Perm (Fin 4))) {σ : Equiv.Perm (Fin 4)}
    (hσ : σ ∈ kleinFour) : α σ ∈ kleinFour := by
  have hnorm : kleinFour.Normal := ⟨fun n hn g => conj_mem_kleinFour g hn⟩
  have hW : (kleinFour.map α.toMonoidHom).Normal := hnorm.map α.toMonoidHom α.surjective
  have hc : Nat.card (kleinFour.map α.toMonoidHom) = 4 := by
    rw [Subgroup.card_map_of_injective α.injective, card_kleinFour]
  have := e22pl2sevb_perm4_normal_eq _ hW hc
  rw [← this]
  exact Subgroup.mem_map_of_mem α.toMonoidHom hσ

theorem e22pl2sevb_isKleinFour_of_card {G : Type*} [Group G] {V : Subgroup G}
    (hc : Nat.card V = 4) (hsq : ∀ v ∈ V, v * v = 1) : IsKleinFour ↥V := by
  refine ⟨hc, ?_⟩
  have h2 : Monoid.exponent ↥V ∣ 2 := by
    apply Monoid.exponent_dvd_of_forall_pow_eq_one
    intro x
    rw [pow_two]
    exact Subtype.ext (hsq x x.2)
  rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
  · exfalso
    have : Finite ↥V := Nat.finite_of_card_ne_zero (by omega)
    rw [Monoid.exp_eq_one_iff, ← Finite.card_le_one_iff_subsingleton] at h
    omega
  · exact h

theorem e22pl2sevb_exists_kleinFour_normalizer {G : Type*} [Group G] (M : Subgroup G)
    (e : ↥M ≃* Equiv.Perm (Fin 4)) :
    ∃ V : Subgroup G, IsKleinFour ↥V ∧
      Subgroup.normalizer (M : Set G) ≤ Subgroup.normalizer (V : Set G) := by
  classical
  set V : Subgroup G := (kleinFour.map e.symm.toMonoidHom).map M.subtype with hV
  have hVmem : ∀ x : G, x ∈ V ↔ ∃ m : ↥M, e m ∈ kleinFour ∧ (m : G) = x := by
    intro x
    rw [hV, Subgroup.mem_map]
    constructor
    · rintro ⟨m, hm, rfl⟩
      obtain ⟨σ, hσ, rfl⟩ := Subgroup.mem_map.mp hm
      exact ⟨e.symm σ, by simpa using hσ, rfl⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨m, Subgroup.mem_map.mpr ⟨e m, hm, by simp⟩, rfl⟩
  have hcard : Nat.card V = 4 := by
    rw [hV, Subgroup.card_map_of_injective M.subtype_injective,
      Subgroup.card_map_of_injective e.symm.injective, card_kleinFour]
  have hsq : ∀ v ∈ V, v * v = 1 := by
    intro v hv
    obtain ⟨m, hm, rfl⟩ := (hVmem v).mp hv
    have h1 : e (m * m) = 1 := by rw [map_mul]; exact e22pl2sevb_kleinFour_sq hm
    have h2 : m * m = 1 := e.injective (by rw [h1, map_one])
    exact congrArg Subtype.val h2
  have key : ∀ b ∈ Subgroup.normalizer (M : Set G), ∀ v ∈ V, b * v * b⁻¹ ∈ V := by
    intro b hb v hv
    obtain ⟨m, hm, rfl⟩ := (hVmem v).mp hv
    let φ : MulAut ↥M := M.normalizerMonoidHom ⟨b, hb⟩
    let α : MulAut (Equiv.Perm (Fin 4)) := (e.symm.trans φ).trans e
    have hα : α (e m) ∈ kleinFour := e22pl2sevb_perm4_aut_mem α hm
    refine (hVmem _).mpr ⟨φ m, ?_, ?_⟩
    · simpa [α] using hα
    · exact M.normalizerMonoidHom_apply_apply_coe ⟨b, hb⟩ m
  refine ⟨V, e22pl2sevb_isKleinFour_of_card hcard hsq, fun b hb => ?_⟩
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => key b hb h hh, fun hh => ?_⟩
  have h1 := key b⁻¹ (Subgroup.inv_mem _ hb) _ hh
  have h2 : b⁻¹ * (b * h * b⁻¹) * b⁻¹⁻¹ = h := by group
  rwa [h2] at h1

theorem e22pl2sevb_card_normalizer_dvd {G : Type*} [Group G] {V : Subgroup G}
    (hV : IsKleinFour ↥V) (hcent : Subgroup.centralizer (V : Set G) = V) :
    Nat.card (Subgroup.normalizer (V : Set G)) ∣ 24 := by
  have := hV
  have h1 := Subgroup.card_ker_mul_card_range V.normalizerMonoidHom
  have h2 : Nat.card V.normalizerMonoidHom.ker = 4 := by
    rw [Subgroup.normalizerMonoidHom_ker, hcent,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.le_normalizer (H := V))).toEquiv]
    exact IsKleinFour.card_four
  have h3 : Nat.card V.normalizerMonoidHom.range ∣ 6 := by
    rw [← CFSG.GorensteinWalter.kleinFourAut_card ↥V]
    exact Subgroup.card_subgroup_dvd_card _
  rw [h2] at h1
  rw [← h1]
  exact (Nat.mul_dvd_mul_left 4 h3 : 4 * _ ∣ 4 * 6)

theorem e22pl2sevb_false_of_perm_four {G : Type*} [Group G] {M D : Subgroup G}
    (e : ↥M ≃* Equiv.Perm (Fin 4)) (hDM : D ≤ Subgroup.normalizer (M : Set G))
    (hcent : ∀ V : Subgroup G, IsKleinFour ↥V → Subgroup.centralizer (V : Set G) = V)
    (hD : Nat.card D = 16) : False := by
  obtain ⟨V, hV, hVN⟩ := e22pl2sevb_exists_kleinFour_normalizer M e
  have h1 := e22pl2sevb_card_normalizer_dvd hV (hcent V hV)
  have h2 : Nat.card D ∣ Nat.card (Subgroup.normalizer (V : Set G)) :=
    Subgroup.card_dvd_of_le (hDM.trans hVN)
  rw [hD] at h2
  have h3 := dvd_trans h2 h1
  omega

end CFSG.Quasithin.E22L2
