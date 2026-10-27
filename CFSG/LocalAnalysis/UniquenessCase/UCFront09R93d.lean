module

public import Mathlib.GroupTheory.PGroup
import CFSG.LocalAnalysis.UniquenessCase.UC6Mod

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open Subgroup

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem centralizer_map_conj_le_of_mem {Z M : Subgroup G} (hZ : centralizer (Z : Set G) ≤ M)
    {b : G} (hb : b ∈ M) :
    centralizer ((Z.map (MulAut.conj b).toMonoidHom : Subgroup G) : Set G) ≤ M := by
  intro n hn
  have hkey : b⁻¹ * n * b ∈ centralizer (Z : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hmem : b * z * b⁻¹ ∈ (Z.map (MulAut.conj b).toMonoidHom : Subgroup G) :=
      Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
    have hcomm : (b * z * b⁻¹) * n = n * (b * z * b⁻¹) :=
      (Subgroup.mem_centralizer_iff.mp hn) _ hmem
    calc z * (b⁻¹ * n * b) = b⁻¹ * ((b * z * b⁻¹) * n) * b := by group
      _ = b⁻¹ * (n * (b * z * b⁻¹)) * b := by rw [hcomm]
      _ = (b⁻¹ * n * b) * z := by group
  have hn_eq : n = b * (b⁻¹ * n * b) * b⁻¹ := by group
  rw [hn_eq]
  exact M.mul_mem (M.mul_mem hb (hZ hkey)) (M.inv_mem hb)

theorem exists_minimal_invariant_not_le {K O M : Subgroup G}
    (hKO : K ≤ normalizer (O : Set G)) (hOM : ¬ O ≤ M) :
    ∃ U : Subgroup G, U ≤ O ∧ K ≤ normalizer (U : Set G) ∧ ¬ U ≤ M ∧
      ∀ V : Subgroup G, V ≤ O → K ≤ normalizer (V : Set G) → ¬ V ≤ M →
        Nat.card U ≤ Nat.card V := by
  classical
  have hex : ∃ n : ℕ, ∃ U : Subgroup G, U ≤ O ∧
      K ≤ normalizer (U : Set G) ∧ ¬ U ≤ M ∧ n = Nat.card U :=
    ⟨Nat.card O, O, le_rfl, hKO, hOM, rfl⟩
  obtain ⟨U, hUle, hUK, hUM, hUcard⟩ := Nat.find_spec hex
  refine ⟨U, hUle, hUK, hUM, fun V hVle hVK hVM => ?_⟩
  rw [← hUcard]
  exact Nat.find_min' hex ⟨V, hVle, hVK, hVM, rfl⟩

theorem exists_maximal_invariant_normal {K U : Subgroup G} (hUbot : U ≠ ⊥) :
    ∃ W : Subgroup G, W ≤ U ∧ U ≤ normalizer (W : Set G) ∧ K ≤ normalizer (W : Set G) ∧
      W ≠ U ∧ ∀ X : Subgroup G, W ≤ X → X ≤ U → U ≤ normalizer (X : Set G) →
        K ≤ normalizer (X : Set G) → X ≠ U → X = W := by
  classical
  have hbotU : U ≤ normalizer ((⊥ : Subgroup G) : Set G) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hbotK : K ≤ normalizer ((⊥ : Subgroup G) : Set G) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hex : ∃ n : ℕ, ∃ W : Subgroup G, W ≤ U ∧ U ≤ normalizer (W : Set G) ∧
      K ≤ normalizer (W : Set G) ∧ W ≠ U ∧ n = Nat.card U - Nat.card W :=
    ⟨Nat.card U - Nat.card ↥(⊥ : Subgroup G), ⊥, bot_le, hbotU, hbotK,
      fun h => hUbot h.symm, rfl⟩
  obtain ⟨W, hWle, hWU, hWK, hWne, hWcard⟩ := Nat.find_spec hex
  refine ⟨W, hWle, hWU, hWK, hWne, fun X hWX hXU hXU' hXK hXne => ?_⟩
  have h : Nat.find hex ≤ Nat.card U - Nat.card X :=
    Nat.find_min' hex ⟨X, hXU, hXU', hXK, hXne, rfl⟩
  have hWU' : Nat.card W ≤ Nat.card U :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hWle)
  have hXU'' : Nat.card X ≤ Nat.card U :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hXU)
  have hcard : Nat.card X ≤ Nat.card W := by omega
  exact (Subgroup.eq_of_le_of_card_ge hWX hcard).symm

theorem eq_zpowers_of_card_eq_three {Z : Subgroup G} (hZ3 : Nat.card Z = 3) {z : G}
    (hzZ : z ∈ Z) (hz1 : z ≠ 1) : Z = zpowers z ∧ orderOf z = 3 := by
  have hdvd := Subgroup.orderOf_dvd_natCard Z hzZ
  rw [hZ3] at hdvd
  have hzord : orderOf z = 3 := ((Nat.dvd_prime Nat.prime_three).mp hdvd).resolve_left
    fun h => hz1 (orderOf_eq_one_iff.mp h)
  refine ⟨(Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzZ) ?_).symm, hzord⟩
  rw [Nat.card_zpowers, hzord, hZ3]

theorem forall_fixed_of_fixed_conj {K Z U W : Subgroup G} (hZK : Z ≤ K) (hZ3 : Nat.card Z = 3)
    (hWK : K ≤ normalizer (W : Set G)) (hWU : U ≤ normalizer (W : Set G))
    {b z u : G} (hb : b ∈ K) (hzZ : z ∈ Z) (hz1 : z ≠ 1) (hu : u ∈ U)
    (hq : u⁻¹ * (b * z * b⁻¹) * u * (b * z * b⁻¹)⁻¹ ∈ W) :
    ∀ x ∈ Z, u⁻¹ * (b * x * b⁻¹) * u * (b * x * b⁻¹)⁻¹ ∈ W := by
  have hbN : b ∈ normalizer (W : Set G) := hWK hb
  have hbNinv : b⁻¹ ∈ normalizer (W : Set G) := Subgroup.inv_mem _ hbN
  let S : Subgroup G :=
    { carrier := {y : G | y ∈ normalizer (W : Set G) ∧
        u⁻¹ * (b * y * b⁻¹) * u * (b * y * b⁻¹)⁻¹ ∈ W},
      one_mem' := ⟨Subgroup.one_mem _, by simpa using W.one_mem⟩,
      mul_mem' := by
        rintro y₁ y₂ ⟨h1N, h1⟩ ⟨h2N, h2⟩
        have hA1N : b * y₁ * b⁻¹ ∈ normalizer (W : Set G) :=
          Subgroup.mul_mem _ (Subgroup.mul_mem _ hbN h1N) hbNinv
        refine ⟨Subgroup.mul_mem _ h1N h2N, ?_⟩
        have heq : u⁻¹ * (b * (y₁ * y₂) * b⁻¹) * u * (b * (y₁ * y₂) * b⁻¹)⁻¹ =
            (u⁻¹ * (b * y₁ * b⁻¹) * u * (b * y₁ * b⁻¹)⁻¹) *
              ((b * y₁ * b⁻¹) * (u⁻¹ * (b * y₂ * b⁻¹) * u * (b * y₂ * b⁻¹)⁻¹) *
                (b * y₁ * b⁻¹)⁻¹) := by group
        rw [heq]
        exact W.mul_mem h1 ((Subgroup.mem_normalizer_iff.mp hA1N _).mp h2),
      inv_mem' := by
        rintro y ⟨hyN, hy⟩
        have hAN : b * y * b⁻¹ ∈ normalizer (W : Set G) :=
          Subgroup.mul_mem _ (Subgroup.mul_mem _ hbN hyN) hbNinv
        refine ⟨Subgroup.inv_mem _ hyN, ?_⟩
        have heq : u⁻¹ * (b * y⁻¹ * b⁻¹) * u * (b * y⁻¹ * b⁻¹)⁻¹ =
            (b * y * b⁻¹)⁻¹ * (u⁻¹ * (b * y * b⁻¹) * u * (b * y * b⁻¹)⁻¹)⁻¹ *
              (b * y * b⁻¹) := by group
        rw [heq]
        simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hAN) _).mp
          (W.inv_mem hy) }
  have hZgen := (eq_zpowers_of_card_eq_three hZ3 hzZ hz1).1
  have hle : zpowers z ≤ S := Subgroup.zpowers_le.mpr ⟨hWK (hZK hzZ), hq⟩
  intro x hx
  exact (hle (hZgen ▸ hx)).2

theorem mem_inf_sup_of_fixed_conj {K Z M U W : Subgroup G} (hZ3 : Nat.card Z = 3)
    (hZK : Z ≤ K) (hKM : K ≤ M) (hCZ : centralizer (Z : Set G) ≤ M)
    (hFW : ¬ 3 ∣ Nat.card W) (hWle : W ≤ U) (hWK : K ≤ normalizer (W : Set G))
    {b : G} (hb : b ∈ K) {u : G} (hu : u ∈ U)
    (hq : ∀ x ∈ Z, u⁻¹ * (b * x * b⁻¹) * u * (b * x * b⁻¹)⁻¹ ∈ W) :
    u ∈ (U ⊓ M) ⊔ W := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set X : Subgroup G := Z.map (MulAut.conj b).toMonoidHom with hX
  have hXcard : Nat.card X = 3 := by
    rw [hX, Subgroup.card_map_of_injective (f := (MulAut.conj b).toMonoidHom)
      (fun x y hxy => (MulAut.conj b).injective hxy), hZ3]
  have hXpg : IsPGroup 3 ↥X := IsPGroup.of_card (n := 1) (by rw [hXcard, pow_one])
  have hXNW : ∀ x ∈ X, ∀ f ∈ W, x * f * x⁻¹ ∈ W := by
    intro x hx f hf
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hx
    have hxN : b * z * b⁻¹ ∈ normalizer (W : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (hWK hb) (hWK (hZK hz)))
        (Subgroup.inv_mem _ (hWK hb))
    exact (Subgroup.mem_normalizer_iff.mp hxN f).mp hf
  have hq' : ∀ x ∈ X, u⁻¹ * (x * u * x⁻¹) ∈ W := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hx
    change u⁻¹ * ((b * z * b⁻¹) * u * (b * z * b⁻¹)⁻¹) ∈ W
    simpa only [mul_assoc] using hq z hz
  obtain ⟨n, hnW, hnfix⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC6.exists_fixed_in_coset_uc6 X W hXpg hFW hXNW u hq'
  have hnU : n ∈ U := by
    rw [show n = u * (u⁻¹ * n) by group]
    exact U.mul_mem hu (hWle hnW)
  have hnC : n ∈ centralizer (X : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    calc x * n = (x * n * x⁻¹) * x := by group
      _ = n * x := by rw [hnfix x hx]
  have hnM : n ∈ M := centralizer_map_conj_le_of_mem hCZ (hKM hb) hnC
  rw [show u = n * (u⁻¹ * n)⁻¹ by group]
  exact Subgroup.mul_mem _ ((le_sup_left : U ⊓ M ≤ (U ⊓ M) ⊔ W) (Subgroup.mem_inf.mpr ⟨hnU, hnM⟩))
    ((le_sup_right : W ≤ (U ⊓ M) ⊔ W) (W.inv_mem hnW))

omit [Finite G] in
theorem inv_mul_conj_mem_of_conj_mul_mem {W : Subgroup G} {u x : G}
    (hu : u ∈ normalizer (W : Set G)) (h : x * u * x⁻¹ * u⁻¹ ∈ W) :
    u⁻¹ * (x * u * x⁻¹) ∈ W := by
  rw [show u⁻¹ * (x * u * x⁻¹) = u⁻¹ * (x * u * x⁻¹ * u⁻¹) * u by group]
  simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hu) _).mp h

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09
