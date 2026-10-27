module

public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieL3OLinesDiag
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieL3OLinesRoots

public section

namespace CFSG.Quasithin.H13.NQCore.L3Odd

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups

section Generic

variable {G : Type*} [Group G]

theorem eq_of_card_eq_prime [Finite G] {p : ℕ} [hp : Fact p.Prime] {U V : Subgroup G}
    (hU : Nat.card U = p) (hV : Nat.card V = p) {x : G} (hxU : x ∈ U) (hxV : x ∈ V)
    (hx : x ≠ 1) : U = V := by
  have hd : Nat.card (U ⊓ V : Subgroup G) ∣ p := hU ▸ Subgroup.card_dvd_of_le inf_le_left
  have hne : Nat.card (U ⊓ V : Subgroup G) ≠ 1 := by
    intro h
    have hb : U ⊓ V = ⊥ := Subgroup.card_eq_one.1 h
    have hxm : x ∈ U ⊓ V := ⟨hxU, hxV⟩
    rw [hb, Subgroup.mem_bot] at hxm
    exact hx hxm
  have hc : Nat.card (U ⊓ V : Subgroup G) = p := ((Nat.dvd_prime hp.out).1 hd).resolve_left hne
  have h1 : U ⊓ V = U := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hc, hU])
  have h2 : U ⊓ V = V := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hc, hV])
  rw [← h1, h2]

theorem centralizer_map_equiv (φ : G ≃* G) (H : Subgroup G) :
    Subgroup.centralizer ((H.map φ.toMonoidHom : Subgroup G) : Set G) =
      (Subgroup.centralizer (H : Set G)).map φ.toMonoidHom := by
  ext g
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h k hk
    apply φ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact h _ (Subgroup.mem_map.2 ⟨k, hk, rfl⟩)
  · intro h k hk
    obtain ⟨k', hk', rfl⟩ := Subgroup.mem_map.1 hk
    have := congrArg φ (h k' hk')
    simpa using this

end Generic

section Torus

variable {K : Type} [Field K] {p : ℕ}

theorem diagHom_pow_eq_one {a b : Kˣ} (ha : a ^ p = 1) (hb : b ^ p = 1) :
    (diagHom (a, b) : SL(3, K)) ^ p = 1 := by
  rw [← map_pow, Prod.pow_def, ha, hb]
  exact map_one diagHom

theorem centralizer_le_of_regular [hp : Fact p.Prime] (hp3 : p ≠ 3) {a b : Kˣ} (ha : a ^ p = 1)
    (hb : b ^ p = 1) (hreg : IsRegular (a, b)) {g : projectiveSL 3 K}
    (hg : proj 3 K (diagHom (a, b)) * g = g * proj 3 K (diagHom (a, b))) :
    g ∈ Subgroup.centralizer (torusP K p : Set (projectiveSL 3 K)) := by
  obtain ⟨g', rfl⟩ := proj_surjective 3 K g
  have h1 : g' * diagHom (a, b) = diagHom (a, b) * g' :=
    (proj_commute_iff hp3 (diagHom_pow_eq_one ha hb)).1 hg.symm
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨a', b', -, -, rfl⟩ := mem_torusP.1 hy
  rw [← map_mul, ← map_mul, commute_diagHom_of_commute_regular hreg h1 (a', b')]

theorem proj_trv_commute_iff [hp : Fact p.Prime] (hp3 : p ≠ 3) {a b : Kˣ} (ha : a ^ p = 1)
    (hb : b ^ p = 1) (i j : Fin 3) (hij : i ≠ j) :
    proj 3 K (trv i j hij) * proj 3 K (diagHom (a, b)) =
        proj 3 K (diagHom (a, b)) * proj 3 K (trv i j hij) ↔ dv (a, b) i = dv (a, b) j := by
  rw [proj_commute_iff hp3 (diagHom_pow_eq_one ha hb), trv_commute_iff]

theorem isRegular_inv [hp : Fact p.Prime] (hp2 : p ≠ 2) {ζ : Kˣ} (hζ : ζ ^ p = 1) (hζ1 : ζ ≠ 1) :
    IsRegular (ζ, ζ⁻¹) := by
  have h2 : ζ ≠ ζ⁻¹ := by
    intro h
    apply hζ1
    refine eq_one_of_pow_eq_one_of_prime Nat.prime_two hp2 hζ ?_
    rw [pow_two]
    nth_rewrite 2 [h]
    exact mul_inv_cancel ζ
  rw [isRegular_iff]
  refine ⟨h2, ?_, ?_⟩
  · simpa using hζ1
  · simpa using hζ1

theorem proj_trv_not_mem_centralizer [Finite K] [hp : Fact p.Prime] (hp5 : 5 ≤ p)
    (hpq : p ∣ Nat.card K - 1) (i j : Fin 3) (hij : i ≠ j) :
    proj 3 K (trv i j hij) ∉ Subgroup.centralizer (torusP K p : Set (projectiveSL 3 K)) := by
  obtain ⟨ζ, hζ, hζ1⟩ := exists_ne_one hpq
  have hζ' : ζ⁻¹ ^ p = 1 := by rw [inv_pow, hζ, inv_one]
  intro h
  rw [Subgroup.mem_centralizer_iff] at h
  have hmem : proj 3 K (diagHom (ζ, ζ⁻¹)) ∈ torusP K p := mem_torusP.2 ⟨ζ, ζ⁻¹, hζ, hζ', rfl⟩
  have hc := (proj_trv_commute_iff (by omega) hζ hζ' i j hij).1 (h _ hmem).symm
  exact isRegular_inv (by omega) hζ hζ1 i j hij hc

end Torus

end CFSG.Quasithin.H13.NQCore.L3Odd
