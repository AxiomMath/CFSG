module

public import CFSG.RankThree.PartOne.KF.U4Perm
public import CFSG.RankThree.PartOne.KF.R12Unitary
public import CFSG.RankThree.PartOne.S12.Sec12Restrict
public import CFSG.RankThree.PartOne.S12.Sec12A

public section

namespace CFSG.RankThree.PartOne.U5LIFT

open CFSG CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.Sec12Three CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

structure U5Ctx {G : Type} [Group G] [Finite G] (A : Subgroup G) (c : G) (L E : Subgroup G)
    (f : ℕ) (K : Type) [Field K] where
  h : Sec12Hyp G 5 A c L E
  hE4 : Nat.card E = 5 ^ 4
  R : Restr c L E (E ⊓ L)
  hU : UnitaryFieldData 2 f K
  hf2 : 2 ≤ f
  hpq : 5 ∣ 2 ^ f + 1
  φ : unitarySU 2 f K 5 →* G
  φ_mem : ∀ g, φ g ∈ L
  φ_surj : ∀ l ∈ L, ∃ g, φ g = l
  φ_ker : ∀ g, φ g = 1 → g ∈ scalarsU K f
  hφ : ∀ g, φ g ∈ E ↔ (g : GL (Fin 5) K) ∈ torusSU 5 5 K

namespace U5Ctx

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L E : Subgroup G} {f : ℕ}
  {K : Type} [Field K] (C : U5Ctx A c L E f K)

theorem phi_mem_E_iff (g : unitarySU 2 f K 5) :
    C.φ g ∈ E ↔ (g : GL (Fin 5) K) ∈ torusSU 5 5 K := C.hφ g

include C in
theorem torus_le (x : GL (Fin 5) K) (hx : x ∈ torusSU 5 5 K) : x ∈ unitarySU 2 f K 5 :=
  torusSU_le_unitarySU C.hU C.hpq hx

theorem exists_phi_eq {l : G} (hl : l ∈ L) : ∃ g : unitarySU 2 f K 5, C.φ g = l := C.φ_surj l hl

theorem exists_decomp {e : G} (he : e ∈ E) :
    ∃ x : unitarySU 2 f K 5, (x : GL (Fin 5) K) ∈ torusSU 5 5 K ∧ ∃ i : ℤ, e = C.φ x * c ^ i := by
  obtain ⟨f', hf', i, hfi⟩ := C.R.exists_mul_zpow he
  obtain ⟨hf'E, hf'L⟩ := Subgroup.mem_inf.mp hf'
  obtain ⟨x, hx⟩ := C.exists_phi_eq hf'L
  refine ⟨x, (C.phi_mem_E_iff x).mp (hx ▸ hf'E), i, ?_⟩
  rw [hx]
  exact hfi

theorem phi_mul_zpow_mem {x : unitarySU 2 f K 5} (hx : (x : GL (Fin 5) K) ∈ torusSU 5 5 K)
    (i : ℤ) : C.φ x * c ^ i ∈ E :=
  E.mul_mem ((C.phi_mem_E_iff x).mpr hx) (E.zpow_mem C.R.c_mem i)

theorem c_comm_phi (g : unitarySU 2 f K 5) : c * C.φ g = C.φ g * c :=
  C.R.comm _ (C.φ_mem g)

include C in
theorem exists_unit_root : ∃ ζ : Kˣ, IsPrimitiveRoot ζ 5 := by
  obtain ⟨z, hz⟩ := exists_isPrimitiveRoot C.hU C.h.prime C.hpq
  have hz0 : z ≠ 0 := hz.ne_zero C.h.prime.ne_zero
  exact ⟨Units.mk0 z hz0, IsPrimitiveRoot.coe_units_iff.mp (by simpa using hz)⟩

include C in
theorem hdist : ∀ i j : Fin 5, i ≠ j → ∃ x ∈ torusSU 5 5 K, ent x i i ≠ ent x j j := by
  obtain ⟨ζ, hζ⟩ := C.exists_unit_root
  intro i j hij
  exact torus_char_distinct hζ.pow_eq_one
    (hζ.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)) i j hij

theorem normalizes_torus {w : G} (hwE : w ∈ Subgroup.normalizer (E : Set G))
    {g : unitarySU 2 f K 5} (hg : C.φ g = w) :
    (∀ x ∈ torusSU 5 5 K, (g : GL (Fin 5) K) * x * (g : GL (Fin 5) K)⁻¹ ∈ torusSU 5 5 K) ∧
      ∀ x ∈ torusSU 5 5 K, (g : GL (Fin 5) K)⁻¹ * x * (g : GL (Fin 5) K) ∈ torusSU 5 5 K := by
  have key : ∀ (g' : unitarySU 2 f K 5), C.φ g' ∈ Subgroup.normalizer (E : Set G) →
      ∀ x ∈ torusSU 5 5 K,
        (g' : GL (Fin 5) K) * x * (g' : GL (Fin 5) K)⁻¹ ∈ torusSU 5 5 K := by
    intro g' hg' x hx
    have hxΓ := C.torus_le x hx
    have h1 : C.φ g' * C.φ ⟨x, hxΓ⟩ * (C.φ g')⁻¹ ∈ E :=
      ((Subgroup.mem_normalizer_iff.mp hg') _).1 ((C.phi_mem_E_iff ⟨x, hxΓ⟩).mpr hx)
    have h2 : C.φ g' * C.φ ⟨x, hxΓ⟩ * (C.φ g')⁻¹ = C.φ (g' * ⟨x, hxΓ⟩ * g'⁻¹) := by
      simp [map_mul, map_inv]
    rw [h2] at h1
    exact (C.phi_mem_E_iff _).mp h1
  refine ⟨key g (hg ▸ hwE), ?_⟩
  intro x hx
  have := key g⁻¹ (by
    rw [map_inv, hg]
    exact (Subgroup.inv_mem _ hwE)) x hx
  simpa using this

theorem conj_phi_mul_zpow (g x : unitarySU 2 f K 5) (i : ℤ) :
    C.φ g * (C.φ x * c ^ i) * (C.φ g)⁻¹ = C.φ (g * x * g⁻¹) * c ^ i := by
  have h1 : C.φ g * c ^ i * (C.φ g)⁻¹ = c ^ i := C.R.conj_zpow (C.φ_mem g) i
  calc C.φ g * (C.φ x * c ^ i) * (C.φ g)⁻¹
      = (C.φ g * C.φ x * (C.φ g)⁻¹) * (C.φ g * c ^ i * (C.φ g)⁻¹) := by group
    _ = C.φ (g * x * g⁻¹) * c ^ i := by rw [h1]; simp [map_mul, map_inv]

include C in
theorem exists_perm {w : G} (hwL : w ∈ L) (hwE : w ∈ Subgroup.normalizer (E : Set G)) :
    ∃ (g : unitarySU 2 f K 5) (τ : Equiv.Perm (Fin 5)), C.φ g = w ∧
      NormPerm 5 (g : GL (Fin 5) K) τ := by
  obtain ⟨g, hg⟩ := C.exists_phi_eq hwL
  obtain ⟨h1, h2⟩ := C.normalizes_torus hwE hg
  obtain ⟨τ, hτ⟩ := exists_normPerm C.hdist h1 h2
  exact ⟨g, τ, hg, hτ⟩

end U5Ctx

end CFSG.RankThree.PartOne.U5LIFT
