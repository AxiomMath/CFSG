module

public import CFSG.RankThree.PartOne.KF.UnitaryModel
public import CFSG.RankThree.PartOne.S12.Sec12Restrict

public section

namespace CFSG.RankThree.PartOne.KFU

open CFSG CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.Sec12Three
  CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

structure U4Ctx {G : Type} [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G)
    (L E : Subgroup G) (f : ℕ) (K : Type) [Field K] where
  h : Sec12Hyp G p A c L E
  hE4 : Nat.card E = p ^ 4
  R : Restr c L E (E ⊓ L)
  hcL : c ∉ L
  hU : UnitaryFieldData 2 f K
  hf2 : 2 ≤ f
  hpq : p ∣ 2 ^ f + 1
  ψ : unitarySU 2 f K 4 ≃* L
  hψ : ∀ g : unitarySU 2 f K 4, (ψ g : G) ∈ E ↔ (g : GL (Fin 4) K) ∈ torusSU p 4 K

namespace U4Ctx

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
  {f : ℕ} {K : Type} [Field K] (C : U4Ctx p A c L E f K)

@[expose] def phi : unitarySU 2 f K 4 →* G := L.subtype.comp C.ψ.toMonoidHom

theorem coe_phi (g : unitarySU 2 f K 4) : (C.phi g : G) = ((C.ψ g : L) : G) := rfl

theorem phi_injective : Function.Injective C.phi := fun _ _ hxy =>
  C.ψ.injective (Subtype.ext hxy)

theorem phi_mem_L (g : unitarySU 2 f K 4) : C.phi g ∈ L := (C.ψ g).2

theorem phi_mem_E_iff (g : unitarySU 2 f K 4) :
    C.phi g ∈ E ↔ (g : GL (Fin 4) K) ∈ torusSU p 4 K := C.hψ g

include C in
theorem torus_le (x : GL (Fin 4) K) (hx : x ∈ torusSU p 4 K) : x ∈ unitarySU 2 f K 4 :=
  torusSU_le_unitarySU C.hU C.hpq hx

theorem exists_phi_eq {l : G} (hl : l ∈ L) : ∃ g : unitarySU 2 f K 4, C.phi g = l :=
  ⟨C.ψ.symm ⟨l, hl⟩, by rw [coe_phi, MulEquiv.apply_symm_apply]⟩

theorem exists_decomp {e : G} (he : e ∈ E) :
    ∃ x : unitarySU 2 f K 4, (x : GL (Fin 4) K) ∈ torusSU p 4 K ∧ ∃ i : ℤ,
      e = C.phi x * c ^ i := by
  obtain ⟨f', hf', i, hfi⟩ := C.R.exists_mul_zpow he
  obtain ⟨hf'E, hf'L⟩ := Subgroup.mem_inf.mp hf'
  obtain ⟨x, hx⟩ := C.exists_phi_eq hf'L
  refine ⟨x, (C.phi_mem_E_iff x).mp (hx ▸ hf'E), i, ?_⟩
  rw [hx]
  exact hfi

theorem phi_mul_zpow_mem {x : unitarySU 2 f K 4} (hx : (x : GL (Fin 4) K) ∈ torusSU p 4 K)
    (i : ℤ) : C.phi x * c ^ i ∈ E :=
  E.mul_mem ((C.phi_mem_E_iff x).mpr hx) (E.zpow_mem C.R.c_mem i)

theorem c_comm_phi (g : unitarySU 2 f K 4) : c * C.phi g = C.phi g * c :=
  C.R.comm _ (C.phi_mem_L g)

theorem normalizes_torus {w : G} (hwE : w ∈ Subgroup.normalizer (E : Set G))
    {g : unitarySU 2 f K 4} (hg : C.phi g = w) :
    (∀ x ∈ torusSU p 4 K, (g : GL (Fin 4) K) * x * (g : GL (Fin 4) K)⁻¹ ∈ torusSU p 4 K) ∧
      ∀ x ∈ torusSU p 4 K, (g : GL (Fin 4) K)⁻¹ * x * (g : GL (Fin 4) K) ∈ torusSU p 4 K := by
  have key : ∀ (g' : unitarySU 2 f K 4), C.phi g' ∈ Subgroup.normalizer (E : Set G) →
      ∀ x ∈ torusSU p 4 K,
        (g' : GL (Fin 4) K) * x * (g' : GL (Fin 4) K)⁻¹ ∈ torusSU p 4 K := by
    intro g' hg' x hx
    have hxΓ := C.torus_le x hx
    have h1 : C.phi g' * C.phi ⟨x, hxΓ⟩ * (C.phi g')⁻¹ ∈ E :=
      ((Subgroup.mem_normalizer_iff.mp hg') _).1 ((C.phi_mem_E_iff ⟨x, hxΓ⟩).mpr hx)
    have h2 : C.phi g' * C.phi ⟨x, hxΓ⟩ * (C.phi g')⁻¹ = C.phi (g' * ⟨x, hxΓ⟩ * g'⁻¹) := by
      simp [map_mul, map_inv]
    rw [h2] at h1
    exact (C.phi_mem_E_iff _).mp h1
  refine ⟨key g (hg ▸ hwE), ?_⟩
  intro x hx
  have := key g⁻¹ (by
    rw [map_inv, hg]
    exact (Subgroup.inv_mem _ hwE)) x hx
  simpa using this

theorem conj_phi_mul_zpow (g x : unitarySU 2 f K 4) (i : ℤ) :
    C.phi g * (C.phi x * c ^ i) * (C.phi g)⁻¹ = C.phi (g * x * g⁻¹) * c ^ i := by
  have h1 : C.phi g * c ^ i * (C.phi g)⁻¹ = c ^ i := C.R.conj_zpow (C.phi_mem_L g) i
  calc C.phi g * (C.phi x * c ^ i) * (C.phi g)⁻¹
      = (C.phi g * C.phi x * (C.phi g)⁻¹) * (C.phi g * c ^ i * (C.phi g)⁻¹) := by group
    _ = C.phi (g * x * g⁻¹) * c ^ i := by rw [h1]; simp [map_mul, map_inv]

end U4Ctx

end CFSG.RankThree.PartOne.KFU
