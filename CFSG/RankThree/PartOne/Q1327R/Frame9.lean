module

public import CFSG.RankThree.PartOne.KF.UnitaryModel
public import CFSG.RankThree.PartOne.KF.U4Perm
public import CFSG.RankThree.PartOne.S12.Sec12Restrict

public section

namespace CFSG.RankThree.PartOne.Q1327R

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.Sec12Three
  CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

structure U4Frame {G : Type} [Group G] (p f : ℕ) (K : Type) [Field K] (X F : Subgroup G) where
  hp : p.Prime
  hp5 : 5 ≤ p
  hU : UnitaryFieldData 2 f K
  hf2 : 2 ≤ f
  hpq : p ∣ 2 ^ f + 1
  hFX : F ≤ X
  ψ : unitarySU 2 f K 4 ≃* X
  hψ : ∀ g : unitarySU 2 f K 4, ((ψ g : X) : G) ∈ F ↔ (g : GL (Fin 4) K) ∈ torusSU p 4 K

namespace U4Frame

variable {G : Type} [Group G] {p f : ℕ} {K : Type} [Field K] {X F : Subgroup G}
  (C : U4Frame p f K X F)

@[expose] def phi : unitarySU 2 f K 4 →* G := X.subtype.comp C.ψ.toMonoidHom

theorem coe_phi (g : unitarySU 2 f K 4) : (C.phi g : G) = ((C.ψ g : X) : G) := rfl

theorem phi_injective : Function.Injective C.phi := fun _ _ hxy => C.ψ.injective (Subtype.ext hxy)

theorem phi_mem_X (g : unitarySU 2 f K 4) : C.phi g ∈ X := (C.ψ g).2

theorem phi_mem_F_iff (g : unitarySU 2 f K 4) :
    C.phi g ∈ F ↔ (g : GL (Fin 4) K) ∈ torusSU p 4 K := C.hψ g

include C in
theorem torus_le (x : GL (Fin 4) K) (hx : x ∈ torusSU p 4 K) : x ∈ unitarySU 2 f K 4 :=
  torusSU_le_unitarySU C.hU C.hpq hx

theorem exists_phi_eq {l : G} (hl : l ∈ X) : ∃ g : unitarySU 2 f K 4, C.phi g = l :=
  ⟨C.ψ.symm ⟨l, hl⟩, by rw [coe_phi, MulEquiv.apply_symm_apply]⟩

theorem exists_decomp {e : G} (he : e ∈ F) :
    ∃ x : unitarySU 2 f K 4, (x : GL (Fin 4) K) ∈ torusSU p 4 K ∧ e = C.phi x := by
  obtain ⟨x, hx⟩ := C.exists_phi_eq (C.hFX he)
  exact ⟨x, (C.phi_mem_F_iff x).mp (hx ▸ he), hx.symm⟩

theorem phi_mem_F_of_torus {x : unitarySU 2 f K 4} (hx : (x : GL (Fin 4) K) ∈ torusSU p 4 K) :
    C.phi x ∈ F := (C.phi_mem_F_iff x).mpr hx

theorem conj_phi (g x : unitarySU 2 f K 4) :
    C.phi g * C.phi x * (C.phi g)⁻¹ = C.phi (g * x * g⁻¹) := by
  simp [map_mul, map_inv]

include C in
theorem normalizes_torus {w : G} (hwF : w ∈ Subgroup.normalizer (F : Set G))
    {g : unitarySU 2 f K 4} (hg : C.phi g = w) :
    (∀ x ∈ torusSU p 4 K, (g : GL (Fin 4) K) * x * (g : GL (Fin 4) K)⁻¹ ∈ torusSU p 4 K) ∧
      ∀ x ∈ torusSU p 4 K, (g : GL (Fin 4) K)⁻¹ * x * (g : GL (Fin 4) K) ∈ torusSU p 4 K := by
  have key : ∀ (g' : unitarySU 2 f K 4), C.phi g' ∈ Subgroup.normalizer (F : Set G) →
      ∀ x ∈ torusSU p 4 K,
        (g' : GL (Fin 4) K) * x * (g' : GL (Fin 4) K)⁻¹ ∈ torusSU p 4 K := by
    intro g' hg' x hx
    have hxΓ := C.torus_le x hx
    have h1 : C.phi g' * C.phi ⟨x, hxΓ⟩ * (C.phi g')⁻¹ ∈ F :=
      ((Subgroup.mem_normalizer_iff.mp hg') _).1 ((C.phi_mem_F_iff ⟨x, hxΓ⟩).mpr hx)
    rw [C.conj_phi] at h1
    exact (C.phi_mem_F_iff _).mp h1
  refine ⟨key g (hg ▸ hwF), ?_⟩
  intro x hx
  have := key g⁻¹ (by
    rw [map_inv, hg]
    exact (Subgroup.inv_mem _ hwF)) x hx
  simpa using this

include C in
theorem exists_unit_root : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p := by
  obtain ⟨z, hz⟩ := exists_isPrimitiveRoot C.hU C.hp C.hpq
  have hz0 : z ≠ 0 := hz.ne_zero C.hp.ne_zero
  exact ⟨Units.mk0 z hz0, IsPrimitiveRoot.coe_units_iff.mp (by simpa using hz)⟩

include C in
theorem hdist : ∀ i j : Fin 4, i ≠ j → ∃ x ∈ torusSU p 4 K, ent x i i ≠ ent x j j := by
  obtain ⟨ζ, hζ⟩ := C.exists_unit_root
  have h3 := C.hp5
  intro i j hij
  exact torus_char_distinct hζ.pow_eq_one
    (hζ.pow_ne_one_of_pos_of_lt (by norm_num) (by omega)) i j hij

theorem exists_perm {w : G} (hwX : w ∈ X) (hwF : w ∈ Subgroup.normalizer (F : Set G)) :
    ∃ (g : unitarySU 2 f K 4) (τ : Equiv.Perm (Fin 4)), C.phi g = w ∧
      NormPerm p (g : GL (Fin 4) K) τ := by
  obtain ⟨g, hg⟩ := C.exists_phi_eq hwX
  obtain ⟨h1, h2⟩ := C.normalizes_torus hwF hg
  obtain ⟨τ, hτ⟩ := exists_normPerm C.hdist h1 h2
  exact ⟨g, τ, hg, hτ⟩

omit [Field K] in
theorem coe_conj_apply (w : G) (hwF : w ∈ Subgroup.normalizer (F : Set G)) (e : F) :
    ((F.normalizerMonoidHom ⟨w, hwF⟩ e : F) : G) = w * e * w⁻¹ := rfl

end U4Frame

end CFSG.RankThree.PartOne.Q1327R
