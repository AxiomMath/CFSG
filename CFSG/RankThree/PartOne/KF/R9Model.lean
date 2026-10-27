module

public import CFSG.RankThree.PartOne.KF.R9Perm
public import CFSG.RankThree.PartOne.S12.Sec12Restrict
public import CFSG.RankThree.PartOne.KF.UnitaryModel

public section

namespace CFSG.RankThree.PartOne.KFU

open CFSG CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne

structure R9Ctx {G : Type} [Group G] [Finite G] (p : ℕ) (L F : Subgroup G) (f : ℕ)
    (K : Type) [Field K] where
  hp : p.Prime
  h5 : 5 ≤ p
  hU : UnitaryFieldData 2 f K
  hf2 : 2 ≤ f
  hpq : p ∣ 2 ^ f + 1
  hFL : F ≤ L
  ψ : unitarySU 2 f K 4 ≃* L
  hψ : ∀ g : unitarySU 2 f K 4, (ψ g : G) ∈ F ↔ (g : GL (Fin 4) K) ∈ torusSU p 4 K

namespace R9Ctx

variable {G : Type} [Group G] [Finite G] {p : ℕ} {L F : Subgroup G} {f : ℕ} {K : Type} [Field K]
  (C : R9Ctx p L F f K)

@[expose] def phi : unitarySU 2 f K 4 →* G := L.subtype.comp C.ψ.toMonoidHom

theorem coe_phi (g : unitarySU 2 f K 4) : (C.phi g : G) = ((C.ψ g : L) : G) := rfl

theorem phi_injective : Function.Injective C.phi := fun _ _ hxy => C.ψ.injective (Subtype.ext hxy)

theorem phi_mem_L (g : unitarySU 2 f K 4) : C.phi g ∈ L := (C.ψ g).2

theorem phi_mem_F_iff (g : unitarySU 2 f K 4) :
    C.phi g ∈ F ↔ (g : GL (Fin 4) K) ∈ torusSU p 4 K := C.hψ g

include C in
theorem torus_le (x : GL (Fin 4) K) (hx : x ∈ torusSU p 4 K) : x ∈ unitarySU 2 f K 4 :=
  torusSU_le_unitarySU C.hU C.hpq hx

theorem exists_phi_eq {l : G} (hl : l ∈ L) : ∃ g : unitarySU 2 f K 4, C.phi g = l :=
  ⟨C.ψ.symm ⟨l, hl⟩, by rw [coe_phi, MulEquiv.apply_symm_apply]⟩

theorem exists_decomp {e : G} (he : e ∈ F) :
    ∃ x : unitarySU 2 f K 4, (x : GL (Fin 4) K) ∈ torusSU p 4 K ∧ C.phi x = e := by
  obtain ⟨x, hx⟩ := C.exists_phi_eq (C.hFL he)
  exact ⟨x, (C.phi_mem_F_iff x).mp (hx ▸ he), hx⟩

include C in
theorem exists_unit_root : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p := by
  obtain ⟨z, hz⟩ := exists_isPrimitiveRoot C.hU C.hp C.hpq
  have hz0 : z ≠ 0 := hz.ne_zero C.hp.ne_zero
  exact ⟨Units.mk0 z hz0, IsPrimitiveRoot.coe_units_iff.mp (by simpa using hz)⟩

include C in
theorem hdist : ∀ i j : Fin 4, i ≠ j → ∃ x ∈ torusSU p 4 K, ent x i i ≠ ent x j j := by
  obtain ⟨ζ, hζ⟩ := C.exists_unit_root
  have h5 := C.h5
  intro i j hij
  exact torus_char_distinct hζ.pow_eq_one
    (hζ.pow_ne_one_of_pos_of_lt (by norm_num) (by omega)) i j hij

theorem conj_torus_mem {g : unitarySU 2 f K 4}
    (hg : C.phi g ∈ Subgroup.normalizer (F : Set G)) :
    ∀ x ∈ torusSU p 4 K,
      (g : GL (Fin 4) K) * x * (g : GL (Fin 4) K)⁻¹ ∈ torusSU p 4 K := by
  intro x hx
  have hxΓ := C.torus_le x hx
  have h1 : C.phi g * C.phi ⟨x, hxΓ⟩ * (C.phi g)⁻¹ ∈ F :=
    ((Subgroup.mem_normalizer_iff.mp hg) _).1 ((C.phi_mem_F_iff ⟨x, hxΓ⟩).mpr hx)
  have h2 : C.phi g * C.phi ⟨x, hxΓ⟩ * (C.phi g)⁻¹ = C.phi (g * ⟨x, hxΓ⟩ * g⁻¹) := by
    simp [map_mul, map_inv]
  rw [h2] at h1
  exact (C.phi_mem_F_iff _).mp h1

theorem exists_perm {w : G} (hwL : w ∈ L) (hwF : w ∈ Subgroup.normalizer (F : Set G)) :
    ∃ (g : unitarySU 2 f K 4) (τ : Equiv.Perm (Fin 4)), C.phi g = w ∧
      NormPerm p (g : GL (Fin 4) K) τ := by
  obtain ⟨g, hg⟩ := C.exists_phi_eq hwL
  have h1 := C.conj_torus_mem (hg ▸ hwF)
  have h2 := C.conj_torus_mem (g := g⁻¹) (by
    rw [map_inv, hg]
    exact Subgroup.inv_mem _ hwF)
  obtain ⟨τ, hτ⟩ := exists_normPerm C.hdist h1 (by simpa using h2)
  exact ⟨g, τ, hg, hτ⟩

@[expose] noncomputable def permHom : Equiv.Perm (Fin 4) →* unitarySU 2 f K 4 :=
  (permGL (n := 4) (K := K)).codRestrict _ fun σ => permGL_mem_unitarySU C.hU σ

theorem coe_permHom (σ : Equiv.Perm (Fin 4)) :
    ((C.permHom σ : unitarySU 2 f K 4) : GL (Fin 4) K) = permGL σ := rfl

theorem phi_perm_conj_mem (σ : Equiv.Perm (Fin 4)) {e : G} (he : e ∈ F) :
    C.phi (C.permHom σ) * e * (C.phi (C.permHom σ))⁻¹ ∈ F := by
  obtain ⟨x, hx, rfl⟩ := C.exists_decomp he
  have h1 : C.phi (C.permHom σ) * C.phi x * (C.phi (C.permHom σ))⁻¹ =
      C.phi (C.permHom σ * x * (C.permHom σ)⁻¹) := by simp [map_mul, map_inv]
  rw [h1, C.phi_mem_F_iff]
  have := (normPerm_permGL (p := p) σ).1 (x : GL (Fin 4) K) hx
  simpa [coe_permHom] using this

theorem phi_perm_mem_normalizer (σ : Equiv.Perm (Fin 4)) :
    C.phi (C.permHom σ) ∈ Subgroup.normalizer (F : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => C.phi_perm_conj_mem σ hh, fun hh => ?_⟩
  have := C.phi_perm_conj_mem σ⁻¹ hh
  rw [map_inv, map_inv] at this
  convert this using 1
  group

@[expose] noncomputable def permPhi : Equiv.Perm (Fin 4) →* ↥(Subgroup.normalizer (F : Set G)) where
  toFun σ := ⟨C.phi (C.permHom σ), C.phi_perm_mem_normalizer σ⟩
  map_one' := Subtype.ext (by simp)
  map_mul' σ τ := Subtype.ext (by simp [map_mul])

@[expose] noncomputable def weylHom : Equiv.Perm (Fin 4) →* MulAut ↥F :=
  F.normalizerMonoidHom.comp C.permPhi

theorem coe_weylHom_apply (σ : Equiv.Perm (Fin 4)) (e : F) :
    ((C.weylHom σ e : F) : G) = C.phi (C.permHom σ) * e * (C.phi (C.permHom σ))⁻¹ := rfl

include C in
theorem torusImage_eq_range : torusImage F L = C.weylHom.range := by
  ext t
  rw [MonoidHom.mem_range]
  constructor
  · intro ht
    obtain ⟨w, hwL, hwF, rfl⟩ := Sec12Three.mem_torusImage_iff.mp ht
    obtain ⟨g, τ, hg, hτ⟩ := C.exists_perm hwL hwF
    refine ⟨τ, MulEquiv.ext fun e => Subtype.ext ?_⟩
    obtain ⟨x, hx, hxe⟩ := C.exists_decomp e.2
    obtain ⟨v, hv1, hv2, hvx⟩ := mem_torusSU_iff.mp hx
    have hv : v ∈ torusVec p 4 K := ⟨hv1, hv2⟩
    rw [coe_weylHom_apply]
    show _ = w * (e : G) * w⁻¹
    rw [← hg, ← hxe]
    have h1 : C.phi g * C.phi x * (C.phi g)⁻¹ = C.phi (g * x * g⁻¹) := by
      simp [map_mul, map_inv]
    have h2 : C.phi (C.permHom τ) * C.phi x * (C.phi (C.permHom τ))⁻¹ =
        C.phi (C.permHom τ * x * (C.permHom τ)⁻¹) := by simp [map_mul, map_inv]
    rw [h1, h2]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_permHom]
    rw [← hvx, permGL_conj_diagU, hτ.conj_diagU hv]
  · rintro ⟨σ, rfl⟩
    exact Sec12Three.mem_torusImage_iff.mpr ⟨C.phi (C.permHom σ), C.phi_mem_L _,
      C.phi_perm_mem_normalizer σ, rfl⟩

end R9Ctx

end CFSG.RankThree.PartOne.KFU
