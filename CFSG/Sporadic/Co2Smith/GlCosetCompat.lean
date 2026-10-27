module

public import CFSG.Sporadic.Co2Smith.GlDefs
public import CFSG.Sporadic.Co2Smith.G21
public import CFSG.Sporadic.Co2Smith.GlDataG1

public section

namespace CFSG.Sporadic.Co2Smith

open Subgroup CFSG.Sporadic.Co2Rank3 CFSG.Sporadic.Co2Cert

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

structure SmithMarkedData
    {G : Type*} [Group G] (z : G) where
  φ : centralizer ({z} : Set G) ≃* Cz
  ρ : C0c →* G
  G₁ : Subgroup G
  ψ : G₁ ≃* co2P0
  φ_z : φ (zC z) = zCz
  marking : SmithC0Marking φ α3c ρ
  ψ_cz : ∀ (h : G₁) (hz : (h : G) ∈ centralizer ({z} : Set G)),
    (ψ h : Equiv.Perm (Fin 2300)) =
      cPerm * (co2PermEquiv (φ ⟨h, hz⟩ : K) : Equiv.Perm (Fin 2300)) * cPerm⁻¹
  ψ_c0 : ∀ w : C0c, (w : K) ∈ G1c → ∃ hw : ρ w ∈ G₁,
    (ψ ⟨ρ w, hw⟩ : Equiv.Perm (Fin 2300)) =
      cPerm * (co2PermEquiv (w : K) : Equiv.Perm (Fin 2300)) * cPerm⁻¹

namespace SmithMarkedData

variable
  {G : Type*} [Group G] {z : G} (S : SmithMarkedData z)

@[expose] noncomputable def phiInv : Cz →* G :=
  (centralizer ({z} : Set G)).subtype.comp S.φ.symm.toMonoidHom

theorem phiInv_apply (g : Cz) : S.phiInv g = (S.φ.symm g : G) := rfl

theorem phiInv_mem_centralizer (g : Cz) : S.phiInv g ∈ centralizer ({z} : Set G) :=
  (S.φ.symm g).2

theorem ψ_injective {h h' : S.G₁}
    (e : (S.ψ h : Equiv.Perm (Fin 2300)) = (S.ψ h' : Equiv.Perm (Fin 2300))) : h = h' :=
  S.ψ.injective (Subtype.ext e)

theorem exists_ψ_eq {σ : Equiv.Perm (Fin 2300)} (hσ : σ ∈ co2P0) :
    ∃ h : S.G₁, (S.ψ h : Equiv.Perm (Fin 2300)) = σ :=
  ⟨S.ψ.symm ⟨σ, hσ⟩, by rw [MulEquiv.apply_symm_apply]⟩

theorem ψ_apply_zero (h : S.G₁) : (S.ψ h : Equiv.Perm (Fin 2300)) 0 = 0 :=
  MulAction.mem_stabilizer_iff.1 (S.ψ h).2.2

theorem marking_c0 (w : K) : cPerm * (co2PermEquiv w : Equiv.Perm (Fin 2300)) * cPerm⁻¹ =
    psiK w := by
  rw [co2PermEquiv_apply, psiK_apply]

theorem ρ_eq_phiInv {k : K} (hk0 : k ∈ C0c) (hkz : k ∈ Cz) :
    S.ρ ⟨k, hk0⟩ = S.phiInv ⟨k, hkz⟩ :=
  S.marking.2.2 ⟨k, hk0⟩ hkz

theorem phiInv_zCz : S.phiInv zCz = z := by
  rw [phiInv_apply, ← S.φ_z, MulEquiv.symm_apply_apply]
  rfl

@[expose] def Compat (x : G) (xc : K) (h : S.G₁) : Prop :=
  ∃ hm : x * (h : G) * x⁻¹ ∈ S.G₁, (S.ψ ⟨_, hm⟩ : Equiv.Perm (Fin 2300)) =
    psiK xc * (S.ψ h : Equiv.Perm (Fin 2300)) * (psiK xc)⁻¹

variable {S} in
theorem Compat.mem {x : G} {xc : K} {h : S.G₁} (hx : S.Compat x xc h) :
    x * (h : G) * x⁻¹ ∈ S.G₁ :=
  hx.1

@[expose] def compatSubgroup (x : G) (xc : K) : Subgroup S.G₁ where
  carrier := {h | S.Compat x xc h}
  mul_mem' := by
    rintro a b ⟨ha, ea⟩ ⟨hb, eb⟩
    have e1 : x * ((a * b : S.G₁) : G) * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹) := by
      rw [Subgroup.coe_mul]
      group
    have hm : x * ((a * b : S.G₁) : G) * x⁻¹ ∈ S.G₁ := by
      rw [e1]
      exact S.G₁.mul_mem ha hb
    refine ⟨hm, ?_⟩
    have e : (⟨_, hm⟩ : S.G₁) = ⟨_, ha⟩ * ⟨_, hb⟩ := Subtype.ext e1
    rw [e, map_mul, Subgroup.coe_mul, ea, eb, map_mul, Subgroup.coe_mul]
    group
  one_mem' := by
    have e1 : x * ((1 : S.G₁) : G) * x⁻¹ = 1 := by
      rw [Subgroup.coe_one]
      group
    have hm : x * ((1 : S.G₁) : G) * x⁻¹ ∈ S.G₁ := by
      rw [e1]
      exact S.G₁.one_mem
    refine ⟨hm, ?_⟩
    have e : (⟨_, hm⟩ : S.G₁) = 1 := Subtype.ext e1
    rw [e, map_one, Subgroup.coe_one]
    group
  inv_mem' := by
    rintro a ⟨ha, ea⟩
    have e1 : x * ((a⁻¹ : S.G₁) : G) * x⁻¹ = (x * a * x⁻¹)⁻¹ := by
      rw [Subgroup.coe_inv]
      group
    have hm : x * ((a⁻¹ : S.G₁) : G) * x⁻¹ ∈ S.G₁ := by
      rw [e1]
      exact S.G₁.inv_mem ha
    refine ⟨hm, ?_⟩
    have e : (⟨_, hm⟩ : S.G₁) = (⟨_, ha⟩ : S.G₁)⁻¹ := Subtype.ext e1
    rw [e, map_inv, Subgroup.coe_inv, ea, map_inv, Subgroup.coe_inv]
    group

variable {S} in
theorem Compat.trans {x y : G} {xc yc : K} {h : S.G₁} (hx : S.Compat x xc h)
    (hy : S.Compat y yc ⟨_, hx.mem⟩) : S.Compat (y * x) (yc * xc) h := by
  obtain ⟨hm, e⟩ := hx
  obtain ⟨hm', e'⟩ := hy
  have h1 : y * x * (h : G) * (y * x)⁻¹ = y * (x * h * x⁻¹) * y⁻¹ := by group
  have hm'' : y * x * (h : G) * (y * x)⁻¹ ∈ S.G₁ := by
    rw [h1]
    exact hm'
  refine ⟨hm'', ?_⟩
  have e2 : (⟨_, hm''⟩ : S.G₁) = ⟨_, hm'⟩ := Subtype.ext h1
  rw [e2, e', e, map_mul]
  group

theorem mem_of_mem_closure {T : Subgroup S.G₁} {A : Set (Equiv.Perm (Fin 2300))}
    (hA : ∀ σ ∈ A, ∃ h ∈ T, (S.ψ h : Equiv.Perm (Fin 2300)) = σ) {h : S.G₁}
    (hh : (S.ψ h : Equiv.Perm (Fin 2300)) ∈ Subgroup.closure A) : h ∈ T := by
  have hle : Subgroup.closure A ≤ (T.map S.ψ.toMonoidHom).map co2P0.subtype := by
    rw [Subgroup.closure_le]
    intro σ hσ
    obtain ⟨h', hh', rfl⟩ := hA σ hσ
    exact ⟨S.ψ h', ⟨h', hh', rfl⟩, rfl⟩
  obtain ⟨_, ⟨h', hh', rfl⟩, e⟩ := hle hh
  rw [← S.ψ_injective e]
  exact hh'

@[expose] noncomputable def Ψ : G1c →* G :=
  S.G₁.subtype.comp (S.ψ.symm.toMonoidHom.comp G1cEquiv.toMonoidHom)

theorem Ψ_mem (k : G1c) : S.Ψ k ∈ S.G₁ := (S.ψ.symm (G1cEquiv k)).2

theorem Ψ_eq (k : G1c) : (⟨S.Ψ k, S.Ψ_mem k⟩ : S.G₁) = S.ψ.symm (G1cEquiv k) := rfl

theorem ψ_Ψ (k : G1c) : (S.ψ ⟨S.Ψ k, S.Ψ_mem k⟩ : Equiv.Perm (Fin 2300)) = psiK k := by
  rw [S.Ψ_eq, MulEquiv.apply_symm_apply, G1cEquiv_apply]

theorem ρ_eq_Ψ {k : K} (hk0 : k ∈ C0c) (hk1 : k ∈ G1c) : S.ρ ⟨k, hk0⟩ = S.Ψ ⟨k, hk1⟩ := by
  obtain ⟨hw, e⟩ := S.ψ_c0 ⟨k, hk0⟩ hk1
  have : (⟨S.ρ ⟨k, hk0⟩, hw⟩ : S.G₁) = ⟨S.Ψ ⟨k, hk1⟩, S.Ψ_mem _⟩ := by
    apply S.ψ_injective
    rw [e, S.ψ_Ψ, marking_c0]
  exact congrArg Subtype.val this

theorem Ψ_z0 (hz1 : z0 ∈ G1c) : S.Ψ ⟨z0, hz1⟩ = z := by
  have hz0 : z0 ∈ C0c := x16K_eq ▸ x16K_mem_C0c
  rw [← S.ρ_eq_Ψ hz0 hz1, S.ρ_eq_phiInv hz0 z0_mem_Cz]
  exact S.phiInv_zCz

theorem Ψ_eq_phiInv (hz1 : z0 ∈ G1c) {k : K} (hk1 : k ∈ G1c) (hkz : k ∈ Cz) :
    S.Ψ ⟨k, hk1⟩ = S.phiInv ⟨k, hkz⟩ := by
  have hc : S.Ψ ⟨k, hk1⟩ ∈ centralizer ({z} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    have e : S.Ψ ⟨k, hk1⟩ * S.Ψ ⟨z0, hz1⟩ = S.Ψ ⟨z0, hz1⟩ * S.Ψ ⟨k, hk1⟩ := by
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (comm_of_mem_Cz hkz)
    rwa [S.Ψ_z0 hz1] at e
  have e := S.ψ_cz ⟨S.Ψ ⟨k, hk1⟩, S.Ψ_mem _⟩ hc
  rw [S.ψ_Ψ, marking_c0] at e
  have e' : (S.φ ⟨S.Ψ ⟨k, hk1⟩, hc⟩ : K) = k := (psiK_injective e).symm
  have e'' : S.φ ⟨S.Ψ ⟨k, hk1⟩, hc⟩ = ⟨k, hkz⟩ := Subtype.ext e'
  rw [phiInv_apply, ← e'', MulEquiv.symm_apply_apply]

theorem mem_G1c_of_phiInv_mem {g : K} (hg : g ∈ Cz) (h : S.phiInv ⟨g, hg⟩ ∈ S.G₁) :
    g ∈ G1c := by
  have e := S.ψ_cz ⟨_, h⟩ (S.phiInv_mem_centralizer _)
  have e2 : S.φ ⟨S.phiInv ⟨g, hg⟩, S.phiInv_mem_centralizer _⟩ = ⟨g, hg⟩ := by
    rw [show (⟨S.phiInv ⟨g, hg⟩, S.phiInv_mem_centralizer _⟩ : centralizer ({z} : Set G)) =
      S.φ.symm ⟨g, hg⟩ from rfl, MulEquiv.apply_symm_apply]
  rw [e2, marking_c0] at e
  have h0 := S.ψ_apply_zero ⟨_, h⟩
  rw [e, ← cPerm_p0, psiK_fix_iff] at h0
  exact h0

theorem compat_Ψ (xc : G1c) (h : S.G₁) : S.Compat (S.Ψ xc) xc h := by
  refine ⟨S.G₁.mul_mem (S.G₁.mul_mem (S.Ψ_mem xc) h.2) (S.G₁.inv_mem (S.Ψ_mem xc)), ?_⟩
  have e : (⟨S.Ψ xc * h * (S.Ψ xc)⁻¹, S.G₁.mul_mem (S.G₁.mul_mem (S.Ψ_mem xc) h.2)
      (S.G₁.inv_mem (S.Ψ_mem xc))⟩ : S.G₁) =
      ⟨S.Ψ xc, S.Ψ_mem xc⟩ * h * (⟨S.Ψ xc, S.Ψ_mem xc⟩ : S.G₁)⁻¹ := rfl
  rw [e, map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
    S.ψ_Ψ]

theorem ψ_eq_of_eq_Ψ {g : G} (hg : g ∈ S.G₁) {k : G1c} (e : g = S.Ψ k) :
    (S.ψ ⟨g, hg⟩ : Equiv.Perm (Fin 2300)) = psiK k := by
  have e' : (⟨g, hg⟩ : S.G₁) = ⟨S.Ψ k, S.Ψ_mem k⟩ := Subtype.ext e
  rw [e', S.ψ_Ψ]

theorem compat_phiInv (hz1 : z0 ∈ G1c) {xc k : K} (hxc : xc ∈ Cz) (hk1 : k ∈ G1c) (hkz : k ∈ Cz)
    (hc : xc * k * xc⁻¹ ∈ G1c) :
    S.Compat (S.phiInv ⟨xc, hxc⟩) xc ⟨S.Ψ ⟨k, hk1⟩, S.Ψ_mem _⟩ := by
  have hcz : xc * k * xc⁻¹ ∈ Cz := Cz.mul_mem (Cz.mul_mem hxc hkz) (Cz.inv_mem hxc)
  have e : S.phiInv ⟨xc, hxc⟩ * S.Ψ ⟨k, hk1⟩ * (S.phiInv ⟨xc, hxc⟩)⁻¹ = S.Ψ ⟨_, hc⟩ := by
    rw [S.Ψ_eq_phiInv hz1 hk1 hkz, S.Ψ_eq_phiInv hz1 hc hcz, ← map_inv, ← map_mul, ← map_mul]
    rfl
  have hm : S.phiInv ⟨xc, hxc⟩ * S.Ψ ⟨k, hk1⟩ * (S.phiInv ⟨xc, hxc⟩)⁻¹ ∈ S.G₁ := by
    rw [e]
    exact S.Ψ_mem _
  refine ⟨hm, ?_⟩
  rw [S.ψ_eq_of_eq_Ψ hm e, S.ψ_Ψ, map_mul, map_mul, map_inv]

theorem compat_ρ {xc k : K} (hxc : xc ∈ C0c) (hk1 : k ∈ G1c) (hk0 : k ∈ C0c)
    (hc : xc * k * xc⁻¹ ∈ G1c) :
    S.Compat (S.ρ ⟨xc, hxc⟩) xc ⟨S.Ψ ⟨k, hk1⟩, S.Ψ_mem _⟩ := by
  have hc0 : xc * k * xc⁻¹ ∈ C0c := C0c.mul_mem (C0c.mul_mem hxc hk0) (C0c.inv_mem hxc)
  have e : S.ρ ⟨xc, hxc⟩ * S.Ψ ⟨k, hk1⟩ * (S.ρ ⟨xc, hxc⟩)⁻¹ = S.Ψ ⟨_, hc⟩ := by
    rw [← S.ρ_eq_Ψ hk0 hk1, ← S.ρ_eq_Ψ hc0 hc, ← map_inv, ← map_mul, ← map_mul]
    rfl
  have hm : S.ρ ⟨xc, hxc⟩ * S.Ψ ⟨k, hk1⟩ * (S.ρ ⟨xc, hxc⟩)⁻¹ ∈ S.G₁ := by
    rw [e]
    exact S.Ψ_mem _
  refine ⟨hm, ?_⟩
  rw [S.ψ_eq_of_eq_Ψ hm e, S.ψ_Ψ, map_mul, map_mul, map_inv]

end SmithMarkedData

end CFSG.Sporadic.Co2Smith
