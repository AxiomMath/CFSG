module

public import CFSG.Quasithin.EmptyFaithful.S146zNCtx
public import CFSG.Quasithin.EmptyFaithful.S146zNFix

public section

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement

namespace CFSG.Quasithin.ThreeC

section Klein

variable {G : Type} [Group G] {T M K U₁ U₂ : Subgroup G} {s : G}

local notation "Zz" => quasithinOmegaOneCenter T

theorem secRho_fix_iff {Z U X : Subgroup G} (hXZ : X ≤ Subgroup.normalizer (Z : Set G))
    (hXU : X ≤ Subgroup.normalizer (U : Set G)) (hU : U ≤ Subgroup.normalizer (Z : Set G)) (g h : ↥X)
    (H : ∀ u ∈ U, ((g : G) * u * (g : G)⁻¹ * u⁻¹ ∈ Z ↔ (h : G) * u * (h : G)⁻¹ * u⁻¹ ∈ Z)) :
    ∀ w : ↥(tildeOf Z U), secRho hXZ hXU g w = w ↔ secRho hXZ hXU h w = w := by
  intro w
  obtain ⟨x', hx', hxw⟩ := mem_secImg.mp w.2
  have hw : w = tildeElt hU (x' : G) hx' := Subtype.ext hxw.symm
  rw [hw, secRho_apply_tildeElt_iff hXZ hXU hU g _ hx', secRho_apply_tildeElt_iff hXZ hXU hU h _ hx']
  exact H _ hx'

theorem secRho_comm_mem_of_eq {Z U X : Subgroup G} (hXZ : X ≤ Subgroup.normalizer (Z : Set G))
    (hXU : X ≤ Subgroup.normalizer (U : Set G)) (hU : U ≤ Subgroup.normalizer (Z : Set G))
    {x y : G} (hxX : x ∈ X) (hyX : y ∈ X)
    (h : secRho hXZ hXU ⟨x, hxX⟩ = secRho hXZ hXU ⟨y, hyX⟩) :
    ∀ u ∈ U, (x⁻¹ * y) * u * (x⁻¹ * y)⁻¹ * u⁻¹ ∈ Z := by
  intro u hu
  have h1 : secRho hXZ hXU ((⟨x, hxX⟩ : ↥X)⁻¹ * ⟨y, hyX⟩) = 1 := by
    rw [map_mul, map_inv, h, inv_mul_cancel]
  exact commutator_mem_of_secRho_eq_one hXZ hXU hU h1 hu

variable [Finite G]

theorem CCtx.sigma_apply (S : Setting146 G T M) (c : CCtx T M K U₁ U₂ s)
    {σ : MulAut (MulAut ↥(tildeOf Zz U₁))}
    (hσρ : ∀ k : ↥K, σ (c.hSec.rho k) = c.hSec.rho (conjAct K ⟨s⁻¹, Subgroup.inv_mem _ c.hsK⟩ k))
    {X : Subgroup G} (hXZ : X ≤ Subgroup.normalizer (Zz : Set G))
    (hXU : X ≤ Subgroup.normalizer (U₁ : Set G)) (hKX : K ≤ X)
    {x : G} (hxK : x ∈ Subgroup.normalizer (K : Set G))
    (hxU : x ∈ Subgroup.normalizer (uOfL22 T M : Set G))
    (hxZ : x ∈ Subgroup.normalizer (Zz : Set G)) (hx₁ : conjSub x U₁ = U₁)
    (hxX : x ∈ X) (hxsX : s⁻¹ * x * s ∈ X) :
    σ (secRho hXZ hXU ⟨x, hxX⟩) = secRho hXZ hXU ⟨s⁻¹ * x * s, hxsX⟩ := by
  classical
  obtain ⟨kx, hkx, htx⟩ := c.exists_k S hxK hxU hxZ hx₁
  have hkxX : (kx : G) ∈ X := hKX hkx
  have hρ : ∀ (k : G) (hk : k ∈ K), c.hSec.rho ⟨k, hk⟩ = secRho hXZ hXU ⟨k, hKX hk⟩ :=
    fun k hk => secRho_congr c.hSec.KZ c.hSec.KU hXZ hXU rfl
  have hxkx : secRho hXZ hXU ⟨x, hxX⟩ = secRho hXZ hXU ⟨kx, hkxX⟩ := by
    apply secRho_eq_of_comm hXZ hXU c.hSec.norm
    intro u hu
    exact htx u (Subgroup.mem_sup_left hu)
  have hnuK : s⁻¹ ∈ Subgroup.normalizer (K : Set G) := Subgroup.inv_mem _ c.hsK
  have e1 : secRho hXZ hXU ⟨kx, hkxX⟩ = c.hSec.rho ⟨kx, hkx⟩ := (hρ kx hkx).symm
  rw [hxkx, e1, hσρ]
  have hcoe : ((conjAct K ⟨s⁻¹, hnuK⟩ ⟨kx, hkx⟩ : ↥K) : G) = s⁻¹ * kx * s := by
    have := conjAct_apply_coe' K ⟨s⁻¹, hnuK⟩ ⟨kx, hkx⟩
    simpa using this
  have hkxsK : s⁻¹ * kx * s ∈ K := hcoe ▸ (conjAct K ⟨s⁻¹, hnuK⟩ ⟨kx, hkx⟩).2
  have e2 : c.hSec.rho (conjAct K ⟨s⁻¹, hnuK⟩ ⟨kx, hkx⟩) =
      secRho hXZ hXU ⟨s⁻¹ * kx * s, hKX hkxsK⟩ := by
    rw [hρ _ (conjAct K ⟨s⁻¹, hnuK⟩ ⟨kx, hkx⟩).2]
    exact congrArg (secRho hXZ hXU) (Subtype.ext hcoe)
  rw [e2]
  refine Eq.symm (secRho_eq_of_comm hXZ hXU c.hSec.norm ?_)
  intro u hu
  have e3 : ((⟨s⁻¹ * kx * s, hKX hkxsK⟩ : ↥X)⁻¹ * ⟨s⁻¹ * x * s, hxsX⟩ : ↥X) =
      (⟨s⁻¹ * (kx⁻¹ * x) * s, by
        have : s⁻¹ * (kx⁻¹ * x) * s = (s⁻¹ * kx * s)⁻¹ * (s⁻¹ * x * s) := by group
        rw [this]; exact X.mul_mem (X.inv_mem (hKX hkxsK)) hxsX⟩ : ↥X) :=
    Subtype.ext (by show (s⁻¹ * kx * s)⁻¹ * (s⁻¹ * x * s) = s⁻¹ * (kx⁻¹ * x) * s; group)
  rw [e3]
  exact c.comm_conj_s (fun u' hu' => htx u' (Subgroup.mem_sup_right hu')) u hu

theorem CCtx.act_eq_of_fix (S : Setting146 G T M) (c : CCtx T M K U₁ U₂ s) {x y : G}
    (hxK : x ∈ Subgroup.normalizer (K : Set G)) (hxU : x ∈ Subgroup.normalizer (uOfL22 T M : Set G))
    (hxZ : x ∈ Subgroup.normalizer (Zz : Set G)) (hx₁ : conjSub x U₁ = U₁)
    (hyK : y ∈ Subgroup.normalizer (K : Set G)) (hyU : y ∈ Subgroup.normalizer (uOfL22 T M : Set G))
    (hyZ : y ∈ Subgroup.normalizer (Zz : Set G)) (hy₁ : conjSub y U₁ = U₁)
    (hx2 : x * x = 1) (hy2 : y * y = 1)
    (hxn : ∃ w ∈ U₁, x * w * x⁻¹ * w⁻¹ ∉ Zz) (hyn : ∃ w ∈ U₁, y * w * y⁻¹ * w⁻¹ ∉ Zz)
    (hA : ∀ u ∈ U₁, (x * u * x⁻¹ * u⁻¹ ∈ Zz ↔ y * u * y⁻¹ * u⁻¹ ∈ Zz))
    (hB : ∀ u ∈ U₂, (x * u * x⁻¹ * u⁻¹ ∈ Zz ↔ y * u * y⁻¹ * u⁻¹ ∈ Zz)) :
    ∀ z ∈ U₁ ⊔ U₂, (x⁻¹ * y) * z * (x⁻¹ * y)⁻¹ * z⁻¹ ∈ Zz := by
  classical
  have hsZ := c.hsZ
  obtain ⟨σ, hσρ, hσout⟩ := c.exists_sigma
  set X : Subgroup G := Subgroup.normalizer (Zz : Set G) ⊓ Subgroup.normalizer (U₁ : Set G) with hXdef
  have hXZ : X ≤ Subgroup.normalizer (Zz : Set G) := inf_le_left
  have hXU : X ≤ Subgroup.normalizer (U₁ : Set G) := inf_le_right
  have hKX : K ≤ X := fun k hk => ⟨c.hSec.KZ hk, c.hSec.KU hk⟩
  have hxX : x ∈ X := ⟨hxZ, mem_normalizer_of_conjSub_eq hx₁⟩
  have hyX : y ∈ X := ⟨hyZ, mem_normalizer_of_conjSub_eq hy₁⟩
  have hxsX : s⁻¹ * x * s ∈ X :=
    ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hsZ) hxZ) hsZ,
      mem_normalizer_of_conjSub_eq (c.conjSub_s_inner S hxK hxU hxZ hx₁)⟩
  have hysX : s⁻¹ * y * s ∈ X :=
    ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hsZ) hyZ) hsZ,
      mem_normalizer_of_conjSub_eq (c.conjSub_s_inner S hyK hyU hyZ hy₁)⟩
  have hσx := c.sigma_apply S hσρ hXZ hXU hKX hxK hxU hxZ hx₁ hxX hxsX
  have hσy := c.sigma_apply S hσρ hXZ hXU hKX hyK hyU hyZ hy₁ hyX hysX
  set a := secRho hXZ hXU ⟨x, hxX⟩ with ha
  set b := secRho hXZ hXU ⟨y, hyX⟩ with hb
  have ha2 : a * a = 1 := by
    rw [ha, ← map_mul]
    have : (⟨x, hxX⟩ * ⟨x, hxX⟩ : ↥X) = 1 := Subtype.ext hx2
    rw [this, map_one]
  have hb2 : b * b = 1 := by
    rw [hb, ← map_mul]
    have : (⟨y, hyX⟩ * ⟨y, hyX⟩ : ↥X) = 1 := Subtype.ext hy2
    rw [this, map_one]
  have ha1 : a ≠ 1 := by
    intro h
    obtain ⟨w, hw, hwn⟩ := hxn
    exact hwn (commutator_mem_of_secRho_eq_one hXZ hXU c.hSec.norm (x := ⟨x, hxX⟩) h hw)
  have hb1 : b ≠ 1 := by
    intro h
    obtain ⟨w, hw, hwn⟩ := hyn
    exact hwn (commutator_mem_of_secRho_eq_one hXZ hXU c.hSec.norm (x := ⟨y, hyX⟩) h hw)
  have hF : ∀ w : ↥(tildeOf Zz U₁), a w = w ↔ b w = w :=
    secRho_fix_iff hXZ hXU c.hSec.norm ⟨x, hxX⟩ ⟨y, hyX⟩ (fun u hu => hA u hu)
  have hconjZ : ∀ w : G, s⁻¹ * w * s ∈ Zz ↔ w ∈ Zz := fun w => by
    have := Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hsZ) w
    simpa using this.symm
  have hFσ : ∀ w : ↥(tildeOf Zz U₁), σ a w = w ↔ σ b w = w := by
    rw [ha, hb, hσx, hσy]
    refine secRho_fix_iff hXZ hXU c.hSec.norm ⟨s⁻¹ * x * s, hxsX⟩ ⟨s⁻¹ * y * s, hysX⟩ (fun u hu => ?_)
    have hu₂ : s * u * s⁻¹ ∈ U₂ := by rw [c.hU₂]; exact mul_mem_conjSub hu
    have ex : (s⁻¹ * x * s) * u * (s⁻¹ * x * s)⁻¹ * u⁻¹ =
        s⁻¹ * (x * (s * u * s⁻¹) * x⁻¹ * (s * u * s⁻¹)⁻¹) * s := by group
    have ey : (s⁻¹ * y * s) * u * (s⁻¹ * y * s)⁻¹ * u⁻¹ =
        s⁻¹ * (y * (s * u * s⁻¹) * y⁻¹ * (s * u * s⁻¹)⁻¹) * s := by group
    show (s⁻¹ * x * s) * u * (s⁻¹ * x * s)⁻¹ * u⁻¹ ∈ Zz ↔ (s⁻¹ * y * s) * u * (s⁻¹ * y * s)⁻¹ * u⁻¹ ∈ Zz
    rw [ex, ey, hconjZ, hconjZ]
    exact hB _ hu₂
  have hel := c.hSec.isElemAbelian_tilde
  have hab : a = b := fix_injective (W := ↥(tildeOf Zz U₁))
    (fun p q => Subtype.ext (isElemAbelian_comm hel p.2 q.2))
    (fun p => Subtype.ext (by simpa [pow_two] using isElemAbelian_pow_eq_one hel p.2))
    c.hSec.card_tilde σ hσout ha2 hb2 ha1 hb1 hF hFσ
  have htriv : ∀ w ∈ U₁, (x⁻¹ * y) * w * (x⁻¹ * y)⁻¹ * w⁻¹ ∈ Zz :=
    secRho_comm_mem_of_eq hXZ hXU c.hSec.norm hxX hyX hab
  have hxyK : x⁻¹ * y ∈ Subgroup.normalizer (K : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hxK) hyK
  have hxyU : x⁻¹ * y ∈ Subgroup.normalizer (uOfL22 T M : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hxU) hyU
  have hxyZ : x⁻¹ * y ∈ Subgroup.normalizer (Zz : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hxZ) hyZ
  have hxyU₁ : x⁻¹ * y ∈ Subgroup.normalizer (U₁ : Set G) :=
    hXU (X.mul_mem (X.inv_mem hxX) hyX)
  exact c.trivial_of_centralizes S hxyK hxyU hxyZ (c.centralizes_of_trivial₁ hxyK hxyZ hxyU₁ htriv)

end Klein

end CFSG.Quasithin.ThreeC
