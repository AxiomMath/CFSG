module

public import CFSG.Assembly.Defs
public import CFSG.Monster.GMS.CoTwoCentral

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic
open CFSG.Sporadic.Co1.Module hiding co1Act
open scoped commutatorElement

namespace CoTwoAutSetup

variable {G : Type} [Group G] {t : G} (L : LeechSystem t)

open scoped Classical in
@[expose] noncomputable def phiG (g : G) : Co1 :=
  if h : g ∈ Subgroup.centralizer ({t} : Set G) then L.φ ⟨g, h⟩ else 1

theorem phiG_of_mem (L : LeechSystem t) {g : G} (hg : g ∈ Subgroup.centralizer ({t} : Set G)) :
    phiG L g = L.φ ⟨g, hg⟩ := by
  unfold phiG
  simp [hg]

theorem phiG_mul (L : LeechSystem t) {g h : G} (hg : g ∈ Subgroup.centralizer ({t} : Set G))
    (hh : h ∈ Subgroup.centralizer ({t} : Set G)) : phiG L (g * h) = phiG L g * phiG L h := by
  rw [phiG_of_mem L (mul_mem hg hh), phiG_of_mem L hg, phiG_of_mem L hh, ← map_mul]
  rfl

theorem phiG_one (L : LeechSystem t) : phiG L (1 : G) = 1 := by
  rw [phiG_of_mem L (one_mem _)]
  exact map_one L.φ

theorem phiG_inv (L : LeechSystem t) {g : G} (hg : g ∈ Subgroup.centralizer ({t} : Set G)) :
    phiG L g⁻¹ = (phiG L g)⁻¹ := by
  rw [phiG_of_mem L (inv_mem hg), phiG_of_mem L hg, ← map_inv]
  rfl

theorem phiG_eq_one_iff (L : LeechSystem t) {g : G} (hg : g ∈ Subgroup.centralizer ({t} : Set G)) :
    phiG L g = 1 ↔ g ∈ leechQ t := by
  rw [phiG_of_mem L hg]
  exact L.φ_ker ⟨g, hg⟩

theorem vec_conj_phiG (L : LeechSystem t) {c q : G}
    (hc : c ∈ Subgroup.centralizer ({t} : Set G)) (hq : q ∈ leechQ t) :
    L.vec (c * q * c⁻¹) = co1Act (phiG L c) (L.vec q) := by
  rw [phiG_of_mem L hc]
  exact L.vec_conj' hc hq

theorem phiG_eq_one_of_mem (L : LeechSystem t) {q : G} (hq : q ∈ leechQ t) : phiG L q = 1 :=
  (phiG_eq_one_iff L (L.mem_centralizer hq)).2 hq

@[expose] def Xsub (x t : G) : Subgroup G :=
  Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer {t}

@[expose] def Rsub (x t : G) : Subgroup G := leechQ t ⊓ Subgroup.centralizer ({x} : Set G)

variable {x : G}

theorem Xsub_le_C {g : G} (hg : g ∈ Xsub x t) : g ∈ Subgroup.centralizer ({t} : Set G) := hg.2

theorem Rsub_le_Xsub (L : LeechSystem t) {r : G} (hr : r ∈ Rsub x t) : r ∈ Xsub x t :=
  ⟨hr.2, L.mem_centralizer hr.1⟩

theorem x_comm_t (L : LeechSystem t) (hx : x ∈ leechQ t) : x * t = t * x :=
  Subgroup.mem_centralizer_singleton_iff.1 (L.mem_centralizer hx)

theorem t_mem_Rsub (L : LeechSystem t) (hx : x ∈ leechQ t) : t ∈ Rsub x t :=
  ⟨L.z_mem, Subgroup.mem_centralizer_singleton_iff.2 (x_comm_t L hx).symm⟩

theorem x_mem_Rsub (hx : x ∈ leechQ t) : x ∈ Rsub x t :=
  ⟨hx, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩

theorem t_central {g : G} (hg : g ∈ Xsub x t) : g * t = t * g :=
  Subgroup.mem_centralizer_singleton_iff.1 hg.2

theorem x_central {g : G} (hg : g ∈ Xsub x t) : g * x = x * g :=
  Subgroup.mem_centralizer_singleton_iff.1 hg.1

theorem conj_mem_Rsub (L : LeechSystem t) {g r : G} (hg : g ∈ Xsub x t) (hr : r ∈ Rsub x t) :
    g * r * g⁻¹ ∈ Rsub x t := by
  refine ⟨L.conj_mem' hg.2 hr.1, ?_⟩
  show g * r * g⁻¹ ∈ Subgroup.centralizer ({x} : Set G)
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hxg := Subgroup.mem_centralizer_singleton_iff.1 hg.1
  have hxr := Subgroup.mem_centralizer_singleton_iff.1 hr.2
  calc g * r * g⁻¹ * x = g * r * (g⁻¹ * x) := by group
    _ = g * r * (x * g⁻¹) := by
      congr 1
      calc g⁻¹ * x = g⁻¹ * (x * g) * g⁻¹ := by group
        _ = g⁻¹ * (g * x) * g⁻¹ := by rw [hxg]
        _ = x * g⁻¹ := by group
    _ = g * (r * x) * g⁻¹ := by group
    _ = g * (x * r) * g⁻¹ := by rw [hxr]
    _ = x * (g * r * g⁻¹) := by
      calc g * (x * r) * g⁻¹ = (g * x) * r * g⁻¹ := by group
        _ = (x * g) * r * g⁻¹ := by rw [hxg]
        _ = x * (g * r * g⁻¹) := by group

theorem phiG_mem_stab
    (L : LeechSystem t) (hx : x ∈ L.typeSet 0) {c : G} (hc : c ∈ Xsub x t) :
    phiG L c ∈ co1Stab (L.vec x) := by
  have h := L.image_centralizer_inf_one hx.1 (L.vec_ne_zero_of_mem_typeSet hx)
  have hmem : L.φ ⟨c, hc.2⟩ ∈ L.image (Xsub x t) := L.mem_image.2 ⟨⟨c, hc.2⟩, hc, rfl⟩
  rw [phiG_of_mem L hc.2]
  exact h ▸ hmem

theorem exists_lift
    (L : LeechSystem t) (hx : x ∈ L.typeSet 0) {k : Co1}
    (hk : k ∈ co1Stab (L.vec x)) : ∃ c ∈ Xsub x t, phiG L c = k := by
  have h := L.image_centralizer_inf_one hx.1 (L.vec_ne_zero_of_mem_typeSet hx)
  have hk' : k ∈ L.image (Xsub x t) := h ▸ hk
  obtain ⟨c, hcX, hc⟩ := L.mem_image.1 hk'
  exact ⟨c, hcX, by rw [phiG_of_mem L c.2, hc]⟩

theorem vec_perp_of_mem_Rsub
    (L : LeechSystem t) (hx : x ∈ leechQ t) {r : G}
    (hr : r ∈ Rsub x t) : bil₀ (L.vec r) (L.vec x) = 0 :=
  (L.comm_eq_one_iff hr.1 hx).1
    (commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_centralizer_singleton_iff.1 hr.2))

theorem exists_mem_Rsub_vec
    (L : LeechSystem t) (hx : x ∈ leechQ t) {w : Fin 24 → ZMod 2}
    (hw : bil₀ w (L.vec x) = 0) : ∃ r ∈ Rsub x t, L.vec r = w := by
  obtain ⟨q, hq, rfl⟩ := L.vec_surj w
  exact ⟨q, ⟨hq, Subgroup.mem_centralizer_singleton_iff.2
    (commutatorElement_eq_one_iff_mul_comm.1 ((L.comm_eq_one_iff hq hx).2 hw))⟩, rfl⟩

theorem vec_mul_Rsub (L : LeechSystem t) {r s : G} (hr : r ∈ Rsub x t) (hs : s ∈ Rsub x t) :
    L.vec (r * s) = L.vec r + L.vec s := L.vec_mul r hr.1 s hs.1

structure AutOn (X : Subgroup G) (Ψ : G → G) : Prop where
  mem : ∀ g ∈ X, Ψ g ∈ X
  mul : ∀ g ∈ X, ∀ h ∈ X, Ψ (g * h) = Ψ g * Ψ h
  surj : ∀ y ∈ X, ∃ g ∈ X, Ψ g = y
  inj : ∀ g ∈ X, ∀ h ∈ X, Ψ g = Ψ h → g = h

namespace AutOn

variable {X : Subgroup G} {Ψ : G → G} (h : AutOn X Ψ)

include h

theorem map_one' : Ψ 1 = 1 := by
  have := h.mul 1 X.one_mem 1 X.one_mem
  rw [mul_one] at this
  exact (mul_eq_left.1 this.symm)

theorem map_inv' {g : G} (hg : g ∈ X) : Ψ g⁻¹ = (Ψ g)⁻¹ := by
  have := h.mul g hg g⁻¹ (X.inv_mem hg)
  rw [mul_inv_cancel, h.map_one'] at this
  exact eq_inv_of_mul_eq_one_right this.symm

theorem map_conj {c r : G} (hc : c ∈ X) (hr : r ∈ X) :
    Ψ (c * r * c⁻¹) = Ψ c * Ψ r * (Ψ c)⁻¹ := by
  rw [h.mul _ (X.mul_mem hc hr) _ (X.inv_mem hc), h.mul _ hc _ hr, h.map_inv' hc]

theorem conj {c : G} (hc : c ∈ X) : AutOn X (fun g => c * Ψ g * c⁻¹) where
  mem g hg := X.mul_mem (X.mul_mem hc (h.mem g hg)) (X.inv_mem hc)
  mul g hg k hk := by
    show c * Ψ (g * k) * c⁻¹ = (c * Ψ g * c⁻¹) * (c * Ψ k * c⁻¹)
    rw [h.mul g hg k hk]
    group
  surj y hy := by
    obtain ⟨g, hg, hgy⟩ := h.surj (c⁻¹ * y * c) (X.mul_mem (X.mul_mem (X.inv_mem hc) hy) hc)
    refine ⟨g, hg, ?_⟩
    show c * Ψ g * c⁻¹ = y
    rw [hgy]
    group
  inj g hg k hk e := by
    have e' : Ψ g = Ψ k := by
      have := congrArg (fun z => c⁻¹ * z * c) e
      simpa [mul_assoc] using this
    exact h.inj g hg k hk e'

end AutOn

open scoped Classical in
@[expose] noncomputable def autMap (X : Subgroup G) (ψ : ↥X ≃* ↥X) (g : G) : G :=
  if hg : g ∈ X then ((ψ ⟨g, hg⟩ : ↥X) : G) else 1

theorem autMap_apply {X : Subgroup G} (ψ : ↥X ≃* ↥X) {g : G} (hg : g ∈ X) :
    autMap X ψ g = ((ψ ⟨g, hg⟩ : ↥X) : G) := by
  unfold autMap
  simp [hg]

theorem autOn_autMap (X : Subgroup G) (ψ : ↥X ≃* ↥X) : AutOn X (autMap X ψ) where
  mem g hg := by
    rw [autMap_apply ψ hg]
    exact (ψ ⟨g, hg⟩).2
  mul g hg k hk := by
    rw [autMap_apply ψ (X.mul_mem hg hk), autMap_apply ψ hg, autMap_apply ψ hk]
    have : (⟨g * k, X.mul_mem hg hk⟩ : ↥X) = ⟨g, hg⟩ * ⟨k, hk⟩ := rfl
    rw [this, map_mul]
    rfl
  surj y hy := by
    refine ⟨((ψ.symm ⟨y, hy⟩ : ↥X) : G), (ψ.symm ⟨y, hy⟩).2, ?_⟩
    rw [autMap_apply ψ (ψ.symm ⟨y, hy⟩).2]
    simp
  inj g hg k hk e := by
    rw [autMap_apply ψ hg, autMap_apply ψ hk] at e
    have := ψ.injective (Subtype.ext e)
    exact congrArg Subtype.val this

end CoTwoAutSetup

end CFSG.Monster.GMS
