module

public import CFSG.Monster.GMS.S4AssemblyIso
public import CFSG.Monster.GMS.Orbits
public import CFSG.Monster.GMS.Facts.Interfaces
public import CFSG.Monster.GMS.S35
public import Certificates.Certificate3024

public section

namespace CFSG.Monster.GMS.S4Family

open CFSG.Monster.GMS.S4Assembly

local notation "C[" x "]" => Subgroup.centralizer ({x} : Set _)

section Generic

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

theorem isIsoOn_comp {f : G → G'} {g : G' → G''} {H : Subgroup G} {H' : Subgroup G'}
    {H'' : Subgroup G''} (hf : IsIsoOn f H H') (hg : IsIsoOn g H' H'') :
    IsIsoOn (g ∘ f) H H'' where
  map_mem x hx := hg.map_mem _ (hf.map_mem x hx)
  map_mul x hx y hy := by
    simp only [Function.comp_apply]
    rw [hf.map_mul x hx y hy, hg.map_mul _ (hf.map_mem x hx) _ (hf.map_mem y hy)]
  injOn x hx y hy hxy :=
    hf.injOn hx hy (hg.injOn (hf.map_mem x hx) (hf.map_mem y hy) hxy)
  surjOn z hz := by
    obtain ⟨y, hy, rfl⟩ := hg.surjOn z hz
    obtain ⟨x, hx, rfl⟩ := hf.surjOn y hy
    exact ⟨x, hx, rfl⟩

theorem isIsoOn_congr {f₁ f₂ : G → G'} {H : Subgroup G} {H' : Subgroup G'}
    (h : IsIsoOn f₁ H H') (he : ∀ x ∈ H, f₂ x = f₁ x) : IsIsoOn f₂ H H' where
  map_mem x hx := by rw [he x hx]; exact h.map_mem x hx
  map_mul x hx y hy := by
    rw [he x hx, he y hy, he (x * y) (H.mul_mem hx hy)]
    exact h.map_mul x hx y hy
  injOn x hx y hy hxy := h.injOn hx hy (by rw [← he x hx, ← he y hy]; exact hxy)
  surjOn z hz := by
    obtain ⟨x, hx, hxz⟩ := h.surjOn z hz
    exact ⟨x, hx, by rw [he x hx]; exact hxz⟩

theorem isIsoOn_conj_of_iff (c : G) {H H' : Subgroup G}
    (hH : ∀ x, x ∈ H ↔ c * x * c⁻¹ ∈ H') : IsIsoOn (fun x => c * x * c⁻¹) H H' where
  map_mem x hx := (hH x).1 hx
  map_mul x _ y _ := by group
  injOn x _ y _ hxy := by
    have := mul_left_cancel (mul_right_cancel hxy)
    exact this
  surjOn z hz := ⟨c⁻¹ * z * c, (hH _).2 (by rwa [show c * (c⁻¹ * z * c) * c⁻¹ = z by group]),
    by group⟩

theorem isIsoOn_conj_inv_of_iff (c : G) {H H' : Subgroup G}
    (hH : ∀ x, x ∈ H ↔ c⁻¹ * x * c ∈ H') : IsIsoOn (fun x => c⁻¹ * x * c) H H' :=
  isIsoOn_congr (isIsoOn_conj_of_iff c⁻¹ fun x => by rw [inv_inv]; exact hH x)
    fun x _ => by rw [inv_inv]

theorem isIsoOn_conj_self {c : G} {H : Subgroup G} (hc : c ∈ H) :
    IsIsoOn (fun x => c * x * c⁻¹) H H :=
  isIsoOn_conj_of_iff c fun x =>
    ⟨fun hx => H.mul_mem (H.mul_mem hc hx) (H.inv_mem hc), fun hx => by
      have := H.mul_mem (H.mul_mem (H.inv_mem hc) hx) hc
      rwa [show c⁻¹ * (c * x * c⁻¹) * c = x by group] at this⟩

theorem mem_centralizer_of_conj_eq {x k : G} (h : k * x * k⁻¹ = x) : k ∈ C[x] :=
  Subgroup.mem_centralizer_singleton_iff.mpr (by
    calc k * x = k * x * k⁻¹ * k := by group
      _ = x * k := by rw [h])

theorem conj_mem_centralizer_iff (c x y : G) :
    c * x * c⁻¹ ∈ C[c * y * c⁻¹] ↔ x ∈ C[y] := by
  have := mem_centralizer_singleton_map_iff (MulAut.conj c) y x
  simpa only [MulAut.conj_apply] using this

theorem isIsoOn_conj_centralizer (c y : G) :
    IsIsoOn (fun x => c * x * c⁻¹) C[y] C[c * y * c⁻¹] :=
  isIsoOn_conj_of_iff c fun x => (conj_mem_centralizer_iff c x y).symm

theorem conj_inv_mem_centralizer_iff (c x y : G) :
    c⁻¹ * x * c ∈ C[c⁻¹ * y * c] ↔ x ∈ C[y] := by
  simpa only [inv_inv] using conj_mem_centralizer_iff c⁻¹ x y

theorem isIsoOn_conj_inv_centralizer (c y : G) :
    IsIsoOn (fun x => c⁻¹ * x * c) C[y] C[c⁻¹ * y * c] :=
  isIsoOn_conj_inv_of_iff c fun x => (conj_inv_mem_centralizer_iff c x y).symm

theorem isConj_conj_iff (c x y : G) : IsConj x (c * y * c⁻¹) ↔ IsConj x y :=
  ⟨fun h => h.trans (isConj_iff.mpr ⟨c⁻¹, by group⟩),
    fun h => h.trans (isConj_iff.mpr ⟨c, rfl⟩)⟩

theorem isConj_conj_inv_iff (c x y : G) : IsConj x (c⁻¹ * y * c) ↔ IsConj x y := by
  simpa only [inv_inv] using isConj_conj_iff c⁻¹ x y

theorem isIsoOn_inf_centralizer {f : G → G'} {H : Subgroup G} {H' : Subgroup G'}
    (h : IsIsoOn f H H') {x : G} (hx : x ∈ H) :
    IsIsoOn f (H ⊓ C[x]) (H' ⊓ C[f x]) where
  map_mem y hy := ⟨h.map_mem y hy.1, (iso_mem_centralizer_iff h hy.1 hx).2 hy.2⟩
  map_mul y hy z hz := h.map_mul y hy.1 z hz.1
  injOn y hy z hz e := h.injOn hy.1 hz.1 e
  surjOn w hw := by
    obtain ⟨y, hy, rfl⟩ := h.surjOn w hw.1
    exact ⟨y, ⟨hy, (iso_mem_centralizer_iff h hy hx).1 hw.2⟩, rfl⟩

theorem isIsoOn_centralizer_inf {f : G → G'} {H : Subgroup G} {H' : Subgroup G'}
    (h : IsIsoOn f H H') {x : G} (hx : x ∈ H) :
    IsIsoOn f (C[x] ⊓ H) (C[f x] ⊓ H') := by
  rw [inf_comm, inf_comm C[f x]]
  exact isIsoOn_inf_centralizer h hx

theorem isIsoOn_card_eq {f : G → G'} {H : Subgroup G} {H' : Subgroup G'} (h : IsIsoOn f H H') :
    Nat.card H = Nat.card H' :=
  Nat.card_congr (Equiv.ofBijective (fun x : H => (⟨f x, h.map_mem x x.2⟩ : H'))
    ⟨fun x y hxy => Subtype.ext (h.injOn x.2 y.2 (congrArg Subtype.val hxy)), fun y => by
      obtain ⟨x, hx, hxy⟩ := h.surjOn y y.2
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩⟩)

@[expose] noncomputable def isoHom {f : G → G'} {H : Subgroup G} {H' : Subgroup G'}
    (h : IsIsoOn f H H') : H →* H' where
  toFun x := ⟨f x, h.map_mem x x.2⟩
  map_one' := Subtype.ext (iso_map_one h)
  map_mul' x y := Subtype.ext (h.map_mul x x.2 y y.2)

@[expose] noncomputable def isoEquiv {f : G → G'} {H : Subgroup G} {H' : Subgroup G'}
    (h : IsIsoOn f H H') : H ≃* H' :=
  MulEquiv.ofBijective (isoHom h)
    ⟨fun x y hxy => Subtype.ext (h.injOn x.2 y.2 (congrArg Subtype.val hxy)), fun y => by
      obtain ⟨x, hx, hxy⟩ := h.surjOn y y.2
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩⟩

@[expose] noncomputable def extendFun {H : Subgroup G} {H' : Subgroup G'} (φ : H ≃* H') : G → G' :=
  by classical exact fun g => if hg : g ∈ H then (φ ⟨g, hg⟩ : G') else 1

theorem extendFun_apply {H : Subgroup G} {H' : Subgroup G'} (φ : H ≃* H') {g : G} (hg : g ∈ H) :
    extendFun φ g = φ ⟨g, hg⟩ := by
  simp [extendFun, hg]

theorem isIsoOn_extendFun {H : Subgroup G} {H' : Subgroup G'} (φ : H ≃* H') :
    IsIsoOn (extendFun φ) H H' where
  map_mem x hx := by rw [extendFun_apply φ hx]; exact (φ ⟨x, hx⟩).2
  map_mul x hx y hy := by
    rw [extendFun_apply φ hx, extendFun_apply φ hy, extendFun_apply φ (H.mul_mem hx hy)]
    exact congrArg Subtype.val (map_mul φ ⟨x, hx⟩ ⟨y, hy⟩)
  injOn x hx y hy hxy := by
    rw [extendFun_apply φ hx, extendFun_apply φ hy] at hxy
    exact congrArg Subtype.val (φ.injective (Subtype.ext hxy))
  surjOn z hz := by
    refine ⟨(φ.symm ⟨z, hz⟩ : G), (φ.symm ⟨z, hz⟩).2, ?_⟩
    rw [extendFun_apply φ (φ.symm ⟨z, hz⟩).2]
    exact congrArg Subtype.val (φ.apply_symm_apply ⟨z, hz⟩)

end Generic

end CFSG.Monster.GMS.S4Family
