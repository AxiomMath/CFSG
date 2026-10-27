module

public import CFSG.Quasithin.Background.Module
public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.Quasithin

variable {V : Type*} [CommGroup V]

theorem commV_apply_mem_of_normalizes {Y : Subgroup (MulAut V)} {c : MulAut V}
    (hnorm : ∀ y ∈ Y, c * y * c⁻¹ ∈ Y) {w : V} (hw : w ∈ commV Y) : c w ∈ commV Y := by
  induction hw using Subgroup.closure_induction with
  | mem w hw =>
    obtain ⟨y, hy, v, rfl⟩ := hw
    have h1 : c (y v * v⁻¹) = (c * y * c⁻¹) (c v) * (c v)⁻¹ := by
      simp [MulAut.mul_apply]
    rw [h1]
    exact Subgroup.subset_closure ⟨c * y * c⁻¹, hnorm y hy, c v, rfl⟩
  | one => simp
  | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb
  | inv a _ ha => rw [map_inv]; exact inv_mem ha

theorem commV_apply_mem_of_mem_normalizer {L : Subgroup (MulAut V)} {h : MulAut V}
    (hh : h ∈ Subgroup.normalizer (L : Set (MulAut V))) {u : V} (hu : u ∈ commV L) :
    h u ∈ commV L :=
  commV_apply_mem_of_normalizes (fun x hx => (Subgroup.mem_normalizer_iff.1 hh x).1 hx) hu

theorem commV_apply_mem_of_mem {L : Subgroup (MulAut V)} {h : MulAut V} (hh : h ∈ L) {u : V}
    (hu : u ∈ commV L) : h u ∈ commV L :=
  commV_apply_mem_of_normalizes (fun _ hx => L.mul_mem (L.mul_mem hh hx) (L.inv_mem hh)) hu

theorem fixV_apply_mem_of_mem_normalizer {L : Subgroup (MulAut V)} {h : MulAut V}
    (hh : h ∈ Subgroup.normalizer (L : Set (MulAut V))) {u : V} (hu : u ∈ fixV L) :
    h u ∈ fixV L := by
  intro x hx
  have hx' : h⁻¹ * x * h⁻¹⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 (inv_mem hh) x).1 hx
  rw [inv_inv] at hx'
  have h2 : (h⁻¹ * x * h) u = u := hu _ hx'
  calc x (h u) = h ((h⁻¹ * x * h) u) := by
        rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.apply_inv_self]
    _ = h u := by rw [h2]

theorem commV_apply_mem_of_commute {A B : Subgroup (MulAut V)}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {b : MulAut V} (hb : b ∈ B) {u : V}
    (hu : u ∈ commV A) : b u ∈ commV A :=
  commV_apply_mem_of_normalizes (fun y hy => by rw [← hcomm y hy b hb, mul_inv_cancel_right]; exact hy) hu

theorem commV_map_conj_eq (X : Subgroup (MulAut V)) (g : MulAut V) :
    commV (X.map (MulAut.conj g).toMonoidHom) = (commV X).map g.toMonoidHom := by
  apply le_antisymm
  · refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨_, ⟨h, hh, rfl⟩, v, rfl⟩
    refine ⟨h (g⁻¹ v) * (g⁻¹ v)⁻¹, Subgroup.subset_closure ⟨h, hh, g⁻¹ v, rfl⟩, ?_⟩
    simp [MulAut.conj_apply, MulAut.mul_apply]
  · rw [commV, MonoidHom.map_closure]
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨_, ⟨h, hh, u, rfl⟩, rfl⟩
    refine Subgroup.subset_closure ⟨g * h * g⁻¹, ⟨h, hh, rfl⟩, g u, ?_⟩
    simp [MulAut.mul_apply]

theorem commV_zpowers_conj_eq (x g : MulAut V) :
    commV (Subgroup.zpowers (g * x * g⁻¹)) = (commV (Subgroup.zpowers x)).map g.toMonoidHom := by
  rw [← commV_map_conj_eq, MonoidHom.map_zpowers]
  rfl

theorem commV_le_fixV_of_perfect {L₁ L₂ : Subgroup (MulAut V)}
    (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a) (hperf : Group.IsPerfect ↥L₂)
    {C W₁ W₂ : Subgroup V} (hC : C ≤ fixV L₂) (hW₁ : commV L₁ ≤ W₁) (hW₂ : commV L₂ ≤ W₂)
    (hCW : W₁ ⊓ W₂ ≤ C) : commV L₁ ≤ fixV L₂ := by
  intro u hu
  have hmem : ∀ b ∈ L₂, (b : MulAut V) u * u⁻¹ ∈ C := by
    intro b hb
    refine hCW ⟨hW₁ ?_, hW₂ (Subgroup.subset_closure ⟨b, hb, u, rfl⟩)⟩
    exact mul_mem (commV_apply_mem_of_commute hcomm hb hu) (inv_mem hu)
  let f : ↥L₂ →* V :=
    { toFun := fun b => (b : MulAut V) u * u⁻¹
      map_one' := by simp
      map_mul' := fun b b' => by
        have hc : (b' : MulAut V) u * u⁻¹ ∈ fixV L₂ := hC (hmem b' b'.2)
        have h1 : (b : MulAut V) ((b' : MulAut V) u * u⁻¹) = (b' : MulAut V) u * u⁻¹ := hc b b.2
        rw [map_mul, map_inv] at h1
        have h2 : (b : MulAut V) ((b' : MulAut V) u) =
            (b' : MulAut V) u * u⁻¹ * (b : MulAut V) u := mul_inv_eq_iff_eq_mul.1 h1
        show ((b : MulAut V) * (b' : MulAut V)) u * u⁻¹ = _
        rw [MulAut.mul_apply, h2]
        ac_rfl }
  have hker : ∀ b : ↥L₂, f b = 1 := by
    intro b
    have : b ∈ commutator ↥L₂ := by rw [hperf.commutator_eq_top]; trivial
    exact MonoidHom.mem_ker.1 (Abelianization.commutator_subset_ker f this)
  intro b hb
  have := hker ⟨b, hb⟩
  exact mul_inv_eq_one.1 this

end CFSG.Quasithin
