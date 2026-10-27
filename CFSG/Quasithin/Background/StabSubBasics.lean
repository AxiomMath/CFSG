module

public import CFSG.Quasithin.Background.D2Basic

public section

namespace CFSG.Quasithin

namespace StabLat

variable {V : Type*} [CommGroup V]

theorem mem_stabSub_iff_map {g : MulAut V} {J : Subgroup V} :
    g ∈ stabSub J ↔ J.map g.toMonoidHom = J := by
  constructor
  · intro h
    ext u
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact (h w).mpr hw
    · intro hu
      refine ⟨g.symm u, ?_, by simp⟩
      have := (h (g.symm u)).mp (by simpa using hu)
      exact this
  · intro h u
    have hm : ∀ v, v ∈ J ↔ v ∈ J.map g.toMonoidHom := fun v => by rw [h]
    constructor
    · intro hgu
      obtain ⟨w, hw, hwu⟩ := (hm (g u)).mp hgu
      exact (g.injective hwu) ▸ hw
    · intro hu
      exact (hm (g u)).mpr (Subgroup.mem_map_of_mem _ hu)

theorem mem_stabSub_commSub {X : Subgroup (MulAut V)} {Y : Subgroup V} {g : MulAut V}
    (hgY : g ∈ stabSub Y) (hgX : g ∈ Subgroup.normalizer (X : Set (MulAut V))) :
    g ∈ stabSub (commSub Y X) := by
  have key : ∀ g : MulAut V, g ∈ stabSub Y → g ∈ Subgroup.normalizer (X : Set (MulAut V)) →
      ∀ c ∈ commSub Y X, g c ∈ commSub Y X := by
    intro g hgY hgX c hc
    refine Subgroup.closure_induction (p := fun c _ => g c ∈ commSub Y X) ?_ ?_ ?_ ?_ hc
    · rintro _ ⟨x, hx, w, hw, rfl⟩
      have h1 : g (x w * w⁻¹) = (g * x * g⁻¹) (g w) * (g w)⁻¹ := by
        simp [MulAut.mul_apply]
      rw [h1]
      exact Subgroup.subset_closure ⟨g * x * g⁻¹, (Subgroup.mem_normalizer_iff.mp hgX x).mp hx,
        g w, (hgY w).2 hw, rfl⟩
    · simp
    · intro a b _ _ ha hb
      rw [map_mul]
      exact (commSub Y X).mul_mem ha hb
    · intro a _ ha
      rw [map_inv]
      exact (commSub Y X).inv_mem ha
  intro u
  refine ⟨fun h => ?_, fun h => key g hgY hgX u h⟩
  have := key g⁻¹ ((stabSub Y).inv_mem hgY) ((Subgroup.normalizer (X : Set (MulAut V))).inv_mem hgX)
    _ h
  simpa using this

theorem mem_stabSub_of_map_eq {U : Subgroup V} {g : MulAut V} (h : U.map g.toMonoidHom = U) :
    g ∈ stabSub U :=
  mem_stabSub_iff_map.2 h

theorem isElemAbelian2_zpowers {a : MulAut V} (ha : a ^ 2 = 1) :
    IsElemAbelian2 (Subgroup.zpowers a) := by
  refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
  · obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact ((Commute.refl a).zpow_zpow m k).eq
  · obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
    have : a ^ (2 : ℤ) = 1 := by rw [zpow_two, ← pow_two]; exact ha
    simp [this]

end StabLat

end CFSG.Quasithin
