module

public import CFSG.Quasithin.Background.D2Basic

public section

namespace CFSG.Quasithin.StabLat

variable {V W : Type*} [CommGroup V] [CommGroup W]

theorem mulAutCongr_symm_apply (e : V ≃* W) (φ : MulAut W) :
    (MulAut.congr e).symm φ = MulAut.congr e.symm φ := by
  ext
  rfl

theorem mem_stabSub_map_equiv_iff (e : V ≃* W) (U : Subgroup V) (φ : MulAut W) :
    φ ∈ stabSub (U.map e.toMonoidHom) ↔ MulAut.congr e.symm φ ∈ stabSub U := by
  constructor
  · intro h u
    have h1 := h (e u)
    rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply] at h1
    exact h1
  · intro h v
    have h1 := h (e.symm v)
    rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv]
    simpa [MulAut.congr_apply] using h1

theorem stabSub_map_equiv (e : V ≃* W) (U : Subgroup V) :
    stabSub (U.map e.toMonoidHom) = (stabSub U).map (MulAut.congr e).toMonoidHom := by
  ext φ
  rw [mem_stabSub_map_equiv_iff, Subgroup.mem_map_equiv, mulAutCongr_symm_apply]

theorem mem_centSub_map_equiv_iff (e : V ≃* W) (U : Subgroup V) (φ : MulAut W) :
    φ ∈ centSub (U.map e.toMonoidHom) ↔ MulAut.congr e.symm φ ∈ centSub U := by
  constructor
  · intro h u hu
    have h1 := h (e u) ⟨u, hu, rfl⟩
    simp [MulAut.congr_apply, h1]
  · rintro h _ ⟨u, hu, rfl⟩
    have h1 := h u hu
    simp only [MulAut.congr_apply, MulEquiv.symm_symm] at h1
    have h2 := congrArg e h1
    simpa using h2

theorem centSub_map_equiv (e : V ≃* W) (U : Subgroup V) :
    centSub (U.map e.toMonoidHom) = (centSub U).map (MulAut.congr e).toMonoidHom := by
  ext φ
  rw [mem_centSub_map_equiv_iff, Subgroup.mem_map_equiv, mulAutCongr_symm_apply]

end CFSG.Quasithin.StabLat
