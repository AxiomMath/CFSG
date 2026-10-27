module

public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.Quasithin.Background.B1Basic

public section

namespace CFSG.Quasithin.H13.U3.GC137

open CFSG.Quasithin CFSG.Open

section Iso

variable {W W' : Type*} [CommGroup W] [CommGroup W'] (φ : W ≃* W')

@[expose] def theta : MulAut W ≃* MulAut W' := MulAut.congr φ

theorem theta_apply (α : MulAut W) (w : W') : theta φ α w = φ (α (φ.symm w)) := rfl

theorem theta_symm_apply (α : MulAut W') (w : W) : (theta φ).symm α w = φ.symm (α (φ w)) := rfl

theorem mem_map_theta {K : Subgroup (MulAut W)} {x : MulAut W'} :
    x ∈ K.map (theta φ).toMonoidHom ↔ (theta φ).symm x ∈ K :=
  Subgroup.mem_map_equiv

theorem card_map_theta (K : Subgroup (MulAut W)) :
    Nat.card (K.map (theta φ).toMonoidHom) = Nat.card K :=
  Nat.card_congr (K.equivMapOfInjective _ (theta φ).injective).toEquiv.symm

theorem map_theta_le_iff {K K' : Subgroup (MulAut W)} :
    K.map (theta φ).toMonoidHom ≤ K'.map (theta φ).toMonoidHom ↔ K ≤ K' :=
  Subgroup.map_le_map_iff_of_injective (theta φ).injective

theorem fixV_map (K : Subgroup (MulAut W)) :
    fixV (K.map (theta φ).toMonoidHom) = (fixV K).map φ.toMonoidHom := by
  ext w'
  rw [Subgroup.mem_map_equiv]
  constructor
  · intro h x hx
    have h1 := h (theta φ x) ⟨x, hx, rfl⟩
    rw [theta_apply] at h1
    have h2 := congrArg φ.symm h1
    simpa using h2
  · intro h x' hx'
    obtain ⟨x, hx, rfl⟩ := hx'
    have h1 := h x hx
    show φ (x (φ.symm w')) = w'
    simpa using congrArg φ h1

theorem card_fixV_map (K : Subgroup (MulAut W)) :
    Nat.card (fixV (K.map (theta φ).toMonoidHom)) = Nat.card (fixV K) := by
  rw [fixV_map]
  exact Nat.card_congr ((fixV K).equivMapOfInjective _ φ.injective).toEquiv.symm

theorem rkIdx_fixV_map (K : Subgroup (MulAut W)) :
    rkIdx (fixV (K.map (theta φ).toMonoidHom)) = rkIdx (fixV K) := by
  rw [fixV_map]
  unfold rkIdx
  rw [Subgroup.index_map_of_bijective ⟨φ.injective, φ.surjective⟩]

theorem rk_map_theta (K : Subgroup (MulAut W)) :
    rk (K.map (theta φ).toMonoidHom) = rk K := by
  unfold rk
  rw [card_map_theta]

theorem rAV_map (A : Subgroup (MulAut W)) : rAV (A.map (theta φ).toMonoidHom) = rAV A := by
  unfold rAV
  rw [rkIdx_fixV_map, rk_map_theta]

theorem isFFStarOffender_map_iff {X A : Subgroup (MulAut W)} :
    IsFFStarOffender (X.map (theta φ).toMonoidHom) (A.map (theta φ).toMonoidHom) ↔
      IsFFStarOffender X A :=
  isFFStarOffender_map_congr_equiv_iff φ

theorem isStrongFFStarOffender_map_iff {X A : Subgroup (MulAut W)} :
    IsStrongFFStarOffender (X.map (theta φ).toMonoidHom) (A.map (theta φ).toMonoidHom) ↔
      IsStrongFFStarOffender X A := by
  unfold IsStrongFFStarOffender
  rw [isFFStarOffender_map_iff, rAV_map]

theorem conjAut_map (g : MulAut W) (Y : Subgroup (MulAut W)) :
    B1.conjAut (theta φ g) (Y.map (theta φ).toMonoidHom) =
      (B1.conjAut g Y).map (theta φ).toMonoidHom := by
  ext x
  rw [B1.mem_conjAut, mem_map_theta, mem_map_theta, B1.mem_conjAut]
  simp only [map_mul, map_inv, MulEquiv.symm_apply_apply]

theorem isSylowTwoOf_map_theta_iff {A B : Subgroup (MulAut W)} :
    CFSG.QuasithinUnique.IsSylowTwoOf (A.map (theta φ).toMonoidHom)
      (B.map (theta φ).toMonoidHom) ↔ CFSG.QuasithinUnique.IsSylowTwoOf A B := by
  have hidx := Subgroup.relIndex_map_map_of_injective (f := (theta φ).toMonoidHom) A B
    (theta φ).injective
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨(map_theta_le_iff φ).1 h1, ?_, fun h => h3 ?_⟩
    · exact h2.of_equiv (A.equivMapOfInjective _ (theta φ).injective).symm
    · show 2 ∣ (A.map (theta φ).toMonoidHom).relIndex (B.map (theta φ).toMonoidHom)
      rw [hidx]
      exact h
  · rintro ⟨h1, h2, h3⟩
    refine ⟨Subgroup.map_mono h1, ?_, fun h => h3 ?_⟩
    · exact h2.of_equiv (A.equivMapOfInjective _ (theta φ).injective)
    · show 2 ∣ A.relIndex B
      rw [← hidx]
      exact h

end Iso

end CFSG.Quasithin.H13.U3.GC137
