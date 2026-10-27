module

public import CFSG.Monster.Existence.Census.Rigid
public import CFSG.Monster.AxisCount.HSIdentAxis
public import CFSG.Monster.Existence.TwoB

public section

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated
  CFSG.Monster.B CFSG.Monster.B.Short CFSG.Monster.AxisCount CFSG.Monster.Existence.Census

theorem commute_tAxis_of_fix {g : SpaceB ≃ₗ[ℚ] SpaceB} (hg : g ∈ AutO) {a : SpaceB}
    (h : g a = a) (u : SpaceB) : g (tAxis a u) = tAxis a (g u) := by
  have := tAxis_AutO hg a (g u)
  rw [h, LinearEquiv.symm_apply_apply] at this
  exact this.symm

theorem commute_of_fix_of_eq_tAxis {g t : SpaceB ≃ₗ[ℚ] SpaceB} (hg : g ∈ AutO) {a : SpaceB}
    (ht : (t : SpaceB →ₗ[ℚ] SpaceB) = tAxis a) (h : g a = a) : g * t = t * g := by
  refine LinearEquiv.ext fun u => ?_
  have e : ∀ v, t v = tAxis a v := fun v => LinearMap.congr_fun ht v
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, e, e]
  exact commute_tAxis_of_fix hg h u

theorem mem_Gvis_of_fix_axes {g : SpaceB ≃ₗ[ℚ] SpaceB} (hg : g ∈ AutO) (h₁ : g aStar = aStar)
    (h₂ : g aStarMinus = aStarMinus) : g ∈ Gvis := by
  have c₁ : g * tStar = tStar * g := commute_of_fix_of_eq_tAxis hg tAxis_aStar.symm h₁
  have c₂ : g * (tStar * xmat) = tStar * xmat * g := by
    have e : ((tStar * xmat : SpaceB ≃ₗ[ℚ] SpaceB) : SpaceB →ₗ[ℚ] SpaceB) = tAxis aStarMinus := by
      rw [tAxis_aStarMinus, rhoEquiv_zQ_mul_rStar]
    exact commute_of_fix_of_eq_tAxis hg e h₂
  have c₃ : g * xmat = xmat * g := by
    have h : Commute g (tStar⁻¹ * (tStar * xmat)) :=
      (Commute.inv_right c₁).mul_right c₂
    rw [inv_mul_cancel_left] at h
    exact h.eq
  rw [← map_cent_xGriess]
  refine ⟨⟨g, hg⟩, ?_, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  exact Subtype.ext c₃

theorem eq_one_of_fix_axes
    {g : SpaceB ≃ₗ[ℚ] SpaceB} (hg : g ∈ AutO) (h₁ : g aStar = aStar)
    (h₂ : g aStarMinus = aStarMinus)
    (h₃ : ∀ k ∈ rigidKeys, g (wvec k.1 k.2.1 k.2.2) = wvec k.1 k.2.1 k.2.2) : g = 1 :=
  eq_of_fix_rigidKeys (mem_Gvis_of_fix_axes hg h₁ h₂) (one_mem Gvis) h₃

theorem eq_of_fix_axes
    {a b : SpaceB ≃ₗ[ℚ] SpaceB} (ha : a ∈ AutO) (hb : b ∈ AutO)
    (h₁ : a aStar = b aStar) (h₂ : a aStarMinus = b aStarMinus)
    (h₃ : ∀ k ∈ rigidKeys, a (wvec k.1 k.2.1 k.2.2) = b (wvec k.1 k.2.1 k.2.2)) : a = b := by
  have hfix : ∀ v, a v = b v → (b⁻¹ * a) v = v := fun v hv => by
    rw [LinearEquiv.mul_apply, hv]
    exact b.symm_apply_apply v
  have h1 : b⁻¹ * a = 1 :=
    eq_one_of_fix_axes (mul_mem (inv_mem hb) ha) (hfix _ h₁) (hfix _ h₂)
      fun k hk => hfix _ (h₃ k hk)
  exact (inv_mul_eq_one.1 h1).symm

@[expose, noinline] def checkAxRigid (c : Native.Ctx) (w₁ w₂ : List Native.Gen) : Bool :=
  (w₁ ++ w₂).all (fun g => g.validB) &&
    (Native.evalWordC c w₁ HS.axisP).eqv (Native.evalWordC c w₂ HS.axisP) &&
    (Native.evalWordC c w₁ HS.axisM).eqv (Native.evalWordC c w₂ HS.axisM) &&
    rigidKeys.all fun k =>
      (Native.evalWordC c w₁ (rigidDVec k)).eqv (Native.evalWordC c w₂ (rigidDVec k))

theorem wordLin_eq_of_checkAxRigid
    {w₁ w₂ : List Native.Gen}
    (h : checkAxRigid (Native.mkCtx ()) w₁ w₂ = true) : wordLin w₁ = wordLin w₂ := by
  unfold checkAxRigid at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨hv, hP⟩, hM⟩, hK⟩ := h
  have hw₁ : ∀ g ∈ w₁, g.validB = true := fun g hg =>
    List.all_eq_true.1 hv g (List.mem_append_left _ hg)
  have hw₂ : ∀ g ∈ w₂, g.validB = true := fun g hg =>
    List.all_eq_true.1 hv g (List.mem_append_right _ hg)
  have key : ∀ v : Native.DVec,
      (Native.evalWordC (Native.mkCtx ()) w₁ v).eqv (Native.evalWordC (Native.mkCtx ()) w₂ v) =
        true → wordLin w₁ (interp v) = wordLin w₂ (interp v) := fun v hv' => by
    have := eqv_sound hv'
    rwa [evalWordC_sound w₁ hw₁, evalWordC_sound w₂ hw₂] at this
  refine eq_of_fix_axes (Gmat_le_AutO (wordLin_mem_Gmat w₁)) (Gmat_le_AutO (wordLin_mem_Gmat w₂))
    ?_ ?_ fun k hk => ?_
  · have := key _ hP
    rwa [HS.interp_axisP] at this
  · have := key _ hM
    rwa [HS.interp_axisM] at this
  · have := key _ (List.all_eq_true.1 hK k hk)
    rwa [interp_rigidDVec] at this

theorem wordLin_eq_one_of_checkAxRigid
    {w : List Native.Gen}
    (h : checkAxRigid (Native.mkCtx ()) w [] = true) : wordLin w = 1 :=
  wordLin_eq_of_checkAxRigid h

end CFSG.Monster.Existence
