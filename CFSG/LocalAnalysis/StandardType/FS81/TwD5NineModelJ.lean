module

public import CFSG.LocalAnalysis.StandardType.FS81.TwD5NineModelAux
public import CFSG.LocalAnalysis.StandardType.FS81.OrthInner

public section

namespace CFSG.StandardType.FrameRoute.FS81

open QuadraticMap Module CFSG.Open CFSG.Assembly CFSG.SignalizerFunctorTheorem
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC CFSG.RankThree.OrthogonalInvolutions
  CFSG.LieType.SeitzGeneration CFSG.LieType.SeitzGeneration.OrthBlk
  CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.Classical2 (orthDerived)

theorem inf_centralizer_transport {G X : Type*} [Group G] [Group X] {J : Subgroup G}
    {M : Subgroup X} (Ψ : ↥J ≃* ↥M) {t : G} {r : X}
    (hΨ : ∀ g : ↥J, (g : G) * t = t * (g : G) ↔ (Ψ g : X) * r = r * (Ψ g : X)) :
    Nonempty (↥(J ⊓ Subgroup.centralizer ({t} : Set G)) ≃*
        ↥(M ⊓ Subgroup.centralizer ({r} : Set X))) ∧
      (M ⊓ Subgroup.centralizer ((M ⊓ Subgroup.centralizer ({r} : Set X) : Subgroup X) :
          Set X) = ⊥ →
        J ⊓ Subgroup.centralizer ((J ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) :
          Set G) = ⊥) := by
  classical
  let DJ : Subgroup G := J ⊓ Subgroup.centralizer ({t} : Set G)
  let DM : Subgroup X := M ⊓ Subgroup.centralizer ({r} : Set X)
  have hmemM : ∀ g : ↥DJ,
      (Ψ ⟨g, g.2.1⟩ : X) * r = r * (Ψ ⟨g, g.2.1⟩ : X) := fun g =>
    (hΨ ⟨g, g.2.1⟩).mp (Subgroup.mem_centralizer_singleton_iff.mp g.2.2)
  have hmemJ : ∀ y : ↥DM,
      (Ψ.symm ⟨y, y.2.1⟩ : G) * t = t * (Ψ.symm ⟨y, y.2.1⟩ : G) := by
    intro y
    refine (hΨ (Ψ.symm ⟨y, y.2.1⟩)).mpr ?_
    rw [MulEquiv.apply_symm_apply]
    exact Subgroup.mem_centralizer_singleton_iff.mp y.2.2
  let F : ↥DJ ≃* ↥DM :=
    { toFun := fun g =>
        ⟨Ψ ⟨g, g.2.1⟩, Subgroup.mem_inf.mpr ⟨(Ψ ⟨g, g.2.1⟩).2,
          Subgroup.mem_centralizer_singleton_iff.mpr (hmemM g)⟩⟩
      invFun := fun y =>
        ⟨Ψ.symm ⟨y, y.2.1⟩, Subgroup.mem_inf.mpr ⟨(Ψ.symm ⟨y, y.2.1⟩).2,
          Subgroup.mem_centralizer_singleton_iff.mpr (hmemJ y)⟩⟩
      left_inv := by
        intro g
        apply Subtype.ext
        simp
      right_inv := by
        intro y
        apply Subtype.ext
        simp
      map_mul' := by
        intro g h
        apply Subtype.ext
        simpa using congrArg Subtype.val (map_mul Ψ ⟨g, g.2.1⟩ ⟨h, h.2.1⟩) }
  refine ⟨⟨F⟩, ?_⟩
  intro hM
  rw [Subgroup.eq_bot_iff_forall]
  intro g hg
  have hyC : (Ψ ⟨g, hg.1⟩ : X) ∈ Subgroup.centralizer (DM : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hzJ : (Ψ.symm ⟨z, hz.1⟩ : G) ∈ DJ := by
      refine Subgroup.mem_inf.mpr ⟨(Ψ.symm ⟨z, hz.1⟩).2, ?_⟩
      refine Subgroup.mem_centralizer_singleton_iff.mpr
        ((hΨ (Ψ.symm ⟨z, hz.1⟩)).mpr ?_)
      rw [MulEquiv.apply_symm_apply]
      exact Subgroup.mem_centralizer_singleton_iff.mp hz.2
    have hcommJ : (⟨(Ψ.symm ⟨z, hz.1⟩ : G), hzJ.1⟩ : ↥J) * ⟨g, hg.1⟩ =
        ⟨g, hg.1⟩ * ⟨(Ψ.symm ⟨z, hz.1⟩ : G), hzJ.1⟩ :=
      Subtype.ext (Iff.mp (Subgroup.mem_centralizer_iff) hg.2 _ hzJ)
    have hcommM := congrArg Ψ hcommJ
    have hcommX : z * (Ψ ⟨g, hg.1⟩ : X) = (Ψ ⟨g, hg.1⟩ : X) * z := by
      have := congrArg (fun w : ↥M => (w : X)) hcommM
      simpa using this
    exact hcommX
  let y : ↥(M ⊓ Subgroup.centralizer (DM : Set X)) :=
    ⟨Ψ ⟨g, hg.1⟩, Subgroup.mem_inf.mpr ⟨(Ψ ⟨g, hg.1⟩).2, hyC⟩⟩
  have hy1 : (y : X) = 1 :=
    Iff.mp (Subgroup.eq_bot_iff_forall (M ⊓ Subgroup.centralizer (DM : Set X))) hM y y.2
  have hPsi1 : (Ψ ⟨g, hg.1⟩ : ↥M) = 1 := by
    apply Subtype.ext
    simpa [y] using hy1
  have hg1 : (⟨g, hg.1⟩ : ↥J) = 1 := Ψ.injective (by simpa using hPsi1)
  exact congrArg (fun z : ↥J => (z : G)) hg1

theorem commute_reflect_iff_of_restrict {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} {U : Submodule (ZMod 2) V} (hU : IsCompl U (perpOf Q U))
    {g : V ≃ₗ[ZMod 2] V} {gW : perpOf Q U ≃ₗ[ZMod 2] perpOf Q U}
    (hgW : ∀ w : perpOf Q U, ((gW w : perpOf Q U) : V) = g (w : V)) (hgU : ∀ u ∈ U, g u = u)
    {u : V} (hu : u ∈ perpOf Q U) :
    g * reflect Q u = reflect Q u * g ↔
      gW * reflect (Q.restrict (perpOf Q U)) ⟨u, hu⟩ =
        reflect (Q.restrict (perpOf Q U)) ⟨u, hu⟩ * gW := by
  classical
  let W : Submodule (ZMod 2) V := perpOf Q U
  have hUW : IsCompl U W := hU
  by_cases hu0 : Q u = 0
  · have hWu : (Q.restrict W) ⟨u, hu⟩ = 0 := by simpa [W] using hu0
    rw [reflect_of_map_eq_zero (Q := Q) hu0,
      reflect_of_map_eq_zero (Q := Q.restrict W) hWu]
    simp
  · have hWu : (Q.restrict W) ⟨u, hu⟩ ≠ 0 := by simpa [W] using hu0
    have hfixU : ∀ v ∈ U, reflect Q u v = v := by
      intro v hv
      apply reflect_apply_of_polar_eq_zero
      have hup : u ∈ perp Q U := hu
      have hz := mem_perp.mp hup v hv
      rwa [polar_comm] at hz
    have hmapW : ∀ w ∈ W, reflect Q u w ∈ W := by
      intro w hw
      rw [mem_perp]
      intro v hv
      have hO := reflect_mem_orthogonalGroup Q u
      have h1 := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hO v w
      rw [hfixU v hv] at h1
      rw [h1]
      exact mem_perp.mp hw v hv
    have hres : ∀ w : W,
        ((reflect (Q.restrict W) ⟨u, hu⟩ w : W) : V) = reflect Q u (w : V) := by
      intro w
      by_cases h : Q u = 0
      · rw [reflect_of_map_eq_zero (Q := Q) h,
          reflect_of_map_eq_zero (Q := Q.restrict W) (by simpa [W] using h)]
        rfl
      · rw [reflect_apply (Q := Q) h,
          reflect_apply (Q := Q.restrict W) (by simpa [W] using h)]
        simp only [Submodule.coe_sub, Submodule.coe_smul]
        congr 1
    constructor
    · intro hgr
      apply LinearEquiv.ext
      intro w
      apply Subtype.ext
      have h := congrArg (fun e : V ≃ₗ[ZMod 2] V => e (w : V)) hgr
      have h' : g (reflect Q u (w : V)) = reflect Q u (g (w : V)) := by
        simpa only [LinearEquiv.mul_apply] using h
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
      calc ((gW (reflect (Q.restrict W) ⟨u, hu⟩ w) : W) : V)
          = g ((reflect (Q.restrict W) ⟨u, hu⟩ w : W) : V) := hgW _
        _ = g (reflect Q u (w : V)) := by rw [hres w]
        _ = reflect Q u (g (w : V)) := h'
        _ = ((reflect (Q.restrict W) ⟨u, hu⟩ (gW w) : W) : V) := by
              rw [hres (gW w), hgW w]
    · intro hWgr
      apply LinearEquiv.toLinearMap_injective
      apply LinearMap.ext_on_codisjoint hUW.codisjoint
      · intro v hv
        change (g * reflect Q u) v = (reflect Q u * g) v
        rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply,
          hfixU v hv, hgU v hv, hfixU v hv]
      · intro w hw
        change (g * reflect Q u) w = (reflect Q u * g) w
        have hcommW := congrArg (fun e : W ≃ₗ[ZMod 2] W => e ⟨w, hw⟩) hWgr
        have h := congrArg (fun z : W => (z : V)) hcommW
        rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply] at h
        rw [hgW (reflect (Q.restrict W) ⟨u, hu⟩ ⟨w, hw⟩),
          hres ⟨w, hw⟩,
          hres (gW ⟨w, hw⟩),
          hgW ⟨w, hw⟩] at h
        rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
        exact h

end CFSG.StandardType.FrameRoute.FS81

end
