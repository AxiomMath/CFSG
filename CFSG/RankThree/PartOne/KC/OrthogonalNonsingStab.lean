module

public import CFSG.RankThree.PartOne.KC.OrthogonalSupportedScalarDefs
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CRankWitt
import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.RankThree.PartOne.KC.OrthogonalSupportedScalarCentralizer

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Module QuadraticMap CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal
  CFSG.RankThree.OrthogonalInvolutions

variable {K V : Type} [Field K] [CharP K 2] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem reflect_mul_reflect_mem_supportedDerived [Finite K] {S : Submodule K V}
    (hS : (polarBilin (Q.comp S.subtype)).Nondegenerate) {w y : V} (hw : w ∈ S) (hy : y ∈ S)
    (hQw : Q w ≠ 0) (hQy : Q y ≠ 0) : reflect Q w * reflect Q y ∈ supportedDerived Q S := by
  refine mem_supportedDerived.mpr ⟨?_, reflect (Q.comp S.subtype) ⟨w, hw⟩ *
      reflect (Q.comp S.subtype) ⟨y, hy⟩,
    CFSG.LocalAnalysis.GLTheoremA.S172C.Rank.reflect_mul_reflect_mem_orthDerived hS hQw hQy,
    ?_⟩
  · intro v hv
    rw [LinearEquiv.mul_apply, reflect_apply_of_polar_eq_zero (mem_suppPerp.mp hv y hy),
      reflect_apply_of_polar_eq_zero (mem_suppPerp.mp hv w hw)]
  · intro x
    have hstep : ∀ (v : V) (hv : v ∈ S) (hQv : Q v ≠ 0) (z : V) (hz : z ∈ S),
        ((reflect (Q.comp S.subtype) ⟨v, hv⟩ ⟨z, hz⟩ : S) : V) =
          z - (polar Q v z / Q v) • v := by
      intro v hv hQv z hz
      have h := reflect_apply (Q := Q.comp S.subtype) (v := ⟨v, hv⟩) (x := ⟨z, hz⟩)
        (by simpa using hQv)
      rw [h]
      simp only [QuadraticMap.comp_apply, polar_comp_subtype_eq, Submodule.subtype_apply,
        Submodule.coe_sub, Submodule.coe_smul]
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply,
      hstep w hw hQw _ (Submodule.coe_mem _), hstep y hy hQy (x : V) x.2,
      reflect_apply hQy, reflect_apply hQw]

private theorem ker_polarMap_eq_span {W : Submodule K V}
    (hW : (polarBilin (Q.comp W.subtype)).Nondegenerate) (hWdim : finrank K W = 2)
    {e : V} (he : e ∈ W) (he0 : e ≠ 0) :
    LinearMap.ker ((polarBilin Q e).comp W.subtype) =
      Submodule.span K {(⟨e, he⟩ : W)} := by
  let f : W →ₗ[K] K := (polarBilin Q e).comp W.subtype
  have hf : f ≠ 0 := by
    intro hf0
    apply he0
    have h := hW.1 ⟨e, he⟩ fun u => by
      have hu : f u = 0 := by rw [hf0]; rfl
      simpa [f, polarBilin_apply_apply, polar_comp_subtype_eq] using hu
    exact congrArg Subtype.val h
  have hrank : finrank K (LinearMap.range f) = 1 := by
    have hle : finrank K (LinearMap.range f) ≤ 1 := by
      have := Submodule.finrank_mono (show LinearMap.range f ≤ ⊤ from le_top)
      simpa [Module.finrank_self] using this
    have hne : LinearMap.range f ≠ ⊥ := by
      rwa [Ne, LinearMap.range_eq_bot]
    have hpos : 0 < finrank K (LinearMap.range f) := by
      rw [Nat.pos_iff_ne_zero]
      intro h0
      exact hne ((Submodule.finrank_eq_zero).mp h0)
    omega
  have hkerdim : finrank K (LinearMap.ker f) = 1 := by
    have hrn := LinearMap.finrank_range_add_finrank_ker f
    omega
  have heker : (⟨e, he⟩ : W) ∈ LinearMap.ker f := by
    rw [LinearMap.mem_ker]
    have hfe : f ⟨e, he⟩ = polar Q e e := by
      simp [f, polarBilin_apply_apply]
    rw [hfe, polar_self_eq_two_mul, CharTwo.two_eq_zero, zero_mul]
  have hle : Submodule.span K {(⟨e, he⟩ : W)} ≤ LinearMap.ker f := by
    rw [Submodule.span_le]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact heker
  have hdim : finrank K (Submodule.span K {(⟨e, he⟩ : W)}) = 1 := by
    rw [finrank_span_singleton]
    intro h0
    exact he0 (congrArg Subtype.val h0)
  exact (Submodule.eq_of_le_of_finrank_eq hle (by rw [hdim, hkerdim])).symm

theorem mem_span_singleton_sup_of_polar_eq_zero {W P : Submodule K V}
    (hW : (polarBilin (Q.comp W.subtype)).Nondegenerate) (hWdim : finrank K W = 2)
    (hWP : ∀ w ∈ W, ∀ u ∈ P, polar Q w u = 0) {e : V} (he : e ∈ W) (he0 : e ≠ 0) {x : V}
    (hx : x ∈ W ⊔ P) (hex : polar Q e x = 0) : x ∈ Submodule.span K {e} ⊔ P := by
  obtain ⟨w, hw, p, hp, hwp⟩ := Submodule.mem_sup.mp hx
  have hew : polar Q e w = 0 := by
    rw [← hwp, polar_add_right, hWP e he p hp, add_zero] at hex
    exact hex
  have hspan := ker_polarMap_eq_span hW hWdim he he0
  have hwker : (⟨w, hw⟩ : W) ∈ LinearMap.ker ((polarBilin Q e).comp W.subtype) := by
    rw [LinearMap.mem_ker]
    have hfw : ((polarBilin Q e).comp W.subtype) ⟨w, hw⟩ = polar Q e w := by
      simp [polarBilin_apply_apply]
    rw [hfw, hew]
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hspan ▸ hwker)
  have haw : w = a • e := by
    have := congrArg Subtype.val ha
    simpa using this.symm
  rw [← hwp, haw]
  exact Submodule.add_mem_sup (Submodule.smul_mem _ a (Submodule.subset_span rfl)) hp

theorem exists_mem_supportedDerived_fixedFree_of_nonsingular_basis [Finite K]
    {W : Submodule K V} (hW : (polarBilin (Q.comp W.subtype)).Nondegenerate)
    (b : Module.Basis (Fin 2) K W)
    (hQ0 : Q (b 0 : V) ≠ 0) (hQ1 : Q (b 1 : V) ≠ 0) :
    ∃ ρ ∈ supportedDerived Q W, ∀ z ∈ W, ρ z = z → z = 0 := by
  classical
  refine ⟨reflect Q (b 0 : V) * reflect Q (b 1 : V),
    reflect_mul_reflect_mem_supportedDerived hW (b 0).2 (b 1).2 hQ0 hQ1, ?_⟩
  intro z hz hfix
  have hsq : reflect Q (b 0 : V) (reflect Q (b 0 : V) (reflect Q (b 1 : V) z)) =
      reflect Q (b 1 : V) z := by
    have h := congrArg (fun e : V ≃ₗ[K] V => e (reflect Q (b 1 : V) z))
      (reflect_mul_self Q (b 0 : V))
    simpa [LinearEquiv.mul_apply] using h
  have hfix' : reflect Q (b 0 : V) (reflect Q (b 1 : V) z) = z := by
    simpa [LinearEquiv.mul_apply] using hfix
  have h1 : reflect Q (b 1 : V) z = reflect Q (b 0 : V) z := by
    have h := congrArg (reflect Q (b 0 : V)) hfix'
    rwa [hsq] at h
  have hcoef : (polar Q (b 1 : V) z / Q (b 1 : V)) • (b 1 : V) =
      (polar Q (b 0 : V) z / Q (b 0 : V)) • (b 0 : V) := by
    have h := h1
    rw [reflect_apply hQ1, reflect_apply hQ0] at h
    have h' := sub_eq_sub_iff_add_eq_add.mp h
    exact (add_left_cancel h').symm
  have hWeq : (polar Q (b 1 : V) z / Q (b 1 : V)) • b 1 =
      (polar Q (b 0 : V) z / Q (b 0 : V)) • b 0 := by
    apply Subtype.ext
    simpa [Submodule.coe_smul] using hcoef
  have hcv : polar Q (b 1 : V) z / Q (b 1 : V) = 0 := by
    have h := congrArg (b.coord 1) hWeq
    simpa [Module.Basis.coord_apply, Module.Basis.repr_self_apply] using h
  have hcu : polar Q (b 0 : V) z / Q (b 0 : V) = 0 := by
    have h := congrArg (b.coord 0) hWeq
    have h0 : 0 = polar Q (b 0 : V) z / Q (b 0 : V) := by
      simpa [Module.Basis.coord_apply, Module.Basis.repr_self_apply] using h
    exact h0.symm
  have hzu : polar Q (b 0 : V) z = 0 :=
    (div_eq_zero_iff.mp hcu).resolve_right hQ0
  have hzv : polar Q (b 1 : V) z = 0 :=
    (div_eq_zero_iff.mp hcv).resolve_right hQ1
  have hzperp : ∀ y ∈ W, polar Q z y = 0 := by
    intro y hy
    let y' : W := ⟨y, hy⟩
    have hyrepr : y = b.repr y' 0 • (b 0 : V) + b.repr y' 1 • (b 1 : V) := by
      have h := congrArg Subtype.val (b.sum_repr y')
      simp only [Fin.sum_univ_two, Submodule.coe_add, Submodule.coe_smul] at h
      exact h.symm
    calc polar Q z y = polar Q z (b.repr y' 0 • (b 0 : V) + b.repr y' 1 • (b 1 : V)) := by
          rw [hyrepr]
      _ = b.repr y' 0 * polar Q z (b 0 : V) + b.repr y' 1 * polar Q z (b 1 : V) := by
          rw [polar_add_right, polar_smul_right_eq, polar_smul_right_eq]
      _ = 0 := by
          rw [show polar Q z (b 0 : V) = 0 by rw [polar_comm, hzu],
            show polar Q z (b 1 : V) = 0 by rw [polar_comm, hzv]]
          simp
  have hzmem : (⟨z, hz⟩ : W) = 0 := hW.1 ⟨z, hz⟩ fun y => by
    simpa [polarBilin_apply_apply, polar_comp_subtype_eq] using hzperp y y.2
  exact Subtype.ext_iff.mp hzmem

private theorem exists_mem_supportedDerived_forall_eq_self_imp_eq_zero [Finite K]
    {W : Submodule K V} (hW : (polarBilin (Q.comp W.subtype)).Nondegenerate)
    (hWdim : finrank K W = 2) (hWaniso : ∀ w ∈ W, Q w = 0 → w = 0) :
    ∃ ρ ∈ supportedDerived Q W, ∀ z ∈ W, ρ z = z → z = 0 := by
  let b : Module.Basis (Fin 2) K W := Module.finBasisOfFinrankEq K W hWdim
  exact exists_mem_supportedDerived_fixedFree_of_nonsingular_basis hW b
    (fun h => b.ne_zero 0 (Subtype.ext (hWaniso _ (b 0).2 h)))
    (fun h => b.ne_zero 1 (Subtype.ext (hWaniso _ (b 1).2 h)))

theorem apply_eq_of_involution_commute_supportedDerived_anisotropic_plane [Finite K]
    {W : Submodule K V} (hW : (polarBilin (Q.comp W.subtype)).Nondegenerate)
    (hWdim : finrank K W = 2) (hWaniso : ∀ w ∈ W, Q w = 0 → w = 0)
    {g : V ≃ₗ[K] V} (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hg2 : g ^ 2 = 1) (hcomm : ∀ r ∈ supportedDerived Q W, Commute g r) :
    ∀ w ∈ W, g w = w := by
  classical
  obtain ⟨ρ, hρ, hρfix⟩ :=
    exists_mem_supportedDerived_forall_eq_self_imp_eq_zero hW hWdim hWaniso
  have hWon : PolarNondegOn Q W := polarNondegOn_of_nondegenerate hW
  have hρO : ρ ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    supportedDerived_le_orthogonalGroup hWon hρ
  have hdisp : ∀ x : V, ρ x - x ∈ W := by
    intro x
    obtain ⟨w, hw, p, hp, hwpx⟩ :=
      suppExists_add_of_isCompl (isCompl_suppPerp hWon) x
    have hρp : ρ p = p := supportedDerived_apply_perp hρ hp
    have hρw : ρ w ∈ W := supportedDerived_apply_mem hρ hw
    have hx : ρ x - x = ρ w - w := by
      rw [← hwpx, map_add, hρp]
      abel
    rw [hx]
    exact Submodule.sub_mem W hρw hw
  have hρcomm : ∀ y : V, g (ρ y) = ρ (g y) := by
    intro y
    have h := congrArg (fun e : V ≃ₗ[K] V => e y) (hcomm ρ hρ).eq
    simpa [LinearEquiv.mul_apply] using h
  let d : W →ₗ[K] W :=
    ((ρ : V →ₗ[K] V) - 1).restrict (p := W) (q := W) fun x _ => hdisp x
  have hdker : ∀ x : W, d x = 0 → x = 0 := by
    intro x hx
    have hval : ρ (x : V) - (x : V) = 0 := by
      have h := congrArg Subtype.val hx
      simpa [d] using h
    have hρx : ρ (x : V) = x := sub_eq_zero.mp hval
    exact Subtype.ext (hρfix (x : V) x.2 hρx)
  have hdinj : Function.Injective d := by
    intro x y hxy
    have hzero : d (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have hsub : x - y = 0 := hdker (x - y) hzero
    exact sub_eq_zero.mp hsub
  have hdsurj : Function.Surjective d := LinearMap.surjective_of_injective hdinj
  have hgW : ∀ w ∈ W, g w ∈ W := by
    intro w hw
    obtain ⟨y, hy⟩ := hdsurj ⟨w, hw⟩
    have hyval : ρ (y : V) - (y : V) = w := by
      have h := congrArg Subtype.val hy
      simpa [d] using h
    have hstep : g w = ρ (g (y : V)) - g (y : V) := by
      calc g w = g (ρ (y : V) - (y : V)) := by rw [hyval]
        _ = g (ρ (y : V)) - g (y : V) := map_sub g _ _
        _ = ρ (g (y : V)) - g (y : V) := by rw [hρcomm]
    rw [hstep]
    exact hdisp (g (y : V))
  have hnoeigen : ∀ z ∈ W, z ≠ 0 → ρ z ∉ Submodule.span K {z} := by
    intro z hz hz0 hmem
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    have hQz : Q z ≠ 0 := fun h => hz0 (hWaniso z hz h)
    have hQ : Q (ρ z) = Q z := TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hρO z
    have hcQ : Q (ρ z) = c ^ 2 * Q z := by
      rw [← hc, map_smul_eq_sq]
    have hc2 : c ^ 2 = 1 := by
      have h : c ^ 2 * Q z = 1 * Q z := by rw [← hcQ, hQ, one_mul]
      exact mul_right_cancel₀ hQz h
    have hc1 : c = 1 := CharTwo.sq_inj.mp (by simpa using hc2)
    have hρz : ρ z = z := by rw [← hc, hc1, one_smul]
    exact hz0 (hρfix z hz hρz)
  have hg2' : g * g = 1 := by simpa [pow_two] using hg2
  intro w hw
  have hzW : g w - w ∈ W := Submodule.sub_mem W (hgW w hw) hw
  have hzcomm : g w - w ∈ commSpace g := sub_mem_commSpace g w
  have hρzcomm : ρ (g w - w) ∈ commSpace g := by
    have hρg : g (ρ w) = ρ (g w) := hρcomm w
    refine mem_commSpace.mpr ⟨ρ w, ?_⟩
    rw [map_sub, hρg]
  have hpol : polar Q (g w - w) (ρ (g w - w)) = 0 :=
    polar_commSpace_eq_zero hgO hg2' hzcomm hρzcomm
  by_contra hne
  have hne0 : g w - w ≠ 0 := sub_ne_zero.mpr hne
  have hspan : ρ (g w - w) ∈ Submodule.span K {g w - w} := by
    have hmem : ρ (g w - w) ∈ W ⊔ (⊥ : Submodule K V) := by
      rw [sup_bot_eq]
      exact supportedDerived_apply_mem hρ hzW
    have horth : ∀ x ∈ W, ∀ u ∈ (⊥ : Submodule K V), polar Q x u = 0 := by
      intro x _ u hu
      rw [Submodule.mem_bot] at hu
      rw [hu, polar_zero_right]
    have h := mem_span_singleton_sup_of_polar_eq_zero (P := ⊥) hW hWdim horth hzW hne0 hmem hpol
    simpa using h
  exact hnoeigen (g w - w) hzW hne0 hspan

end CFSG.RankThree.PartOne.KCOrthogonal
