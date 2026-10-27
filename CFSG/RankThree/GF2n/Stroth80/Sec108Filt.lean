module

public import CFSG.RankThree.GF2n.Stroth80.Sec108Setup
public import CFSG.RankThree.GF2n.Stroth80.Sec10Sigma
public import CFSG.RankThree.GF2n.Smith81.OrthE1Steps

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {hc : Ctx M Q Z B} {t : G} {Y : Subgroup G}

noncomputable def Sec108Data.nu (D : Sec108Data hc t Y) (AM : Smith81.Smith23E1.ActionModel M Q Z) :
    AM.M₀.E →ₗ[AM.K] AM.M₀.E :=
  (AM.φ ⟨t, D.t_mem_H0⟩ : AM.M₀.E →ₗ[AM.K] AM.M₀.E) - LinearMap.id

theorem Sec108Data.nu_apply (D : Sec108Data hc t Y) (AM : Smith81.Smith23E1.ActionModel M Q Z)
    (e : AM.M₀.E) : D.nu AM e = AM.φ ⟨t, D.t_mem_H0⟩ e - e := by
  simp only [Sec108Data.nu, LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_coe]

private theorem Sec108Data.t_action_sq (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) :
    AM.φ ⟨t, D.t_mem_H0⟩ * AM.φ ⟨t, D.t_mem_H0⟩ = 1 := by
  rw [← map_mul,
    show (⟨t, D.t_mem_H0⟩ * ⟨t, D.t_mem_H0⟩ : ↥(H0 M Z)) = 1 by
      ext
      simpa using D.sit.x_sq,
    map_one]

private theorem Sec108Data.t_action_apply_apply (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) (e : AM.M₀.E) :
    AM.φ ⟨t, D.t_mem_H0⟩ (AM.φ ⟨t, D.t_mem_H0⟩ e) = e := by
  have h := congrArg (fun g : AM.M₀.E ≃ₗ[AM.K] AM.M₀.E => g e) (D.t_action_sq AM)
  simpa [mul_apply] using h

private theorem Sec108Data.t_action_isometry (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) (e f : AM.M₀.E) :
    AM.M₀.B (AM.φ ⟨t, D.t_mem_H0⟩ e) (AM.φ ⟨t, D.t_mem_H0⟩ f) = AM.M₀.B e f :=
  quadModel_B_iso AM.M₀ (AM.φ ⟨t, D.t_mem_H0⟩) (AM.φ_Qf ⟨t, D.t_mem_H0⟩) e f

theorem Sec108Data.nu_comp_nu (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) :
    D.nu AM ∘ₗ D.nu AM = 0 := by
  have hT2 : (AM.φ ⟨t, D.t_mem_H0⟩ : AM.M₀.E →ₗ[AM.K] AM.M₀.E) ∘ₗ
      (AM.φ ⟨t, D.t_mem_H0⟩ : AM.M₀.E →ₗ[AM.K] AM.M₀.E) = LinearMap.id := by
    ext e
    simpa [LinearMap.comp_apply] using D.t_action_apply_apply AM e
  rw [← LinearMap.range_le_ker_iff]
  exact Tim79.QuadModel.range_le_ker_of_sq_eq_one AM.M₀ hT2

theorem Sec108Data.B_nu (D : Sec108Data hc t Y) (AM : Smith81.Smith23E1.ActionModel M Q Z)
    (e f : AM.M₀.E) : AM.M₀.B (D.nu AM e) f = AM.M₀.B e (D.nu AM f) := by
  have hiso : AM.M₀.B (AM.φ ⟨t, D.t_mem_H0⟩ e) f = AM.M₀.B e (AM.φ ⟨t, D.t_mem_H0⟩ f) := by
    have h := D.t_action_isometry AM e (AM.φ ⟨t, D.t_mem_H0⟩ f)
    rwa [D.t_action_apply_apply AM f] at h
  simp only [Sec108Data.nu, LinearMap.sub_apply, LinearMap.id_apply]
  calc AM.M₀.B (AM.φ ⟨t, D.t_mem_H0⟩ e - e) f
      = AM.M₀.B (AM.φ ⟨t, D.t_mem_H0⟩ e) f - AM.M₀.B e f := by
        rw [map_sub, LinearMap.sub_apply]
    _ = AM.M₀.B e (AM.φ ⟨t, D.t_mem_H0⟩ f) - AM.M₀.B e f := by rw [hiso]
    _ = AM.M₀.B e (AM.φ ⟨t, D.t_mem_H0⟩ f - f) := by rw [LinearMap.map_sub]

theorem Sec108Data.img_Ut_eq (D : Sec108Data hc t Y) (AM : Smith81.Smith23E1.ActionModel M Q Z) :
    AM.M₀.img (Ut Q Z t) = (LinearMap.range (D.nu AM) : Set AM.M₀.E) := by
  have htM : t ∈ M := hc.LB_le_M D.good.1.mem_LB
  obtain ⟨htQ, htQ'⟩ := hc.conj_mem_Q_of_mem_M htM
  ext v
  exact mem_img_comm_zpowers_sup_iff AM.M₀ AM.glob.reg (AM.φ ⟨t, D.t_mem_H0⟩) htQ htQ'
    (fun x hx => AM.φ_π ⟨t, D.t_mem_H0⟩ x hx) v

theorem Sec108Data.finrank_E (D : Sec108Data hc t Y) (AM : Smith81.Smith23E1.ActionModel M Q Z) :
    Module.finrank AM.K AM.M₀.E = 12 := by
  have hK : 1 < Nat.card AM.K := by
    rw [AM.glob.card]
    have := hc.hyp.q4
    omega
  have h := AM.glob.finrank_E D.hyp.width hK
  omega

private theorem finrank_comap_eq_add_finrank {K E : Type} [Field K] [AddCommGroup E] [Module K E]
    [FiniteDimensional K E] (f : E →ₗ[K] E) {W : Submodule K E}
    (hW : W ≤ LinearMap.range f) :
    Module.finrank K (W.comap f) = Module.finrank K W + Module.finrank K (LinearMap.ker f) := by
  let g : W.comap f →ₗ[K] W := f.restrict (fun x hx => hx)
  have hker : LinearMap.ker g = (LinearMap.ker f).comap (W.comap f).subtype :=
    LinearMap.ker_restrict (f := f) (p := W.comap f) (q := W) (fun x hx => hx)
  have hle : LinearMap.ker f ≤ W.comap f := fun x hx => by
    rw [Submodule.mem_comap, LinearMap.mem_ker.mp hx]
    exact W.zero_mem
  have hkerdim : Module.finrank K (LinearMap.ker g) = Module.finrank K (LinearMap.ker f) := by
    rw [hker]
    exact (Submodule.comapSubtypeEquivOfLe hle).finrank_eq
  have hrankg : LinearMap.range g = ⊤ := by
    rw [LinearMap.range_eq_top]
    rintro ⟨w, hw⟩
    obtain ⟨e, he⟩ := hW hw
    refine ⟨⟨e, ?_⟩, ?_⟩
    · rw [Submodule.mem_comap, he]
      exact hw
    · ext
      exact he
  have hrank := LinearMap.finrank_range_add_finrank_ker g
  rw [hrankg, finrank_top, hkerdim] at hrank
  omega

theorem Sec108Data.finrank_range_nu (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) :
    Module.finrank AM.K (LinearMap.range (D.nu AM)) = 6 := by
  have hq : 1 < Nat.card Z := by
    have := hc.hyp.q4
    omega
  have htM : t ∈ M := hc.LB_le_M D.good.1.mem_LB
  obtain ⟨htQ, htQ'⟩ := hc.conj_mem_Q_of_mem_M htM
  have hcard := card_comm_zpowers_sup AM.M₀ AM.glob.reg (AM.φ ⟨t, D.t_mem_H0⟩) htQ htQ'
    (fun x hx => AM.φ_π ⟨t, D.t_mem_H0⟩ x hx)
  have hcard' : Nat.card (Ut Q Z t) = Nat.card Z *
      Nat.card AM.K ^ Module.finrank AM.K (LinearMap.range (D.nu AM)) := hcard
  have heq : Nat.card Z ^ 7 = Nat.card Z *
      Nat.card Z ^ Module.finrank AM.K (LinearMap.range (D.nu AM)) := by
    rw [← D.card_Ut, hcard', AM.glob.card]
  have h2 : Nat.card Z ^ 7 =
      Nat.card Z ^ (1 + Module.finrank AM.K (LinearMap.range (D.nu AM))) := by
    rw [pow_add, pow_one]
    exact heq
  have h3 := Nat.pow_right_injective hq h2
  omega

theorem Sec108Data.range_nu_eq_ker (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) :
    LinearMap.range (D.nu AM) = LinearMap.ker (D.nu AM) := by
  have hle : LinearMap.range (D.nu AM) ≤ LinearMap.ker (D.nu AM) :=
    LinearMap.range_le_ker_iff.mpr (D.nu_comp_nu AM)
  have hrn := LinearMap.finrank_range_add_finrank_ker (D.nu AM)
  have hE := D.finrank_E AM
  have hr := D.finrank_range_nu AM
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  omega

theorem Sec108Data.orthogonal_range_nu (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) :
    AM.M₀.B.orthogonal (LinearMap.range (D.nu AM)) = LinearMap.range (D.nu AM) := by
  have hrefl : AM.M₀.B.IsRefl := LinearMap.IsAlt.isRefl AM.M₀.alt
  have hnd : AM.M₀.B.Nondegenerate :=
    hrefl.nondegenerate_iff_separatingLeft.mpr AM.M₀.nondeg
  have h := range_sub_one_eq_orthogonal_ker AM.M₀.B hnd hrefl
    (AM.φ ⟨t, D.t_mem_H0⟩ : AM.M₀.E →ₗ[AM.K] AM.M₀.E)
    (D.t_action_isometry AM) (D.t_action_apply_apply AM)
  have h' : LinearMap.range (D.nu AM) =
      AM.M₀.B.orthogonal (LinearMap.ker (D.nu AM)) := by
    simpa only [Sec108Data.nu, Module.End.one_eq_id] using h
  rw [← D.range_nu_eq_ker AM] at h'
  exact h'.symm

theorem Sec108Data.finrank_Vsp (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) :
    Module.finrank AM.K (AM.Vsp hc t) = 3 := by
  have hq : 1 < Nat.card Z := by
    have := hc.hyp.q4
    omega
  have hcard : Nat.card (Vt M (LB M Q B) B Z t) =
      Nat.card Z * Nat.card (AM.M₀.img (Vt M (LB M Q B) B Z t)) :=
    AM.M₀.card_eq (hc.Vt_le_Q t) sec39_Z_le_Vt
  have hVsp : Nat.card (AM.Vsp hc t) =
      Nat.card (AM.M₀.img (Vt M (LB M Q B) B Z t)) := rfl
  have hpow : Nat.card (AM.Vsp hc t) =
      Nat.card AM.K ^ Module.finrank AM.K (AM.Vsp hc t) :=
    Module.natCard_eq_pow_finrank
  have heq : Nat.card Z ^ 4 =
      Nat.card Z * Nat.card Z ^ Module.finrank AM.K (AM.Vsp hc t) := by
    rw [← D.card_Vt, hcard, ← hVsp, hpow, AM.glob.card]
  have h2 : Nat.card Z ^ 4 =
      Nat.card Z ^ (1 + Module.finrank AM.K (AM.Vsp hc t)) := by
    rw [pow_add, pow_one]
    exact heq
  have h3 := Nat.pow_right_injective hq h2
  omega

theorem Sec108Data.Vsp_le_range_nu (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) :
    AM.Vsp hc t ≤ LinearMap.range (D.nu AM) := by
  intro e he
  have h35 : CQt Q Z (LB M Q B) = ((B ⊔ Z : Subgroup G) : Set G) :=
    (stroth_3_5 D.h34 hc D.hyp.width D.hyp.n_gt D.hyp.noA2 D.hyp.gen).2.1
  have hVt : Vt M (LB M Q B) B Z t ≤ Tt Q Z (Vt M (LB M Q B) B Z t) t :=
    hc.Vt_le_Tt_of_SLNat (D.hyp.toSec5 D.good.1.mem_LB D.good.1.2.2.1) h35
      (SLMNat.toSLNat D.slm (by norm_num))
  have hTt_le_Ut : Tt Q Z (Vt M (LB M Q B) B Z t) t ≤ Ut Q Z t :=
    sup_le_sup_right (Subgroup.commutator_mono inf_le_left le_rfl) Z
  have he' : e ∈ AM.M₀.img (Ut Q Z t) :=
    AM.M₀.img_mono (hVt.trans hTt_le_Ut) (mem_imgSub.mp he)
  have htM : t ∈ M := hc.LB_le_M D.good.1.mem_LB
  obtain ⟨htQ, htQ'⟩ := hc.conj_mem_Q_of_mem_M htM
  exact (mem_img_comm_zpowers_sup_iff AM.M₀ AM.glob.reg (AM.φ ⟨t, D.t_mem_H0⟩) htQ htQ'
    (fun x hx => AM.φ_π ⟨t, D.t_mem_H0⟩ x hx) e).mp he'

theorem Sec108Data.orthogonal_Vsp_eq_comap (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) :
    AM.M₀.B.orthogonal (AM.Vsp hc t) = (AM.Vsp hc t).comap (D.nu AM) := by
  have hrefl : AM.M₀.B.IsRefl := LinearMap.IsAlt.isRefl AM.M₀.alt
  have hnd : AM.M₀.B.Nondegenerate :=
    hrefl.nondegenerate_iff_separatingLeft.mpr AM.M₀.nondeg
  have hle : AM.M₀.B.orthogonal (AM.Vsp hc t) ≤ (AM.Vsp hc t).comap (D.nu AM) := by
    intro e he
    rw [Submodule.mem_comap]
    exact Good103.sub_mem_Vsp_of_orthogonal D.h34 D.h311a D.hspread D.hyp D.good AM.glob
      (AM.φ ⟨t, D.t_mem_H0⟩) (fun x hx => AM.φ_π ⟨t, D.t_mem_H0⟩ x hx) e
      (fun v hv => hrefl.eq_iff.mpr (LinearMap.BilinForm.mem_orthogonal_iff.mp he v hv))
  have hdim : Module.finrank AM.K (AM.M₀.B.orthogonal (AM.Vsp hc t)) =
      Module.finrank AM.K ((AM.Vsp hc t).comap (D.nu AM)) := by
    rw [LinearMap.BilinForm.finrank_orthogonal hnd, D.finrank_E AM, D.finrank_Vsp AM,
      finrank_comap_eq_add_finrank (D.nu AM) (D.Vsp_le_range_nu AM), D.finrank_Vsp AM,
      ← D.range_nu_eq_ker AM, D.finrank_range_nu AM]
  exact Submodule.eq_of_le_of_finrank_eq hle hdim

private noncomputable def dualOnRange {K E U : Type} [Field K] [AddCommGroup E] [Module K E]
    [AddCommGroup U] [Module K U] (B : LinearMap.BilinForm K E) (s : U →ₗ[K] E) :
    E →ₗ[K] (U →ₗ[K] K) where
  toFun e := (B e).comp s
  map_add' e₁ e₂ := by
    ext u
    simp
  map_smul' c e := by
    ext u
    simp

private theorem kernel_nu_le_dualKernel (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) :
    LinearMap.ker (D.nu AM) ≤ LinearMap.ker
      (dualOnRange AM.M₀.B (Submodule.subtype (LinearMap.range (D.nu AM)))) := by
  intro e he
  rw [LinearMap.mem_ker] at he ⊢
  ext w
  have hrefl : AM.M₀.B.IsRefl := LinearMap.IsAlt.isRefl AM.M₀.alt
  have horth : e ∈ AM.M₀.B.orthogonal (LinearMap.range (D.nu AM)) := by
    rw [D.orthogonal_range_nu AM, D.range_nu_eq_ker AM, LinearMap.mem_ker]
    exact he
  exact hrefl.eq_iff.mpr ((LinearMap.BilinForm.mem_orthogonal_iff.mp horth) w w.2)

noncomputable def Sec108Data.Pform (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) :
    LinearMap.BilinForm AM.K (LinearMap.range (D.nu AM)) :=
  ((LinearMap.ker (D.nu AM)).liftQ
      (dualOnRange AM.M₀.B (Submodule.subtype (LinearMap.range (D.nu AM))))
      (kernel_nu_le_dualKernel D AM)).comp
    ((LinearMap.quotKerEquivRange (D.nu AM)).symm : _ →ₗ[AM.K] _)

theorem Sec108Data.Pform_nu (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) (e : AM.M₀.E)
    (u : LinearMap.range (D.nu AM)) :
    D.Pform AM ⟨D.nu AM e, LinearMap.mem_range_self _ e⟩ u = AM.M₀.B e u := by
  simp only [Sec108Data.Pform, LinearMap.comp_apply, LinearEquiv.coe_coe,
    Submodule.liftQ_apply, LinearMap.quotKerEquivRange_symm_apply_image, dualOnRange,
    LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_subtype]
  rfl

theorem Sec108Data.Pform_nondegenerate (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) : (D.Pform AM).Nondegenerate := by
  constructor
  · intro u hu
    obtain ⟨e, he⟩ := u.2
    have hzero : D.nu AM e = 0 := by
      refine AM.M₀.nondeg (D.nu AM e) fun f => ?_
      rw [D.B_nu AM e f]
      have h := hu ⟨D.nu AM f, LinearMap.mem_range_self _ f⟩
      rw [show u = ⟨D.nu AM e, LinearMap.mem_range_self _ e⟩ from Subtype.ext he.symm] at h
      rwa [D.Pform_nu AM e] at h
    refine Subtype.ext ?_
    rw [← he]
    exact hzero
  · intro v hv
    refine Subtype.ext ?_
    refine AM.M₀.nondeg v.1 fun e => ?_
    have h := hv ⟨D.nu AM e, LinearMap.mem_range_self _ e⟩
    rw [D.Pform_nu AM e] at h
    exact (LinearMap.IsAlt.isRefl AM.M₀.alt).eq_iff.mpr h

theorem Sec108Data.Pform_Vsp (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) (u v : LinearMap.range (D.nu AM))
    (hu : (u : AM.M₀.E) ∈ AM.Vsp hc t) (hv : (v : AM.M₀.E) ∈ AM.Vsp hc t) :
    D.Pform AM u v = 0 := by
  obtain ⟨e, he⟩ := u.2
  have hu' : u = ⟨D.nu AM e, LinearMap.mem_range_self _ e⟩ := Subtype.ext he.symm
  rw [hu', D.Pform_nu AM e]
  have hrefl : AM.M₀.B.IsRefl := LinearMap.IsAlt.isRefl AM.M₀.alt
  have horth : e ∈ AM.M₀.B.orthogonal (AM.Vsp hc t) := by
    rw [D.orthogonal_Vsp_eq_comap AM, Submodule.mem_comap]
    rwa [he]
  exact hrefl.eq_iff.mpr ((LinearMap.BilinForm.mem_orthogonal_iff.mp horth) v.1 hv)

theorem Sec108Data.Pform_map (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {m : ↥(H0 M Z)}
    (hm : ∀ e, AM.φ m (AM.φ ⟨t, D.t_mem_H0⟩ e) = AM.φ ⟨t, D.t_mem_H0⟩ (AM.φ m e))
    (e f : AM.M₀.E) :
    D.Pform AM ⟨D.nu AM (AM.φ m e), LinearMap.mem_range_self _ _⟩
        ⟨D.nu AM (AM.φ m f), LinearMap.mem_range_self _ _⟩ =
      D.Pform AM ⟨D.nu AM e, LinearMap.mem_range_self _ _⟩
        ⟨D.nu AM f, LinearMap.mem_range_self _ _⟩ := by
  rw [D.Pform_nu AM (AM.φ m e), D.Pform_nu AM e]
  have hνm : D.nu AM (AM.φ m f) = AM.φ m (D.nu AM f) := by
    simp only [Sec108Data.nu, LinearMap.sub_apply, LinearMap.id_apply]
    rw [map_sub]
    congr 1
    exact (hm f).symm
  have hsub : (⟨D.nu AM (AM.φ m f), LinearMap.mem_range_self _ _⟩ :
      LinearMap.range (D.nu AM)) = ⟨AM.φ m (D.nu AM f), hνm ▸ LinearMap.mem_range_self _ _⟩ :=
    Subtype.ext hνm
  rw [hsub]
  exact quadModel_B_iso AM.M₀ (AM.φ m) (AM.φ_Qf m) e (D.nu AM f)

end CFSG.RankThree.GF2n.Stroth80
