module

public import CFSG.RankThree.GF2n.Stroth80.Sec108Filt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {hc : Ctx M Q Z B} {t : G} {Y : Subgroup G}

private theorem smul_mem_img_inf_QB (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) (c : AM.K) (e : AM.M₀.E)
    (he : e ∈ AM.M₀.img (Q ⊓ QB B)) : c • e ∈ AM.M₀.img (Q ⊓ QB B) := by
  obtain ⟨W, hW⟩ := Ctx.exists_submodule_inf_QB hc D.hyp.width D.card_inf_QB AM.glob
  exact (hW _).mp (W.smul_mem c ((hW _).mpr he))

noncomputable def Sec108Data.Asp (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) : Submodule AM.K AM.M₀.E :=
  imgSub AM.M₀ (Q ⊓ QB B) (smul_mem_img_inf_QB D AM)

theorem Sec108Data.mem_Asp (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {e : AM.M₀.E} :
    e ∈ D.Asp AM ↔ e ∈ AM.M₀.img (Q ⊓ QB B) :=
  Iff.rfl

private theorem smul_mem_img_B (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) (c : AM.K) (e : AM.M₀.E)
    (he : e ∈ AM.M₀.img B) : c • e ∈ AM.M₀.img B := by
  obtain ⟨b, -, -, hB, -, -⟩ := Ctx.dictB hc AM.glob
  obtain ⟨s, rfl⟩ := (hB e).mp he
  exact (hB _).mpr ⟨c * s, by rw [smul_smul]⟩

noncomputable def Sec108Data.Bsp (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) : Submodule AM.K AM.M₀.E :=
  imgSub AM.M₀ B (smul_mem_img_B D AM)

theorem Sec108Data.mem_Bsp (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {e : AM.M₀.E} :
    e ∈ D.Bsp AM ↔ e ∈ AM.M₀.img B :=
  Iff.rfl

private theorem Bsp_eq_span (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {b : AM.M₀.E}
    (hb : ∀ v : AM.M₀.E, v ∈ AM.M₀.img B ↔ ∃ s : AM.K, v = s • b) :
    D.Bsp AM = Submodule.span AM.K {b} := by
  ext e
  rw [D.mem_Bsp AM, hb, Submodule.mem_span_singleton]
  exact exists_congr fun s => eq_comm

theorem Sec108Data.finrank_Bsp (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) : Module.finrank AM.K (D.Bsp AM) = 1 := by
  obtain ⟨b, hb0, -, hB, -, -⟩ := Ctx.dictB hc AM.glob
  rw [Bsp_eq_span D AM hB, finrank_span_singleton hb0]

theorem Sec108Data.Bsp_le_Vsp (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) : D.Bsp AM ≤ AM.Vsp hc t := by
  intro e he
  rw [D.mem_Bsp AM] at he
  exact mem_imgSub.mpr (AM.M₀.img_mono (hc.B_le_Vt D.good.1.mem_LB) he)

theorem Sec108Data.Vsp_le_Asp (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) : AM.Vsp hc t ≤ D.Asp AM := by
  have hVQB : Vt M (LB M Q B) B Z t ≤ QB B :=
    stroth310SL_of_34 D.h34 G M Q Z B hc 6 t
      (D.hyp.toSec5 D.good.1.mem_LB D.good.1.2.2.1) (SLMNat.toSLNat D.slm (by norm_num))
  intro e he
  exact mem_imgSub.mpr (AM.M₀.img_mono (le_inf (hc.Vt_le_Q t) hVQB) (mem_imgSub.mp he))

private theorem phi_fixes_of_mem_Bsp (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) (x : ↥(LB M Q B)) {w : AM.M₀.E}
    (hw : w ∈ D.Bsp AM) : AM.φ ⟨x, hc.LB_le_H0 x.2⟩ w = w := by
  obtain ⟨b, -, -, hB, -, -⟩ := Ctx.dictB hc AM.glob
  have hTb : AM.φ ⟨x, hc.LB_le_H0 x.2⟩ b = b :=
    (Ctx.LB_act_fix_line hc AM.glob hB x.2
      (T := (AM.φ ⟨x, hc.LB_le_H0 x.2⟩ : AM.M₀.E →ₗ[AM.K] AM.M₀.E))
      (fun z hz => AM.φ_π ⟨x, hc.LB_le_H0 x.2⟩ z hz)).1
  obtain ⟨c, rfl⟩ := (hB w).mp ((D.mem_Bsp AM).mp hw)
  rw [LinearEquiv.map_smul, hTb]

noncomputable def Sec108Data.delta (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) (x : ↥(LB M Q B)) :
    ↥(D.Asp AM) →ₗ[AM.K] ↥(D.Bsp AM) :=
  ((AM.φ ⟨x, hc.LB_le_H0 x.2⟩ : AM.M₀.E →ₗ[AM.K] AM.M₀.E) - LinearMap.id).restrict
    (fun a ha => by
      obtain ⟨b, -, -, hB, -, -⟩ := Ctx.dictB hc AM.glob
      obtain ⟨c, hc'⟩ := (Ctx.LB_act_fix_line hc AM.glob hB x.2
        (T := (AM.φ ⟨x, hc.LB_le_H0 x.2⟩ : AM.M₀.E →ₗ[AM.K] AM.M₀.E))
        (fun z hz => AM.φ_π ⟨x, hc.LB_le_H0 x.2⟩ z hz)).2 a ((D.mem_Asp AM).mp ha)
      rw [LinearMap.sub_apply, LinearMap.id_apply, hc', D.mem_Bsp AM]
      exact (hB _).mpr ⟨c, rfl⟩)

theorem Sec108Data.delta_apply (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) (x : ↥(LB M Q B)) (a : ↥(D.Asp AM)) :
    ((D.delta AM x a : ↥(D.Bsp AM)) : AM.M₀.E) =
      AM.φ ⟨x, hc.LB_le_H0 x.2⟩ a - a := by
  rw [Sec108Data.delta, LinearMap.coe_restrict_apply, LinearMap.sub_apply, LinearMap.id_apply]
  rfl

theorem Sec108Data.delta_Bsp (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) (x : ↥(LB M Q B)) (a : ↥(D.Asp AM))
    (ha : (a : AM.M₀.E) ∈ D.Bsp AM) : D.delta AM x a = 0 := by
  apply Subtype.ext
  rw [D.delta_apply AM x a, phi_fixes_of_mem_Bsp D AM x ha, sub_self]
  rfl

theorem Sec108Data.delta_mul (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) (x y : ↥(LB M Q B)) :
    D.delta AM (x * y) = D.delta AM x + D.delta AM y := by
  ext a
  rw [LinearMap.add_apply, Submodule.coe_add, D.delta_apply AM (x * y) a,
    D.delta_apply AM x a, D.delta_apply AM y a]
  have hxy : (⟨((x * y : ↥(LB M Q B)) : G), hc.LB_le_H0 (x * y).2⟩ : ↥(H0 M Z)) =
      ⟨x, hc.LB_le_H0 x.2⟩ * ⟨y, hc.LB_le_H0 y.2⟩ := rfl
  have hcomp : AM.φ ⟨(x * y : ↥(LB M Q B)), hc.LB_le_H0 (x * y).2⟩ a =
      AM.φ ⟨x, hc.LB_le_H0 x.2⟩ (AM.φ ⟨y, hc.LB_le_H0 y.2⟩ a) := by
    rw [hxy, map_mul]
    exact LinearEquiv.mul_apply (R := AM.K) (M := AM.M₀.E)
      (AM.φ ⟨x, hc.LB_le_H0 x.2⟩) (AM.φ ⟨y, hc.LB_le_H0 y.2⟩) (a : AM.M₀.E)
  have hfix : AM.φ ⟨x, hc.LB_le_H0 x.2⟩ (AM.φ ⟨y, hc.LB_le_H0 y.2⟩ a - a) =
      AM.φ ⟨y, hc.LB_le_H0 y.2⟩ a - a := by
    have hw : AM.φ ⟨y, hc.LB_le_H0 y.2⟩ a - a ∈ D.Bsp AM := by
      rw [← D.delta_apply AM y a]
      exact (D.delta AM y a).2
    exact phi_fixes_of_mem_Bsp D AM x hw
  have hgoal : AM.φ ⟨(x * y : ↥(LB M Q B)), hc.LB_le_H0 (x * y).2⟩ a - a =
      (AM.φ ⟨x, hc.LB_le_H0 x.2⟩ a - a) + (AM.φ ⟨y, hc.LB_le_H0 y.2⟩ a - a) := by
    rw [hcomp]
    have hv : AM.φ ⟨x, hc.LB_le_H0 x.2⟩ (AM.φ ⟨y, hc.LB_le_H0 y.2⟩ a) =
        (AM.φ ⟨y, hc.LB_le_H0 y.2⟩ a - a) + AM.φ ⟨x, hc.LB_le_H0 x.2⟩ a := by
      calc AM.φ ⟨x, hc.LB_le_H0 x.2⟩ (AM.φ ⟨y, hc.LB_le_H0 y.2⟩ a)
          = AM.φ ⟨x, hc.LB_le_H0 x.2⟩
              ((AM.φ ⟨y, hc.LB_le_H0 y.2⟩ a - a) + a) := by rw [sub_add_cancel]
        _ = AM.φ ⟨x, hc.LB_le_H0 x.2⟩ (AM.φ ⟨y, hc.LB_le_H0 y.2⟩ a - a) +
              AM.φ ⟨x, hc.LB_le_H0 x.2⟩ a := by rw [map_add]
        _ = (AM.φ ⟨y, hc.LB_le_H0 y.2⟩ a - a) + AM.φ ⟨x, hc.LB_le_H0 x.2⟩ a := by rw [hfix]
    rw [hv]
    abel
  exact hgoal

theorem Sec108Data.delta_eq_zero_iff (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) (x : ↥(LB M Q B)) :
    D.delta AM x = 0 ↔ (x : G) ∈ Q := by
  constructor
  · intro hx
    have hcommZ : ∀ d ∈ Q ⊓ QB B, ⁅(x : G), d⁆ ∈ Z := by
      intro d hd
      have hmem : AM.M₀.π d ∈ D.Asp AM :=
        (D.mem_Asp AM).mpr (AM.M₀.pi_mem_img (S := Q ⊓ QB B) hd hd.1)
      have h0 : D.delta AM x ⟨AM.M₀.π d, hmem⟩ = 0 := by rw [hx]; rfl
      have h1 := congrArg (fun z : ↥(D.Bsp AM) => (z : AM.M₀.E)) h0
      rw [D.delta_apply AM x ⟨AM.M₀.π d, hmem⟩] at h1
      have hfix : AM.φ ⟨x, hc.LB_le_H0 x.2⟩ (AM.M₀.π d) = AM.M₀.π d :=
        sub_eq_zero.mp (by simpa using h1)
      exact (comm_mem_iff_fix (M₀ := AM.M₀) (T := AM.φ ⟨x, hc.LB_le_H0 x.2⟩)
        (hc.conj_mem_Q_of_mem_M (hc.LB_le_M x.2)).1
        (fun z hz => AM.φ_π ⟨x, hc.LB_le_H0 x.2⟩ z hz) hd.1).mpr hfix
    obtain ⟨s, hs, y, hy, hxy⟩ := hc.exists_mul_of_mem_LB x.2
    rw [hxy] at hcommZ
    have hsdZ : ∀ d ∈ Q ⊓ QB B, ⁅s, d⁆ ∈ Z := by
      intro d hd
      have hyd : ⁅y, d⁆ ∈ Z := hc.hyp.toHyp79.comm_mem_V hy (Subgroup.mem_inf.mp hd).1
      have hconj : s * ⁅y, d⁆ * s⁻¹ ∈ Z :=
        (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hs.2) _).mp hyd
      have e : ⁅s * y, d⁆ = (s * ⁅y, d⁆ * s⁻¹) * ⁅s, d⁆ := by
        simp only [commutatorElement_def]
        group
      have hinv : (s * ⁅y, d⁆ * s⁻¹)⁻¹ * ⁅s * y, d⁆ = ⁅s, d⁆ := by
        rw [e]
        group
      rw [← hinv]
      exact Z.mul_mem (Z.inv_mem hconj) (hcommZ d hd)
    have hsQ : s ∈ Q := hc.LB_hom_inj_of_card D.hyp.width D.card_inf_QB hs hsdZ
    rw [hxy]
    exact Q.mul_mem hsQ hy
  · intro hxQ
    have h1 : AM.φ ⟨x, hc.LB_le_H0 x.2⟩ = 1 :=
      (AM.φ_ker ⟨x, hc.LB_le_H0 x.2⟩).mpr hxQ
    refine LinearMap.ext fun a => ?_
    have h2 : AM.φ ⟨x, hc.LB_le_H0 x.2⟩ a = a := by
      rw [h1]
      rfl
    apply Subtype.ext
    rw [LinearMap.zero_apply, D.delta_apply AM x a, h2, sub_self]
    rfl

theorem Sec108Data.exists_delta_eq (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z)
    (f : ↥(D.Asp AM) →ₗ[AM.K] ↥(D.Bsp AM))
    (hf : ∀ a : ↥(D.Asp AM), (a : AM.M₀.E) ∈ D.Bsp AM → f a = 0) :
    ∃ x : ↥(LB M Q B), D.delta AM x = f := by
  haveI : Module.Free AM.K AM.M₀.E := Module.Free.of_divisionRing AM.K AM.M₀.E
  obtain ⟨b, hbY, hb0, hB, -, hex, -⟩ :=
    Ctx.elation_package hc D.hyp.width D.hyp.n_gt D.hyp.noA2
      (card_LB_of_ctx D.h34 hc D.hyp.width D.hyp.n_gt D.hyp.noA2 D.hyp.gen).1
      D.card_inf_QB AM.glob (le_inf hc.le hc.B_le_QB) le_rfl (smul_mem_img_inf_QB D AM)
  obtain ⟨g, hgb⟩ := Module.Projective.exists_dual_eq_one AM.K hb0
  have hbBsp : (b : AM.M₀.E) ∈ D.Bsp AM :=
    (D.mem_Bsp AM).mpr ((hB b).mpr ⟨1, (one_smul AM.K b).symm⟩)
  set f' : Module.Dual AM.K ↥(D.Asp AM) := g.comp ((D.Bsp AM).subtype.comp f) with hf'def
  have hf'b : f' ⟨b, hbY⟩ = 0 := by
    have h0 : f ⟨b, hbY⟩ = 0 := hf ⟨b, hbY⟩ hbBsp
    rw [hf'def]
    simp only [LinearMap.comp_apply, Submodule.coe_subtype, h0, Submodule.coe_zero, map_zero]
  obtain ⟨l, hl, hexl⟩ := hex f' hf'b
  refine ⟨⟨l, hl⟩, ?_⟩
  ext a
  have hS : AM.φ ⟨l, hc.LB_le_H0 hl⟩ (a : AM.M₀.E) = (a : AM.M₀.E) + f' a • b :=
    hexl (AM.φ ⟨l, hc.LB_le_H0 hl⟩)
      (fun z hz => AM.φ_π ⟨l, hc.LB_le_H0 hl⟩ z hz) a
  rw [D.delta_apply AM ⟨l, hl⟩ a, hS]
  obtain ⟨c, hc'⟩ := (hB _).mp ((D.mem_Bsp AM).mp (f a).2)
  have hfc : f' a = c := by
    rw [hf'def]
    simp only [LinearMap.comp_apply, Submodule.coe_subtype]
    rw [hc', map_smul, hgb, smul_eq_mul, mul_one]
  rw [hfc, hc']
  abel

private theorem mem_range_nu_iff_mem_Ut (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {u : AM.M₀.E} :
    u ∈ LinearMap.range (D.nu AM) ↔ u ∈ AM.M₀.img (Ut Q Z t) := by
  have h : u ∈ (AM.M₀.img (Ut Q Z t) : Set AM.M₀.E) ↔
      u ∈ (LinearMap.range (D.nu AM) : Set AM.M₀.E) := by rw [D.img_Ut_eq AM]
  exact h.symm

private theorem range_nu_eq_range_sub_one (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) :
    LinearMap.range (D.nu AM) =
      LinearMap.range ((AM.φ ⟨t, D.t_mem_H0⟩ : AM.M₀.E →ₗ[AM.K] AM.M₀.E) - 1) := by
  have htM : t ∈ M := hc.LB_le_M D.good.1.mem_LB
  obtain ⟨htQ, htQ'⟩ := hc.conj_mem_Q_of_mem_M htM
  refine SetLike.ext fun v => ?_
  refine (mem_range_nu_iff_mem_Ut D AM).trans ?_
  rw [show Ut Q Z t = ⁅Q, Subgroup.zpowers t⁆ ⊔ Z from rfl]
  exact mem_img_comm_zpowers_sup_iff AM.M₀ AM.glob.reg (AM.φ ⟨t, D.t_mem_H0⟩) htQ htQ'
    (fun x hx => AM.φ_π ⟨t, D.t_mem_H0⟩ x hx) v

private theorem range_sub_one_eq_ker_sub_one (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) :
    LinearMap.range ((AM.φ ⟨t, D.t_mem_H0⟩ : AM.M₀.E →ₗ[AM.K] AM.M₀.E) - 1) =
      LinearMap.ker ((AM.φ ⟨t, D.t_mem_H0⟩ : AM.M₀.E →ₗ[AM.K] AM.M₀.E) - 1) := by
  have hsq : AM.φ ⟨t, D.t_mem_H0⟩ * AM.φ ⟨t, D.t_mem_H0⟩ = 1 := by
    rw [← map_mul, show (⟨t, D.t_mem_H0⟩ * ⟨t, D.t_mem_H0⟩ : ↥(H0 M Z)) = 1 by
      ext
      simpa using D.sit.x_sq, map_one]
  have hT2 : (AM.φ ⟨t, D.t_mem_H0⟩ : AM.M₀.E →ₗ[AM.K] AM.M₀.E) ∘ₗ
      (AM.φ ⟨t, D.t_mem_H0⟩ : AM.M₀.E →ₗ[AM.K] AM.M₀.E) = LinearMap.id := by
    ext e
    exact congrArg (fun g : AM.M₀.E ≃ₗ[AM.K] AM.M₀.E => g e) hsq
  have hle := Tim79.QuadModel.range_le_ker_of_sq_eq_one AM.M₀ hT2
  have hrange : Module.finrank AM.K
      (LinearMap.range ((AM.φ ⟨t, D.t_mem_H0⟩ : AM.M₀.E →ₗ[AM.K] AM.M₀.E) - 1)) = 6 := by
    rw [← range_nu_eq_range_sub_one D AM]
    exact D.finrank_range_nu AM
  have hker : Module.finrank AM.K
      (LinearMap.ker ((AM.φ ⟨t, D.t_mem_H0⟩ : AM.M₀.E →ₗ[AM.K] AM.M₀.E) - 1)) = 6 := by
    have hrn := LinearMap.finrank_range_add_finrank_ker
      ((AM.φ ⟨t, D.t_mem_H0⟩ : AM.M₀.E →ₗ[AM.K] AM.M₀.E) - 1)
    have hE := D.finrank_E AM
    omega
  exact Submodule.eq_of_le_of_finrank_eq hle (by rw [hrange, hker])

private theorem eq_smul_of_ker_le (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z)
    (f g : ↥(D.Asp AM) →ₗ[AM.K] ↥(D.Bsp AM)) {b : AM.M₀.E}
    (hb : ∀ v : AM.M₀.E, v ∈ AM.M₀.img B ↔ ∃ s : AM.K, v = s • b)
    (hb0 : b ≠ 0) (hg : g ≠ 0) (hker : LinearMap.ker g ≤ LinearMap.ker f) :
    ∃ c : AM.K, f = c • g := by
  haveI : Module.Free AM.K ↥(D.Bsp AM) := Module.Free.of_divisionRing AM.K ↥(D.Bsp AM)
  have hbB : (b : AM.M₀.E) ∈ D.Bsp AM := (D.mem_Bsp AM).mpr ((hb b).mpr ⟨1, (one_smul _ b).symm⟩)
  have hbne : (⟨b, hbB⟩ : ↥(D.Bsp AM)) ≠ 0 := fun h => hb0 (congrArg Subtype.val h)
  obtain ⟨gb, hgb⟩ := Module.Projective.exists_dual_eq_one AM.K hbne
  have hline : ∀ w : ↥(D.Bsp AM), ∃ s : AM.K, w = s • (⟨b, hbB⟩ : ↥(D.Bsp AM)) := by
    intro w
    obtain ⟨s, hs⟩ := (hb (w : AM.M₀.E)).mp ((D.mem_Bsp AM).mp w.2)
    exact ⟨s, Subtype.ext hs⟩
  have hginj : ∀ w : ↥(D.Bsp AM), gb w = 0 → w = 0 := by
    intro w hw
    obtain ⟨s, rfl⟩ := hline w
    rw [map_smul, hgb, smul_eq_mul, mul_one] at hw
    rw [hw, zero_smul]
  have hgone : gb.comp g ≠ 0 := by
    intro h
    apply hg
    ext a
    simpa using hginj _ (by simpa using LinearMap.congr_fun h a)
  have hker' : LinearMap.ker (gb.comp g) ≤ LinearMap.ker (gb.comp f) := by
    intro a ha
    rw [LinearMap.mem_ker] at ha ⊢
    have hga : g a = 0 := by
      apply hginj
      rwa [← LinearMap.comp_apply]
    have hfa : f a = 0 := hker (by rw [LinearMap.mem_ker]; exact hga)
    rw [LinearMap.comp_apply, hfa, map_zero]
  obtain ⟨c, hc⟩ : ∃ c : AM.K, gb.comp f = c • (gb.comp g) := by
    have h := mem_span_of_iInf_ker_le_ker (ι := Unit) (L := fun _ => gb.comp g) (K := gb.comp f)
      (by simpa using hker')
    rw [Set.range_const, Submodule.mem_span_singleton] at h
    obtain ⟨c, hc⟩ := h
    exact ⟨c, hc.symm⟩
  refine ⟨c, ?_⟩
  ext a
  have h1 := LinearMap.congr_fun hc a
  rw [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.comp_apply, smul_eq_mul] at h1
  obtain ⟨s, hs⟩ := hline (f a)
  obtain ⟨s', hs'⟩ := hline (g a)
  have h2 : gb (f a) = s := by rw [hs, map_smul, hgb, smul_eq_mul, mul_one]
  have h3 : gb (g a) = s' := by rw [hs', map_smul, hgb, smul_eq_mul, mul_one]
  rw [h2, h3] at h1
  simp only [LinearMap.smul_apply, Submodule.coe_smul, Submodule.coe_mk, hs, hs', h1, mul_smul]

theorem Sec108Data.root_fix_range_nu (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {y : G} (hy : y ∈ Y) {u : AM.M₀.E}
    (hu : u ∈ LinearMap.range (D.nu AM)) :
    AM.φ ⟨y, hc.LB_le_H0 (D.root_le_LB hy)⟩ u = u := by
  obtain ⟨w, hwUt, hwQ, rfl⟩ := (AM.M₀.mem_img).mp ((mem_range_nu_iff_mem_Ut D AM).mp hu)
  have hwC : w ∈ Q ⊓ Subgroup.centralizer ({t} : Set G) := by
    rw [D.inf_centralizer_eq]
    exact hwUt
  have hcomm : y * w = w * y :=
    Subgroup.mem_centralizer_iff.mp (D.inf_centralizer_le hwC) y hy
  rw [← AM.φ_π ⟨y, hc.LB_le_H0 (D.root_le_LB hy)⟩ w hwQ]
  congr 1
  rw [hcomm]
  group

theorem Sec108Data.mem_range_nu_iff (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) (a : ↥(D.Asp AM)) :
    (a : AM.M₀.E) ∈ LinearMap.range (D.nu AM) ↔
      D.delta AM ⟨t, D.good.1.mem_LB⟩ a = 0 := by
  have hfix : (a : AM.M₀.E) ∈ LinearMap.range (D.nu AM) ↔
      AM.φ ⟨t, D.t_mem_H0⟩ (a : AM.M₀.E) = (a : AM.M₀.E) := by
    rw [range_nu_eq_range_sub_one D AM, range_sub_one_eq_ker_sub_one D AM, LinearMap.mem_ker]
    constructor
    · intro h
      have h1 : (AM.φ ⟨t, D.t_mem_H0⟩ : AM.M₀.E →ₗ[AM.K] AM.M₀.E) (a : AM.M₀.E) -
          (a : AM.M₀.E) = 0 := by simpa using h
      exact sub_eq_zero.mp h1
    · intro h
      have h1 : (AM.φ ⟨t, D.t_mem_H0⟩ : AM.M₀.E →ₗ[AM.K] AM.M₀.E) (a : AM.M₀.E) -
          (a : AM.M₀.E) = 0 := sub_eq_zero.mpr h
      simpa using h1
  rw [hfix]
  constructor
  · intro h
    apply Subtype.ext
    rw [D.delta_apply AM ⟨t, D.good.1.mem_LB⟩ a]
    exact sub_eq_zero.mpr h
  · intro h
    have h1 := congrArg (fun z : ↥(D.Bsp AM) => (z : AM.M₀.E)) h
    rw [D.delta_apply AM ⟨t, D.good.1.mem_LB⟩ a] at h1
    exact sub_eq_zero.mp (by simpa using h1)

theorem Sec108Data.delta_t_ne_zero (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) :
    D.delta AM ⟨t, D.good.1.mem_LB⟩ ≠ 0 := by
  intro h
  exact D.good.1.2.2.1 ((D.delta_eq_zero_iff AM ⟨t, D.good.1.mem_LB⟩).mp h)

private theorem ker_delta_le_of_mem_root (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {y : G} (hy : y ∈ Y) :
    LinearMap.ker (D.delta AM ⟨t, D.good.1.mem_LB⟩) ≤
      LinearMap.ker (D.delta AM ⟨y, D.root_le_LB hy⟩) := by
  intro a ha
  rw [LinearMap.mem_ker] at ha ⊢
  have hV : (a : AM.M₀.E) ∈ LinearMap.range (D.nu AM) := (D.mem_range_nu_iff AM a).mpr ha
  have hfix := D.root_fix_range_nu AM hy hV
  apply Subtype.ext
  rw [D.delta_apply AM ⟨y, D.root_le_LB hy⟩ a, sub_eq_zero.mpr hfix]
  rfl

private theorem delta_injective_on_root (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {y₁ y₂ : G} (h₁ : y₁ ∈ Y) (h₂ : y₂ ∈ Y)
    (h : D.delta AM ⟨y₁, D.root_le_LB h₁⟩ = D.delta AM ⟨y₂, D.root_le_LB h₂⟩) : y₁ = y₂ := by
  have hneg : D.delta AM ⟨y₁, D.root_le_LB h₁⟩⁻¹ = - D.delta AM ⟨y₁, D.root_le_LB h₁⟩ := by
    have hone : D.delta AM (⟨y₁, D.root_le_LB h₁⟩⁻¹ * ⟨y₁, D.root_le_LB h₁⟩) = 0 :=
      (D.delta_eq_zero_iff AM _).mpr (by simpa using Q.one_mem)
    have hm := D.delta_mul AM ⟨y₁, D.root_le_LB h₁⟩⁻¹ ⟨y₁, D.root_le_LB h₁⟩
    rw [hone] at hm
    exact eq_neg_of_add_eq_zero_left hm.symm
  have hz0 : D.delta AM (⟨y₁, D.root_le_LB h₁⟩⁻¹ * ⟨y₂, D.root_le_LB h₂⟩) = 0 := by
    rw [D.delta_mul AM, hneg, h]
    abel
  have hzQ : y₁⁻¹ * y₂ ∈ Q := (D.delta_eq_zero_iff AM _).mp hz0
  have hz1 : y₁⁻¹ * y₂ = 1 := by
    have hbot : y₁⁻¹ * y₂ ∈ (⊥ : Subgroup G) := by
      rw [← (smith_1_12 D.sit).2]
      exact Subgroup.mem_inf.mpr ⟨Y.mul_mem (Y.inv_mem h₁) h₂, hzQ⟩
    simpa using hbot
  exact (by simpa using congrArg (fun t => y₁ * t) hz1 : y₂ = y₁).symm

private theorem smul_delta_mem_range_root (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) (c : AM.K) :
    c • D.delta AM ⟨t, D.good.1.mem_LB⟩ ∈
      Set.range (fun y : ↥Y => D.delta AM ⟨(y : G), D.root_le_LB y.2⟩) := by
  classical
  obtain ⟨b, hb0, -, hB, -, -⟩ := Ctx.dictB hc AM.glob
  set Φ : ↥Y → (↥(D.Asp AM) →ₗ[AM.K] ↥(D.Bsp AM)) :=
    fun y => D.delta AM ⟨(y : G), D.root_le_LB y.2⟩ with hΦ
  have hinj : Function.Injective Φ := fun y₁ y₂ h =>
    Subtype.ext (delta_injective_on_root D AM y₁.2 y₂.2 h)
  have hYcard : Nat.card ↥Y = Nat.card AM.K := by
    obtain ⟨g, hg⟩ := D.sit.conj
    rw [hg, card_conjSubgroup, ← AM.glob.card]
  have h1 : Nat.card (Set.range Φ) = Nat.card AM.K :=
    (Nat.card_congr (Equiv.ofInjective Φ hinj)).symm.trans hYcard
  have hline : Nat.card (Set.range (fun c : AM.K => c • D.delta AM ⟨t, D.good.1.mem_LB⟩)) =
      Nat.card AM.K := by
    have hset : (Submodule.span AM.K {D.delta AM ⟨t, D.good.1.mem_LB⟩} : Set _) =
        Set.range (fun c : AM.K => c • D.delta AM ⟨t, D.good.1.mem_LB⟩) := by
      ext w
      show w ∈ Submodule.span AM.K {D.delta AM ⟨t, D.good.1.mem_LB⟩} ↔
        ∃ c : AM.K, c • D.delta AM ⟨t, D.good.1.mem_LB⟩ = w
      rw [Submodule.mem_span_singleton]
    rw [← hset]
    exact (Nat.card_congr (LinearEquiv.toSpanNonzeroSingleton AM.K
      (↥(D.Asp AM) →ₗ[AM.K] ↥(D.Bsp AM)) _ (D.delta_t_ne_zero AM)).toEquiv).symm
  have hsub : Set.range Φ ⊆ Set.range (fun c : AM.K => c • D.delta AM ⟨t, D.good.1.mem_LB⟩) := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨c, hc⟩ := eq_smul_of_ker_le D AM _ _ hB hb0 (D.delta_t_ne_zero AM)
      (ker_delta_le_of_mem_root D AM y.2)
    exact ⟨c, hc.symm⟩
  have heq : Set.range Φ = Set.range (fun c : AM.K => c • D.delta AM ⟨t, D.good.1.mem_LB⟩) := by
    refine Set.eq_of_subset_of_ncard_le hsub ?_
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, hline, h1]
  rw [heq]
  exact ⟨c, rfl⟩

private theorem exists_smul_delta_of_fixes_range (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) (x : ↥(LB M Q B))
    (hfix : ∀ u ∈ LinearMap.range (D.nu AM), AM.φ ⟨x, hc.LB_le_H0 x.2⟩ u = u) :
    ∃ c : AM.K, D.delta AM x = c • D.delta AM ⟨t, D.good.1.mem_LB⟩ := by
  have hker : LinearMap.ker (D.delta AM ⟨t, D.good.1.mem_LB⟩) ≤
      LinearMap.ker (D.delta AM x) := by
    intro a ha
    rw [LinearMap.mem_ker] at ha ⊢
    have h := hfix (a : AM.M₀.E) ((D.mem_range_nu_iff AM a).mpr ha)
    apply Subtype.ext
    rw [D.delta_apply AM x a, h, sub_self]
    rfl
  obtain ⟨b, hb0, -, hB, -, -⟩ := Ctx.dictB hc AM.glob
  exact eq_smul_of_ker_le D AM _ _ hB hb0 (D.delta_t_ne_zero AM) hker

private theorem delta_inv_mul_mem_Q (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {y : G} (hy : y ∈ Y) {x : ↥(LB M Q B)}
    (h : D.delta AM ⟨y, D.root_le_LB hy⟩ = D.delta AM x) : y⁻¹ * (x : G) ∈ Q := by
  have hneg : D.delta AM ⟨y, D.root_le_LB hy⟩⁻¹ = - D.delta AM ⟨y, D.root_le_LB hy⟩ := by
    have hone : D.delta AM (⟨y, D.root_le_LB hy⟩⁻¹ * ⟨y, D.root_le_LB hy⟩) = 0 :=
      (D.delta_eq_zero_iff AM _).mpr (by simpa using Q.one_mem)
    have hm := D.delta_mul AM ⟨y, D.root_le_LB hy⟩⁻¹ ⟨y, D.root_le_LB hy⟩
    rw [hone] at hm
    exact eq_neg_of_add_eq_zero_left hm.symm
  have hz0 : D.delta AM (⟨y, D.root_le_LB hy⟩⁻¹ * x) = 0 := by
    rw [D.delta_mul AM, hneg, h]
    abel
  exact (D.delta_eq_zero_iff AM _).mp hz0

theorem Sec108Data.exists_root_delta_eq_iff (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z)
    (f : ↥(D.Asp AM) →ₗ[AM.K] ↥(D.Bsp AM)) :
    (∃ y : ↥(LB M Q B), (y : G) ∈ Y ∧ D.delta AM y = f) ↔
      ∃ c : AM.K, f = c • D.delta AM ⟨t, D.good.1.mem_LB⟩ := by
  constructor
  · rintro ⟨y, hyY, rfl⟩
    obtain ⟨b, hb0, -, hB, -, -⟩ := Ctx.dictB hc AM.glob
    exact eq_smul_of_ker_le D AM _ _ hB hb0 (D.delta_t_ne_zero AM)
      (ker_delta_le_of_mem_root D AM hyY)
  · rintro ⟨c, rfl⟩
    obtain ⟨y, hy⟩ := smul_delta_mem_range_root D AM c
    exact ⟨⟨(y : G), D.root_le_LB y.2⟩, y.2, hy⟩

theorem Sec108Data.fix_range_nu_iff (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) (x : ↥(LB M Q B)) :
    (∀ u ∈ LinearMap.range (D.nu AM), AM.φ ⟨x, hc.LB_le_H0 x.2⟩ u = u) ↔
      ∃ y ∈ Y, y⁻¹ * (x : G) ∈ Q := by
  constructor
  · intro hfix
    obtain ⟨c, hc⟩ := exists_smul_delta_of_fixes_range D AM x hfix
    obtain ⟨y, hyY, hy⟩ := (D.exists_root_delta_eq_iff AM _).mpr ⟨c, rfl⟩
    exact ⟨(y : G), hyY, delta_inv_mul_mem_Q D AM hyY (hy.trans hc.symm)⟩
  · rintro ⟨y, hyY, hyQ⟩ u hu
    have hL : y⁻¹ * (x : G) ∈ LB M Q B :=
      (LB M Q B).mul_mem ((LB M Q B).inv_mem (D.root_le_LB hyY)) x.2
    have hq' : AM.φ ⟨y⁻¹ * (x : G), hc.LB_le_H0 hL⟩ = 1 := (AM.φ_ker _).mpr hyQ
    have hEq : AM.φ ⟨x, hc.LB_le_H0 x.2⟩ = AM.φ ⟨y, hc.LB_le_H0 (D.root_le_LB hyY)⟩ := by
      have h1 : (⟨x, hc.LB_le_H0 x.2⟩ : ↥(H0 M Z)) =
          ⟨y, hc.LB_le_H0 (D.root_le_LB hyY)⟩ * ⟨y⁻¹ * (x : G), hc.LB_le_H0 hL⟩ := by
        ext
        show (x : G) = y * (y⁻¹ * (x : G))
        group
      rw [h1, map_mul, hq', mul_one]
    rw [hEq]
    exact D.root_fix_range_nu AM hyY hu

theorem Sec108Data.card_LB_inf_CN (D : Sec108Data hc t Y) :
    Nat.card ↥(LB M Q B ⊓ hc.CN t) = Nat.card Z ^ 3 * Nat.card Q := by
  obtain ⟨AM⟩ := Smith81.Smith23E1.ActionModel.nonempty hc.hyp
  have hVQB : Vt M (LB M Q B) B Z t ≤ QB B :=
    stroth310SL_of_34 D.h34 G M Q Z B hc 6 t
      (D.hyp.toSec5 D.good.1.mem_LB D.good.1.2.2.1) (SLMNat.toSLNat D.slm (by norm_num))
  have hY : ∀ (c : AM.K) (e : AM.M₀.E), e ∈ AM.M₀.img (Vt M (LB M Q B) B Z t) →
      c • e ∈ AM.M₀.img (Vt M (LB M Q B) B Z t) :=
    fun c e he => hc.smul_mem_img_Vt AM.glob t c he
  obtain ⟨-, -, -, -, -, -, hcount⟩ :=
    Ctx.elation_package hc D.hyp.width D.hyp.n_gt D.hyp.noA2
      (card_LB_of_ctx D.h34 hc D.hyp.width D.hyp.n_gt D.hyp.noA2 D.hyp.gen).1
      D.card_inf_QB AM.glob (hc.B_le_Vt D.good.1.mem_LB) (le_inf (hc.Vt_le_Q t) hVQB) hY
  have hT : ∀ x : G, x ∈ LB M Q B ⊓ hc.CN t ↔
      x ∈ LB M Q B ∧ ∀ y ∈ Vt M (LB M Q B) B Z t, ⁅x, y⁆ ∈ Z := by
    intro x
    rw [Subgroup.mem_inf, Ctx.mem_CN]
    exact ⟨fun h => ⟨h.1, h.2.2⟩,
      fun h => ⟨h.1, le_Rt (LB M Q B) (t := t) D.good.1.mem_LB h.1, h.2⟩⟩
  have hmain : Nat.card ↥(LB M Q B) = Nat.card ↥(LB M Q B ⊓ hc.CN t) * Nat.card Z ^ 2 := by
    have hfin : Module.finrank AM.K ↥(imgSub AM.M₀ (Vt M (LB M Q B) B Z t) hY) = 3 :=
      D.finrank_Vsp AM
    rw [hcount (LB M Q B ⊓ hc.CN t) hT, hfin, AM.glob.card]
  have heq : Nat.card ↥(LB M Q B ⊓ hc.CN t) * Nat.card Z ^ 2 = Nat.card Q * Nat.card Z ^ 5 := by
    rw [← hmain, (card_LB_of_ctx D.h34 hc D.hyp.width D.hyp.n_gt D.hyp.noA2 D.hyp.gen).1]
  have h2 : Nat.card ↥(LB M Q B ⊓ hc.CN t) * Nat.card Z ^ 2 =
      (Nat.card Z ^ 3 * Nat.card Q) * Nat.card Z ^ 2 := by
    rw [heq]
    ring
  exact Nat.eq_of_mul_eq_mul_right (pow_pos Nat.card_pos 2) h2

end CFSG.RankThree.GF2n.Stroth80
