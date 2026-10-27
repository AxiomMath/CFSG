module

public import CFSG.Quasithin.Background.F2Equiv
import Mathlib.Tactic.Group

public section

namespace CFSG.Quasithin

universe u v w w'

namespace Amalgam

open Completion

section Setting

variable (D : Type u) [Preorder D] (Y : Type w) [Group Y]

structure XYSetting where
  Xd : D → Subgroup Y
  Yd : D → Subgroup Y
  mono_X : Monotone Xd
  mono_Y : Monotone Yd
  le : ∀ d, Xd d ≤ Yd d
  normal : ∀ d, ((Xd d).subgroupOf (Yd d)).Normal
  gen_Y : ⨆ d, Yd d = ⊤
  least : D
  least_le : ∀ d, least ≤ d

end Setting

namespace XYSetting

variable {D : Type u} [Preorder D] {Y : Type w} [Group Y] (S : XYSetting D Y)

abbrev alpha : Amalgam.{u, w} D := ofSubgroups S.Xd S.mono_X

abbrev gamma : Amalgam.{u, w} D := ofSubgroups S.Yd S.mono_Y

theorem conj_mem {d : D} {y : Y} (hy : y ∈ S.Yd d) {x : Y} (hx : x ∈ S.Xd d) :
    y * x * y⁻¹ ∈ S.Xd d := by
  have h := (S.normal d).conj_mem ⟨x, S.le d hx⟩ (Subgroup.mem_subgroupOf.mpr hx) ⟨y, hy⟩
  exact Subgroup.mem_subgroupOf.mp h

theorem conj_inv_mem {d : D} {y : Y} (hy : y ∈ S.Yd d) {x : Y} (hx : x ∈ S.Xd d) :
    y⁻¹ * x * y ∈ S.Xd d := by
  have := S.conj_mem ((S.Yd d).inv_mem hy) hx
  simpa using this

@[expose] def conjX (d : D) (y : S.Yd d) : MulAut (S.Xd d) where
  toFun x := ⟨y * x * y⁻¹, S.conj_mem y.2 x.2⟩
  invFun x := ⟨y⁻¹ * x * y, S.conj_inv_mem y.2 x.2⟩
  left_inv x := Subtype.ext (by simp [mul_assoc])
  right_inv x := Subtype.ext (by simp [mul_assoc])
  map_mul' x x' := Subtype.ext (by simp [mul_assoc])

@[expose] def cAut (y : S.Yd S.least) : Aut S.alpha :=
  ⟨fun d => S.conjX d ⟨y, S.mono_Y (S.least_le d) y.2⟩, fun {_ _} _ _ => Subtype.ext rfl⟩

theorem cAut_apply_coe (y : S.Yd S.least) (d : D) (x : S.Xd d) :
    (((S.cAut y).1 d x : S.Xd d) : Y) = y * x * y⁻¹ := rfl

@[expose] def c : S.Yd S.least →* Aut S.alpha where
  toFun := S.cAut
  map_one' := by
    apply Subtype.ext
    funext d
    ext x
    show (1 : Y) * x * (1 : Y)⁻¹ = x
    simp
  map_mul' y y' := by
    apply Subtype.ext
    funext d
    ext x
    show ((y * y' : S.Yd S.least) : Y) * x * ((y * y' : S.Yd S.least) : Y)⁻¹ =
      (y : Y) * ((y' : Y) * x * (y' : Y)⁻¹) * (y : Y)⁻¹
    simp [mul_assoc]

theorem hatPi_c (x : S.Xd S.least) :
    hatPi (S.c ⟨x, S.le _ x.2⟩) = MulAut.conj (ξ S.alpha S.least x) := by
  apply MulEquiv.ext
  intro g
  have h : (hatPi (S.c ⟨x, S.le _ x.2⟩)).toMonoidHom =
      ((MulAut.conj (ξ S.alpha S.least x)).toMonoidHom) := by
    refine hom_ext fun d z => ?_
    show hatPi (S.c ⟨x, S.le _ x.2⟩) (ξ S.alpha d z) =
      ξ S.alpha S.least x * ξ S.alpha d z * (ξ S.alpha S.least x)⁻¹
    rw [hatPi_ξ]
    have hx : ξ S.alpha S.least x = ξ S.alpha d (S.alpha.map (S.least_le d) x) :=
      (ξ_map (α := S.alpha) (S.least_le d) x).symm
    have e : (S.c ⟨x, S.le _ x.2⟩).1 d z =
        S.alpha.map (S.least_le d) x * z * (S.alpha.map (S.least_le d) x)⁻¹ := rfl
    rw [hx, e, map_mul, map_mul, map_inv]
  exact congrArg (fun f => f g) h

section Completions

variable {G : Type w'} [Group G]

theorem c_mem_stabilizer (μ : Completion S.alpha G) (x : S.Xd S.least) :
    S.c ⟨x, S.le _ x.2⟩ ∈ stabilizer μ := by
  rw [mem_stabilizer, isEquivalent_act_iff, hatPi_c]
  have hN : μ.hat.ker.Normal := inferInstance
  ext z
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨k, hk, rfl⟩
    show ξ S.alpha S.least x * k * (ξ S.alpha S.least x)⁻¹ ∈ μ.hat.ker
    exact hN.conj_mem k hk _
  · intro hz
    refine ⟨(ξ S.alpha S.least x)⁻¹ * z * ξ S.alpha S.least x, ?_, ?_⟩
    · have := hN.conj_mem z hz (ξ S.alpha S.least x)⁻¹
      simpa using this
    · show ξ S.alpha S.least x * ((ξ S.alpha S.least x)⁻¹ * z * ξ S.alpha S.least x) *
        (ξ S.alpha S.least x)⁻¹ = z
      group

theorem piMinus_c (μ : Completion S.alpha G) (x : S.Xd S.least) :
    piMinus μ ⟨S.c ⟨x, S.le _ x.2⟩, S.c_mem_stabilizer μ x⟩ = MulAut.conj (μ.toHom S.least x) := by
  apply mulAut_ext (μ := μ)
  intro d z
  rw [piMinus_apply, MulAut.conj_apply]
  have hx : μ.toHom S.least x = μ.toHom d (S.alpha.map (S.least_le d) x) := (μ.comm _ x).symm
  have e : (S.c ⟨x, S.le _ x.2⟩).1 d z =
      S.alpha.map (S.least_le d) x * z * (S.alpha.map (S.least_le d) x)⁻¹ := rfl
  rw [hx, e, map_mul, map_mul, map_inv]

end Completions

section Lemma211

variable {G : Type w'} [Group G]

structure Hyp211 (μ : Completion S.alpha G) : Prop where
  faithful : μ.IsFaithful
  stab : ∀ y : S.Yd S.least, S.c y ∈ stabilizer μ
  inter_trivial :
    (⨅ d, (Subgroup.centralizer (S.Xd d : Set Y)).subgroupOf (S.Yd S.least)) = ⊥
  factor : ∀ d, ∀ g ∈ S.Yd d, ∃ y ∈ S.Yd S.least, ∃ x ∈ S.Xd d, g = y * x
  inter : ∀ d, S.Yd S.least ⊓ S.Xd d = S.Xd S.least

theorem mulAut_mul_conj_mul_inv (φ : MulAut G) (g : G) :
    φ * MulAut.conj g * φ⁻¹ = MulAut.conj (φ g) := by
  ext x
  simp [MulAut.conj_apply]

variable {S}

namespace Hyp211

variable {μ : Completion S.alpha G} (h : S.Hyp211 μ)

noncomputable def piC : S.Yd S.least →* MulAut G :=
  (piMinus μ).comp (S.c.codRestrict (stabilizer μ) h.stab)

theorem piC_X (x : S.Xd S.least) :
    h.piC ⟨x, S.le _ x.2⟩ = MulAut.conj (μ.toHom S.least x) :=
  S.piMinus_c μ x

theorem piC_apply (y : S.Yd S.least) (d : D) (z : S.Xd d) :
    h.piC y (μ.toHom d z) = μ.toHom d ((S.cAut y).1 d z) :=
  piMinus_apply μ ⟨S.c y, h.stab y⟩ d z

include h in
theorem exists_decomp (d : D) (g : S.Yd d) :
    ∃ (y : S.Yd S.least) (x : S.Xd d), (y : Y) * (x : Y) = (g : Y) := by
  obtain ⟨y, hy, x, hx, hg⟩ := h.factor d g g.2
  exact ⟨⟨y, hy⟩, ⟨x, hx⟩, hg.symm⟩

theorem decomp_eq (d : D) {y y' : S.Yd S.least} {x x' : S.Xd d}
    (hxy : (y : Y) * (x : Y) = (y' : Y) * (x' : Y)) :
    h.piC y * MulAut.conj (μ.toHom d x) = h.piC y' * MulAut.conj (μ.toHom d x') := by
  have hw : (y' : Y)⁻¹ * (y : Y) ∈ S.Xd S.least := by
    have h1 : (y' : Y)⁻¹ * (y : Y) = (x' : Y) * (x : Y)⁻¹ := by
      calc (y' : Y)⁻¹ * (y : Y) = (y' : Y)⁻¹ * ((y : Y) * (x : Y)) * (x : Y)⁻¹ := by group
        _ = (y' : Y)⁻¹ * ((y' : Y) * (x' : Y)) * (x : Y)⁻¹ := by rw [hxy]
        _ = (x' : Y) * (x : Y)⁻¹ := by group
    have hmem : (y' : Y)⁻¹ * (y : Y) ∈ S.Yd S.least ⊓ S.Xd d :=
      ⟨(S.Yd S.least).mul_mem ((S.Yd S.least).inv_mem y'.2) y.2, by
        rw [h1]; exact (S.Xd d).mul_mem x'.2 ((S.Xd d).inv_mem x.2)⟩
    rw [h.inter d] at hmem
    exact hmem
  obtain ⟨w, hw'⟩ : ∃ w : S.Xd S.least, (w : Y) = (y' : Y)⁻¹ * (y : Y) := ⟨⟨_, hw⟩, rfl⟩
  have hy : y = y' * ⟨(w : Y), S.le _ w.2⟩ := by
    apply Subtype.ext
    show (y : Y) = (y' : Y) * (w : Y)
    rw [hw']
    group
  have hx' : x' = S.alpha.map (S.least_le d) w * x := by
    apply Subtype.ext
    show (x' : Y) = (w : Y) * (x : Y)
    rw [hw']
    calc (x' : Y) = (y' : Y)⁻¹ * ((y' : Y) * (x' : Y)) := by group
      _ = (y' : Y)⁻¹ * ((y : Y) * (x : Y)) := by rw [hxy]
      _ = ((y' : Y)⁻¹ * (y : Y)) * (x : Y) := by group
  subst hy hx'
  have hμ : μ.toHom S.least w = μ.toHom d (S.alpha.map (S.least_le d) w) := (μ.comm _ w).symm
  rw [map_mul, h.piC_X w, hμ, map_mul (μ.toHom d), map_mul MulAut.conj, mul_assoc]

@[expose] noncomputable def G0 : Subgroup (MulAut G) :=
  (MulAut.conj : G →* MulAut G).range ⊔ h.piC.range

noncomputable def etaFun (d : D) (g : S.Yd d) : MulAut G :=
  h.piC (Classical.choose (h.exists_decomp d g)) *
    MulAut.conj (μ.toHom d (Classical.choose (Classical.choose_spec (h.exists_decomp d g))))

theorem etaFun_eq (d : D) (g : S.Yd d) (y : S.Yd S.least) (x : S.Xd d)
    (hg : (y : Y) * (x : Y) = (g : Y)) :
    h.etaFun d g = h.piC y * MulAut.conj (μ.toHom d x) :=
  h.decomp_eq d ((Classical.choose_spec (Classical.choose_spec (h.exists_decomp d g))).trans hg.symm)

theorem etaFun_one (d : D) : h.etaFun d 1 = 1 := by
  rw [h.etaFun_eq d 1 1 1 (by simp)]
  simp

theorem etaFun_mul (d : D) (g g' : S.Yd d) :
    h.etaFun d (g * g') = h.etaFun d g * h.etaFun d g' := by
  obtain ⟨y, x, hg⟩ := h.exists_decomp d g
  obtain ⟨y', x', hg'⟩ := h.exists_decomp d g'
  have hy'd : (y' : Y) ∈ S.Yd d := S.mono_Y (S.least_le d) y'.2
  let a : S.Xd d := ⟨(y' : Y)⁻¹ * x * y', S.conj_inv_mem hy'd x.2⟩
  have hgg' : ((y * y' : S.Yd S.least) : Y) * ((a * x' : S.Xd d) : Y) = ((g * g' : S.Yd d) : Y) := by
    show (y : Y) * (y' : Y) * (((y' : Y)⁻¹ * x * y') * x') = (g : Y) * (g' : Y)
    rw [← hg, ← hg']
    group
  rw [h.etaFun_eq d (g * g') (y * y') (a * x') hgg', h.etaFun_eq d g y x hg,
    h.etaFun_eq d g' y' x' hg']
  have key : h.piC y' * MulAut.conj (μ.toHom d a) = MulAut.conj (μ.toHom d x) * h.piC y' := by
    have h1 := mulAut_mul_conj_mul_inv (h.piC y') (μ.toHom d a)
    have h2 : h.piC y' (μ.toHom d a) = μ.toHom d x := by
      rw [h.piC_apply]
      congr 1
      apply Subtype.ext
      show (y' : Y) * ((y' : Y)⁻¹ * x * y') * (y' : Y)⁻¹ = x
      group
    rw [h2, mul_inv_eq_iff_eq_mul] at h1
    exact h1
  rw [map_mul h.piC, map_mul (μ.toHom d), map_mul MulAut.conj]
  calc h.piC y * h.piC y' * (MulAut.conj (μ.toHom d a) * MulAut.conj (μ.toHom d x'))
      = h.piC y * (h.piC y' * MulAut.conj (μ.toHom d a)) * MulAut.conj (μ.toHom d x') := by
        simp only [mul_assoc]
    _ = h.piC y * (MulAut.conj (μ.toHom d x) * h.piC y') * MulAut.conj (μ.toHom d x') := by
        rw [key]
    _ = _ := by simp only [mul_assoc]

@[expose] noncomputable def eta (d : D) : S.Yd d →* MulAut G where
  toFun := h.etaFun d
  map_one' := h.etaFun_one d
  map_mul' := h.etaFun_mul d

theorem eta_apply (d : D) (g : S.Yd d) : h.eta d g = h.etaFun d g := rfl

theorem eta_mem_G0 (d : D) (g : S.Yd d) : h.eta d g ∈ h.G0 := by
  obtain ⟨y, x, hg⟩ := h.exists_decomp d g
  rw [eta_apply, h.etaFun_eq d g y x hg]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ⟨y, rfl⟩) (Subgroup.mem_sup_left ⟨_, rfl⟩)

theorem eta_apply_X (d : D) (x : S.Xd d) :
    h.eta d ⟨x, S.le d x.2⟩ = MulAut.conj (μ.toHom d x) := by
  rw [eta_apply, h.etaFun_eq d _ 1 x (by simp)]
  simp

theorem eta_apply_least (y : S.Yd S.least) : h.eta S.least y = h.piC y := by
  rw [eta_apply, h.etaFun_eq S.least y y 1 (by simp)]
  simp

theorem eta_map {d d' : D} (hd : d ≤ d') (g : S.Yd d) :
    h.eta d' (S.gamma.map hd g) = h.eta d g := by
  obtain ⟨y, x, hg⟩ := h.exists_decomp d g
  rw [eta_apply, eta_apply, h.etaFun_eq d' (S.gamma.map hd g) y (S.alpha.map hd x) hg,
    h.etaFun_eq d g y x hg, μ.comm]

theorem range_iSup_eta : (⨆ d, (h.eta d).range) = h.G0 := by
  apply le_antisymm
  · exact iSup_le fun d => by
      rintro _ ⟨g, rfl⟩
      exact h.eta_mem_G0 d g
  · refine sup_le ?_ ?_
    · rw [MonoidHom.range_eq_map, ← μ.gen, Subgroup.map_iSup]
      refine iSup_le fun d => ?_
      rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
      refine le_iSup (fun d => (h.eta d).range) d ?_
      exact ⟨⟨x, S.le d x.2⟩, h.eta_apply_X d x⟩
    · rintro _ ⟨y, rfl⟩
      refine le_iSup (fun d => (h.eta d).range) S.least ?_
      exact ⟨y, h.eta_apply_least y⟩

end Hyp211

end Lemma211

end XYSetting

namespace Completion

variable {D : Type u} [Preorder D] {α : Amalgam.{u, v} D} {G : Type w'} [Group G]

abbrev inn (G : Type w') [Group G] : Subgroup (MulAut G) := (MulAut.conj : G →* MulAut G).range

@[expose] noncomputable def innComp (μ : Completion α G) : Completion α (inn G) where
  toHom d := ((MulAut.conj : G →* MulAut G).comp (μ.toHom d)).codRestrict (inn G)
    (fun x => MonoidHom.mem_range.mpr ⟨μ.toHom d x, rfl⟩)
  comm := fun {d e} hd x => Subtype.ext (by
    show MulAut.conj (μ.toHom e (α.map hd x)) = MulAut.conj (μ.toHom d x)
    rw [μ.comm])
  gen := by
    refine Subgroup.map_injective (f := (inn G).subtype) (inn G).subtype_injective ?_
    rw [Subgroup.map_iSup, Subgroup.map_top, Subgroup.range_subtype]
    have : ∀ d, ((((MulAut.conj : G →* MulAut G).comp (μ.toHom d)).codRestrict (inn G)
        (fun x => MonoidHom.mem_range.mpr ⟨μ.toHom d x, rfl⟩)).range.map (inn G).subtype) =
        (μ.toHom d).range.map (MulAut.conj : G →* MulAut G) := by
      intro d
      ext z
      constructor
      · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
        exact ⟨μ.toHom d x, ⟨x, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
        exact ⟨_, ⟨x, rfl⟩, rfl⟩
    simp only [this]
    rw [← Subgroup.map_iSup, μ.gen]
    exact (MonoidHom.range_eq_map _).symm

theorem innComp_apply (μ : Completion α G) (d : D) (x : α.X d) :
    ((μ.innComp.toHom d x : inn G) : MulAut G) = MulAut.conj (μ.toHom d x) := rfl

theorem conj_eq_one_iff {g : G} : MulAut.conj g = 1 ↔ g ∈ Subgroup.center G := by
  rw [Subgroup.mem_center_iff]
  constructor
  · intro h x
    have := congrArg (fun φ : MulAut G => φ x) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc x * g = (g * x * g⁻¹) * g := by rw [this]
      _ = g * x := by group
  · intro h
    ext x
    simp only [MulAut.conj_apply, MulAut.one_apply]
    rw [← h x]
    group

theorem innComp_injective_iff (μ : Completion α G) :
    (∀ d, Function.Injective (μ.innComp.toHom d)) ↔
      ∀ d (x : α.X d), μ.toHom d x ∈ Subgroup.center G → x = 1 := by
  constructor
  · intro h d x hx
    refine (injective_iff_map_eq_one (μ.innComp.toHom d)).mp (h d) x ?_
    apply Subtype.ext
    exact (conj_eq_one_iff).mpr hx
  · intro h d
    rw [injective_iff_map_eq_one]
    intro x hx
    apply h d x
    rw [← conj_eq_one_iff]
    exact congrArg Subtype.val hx

theorem isEquivalent_innComp (μ : Completion α G) (hZ : Subgroup.center G = ⊥) :
    IsEquivalent μ μ.innComp := by
  have hinj : Function.Injective (MulAut.conj : G →* MulAut G) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have := (conj_eq_one_iff).mp hg
    rwa [hZ, Subgroup.mem_bot] at this
  refine ⟨MonoidHom.ofInjective hinj, fun d x => ?_⟩
  apply Subtype.ext
  exact MonoidHom.ofInjective_apply hinj

end Completion

namespace XYSetting

variable {D : Type u} [Preorder D] {Y : Type w} [Group Y] {S : XYSetting D Y}
  {G : Type w'} [Group G]

namespace Hyp211

variable {μ : Completion S.alpha G} (h : S.Hyp211 μ)

theorem eta_injective
    (hC : ∀ d, ∀ g ∈ S.Yd d, g ∈ Subgroup.centralizer (S.Xd d : Set Y) → g ∈ S.Xd d)
    (hZ : ∀ d (x : S.Xd d), μ.toHom d x ∈ Subgroup.center G → x = 1) (d : D) :
    Function.Injective (h.eta d) := by
  rw [injective_iff_map_eq_one]
  intro g hg0
  obtain ⟨y, x, hgdec⟩ := h.exists_decomp d g
  have hg : h.piC y * MulAut.conj (μ.toHom d x) = 1 := by
    rw [← h.etaFun_eq d g y x hgdec]
    exact hg0
  have hcent : (g : Y) ∈ Subgroup.centralizer (S.Xd d : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have h1 := congrArg (fun φ : MulAut G => φ (μ.toHom d ⟨z, hz⟩)) hg
    simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.one_apply] at h1
    rw [← map_inv, ← map_mul, ← map_mul, h.piC_apply] at h1
    have h2 := h.faithful d h1
    have h3 : (y : Y) * ((x : Y) * z * (x : Y)⁻¹) * (y : Y)⁻¹ = z := congrArg Subtype.val h2
    rw [← hgdec]
    calc z * ((y : Y) * (x : Y)) = ((y : Y) * ((x : Y) * z * (x : Y)⁻¹) * (y : Y)⁻¹) *
          ((y : Y) * (x : Y)) := by rw [h3]
      _ = (y : Y) * (x : Y) * z := by group
  have hgX := hC d g g.2 hcent
  have e : (⟨((⟨g, hgX⟩ : S.Xd d) : Y), S.le d hgX⟩ : S.Yd d) = g := Subtype.ext rfl
  have h4 := h.eta_apply_X d ⟨g, hgX⟩
  rw [e, hg0] at h4
  have h5 : μ.toHom d ⟨g, hgX⟩ ∈ Subgroup.center G := (Completion.conj_eq_one_iff).mp h4.symm
  have h6 := hZ d ⟨g, hgX⟩ h5
  apply Subtype.ext
  have h7 := congrArg Subtype.val h6
  exact h7

end Hyp211

end XYSetting

end Amalgam

end CFSG.Quasithin
