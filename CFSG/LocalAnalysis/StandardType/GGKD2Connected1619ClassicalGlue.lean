module

public import CFSG.LocalAnalysis.StandardType.GGKD2Connected1619Contracts
public import CFSG.LocalAnalysis.StandardType.GGTPNDefs
public import CFSG.LocalAnalysis.StandardType.GGTCJDivLin
public import CFSG.LocalAnalysis.StandardType.GGTCJDatum


public section

namespace S2MathAs3_1619Final

open CFSG CFSG.Assembly CFSG.StandardType S2MathAs3_1615
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)

private theorem ltrspg_fixSubgroup_conj {G : Type} [Group G] (x : G) :
    fixSubgroup (MulAut.conj x) = Subgroup.centralizer ({x} : Set G) := by
  ext h
  rw [mem_fixSubgroup, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hh
    rw [MulAut.conj_apply] at hh
    calc h * x = (x * h * x⁻¹) * x := by conv_lhs => rw [← hh]
      _ = x * h := by group
  · intro hh
    rw [MulAut.conj_apply]
    calc x * h * x⁻¹ = h * x * x⁻¹ := by rw [← hh]
      _ = h := by group

private theorem ltrspg_congr_eq_conj {R H : Type} [Group R] [Group H] (θ : R ≃* H)
    (β : MulAut R) (y : H) (hy : ∀ r : R, θ (β r) = y * θ r * y⁻¹) :
    MulAut.congr θ β = MulAut.conj y := by
  ext r
  rw [MulAut.conj_apply]
  show θ (β (θ.symm r)) = y * r * y⁻¹
  rw [hy (θ.symm r), θ.apply_symm_apply]

private noncomputable def ltrspg_quotCenterCongr {A B : Type} [Group A] [Group B]
    (e : A ≃* B) : A ⧸ Subgroup.center A ≃* B ⧸ Subgroup.center B :=
  QuotientGroup.congr (Subgroup.center A) (Subgroup.center B) e (by
    ext b
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact (mem_center_iff_of_mulEquiv e a).2 ha
    · intro hb
      exact ⟨e.symm b, (mem_center_iff_of_mulEquiv e _).1 (by simpa using hb), by simp⟩)

private theorem ltrspg_quotCenterCongr_mk {A B : Type} [Group A] [Group B]
    (e : A ≃* B) (a : A) :
    ltrspg_quotCenterCongr e (QuotientGroup.mk a) = QuotientGroup.mk (e a) := by
  rfl

private theorem ltrspg_eq_of_conj_eq {H : Type} [Group H]
    (hz : ∀ z : H, (∀ h : H, z * h = h * z) → z = 1)
    {a b : H} (hconj : MulAut.conj a = MulAut.conj b) : a = b := by
  have hcomm : ∀ g : H, (b⁻¹ * a) * g = g * (b⁻¹ * a) := by
    intro g
    have hg : a * g * a⁻¹ = b * g * b⁻¹ := by
      have := congrArg (fun f : MulAut H => f g) hconj
      simpa only [MulAut.conj_apply] using this
    have hg' : a * g = b * g * b⁻¹ * a := by
      calc a * g = (a * g * a⁻¹) * a := by group
        _ = (b * g * b⁻¹) * a := by rw [hg]
        _ = b * g * b⁻¹ * a := by group
    calc (b⁻¹ * a) * g = b⁻¹ * (a * g) := by group
      _ = b⁻¹ * (b * g * b⁻¹ * a) := by rw [hg']
      _ = g * (b⁻¹ * a) := by group
  have hz1 : b⁻¹ * a = 1 := hz _ hcomm
  calc a = b * (b⁻¹ * a) := by group
    _ = b := by rw [hz1, mul_one]

theorem QuotientInner.of_map {A B : Type} [Group A] [Group B]
    (e : A ≃* B) (C : Subgroup A) (γ : MulAut A) (δ : MulAut B)
    (hγδ : ∀ c : A, e (γ c) = δ (e c))
    (h : QuotientInner (C.map e.toMonoidHom) δ) : QuotientInner C γ := by
  obtain ⟨z', hz'⟩ := h
  let eC : ↥C ≃* ↥(C.map e.toMonoidHom) :=
    Subgroup.equivMapOfInjective C e.toMonoidHom e.injective
  let ebar : ↥C ⧸ Subgroup.center ↥C ≃*
      ↥(C.map e.toMonoidHom) ⧸ Subgroup.center ↥(C.map e.toMonoidHom) :=
    ltrspg_quotCenterCongr eC
  refine ⟨ebar.symm z', ?_⟩
  intro c c' hcc'
  have hδ : δ ((eC c : ↥(C.map e.toMonoidHom)) : B) =
      ((eC c' : ↥(C.map e.toMonoidHom)) : B) := by
    show δ (e (c : A)) = e (c' : A)
    rw [← hγδ (c : A), hcc']
  have hz'c := hz' (eC c) (eC c') hδ
  apply ebar.injective
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  rw [ltrspg_quotCenterCongr_mk, ltrspg_quotCenterCongr_mk]
  exact hz'c

theorem rawActionAt_of_model {R : Type} [Group R] {I : Set (MulAut R)} {H : Type} [Group H]
    (θ : R ≃* H) (hI : ∀ β ∈ I, ∃ y : H, ∀ r : R, θ (β r) = y * θ r * y⁻¹)
    (hH : ClassicalModelAction H) (hz : ∀ z : H, (∀ h : H, z * h = h * z) → z = 1) :
    RawActionAt R I := by
  intro φ hφI hφ1 hφ3 C hC hlab β hβI hβφ hβC
  obtain ⟨x, hx⟩ := hI φ hφI
  obtain ⟨y, hy⟩ := hI β hβI
  have hx1 : x ≠ 1 := by
    intro hxeq
    apply hφ1
    ext r
    apply θ.injective
    rw [hx r, hxeq]
    simp
  have hconjφ : MulAut.congr θ φ = MulAut.conj x := ltrspg_congr_eq_conj θ φ x hx
  have hconjβ : MulAut.congr θ β = MulAut.conj y := ltrspg_congr_eq_conj θ β y hy
  have hx3 : x ^ 3 = 1 := by
    have hconj3 : MulAut.conj (x ^ 3) = 1 := by
      have h1 : MulAut.congr θ (φ ^ 3) = MulAut.conj (x ^ 3) := by
        rw [map_pow (MulAut.congr θ) φ 3, hconjφ,
          ← map_pow (MulAut.conj : H →* MulAut H) x 3]
      rw [hφ3, map_one] at h1
      exact h1.symm
    apply hz
    intro h
    have hh : x ^ 3 * h * (x ^ 3)⁻¹ = h := by
      have := congrArg (fun f : MulAut H => f h) hconj3
      rw [MulAut.conj_apply] at this
      simpa using this
    calc x ^ 3 * h = (x ^ 3 * h * (x ^ 3)⁻¹) * x ^ 3 := by group
      _ = h * x ^ 3 := by rw [hh]
  have hCfix : IsComponentOf C (fixSubgroup φ) := by
    rwa [TCJ.tcj_ggFixSub_eq_fixSubgroup] at hC
  have hcomp : IsComponentOf (C.map θ.toMonoidHom) (Subgroup.centralizer ({x} : Set H)) := by
    have htrans := TCJ.tcjLin_component_transport θ φ hCfix
    rw [hconjφ, ltrspg_fixSubgroup_conj x] at htrans
    exact htrans
  have hlab' : GGHasLabel (⟨.A, 1, 3⟩ : LargeEvenLabel)
      (↥(C.map θ.toMonoidHom) ⧸ Subgroup.center ↥(C.map θ.toMonoidHom)) :=
    ggHasLabel_quotCenter_of_mulEquiv
      (Subgroup.equivMapOfInjective C θ.toMonoidHom θ.injective) hlab
  have hyC' : ∀ c ∈ C.map θ.toMonoidHom, MulAut.conj y c ∈ C.map θ.toMonoidHom := by
    intro c hc
    rw [Subgroup.mem_map] at hc ⊢
    obtain ⟨a, ha, rfl⟩ := hc
    refine ⟨β a, hβC a ha, ?_⟩
    rw [MulAut.conj_apply]
    exact hy a
  have hxy : x * y = y * x := by
    have hconjMul : MulAut.conj y * MulAut.conj x = MulAut.conj x * MulAut.conj y := by
      have h := congrArg (MulAut.congr θ) hβφ
      rw [map_mul, map_mul, hconjβ, hconjφ] at h
      exact h
    have hyx : y * x = x * y := by
      apply ltrspg_eq_of_conj_eq hz
      rw [map_mul (MulAut.conj : H →* MulAut H), map_mul (MulAut.conj : H →* MulAut H)]
      exact hconjMul
    exact hyx.symm
  have hy' : ∀ r : R, θ (β r) = MulAut.conj y (θ r) := by
    intro r
    rw [MulAut.conj_apply]
    exact hy r
  have hqi : QuotientInner (C.map θ.toMonoidHom) (MulAut.conj y) :=
    hH x hx1 hx3 (C.map θ.toMonoidHom) hcomp hlab' y hxy hyC'
  exact QuotientInner.of_map θ C β (MulAut.conj y) hy' hqi

end S2MathAs3_1619Final

end
