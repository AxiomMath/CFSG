module

public import CFSG.LocalAnalysis.StandardType.GGQ2HypLin
public import CFSG.LocalAnalysis.StandardType.GGQ2HypStab
public import CFSG.LocalAnalysis.StandardType.GGWAutNormalizer
import CFSG.LocalAnalysis.StandardType.GGIndepFixLineStep2Defs
import CFSG.LocalAnalysis.StandardType.GGLargeDepRestrictAux

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {V ι : Type} [AddCommGroup V] [Module (ZMod 3) V]

theorem ggQ2Hyp_pm_of_stab (hK : GGReflClassOmegaInput)
    [Module.Finite (ZMod 3) V] [Nonempty ι] (A : Subgroup (V ≃ₗ[ZMod 3] V))
    (hTF : TransvectionFree A)
    (c : ι → V) (α : ι → Module.Dual (ZMod 3) V) (hαc : ∀ i, α i (c i) = 2)
    (s : ι → (V ≃ₗ[ZMod 3] V)) (hs : ∀ i v, s i v = v - α i v • c i) (hsR : ∀ i, s i ∈ reflGp A)
    (x : V) (hfix : ∀ z, (∀ i, α i z = 0) → z ∈ Submodule.span (ZMod 3) {x})
    (hconn : ∀ i j, Relation.ReflTransGen (fun a b => α a (c b) ≠ 0 ∧ α b (c a) ≠ 0) i j)
    (h5 : 5 ≤ Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range c)))
    (hhyp : Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range c)) + 1 =
      Module.finrank (ZMod 3) V)
    (hRH : ∀ r ∈ reflGp A, ∀ h ∈ Submodule.span (ZMod 3) (Set.range c),
      r h ∈ Submodule.span (ZMod 3) (Set.range c))
    (hRx : ¬ ∀ r ∈ reflGp A, r x ∈ Submodule.span (ZMod 3) {x}) :
    ∀ a ∈ A, ∃ r ∈ reflGp A, (∀ v, a v = r v) ∨ (∀ v, a v = -(r v)) := by
  classical
  let H : Submodule (ZMod 3) V := Submodule.span (ZMod 3) (Set.range c)
  let R : Subgroup (V ≃ₗ[ZMod 3] V) := reflGp A
  have h2 : 2 ≤ Module.finrank (ZMod 3) H := by
    change 2 ≤ Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range c))
    omega
  have h5H : 5 ≤ Module.finrank (ZMod 3) H := by
    change 5 ≤ Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range c))
    exact h5
  have hAstab : A ≤ ggLinStab H := by
    intro a ha
    constructor
    · intro v hv
      exact ggQ2Hyp_A_stab A c α s hs hsR x hfix hconn h2 hRH a ha v hv
    · intro v hv
      have h := ggQ2Hyp_A_stab A c α s hs hsR x hfix hconn h2 hRH a⁻¹ (A.inv_mem ha) v hv
      simpa using h
  have hR_le_A : R ≤ A := ggWAut_reflGp_le A
  have hRbar_mem : ∀ r (hr : r ∈ R),
      ggLinRestrictHom H ⟨r, hAstab (hR_le_A hr)⟩ ∈
        (R.subgroupOf (ggLinStab H)).map (ggLinRestrictHom H) := by
    intro r hr
    exact Subgroup.mem_map.mpr
      ⟨⟨r, hAstab (hR_le_A hr)⟩, Subgroup.mem_subgroupOf.mpr hr, rfl⟩
  have hRbar_conj : ∀ (b : V ≃ₗ[ZMod 3] V) (hb : b ∈ A)
      (rbar : ↥H ≃ₗ[ZMod 3] ↥H),
      rbar ∈ (R.subgroupOf (ggLinStab H)).map (ggLinRestrictHom H) →
      ggLinRestrictHom H ⟨b, hAstab hb⟩ * rbar *
        (ggLinRestrictHom H ⟨b, hAstab hb⟩)⁻¹ ∈
          (R.subgroupOf (ggLinStab H)).map (ggLinRestrictHom H) := by
    intro b hb rbar hrbar
    rw [Subgroup.mem_map] at hrbar ⊢
    obtain ⟨g, hg, rfl⟩ := hrbar
    refine ⟨(⟨b, hAstab hb⟩ : ↥(ggLinStab H)) * g *
      (⟨b, hAstab hb⟩ : ↥(ggLinStab H))⁻¹, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf] at hg ⊢
      have hmem : b * (g : V ≃ₗ[ZMod 3] V) * b⁻¹ ∈ R :=
        ggWAut_reflGp_conj A hb hg
      simpa using hmem
    · rw [map_mul, map_mul, map_inv]
  let Rbar : Subgroup (↥H ≃ₗ[ZMod 3] ↥H) :=
    (R.subgroupOf (ggLinStab H)).map (ggLinRestrictHom H)
  have hRbar_mem' : ∀ r (hr : r ∈ R),
      ggLinRestrictHom H ⟨r, hAstab (hR_le_A hr)⟩ ∈ Rbar := by
    intro r hr
    exact hRbar_mem r hr
  let cbar : ι → ↥H := fun i => ⟨c i, Submodule.subset_span (Set.mem_range_self i)⟩
  let sbar : ι → (↥H ≃ₗ[ZMod 3] ↥H) := fun i =>
    ggLinRestrictHom H ⟨s i, hAstab (hR_le_A (hsR i))⟩
  have hsbar_mem : ∀ i, sbar i ∈ Rbar := fun i => hRbar_mem' (s i) (hsR i)
  have hsbar_apply : ∀ (i : ι) (v : ↥H),
      sbar i v = v - (α i (v : V)) • cbar i := by
    intro i v
    apply Subtype.ext
    show (((ggLinRestrictHom H ⟨s i, hAstab (hR_le_A (hsR i))⟩) v : ↥H) : V) =
      ((v - (α i (v : V)) • cbar i : ↥H) : V)
    rw [l04fD2_restrict_apply]
    rw [hs i (v : V)]
    simp [cbar]
  have hspan : Submodule.span (ZMod 3) (Set.range cbar) = ⊤ := by
    have hmap : Submodule.map H.subtype (Submodule.span (ZMod 3) (Set.range cbar)) = H := by
      rw [Submodule.map_span]
      have hrange : H.subtype '' Set.range cbar = Set.range c := by
        ext v
        constructor
        · rintro ⟨x, ⟨i, rfl⟩, hx⟩
          exact ⟨i, hx⟩
        · rintro ⟨i, hi⟩
          exact ⟨cbar i, ⟨i, rfl⟩, hi⟩
      rw [hrange]
    have hmaptop : Submodule.map H.subtype (⊤ : Submodule (ZMod 3) ↥H) = H := by
      rw [Submodule.map_top]
      exact Submodule.range_subtype H
    refine Submodule.map_injective_of_injective H.subtype_injective ?_
    rw [hmap, hmaptop]
  have habs_irred : ∀ W : Submodule (ZMod 3) ↥H,
      (∀ a ∈ Rbar, ∀ w ∈ W, a w ∈ W) → W = ⊥ ∨ W = ⊤ := by
    intro W hW
    let U : Submodule (ZMod 3) V := W.map H.subtype
    have hUstab : ∀ r ∈ R, ∀ u ∈ U, r u ∈ U := by
      intro r hr u hu
      rw [Submodule.mem_map] at hu
      obtain ⟨w, hw, rfl⟩ := hu
      have hrM : r ∈ ggLinStab H := hAstab (hR_le_A hr)
      let rbar : ↥H ≃ₗ[ZMod 3] ↥H := ggLinRestrictHom H ⟨r, hrM⟩
      have hrbar : rbar ∈ Rbar := hRbar_mem' r hr
      have hmem : rbar w ∈ W := hW rbar hrbar w hw
      have hthis : H.subtype (rbar w) = r (H.subtype w) :=
        l04fD2_restrict_apply H ⟨r, hrM⟩ w
      rw [← hthis]
      exact Submodule.mem_map_of_mem hmem
    have hUdich : ∀ i, ∀ u ∈ U, α i u • c i ∈ U := by
      intro i u hu
      have h1 : s i ∈ R := hsR i
      have h2' := hUstab (s i) h1 u hu
      have heq : α i u • c i = u - s i u := by
        rw [hs i u]
        abel
      rw [heq]
      exact Submodule.sub_mem U hu h2'
    rcases ggQ2Mix_stable_dichotomy c α x hfix hconn U hUdich with hHU | hUx
    · right
      rw [eq_top_iff]
      intro w _
      have hw : (w : V) ∈ U := hHU w.2
      rw [Submodule.mem_map] at hw
      obtain ⟨w', hw', hw'eq⟩ := hw
      have hw'w : w' = w := Subtype.ext hw'eq
      simpa [hw'w] using hw'
    · left
      rw [eq_bot_iff]
      intro w hw
      rw [Submodule.mem_bot]
      by_contra hwn
      have hUne : U ≠ ⊥ := by
        intro hbot
        have hmemV : (w : V) ∈ U := Submodule.mem_map_of_mem hw
        rw [hbot] at hmemV
        rw [Submodule.mem_bot] at hmemV
        exact hwn (Subtype.ext hmemV)
      have hxU : x ∈ U := by
        obtain ⟨u, huU, hu0⟩ := (Submodule.ne_bot_iff U).mp hUne
        have hu_span : u ∈ Submodule.span (ZMod 3) {x} := hUx huU
        rw [Submodule.mem_span_singleton] at hu_span
        obtain ⟨a, ha⟩ := hu_span
        have ha0 : a ≠ 0 := by
          intro ha0
          apply hu0
          rw [← ha, ha0, zero_smul]
        have hx : x = a⁻¹ • u := by
          rw [← ha, smul_smul, inv_mul_cancel₀ ha0, one_smul]
        rw [hx]
        exact Submodule.smul_mem U _ huU
      exact hRx (fun r hr => hUx (hUstab r hr x hxU))
  have habs_comm : ∀ T : Module.End (ZMod 3) ↥H,
      (∀ a ∈ Rbar, T ∘ₗ (a : ↥H →ₗ[ZMod 3] ↥H) =
        (a : ↥H →ₗ[ZMod 3] ↥H) ∘ₗ T) →
        ∃ c : ZMod 3, T = c • LinearMap.id := by
    intro T hT
    obtain ⟨i₀⟩ := ‹Nonempty ι›
    have hTs : ∀ (i : ι) (v : ↥H), T (sbar i v) = sbar i (T v) := by
      intro i v
      have h := congrArg (fun f : Module.End (ZMod 3) ↥H => f v) (hT (sbar i) (hsbar_mem i))
      simpa [LinearMap.comp_apply] using h
    have hTs' : ∀ (i : ι) (v : ↥H),
        T (v - (α i (v : V)) • cbar i) =
          T v - (α i (((T v : ↥H) : V))) • cbar i := by
      intro i v
      have h := hTs i v
      rw [hsbar_apply i v, hsbar_apply i (T v)] at h
      exact h
    have hc_ne : ∀ i, cbar i ≠ 0 := by
      intro i hci0
      have hzero : α i (c i) = 0 := by
        have hci : c i = (cbar i : V) := rfl
        rw [hci, hci0]
        simp
      rw [hαc i] at hzero
      exact (by decide : (2 : ZMod 3) ≠ 0) hzero
    have hμ_exists : ∀ i, ∃ μ_i : ZMod 3, T (cbar i) = μ_i • cbar i := by
      intro i
      have hsi : cbar i - (α i ((cbar i : ↥H) : V)) • cbar i = - cbar i := by
        have hci : ((cbar i : ↥H) : V) = c i := rfl
        rw [hci, hαc i]
        module
      have h := hTs' i (cbar i)
      rw [hsi, map_neg] at h
      have h2' : (2 : ZMod 3) • T (cbar i) =
          (α i (((T (cbar i) : ↥H) : V))) • cbar i := by
        calc
          (2 : ZMod 3) • T (cbar i) = T (cbar i) + T (cbar i) := by rw [two_smul]
          _ = (T (cbar i) - (α i (((T (cbar i) : ↥H) : V))) • cbar i) +
                (α i (((T (cbar i) : ↥H) : V))) • cbar i + T (cbar i) := by abel
          _ = -T (cbar i) + (α i (((T (cbar i) : ↥H) : V))) • cbar i +
                T (cbar i) := by rw [← h]
          _ = (α i (((T (cbar i) : ↥H) : V))) • cbar i := by abel
      refine ⟨(2 : ZMod 3)⁻¹ * α i (((T (cbar i) : ↥H) : V)), ?_⟩
      calc
        T (cbar i) = (2 : ZMod 3)⁻¹ • ((2 : ZMod 3) • T (cbar i)) := by
          rw [smul_smul, inv_mul_cancel₀ (by decide : (2 : ZMod 3) ≠ 0), one_smul]
        _ = (2 : ZMod 3)⁻¹ • ((α i (((T (cbar i) : ↥H) : V))) • cbar i) := by rw [h2']
        _ = ((2 : ZMod 3)⁻¹ * α i (((T (cbar i) : ↥H) : V))) • cbar i := by
          rw [smul_smul]
    choose μ hμ using hμ_exists
    have hμ_edge : ∀ a b, α a (c b) ≠ 0 → α b (c a) ≠ 0 → μ a = μ b := by
      intro a b hab hba
      have h := hTs' b (cbar a)
      rw [map_sub, map_smul] at h
      have h1 : (α b (c a)) • T (cbar b) =
          (α b (((T (cbar a) : ↥H) : V))) • cbar b := by
        have h2' : -((α b (c a)) • T (cbar b)) =
            -((α b (((T (cbar a) : ↥H) : V))) • cbar b) := by
          calc
            -((α b (c a)) • T (cbar b)) =
                T (cbar a) - (α b (c a)) • T (cbar b) - T (cbar a) := by abel
            _ = T (cbar a) - (α b (((T (cbar a) : ↥H) : V))) • cbar b -
                  T (cbar a) := by rw [h]
            _ = -((α b (((T (cbar a) : ↥H) : V))) • cbar b) := by abel
        exact neg_inj.mp h2'
      rw [hμ b, hμ a] at h1
      simp only [smul_smul, map_smul, smul_eq_mul, Submodule.coe_smul] at h1
      have hzero : (α b (c a) * μ b - μ a * α b (c a)) • cbar b = 0 := by
        rw [sub_smul, h1, sub_self]
      have hscalar : α b (c a) * μ b - μ a * α b (c a) = 0 := by
        by_contra hne
        have hne' : (α b (c a) * μ b - μ a * α b (c a)) • cbar b ≠ 0 := by
          intro hz
          rw [smul_eq_zero] at hz
          rcases hz with h0 | h0
          · exact hne h0
          · exact hc_ne b h0
        exact hne' hzero
      have hcomm : α b (c a) * μ b = α b (c a) * μ a := by
        rw [mul_comm (μ a) (α b (c a))] at hscalar
        exact sub_eq_zero.mp hscalar
      exact (mul_left_cancel₀ hba hcomm).symm
    have hμ_const : ∀ i, μ i = μ i₀ := by
      intro i
      have hpath := hconn i₀ i
      induction hpath with
      | refl => rfl
      | tail hab hbc ih =>
          rename_i b d
          exact (hμ_edge b d hbc.1 hbc.2).symm.trans ih
    let μ₀ : ZMod 3 := μ i₀
    have hH : ∀ h ∈ Submodule.span (ZMod 3) (Set.range cbar), T h = μ₀ • h := by
      intro h hh
      apply Submodule.span_induction (p := fun x _ => T x = μ₀ • x) _ _ _ _ hh
      · rintro x ⟨i, rfl⟩
        rw [hμ i, hμ_const i]
      · simp
      · intro x y _ _ ihx ihy
        rw [map_add, ihx, ihy, smul_add]
      · intro a x _ ihx
        rw [map_smul, ihx, smul_smul, smul_smul, mul_comm a μ₀]
    refine ⟨μ₀, ?_⟩
    apply LinearMap.ext
    intro v
    have hv : v ∈ Submodule.span (ZMod 3) (Set.range cbar) := by
      rw [hspan]
      exact Submodule.mem_top
    rw [LinearMap.smul_apply, LinearMap.id_apply]
    exact hH v hv
  have hgen : Rbar = Subgroup.closure {r | r ∈ Rbar ∧ GGLinRefl r} := by
    apply le_antisymm
    · intro w hw
      change w ∈ (R.subgroupOf (ggLinStab H)).map (ggLinRestrictHom H) at hw
      rw [Subgroup.mem_map] at hw
      obtain ⟨g, hg, rfl⟩ := hw
      have hgR : (g : V ≃ₗ[ZMod 3] V) ∈ R := Subgroup.mem_subgroupOf.mp hg
      have hgR' : (g : V ≃ₗ[ZMod 3] V) ∈
          Subgroup.closure {t | t ∈ A ∧ IsReflLin t} := hgR
      refine Subgroup.closure_induction
        (p := fun x hx => ggLinRestrictHom H ⟨x, hAstab (hR_le_A hx)⟩ ∈
          Subgroup.closure {r | r ∈ Rbar ∧ GGLinRefl r})
        ?_ ?_ ?_ ?_ hgR'
      · rintro t ⟨htA, htRefl⟩
        refine Subgroup.subset_closure
          ⟨hRbar_mem' t (Subgroup.subset_closure ⟨htA, htRefl⟩), ?_⟩
        obtain ⟨c₀, φ, hφc, rfl⟩ := htRefl
        have hc0H : c₀ ∈ H := by
          have hmove := ggQ2Hyp_refl_move A hTF c α hαc s hs hsR x hfix hconn h2 hhyp hRH hRx
            (Module.reflection hφc) htA ⟨c₀, φ, hφc, rfl⟩ c₀
          have hc : Module.reflection hφc c₀ = -c₀ := by
            rw [Module.reflection_apply, hφc]
            module
          rw [hc] at hmove
          have hsum : (-2 : ZMod 3) • c₀ ∈ H := by
            convert hmove using 1
            module
          have hcoef : (-2 : ZMod 3) = 1 := by decide
          rwa [hcoef, one_smul] at hsum
        exact l04fD2_restrict_refl (p := 3) (by decide) H
          ⟨Module.reflection hφc,
            hAstab (hR_le_A (Subgroup.subset_closure ⟨htA, ⟨c₀, φ, hφc, rfl⟩⟩))⟩
          hc0H hφc (fun v => Module.reflection_apply v hφc)
      · have honeM : (⟨1, hAstab (hR_le_A (Subgroup.one_mem R))⟩ :
            ↥(ggLinStab H)) = 1 := by
          ext
          rfl
        rw [honeM, map_one]
        exact Subgroup.one_mem _
      · intro x y hx hy ihx ihy
        have hxy : (⟨x * y, hAstab (hR_le_A (Subgroup.mul_mem R hx hy))⟩ :
            ↥(ggLinStab H)) = ⟨x, hAstab (hR_le_A hx)⟩ *
              ⟨y, hAstab (hR_le_A hy)⟩ := by
          ext
          rfl
        rw [hxy, map_mul]
        exact Subgroup.mul_mem _ ihx ihy
      · intro x hx ih
        have hxinv : (⟨x⁻¹, hAstab (hR_le_A (Subgroup.inv_mem R hx))⟩ :
            ↥(ggLinStab H)) = (⟨x, hAstab (hR_le_A hx)⟩ : ↥(ggLinStab H))⁻¹ := by
          ext
          rfl
        rw [hxinv, map_inv]
        exact Subgroup.inv_mem _ ih
    · exact (Subgroup.closure_le Rbar).mpr (fun r hr => hr.1)
  have hneg : ∀ r ∈ Rbar, ¬ ∀ v, r v = -v := by
    intro r hr hneg_r
    change r ∈ (R.subgroupOf (ggLinStab H)).map (ggLinRestrictHom H) at hr
    rw [Subgroup.mem_map] at hr
    obtain ⟨g, hg, hg_eq⟩ := hr
    have hgR : (g : V ≃ₗ[ZMod 3] V) ∈ R := Subgroup.mem_subgroupOf.mp hg
    apply ggQ2Hyp_R_not_neg A hTF c α hαc s hs hsR x hfix hconn h2 hhyp hRH hRx
      (g : V ≃ₗ[ZMod 3] V) hgR
    intro h hh
    have h1 : ggLinRestrictHom H g ⟨h, hh⟩ = -⟨h, hh⟩ := by
      rw [hg_eq]
      exact hneg_r ⟨h, hh⟩
    have h2' : (((ggLinRestrictHom H g ⟨h, hh⟩ : ↥H) : V)) = -h := by
      rw [h1]
      rfl
    rwa [l04fD2_restrict_apply] at h2'
  have hnorm : ∀ a (ha : a ∈ A),
      ggLinRestrictHom H ⟨a, hAstab ha⟩ ∈
        Subgroup.normalizer (Rbar : Set (↥H ≃ₗ[ZMod 3] ↥H)) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro rbar
    constructor
    · intro hr
      exact hRbar_conj a ha rbar hr
    · intro hconj
      have h_inv : ggLinRestrictHom H ⟨a⁻¹, hAstab (A.inv_mem ha)⟩ =
          (ggLinRestrictHom H ⟨a, hAstab ha⟩)⁻¹ := by
        rw [← map_inv]
        rfl
      have hmem := hRbar_conj a⁻¹ (A.inv_mem ha)
        (ggLinRestrictHom H ⟨a, hAstab ha⟩ * rbar *
          (ggLinRestrictHom H ⟨a, hAstab ha⟩)⁻¹) hconj
      have heq : ggLinRestrictHom H ⟨a⁻¹, hAstab (A.inv_mem ha)⟩ *
          (ggLinRestrictHom H ⟨a, hAstab ha⟩ * rbar *
            (ggLinRestrictHom H ⟨a, hAstab ha⟩)⁻¹) *
          (ggLinRestrictHom H ⟨a⁻¹, hAstab (A.inv_mem ha)⟩)⁻¹ = rbar := by
        rw [h_inv]
        group
      rwa [heq] at hmem
  have habs : ZS.AbsIrred 3 Rbar := ⟨habs_irred, habs_comm⟩
  intro a ha
  let abar : ↥H ≃ₗ[ZMod 3] ↥H := ggLinRestrictHom H ⟨a, hAstab ha⟩
  have hnorm_a : abar ∈ Subgroup.normalizer (Rbar : Set (↥H ≃ₗ[ZMod 3] ↥H)) :=
    hnorm a ha
  obtain ⟨rbar, hrbar, hpm_rbar⟩ :=
    ggWAut_normalizer_pm hK (V := ↥H) h5H Rbar habs hgen hneg hnorm_a
  change rbar ∈ (R.subgroupOf (ggLinStab H)).map (ggLinRestrictHom H) at hrbar
  rw [Subgroup.mem_map] at hrbar
  obtain ⟨g, hg, hg_eq⟩ := hrbar
  have hgR : (g : V ≃ₗ[ZMod 3] V) ∈ R := Subgroup.mem_subgroupOf.mp hg
  refine ⟨(g : V ≃ₗ[ZMod 3] V), hgR, ?_⟩
  rcases hpm_rbar with hpm1 | hpm2
  · left
    have hfixH : ∀ h ∈ H, ((g : V ≃ₗ[ZMod 3] V)⁻¹ * a) h = h := by
      intro h hh
      have h1 : abar ⟨h, hh⟩ = rbar ⟨h, hh⟩ := hpm1 ⟨h, hh⟩
      have h3 : (((abar ⟨h, hh⟩ : ↥H) : V)) = (((rbar ⟨h, hh⟩ : ↥H) : V)) := by
        rw [h1]
      rw [l04fD2_restrict_apply, ← hg_eq, l04fD2_restrict_apply] at h3
      change (g : V ≃ₗ[ZMod 3] V)⁻¹ (a h) = h
      rw [h3]
      exact (g : V ≃ₗ[ZMod 3] V).symm_apply_apply h
    have hmemA : ((g : V ≃ₗ[ZMod 3] V)⁻¹ * a) ∈ A :=
      A.mul_mem (A.inv_mem (hR_le_A hgR)) ha
    have hone : ∀ v, ((g : V ≃ₗ[ZMod 3] V)⁻¹ * a) v = v :=
      ggQ2Hyp_one A hTF c α hαc s hs hsR x hfix hconn h2 hhyp hRH hRx
        ((g : V ≃ₗ[ZMod 3] V)⁻¹ * a) hmemA hfixH
    intro v
    have hv := hone v
    have h4 : (g : V ≃ₗ[ZMod 3] V)
        (((g : V ≃ₗ[ZMod 3] V)⁻¹ * a) v) = (g : V ≃ₗ[ZMod 3] V) v := by rw [hv]
    simpa using h4
  · right
    have hfixH : ∀ h ∈ H, ((g : V ≃ₗ[ZMod 3] V)⁻¹ * a) h = -h := by
      intro h hh
      have h1 : abar ⟨h, hh⟩ = -(rbar ⟨h, hh⟩) := hpm2 ⟨h, hh⟩
      have h3 : (((abar ⟨h, hh⟩ : ↥H) : V)) = ((-(rbar ⟨h, hh⟩) : ↥H) : V) := by
        rw [h1]
      rw [l04fD2_restrict_apply, Submodule.coe_neg, ← hg_eq,
        l04fD2_restrict_apply] at h3
      change (g : V ≃ₗ[ZMod 3] V)⁻¹ (a h) = -h
      rw [h3, map_neg]
      congr 1
      exact (g : V ≃ₗ[ZMod 3] V).symm_apply_apply h
    have hmemA : ((g : V ≃ₗ[ZMod 3] V)⁻¹ * a) ∈ A :=
      A.mul_mem (A.inv_mem (hR_le_A hgR)) ha
    have hneg1 : ∀ v, ((g : V ≃ₗ[ZMod 3] V)⁻¹ * a) v = -v :=
      ggQ2Hyp_neg A hTF c α hαc s hs hsR x hfix hconn h2 hhyp hRH hRx
        ((g : V ≃ₗ[ZMod 3] V)⁻¹ * a) hmemA hfixH
    intro v
    have hv := hneg1 v
    have h4 : (g : V ≃ₗ[ZMod 3] V)
        (((g : V ≃ₗ[ZMod 3] V)⁻¹ * a) v) = (g : V ≃ₗ[ZMod 3] V) (-v) := by rw [hv]
    simpa using h4

theorem ggQ2Hyp_pm (hK : GGReflClassOmegaInput)
    [Module.Finite (ZMod 3) V] [Nonempty ι] (A : Subgroup (V ≃ₗ[ZMod 3] V))
    (hTF : TransvectionFree A)
    (c : ι → V) (α : ι → Module.Dual (ZMod 3) V) (hαc : ∀ i, α i (c i) = 2)
    (s : ι → (V ≃ₗ[ZMod 3] V)) (hs : ∀ i v, s i v = v - α i v • c i) (hsR : ∀ i, s i ∈ reflGp A)
    (x : V) (hfix : ∀ z, (∀ i, α i z = 0) → z ∈ Submodule.span (ZMod 3) {x})
    (hconn : ∀ i j, Relation.ReflTransGen (fun a b => α a (c b) ≠ 0 ∧ α b (c a) ≠ 0) i j)
    (h5 : 5 ≤ Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range c)))
    (hhyp : Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range c)) + 1 =
      Module.finrank (ZMod 3) V)
    (hNotAbs : ¬ ZS.AbsIrred 3 (reflGp A)) :
    ∀ a ∈ A, ∃ r ∈ reflGp A, ∃ ε : ZMod 3, ε ≠ 0 ∧ a x = ε • r x := by
  have h2 : 2 ≤ Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range c)) := by omega
  by_cases hRxAll : ∀ r ∈ reflGp A, r x ∈ Submodule.span (ZMod 3) {x}
  · intro a ha
    have hline : a x ∈ Submodule.span (ZMod 3) {x} :=
      ggQ2Hyp_line_of_R A c α s hs hsR x hfix hconn h2 hRxAll a ha
    refine ⟨1, one_mem _, ?_⟩
    by_cases hx0 : x = 0
    · refine ⟨1, one_ne_zero, ?_⟩
      simp [hx0]
    · rw [Submodule.mem_span_singleton] at hline
      obtain ⟨ε, hε⟩ := hline
      refine ⟨ε, ?_, hε.symm⟩
      intro hε0
      apply hx0
      have hz : a x = 0 := by rw [← hε, hε0, zero_smul]
      exact a.injective (by rw [hz, map_zero])
  · by_cases hRH : ∀ r ∈ reflGp A, ∀ h ∈ Submodule.span (ZMod 3) (Set.range c),
        r h ∈ Submodule.span (ZMod 3) (Set.range c)
    · intro a ha
      obtain ⟨r, hr, hpm⟩ :=
        ggQ2Hyp_pm_of_stab hK A hTF c α hαc s hs hsR x hfix hconn h5 hhyp hRH hRxAll a ha
      rcases hpm with hpm | hpm
      · refine ⟨r, hr, 1, one_ne_zero, ?_⟩
        rw [hpm]
        simp
      · refine ⟨r, hr, -1, (by decide : (-1 : ZMod 3) ≠ 0), ?_⟩
        rw [hpm]
        simp
    · intro a ha
      exact absurd (ggQ2Hyp_absIrred A c α hαc s hs hsR x hfix hconn hhyp hRH hRxAll) hNotAbs

theorem ggQ2Hyp_pm_neg [Module.Finite (ZMod 3) V] [Nonempty ι] (A : Subgroup (V ≃ₗ[ZMod 3] V))
    (hTF : TransvectionFree A)
    (c : ι → V) (α : ι → Module.Dual (ZMod 3) V) (hαc : ∀ i, α i (c i) = 2)
    (s : ι → (V ≃ₗ[ZMod 3] V)) (hs : ∀ i v, s i v = v - α i v • c i) (hsR : ∀ i, s i ∈ reflGp A)
    (x : V) (hfix : ∀ z, (∀ i, α i z = 0) → z ∈ Submodule.span (ZMod 3) {x})
    (hconn : ∀ i j, Relation.ReflTransGen (fun a b => α a (c b) ≠ 0 ∧ α b (c a) ≠ 0) i j)
    (h2 : 2 ≤ Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range c)))
    (hhyp : Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range c)) + 1 =
      Module.finrank (ZMod 3) V)
    (hw : ∃ w ∈ reflGp A, ∀ h ∈ Submodule.span (ZMod 3) (Set.range c), w h = -h)
    (hNotAbs : ¬ ZS.AbsIrred 3 (reflGp A)) :
    ∀ a ∈ A, ∃ r ∈ reflGp A, ∃ ε : ZMod 3, ε ≠ 0 ∧ a x = ε • r x := by
  by_cases hRxAll : ∀ r ∈ reflGp A, r x ∈ Submodule.span (ZMod 3) {x}
  · intro a ha
    have hline : a x ∈ Submodule.span (ZMod 3) {x} :=
      ggQ2Hyp_line_of_R A c α s hs hsR x hfix hconn h2 hRxAll a ha
    refine ⟨1, one_mem _, ?_⟩
    by_cases hx0 : x = 0
    · refine ⟨1, one_ne_zero, ?_⟩
      simp [hx0]
    · rw [Submodule.mem_span_singleton] at hline
      obtain ⟨ε, hε⟩ := hline
      refine ⟨ε, ?_, hε.symm⟩
      intro hε0
      apply hx0
      have hz : a x = 0 := by rw [← hε, hε0, zero_smul]
      exact a.injective (by rw [hz, map_zero])
  · by_cases hRH : ∀ r ∈ reflGp A, ∀ h ∈ Submodule.span (ZMod 3) (Set.range c),
        r h ∈ Submodule.span (ZMod 3) (Set.range c)
    · obtain ⟨w, hwR, hwH⟩ := hw
      exact absurd hwH
        (ggQ2Hyp_R_not_neg A hTF c α hαc s hs hsR x hfix hconn h2 hhyp hRH hRxAll w hwR)
    · intro a ha
      exact absurd (ggQ2Hyp_absIrred A c α hαc s hs hsR x hfix hconn hhyp hRH hRxAll) hNotAbs

end CFSG.StandardType

end
