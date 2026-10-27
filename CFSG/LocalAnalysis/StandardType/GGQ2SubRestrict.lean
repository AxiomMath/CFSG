module

public import CFSG.LocalAnalysis.StandardType.GGQ2SubStab
public import CFSG.LocalAnalysis.StandardType.GGWAutNormalizer
import CFSG.LocalAnalysis.StandardType.GGIndepFixLineStep2Defs
import CFSG.LocalAnalysis.StandardType.GGLargeDepRestrictAux

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {V ι : Type} [AddCommGroup V] [Module (ZMod 3) V]

private theorem ggQ2Sub_inv_mem_of_map_le {a : V ≃ₗ[ZMod 3] V} {U : Submodule (ZMod 3) V}
    (h : U ≤ Submodule.map (a : V →ₗ[ZMod 3] V) U) {u : V} (hu : u ∈ U) : a.symm u ∈ U := by
  obtain ⟨w, hw, hwv⟩ := Submodule.mem_map.mp (h hu)
  rw [← hwv]
  simpa using hw

private theorem ggQ2Sub_mem_of_map_inv_le {a : V ≃ₗ[ZMod 3] V} {U : Submodule (ZMod 3) V}
    (h : U ≤ Submodule.map (a.symm : V →ₗ[ZMod 3] V) U) {u : V} (hu : u ∈ U) : a u ∈ U := by
  obtain ⟨w, hw, hwv⟩ := Submodule.mem_map.mp (h hu)
  rw [← hwv]
  simpa using hw

theorem ggQ2Sub_pm_of_stab (hK : GGReflClassOmegaInput) [Module.Finite (ZMod 3) V] [Nonempty ι]
    (A : Subgroup (V ≃ₗ[ZMod 3] V)) (hTF : TransvectionFree A)
    (c : ι → V) (α : ι → Module.Dual (ZMod 3) V) (hαc : ∀ i, α i (c i) = 2)
    (s : ι → (V ≃ₗ[ZMod 3] V)) (hs : ∀ i v, s i v = v - α i v • c i) (hsR : ∀ i, s i ∈ reflGp A)
    (x : V) (hfix : ∀ z, (∀ i, α i z = 0) → z ∈ Submodule.span (ZMod 3) {x})
    (hxfix : ∀ i, α i x = 0)
    (hconn : ∀ i j, Relation.ReflTransGen (fun a b => α a (c b) ≠ 0 ∧ α b (c a) ≠ 0) i j)
    (h2 : 2 ≤ Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range c)))
    (U : Submodule (ZMod 3) V) (hHU : Submodule.span (ZMod 3) (Set.range c) ≤ U) (hUtop : U ≠ ⊤)
    (h5 : 5 ≤ Module.finrank (ZMod 3) U)
    (hRU : ∀ r ∈ reflGp A, ∀ u ∈ U, r u ∈ U)
    (hmin : ∀ W : Submodule (ZMod 3) V, (∀ r ∈ reflGp A, ∀ w ∈ W, r w ∈ W) →
      Submodule.span (ZMod 3) (Set.range c) ≤ W → W ≤ U → W = U)
    (hRx : ¬ ∀ r ∈ reflGp A, r x ∈ Submodule.span (ZMod 3) {x}) :
    ∀ a ∈ A, ∃ r ∈ reflGp A, ∃ ε : ZMod 3, ε ≠ 0 ∧ a x = ε • r x := by
  classical
  let H : Submodule (ZMod 3) V := Submodule.span (ZMod 3) (Set.range c)
  let R : Subgroup (V ≃ₗ[ZMod 3] V) := reflGp A
  have hR_le_A : R ≤ A := ggWAut_reflGp_le A
  have hkey : ∀ b ∈ A, U ≤ Submodule.map (b : V →ₗ[ZMod 3] V) U := by
    intro b hb
    let W' : Submodule (ZMod 3) V := Submodule.map (b : V →ₗ[ZMod 3] V) U
    have hW'stab : ∀ r ∈ R, ∀ w ∈ W', r w ∈ W' := by
      intro r hr w hw
      obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hw
      have hconj : b⁻¹ * r * b ∈ R := ggWAut_reflGp_conj A (A.inv_mem hb) hr
      have hmem : (b⁻¹ * r * b) u ∈ U := hRU (b⁻¹ * r * b) hconj u hu
      refine Submodule.mem_map.mpr ⟨(b⁻¹ * r * b) u, hmem, ?_⟩
      simp only [LinearEquiv.coe_toLinearMap]
      rw [← LinearEquiv.mul_apply, show b * (b⁻¹ * r * b) = r * b by group,
        LinearEquiv.mul_apply]
    have hW's : ∀ i, ∀ w ∈ W', α i w • c i ∈ W' := by
      intro i w hw
      have h1 : s i w ∈ W' := hW'stab (s i) (hsR i) w hw
      have hsub : α i w • c i = w - s i w := by rw [hs i w]; abel
      rw [hsub]
      exact W'.sub_mem hw h1
    have hW'fin : Module.finrank (ZMod 3) W' = Module.finrank (ZMod 3) U :=
      LinearEquiv.finrank_map_eq b U
    rcases ggQ2Mix_stable_dichotomy c α x hfix hconn W' hW's with hHW' | hW'x
    · have hstab : ∀ r ∈ reflGp A, ∀ w ∈ W' ⊓ U, r w ∈ W' ⊓ U := by
        intro r hr w hw
        obtain ⟨hwW', hwU⟩ := Submodule.mem_inf.mp hw
        exact Submodule.mem_inf.mpr ⟨hW'stab r hr w hwW', hRU r hr w hwU⟩
      have hHWinf : H ≤ W' ⊓ U := le_inf hHW' hHU
      have hWU : W' ⊓ U = U := hmin _ hstab hHWinf inf_le_right
      show U ≤ W'
      rw [← hWU]
      exact inf_le_left
    · exfalso
      have hle : Module.finrank (ZMod 3) W' ≤ 1 := by
        have h1 : Module.finrank (ZMod 3) W' ≤
            Module.finrank (ZMod 3) (Submodule.span (ZMod 3) {x}) :=
          Submodule.finrank_mono hW'x
        have hxle : Module.finrank (ZMod 3) (Submodule.span (ZMod 3) {x}) ≤ 1 := by
          simpa using finrank_span_le_card (R := ZMod 3) ({x} : Set V)
        omega
      omega
  have hAstab : A ≤ ggLinStab U := by
    intro a ha
    constructor
    · intro v hv
      exact ggQ2Sub_mem_of_map_inv_le (hkey a⁻¹ (A.inv_mem ha)) hv
    · intro v hv
      exact ggQ2Sub_inv_mem_of_map_le (hkey a ha) hv
  have hRbar_mem : ∀ r (hr : r ∈ R),
      ggLinRestrictHom U ⟨r, hAstab (hR_le_A hr)⟩ ∈
        (R.subgroupOf (ggLinStab U)).map (ggLinRestrictHom U) := by
    intro r hr
    exact Subgroup.mem_map.mpr
      ⟨⟨r, hAstab (hR_le_A hr)⟩, Subgroup.mem_subgroupOf.mpr hr, rfl⟩
  have hRbar_conj : ∀ (b : V ≃ₗ[ZMod 3] V) (hb : b ∈ A)
      (rbar : ↥U ≃ₗ[ZMod 3] ↥U),
      rbar ∈ (R.subgroupOf (ggLinStab U)).map (ggLinRestrictHom U) →
      ggLinRestrictHom U ⟨b, hAstab hb⟩ * rbar *
        (ggLinRestrictHom U ⟨b, hAstab hb⟩)⁻¹ ∈
          (R.subgroupOf (ggLinStab U)).map (ggLinRestrictHom U) := by
    intro b hb rbar hrbar
    rw [Subgroup.mem_map] at hrbar ⊢
    obtain ⟨g, hg, rfl⟩ := hrbar
    refine ⟨(⟨b, hAstab hb⟩ : ↥(ggLinStab U)) * g *
      (⟨b, hAstab hb⟩ : ↥(ggLinStab U))⁻¹, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf] at hg ⊢
      have hmem : b * (g : V ≃ₗ[ZMod 3] V) * b⁻¹ ∈ R :=
        ggWAut_reflGp_conj A hb hg
      simpa using hmem
    · rw [map_mul, map_mul, map_inv]
  let Rbar : Subgroup (↥U ≃ₗ[ZMod 3] ↥U) :=
    (R.subgroupOf (ggLinStab U)).map (ggLinRestrictHom U)
  have hRbar_mem' : ∀ r (hr : r ∈ R),
      ggLinRestrictHom U ⟨r, hAstab (hR_le_A hr)⟩ ∈ Rbar := by
    intro r hr
    exact hRbar_mem r hr
  let cbar : ι → ↥U := fun i => ⟨c i, hHU (Submodule.subset_span (Set.mem_range_self i))⟩
  let sbar : ι → (↥U ≃ₗ[ZMod 3] ↥U) := fun i =>
    ggLinRestrictHom U ⟨s i, hAstab (hR_le_A (hsR i))⟩
  have hsbar_mem : ∀ i, sbar i ∈ Rbar := fun i => hRbar_mem' (s i) (hsR i)
  have hsbar_apply : ∀ (i : ι) (v : ↥U),
      sbar i v = v - (α i (v : V)) • cbar i := by
    intro i v
    apply Subtype.ext
    show (((ggLinRestrictHom U ⟨s i, hAstab (hR_le_A (hsR i))⟩) v : ↥U) : V) =
      ((v - (α i (v : V)) • cbar i : ↥U) : V)
    rw [l04fD2_restrict_apply]
    rw [hs i (v : V)]
    simp [cbar]
  have habs_irred : ∀ W : Submodule (ZMod 3) ↥U,
      (∀ a ∈ Rbar, ∀ w ∈ W, a w ∈ W) → W = ⊥ ∨ W = ⊤ := by
    intro W hW
    let Z : Submodule (ZMod 3) V := W.map U.subtype
    have hZstab : ∀ r ∈ R, ∀ z ∈ Z, r z ∈ Z := by
      intro r hr z hz
      rw [Submodule.mem_map] at hz
      obtain ⟨w, hw, rfl⟩ := hz
      have hrM : r ∈ ggLinStab U := hAstab (hR_le_A hr)
      let rbar : ↥U ≃ₗ[ZMod 3] ↥U := ggLinRestrictHom U ⟨r, hrM⟩
      have hrbar : rbar ∈ Rbar := hRbar_mem' r hr
      have hmem : rbar w ∈ W := hW rbar hrbar w hw
      have hthis : U.subtype (rbar w) = r (U.subtype w) :=
        l04fD2_restrict_apply U ⟨r, hrM⟩ w
      rw [← hthis]
      exact Submodule.mem_map_of_mem hmem
    have hZdich : ∀ i, ∀ z ∈ Z, α i z • c i ∈ Z := by
      intro i z hz
      have h1 : s i ∈ R := hsR i
      have h2' := hZstab (s i) h1 z hz
      have heq : α i z • c i = z - s i z := by
        rw [hs i z]
        abel
      rw [heq]
      exact Submodule.sub_mem Z hz h2'
    have hZUle : Z ≤ U := by
      intro z hz
      obtain ⟨w, -, rfl⟩ := Submodule.mem_map.mp hz
      exact w.2
    rcases ggQ2Mix_stable_dichotomy c α x hfix hconn Z hZdich with hHZ | hZx
    · right
      have hZU : Z = U := hmin Z hZstab hHZ hZUle
      rw [eq_top_iff]
      intro w _
      have hw : (w : V) ∈ Z := by
        rw [hZU]
        exact w.2
      rw [Submodule.mem_map] at hw
      obtain ⟨w', hw', hw'eq⟩ := hw
      have hw'w : w' = w := Subtype.ext hw'eq
      simpa [hw'w] using hw'
    · left
      rw [eq_bot_iff]
      intro w hw
      rw [Submodule.mem_bot]
      by_contra hwn
      have hZne : Z ≠ ⊥ := by
        intro hbot
        have hmemV : (w : V) ∈ Z := Submodule.mem_map_of_mem hw
        rw [hbot] at hmemV
        rw [Submodule.mem_bot] at hmemV
        exact hwn (Subtype.ext hmemV)
      have hxZ : x ∈ Z := by
        obtain ⟨z, hzZ, hz0⟩ := (Submodule.ne_bot_iff Z).mp hZne
        have hz_span : z ∈ Submodule.span (ZMod 3) {x} := hZx hzZ
        rw [Submodule.mem_span_singleton] at hz_span
        obtain ⟨a, ha⟩ := hz_span
        have ha0 : a ≠ 0 := by
          intro ha0
          apply hz0
          rw [← ha, ha0, zero_smul]
        have hx : x = a⁻¹ • z := by
          rw [← ha, smul_smul, inv_mul_cancel₀ ha0, one_smul]
        rw [hx]
        exact Submodule.smul_mem Z _ hzZ
      exact hRx (fun r hr => hZx (hZstab r hr x hxZ))
  have habs_comm : ∀ T : Module.End (ZMod 3) ↥U,
      (∀ a ∈ Rbar, T ∘ₗ (a : ↥U →ₗ[ZMod 3] ↥U) =
        (a : ↥U →ₗ[ZMod 3] ↥U) ∘ₗ T) →
        ∃ c : ZMod 3, T = c • LinearMap.id := by
    intro T hT
    obtain ⟨i₀⟩ := ‹Nonempty ι›
    have hTs : ∀ (i : ι) (v : ↥U), T (sbar i v) = sbar i (T v) := by
      intro i v
      have h := congrArg (fun f : Module.End (ZMod 3) ↥U => f v) (hT (sbar i) (hsbar_mem i))
      simpa [LinearMap.comp_apply] using h
    have hTs' : ∀ (i : ι) (v : ↥U),
        T (v - (α i (v : V)) • cbar i) =
          T v - (α i (((T v : ↥U) : V))) • cbar i := by
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
      have hsi : cbar i - (α i ((cbar i : ↥U) : V)) • cbar i = - cbar i := by
        have hci : ((cbar i : ↥U) : V) = c i := rfl
        rw [hci, hαc i]
        module
      have h := hTs' i (cbar i)
      rw [hsi, map_neg] at h
      have h2' : (2 : ZMod 3) • T (cbar i) =
          (α i (((T (cbar i) : ↥U) : V))) • cbar i := by
        calc
          (2 : ZMod 3) • T (cbar i) = T (cbar i) + T (cbar i) := by rw [two_smul]
          _ = (T (cbar i) - (α i (((T (cbar i) : ↥U) : V))) • cbar i) +
                (α i (((T (cbar i) : ↥U) : V))) • cbar i + T (cbar i) := by abel
          _ = -T (cbar i) + (α i (((T (cbar i) : ↥U) : V))) • cbar i +
                T (cbar i) := by rw [← h]
          _ = (α i (((T (cbar i) : ↥U) : V))) • cbar i := by abel
      refine ⟨(2 : ZMod 3)⁻¹ * α i (((T (cbar i) : ↥U) : V)), ?_⟩
      calc
        T (cbar i) = (2 : ZMod 3)⁻¹ • ((2 : ZMod 3) • T (cbar i)) := by
          rw [smul_smul, inv_mul_cancel₀ (by decide : (2 : ZMod 3) ≠ 0), one_smul]
        _ = (2 : ZMod 3)⁻¹ • ((α i (((T (cbar i) : ↥U) : V))) • cbar i) := by rw [h2']
        _ = ((2 : ZMod 3)⁻¹ * α i (((T (cbar i) : ↥U) : V))) • cbar i := by
          rw [smul_smul]
    choose μ hμ using hμ_exists
    have hμ_edge : ∀ a b, α a (c b) ≠ 0 → α b (c a) ≠ 0 → μ a = μ b := by
      intro a b hab hba
      have h := hTs' b (cbar a)
      rw [map_sub, map_smul] at h
      have h1 : (α b (c a)) • T (cbar b) =
          (α b (((T (cbar a) : ↥U) : V))) • cbar b := by
        have h2' : -((α b (c a)) • T (cbar b)) =
            -((α b (((T (cbar a) : ↥U) : V))) • cbar b) := by
          calc
            -((α b (c a)) • T (cbar b)) =
                T (cbar a) - (α b (c a)) • T (cbar b) - T (cbar a) := by abel
            _ = T (cbar a) - (α b (((T (cbar a) : ↥U) : V))) • cbar b -
                  T (cbar a) := by rw [h]
            _ = -((α b (((T (cbar a) : ↥U) : V))) • cbar b) := by abel
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
    let K : Submodule (ZMod 3) ↥U := LinearMap.ker (T - μ₀ • LinearMap.id)
    have hspanK : Submodule.span (ZMod 3) (Set.range cbar) ≤ K := by
      intro h hh
      rw [LinearMap.mem_ker]
      rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
      exact hH h hh
    have hKstab : ∀ r ∈ Rbar, ∀ v ∈ K, r v ∈ K := by
      intro r hr v hv
      rw [LinearMap.mem_ker] at hv ⊢
      have hcomm : T (r v) = r (T v) := by
        have h := LinearMap.congr_fun (hT r hr) v
        simpa [LinearMap.comp_apply] using h
      rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
      have hv' : T v = μ₀ • v := by
        have h := sub_eq_zero.mp hv
        simpa using h
      rw [hcomm, hv', map_smul]
      exact sub_self _
    have hKmapstab : ∀ r ∈ R, ∀ w ∈ Submodule.map U.subtype K,
        r w ∈ Submodule.map U.subtype K := by
      intro r hr w hw
      obtain ⟨k, hk, rfl⟩ := Submodule.mem_map.mp hw
      have hrM : r ∈ ggLinStab U := hAstab (hR_le_A hr)
      let rbar : ↥U ≃ₗ[ZMod 3] ↥U := ggLinRestrictHom U ⟨r, hrM⟩
      have hrbar : rbar ∈ Rbar := hRbar_mem' r hr
      have hmem : rbar k ∈ K := hKstab rbar hrbar k hk
      exact Submodule.mem_map.mpr
        ⟨rbar k, hmem, l04fD2_restrict_apply U ⟨r, hrM⟩ k⟩
    have hHK : H ≤ Submodule.map U.subtype K := by
      have hmap : Submodule.map U.subtype (Submodule.span (ZMod 3) (Set.range cbar)) =
          Submodule.span (ZMod 3) (Set.range c) := by
        rw [Submodule.map_span]
        have hrange : U.subtype '' Set.range cbar = Set.range c := by
          ext v
          constructor
          · rintro ⟨x, ⟨i, rfl⟩, hx⟩
            exact ⟨i, hx⟩
          · rintro ⟨i, hi⟩
            exact ⟨cbar i, ⟨i, rfl⟩, hi⟩
        rw [hrange]
      rw [show H = Submodule.span (ZMod 3) (Set.range c) from rfl, ← hmap]
      exact Submodule.map_mono hspanK
    have hUle : Submodule.map U.subtype K ≤ U := by
      intro w hw
      obtain ⟨k, -, rfl⟩ := Submodule.mem_map.mp hw
      exact k.2
    have hKeq : Submodule.map U.subtype K = U := hmin _ hKmapstab hHK hUle
    have hKtop : K = ⊤ := by
      refine Submodule.map_injective_of_injective U.subtype_injective ?_
      rw [hKeq, Submodule.map_top, Submodule.range_subtype]
    refine ⟨μ₀, ?_⟩
    apply LinearMap.ext
    intro v
    have hv : v ∈ K := by
      rw [hKtop]
      exact Submodule.mem_top
    rw [LinearMap.mem_ker] at hv
    rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at hv
    simpa using hv
  have hgen : Rbar = Subgroup.closure {r | r ∈ Rbar ∧ GGLinRefl r} := by
    apply le_antisymm
    · intro w hw
      change w ∈ (R.subgroupOf (ggLinStab U)).map (ggLinRestrictHom U) at hw
      rw [Subgroup.mem_map] at hw
      obtain ⟨g, hg, rfl⟩ := hw
      have hgR : (g : V ≃ₗ[ZMod 3] V) ∈ R := Subgroup.mem_subgroupOf.mp hg
      have hgR' : (g : V ≃ₗ[ZMod 3] V) ∈
          Subgroup.closure {t | t ∈ A ∧ IsReflLin t} := hgR
      refine Subgroup.closure_induction
        (p := fun x hx => ggLinRestrictHom U ⟨x, hAstab (hR_le_A hx)⟩ ∈
          Subgroup.closure {r | r ∈ Rbar ∧ GGLinRefl r})
        ?_ ?_ ?_ ?_ hgR'
      · rintro t ⟨htA, htRefl⟩
        have htR : t ∈ R := Subgroup.subset_closure ⟨htA, htRefl⟩
        refine Subgroup.subset_closure ⟨hRbar_mem' t htR, ?_⟩
        obtain ⟨c₀, φ, hφc, rfl⟩ := htRefl
        have hc0U : c₀ ∈ U :=
          ggQ2Sub_refl_centre A hTF c α hαc s hs hsR x hfix U hHU hRU hRx hφc
            (ggWAut_reflGp_le A htR)
        exact l04fD2_restrict_refl (p := 3) (by decide) U
          ⟨Module.reflection hφc, hAstab (hR_le_A htR)⟩ hc0U hφc
          (fun v => Module.reflection_apply v hφc)
      · have honeM : (⟨1, hAstab (hR_le_A (Subgroup.one_mem R))⟩ :
            ↥(ggLinStab U)) = 1 := by
          ext
          rfl
        rw [honeM, map_one]
        exact Subgroup.one_mem _
      · intro x y hx hy ihx ihy
        have hxy : (⟨x * y, hAstab (hR_le_A (Subgroup.mul_mem R hx hy))⟩ :
            ↥(ggLinStab U)) = ⟨x, hAstab (hR_le_A hx)⟩ *
              ⟨y, hAstab (hR_le_A hy)⟩ := by
          ext
          rfl
        rw [hxy, map_mul]
        exact Subgroup.mul_mem _ ihx ihy
      · intro x hx ih
        have hxinv : (⟨x⁻¹, hAstab (hR_le_A (Subgroup.inv_mem R hx))⟩ :
            ↥(ggLinStab U)) = (⟨x, hAstab (hR_le_A hx)⟩ : ↥(ggLinStab U))⁻¹ := by
          ext
          rfl
        rw [hxinv, map_inv]
        exact Subgroup.inv_mem _ ih
    · exact (Subgroup.closure_le Rbar).mpr (fun r hr => hr.1)
  have hneg : ∀ r ∈ Rbar, ¬ ∀ v, r v = -v := by
    intro r hr hneg_r
    change r ∈ (R.subgroupOf (ggLinStab U)).map (ggLinRestrictHom U) at hr
    rw [Subgroup.mem_map] at hr
    obtain ⟨g, hg, hg_eq⟩ := hr
    have hgR : (g : V ≃ₗ[ZMod 3] V) ∈ R := Subgroup.mem_subgroupOf.mp hg
    apply ggQ2Sub_not_neg A hTF c α hαc s hs hsR x hfix hxfix hconn h2 U hHU hUtop hRU hRx
      (g : V ≃ₗ[ZMod 3] V) hgR
    intro u hu
    have h1 : ggLinRestrictHom U g ⟨u, hu⟩ = -⟨u, hu⟩ := by
      rw [hg_eq]
      exact hneg_r ⟨u, hu⟩
    have h2' : (((ggLinRestrictHom U g ⟨u, hu⟩ : ↥U) : V)) = -u := by
      rw [h1]
      rfl
    rwa [l04fD2_restrict_apply] at h2'
  have hnorm : ∀ a (ha : a ∈ A),
      ggLinRestrictHom U ⟨a, hAstab ha⟩ ∈
        Subgroup.normalizer (Rbar : Set (↥U ≃ₗ[ZMod 3] ↥U)) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro rbar
    constructor
    · intro hr
      exact hRbar_conj a ha rbar hr
    · intro hconj
      have h_inv : ggLinRestrictHom U ⟨a⁻¹, hAstab (A.inv_mem ha)⟩ =
          (ggLinRestrictHom U ⟨a, hAstab ha⟩)⁻¹ := by
        rw [← map_inv]
        rfl
      have hmem := hRbar_conj a⁻¹ (A.inv_mem ha)
        (ggLinRestrictHom U ⟨a, hAstab ha⟩ * rbar *
          (ggLinRestrictHom U ⟨a, hAstab ha⟩)⁻¹) hconj
      have heq : ggLinRestrictHom U ⟨a⁻¹, hAstab (A.inv_mem ha)⟩ *
          (ggLinRestrictHom U ⟨a, hAstab ha⟩ * rbar *
            (ggLinRestrictHom U ⟨a, hAstab ha⟩)⁻¹) *
          (ggLinRestrictHom U ⟨a⁻¹, hAstab (A.inv_mem ha)⟩)⁻¹ = rbar := by
        rw [h_inv]
        group
      rwa [heq] at hmem
  have habs : ZS.AbsIrred 3 Rbar := ⟨habs_irred, habs_comm⟩
  intro a ha
  let abar : ↥U ≃ₗ[ZMod 3] ↥U := ggLinRestrictHom U ⟨a, hAstab ha⟩
  have hnorm_a : abar ∈ Subgroup.normalizer (Rbar : Set (↥U ≃ₗ[ZMod 3] ↥U)) :=
    hnorm a ha
  obtain ⟨rbar, hrbar, hpm_rbar⟩ :=
    ggWAut_normalizer_pm hK (V := ↥U) h5 Rbar habs hgen hneg hnorm_a
  change rbar ∈ (R.subgroupOf (ggLinStab U)).map (ggLinRestrictHom U) at hrbar
  rw [Subgroup.mem_map] at hrbar
  obtain ⟨g, hg, hg_eq⟩ := hrbar
  have hgR : (g : V ≃ₗ[ZMod 3] V) ∈ R := Subgroup.mem_subgroupOf.mp hg
  have hmemA : ((g : V ≃ₗ[ZMod 3] V)⁻¹ * a) ∈ A :=
    A.mul_mem (A.inv_mem (hR_le_A hgR)) ha
  have hx0 : x ≠ 0 := by
    intro hx
    apply hRx
    intro r hr
    rw [hx, map_zero]
    exact Submodule.zero_mem _
  have hax0 : a x ≠ 0 := by
    intro h0
    apply hx0
    exact a.injective (by rw [h0, map_zero])
  rcases hpm_rbar with hpm1 | hpm2
  · have hU : ∀ u ∈ U, ((g : V ≃ₗ[ZMod 3] V)⁻¹ * a) u = (1 : ZMod 3) • u := by
      intro u hu
      have h1 : abar ⟨u, hu⟩ = rbar ⟨u, hu⟩ := hpm1 ⟨u, hu⟩
      have h3 : (((abar ⟨u, hu⟩ : ↥U) : V)) = (((rbar ⟨u, hu⟩ : ↥U) : V)) := by
        rw [h1]
      rw [l04fD2_restrict_apply, ← hg_eq, l04fD2_restrict_apply] at h3
      change (g : V ≃ₗ[ZMod 3] V)⁻¹ (a u) = (1 : ZMod 3) • u
      rw [h3, one_smul]
      exact (g : V ≃ₗ[ZMod 3] V).symm_apply_apply u
    have hscalar := ggQ2Sub_scalar_x A hTF c α hαc s hs
      (fun i => ggWAut_reflGp_le A (hsR i)) x hfix hxfix U hHU hmemA
      (ε := (1 : ZMod 3)) one_ne_zero hU
    obtain ⟨lam, hlam⟩ := Submodule.mem_span_singleton.mp hscalar
    have hmain : a x = lam • (g : V ≃ₗ[ZMod 3] V) x := by
      have h1 : (g : V ≃ₗ[ZMod 3] V) (((g : V ≃ₗ[ZMod 3] V)⁻¹ * a) x) =
          lam • (g : V ≃ₗ[ZMod 3] V) x := by
        rw [← hlam, map_smul]
      have h2 : (g : V ≃ₗ[ZMod 3] V) (((g : V ≃ₗ[ZMod 3] V)⁻¹ * a) x) = a x := by
        rw [LinearEquiv.mul_apply]
        exact (g : V ≃ₗ[ZMod 3] V).apply_symm_apply (a x)
      rw [← h2, h1]
    refine ⟨(g : V ≃ₗ[ZMod 3] V), hgR, lam, ?_, hmain⟩
    intro hlam0
    apply hax0
    rw [hmain, hlam0, zero_smul]
  · have hU : ∀ u ∈ U, ((g : V ≃ₗ[ZMod 3] V)⁻¹ * a) u = (-1 : ZMod 3) • u := by
      intro u hu
      have h1 : abar ⟨u, hu⟩ = -(rbar ⟨u, hu⟩) := hpm2 ⟨u, hu⟩
      have h3 : (((abar ⟨u, hu⟩ : ↥U) : V)) = ((-(rbar ⟨u, hu⟩) : ↥U) : V) := by
        rw [h1]
      rw [l04fD2_restrict_apply, Submodule.coe_neg, ← hg_eq, l04fD2_restrict_apply] at h3
      change (g : V ≃ₗ[ZMod 3] V)⁻¹ (a u) = (-1 : ZMod 3) • u
      rw [h3, neg_one_smul, map_neg]
      congr 1
      exact (g : V ≃ₗ[ZMod 3] V).symm_apply_apply u
    have hscalar := ggQ2Sub_scalar_x A hTF c α hαc s hs
      (fun i => ggWAut_reflGp_le A (hsR i)) x hfix hxfix U hHU hmemA
      (ε := (-1 : ZMod 3)) (by decide) hU
    obtain ⟨lam, hlam⟩ := Submodule.mem_span_singleton.mp hscalar
    have hmain : a x = lam • (g : V ≃ₗ[ZMod 3] V) x := by
      have h1 : (g : V ≃ₗ[ZMod 3] V) (((g : V ≃ₗ[ZMod 3] V)⁻¹ * a) x) =
          lam • (g : V ≃ₗ[ZMod 3] V) x := by
        rw [← hlam, map_smul]
      have h2 : (g : V ≃ₗ[ZMod 3] V) (((g : V ≃ₗ[ZMod 3] V)⁻¹ * a) x) = a x := by
        rw [LinearEquiv.mul_apply]
        exact (g : V ≃ₗ[ZMod 3] V).apply_symm_apply (a x)
      rw [← h2, h1]
    refine ⟨(g : V ≃ₗ[ZMod 3] V), hgR, lam, ?_, hmain⟩
    intro hlam0
    apply hax0
    rw [hmain, hlam0, zero_smul]

theorem ggQ2Codim2_pm (hK : GGReflClassOmegaInput) [Module.Finite (ZMod 3) V] [Nonempty ι]
    (A : Subgroup (V ≃ₗ[ZMod 3] V)) (hTF : TransvectionFree A)
    (c : ι → V) (α : ι → Module.Dual (ZMod 3) V) (hαc : ∀ i, α i (c i) = 2)
    (s : ι → (V ≃ₗ[ZMod 3] V)) (hs : ∀ i v, s i v = v - α i v • c i) (hsR : ∀ i, s i ∈ reflGp A)
    (x : V) (hfix : ∀ z, (∀ i, α i z = 0) → z ∈ Submodule.span (ZMod 3) {x})
    (hxfix : ∀ i, α i x = 0)
    (hconn : ∀ i j, Relation.ReflTransGen (fun a b => α a (c b) ≠ 0 ∧ α b (c a) ≠ 0) i j)
    (hdim : Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range c)) + 2 =
      Module.finrank (ZMod 3) V)
    (h4 : 4 ≤ Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range c)))
    (hH5 : (∀ r ∈ reflGp A, ∀ h ∈ Submodule.span (ZMod 3) (Set.range c),
        r h ∈ Submodule.span (ZMod 3) (Set.range c)) →
      (¬ ∀ r ∈ reflGp A, r x ∈ Submodule.span (ZMod 3) {x}) →
        5 ≤ Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range c)))
    (hNotAbs : ¬ ZS.AbsIrred 3 (reflGp A)) :
    ∀ a ∈ A, ∃ r ∈ reflGp A, ∃ ε : ZMod 3, ε ≠ 0 ∧ a x = ε • r x := by
  classical
  let H : Submodule (ZMod 3) V := Submodule.span (ZMod 3) (Set.range c)
  have h2 : 2 ≤ Module.finrank (ZMod 3) H := by
    change 2 ≤ Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range c))
    omega
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
    · have hUtop : H ≠ ⊤ := by
        intro htop
        have hdimH : Module.finrank (ZMod 3) H + 2 = Module.finrank (ZMod 3) V := hdim
        have hfr : Module.finrank (ZMod 3) H = Module.finrank (ZMod 3) V := by
          rw [htop]
          exact finrank_top _ _
        omega
      intro a ha
      exact ggQ2Sub_pm_of_stab hK A hTF c α hαc s hs hsR x hfix hxfix hconn h2 H le_rfl
        hUtop (hH5 hRH hRxAll) hRH (fun W _ hHW hWH => le_antisymm hWH hHW) hRxAll a ha
    · have hex : ∃ U : Submodule (ZMod 3) V,
          (∀ r ∈ reflGp A, ∀ w ∈ U, r w ∈ U) ∧ H ≤ U ∧ U ≠ ⊤ := by
        by_contra hcon
        push Not at hcon
        exact hNotAbs
          (ggQ2Hyp_absIrred_of_stable A c α hαc s hs hsR x hfix hconn hcon hRxAll)
      obtain ⟨U, hRU, hHU, hUtop⟩ := hex
      have hne : U ≠ H := by
        intro hUH
        apply hRH
        intro r hr h hh
        have hmem : r h ∈ U := hRU r hr h (hHU hh)
        show r h ∈ H
        rw [← hUH]
        exact hmem
      have hlt : H < U := lt_of_le_of_ne hHU (Ne.symm hne)
      have hfinlt : Module.finrank (ZMod 3) H < Module.finrank (ZMod 3) U :=
        Submodule.finrank_lt_finrank_of_lt hlt
      have hUfin : Module.finrank (ZMod 3) U < Module.finrank (ZMod 3) V :=
        Submodule.finrank_lt hUtop
      have hdimH : Module.finrank (ZMod 3) H + 2 = Module.finrank (ZMod 3) V := hdim
      have h4H : 4 ≤ Module.finrank (ZMod 3) H := h4
      have hfin : Module.finrank (ZMod 3) U = Module.finrank (ZMod 3) H + 1 := by omega
      have h5 : 5 ≤ Module.finrank (ZMod 3) U := by omega
      have hmin : ∀ W : Submodule (ZMod 3) V, (∀ r ∈ reflGp A, ∀ w ∈ W, r w ∈ W) →
          H ≤ W → W ≤ U → W = U := by
        intro W hWstab hHW hWU
        have h1 : Module.finrank (ZMod 3) H ≤ Module.finrank (ZMod 3) W :=
          Submodule.finrank_mono hHW
        have h2' : Module.finrank (ZMod 3) W ≤ Module.finrank (ZMod 3) U :=
          Submodule.finrank_mono hWU
        rcases eq_or_lt_of_le h1 with heq | hlt'
        · exfalso
          have hWH : W = H := (Submodule.eq_of_le_of_finrank_eq hHW heq).symm
          apply hRH
          intro r hr h hh
          have hmem : r h ∈ W := hWstab r hr h (by rw [hWH]; exact hh)
          show r h ∈ H
          rw [← hWH]
          exact hmem
        · have heqU : Module.finrank (ZMod 3) W = Module.finrank (ZMod 3) U := by omega
          exact Submodule.eq_of_le_of_finrank_eq hWU heqU
      intro a ha
      exact ggQ2Sub_pm_of_stab hK A hTF c α hαc s hs hsR x hfix hxfix hconn h2 U hHU hUtop
        h5 hRU hmin hRxAll a ha

end CFSG.StandardType

end
