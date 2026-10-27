module

public import CFSG.LocalAnalysis.StandardType.GGWAutCommon
public import CFSG.LocalAnalysis.StandardType.GGQ2MixedCentreLin

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {V ι : Type} [AddCommGroup V] [Module (ZMod 3) V]

private theorem ggQ2Hyp_smul_mem_of_stable (c : ι → V) (α : ι → Module.Dual (ZMod 3) V)
    (s : ι → V ≃ₗ[ZMod 3] V) (hs : ∀ i v, s i v = v - α i v • c i)
    (U : Submodule (ZMod 3) V) (hU : ∀ i, ∀ u ∈ U, s i u ∈ U) :
    ∀ i, ∀ u ∈ U, α i u • c i ∈ U := by
  intro i u hu
  have h := Submodule.sub_mem U hu (hU i u hu)
  rw [hs i u] at h
  rw [sub_sub_cancel] at h
  exact h

private theorem ggQ2Hyp_eq_bot_of_le_span_singleton (x : V) (W : Submodule (ZMod 3) V)
    (hW : W ≤ Submodule.span (ZMod 3) {x}) (hx : x ∉ W) : W = ⊥ := by
  by_contra hbot
  obtain ⟨w, hwW, hw0⟩ := W.ne_bot_iff.mp hbot
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hW hwW)
  have ha0 : a ≠ 0 := by
    intro h0
    exact hw0 (by rw [← ha, h0, zero_smul])
  refine hx ?_
  have hxw : x = a⁻¹ • w := by
    rw [← ha, smul_smul, inv_mul_cancel₀ ha0, one_smul]
  rw [hxw]
  exact Submodule.smul_mem W _ hwW

private theorem ggQ2Hyp_commute_on_span [Nonempty ι]
    (c : ι → V) (α : ι → Module.Dual (ZMod 3) V) (hαc : ∀ i, α i (c i) = 2)
    (s : ι → V ≃ₗ[ZMod 3] V) (hs : ∀ i v, s i v = v - α i v • c i)
    (hconn : ∀ i j, Relation.ReflTransGen
      (fun a b => α a (c b) ≠ 0 ∧ α b (c a) ≠ 0) i j)
    (T : Module.End (ZMod 3) V) (hTs : ∀ i v, T (s i v) = s i (T v)) :
    ∃ μ : ZMod 3, ∀ h ∈ Submodule.span (ZMod 3) (Set.range c), T h = μ • h := by
  classical
  have hkey : ∀ i v, α i v • T (c i) = α i (T v) • c i := by
    intro i v
    have h := hTs i v
    rw [hs i v, hs i (T v), map_sub, map_smul] at h
    calc
      α i v • T (c i) = T v - (T v - α i v • T (c i)) := (sub_sub_cancel _ _).symm
      _ = T v - (T v - α i (T v) • c i) := by rw [h]
      _ = α i (T v) • c i := sub_sub_cancel _ _
  have hc_ne : ∀ i, c i ≠ 0 := by
    intro i hci0
    have h := hαc i
    rw [hci0, map_zero] at h
    exact (by decide : (2 : ZMod 3) ≠ 0) h.symm
  have htc : ∀ i, ∃ μ_i : ZMod 3, T (c i) = μ_i • c i := by
    intro i
    have h := hkey i (c i)
    rw [hαc i] at h
    refine ⟨(2 : ZMod 3)⁻¹ * α i (T (c i)), ?_⟩
    calc
      T (c i) = (2 : ZMod 3)⁻¹ • ((2 : ZMod 3) • T (c i)) := by
        rw [smul_smul, inv_mul_cancel₀ (by decide : (2 : ZMod 3) ≠ 0), one_smul]
      _ = (2 : ZMod 3)⁻¹ • (α i (T (c i)) • c i) := by rw [h]
      _ = ((2 : ZMod 3)⁻¹ * α i (T (c i))) • c i := by rw [smul_smul]
  choose μ hμ using htc
  have hμ_edge : ∀ a b, α a (c b) ≠ 0 → α b (c a) ≠ 0 → μ a = μ b := by
    intro a b hab hba
    have h := hkey b (c a)
    have h1 : α b (c a) • T (c b) = α b (T (c a)) • c b := h
    rw [hμ b, hμ a] at h1
    simp only [smul_smul, map_smul, smul_eq_mul] at h1
    have hzero : (α b (c a) * μ b - μ a * α b (c a)) • c b = 0 := by
      rw [sub_smul, h1, sub_self]
    have hscalar : α b (c a) * μ b - μ a * α b (c a) = 0 := by
      by_contra hne
      have hne' : (α b (c a) * μ b - μ a * α b (c a)) • c b ≠ 0 := by
        intro hz
        rw [smul_eq_zero] at hz
        rcases hz with h | h
        · exact hne h
        · exact hc_ne b h
      exact hne' hzero
    have hcomm : α b (c a) * μ b = α b (c a) * μ a := by
      rw [mul_comm (μ a) (α b (c a))] at hscalar
      exact sub_eq_zero.mp hscalar
    exact (mul_left_cancel₀ hba hcomm).symm
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  let μ₀ : ZMod 3 := μ i₀
  have hμ_const : ∀ i, μ i = μ₀ := by
    intro i
    have hpath := hconn i₀ i
    induction hpath with
    | refl => rfl
    | tail hab hbc ih =>
        rename_i b d
        exact (hμ_edge b d hbc.1 hbc.2).symm.trans ih
  have hH : ∀ h ∈ Submodule.span (ZMod 3) (Set.range c), T h = μ₀ • h := by
    intro h hh
    apply Submodule.span_induction (p := fun x _ => T x = μ₀ • x) _ _ _ _ hh
    · rintro x ⟨i, rfl⟩
      rw [hμ i, hμ_const i]
    · simp
    · intro x y hx hy ihx ihy
      rw [map_add, ihx, ihy, smul_add]
    · intro a x hx ihx
      rw [map_smul, ihx, smul_smul, smul_smul, mul_comm a μ₀]
  exact ⟨μ₀, hH⟩

theorem ggQ2Hyp_line_of_R [Module.Finite (ZMod 3) V] (A : Subgroup (V ≃ₗ[ZMod 3] V))
    (c : ι → V) (α : ι → Module.Dual (ZMod 3) V) (s : ι → (V ≃ₗ[ZMod 3] V))
    (hs : ∀ i v, s i v = v - α i v • c i) (hsR : ∀ i, s i ∈ reflGp A) (x : V)
    (hfix : ∀ z, (∀ i, α i z = 0) → z ∈ Submodule.span (ZMod 3) {x})
    (hconn : ∀ i j, Relation.ReflTransGen (fun a b => α a (c b) ≠ 0 ∧ α b (c a) ≠ 0) i j)
    (h2 : 2 ≤ Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range c)))
    (hRx : ∀ r ∈ reflGp A, r x ∈ Submodule.span (ZMod 3) {x}) :
    ∀ a ∈ A, a x ∈ Submodule.span (ZMod 3) {x} := by
  intro a ha
  let U : Submodule (ZMod 3) V := Submodule.span (ZMod 3) {a x}
  have hstep : ∀ i, s i (a x) ∈ U := by
    intro i
    have hmemR : a⁻¹ * s i * a ∈ reflGp A := by
      simpa using ggWAut_reflGp_conj A (A.inv_mem ha) (hsR i)
    have hconj : (a⁻¹ * s i * a) x ∈ Submodule.span (ZMod 3) {x} := hRx _ hmemR
    have h := Submodule.apply_mem_span_image_of_mem_span
      (f := (a : V →ₗ[ZMod 3] V)) hconj
    have h' : a ((a⁻¹ * s i * a) x) ∈ Submodule.span (ZMod 3) {a x} := by
      simpa using h
    have hcomp : a * (a⁻¹ * s i * a) = s i * a := by group
    have heq : a ((a⁻¹ * s i * a) x) = s i (a x) := by
      calc
        a ((a⁻¹ * s i * a) x) = (a * (a⁻¹ * s i * a)) x :=
          (LinearEquiv.mul_apply _ _ _).symm
        _ = (s i * a) x := by rw [hcomp]
        _ = s i (a x) := LinearEquiv.mul_apply _ _ _
    rwa [heq] at h'
  have hU : ∀ i, ∀ u ∈ U, α i u • c i ∈ U :=
    ggQ2Hyp_smul_mem_of_stable c α s hs U (fun i u hu => by
      have hmaple : Submodule.map (s i).toLinearMap U ≤ U := by
        rw [show U = Submodule.span (ZMod 3) {a x} from rfl, Submodule.map_span]
        rw [Submodule.span_le]
        rintro _ ⟨v, hv, rfl⟩
        rw [Set.mem_singleton_iff] at hv
        subst hv
        exact hstep i
      exact hmaple (Submodule.mem_map_of_mem hu))
  rcases ggQ2Mix_stable_dichotomy c α x hfix hconn U hU with hH | hx
  · exfalso
    have hle : Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range c)) ≤
        Module.finrank (ZMod 3) U := Submodule.finrank_mono hH
    have hUle : Module.finrank (ZMod 3) U ≤ 1 := by
      by_cases h0 : a x = 0
      · have hbot : U = ⊥ := by
          rw [show U = Submodule.span (ZMod 3) {a x} from rfl,
            Submodule.span_singleton_eq_bot.mpr h0]
        rw [hbot]
        simp
      · rw [show U = Submodule.span (ZMod 3) {a x} from rfl, finrank_span_singleton h0]
    omega
  · exact hx (Submodule.mem_span_singleton_self (a x))

theorem ggQ2Hyp_absIrred [Module.Finite (ZMod 3) V] [Nonempty ι]
    (A : Subgroup (V ≃ₗ[ZMod 3] V)) (c : ι → V) (α : ι → Module.Dual (ZMod 3) V)
    (hαc : ∀ i, α i (c i) = 2) (s : ι → (V ≃ₗ[ZMod 3] V))
    (hs : ∀ i v, s i v = v - α i v • c i) (hsR : ∀ i, s i ∈ reflGp A) (x : V)
    (hfix : ∀ z, (∀ i, α i z = 0) → z ∈ Submodule.span (ZMod 3) {x})
    (hconn : ∀ i j, Relation.ReflTransGen (fun a b => α a (c b) ≠ 0 ∧ α b (c a) ≠ 0) i j)
    (hhyp : Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range c)) + 1 =
      Module.finrank (ZMod 3) V)
    (hRH : ¬ ∀ r ∈ reflGp A, ∀ h ∈ Submodule.span (ZMod 3) (Set.range c),
      r h ∈ Submodule.span (ZMod 3) (Set.range c))
    (hRx : ¬ ∀ r ∈ reflGp A, r x ∈ Submodule.span (ZMod 3) {x}) :
    ZS.AbsIrred 3 (reflGp A) := by
  classical
  have hInv : ∀ W : Submodule (ZMod 3) V,
      (∀ r ∈ reflGp A, ∀ w ∈ W, r w ∈ W) → W = ⊥ ∨ W = ⊤ := by
    intro W hW
    have hUW : ∀ i, ∀ u ∈ W, α i u • c i ∈ W :=
      ggQ2Hyp_smul_mem_of_stable c α s hs W (fun i u hu => hW (s i) (hsR i) u hu)
    rcases ggQ2Mix_stable_dichotomy c α x hfix hconn W hUW with hH | hx
    · have hfinH : Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range c)) ≤
          Module.finrank (ZMod 3) W := Submodule.finrank_mono hH
      have hfinW : Module.finrank (ZMod 3) W ≤ Module.finrank (ZMod 3) V :=
        Submodule.finrank_le W
      by_cases hEq : Module.finrank (ZMod 3) W =
          Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range c))
      · exfalso
        have hWH : Submodule.span (ZMod 3) (Set.range c) = W :=
          Submodule.eq_of_le_of_finrank_eq hH hEq.symm
        apply hRH
        intro r hr h hh
        rw [hWH] at hh ⊢
        exact hW r hr h hh
      · right
        apply Submodule.eq_top_of_finrank_eq
        have hlt : Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range c)) <
            Module.finrank (ZMod 3) W := lt_of_le_of_ne hfinH (Ne.symm hEq)
        omega
    · left
      apply ggQ2Hyp_eq_bot_of_le_span_singleton x W hx
      intro hxW
      apply hRx
      intro r hr
      exact hx (hW r hr x hxW)
  refine ⟨hInv, ?_⟩
  intro T hT
  have hTs : ∀ i v, T (s i v) = s i (T v) := by
    intro i v
    have h := LinearMap.congr_fun (hT (s i) (hsR i)) v
    simpa [LinearMap.comp_apply] using h
  obtain ⟨μ, hμ⟩ := ggQ2Hyp_commute_on_span c α hαc s hs hconn T hTs
  let K : Submodule (ZMod 3) V := LinearMap.ker (T - μ • LinearMap.id)
  have hHK : Submodule.span (ZMod 3) (Set.range c) ≤ K := by
    intro h hh
    rw [LinearMap.mem_ker]
    rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hμ h hh, sub_self]
  have hKstab : ∀ r ∈ reflGp A, ∀ v ∈ K, r v ∈ K := by
    intro r hr v hv
    rw [LinearMap.mem_ker] at hv ⊢
    have hcomm : T (r v) = r (T v) := by
      have h := LinearMap.congr_fun (hT r hr) v
      simpa [LinearMap.comp_apply] using h
    rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
    have hv' : T v = μ • v := by
      have h := sub_eq_zero.mp hv
      simpa using h
    rw [hcomm, hv', map_smul]
    exact sub_self _
  have hHne : Submodule.span (ZMod 3) (Set.range c) ≠ ⊥ := by
    let i : ι := Classical.arbitrary ι
    intro hbot
    have hci : c i = 0 := by
      have hmem : c i ∈ Submodule.span (ZMod 3) (Set.range c) :=
        Submodule.subset_span (Set.mem_range_self i)
      rwa [hbot, Submodule.mem_bot] at hmem
    have h := hαc i
    rw [hci, map_zero] at h
    exact (by decide : (2 : ZMod 3) ≠ 0) h.symm
  rcases hInv K hKstab with hKbot | hKtop
  · exfalso
    have hHbot : Submodule.span (ZMod 3) (Set.range c) = ⊥ :=
      eq_bot_iff.mpr (by rwa [hKbot] at hHK)
    exact hHne hHbot
  · refine ⟨μ, ?_⟩
    apply LinearMap.ext
    intro v
    have hv : v ∈ K := by
      rw [hKtop]
      exact Submodule.mem_top
    rw [LinearMap.mem_ker] at hv
    rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at hv
    simpa using hv

theorem ggQ2Hyp_absIrred_top [Module.Finite (ZMod 3) V] [Nonempty ι]
    (A : Subgroup (V ≃ₗ[ZMod 3] V)) (c : ι → V) (α : ι → Module.Dual (ZMod 3) V)
    (hαc : ∀ i, α i (c i) = 2) (s : ι → (V ≃ₗ[ZMod 3] V))
    (hs : ∀ i v, s i v = v - α i v • c i) (hsR : ∀ i, s i ∈ reflGp A) (x : V)
    (hfix : ∀ z, (∀ i, α i z = 0) → z ∈ Submodule.span (ZMod 3) {x})
    (hconn : ∀ i j, Relation.ReflTransGen (fun a b => α a (c b) ≠ 0 ∧ α b (c a) ≠ 0) i j)
    (htop : Submodule.span (ZMod 3) (Set.range c) = ⊤)
    (hRx : ¬ ∀ r ∈ reflGp A, r x ∈ Submodule.span (ZMod 3) {x}) :
    ZS.AbsIrred 3 (reflGp A) := by
  classical
  have hInv : ∀ W : Submodule (ZMod 3) V,
      (∀ r ∈ reflGp A, ∀ w ∈ W, r w ∈ W) → W = ⊥ ∨ W = ⊤ := by
    intro W hW
    have hUW : ∀ i, ∀ u ∈ W, α i u • c i ∈ W :=
      ggQ2Hyp_smul_mem_of_stable c α s hs W (fun i u hu => hW (s i) (hsR i) u hu)
    rcases ggQ2Mix_stable_dichotomy c α x hfix hconn W hUW with hH | hx
    · right
      exact top_le_iff.mp (by rwa [htop] at hH)
    · left
      apply ggQ2Hyp_eq_bot_of_le_span_singleton x W hx
      intro hxW
      apply hRx
      intro r hr
      exact hx (hW r hr x hxW)
  refine ⟨hInv, ?_⟩
  intro T hT
  have hTs : ∀ i v, T (s i v) = s i (T v) := by
    intro i v
    have h := LinearMap.congr_fun (hT (s i) (hsR i)) v
    simpa [LinearMap.comp_apply] using h
  obtain ⟨μ, hμ⟩ := ggQ2Hyp_commute_on_span c α hαc s hs hconn T hTs
  refine ⟨μ, ?_⟩
  apply LinearMap.ext
  intro v
  have hv : v ∈ Submodule.span (ZMod 3) (Set.range c) := by
    rw [htop]
    exact Submodule.mem_top
  simpa using hμ v hv

theorem ggQ2Hyp_absIrred_of_stable [Module.Finite (ZMod 3) V] [Nonempty ι]
    (A : Subgroup (V ≃ₗ[ZMod 3] V)) (c : ι → V) (α : ι → Module.Dual (ZMod 3) V)
    (hαc : ∀ i, α i (c i) = 2) (s : ι → (V ≃ₗ[ZMod 3] V))
    (hs : ∀ i v, s i v = v - α i v • c i) (hsR : ∀ i, s i ∈ reflGp A) (x : V)
    (hfix : ∀ z, (∀ i, α i z = 0) → z ∈ Submodule.span (ZMod 3) {x})
    (hconn : ∀ i j, Relation.ReflTransGen (fun a b => α a (c b) ≠ 0 ∧ α b (c a) ≠ 0) i j)
    (hW : ∀ W : Submodule (ZMod 3) V, (∀ r ∈ reflGp A, ∀ w ∈ W, r w ∈ W) →
      Submodule.span (ZMod 3) (Set.range c) ≤ W → W = ⊤)
    (hRx : ¬ ∀ r ∈ reflGp A, r x ∈ Submodule.span (ZMod 3) {x}) :
    ZS.AbsIrred 3 (reflGp A) := by
  classical
  have hInv : ∀ W : Submodule (ZMod 3) V,
      (∀ r ∈ reflGp A, ∀ w ∈ W, r w ∈ W) → W = ⊥ ∨ W = ⊤ := by
    intro W hWs
    have hUW : ∀ i, ∀ u ∈ W, α i u • c i ∈ W :=
      ggQ2Hyp_smul_mem_of_stable c α s hs W (fun i u hu => hWs (s i) (hsR i) u hu)
    rcases ggQ2Mix_stable_dichotomy c α x hfix hconn W hUW with hH | hx
    · exact Or.inr (hW W hWs hH)
    · left
      apply ggQ2Hyp_eq_bot_of_le_span_singleton x W hx
      intro hxW
      apply hRx
      intro r hr
      exact hx (hWs r hr x hxW)
  refine ⟨hInv, ?_⟩
  intro T hT
  have hTs : ∀ i v, T (s i v) = s i (T v) := by
    intro i v
    have h := LinearMap.congr_fun (hT (s i) (hsR i)) v
    simpa [LinearMap.comp_apply] using h
  obtain ⟨μ, hμ⟩ := ggQ2Hyp_commute_on_span c α hαc s hs hconn T hTs
  let K : Submodule (ZMod 3) V := LinearMap.ker (T - μ • LinearMap.id)
  have hHK : Submodule.span (ZMod 3) (Set.range c) ≤ K := by
    intro h hh
    rw [LinearMap.mem_ker]
    rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hμ h hh, sub_self]
  have hKstab : ∀ r ∈ reflGp A, ∀ v ∈ K, r v ∈ K := by
    intro r hr v hv
    rw [LinearMap.mem_ker] at hv ⊢
    have hcomm : T (r v) = r (T v) := by
      have h := LinearMap.congr_fun (hT r hr) v
      simpa [LinearMap.comp_apply] using h
    rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
    have hv' : T v = μ • v := by
      have h := sub_eq_zero.mp hv
      simpa using h
    rw [hcomm, hv', map_smul]
    exact sub_self _
  have hKtop : K = ⊤ := hW K hKstab hHK
  refine ⟨μ, ?_⟩
  apply LinearMap.ext
  intro v
  have hv : v ∈ K := by
    rw [hKtop]
    exact Submodule.mem_top
  rw [LinearMap.mem_ker] at hv
  rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at hv
  simpa using hv

theorem ggQ2Hyp_pm_top [Module.Finite (ZMod 3) V] [Nonempty ι]
    (A : Subgroup (V ≃ₗ[ZMod 3] V)) (c : ι → V) (α : ι → Module.Dual (ZMod 3) V)
    (hαc : ∀ i, α i (c i) = 2) (s : ι → (V ≃ₗ[ZMod 3] V))
    (hs : ∀ i v, s i v = v - α i v • c i) (hsR : ∀ i, s i ∈ reflGp A) (x : V)
    (hfix : ∀ z, (∀ i, α i z = 0) → z ∈ Submodule.span (ZMod 3) {x})
    (hconn : ∀ i j, Relation.ReflTransGen (fun a b => α a (c b) ≠ 0 ∧ α b (c a) ≠ 0) i j)
    (htop : Submodule.span (ZMod 3) (Set.range c) = ⊤) (h2 : 2 ≤ Module.finrank (ZMod 3) V)
    (hNotAbs : ¬ ZS.AbsIrred 3 (reflGp A)) :
    ∀ a ∈ A, ∃ r ∈ reflGp A, ∃ ε : ZMod 3, ε ≠ 0 ∧ a x = ε • r x := by
  have hRx : ∀ r ∈ reflGp A, r x ∈ Submodule.span (ZMod 3) {x} := by
    by_contra h
    exact hNotAbs (ggQ2Hyp_absIrred_top A c α hαc s hs hsR x hfix hconn htop h)
  have h2' : 2 ≤ Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range c)) := by
    rw [htop, finrank_top]
    exact h2
  have hline := ggQ2Hyp_line_of_R A c α s hs hsR x hfix hconn h2' hRx
  intro a ha
  by_cases hx0 : x = 0
  · refine ⟨1, Subgroup.one_mem _, 1, one_ne_zero, ?_⟩
    simp [hx0]
  · obtain ⟨ε, hε⟩ := Submodule.mem_span_singleton.mp (hline a ha)
    have hax0 : a x ≠ 0 := by
      intro h0
      apply hx0
      have h := a.injective (by simpa using h0)
      simpa using h
    have hε0 : ε ≠ 0 := by
      intro h0
      apply hax0
      rw [← hε, h0, zero_smul]
    exact ⟨1, Subgroup.one_mem _, ε, hε0, by simpa using hε.symm⟩

end CFSG.StandardType

end
