module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2OmegaRadicalLevi

public section

namespace CFSG.StandardType.LieKnownR2.POmega.Radical

open CFSG.Open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.StandardType CFSG.StandardType.ClassicalPosition
open scoped commutatorElement

private theorem core_polar_span_eq_zero {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {P P' : HypPair Q} {w x : V}
    (hx : x ∈ siegelY K P.e P'.e) (he : polar Q P.e w = 0) (he' : polar Q P'.e w = 0) :
    polar Q x w = 0 := by
  obtain ⟨c₁, c₂, rfl⟩ := Submodule.mem_span_pair.mp hx
  rw [polar_add_left, polar_smul_left_eq, polar_smul_left_eq, he, he']
  simp

private theorem core_polar_eq_zero_of_mem_siegelY {K V : Type} [Field K] [AddCommGroup V]
    [Module K V] {Q : QuadraticForm K V} {P P' : HypPair Q} (h : P.Orth P')
    {x y : V} (hx : x ∈ siegelY K P.e P'.e) (hy : y ∈ siegelY K P.e P'.e) :
    polar Q x y = 0 := by
  obtain ⟨c₁, c₂, rfl⟩ := Submodule.mem_span_pair.mp hx
  obtain ⟨d₁, d₂, rfl⟩ := Submodule.mem_span_pair.mp hy
  simp only [polar_add_left, polar_add_right, polar_smul_left_eq, polar_smul_right_eq,
    P.polar_ee, P'.polar_ee, h.ee, polar_comm Q P'.e P.e]
  ring

private theorem core_Q_eq_zero_of_mem_siegelY {K V : Type} [Field K] [AddCommGroup V]
    [Module K V] {Q : QuadraticForm K V} {P P' : HypPair Q} (h : P.Orth P') {x : V}
    (hx : x ∈ siegelY K P.e P'.e) : Q x = 0 := by
  obtain ⟨c₁, c₂, rfl⟩ := Submodule.mem_span_pair.mp hx
  rw [QuadraticMap.map_add Q, map_smul_eq_sq, map_smul_eq_sq, P.Q_e, P'.Q_e,
    polar_smul_left_eq, polar_smul_right_eq, h.ee]
  ring

private theorem core_mem_orthogonalGroup {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {P P' : HypPair Q} {g : V ≃ₗ[K] V}
    (hg : g ∈ axisRadical Q P.e P'.e) : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
  elementaryGroup_le_orthogonalGroup Q
    ((axisRadical_le_axisParabolic P P').trans (axisParabolic_le_elementaryGroup P P') hg)

private theorem core_fixes_siegelY {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {P P' : HypPair Q} (h : P.Orth P') {g : V ≃ₗ[K] V}
    (hg : g ∈ axisRadical Q P.e P'.e) : ∀ v ∈ siegelY K P.e P'.e, g v = v := by
  induction hg using Subgroup.closure_induction with
  | mem a ha =>
    obtain ⟨u, w, hu, hw1, hw2, rfl⟩ := ha
    intro v hv
    refine eichler_apply_of_polar_eq_zero ?_ ?_
    · exact core_polar_eq_zero_of_mem_siegelY h hv hu
    · exact core_polar_span_eq_zero hv hw1 hw2
  | one => intro v hv; rfl
  | mul a b _ _ ha hb =>
    intro v hv
    rw [LinearEquiv.mul_apply, hb v hv, ha v hv]
  | inv a _ ha =>
    intro v hv
    apply a.injective
    rw [LinearEquiv.apply_inv_apply', ha v hv]

private theorem core_sub_mem_siegelY {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {P P' : HypPair Q} (h : P.Orth P') {g : V ≃ₗ[K] V}
    (hg : g ∈ axisRadical Q P.e P'.e) :
    ∀ v, (∀ x ∈ siegelY K P.e P'.e, polar Q v x = 0) →
      g v - v ∈ siegelY K P.e P'.e := by
  induction hg using Subgroup.closure_induction with
  | mem a ha =>
    obtain ⟨u, w, hu, hw1, hw2, rfl⟩ := ha
    intro v hv
    have huQ : Q u = 0 := core_Q_eq_zero_of_mem_siegelY h hu
    have huw : polar Q u w = 0 := core_polar_span_eq_zero hu hw1 hw2
    have hvu : polar Q v u = 0 := hv u hu
    have hmem : polar Q v w • u ∈ siegelY K P.e P'.e := Submodule.smul_mem _ _ hu
    have heq : eichler Q u w v - v = -(polar Q v w • u) := by
      rw [eichler_apply huQ huw, hvu]
      simp only [zero_smul, mul_zero, add_zero]
      abel
    rw [heq]
    exact Submodule.neg_mem _ hmem
  | one => intro v hv; simp
  | mul a b _ _ ha hb =>
    intro v hv
    have hbv : b v - v ∈ siegelY K P.e P'.e := hb v hv
    have hbpol : ∀ x ∈ siegelY K P.e P'.e, polar Q (b v) x = 0 := by
      intro x hx
      have h1 : b v = v + (b v - v) := by abel
      rw [h1, polar_add_left, hv x hx,
        core_polar_eq_zero_of_mem_siegelY h hbv hx, add_zero]
    have hav : a (b v) - b v ∈ siegelY K P.e P'.e := ha (b v) hbpol
    have hsplit : (a * b) v - v = (a (b v) - b v) + (b v - v) := by
      rw [LinearEquiv.mul_apply]; abel
    rw [hsplit]
    exact Submodule.add_mem _ hav hbv
  | inv a ha_mem ha_ih =>
    intro v hv
    have haO : a ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
      core_mem_orthogonalGroup ha_mem
    have hafix := core_fixes_siegelY h ha_mem
    have hapol : ∀ x ∈ siegelY K P.e P'.e, polar Q (a⁻¹ v) x = 0 := by
      intro x hx
      have h1 := polar_map_of_mem haO (a⁻¹ v) x
      rw [LinearEquiv.apply_inv_apply', hafix x hx] at h1
      rw [← h1]
      exact hv x hx
    have hmove : a (a⁻¹ v) - a⁻¹ v ∈ siegelY K P.e P'.e := ha_ih (a⁻¹ v) hapol
    have hd : a⁻¹ v - v = -(a (a⁻¹ v) - a⁻¹ v) := by
      rw [LinearEquiv.apply_inv_apply']; abel
    rw [hd]
    exact Submodule.neg_mem _ hmove

private theorem core_dev_mul {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {P P' : HypPair Q} (h : P.Orth P') {g h' : V ≃ₗ[K] V}
    (hg : g ∈ axisRadical Q P.e P'.e) (hh : h' ∈ axisRadical Q P.e P'.e) :
    ∀ v, (∀ x ∈ siegelY K P.e P'.e, polar Q v x = 0) →
      (g * h') v - v = (g v - v) + (h' v - v) := by
  intro v hv
  have hhv : h' v - v ∈ siegelY K P.e P'.e := core_sub_mem_siegelY h hh v hv
  have hgfix := core_fixes_siegelY h hg
  have hsplit : h' v = v + (h' v - v) := by abel
  rw [LinearEquiv.mul_apply, hsplit, map_add, hgfix (h' v - v) hhv]
  abel

private theorem core_dev_inv {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {P P' : HypPair Q} (h : P.Orth P') {g : V ≃ₗ[K] V}
    (hg : g ∈ axisRadical Q P.e P'.e) :
    ∀ v, (∀ x ∈ siegelY K P.e P'.e, polar Q v x = 0) → g⁻¹ v - v = -(g v - v) := by
  intro v hv
  have hh := core_dev_mul h hg (inv_mem hg) v hv
  rw [mul_inv_cancel] at hh
  simp at hh
  rw [eq_neg_iff_add_eq_zero, add_comm]
  exact hh.symm

private theorem core_comm_fixes_perp {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {P P' : HypPair Q} (h : P.Orth P') {g h' : V ≃ₗ[K] V}
    (hg : g ∈ axisRadical Q P.e P'.e) (hh : h' ∈ axisRadical Q P.e P'.e) :
    ∀ v, (∀ x ∈ siegelY K P.e P'.e, polar Q v x = 0) → ⁅g, h'⁆ v = v := by
  intro v hv
  have dev : ∀ {a b : V ≃ₗ[K] V}, a ∈ axisRadical Q P.e P'.e →
      b ∈ axisRadical Q P.e P'.e → (a * b) v - v = (a v - v) + (b v - v) :=
    fun ha hb => core_dev_mul h ha hb v hv
  rw [commutatorElement_def]
  apply sub_eq_zero.mp
  rw [show g * h' * g⁻¹ * h'⁻¹ = g * (h' * (g⁻¹ * h'⁻¹)) by group]
  rw [dev hg (mul_mem hh (mul_mem (inv_mem hg) (inv_mem hh)))]
  rw [dev hh (mul_mem (inv_mem hg) (inv_mem hh))]
  rw [dev (inv_mem hg) (inv_mem hh)]
  rw [core_dev_inv h hg v hv, core_dev_inv h hh v hv]
  abel

private theorem core_comm_mem_siegelGroup {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {P P' : HypPair Q} (h : P.Orth P') {g h' : V ≃ₗ[K] V}
    (hg : g ∈ axisRadical Q P.e P'.e) (hh : h' ∈ axisRadical Q P.e P'.e)
    [CharP K 2] (hQ : (polarBilin Q).Nondegenerate) (hV : 6 ≤ Module.finrank K V) :
    ⁅g, h'⁆ ∈ siegelGroup Q P.e P'.e := by
  haveI : FiniteDimensional K V := FiniteDimensional.of_finrank_pos (by omega)
  have hk_mem : ⁅g, h'⁆ ∈ axisRadical Q P.e P'.e := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hg hh) (inv_mem hg)) (inv_mem hh)
  have hk_fixY := core_fixes_siegelY h hk_mem
  have hk_ortho : ⁅g, h'⁆ ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    core_mem_orthogonalGroup hk_mem
  have hk_fixperp : ∀ v, (∀ x ∈ siegelY K P.e P'.e, polar Q v x = 0) → ⁅g, h'⁆ v = v :=
    core_comm_fixes_perp h hg hh
  have hcent : ⁅g, h'⁆ ∈ Subgroup.centralizer (axisRadical Q P.e P'.e : Set (V ≃ₗ[K] V)) := by
    rw [axisRadical, Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
    rintro x ⟨u, w, hu, ha, hb, rfl⟩
    have hwperp : ∀ y ∈ siegelY K P.e P'.e, polar Q w y = 0 :=
      fun y hy => by rw [polar_comm]; exact core_polar_span_eq_zero hy ha hb
    have hfixw : ⁅g, h'⁆ w = w := hk_fixperp w hwperp
    have hfixu : ⁅g, h'⁆ u = u := hk_fixY u hu
    have hconj := eichler_conj hk_ortho u w
    rw [hfixu, hfixw] at hconj
    have h2 := congrArg (· * ⁅g, h'⁆) hconj
    rw [mul_assoc, inv_mul_cancel, mul_one] at h2
    exact h2.symm
  have hk_elem : ⁅g, h'⁆ ∈ elementaryGroup Q :=
    ((axisRadical_le_axisParabolic P P').trans (axisParabolic_le_elementaryGroup P P')) hk_mem
  have hC : ⁅g, h'⁆ ∈
      (Subgroup.centralizer (axisRadical Q P.e P'.e : Set (V ≃ₗ[K] V)) ⊓
        elementaryGroup Q : Subgroup (V ≃ₗ[K] V)) := Subgroup.mem_inf.mpr ⟨hcent, hk_elem⟩
  have hC' : ⁅g, h'⁆ ∈
      (((Subgroup.centralizer (axisRadical Q P.e P'.e : Set (V ≃ₗ[K] V)) ⊓
        elementaryGroup Q : Subgroup (V ≃ₗ[K] V))) : Set (V ≃ₗ[K] V)) := hC
  rw [centralizer_axisRadical_inf_eq hQ h hV] at hC'
  obtain ⟨c, hc⟩ := hC'
  rw [← hc]
  exact Subgroup.subset_closure ⟨c, rfl⟩

private theorem core_axisRadical_sub_mem_perp {K V : Type} [Field K] [AddCommGroup V]
    [Module K V] {Q : QuadraticForm K V} {P P' : HypPair Q} (h : P.Orth P') {g : V ≃ₗ[K] V}
    (hg : g ∈ axisRadical Q P.e P'.e) :
    ∀ v, g v - v ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) (siegelY K P.e P'.e) := by
  induction hg using Subgroup.closure_induction with
  | mem a ha =>
    obtain ⟨u, w, hu, ha1, ha2, rfl⟩ := ha
    intro v
    have hwperp : w ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) (siegelY K P.e P'.e) :=
      (LinearMap.BilinForm.mem_orthogonal_iff).mpr fun x hx => by
        rw [polarBilin_apply_apply]
        exact core_polar_span_eq_zero hx ha1 ha2
    have huperp : u ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) (siegelY K P.e P'.e) :=
      (LinearMap.BilinForm.mem_orthogonal_iff).mpr fun x hx => by
        rw [polarBilin_apply_apply]
        exact core_polar_eq_zero_of_mem_siegelY h hx hu
    have huQ : Q u = 0 := core_Q_eq_zero_of_mem_siegelY h hu
    have huw : polar Q u w = 0 := core_polar_span_eq_zero hu ha1 ha2
    have heq : eichler Q u w v - v =
        polar Q v u • w - (polar Q v w + Q w * polar Q v u) • u := by
      rw [eichler_apply huQ huw]; abel
    rw [heq]
    exact Submodule.sub_mem _
      (Submodule.smul_mem _ _ hwperp) (Submodule.smul_mem _ _ huperp)
  | one => intro v; simp
  | mul a b _ _ ha hb =>
    intro v
    have hsplit : (a * b) v - v = (a (b v) - b v) + (b v - v) := by
      rw [LinearEquiv.mul_apply]; abel
    rw [hsplit]
    exact Submodule.add_mem _ (ha (b v)) (hb v)
  | inv a _ ha =>
    intro v
    have hd : a⁻¹ v - v = -(a (a⁻¹ v) - a⁻¹ v) := by
      rw [LinearEquiv.apply_inv_apply']; abel
    rw [hd]
    exact Submodule.neg_mem _ (ha (a⁻¹ v))

private theorem core_siegelGroup_fixes_perp {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {P P' : HypPair Q} {g : V ≃ₗ[K] V}
    (hg : g ∈ siegelGroup Q P.e P'.e) :
    ∀ z, z ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) (siegelY K P.e P'.e) → g z = z := by
  rw [siegelGroup] at hg
  induction hg using Subgroup.closure_induction with
  | mem a ha =>
    obtain ⟨c, rfl⟩ := ha
    intro z hz
    refine eichler_apply_of_polar_eq_zero ?_ ?_
    · rw [polar_comm, ← polarBilin_apply_apply]
      exact (LinearMap.BilinForm.mem_orthogonal_iff.mp hz) P.e (Submodule.subset_span (by simp))
    · rw [polar_smul_right_eq, polar_comm, ← polarBilin_apply_apply]
      rw [(LinearMap.BilinForm.mem_orthogonal_iff.mp hz) P'.e (Submodule.subset_span (by simp)),
        mul_zero]
  | one => intro z hz; rfl
  | mul a b _ _ ha hb =>
    intro z hz
    rw [LinearEquiv.mul_apply, hb z hz, ha z hz]
  | inv a _ ha =>
    intro z hz
    apply a.injective
    rw [LinearEquiv.apply_inv_apply', ha z hz]

private theorem core_siegelGroup_sub_mem_Y {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {P P' : HypPair Q} (h : P.Orth P') {g : V ≃ₗ[K] V}
    (hg : g ∈ siegelGroup Q P.e P'.e) : ∀ v, g v - v ∈ siegelY K P.e P'.e := by
  rw [siegelGroup] at hg
  induction hg using Subgroup.closure_induction with
  | mem a ha =>
    obtain ⟨c, rfl⟩ := ha
    intro v
    have hpol : polar Q P.e (c • P'.e) = 0 := by
      rw [polar_smul_right_eq, h.ee, mul_zero]
    have heq : eichler Q P.e (c • P'.e) v - v =
        polar Q v P.e • (c • P'.e) -
          (polar Q v (c • P'.e) + Q (c • P'.e) * polar Q v P.e) • P.e := by
      rw [eichler_apply P.Q_e hpol]; abel
    rw [heq]
    exact Submodule.sub_mem _
      (Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  | one => intro v; simp
  | mul a b _ _ ha hb =>
    intro v
    have hsplit : (a * b) v - v = (a (b v) - b v) + (b v - v) := by
      rw [LinearEquiv.mul_apply]; abel
    rw [hsplit]
    exact Submodule.add_mem _ (ha (b v)) (hb v)
  | inv a _ ha =>
    intro v
    have hd : a⁻¹ v - v = -(a (a⁻¹ v) - a⁻¹ v) := by
      rw [LinearEquiv.apply_inv_apply']; abel
    rw [hd]
    exact Submodule.neg_mem _ (ha (a⁻¹ v))

theorem orthSiegelCore_commutator_le {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {P P' : HypPair Q} (h : P.Orth P') [CharP K 2]
    (hQ : (polarBilin Q).Nondegenerate) (hV : 6 ≤ Module.finrank K V) :
    ⁅orthSiegelCore Q P.e P'.e, orthSiegelCore Q P.e P'.e⁆ ≤ siegelRoot Q P.e P'.e := by
  rw [Subgroup.commutator_le]
  intro g hg h' hh'
  have hg' : spinAction Q g ∈ axisRadical Q P.e P'.e := hg
  have hh'' : spinAction Q h' ∈ axisRadical Q P.e P'.e := hh'
  change spinAction Q ⁅g, h'⁆ ∈ siegelGroup Q P.e P'.e
  rw [map_commutatorElement]
  exact core_comm_mem_siegelGroup h hg' hh'' hQ hV

theorem orthSiegelCore_le_centralizer {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} (hS : SpinOmegaData Q) {P P' : HypPair Q} (h : P.Orth P') :
    orthSiegelCore Q P.e P'.e ≤ Subgroup.centralizer (siegelRoot Q P.e P'.e : Set (spinGroup Q))
      := by
  have hinj : Function.Injective (spinAction Q) :=
    (MonoidHom.ker_eq_bot_iff (spinAction Q)).mp hS.ker_eq_bot
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro r hr
  apply hinj
  rw [map_mul, map_mul]
  refine LinearEquiv.ext fun v => ?_
  have hyfix := core_fixes_siegelY h hy
  have hysub := core_axisRadical_sub_mem_perp h hy v
  have hrfix := core_siegelGroup_fixes_perp hr
  have hrsub := core_siegelGroup_sub_mem_Y h hr v
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  have h1 : spinAction Q r (spinAction Q y v) =
      spinAction Q r v + (spinAction Q y v - v) := by
    have hsplit : spinAction Q y v = v + (spinAction Q y v - v) := by abel
    rw [hsplit, map_add, hrfix (spinAction Q y v - v) hysub]
    abel
  have h2 : spinAction Q y (spinAction Q r v) =
      spinAction Q y v + (spinAction Q r v - v) := by
    have hsplit : spinAction Q r v = v + (spinAction Q r v - v) := by abel
    rw [hsplit, map_add, hyfix (spinAction Q r v - v) hrsub]
    abel
  rw [h1, h2]
  abel

theorem orthSiegelCore_fixes_Y {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {P P' : HypPair Q} (h : P.Orth P') {y : spinGroup Q}
    (hy : y ∈ orthSiegelCore Q P.e P'.e) :
    ∀ v ∈ siegelY K P.e P'.e, spinAction Q y v = v := by
  exact core_fixes_siegelY h hy

theorem orthSiegelCore_sub_mem_Y {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {P P' : HypPair Q} (h : P.Orth P') {y : spinGroup Q}
    (hy : y ∈ orthSiegelCore Q P.e P'.e) :
    ∀ v, (∀ x ∈ siegelY K P.e P'.e, polar Q v x = 0) →
      spinAction Q y v - v ∈ siegelY K P.e P'.e := by
  exact core_sub_mem_siegelY h hy

end CFSG.StandardType.LieKnownR2.POmega.Radical
