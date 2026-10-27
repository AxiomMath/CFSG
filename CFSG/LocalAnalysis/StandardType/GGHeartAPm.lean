module

public import CFSG.LocalAnalysis.StandardType.GGHeartAMod

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggHA_pm {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {r : ℕ} (hr : 4 ≤ r)
    (h : Fin r → V) (α : Fin r → Module.Dual (ZMod 3) V)
    (hα : ∀ i j, α i (h j) = ((CartanMatrix.A r i j : ℤ) : ZMod 3)) (x : V)
    (hxH : x ∉ Submodule.span (ZMod 3) (Set.range h))
    (hsup : Submodule.span (ZMod 3) (Set.range h) ⊔ Submodule.span (ZMod 3) {x} = ⊤)
    (hxk : ∀ i, α i x = 0)
    (hfix : ∀ v : V, (∀ i, α i v = 0) → v ∈ Submodule.span (ZMod 3) {x})
    (T : V ≃ₗ[ZMod 3] V) (hT : T ∈ Subgroup.normalizer (ggQ2WeylOf h α : Set (V ≃ₗ[ZMod 3] V))) :
    ∃ w ∈ ggQ2WeylOf h α, ∃ ε : ZMod 3, (ε = 1 ∨ ε = -1) ∧
      ∀ v : V, T (w v) - ε • v ∈ Submodule.span (ZMod 3) {x} := by
  classical
  let H : Submodule (ZMod 3) V := Submodule.span (ZMod 3) (Set.range h)
  let L : Submodule (ZMod 3) V := Submodule.span (ZMod 3) ({x} : Set V)
  let W : Subgroup (V ≃ₗ[ZMod 3] V) := ggQ2WeylOf h α
  have hHj : ∀ j : Fin r, h j ∈ H := fun j => Submodule.subset_span (Set.mem_range_self j)
  have hdiag : ∀ j : Fin r, α j (h j) = 2 := by
    intro j
    have hA : CartanMatrix.A r j j = 2 := by
      have h1 := congrFun (CartanMatrix.A_diag (n := r)) j
      simpa using h1
    rw [hα j j, hA]
    norm_num
  let s : Fin r → (V ≃ₗ[ZMod 3] V) := fun j => Module.reflection (h := hdiag j)
  have hs_mem : ∀ j : Fin r, s j ∈ W := by
    intro j
    apply Subgroup.subset_closure
    exact ⟨j, fun v => Module.reflection_apply (h := hdiag j) v⟩
  let FixSub : Subgroup (V ≃ₗ[ZMod 3] V) :=
    { carrier := {w | ∀ v : V, w v - v ∈ H}
      one_mem' := by intro v; simp
      mul_mem' := by
        intro a b ha hb v
        have h1 : (a * b) v - v = (a (b v) - b v) + (b v - v) := by
          rw [LinearEquiv.mul_apply]; abel
        rw [h1]
        exact Submodule.add_mem _ (ha (b v)) (hb v)
      inv_mem' := by
        intro a ha v
        have h1 : a (a⁻¹ v) - a⁻¹ v ∈ H := ha (a⁻¹ v)
        have h2 : v - a⁻¹ v ∈ H := by simpa using h1
        have h3 : a⁻¹ v - v = -(v - a⁻¹ v) := by abel
        rw [h3]
        exact Submodule.neg_mem _ h2 }
  have hWsub : ∀ w ∈ W, ∀ v : V, w v - v ∈ H := by
    have hle : W ≤ FixSub :=
      (Subgroup.closure_le FixSub).mpr (by
        intro t ht
        obtain ⟨j, hj⟩ := ht
        intro v
        rw [hj v]
        have h1 : v - α j v • h j - v = -(α j v • h j) := by abel
        rw [h1]
        exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (hHj j)))
    exact fun w hw => hle hw
  have hWstab : ∀ w ∈ W, ∀ v ∈ H, w v ∈ H := by
    intro w hw v hv
    have h1 := hWsub w hw v
    have h2 : w v = (w v - v) + v := by abel
    rw [h2]
    exact Submodule.add_mem _ h1 hv
  let FixLine : Subgroup (V ≃ₗ[ZMod 3] V) :=
    { carrier := {w | w x = x}
      one_mem' := by simp
      mul_mem' := by intro a b ha hb; show (a * b) x = x; rw [LinearEquiv.mul_apply, hb, ha]
      inv_mem' := by
        intro a ha
        have h1 : a⁻¹ (a x) = a⁻¹ x := congrArg (fun z => a⁻¹ z) ha
        have h2 : x = a⁻¹ x := by simpa using h1
        exact h2.symm }
  have hWx : ∀ w ∈ W, w x = x := by
    have hle : W ≤ FixLine :=
      (Subgroup.closure_le FixLine).mpr (by
        intro t ht
        obtain ⟨j, hj⟩ := ht
        show t x = x
        rw [hj x, hxk j]
        simp)
    exact fun w hw => hle hw
  have hUH : ∀ (U : V ≃ₗ[ZMod 3] V),
      U ∈ Subgroup.normalizer (W : Set (V ≃ₗ[ZMod 3] V)) → ∀ j : Fin r, U (h j) ∈ H := by
    intro U hU j
    have hUconj : U * s j * U⁻¹ ∈ W :=
      (Subgroup.mem_set_normalizer_iff.mp hU (s j)).mp (hs_mem j)
    have hmem := hWsub (U * s j * U⁻¹) hUconj (U (h j))
    have heq : (U * s j * U⁻¹) (U (h j)) - U (h j) = U (h j) := by
      have h1 : (U * s j * U⁻¹) (U (h j)) = U (s j (h j)) := by
        simp [LinearEquiv.mul_apply]
      rw [h1, Module.reflection_apply (h := hdiag j), map_sub, map_smul, hdiag j,
        show (2 : ZMod 3) = -1 by decide]
      module
    rwa [heq] at hmem
  have hTinvnorm : T⁻¹ ∈ Subgroup.normalizer (W : Set (V ≃ₗ[ZMod 3] V)) :=
    (Subgroup.normalizer (W : Set (V ≃ₗ[ZMod 3] V))).inv_mem hT
  have hTpres : ∀ v ∈ H, T v ∈ H := by
    intro v hv
    have hle : Submodule.span (ZMod 3) (Set.range h) ≤ H.comap T.toLinearMap :=
      Submodule.span_le.mpr (by rintro y ⟨j, rfl⟩; exact hUH T hT j)
    exact hle hv
  have hTinvpres : ∀ v ∈ H, T⁻¹ v ∈ H := by
    intro v hv
    have hle : Submodule.span (ZMod 3) (Set.range h) ≤ H.comap T⁻¹.toLinearMap :=
      Submodule.span_le.mpr (by rintro y ⟨j, rfl⟩; exact hUH T⁻¹ hTinvnorm j)
    exact hle hv
  have hmapT : H.map T.toLinearMap = H := by
    apply le_antisymm
    · exact Submodule.map_le_iff_le_comap.mpr hTpres
    · intro v hv
      exact Submodule.mem_map.mpr ⟨T⁻¹ v, hTinvpres v hv, by simp⟩
  let TH : H ≃ₗ[ZMod 3] H := T.ofSubmodules H H hmapT
  have hTH_coe : ∀ u : H, (TH u : V) = T (u : V) :=
    fun u => LinearEquiv.ofSubmodules_apply (e := T) hmapT u
  have hTHinv_coe : ∀ u : H, (TH⁻¹ u : V) = T⁻¹ (u : V) := by
    intro u
    have h := hTH_coe (TH⁻¹ u)
    rw [show TH (TH⁻¹ u) = u by simp] at h
    have hc := congrArg (fun z => T⁻¹ z) h
    simpa using hc.symm
  have hTx_fix : ∀ w ∈ W, w (T x) = T x := by
    intro w hw
    have hconj : T⁻¹ * w * T ∈ W := by
      simpa using (Subgroup.mem_set_normalizer_iff.mp hTinvnorm w).mp hw
    calc w (T x) = T (T⁻¹ (w (T x))) := by simp
      _ = T ((T⁻¹ * w * T) x) := by simp [LinearEquiv.mul_apply]
      _ = T x := by rw [hWx (T⁻¹ * w * T) hconj]
  have hTxL : T x ∈ L := by
    apply hfix
    intro j
    have hfixj : s j (T x) = T x := hTx_fix (s j) (hs_mem j)
    have hrepr : s j (T x) = T x - α j (T x) • h j :=
      Module.reflection_apply (h := hdiag j) (T x)
    rw [hrepr] at hfixj
    have hb : α j (T x) • h j = 0 := sub_eq_self.mp hfixj
    have h1 : α j (α j (T x) • h j) = α j 0 := congrArg (α j) hb
    rw [map_smul, smul_eq_mul, map_zero] at h1
    rw [hdiag j] at h1
    have h2 : (2 : ZMod 3) ≠ 0 := by decide
    exact (mul_eq_zero.mp h1).resolve_right h2
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hTxL
  let h' : Fin r → H := fun j => ⟨h j, hHj j⟩
  let α' : Fin r → Module.Dual (ZMod 3) H := fun j => (α j).comp H.subtype
  have hα' : ∀ i j, α' i (h' j) = ((CartanMatrix.A r i j : ℤ) : ZMod 3) := by
    intro i j
    dsimp only [α', h']
    exact hα i j
  have hspan' : Submodule.span (ZMod 3) (Set.range h') = ⊤ :=
    (Submodule.span_range_subtype_eq_top_iff H hHj).mpr rfl
  have hHL : H ⊓ L = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    rw [Submodule.mem_inf] at hy
    rw [Submodule.mem_bot]
    obtain ⟨c', hc'⟩ := Submodule.mem_span_singleton.mp hy.2
    by_cases hc0 : c' = 0
    · rw [← hc', hc0, zero_smul]
    · exfalso
      apply hxH
      have hmem : c'⁻¹ • y ∈ H := Submodule.smul_mem _ _ hy.1
      rw [← hc'] at hmem
      rw [smul_smul, inv_mul_cancel₀ hc0, one_smul] at hmem
      exact hmem
  have hker' : ∀ u : H, (∀ i, α' i u = 0) → u = 0 := by
    intro u hu
    have hLu : (u : V) ∈ L := hfix (u : V) (fun i => hu i)
    have hbot : (u : V) ∈ (⊥ : Submodule (ZMod 3) V) := by
      have hmem : (u : V) ∈ H ⊓ L := ⟨u.2, hLu⟩
      rwa [hHL] at hmem
    have hzero : (u : V) = 0 := by simpa using hbot
    exact Subtype.ext hzero
  let W' : Subgroup (H ≃ₗ[ZMod 3] H) := ggQ2WeylOf h' α'
  let resFun : W → (H ≃ₗ[ZMod 3] H) := fun w =>
    { toFun := fun u => ⟨(w : V ≃ₗ[ZMod 3] V) (u : V), hWstab (w : V ≃ₗ[ZMod 3] V) w.2 u u.2⟩
      invFun := fun u => ⟨((w⁻¹ : W) : V ≃ₗ[ZMod 3] V) (u : V),
        hWstab ((w⁻¹ : W) : V ≃ₗ[ZMod 3] V) (w⁻¹).2 u u.2⟩
      left_inv := by intro u; apply Subtype.ext; simp
      right_inv := by intro u; apply Subtype.ext; simp
      map_add' := by intro u v; apply Subtype.ext; simp
      map_smul' := by intro a u; apply Subtype.ext; simp }
  have hres_apply : ∀ (w : W) (u : H),
      ((resFun w u : H) : V) = (w : V ≃ₗ[ZMod 3] V) (u : V) := fun w u => rfl
  have hres_apply_symm : ∀ (w : W) (u : H),
      (((resFun w)⁻¹ u : H) : V) = ((w : V ≃ₗ[ZMod 3] V)⁻¹ (u : V)) := fun w u => rfl
  have hres_one : resFun (1 : W) = 1 := by
    ext u; rw [hres_apply]; simp
  have hres_mul : ∀ w₁ w₂ : W, resFun (w₁ * w₂) = resFun w₁ * resFun w₂ := by
    intro w₁ w₂
    ext u
    simp only [Subgroup.coe_mul, LinearEquiv.mul_apply, hres_apply]
  have hres_inv : ∀ w : W, resFun w⁻¹ = (resFun w)⁻¹ := by
    intro w
    ext u
    rw [hres_apply_symm]
    rfl
  have hres_mem_W' : ∀ w : W, resFun w ∈ W' := by
    intro w
    refine Subgroup.closure_induction (p := fun y (hy : y ∈ W) => resFun ⟨y, hy⟩ ∈ W')
      ?_ ?_ ?_ ?_ w.2
    · intro y hyS
      obtain ⟨j, hj⟩ := hyS
      apply Subgroup.subset_closure
      refine ⟨j, fun u => ?_⟩
      apply Subtype.ext
      rw [hres_apply, hj (u : V)]
      rfl
    · have hsub : (⟨(1 : V ≃ₗ[ZMod 3] V), _⟩ : W) = 1 := Subtype.ext rfl
      rw [hsub, hres_one]
      exact W'.one_mem
    · intro x y hx hy px py
      have hx' : resFun ⟨x, hx⟩ ∈ W' := px
      have hy' : resFun ⟨y, hy⟩ ∈ W' := py
      have hprod : resFun ⟨x * y, Subgroup.mul_mem W hx hy⟩ =
          resFun ⟨x, hx⟩ * resFun ⟨y, hy⟩ := by
        rw [show (⟨x * y, Subgroup.mul_mem W hx hy⟩ : W) = ⟨x, hx⟩ * ⟨y, hy⟩ by
          exact Subtype.ext rfl]
        exact hres_mul ⟨x, hx⟩ ⟨y, hy⟩
      rw [hprod]
      exact W'.mul_mem hx' hy'
    · intro x hx px
      have hx' : resFun ⟨x, hx⟩ ∈ W' := px
      have hinv : resFun ⟨x⁻¹, Subgroup.inv_mem W hx⟩ = (resFun ⟨x, hx⟩)⁻¹ := by
        rw [show (⟨x⁻¹, Subgroup.inv_mem W hx⟩ : W) = (⟨x, hx⟩)⁻¹ by
          exact Subtype.ext rfl]
        exact hres_inv ⟨x, hx⟩
      rw [hinv]
      exact W'.inv_mem hx'
  have hsurj : ∀ g ∈ W', ∃ w : W, resFun w = g := by
    intro g hg
    refine Subgroup.closure_induction (p := fun y _ => ∃ w : W, resFun w = y) ?_ ?_ ?_ ?_ hg
    · intro t htS
      obtain ⟨j, hj⟩ := htS
      refine ⟨⟨s j, hs_mem j⟩, ?_⟩
      ext u
      rw [hres_apply, Module.reflection_apply (h := hdiag j), hj u]
      rfl
    · exact ⟨1, hres_one⟩
    · intro x y hx hy px py
      obtain ⟨w1, hw1⟩ := px
      obtain ⟨w2, hw2⟩ := py
      refine ⟨w1 * w2, ?_⟩
      rw [hres_mul, hw1, hw2]
    · intro x hx px
      obtain ⟨w, hw⟩ := px
      refine ⟨w⁻¹, ?_⟩
      rw [hres_inv, hw]
  have hTconj : ∀ w : W, T * (w : V ≃ₗ[ZMod 3] V) * T⁻¹ ∈ W :=
    fun w => (Subgroup.mem_set_normalizer_iff.mp hT (w : V ≃ₗ[ZMod 3] V)).mp w.2
  have hTinvconj : ∀ w : W, T⁻¹ * (w : V ≃ₗ[ZMod 3] V) * T ∈ W := by
    intro w
    simpa using (Subgroup.mem_set_normalizer_iff.mp hTinvnorm (w : V ≃ₗ[ZMod 3] V)).mp w.2
  have hconj_gen : ∀ (U : V ≃ₗ[ZMod 3] V) (UH : H ≃ₗ[ZMod 3] H)
      (w : W) (Uconj : W),
      (∀ u : H, (UH u : V) = U (u : V)) →
      (∀ u : H, (UH⁻¹ u : V) = U⁻¹ (u : V)) →
      (Uconj : V ≃ₗ[ZMod 3] V) = U * (w : V ≃ₗ[ZMod 3] V) * U⁻¹ →
      UH * resFun w * UH⁻¹ = resFun Uconj := by
    intro U UH w Uconj hUH hUHinv hUconj
    ext u
    calc ((UH * resFun w * UH⁻¹) u : V)
        = U ((resFun w (UH⁻¹ u)) : V) := by
          rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hUH]
      _ = U ((w : V ≃ₗ[ZMod 3] V) ((UH⁻¹ u : H) : V)) := by rw [hres_apply]
      _ = U ((w : V ≃ₗ[ZMod 3] V) (U⁻¹ (u : V))) := by rw [hUHinv]
      _ = (U * (w : V ≃ₗ[ZMod 3] V) * U⁻¹) (u : V) := by
          rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
      _ = ((resFun Uconj) u : V) := by rw [hres_apply, hUconj]
  have hconj_T : ∀ w : W, TH * resFun w * TH⁻¹ =
      resFun (⟨T * (w : V ≃ₗ[ZMod 3] V) * T⁻¹, hTconj w⟩ : W) :=
    fun w => hconj_gen T TH w ⟨_, hTconj w⟩ hTH_coe hTHinv_coe rfl
  have hconj_Tinv : ∀ w : W, TH⁻¹ * resFun w * TH =
      resFun (⟨T⁻¹ * (w : V ≃ₗ[ZMod 3] V) * T, hTinvconj w⟩ : W) :=
    fun w => hconj_gen T⁻¹ TH⁻¹ w ⟨_, hTinvconj w⟩ hTHinv_coe (by simpa using hTH_coe) rfl
  have hF : ∀ g ∈ W', TH * g * TH⁻¹ ∈ W' := by
    intro g hg
    obtain ⟨w, hw⟩ := hsurj g hg
    rw [← hw, hconj_T w]
    exact hres_mem_W' _
  have hG : ∀ g ∈ W', TH⁻¹ * g * TH ∈ W' := by
    intro g hg
    obtain ⟨w, hw⟩ := hsurj g hg
    rw [← hw, hconj_Tinv w]
    exact hres_mem_W' _
  have hTHnorm : TH ∈ Subgroup.normalizer (W' : Set (H ≃ₗ[ZMod 3] H)) := by
    rw [Subgroup.mem_set_normalizer_iff]
    intro g
    constructor
    · intro hg; exact hF g hg
    · intro hg
      have h := hG (TH * g * TH⁻¹) hg
      simpa [mul_assoc] using h
  obtain ⟨w₀, hw₀, ε, hε, hval⟩ :=
    ggHA_mod (H := H) hr h' α' hα' hspan' hker' TH hTHnorm
  obtain ⟨w₁, hw₁⟩ := hsurj w₀⁻¹ (W'.inv_mem hw₀)
  refine ⟨(w₁ : V ≃ₗ[ZMod 3] V), w₁.2, ε, hε, ?_⟩
  intro v
  have hv : v ∈ H ⊔ L := by rw [hsup]; trivial
  obtain ⟨u, huH, z, hzL, huv⟩ := Submodule.mem_sup.mp hv
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hzL
  let uH : H := ⟨u, huH⟩
  have hwz : (w₁ : V ≃ₗ[ZMod 3] V) z = z := by
    rw [← ha, map_smul, hWx (w₁ : V ≃ₗ[ZMod 3] V) w₁.2]
  have hwu : (w₁ : V ≃ₗ[ZMod 3] V) u = (((w₀⁻¹) uH : H) : V) := by
    have h := hres_apply w₁ uH
    rw [hw₁] at h
    exact h.symm
  have hTu : T ((w₁ : V ≃ₗ[ZMod 3] V) u) = ε • (u : V) := by
    rw [hwu]
    have h1 : T (((w₀⁻¹) uH : H) : V) = (TH ((w₀⁻¹) uH) : V) := (hTH_coe _).symm
    rw [h1, hval (w₀⁻¹ uH), show w₀ ((w₀⁻¹) uH) = uH by simp]
    rfl
  have hTz : T ((w₁ : V ≃ₗ[ZMod 3] V) z) = (a * c) • x := by
    rw [hwz, ← ha, map_smul, hc.symm, smul_smul]
  have heq : T ((w₁ : V ≃ₗ[ZMod 3] V) v) - ε • v = (a * (c - ε)) • x := by
    rw [huv.symm, map_add, map_add, hTu, hTz, ← ha, smul_add]
    module
  rw [heq]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

end CFSG.StandardType

end
