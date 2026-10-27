module

public import CFSG.RankThree.GF2n.Smith81.S81JMat

public section

namespace CFSG.RankThree.GF2n.Smith81.S81J

open CFSG.RankThree.GF2n.Smith81.A5Cube Matrix Module


variable {K : Type} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

structure SLAct (K : Type) [Field K] (V : Type*) [AddCommGroup V] [Module K V] where
  act : GL (Fin 6) K → (V →ₗ[K] V)
  act_one : act 1 = 1
  act_mul : ∀ g h : GL (Fin 6) K, (g : Matrix (Fin 6) (Fin 6) K).det = 1 →
    (h : Matrix (Fin 6) (Fin 6) K).det = 1 → act (g * h) = act g * act h

namespace SLAct

variable (A : SLAct K V)

def Fix (W : Submodule K (Fin 6 → K)) : Submodule K V where
  carrier := {v | ∀ u ∈ UnipGL K W, A.act u v = v}
  add_mem' := fun {a b} ha hb u hu => by rw [map_add, ha u hu, hb u hu]
  zero_mem' := fun u _ => map_zero _
  smul_mem' := fun c v hv u hu => by rw [map_smul, hv u hu]

theorem mem_Fix {W : Submodule K (Fin 6 → K)} {v : V} :
    v ∈ A.Fix W ↔ ∀ u ∈ UnipGL K W, A.act u v = v := Iff.rfl

theorem det_inv_eq_one {g : GL (Fin 6) K} (hg : (g : Matrix (Fin 6) (Fin 6) K).det = 1) :
    ((g⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det = 1 := by
  have h : (g : Matrix (Fin 6) (Fin 6) K).det *
      ((g⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det = 1 := by
    rw [← Matrix.det_mul, Units.mul_inv, Matrix.det_one]
  rwa [hg, one_mul] at h

theorem act_inv_act {g : GL (Fin 6) K} (hg : (g : Matrix (Fin 6) (Fin 6) K).det = 1) (v : V) :
    A.act g⁻¹ (A.act g v) = v := by
  have h1 : A.act g⁻¹ * A.act g = 1 := by
    rw [← A.act_mul g⁻¹ g (det_inv_eq_one hg) hg, inv_mul_cancel, A.act_one]
  have h2 := congrArg (fun f : V →ₗ[K] V => f v) h1
  exact h2

theorem act_act_inv {g : GL (Fin 6) K} (hg : (g : Matrix (Fin 6) (Fin 6) K).det = 1) (v : V) :
    A.act g (A.act g⁻¹ v) = v := by
  have h1 : A.act g * A.act g⁻¹ = 1 := by
    rw [← A.act_mul g g⁻¹ hg (det_inv_eq_one hg), mul_inv_cancel, A.act_one]
  have h2 := congrArg (fun f : V →ₗ[K] V => f v) h1
  exact h2

theorem actA_inj {g : GL (Fin 6) K} (hg : (g : Matrix (Fin 6) (Fin 6) K).det = 1) :
    Function.Injective (A.act g) := by
  intro v w h
  have h1 := A.act_inv_act hg v
  rw [h] at h1
  exact h1.symm.trans (A.act_inv_act hg w)

theorem actA_conj_apply {g h : GL (Fin 6) K} (hg : (g : Matrix (Fin 6) (Fin 6) K).det = 1)
    (hh : (h : Matrix (Fin 6) (Fin 6) K).det = 1) (x : V) :
    A.act (g * h * g⁻¹) (A.act g x) = A.act g (A.act h x) := by
  have hgh : ((g * h : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det = 1 := by
    rw [Units.val_mul, Matrix.det_mul, hg, hh, one_mul]
  rw [A.act_mul (g * h) g⁻¹ hgh (det_inv_eq_one hg), A.act_mul g h hg hh, Module.End.mul_apply,
    Module.End.mul_apply, A.act_inv_act hg]

theorem Fix_map {g : GL (Fin 6) K} (hg : (g : Matrix (Fin 6) (Fin 6) K).det = 1)
    (W : Submodule K (Fin 6 → K)) :
    (A.Fix W).map (A.act g) =
      A.Fix (W.map (Matrix.mulVecLin (g : Matrix (Fin 6) (Fin 6) K))) := by
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    rw [A.mem_Fix]
    intro u hu
    have hu' := s81A12_conj_mem_inv g W hu
    have hdet' : ((g⁻¹ * u * g : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det = 1 :=
      (mem_UnipGL_iff.1 hu').1
    have key := A.actA_conj_apply hg hdet' v
    rw [show g * (g⁻¹ * u * g) * g⁻¹ = u by group, (A.mem_Fix.1 hv) _ hu'] at key
    exact key
  · intro hw
    refine ⟨A.act g⁻¹ w, ?_, A.act_act_inv hg w⟩
    rw [SetLike.mem_coe, A.mem_Fix]
    intro u hu
    have hu' := s81A12_conj_mem g W hu
    have hdetu : (u : Matrix (Fin 6) (Fin 6) K).det = 1 := (mem_UnipGL_iff.1 hu).1
    have hw' := (A.mem_Fix.1 hw) _ hu'
    have key := A.actA_conj_apply hg hdetu (A.act g⁻¹ w)
    rw [A.act_act_inv hg w, hw'] at key
    exact A.actA_inj hg (key.symm.trans (A.act_act_inv hg w).symm)

theorem finrank_Fix_map {g : GL (Fin 6) K} (hg : (g : Matrix (Fin 6) (Fin 6) K).det = 1)
    (W : Submodule K (Fin 6 → K)) :
    finrank K (A.Fix (W.map (Matrix.mulVecLin (g : Matrix (Fin 6) (Fin 6) K)))) =
      finrank K (A.Fix W) := by
  rw [← A.Fix_map hg W]
  exact (LinearEquiv.finrank_eq
    (Submodule.equivMapOfInjective (A.act g) (A.actA_inj hg) (A.Fix W))).symm

theorem actA_map_eq {p : GL (Fin 6) K} {W : Submodule K (Fin 6 → K)}
    (hpW : ∀ w ∈ W, (p : Matrix (Fin 6) (Fin 6) K).mulVec w ∈ W) :
    W.map (Matrix.mulVecLin (p : Matrix (Fin 6) (Fin 6) K)) = W := by
  have hinj : Function.Injective (Matrix.mulVecLin (p : Matrix (Fin 6) (Fin 6) K)) := by
    intro x y hxy
    have h := congrArg (Matrix.mulVec ((p⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) hxy
    rwa [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Matrix.one_mulVec] at h
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact hpW x hx
  · exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj W)).symm

theorem act_mem_Fix {p : GL (Fin 6) K} (hp : (p : Matrix (Fin 6) (Fin 6) K).det = 1)
    {W : Submodule K (Fin 6 → K)}
    (hpW : ∀ w ∈ W, (p : Matrix (Fin 6) (Fin 6) K).mulVec w ∈ W) {v : V} (hv : v ∈ A.Fix W) :
    A.act p v ∈ A.Fix W := by
  have h := A.Fix_map hp W
  rw [actA_map_eq hpW] at h
  rw [← h]
  exact Submodule.mem_map_of_mem hv

theorem line_scalar {W : Submodule K (Fin 6 → K)} (hW : finrank K (A.Fix W) = 1)
    (f : V →ₗ[K] V) (hf : ∀ v ∈ A.Fix W, f v ∈ A.Fix W) :
    ∃ c : K, ∀ v ∈ A.Fix W, f v = c • v := by
  obtain ⟨v₀, -, hspan⟩ := finrank_eq_one_iff'.1 hW
  have hx : (v₀ : V) ∈ A.Fix W := v₀.2
  obtain ⟨c, hc⟩ := hspan ⟨f (v₀ : V), hf _ hx⟩
  have hfc : f (v₀ : V) = c • (v₀ : V) := (congrArg Subtype.val hc).symm
  refine ⟨c, fun v hv => ?_⟩
  obtain ⟨a, ha⟩ := hspan ⟨v, hv⟩
  have hva : v = a • (v₀ : V) := (congrArg Subtype.val ha).symm
  rw [hva, map_smul, hfc, smul_comm]

theorem act_invol_fix [CharP K 2] {p : GL (Fin 6) K}
    (hp : (p : Matrix (Fin 6) (Fin 6) K).det = 1) (hpp : p * p = 1)
    {W : Submodule K (Fin 6 → K)} (hpW : ∀ w ∈ W, (p : Matrix (Fin 6) (Fin 6) K).mulVec w ∈ W)
    (hW : finrank K (A.Fix W) = 1) : ∀ v ∈ A.Fix W, A.act p v = v := by
  obtain ⟨c, hc⟩ := A.line_scalar hW (A.act p) (fun v hv => A.act_mem_Fix hp hpW hv)
  obtain ⟨v₀, hv₀, -⟩ := finrank_eq_one_iff'.1 hW
  have hx0 : (v₀ : V) ≠ 0 := fun h => hv₀ (Subtype.ext h)
  have hx : (v₀ : V) ∈ A.Fix W := v₀.2
  have h2 : A.act p (A.act p (v₀ : V)) = (v₀ : V) := by
    rw [← Module.End.mul_apply, ← A.act_mul p p hp hp, hpp, A.act_one, Module.End.one_apply]
  have h3 : (c * c) • (v₀ : V) = (v₀ : V) := by
    rw [hc _ hx, map_smul, hc _ hx, smul_smul] at h2
    exact h2
  have hcc : c * c = 1 := by
    have h4 : (c * c - 1) • (v₀ : V) = 0 := by rw [sub_smul, one_smul, h3, sub_self]
    rcases smul_eq_zero.1 h4 with h5 | h5
    · exact sub_eq_zero.1 h5
    · exact absurd h5 hx0
  have hsq : (c - 1) * (c - 1) = 0 := by
    linear_combination hcc + (1 - c) * (CharTwo.two_eq_zero : (2 : K) = 0)
  have hc1 : c = 1 := sub_eq_zero.1 (mul_self_eq_zero.1 hsq)
  intro v hv
  rw [hc v hv, hc1, one_smul]

theorem finrank_Fix_Wc [CharP K 2] (h0 : finrank K (A.Fix (Wc K I0)) = 1) {I : Finset (Fin 6)}
    (hI : I.card = 3) : finrank K (A.Fix (Wc K I)) = 1 := by
  obtain ⟨σ, hσ⟩ := exists_perm_image_eq I hI
  rw [← hσ, ← Wc_map_pm σ I0, A.finrank_Fix_map (det_pm σ) (Wc K I0), h0]

theorem act_pm_Fix [CharP K 2] (σ : Equiv.Perm (Fin 6)) (I : Finset (Fin 6)) :
    (A.Fix (Wc K I)).map (A.act (pm K σ)) = A.Fix (Wc K (I.image σ)) := by
  rw [A.Fix_map (det_pm σ) (Wc K I), Wc_map_pm σ I]

private theorem actB_fix_mul {W : Submodule K (Fin 6 → K)} {g h : GL (Fin 6) K}
    (hg : (g : Matrix (Fin 6) (Fin 6) K).det = 1) (hh : (h : Matrix (Fin 6) (Fin 6) K).det = 1)
    (Hg : ∀ v ∈ A.Fix W, A.act g v = v) (Hh : ∀ v ∈ A.Fix W, A.act h v = v) :
    ∀ v ∈ A.Fix W, A.act (g * h) v = v := by
  intro v hv
  rw [A.act_mul g h hg hh, Module.End.mul_apply, Hh v hv, Hg v hv]

private theorem actB_det_mul {g h : GL (Fin 6) K}
    (hg : (g : Matrix (Fin 6) (Fin 6) K).det = 1) (hh : (h : Matrix (Fin 6) (Fin 6) K).det = 1) :
    ((g * h : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det = 1 := by
  rw [Units.val_mul, Matrix.det_mul, hg, hh, one_mul]

private theorem actB_det_cOn [CharP K 2] {a b : Fin 6} (hab : a ≠ b) (c : Kˣ) :
    ((dg (cOn a b c) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det = 1 := by
  rw [dg_cOn_eq hab c]
  simp only [Units.val_mul, Matrix.det_mul, det_tr, one_mul]

private theorem actB_factor (d : Fin 6 → Kˣ) (hd : ∏ i, d i = 1) :
    ∃ e₀ e₁ f₀ f₁ : Kˣ, d = cOn 0 3 (d 0 * d 1 * d 2) *
      (cOn 0 1 e₀ * cOn 1 2 e₁ * cOn 3 4 f₀ * cOn 4 5 f₁) := by
  refine ⟨d 0 * (d 0 * d 1 * d 2)⁻¹, d 0 * (d 0 * d 1 * d 2)⁻¹ * d 1,
    d 3 * (d 0 * d 1 * d 2), d 3 * (d 0 * d 1 * d 2) * d 4, ?_⟩
  rw [Fin.prod_univ_six] at hd
  have hK : (d 0 : K) * d 1 * d 2 * d 3 * d 4 * d 5 = 1 := by
    have h := congrArg Units.val hd
    simpa [Units.val_mul] using h
  have n0 : (d 0 : K) ≠ 0 := Units.ne_zero _
  have n1 : (d 1 : K) ≠ 0 := Units.ne_zero _
  have n2 : (d 2 : K) ≠ 0 := Units.ne_zero _
  have n3 : (d 3 : K) ≠ 0 := Units.ne_zero _
  have n4 : (d 4 : K) ≠ 0 := Units.ne_zero _
  funext i
  apply Units.ext
  fin_cases i <;> simp [cOn, Pi.mul_apply] <;> field_simp
  all_goals first | ring1 | linear_combination hK

theorem exists_xi [CharP K 2] (h0 : finrank K (A.Fix (Wc K I0)) = 1) :
    ∃ ξ : Kˣ →* Kˣ, ∀ c : Kˣ, ∀ v ∈ A.Fix (Wc K I0),
      A.act (dg (cOn 0 3 c)) v = ((ξ c : Kˣ) : K) • v := by
  obtain ⟨⟨v₀, hv₀⟩, hne0, -⟩ := finrank_eq_one_iff'.1 h0
  have hne : v₀ ≠ 0 := fun h => hne0 (Subtype.ext h)
  have hdet : ∀ c : Kˣ, ((dg (cOn 0 3 c) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det = 1 :=
    fun c => actB_det_cOn (by decide) c
  choose s hs using fun c : Kˣ => A.line_scalar h0 (A.act (dg (cOn 0 3 c)))
    (fun v hv => A.act_mem_Fix (hdet c) (fun w hw => dg_Wc_stable (cOn 0 3 c) I0 hw) hv)
  have hcOn : ∀ c c' : Kˣ, cOn 0 3 (c * c') = cOn 0 3 c * cOn 0 3 c' := by
    intro c c'
    funext i
    simp only [cOn, Pi.mul_apply]
    split_ifs <;> simp_all [mul_inv, mul_comm]
  have hsmul : ∀ c c' : Kˣ, s (c * c') = s c * s c' := by
    intro c c'
    refine smul_left_injective K hne ?_
    show s (c * c') • v₀ = (s c * s c') • v₀
    rw [← hs (c * c') v₀ hv₀, hcOn c c', dg_mul, A.act_mul _ _ (hdet c) (hdet c'),
      Module.End.mul_apply, hs c' v₀ hv₀, map_smul, hs c v₀ hv₀, smul_smul, mul_comm]
  have hs1 : s 1 = 1 := by
    have h1 := hs 1 v₀ hv₀
    have hc1 : cOn 0 3 (1 : Kˣ) = 1 := by
      funext i
      simp only [cOn, Pi.one_apply]
      split_ifs <;> simp
    rw [hc1, dg_one, A.act_one, Module.End.one_apply] at h1
    refine smul_left_injective K hne ?_
    show s 1 • v₀ = (1 : K) • v₀
    rw [one_smul]
    exact h1.symm
  have hsne : ∀ c : Kˣ, s c ≠ 0 := by
    intro c hc
    have h := hsmul c c⁻¹
    rw [mul_inv_cancel, hs1, hc, zero_mul] at h
    exact one_ne_zero h
  refine ⟨MonoidHom.mk' (fun c => Units.mk0 (s c) (hsne c)) (fun c c' => Units.ext (hsmul c c')),
    fun c v hv => ?_⟩
  rw [hs c v hv]
  simp

theorem act_cOn_block [CharP K 2] (h0 : finrank K (A.Fix (Wc K I0)) = 1) {a b : Fin 6}
    (hab : a ≠ b) (hblock : (a ∈ I0 ↔ b ∈ I0)) (c : Kˣ) :
    ∀ v ∈ A.Fix (Wc K I0), A.act (dg (cOn a b c)) v = v := by
  have hfix : ∀ (x y : Fin 6) (hxy : x ≠ y), (x ∈ I0 ↔ y ∈ I0) → ∀ t : K,
      ∀ v ∈ A.Fix (Wc K I0), A.act (transvGL K x y hxy t) v = v := by
    intro x y hxy hxyI t
    exact A.act_invol_fix (W := Wc K I0) (det_tr hxy t) (tr_sq hxy t)
      (fun w hw => tr_Wc_stable hxy t hxyI.symm.1 hw) h0
  intro v hv
  rw [dg_cOn_eq hab c]
  have hdx := actB_det_mul (det_tr hab (c : K)) (det_tr hab.symm ((c⁻¹ : Kˣ) : K))
  have hdy := actB_det_mul (det_tr hab (1 : K)) (det_tr hab.symm (1 : K))
  have hx12 := actB_fix_mul A (det_tr hab (c : K)) (det_tr hab.symm ((c⁻¹ : Kˣ) : K))
    (hfix a b hab hblock (c : K)) (hfix b a hab.symm hblock.symm ((c⁻¹ : Kˣ) : K))
  have hx123 := actB_fix_mul A hdx (det_tr hab (c : K)) hx12 (hfix a b hab hblock (c : K))
  have hy12 := actB_fix_mul A (det_tr hab (1 : K)) (det_tr hab.symm (1 : K))
    (hfix a b hab hblock 1) (hfix b a hab.symm hblock.symm 1)
  have hy123 := actB_fix_mul A hdy (det_tr hab (1 : K)) hy12 (hfix a b hab hblock 1)
  exact actB_fix_mul A (actB_det_mul hdx (det_tr hab (c : K)))
    (actB_det_mul hdy (det_tr hab (1 : K))) hx123 hy123 v hv

theorem weight_I0 [CharP K 2] (h0 : finrank K (A.Fix (Wc K I0)) = 1) {ξ : Kˣ →* Kˣ}
    (hξ : ∀ c : Kˣ, ∀ v ∈ A.Fix (Wc K I0), A.act (dg (cOn 0 3 c)) v = ((ξ c : Kˣ) : K) • v)
    (d : Fin 6 → Kˣ) (hd : ∏ i, d i = 1) :
    ∀ v ∈ A.Fix (Wc K I0), A.act (dg d) v = ((ξ (d 0 * d 1 * d 2) : Kˣ) : K) • v := by
  intro v hv
  obtain ⟨e₀, e₁, f₀, f₁, hfac⟩ := actB_factor d hd
  have hdg : (dg d : GL (Fin 6) K) = dg (cOn 0 3 (d 0 * d 1 * d 2)) *
      (dg (cOn 0 1 e₀) * dg (cOn 1 2 e₁) * dg (cOn 3 4 f₀) * dg (cOn 4 5 f₁)) := by
    conv_lhs => rw [hfac]
    simp only [dg_mul]
  have d1 : ((dg (cOn 0 1 e₀) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det = 1 :=
    actB_det_cOn (by decide) e₀
  have d2 : ((dg (cOn 1 2 e₁) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det = 1 :=
    actB_det_cOn (by decide) e₁
  have d3 : ((dg (cOn 3 4 f₀) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det = 1 :=
    actB_det_cOn (by decide) f₀
  have d4 : ((dg (cOn 4 5 f₁) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det = 1 :=
    actB_det_cOn (by decide) f₁
  have dP : ((dg (cOn 0 3 (d 0 * d 1 * d 2)) : GL (Fin 6) K) :
      Matrix (Fin 6) (Fin 6) K).det = 1 :=
    actB_det_cOn (by decide) _
  have d12 := actB_det_mul d1 d2
  have d123 := actB_det_mul d12 d3
  have dQ := actB_det_mul d123 d4
  have q1 : ∀ w ∈ A.Fix (Wc K I0), A.act (dg (cOn 0 1 e₀)) w = w :=
    act_cOn_block A h0 (by decide) (by decide) e₀
  have q2 : ∀ w ∈ A.Fix (Wc K I0), A.act (dg (cOn 1 2 e₁)) w = w :=
    act_cOn_block A h0 (by decide) (by decide) e₁
  have q3 : ∀ w ∈ A.Fix (Wc K I0), A.act (dg (cOn 3 4 f₀)) w = w :=
    act_cOn_block A h0 (by decide) (by decide) f₀
  have q4 : ∀ w ∈ A.Fix (Wc K I0), A.act (dg (cOn 4 5 f₁)) w = w :=
    act_cOn_block A h0 (by decide) (by decide) f₁
  have q12 := actB_fix_mul A d1 d2 q1 q2
  have q123 := actB_fix_mul A d12 d3 q12 q3
  have q1234 := actB_fix_mul A d123 d4 q123 q4
  rw [hdg, A.act_mul _ _ dP dQ, Module.End.mul_apply, q1234 v hv]
  exact hξ _ v hv

theorem weight_I [CharP K 2] (h0 : finrank K (A.Fix (Wc K I0)) = 1) {ξ : Kˣ →* Kˣ}
    (hξ : ∀ c : Kˣ, ∀ v ∈ A.Fix (Wc K I0), A.act (dg (cOn 0 3 c)) v = ((ξ c : Kˣ) : K) • v)
    {I : Finset (Fin 6)} (hI : I.card = 3) (d : Fin 6 → Kˣ) (hd : ∏ i, d i = 1) :
    ∀ v ∈ A.Fix (Wc K I), A.act (dg d) v = ((ξ (∏ i ∈ I, d i) : Kˣ) : K) • v := by
  obtain ⟨σ, hσI⟩ := exists_perm_image_eq I hI
  have hmap : (A.Fix (Wc K I0)).map (A.act (pm K σ)) = A.Fix (Wc K I) := by
    rw [A.act_pm_Fix σ I0, hσI]
  intro v hv
  have hv' : v ∈ (A.Fix (Wc K I0)).map (A.act (pm K σ)) := by
    rw [hmap]
    exact hv
  obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.1 hv'
  obtain ⟨F, hF⟩ : ∃ F : Fin 6 → Kˣ, ∀ i, F i = d (σ i) := ⟨fun i => d (σ i), fun i => rfl⟩
  have hFconj : pm K σ * dg F * (pm K σ)⁻¹ = dg d := by
    rw [pm_conj_dg]
    congr 1
    funext i
    rw [hF, Equiv.apply_symm_apply]
  have key : (dg d : GL (Fin 6) K) * pm K σ = pm K σ * dg F := by
    rw [← hFconj, inv_mul_cancel_right]
  have hFprod : ∏ i, F i = 1 := by
    simp only [hF]
    rw [Equiv.prod_comp σ d, hd]
  have hdetd : ((dg d : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det = 1 := by
    rw [det_dg, ← Units.coe_prod, hd, Units.val_one]
  have hdetF : ((dg F : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det = 1 := by
    rw [det_dg, ← Units.coe_prod, hFprod, Units.val_one]
  have hdetp : ((pm K σ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det = 1 := det_pm σ
  have hsum : ∏ i ∈ I, d i = F 0 * F 1 * F 2 := by
    rw [← hσI, Finset.prod_image (s := I0) (g := σ) (fun x _ y _ h => σ.injective h),
      hF 0, hF 1, hF 2, show I0 = ({0, 1, 2} : Finset (Fin 6)) from rfl,
      Finset.prod_insert (show (0 : Fin 6) ∉ ({1, 2} : Finset (Fin 6)) by decide),
      Finset.prod_insert (show (1 : Fin 6) ∉ ({2} : Finset (Fin 6)) by decide),
      Finset.prod_singleton, mul_assoc]
  have e1 : A.act (dg d) (A.act (pm K σ) w) = A.act (dg d * pm K σ) w := by
    rw [A.act_mul _ _ hdetd hdetp, Module.End.mul_apply]
  rw [e1, key, A.act_mul _ _ hdetp hdetF, Module.End.mul_apply,
    weight_I0 A h0 hξ F hFprod w hw, map_smul, hsum]

end SLAct

end CFSG.RankThree.GF2n.Smith81.S81J
