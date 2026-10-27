module

public import CFSG.LocalAnalysis.StandardType.GGMaxRankWeyl

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint CFSG.Assembly
open CFSG.LieType.RootSystem


lemma l6m7_symmetrizer_E8 (i : Fin Tag.E8.rank) :
    (Tag.symmetrizer .E8) i i = 1 := by
  simp [Tag.symmetrizer]

theorem l6m7_iform_smul
    (w : WeylGroup .E8) (x y : Fin Tag.E8.rank → ℤ) :
    iform (τ := .E8) (w • x) (w • y) = iform (τ := .E8) x y := by
  induction w using (coxeterSystem .E8).simple_induction_left generalizing x y with
  | one => simp
  | mul_simple_left w i ih =>
    rw [show (simple .E8 i * w) • x = reflect .E8 i (w • x) by rw [mul_smul, simple_smul],
      show (simple .E8 i * w) • y = reflect .E8 i (w • y) by rw [mul_smul, simple_smul],
      iform_reflect, ih]

@[expose] noncomputable def l6m7_form
    (b : Fin Tag.E8.rank → ℤ) :
    (Fin Tag.E8.rank → ℤ) →ₗ[ℤ] ℤ where
  toFun v := iform (τ := .E8) v b
  map_add' v w := by rw [iform_add_left]
  map_smul' c v := iform_smul_left c v b

theorem l6m7_form_apply
    (b v : Fin Tag.E8.rank → ℤ) :
    l6m7_form b v = iform (τ := .E8) v b := rfl

@[expose] noncomputable def l6m7_R
    (b : Fin Tag.E8.rank → ℤ) :
    Module.End ℤ (Fin Tag.E8.rank → ℤ) :=
  LinearMap.id - (l6m7_form b).smulRight b

theorem l6m7_R_apply
    (b v : Fin Tag.E8.rank → ℤ) :
    l6m7_R b v = v - l6m7_form b v • b := by
  simp [l6m7_R]

theorem l6m7_R_neg
    (b : Fin Tag.E8.rank → ℤ) : l6m7_R (-b) = l6m7_R b := by
  apply LinearMap.ext
  intro v
  rw [l6m7_R_apply, l6m7_R_apply, l6m7_form_apply, l6m7_form_apply]
  have h1 : iform (τ := .E8) v (-b) = -iform (τ := .E8) v b := by
    rw [show -b = (-1 : ℤ) • b by simp, iform_smul_right]
    ring
  rw [h1]
  module

theorem l6m7_R_sq
    (b : Fin Tag.E8.rank → ℤ) (hb : iform (τ := .E8) b b = 2) :
    l6m7_R b * l6m7_R b = 1 := by
  apply LinearMap.ext
  intro v
  rw [Module.End.mul_apply, Module.End.one_apply, l6m7_R_apply, l6m7_R_apply,
    map_sub, map_smul]
  simp only [l6m7_form_apply]
  rw [hb]
  module

theorem l6m7_R_comm_of_form_zero
    (b b' : Fin Tag.E8.rank → ℤ)
    (hb : iform (τ := .E8) b b = 2) (hb' : iform (τ := .E8) b' b' = 2)
    (h : iform (τ := .E8) b b' = 0) :
    l6m7_R b * l6m7_R b' = l6m7_R b' * l6m7_R b := by
  apply LinearMap.ext
  intro v
  simp only [Module.End.mul_apply, l6m7_R_apply, map_sub, map_smul, LinearMap.sub_apply,
    LinearMap.smul_apply, smul_eq_mul, hb, hb', h, l6m7_form_apply, iform_comm b' b]
  module

private theorem l6m7_R_braid
    (b b' : Fin Tag.E8.rank → ℤ)
    (hb : iform (τ := .E8) b b = 2) (hb' : iform (τ := .E8) b' b' = 2)
    {c : ℤ} (hc : iform (τ := .E8) b b' = c) (hc2 : c * c = 1) :
    l6m7_R b * l6m7_R b' * l6m7_R b = l6m7_R b' * l6m7_R b * l6m7_R b' := by
  rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hc2 with ⟨hc1, -⟩ | ⟨hcn1, -⟩
  · rw [hc1] at hc
    have hc' : iform (τ := .E8) b' b = 1 := (iform_comm b' b).trans hc
    apply LinearMap.ext
    intro v
    simp only [Module.End.mul_apply, l6m7_R_apply, map_sub, map_smul, LinearMap.sub_apply,
      LinearMap.smul_apply, smul_eq_mul, hb, hb', hc, hc', l6m7_form_apply]
    module
  · rw [hcn1] at hc
    have hc' : iform (τ := .E8) b' b = -1 := (iform_comm b' b).trans hc
    apply LinearMap.ext
    intro v
    simp only [Module.End.mul_apply, l6m7_R_apply, map_sub, map_smul, LinearMap.sub_apply,
      LinearMap.smul_apply, smul_eq_mul, hb, hb', hc, hc', l6m7_form_apply]
    module

theorem l6m7_R_pow_three_of_sq_one
    (b b' : Fin Tag.E8.rank → ℤ)
    (hb : iform (τ := .E8) b b = 2) (hb' : iform (τ := .E8) b' b' = 2)
    {c : ℤ} (hc : iform (τ := .E8) b b' = c) (hc2 : c * c = 1) :
    (l6m7_R b * l6m7_R b') ^ 3 = 1 := by
  have hbraid := l6m7_R_braid b b' hb hb' hc hc2
  have hf := l6m7_R_sq b hb
  have hg := l6m7_R_sq b' hb'
  calc (l6m7_R b * l6m7_R b') ^ 3
      = (l6m7_R b * l6m7_R b' * l6m7_R b) * (l6m7_R b' * l6m7_R b * l6m7_R b') := by
        rw [pow_succ, pow_succ, pow_one]; group
    _ = (l6m7_R b' * l6m7_R b * l6m7_R b') * (l6m7_R b' * l6m7_R b * l6m7_R b') := by
        rw [hbraid]
    _ = 1 := by
        rw [show (l6m7_R b' * l6m7_R b * l6m7_R b') *
              (l6m7_R b' * l6m7_R b * l6m7_R b') =
            l6m7_R b' * l6m7_R b * (l6m7_R b' * l6m7_R b') * l6m7_R b *
              l6m7_R b' by group, hg]
        rw [show l6m7_R b' * l6m7_R b * 1 * l6m7_R b * l6m7_R b' =
            l6m7_R b' * (l6m7_R b * l6m7_R b) * l6m7_R b' by group, hf]
        rw [show l6m7_R b' * 1 * l6m7_R b' = l6m7_R b' * l6m7_R b' by group, hg]

theorem l6m7_weylAction_conj_eq_R
    (w : WeylGroup .E8) (i : Fin Tag.E8.rank) :
    weylAction (isFiniteType_cartan .E8) (w * simple .E8 i * w⁻¹) =
      l6m7_R (weylAction (isFiniteType_cartan .E8) w (Pi.single i 1)) := by
  apply LinearMap.ext
  intro v
  rw [l6m7_R_apply, l6m7_form_apply]
  have hsimple : weylAction (isFiniteType_cartan .E8) (simple .E8 i) =
      reflection (Tag.cartan .E8) i :=
    weylAction_simple (hA := isFiniteType_cartan .E8) i
  rw [mul_assoc, weylAction_mul_apply, weylAction_mul_apply, hsimple, reflection_apply]
  rw [map_sub, map_smul, weylAction_apply_inv_apply]
  have hc : iform (τ := .E8) v (weylAction (isFiniteType_cartan .E8) w (Pi.single i 1)) =
      ∑ j, (Tag.cartan .E8) i j * weylAction (isFiniteType_cartan .E8) w⁻¹ v j := by
    rw [← l6m7_iform_smul w⁻¹ v (weylAction (isFiniteType_cartan .E8) w (Pi.single i 1)),
      show w⁻¹ • (weylAction (isFiniteType_cartan .E8) w (Pi.single i 1)) = Pi.single i 1 by
        rw [smul_def, ← weylAction_mul_apply, inv_mul_cancel, map_one, Module.End.one_apply],
      smul_def, iform_comm, iform_single_left, l6m7_symmetrizer_E8 i, one_mul]
  rw [hc]

@[expose] noncomputable def l6m7_epsNat (b : Fin 8 → (Fin Tag.E8.rank → ℤ)) : ℕ → ℤ
  | 0 => 1
  | n + 1 =>
      l6m7_epsNat b n *
        (if h : n < 7 then -iform (τ := .E8) (b ⟨n, by omega⟩) (b ⟨n + 1, by omega⟩) else 1)

@[expose] noncomputable def l6m7_eps (b : Fin 8 → (Fin Tag.E8.rank → ℤ)) (i : Fin 8) : ℤ :=
  l6m7_epsNat b i.val

theorem l6m7_epsNat_sq (b : Fin 8 → (Fin Tag.E8.rank → ℤ))
    (hc : ∀ k : Fin 7, iform (τ := .E8) (b (Fin.castSucc k)) (b (Fin.succ k)) *
      iform (τ := .E8) (b (Fin.castSucc k)) (b (Fin.succ k)) = 1) :
    ∀ n, l6m7_epsNat b n * l6m7_epsNat b n = 1 := by
  intro n
  induction n with
  | zero => simp [l6m7_epsNat]
  | succ n ih =>
    simp only [l6m7_epsNat]
    by_cases h : n < 7
    · rw [dif_pos h]
      have hk : iform (τ := .E8) (b ⟨n, by omega⟩) (b ⟨n + 1, by omega⟩) *
          iform (τ := .E8) (b ⟨n, by omega⟩) (b ⟨n + 1, by omega⟩) = 1 := by
        have h0 := hc ⟨n, h⟩
        have e1 : (Fin.castSucc ⟨n, h⟩ : Fin 8) = ⟨n, by omega⟩ := Fin.ext rfl
        have e2 : (Fin.succ ⟨n, h⟩ : Fin 8) = ⟨n + 1, by omega⟩ := Fin.ext rfl
        rwa [e1, e2] at h0
      nlinarith [ih, hk]
    · rw [dif_neg h, mul_one, ih]

theorem l6m7_eps_edge (b : Fin 8 → (Fin Tag.E8.rank → ℤ))
    (hc : ∀ k : Fin 7, iform (τ := .E8) (b (Fin.castSucc k)) (b (Fin.succ k)) *
      iform (τ := .E8) (b (Fin.castSucc k)) (b (Fin.succ k)) = 1) (i : Fin 7) :
    l6m7_eps b (Fin.castSucc i) * l6m7_eps b (Fin.succ i) *
      iform (τ := .E8) (b (Fin.castSucc i)) (b (Fin.succ i)) = -1 := by
  have hsq := l6m7_epsNat_sq b hc
  have hstep : l6m7_eps b (Fin.succ i) = l6m7_eps b (Fin.castSucc i) *
      (-iform (τ := .E8) (b (Fin.castSucc i)) (b (Fin.succ i))) := by
    show l6m7_epsNat b (i.val + 1) = l6m7_epsNat b i.val *
      (-iform (τ := .E8) (b (Fin.castSucc i)) (b (Fin.succ i)))
    rw [l6m7_epsNat, dif_pos i.isLt]
    rfl
  rw [hstep]
  have he : l6m7_eps b (Fin.castSucc i) * l6m7_eps b (Fin.castSucc i) = 1 := hsq i.val
  have hci := hc i
  nlinarith [he, hci]

end CFSG.StandardType

end
