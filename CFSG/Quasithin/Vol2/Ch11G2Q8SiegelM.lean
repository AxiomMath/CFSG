module

public import CFSG.Quasithin.Vol2.Ch11G2Q8NormD
public import CFSG.Quasithin.Vol2.Ch11G2Q8N13
public import CFSG.Quasithin.Vol2.Ch11G2Q8Cartan

public section

namespace CFSG.Quasithin.Vol2.Ch11.G2Q8

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.Vol2.KGNat Matrix

variable {F : Type} [Field F] [CharP F 2]

@[expose] noncomputable def tL (s : F) : ↥(cayleyGroup F) := g2A (tv 0 2 (by decide) s)

theorem g2Act_tL (s a b c d e f : F) :
    g2Act (tL s) (q6 a b c d e f) = q6 (a + s * c) b c d e (f + s * d) := by
  rw [tL, g2Act_tv]
  funext k
  rcases k with k | k <;> fin_cases k <;> simp [q6]

theorem tL_mul (s t : F) : tL s * tL t = tL (s + t) := by
  apply cayley_ext
  intro w
  rw [q6_eta w, g2Act_mul_apply, g2Act_tL, g2Act_tL, g2Act_tL]
  refine q6_congr ?_ rfl rfl rfl rfl ?_ <;> ring

theorem g2T_torHom2_comm_tL (a : Fˣ) (s : F) :
    g2T (torHom2 F a) * tL s = tL s * g2T (torHom2 F a) := by
  have ha : (a : F) ≠ 0 := a.ne_zero
  apply cayley_ext
  intro w
  rw [q6_eta w, g2Act_mul_apply, g2Act_mul_apply, g2Act_tL, g2Act_g2T_q6, g2Act_g2T_q6,
    g2Act_tL, torHom2_apply]
  simp only [Units.val_mul, Units.val_inv_eq_inv_val]
  refine q6_congr ?_ rfl rfl rfl rfl ?_
  · field_simp
  · field_simp

@[expose] def polarQ (x y : Ix3 → F) : F :=
  x (.inl 0) * y (.inr 0) + y (.inl 0) * x (.inr 0) + (x (.inl 1) * y (.inr 1) +
    y (.inl 1) * x (.inr 1)) + (x (.inl 2) * y (.inr 2) + y (.inl 2) * x (.inr 2))

@[expose] def normQ (x : Ix3 → F) : F :=
  x (.inl 0) * x (.inr 0) + x (.inl 1) * x (.inr 1) + x (.inl 2) * x (.inr 2)

omit [CharP F 2] in
theorem cayleyNorm_zI (x : Ix3 → F) : cayleyNorm (zI x) = normQ x := by
  rw [zI, cayleyNorm_zmk, normQ]
  ring

omit [CharP F 2] in
theorem normQ_add (x y : Ix3 → F) : normQ (x + y) = normQ x + normQ y + polarQ x y := by
  simp only [normQ, polarQ, Pi.add_apply]
  ring

theorem normQ_g2Act (g : ↥(cayleyGroup F)) (x : Ix3 → F) :
    normQ (g2Act g x) + (cgE g (zI x)).1 * (cgE g (zI x)).1 = normQ x := by
  have h := cg_norm g (zI x)
  rw [g2_zI_eq g x, norm_add_smul_one (cayleyTr_zI _), cayleyNorm_zI, cayleyNorm_zI] at h
  exact h

theorem polarQ_g2Act (g : ↥(cayleyGroup F)) (x y : Ix3 → F) :
    polarQ (g2Act g x) (g2Act g y) = polarQ x y := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hx := normQ_g2Act g x
  have hy := normQ_g2Act g y
  have hxy := normQ_g2Act g (x + y)
  have hr : (cgE g (zI (x + y))).1 = (cgE g (zI x)).1 + (cgE g (zI y)).1 := by
    rw [zI_add, map_add]
    rfl
  rw [map_add, normQ_add, normQ_add, hr] at hxy
  linear_combination hxy - hx - hy - (cgE g (zI x)).1 * (cgE g (zI y)).1 * h2

@[expose] def InC (w : Ix3 → F) : Prop := w (.inl 2) = 0 ∧ w (.inr 0) = 0

omit [CharP F 2] in
theorem inC_iff (w : Ix3 → F) :
    InC w ↔ polarQ w (q6 0 0 0 0 0 1) = 0 ∧ polarQ w (q6 1 0 0 0 0 0) = 0 := by
  simp [InC, polarQ, q6]

theorem g2Act_mem_C_of_stabQ {γ : ↥(cayleyGroup F)} (hγ : γ ∈ stabQ (stdF F 2))
    {w : Ix3 → F} (hw : InC w) : InC (g2Act γ w) := by
  have hγi := (stabQ (stdF F 2)).inv_mem hγ
  have hu : g2Act γ⁻¹ (q6 1 0 0 0 0 0) ∈ stdF F 2 :=
    (mem_stabQ.mp hγi _).mp (mem_stdF_two.mpr ⟨rfl, rfl, rfl, rfl⟩)
  have hv : g2Act γ⁻¹ (q6 0 0 0 0 0 1) ∈ stdF F 2 :=
    (mem_stabQ.mp hγi _).mp (mem_stdF_two.mpr ⟨rfl, rfl, rfl, rfl⟩)
  obtain ⟨a1, a2, a3, a4⟩ := mem_stdF_two.mp hu
  obtain ⟨b1, b2, b3, b4⟩ := mem_stdF_two.mp hv
  obtain ⟨c1, c2⟩ := hw
  rw [inC_iff]
  constructor
  · rw [← g2Act_apply_inv γ (q6 0 0 0 0 0 1), polarQ_g2Act]
    simp [polarQ, b1, b2, b3, b4, c1, c2]
  · rw [← g2Act_apply_inv γ (q6 1 0 0 0 0 0), polarQ_g2Act]
    simp [polarQ, a1, a2, a3, a4, c1, c2]

omit [CharP F 2] in
theorem zI_mul_v0_v1 :
    cayleyMul (zI (q6 (0 : F) 0 0 1 0 0)) (zI (q6 0 0 0 0 1 0)) = zI (q6 0 0 1 0 0 0) := by
  rw [zI_q6, zI_q6, zI_q6, cayleyMul_zmk]
  apply zmk_congr <;> ring

theorem g2Act_tL_of_inC (s : F) {x : Ix3 → F} (hx : InC x) : g2Act (tL s) x = x := by
  obtain ⟨c1, c2⟩ := hx
  conv_lhs => rw [q6_eta x]
  conv_rhs => rw [q6_eta x]
  rw [g2Act_tL, c1, c2, mul_zero, add_zero, add_zero]

theorem g2Act_tL_sub_mem (s : F) (x : Ix3 → F) : g2Act (tL s) x - x ∈ stdF F 2 := by
  have h : g2Act (tL s) x - x = q6 (s * x (.inl 2)) 0 0 0 0 (s * x (.inr 0)) := by
    conv_lhs => rw [q6_eta x]
    rw [g2Act_tL]
    funext j
    rcases j with j | j <;> fin_cases j <;> simp [q6]
  rw [h]
  exact mem_stdF_two.mpr ⟨rfl, rfl, rfl, rfl⟩

theorem eq_tL_of_shape {y : ↥(cayleyGroup F)} (hC : ∀ w, InC w → g2Act y w = w)
    (hF : ∀ w, g2Act y w - w ∈ stdF F 2) : ∃ s : F, y = tL s := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have ha := mem_stdF_two.mp (hF (q6 0 0 1 0 0 0))
  have hb := mem_stdF_two.mp (hF (q6 0 0 0 1 0 0))
  simp only [Pi.sub_apply, q6_apply_inl1, q6_apply_inl2, q6_apply_inr0, q6_apply_inr1,
    sub_zero, sub_eq_zero] at ha hb
  obtain ⟨a1, a2, a3, a4⟩ := ha
  obtain ⟨b1, b2, b3, b4⟩ := hb
  obtain ⟨α, hα⟩ : ∃ α, g2Act y (q6 0 0 1 0 0 0) (.inl 0) = α := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β, g2Act y (q6 0 0 1 0 0 0) (.inr 2) = β := ⟨_, rfl⟩
  obtain ⟨γ, hγ⟩ : ∃ γ, g2Act y (q6 0 0 0 1 0 0) (.inl 0) = γ := ⟨_, rfl⟩
  obtain ⟨δ, hδ⟩ : ∃ δ, g2Act y (q6 0 0 0 1 0 0) (.inr 2) = δ := ⟨_, rfl⟩
  have hu2 : g2Act y (q6 0 0 1 0 0 0) = q6 α 0 1 0 0 β := by
    rw [q6_eta (g2Act y (q6 0 0 1 0 0 0)), a1, a2, a3, a4, hα, hβ]
  have hv0 : g2Act y (q6 0 0 0 1 0 0) = q6 γ 0 0 1 0 δ := by
    rw [q6_eta (g2Act y (q6 0 0 0 1 0 0)), b1, b2, b3, b4, hγ, hδ]
  have hv1 : g2Act y (q6 0 0 0 0 1 0) = q6 0 0 0 0 1 0 := hC _ ⟨rfl, rfl⟩
  have hu1 : g2Act y (q6 0 1 0 0 0 0) = q6 0 1 0 0 0 0 := hC _ ⟨rfl, rfl⟩
  obtain ⟨r₁, e1⟩ := exists_cgE_zI y hv0
  obtain ⟨r₂, e2⟩ := exists_cgE_zI y hv1
  obtain ⟨r₃, e3⟩ := exists_cgE_zI y hu2
  obtain ⟨r₄, e4⟩ := exists_cgE_zI y hu1
  have hm1 := cg_mul y (zI (q6 0 0 0 1 0 0)) (zI (q6 0 0 0 0 1 0))
  rw [zI_mul_v0_v1, e1, e2, e3, cayleyMul_zmk] at hm1
  obtain ⟨-, k2, -, -, k5, -, k7, -⟩ := zmk_inj hm1
  have hm2 := cg_mul y (zI (q6 0 1 0 0 0 0)) (zI (q6 0 0 1 0 0 0))
  rw [zI_mul_u1_u2, e4, e3, e1, cayleyMul_zmk] at hm2
  obtain ⟨-, l2, -, l4, -, -, -, -⟩ := zmk_inj hm2
  have hr2 : r₂ = 0 := by linear_combination -k5
  have hr4 : r₄ = 0 := by linear_combination -l4
  have hβ0 : β = 0 := by linear_combination k7 + δ * hr2
  have hγ0 : γ = 0 := by linear_combination l2 + α * hr4
  have hαδ : α = δ := by linear_combination k2 + γ * hr2 - δ * h2
  refine ⟨α, cayley_ext fun w => ?_⟩
  have hw : w = (q6 (w (.inl 0)) (w (.inl 1)) 0 0 (w (.inr 1)) (w (.inr 2)) +
      w (.inl 2) • q6 0 0 1 0 0 0) + w (.inr 0) • q6 0 0 0 1 0 0 := by
    conv_lhs => rw [q6_eta w]
    rw [smul_q6, smul_q6]
    funext j
    rcases j with j | j <;> fin_cases j <;> simp [q6]
  have hwC : InC (q6 (w (.inl 0)) (w (.inl 1)) 0 0 (w (.inr 1)) (w (.inr 2))) := ⟨rfl, rfl⟩
  rw [hw, map_add, map_add, map_add, map_add, g2Act_smul, g2Act_smul, g2Act_smul, g2Act_smul,
    hC _ hwC, g2Act_tL_of_inC _ hwC, hu2, hv0, hβ0, hγ0, ← hαδ, g2Act_tL, g2Act_tL]
  funext j
  rcases j with j | j <;> fin_cases j <;> simp [q6]

theorem conj_tL_mem {γ : ↥(cayleyGroup F)} (hγ : γ ∈ stabQ (stdF F 2)) (s : F) :
    ∃ s' : F, γ * tL s * γ⁻¹ = tL s' := by
  have hγi := (stabQ (stdF F 2)).inv_mem hγ
  apply eq_tL_of_shape
  · intro w hw
    rw [g2Act_mul_apply, g2Act_mul_apply, g2Act_tL_of_inC s (g2Act_mem_C_of_stabQ hγi hw),
      g2Act_apply_inv]
  · intro w
    have e : g2Act (γ * tL s * γ⁻¹) w - w =
        g2Act γ (g2Act (tL s) (g2Act γ⁻¹ w) - g2Act γ⁻¹ w) := by
      rw [map_sub, g2Act_mul_apply, g2Act_mul_apply, g2Act_apply_inv]
    rw [e]
    exact (mem_stabQ.mp hγ _).mp (g2Act_tL_sub_mem s _)

end CFSG.Quasithin.Vol2.Ch11.G2Q8
