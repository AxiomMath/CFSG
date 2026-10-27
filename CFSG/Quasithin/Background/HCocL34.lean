module

public import CFSG.Quasithin.Background.HCocBase
public import CFSG.Quasithin.Background.HZL34B
public import CFSG.LieType.Multipliers.L34Model

public section

namespace CFSG.Quasithin.H.L34Z

open CFSG.Open CFSG.Fischer Matrix CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk
  CFSG.Quasithin.H.ZTrans CFSG.Quasithin.H.L3W9 CFSG.Quasithin.H13.Ch9.Herm9
  CFSG.Quasithin.H.Coc CFSG.LieType.Multipliers

@[expose] def l9A : List ℕ := [11, 27, 215, 17, 3, 346, 483, 291, 458]

@[expose] def l9B : List ℕ := [1, 101, 134, 65, 96, 120, 40, 428, 340]

@[expose] def l9Cons : List (Option ℕ × List ℕ × List ℕ) :=
  [(none, [0, 0], [142372, 186532, 0, 0, 130336, 0, 147624, 0, 0]),
    (none, [1, 1, 1, 1, 1], [198924, 0, 0, 0, 0, 0, 0, 0, 0]),
    (some 3, [0, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1],
      [0, 180492, 132096, 150528, 0, 205824, 186368, 0, 0]),
    (some 5, [0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0],
      [0, 0, 0, 135168, 0, 30720, 0, 0, 0]),
    (some 7, [0, 0, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0],
      [0, 0, 0, 0, 0, 72704, 0, 0, 0])]

@[expose] def l9Phi : List ℕ := [10, 2, 0, 0, 26, 0, 28, 0, 0, 19, 0, 0, 0, 0, 0, 0, 0, 0]

@[expose] def aM9 : Matrix (Fin 3) (Fin 3) F4 := mc [3, 2, 3, 3, 3, 2, 0, 0, 2]

@[expose] def bM9 : Matrix (Fin 3) (Fin 3) F4 := mc [1, 2, 0, 0, 0, 2, 0, 3, 2]

theorem cols_aM9 : cols aM9 = l9A := by
  decide +kernel

theorem cols_bM9 : cols bM9 = l9B := by
  decide +kernel

theorem l9_lt : ∀ c ∈ l9A ++ l9B, c < 2 ^ 9 := by
  decide +kernel

theorem l9_ok : consOK 9 16 [l9A, l9B] (fun t => colsU.getD t []) l9Cons = true := by
  decide +kernel

theorem l9_cert :
    matOf (2 * 9) (fun v => v ^^^ actM (w0Basis.map (packB 9 l9A l9B)) (actM l9Phi v)) =
      matOf (2 * 9) (conSum [l9A, l9B] 9 0 1 l9Cons) := by
  decide +kernel

theorem actsBy_rho9 {g : GL (Fin 3) F4} {c : List ℕ}
    (hc : cols (g : Matrix (Fin 3) (Fin 3) F4) = c) (hlen : c.length = 9) : ActsBy (rho9 g) c :=
  actsBy_of_lt hlen fun m hm => rho9_toW_cols g hc (lt_of_lt_of_eq hm (by norm_num))

theorem coe_genSL_zero :
    ((L34.genSL 0 : L34.SL3) : Matrix (Fin 3) (Fin 3) F4) = aM9 := by
  have h := L34.coe_lift_genSL [((0 : Fin 2), true)]
  rw [show FreeGroup.mk [((0 : Fin 2), true)] = FreeGroup.of 0 from rfl,
    FreeGroup.lift_apply_of] at h
  rw [h, show L34.wordMat [((0 : Fin 2), true)] =
      (L34.Mat3.ofFun fun i j => aM9 i j).mul L34.Mat3.one from rfl,
    L34.Mat3.toMatrix_mul, L34.Mat3.toMatrix_one, mul_one, L34.Mat3.toMatrix_ofFun]
  rfl

theorem coe_genSL_one :
    ((L34.genSL 1 : L34.SL3) : Matrix (Fin 3) (Fin 3) F4) = bM9 := by
  have h := L34.coe_lift_genSL [((1 : Fin 2), true)]
  rw [show FreeGroup.mk [((1 : Fin 2), true)] = FreeGroup.of 1 from rfl,
    FreeGroup.lift_apply_of] at h
  rw [h, show L34.wordMat [((1 : Fin 2), true)] =
      (L34.Mat3.ofFun fun i j => bM9 i j).mul L34.Mat3.one from rfl,
    L34.Mat3.toMatrix_mul, L34.Mat3.toMatrix_one, mul_one, L34.Mat3.toMatrix_ofFun]
  rfl

@[expose] noncomputable def rhoA9 : MulAut W9 :=
  rho9 (SpecialLinearGroup.toGL (L34.genSL 0))

@[expose] noncomputable def rhoB9 : MulAut W9 :=
  rho9 (SpecialLinearGroup.toGL (L34.genSL 1))

theorem actsBy_rhoA9 : ActsBy rhoA9 l9A :=
  actsBy_rho9 (by
    rw [show ((SpecialLinearGroup.toGL (L34.genSL 0) : GL (Fin 3) F4) :
      Matrix (Fin 3) (Fin 3) F4) = ((L34.genSL 0 : L34.SL3) : Matrix (Fin 3) (Fin 3) F4) from rfl,
      coe_genSL_zero]
    exact cols_aM9) rfl

theorem actsBy_rhoB9 : ActsBy rhoB9 l9B :=
  actsBy_rho9 (by
    rw [show ((SpecialLinearGroup.toGL (L34.genSL 1) : GL (Fin 3) F4) :
      Matrix (Fin 3) (Fin 3) F4) = ((L34.genSL 1 : L34.SL3) : Matrix (Fin 3) (Fin 3) F4) from rfl,
      coe_genSL_one]
    exact cols_bM9) rfl

theorem img9_le_closure :
    img9 ≤ Subgroup.closure {rhoA9, rhoB9} := by
  rw [img9, MonoidHom.range_eq_map, ← L34.closure_genSL, MonoidHom.map_closure]
  refine Subgroup.closure_mono ?_
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  fin_cases i
  · exact Or.inl (MonoidHom.comp_apply _ _ _)
  · exact Or.inr (MonoidHom.comp_apply _ _ _)

theorem u_tgt (t : ℕ) (ht : t < 16) : ∃ ρ ∈ Rbar, ActsBy ρ (colsU.getD t []) :=
  ⟨rho9 (uG t), rho9_uG_mem_Rbar ht, actsBy_rho9 (cols_uG ht) (by
    rw [← cols_uG ht]
    exact length_matOf 9 _)⟩

theorem coc_std
    {δ : MulAut W9 → W9} (hδ : ∀ g ∈ img9, ∀ k ∈ img9, δ (g * k) = δ g * g (δ k))
    (hR : ∀ r ∈ radZ img9 z0, δ r ∈ Subgroup.zpowers z0) :
    ∃ w ∈ vZ img9 z0, ∀ g ∈ img9, δ g = w * (g w)⁻¹ := by
  rw [radZ_std] at hR
  rw [vZ_std]
  obtain ⟨m, hm, h⟩ := eq_inner_std hδ (p := 0) (z := 1) hR (by norm_num) (by decide)
    img9_le_closure ⟨_, rfl⟩ ⟨_, rfl⟩ actsBy_rhoA9 actsBy_rhoB9 l9_lt u_tgt l9_ok w0_lt l9_cert
  exact ⟨toW 9 m, toW_mem_maskSub hm, h⟩

theorem coc_of_binaryNine
    {V : Type} [CommGroup V] [Finite V] {H : Subgroup (MulAut V)} (h : BinaryNineTensor H ⊤ ⊥ 1)
    {z : V} (hz1 : z ≠ 1) {S : Subgroup (MulAut V)} (hSH : S ≤ H)
    (hS : Nat.card ↥S = 2 ^ (Nat.card ↥H).factorization 2) (hzS : z ∈ fixV S)
    {δ : MulAut V → V} (hδ : ∀ g ∈ H, ∀ k ∈ H, δ (g * k) = δ g * g (δ k))
    (hR : ∀ r ∈ radZ H z, δ r ∈ Subgroup.zpowers z) :
    ∃ w ∈ vZ H z, ∀ g ∈ H, δ g = w * (g w)⁻¹ := by
  obtain ⟨e, he, hez⟩ := exists_equiv_z0 h hz1 hSH hS hzS
  refine coc_of_map e hδ hR fun δ₀ hδ₀ hR₀ => ?_
  have key : ∀ (A : Subgroup (MulAut W9)) (w : W9), A = img9 → w = z0 →
      ∀ δ₀ : MulAut W9 → W9, (∀ g ∈ A, ∀ k ∈ A, δ₀ (g * k) = δ₀ g * g (δ₀ k)) →
        (∀ r ∈ radZ A w, δ₀ r ∈ Subgroup.zpowers w) →
          ∃ w' ∈ vZ A w, ∀ g ∈ A, δ₀ g = w' * (g w')⁻¹ := by
    rintro A w rfl rfl δ₀ hδ₀ hR₀
    exact coc_std hδ₀ hR₀
  exact key _ _ he hez δ₀ hδ₀ hR₀

end CFSG.Quasithin.H.L34Z
