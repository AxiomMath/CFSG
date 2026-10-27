module

public import CFSG.LieType.Universal.Unitary.Extras.Unipotent
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5BN

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un

set_option linter.unusedSectionVars false

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.Universal.Unitary.SUExtras CFSG.LieType.Steinberg CFSG.LieType.BorelTits Matrix

section Fpf

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem injective_torusDiag_un5 (g : Fˣ) (hg : orderOf g = 15) :
    Function.Injective ![((g ^ 1 : Fˣ) : F), ((g ^ 4 : Fˣ) : F), ((g ^ 0 : Fˣ) : F),
      ((g ^ 14 : Fˣ) : F), ((g ^ 11 : Fˣ) : F)] := by
  intro i j hij
  have key : ∀ a b : ℕ, ((g ^ a : Fˣ) : F) = ((g ^ b : Fˣ) : F) → a ≡ b [MOD 15] := fun a b h =>
    hg ▸ (pow_eq_pow_iff_modEq.1 (Units.ext h))
  fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at hij ⊢ <;>
  first
    | rfl
    | exact absurd (key _ _ hij) (by decide)

theorem idBelow_unU5 {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2) {y : SU (unitaryInvolution F 2 f) 5}
    (hy : y ∈ unU hF 5) : IdBelow (lvl 1) 1 (mat (unitaryInvolution F 2 f) 5 y) :=
  idBelow_of_mem_iSup (unitaryInvolution_involutive hF) 1 _ (fun γ hγ => by
    have h : 0 < ht (ι := Fin (5 / 2)) γ := hγ.2
    omega) hy

theorem eq_one_of_comm_diagonal_un5 {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2) {d : Fin 5 → F}
    (hd : Function.Injective d) {h y : SU (unitaryInvolution F 2 f) 5}
    (hh : mat (unitaryInvolution F 2 f) 5 h = diagonal d) (hy : y ∈ unU hF 5)
    (hc : h * y * h⁻¹ = y) : y = 1 := by
  have hid := idBelow_unU5 hF hy
  have hcomm : mat (unitaryInvolution F 2 f) 5 h * mat (unitaryInvolution F 2 f) 5 y =
      mat (unitaryInvolution F 2 f) 5 y * mat (unitaryInvolution F 2 f) 5 h := by
    rw [← map_mul, ← map_mul, mul_inv_eq_iff_eq_mul.1 hc]
  apply mat_injective
  rw [map_one]
  ext i j
  by_cases hij : j.val ≤ i.val
  · exact hid i j (by simp only [lvl]; omega)
  · have hne : i ≠ j := fun e => hij (by rw [e])
    have h1 := congrFun (congrFun hcomm i) j
    rw [hh, diagonal_mul, mul_diagonal] at h1
    have h2 : mat (unitaryInvolution F 2 f) 5 y i j * (d i - d j) = 0 := by
      linear_combination h1
    rw [one_apply_ne hne]
    exact (mul_eq_zero.1 h2).resolve_right (sub_ne_zero.2 (hd.ne hne))

end Fpf

section Cartan

variable {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = (2 ^ 2) ^ 2)
  (ζ : traceZero (unitaryInvolution F 2 2)) [hζ : Fact ((ζ : F) ≠ 0)]

theorem exists_cartan_un5 :
    ∃ h ∈ unB hF 5 ⊓ unN hF 5 ζ, ∀ y ∈ unU hF 5, h * y * h⁻¹ = y → y = 1 := by
  classical
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hord : orderOf g = 15 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, Fintype.card_units,
      ← Nat.card_eq_fintype_card, hF]
    norm_num
  have hσ := unitaryInvolution_involutive hF
  have h15 : (g : F) ^ 15 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hord, pow_orderOf_eq_one, Units.val_one]
  have hσg : unitaryInvolution F 2 2 (g : F) = ((g ^ 4 : Fˣ) : F) := by
    rw [unitaryInvolution_apply, Units.val_pow_eq_pow_val]
    norm_num
  have hσe : unitaryInvolution F 2 2 ((g ^ 5 : Fˣ) : F) = ((g ^ 5 : Fˣ) : F) := by
    rw [unitaryInvolution_apply, ← Units.val_pow_eq_pow_val, ← pow_mul]
    congr 1
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]
    calc (g : F) ^ (5 * 2 ^ 2) = (g : F) ^ 15 * (g : F) ^ 5 := by rw [← pow_add]; norm_num
      _ = (g : F) ^ 5 := by rw [h15, one_mul]
  have h0 : (0 : ℕ) + 1 < 5 / 2 := by norm_num
  have h1 : ¬ ((1 : ℕ) + 1 < 5 / 2) := by norm_num
  set k0 : Fin (5 / 2) := ⟨0, by norm_num⟩ with hk0
  set k1 : Fin (5 / 2) := ⟨1, by norm_num⟩ with hk1
  have hc0 : (g : F) ≠ 0 := g.ne_zero
  have he0 : ((g ^ 5 : Fˣ) : F) ≠ 0 := (g ^ 5).ne_zero
  have hmem0 := shortTorus_mem_levelTorus (σ := unitaryInvolution F 2 2) hσ (k := k0) h0 g
  have hmem1 := longTorus_mem_levelTorus (σ := unitaryInvolution F 2 2) (k := k1) h1
    (ζ := ζ) hζ.out (g ^ 5) hσe
  have hd0 := coe_shortTorus (unitaryInvolution F 2 2) hσ (lowIdx_ne_succ h0)
    (lowIdx_ne_rev k0 k0) (lowIdx_ne_rev _ _) (lowIdx_ne_rev _ _) hc0
  have hd1 := coe_longTorus (unitaryInvolution F 2 2) (lowIdx_ne_rev k1 k1) hζ.out hσe he0
  have hT0 := (le_iSup (fun i => levelTorus (unitaryInvolution F 2 2) i) k0) hmem0
  have hT1 := (le_iSup (fun i => levelTorus (unitaryInvolution F 2 2) i) k1) hmem1
  refine ⟨_, by rw [un5B_inf_N hF ζ]; exact mul_mem hT0 hT1, fun y hy hc => ?_⟩
  have hdiag : mat (unitaryInvolution F 2 2)
      5 (shortTorus (unitaryInvolution F 2 2) hσ (lowIdx_ne_succ h0) (lowIdx_ne_rev k0 k0)
        (lowIdx_ne_rev _ _) (g : F) * longTorus (unitaryInvolution F 2 2) (lowIdx_ne_rev k1 k1) ζ
          hσe) = diagonal ![((g ^ 1 : Fˣ) : F), ((g ^ 4 : Fˣ) : F), ((g ^ 0 : Fˣ) : F),
            ((g ^ 14 : Fˣ) : F), ((g ^ 11 : Fˣ) : F)] := by
    rw [map_mul]
    refine (congrArg₂ (· * ·) hd0 hd1).trans ((diagonal_mul_diagonal _ _).trans ?_)
    congr 1
    funext s
    fin_cases s <;> simp [shortTorusFun, longTorusFun, lowIdx, hk0, hk1, Fin.ext_iff, hσg]
    · rw [inv_mul_eq_iff_eq_mul₀ hc0]
      ring
    · rw [mul_inv_eq_iff_eq_mul₀ (pow_ne_zero 5 hc0)]
      linear_combination (-(g : F) ^ 4) * h15
    · exact inv_eq_of_mul_eq_one_right (by linear_combination h15)
  exact eq_one_of_comm_diagonal_un5 hF (injective_torusDiag_un5 g hord) hdiag hy hc

end Cartan

end CFSG.Quasithin.H13.F431.Un
