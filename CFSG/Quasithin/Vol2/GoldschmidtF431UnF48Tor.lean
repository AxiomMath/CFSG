module

public import CFSG.LieType.Universal.Unitary.Extras.Unipotent
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnBN

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.Universal.Unitary.SUExtras CFSG.LieType.Steinberg CFSG.LieType.BorelTits Matrix

section Fpf

variable {F : Type} [Field F] [Finite F] {f : ℕ} [CharP F 2]

theorem exists_torus_param_un (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 2 ≤ f) :
    ∃ c : F, c ≠ 0 ∧ unitaryInvolution F 2 f c ≠ c ∧ c * unitaryInvolution F 2 f c ≠ 1 := by
  classical
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hord : orderOf g = (2 ^ f) ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, Fintype.card_units,
      ← Nat.card_eq_fintype_card, hF]
  have hq4 : 4 ≤ 2 ^ f :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hbar : unitaryInvolution F 2 f (g : F) = ((g ^ 2 ^ f : Fˣ) : F) := by
    rw [unitaryInvolution_apply, Units.val_pow_eq_pow_val]
  refine ⟨g, g.ne_zero, fun h1 => ?_, fun h1 => ?_⟩
  · have h2 : g ^ (2 ^ f - 1) = 1 := by
      have h3 : g ^ (2 ^ f - 1) * g = 1 * g := by
        rw [← pow_succ, Nat.sub_add_cancel (by omega), one_mul]
        apply Units.ext
        rw [← hbar]
        exact h1
      exact mul_right_cancel h3
    have h3 := Nat.le_of_dvd (by omega) (orderOf_dvd_of_pow_eq_one h2)
    rw [hord] at h3
    have key : (2 ^ f) ^ 2 ≥ 2 ^ f * 4 := by
      rw [sq]
      exact Nat.mul_le_mul_left _ hq4
    generalize (2 ^ f) ^ 2 = y at h3 key
    generalize 2 ^ f = x at h3 key hq4
    omega
  · have h2 : g ^ (2 ^ f + 1) = 1 := by
      apply Units.ext
      rw [pow_succ', Units.val_mul, Units.val_one, ← hbar]
      exact h1
    have h3 := Nat.le_of_dvd (by omega) (orderOf_dvd_of_pow_eq_one h2)
    rw [hord] at h3
    have key : (2 ^ f) ^ 2 ≥ 2 ^ f * 4 := by
      rw [sq]
      exact Nat.mul_le_mul_left _ hq4
    generalize (2 ^ f) ^ 2 = y at h3 key
    generalize 2 ^ f = x at h3 key hq4
    omega

omit [Finite F] in
theorem injective_torusDiag_un {σ : F ≃+* F} {c : F} (hc : c ≠ 0) (h1 : σ c ≠ c)
    (h2 : c * σ c ≠ 1) : Function.Injective ![c, c⁻¹, σ c, (σ c)⁻¹] := by
  have hσc : σ c ≠ 0 := (map_ne_zero σ).mpr hc
  have hsq : ∀ x : F, x ≠ 0 → x⁻¹ = x → x = 1 := by
    intro x hx hxx
    have hxx' : x * x = 1 := by
      calc x * x = x * x⁻¹ := by rw [hxx]
        _ = 1 := mul_inv_cancel₀ hx
    rcases mul_self_eq_one_iff.1 hxx' with h | h
    · exact h
    · rw [h, CharTwo.neg_eq]
  have hc1 : c⁻¹ ≠ c := fun h => h1 (by rw [hsq c hc h, map_one])
  have hs1 : (σ c)⁻¹ ≠ σ c := fun h => h1 (by
    have h3 := hsq _ hσc h
    have h4 : c = 1 := σ.injective (h3.trans (map_one σ).symm)
    rw [h3]
    exact h4.symm)
  have e1 : c ≠ σ c := fun h => h1 h.symm
  have e2 : c ≠ (σ c)⁻¹ := fun h => h2 ((mul_eq_one_iff_eq_inv₀ hσc).2 h)
  have e3 : c⁻¹ ≠ σ c := fun h => h2 (by rw [← h]; exact mul_inv_cancel₀ hc)
  have e4 : c⁻¹ ≠ (σ c)⁻¹ := fun h => h1 (inv_injective h).symm
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp at hij ⊢
  all_goals first
    | exact absurd hij e1 | exact absurd hij e1.symm
    | exact absurd hij e2 | exact absurd hij e2.symm
    | exact absurd hij e3 | exact absurd hij e3.symm
    | exact absurd hij e4 | exact absurd hij e4.symm
    | exact absurd hij hc1 | exact absurd hij hc1.symm
    | exact absurd hij hs1 | exact absurd hij hs1.symm

theorem idBelow_unU (hF : Nat.card F = (2 ^ f) ^ 2) {y : SU (unitaryInvolution F 2 f) 4}
    (hy : y ∈ unU hF 4) : IdBelow (lvl 1) 1 (mat (unitaryInvolution F 2 f) 4 y) :=
  idBelow_of_mem_iSup (unitaryInvolution_involutive hF) 1 _ (fun γ hγ => by
    have h : 0 < ht (ι := Fin (4 / 2)) γ := hγ.2
    omega) hy

theorem eq_one_of_comm_diagonal_un (hF : Nat.card F = (2 ^ f) ^ 2) {d : Fin 4 → F}
    (hd : Function.Injective d) {h y : SU (unitaryInvolution F 2 f) 4}
    (hh : mat (unitaryInvolution F 2 f) 4 h = diagonal d) (hy : y ∈ unU hF 4)
    (hc : h * y * h⁻¹ = y) : y = 1 := by
  have hid := idBelow_unU hF hy
  have hcomm : mat (unitaryInvolution F 2 f) 4 h * mat (unitaryInvolution F 2 f) 4 y =
      mat (unitaryInvolution F 2 f) 4 y * mat (unitaryInvolution F 2 f) 4 h := by
    rw [← map_mul, ← map_mul, mul_inv_eq_iff_eq_mul.1 hc]
  apply mat_injective
  rw [map_one]
  ext i j
  by_cases hij : j.val ≤ i.val
  · exact hid i j (by simp only [lvl]; omega)
  · have hne : i ≠ j := fun e => hij (by rw [e])
    have h1 := congrFun (congrFun hcomm i) j
    rw [hh, diagonal_mul, mul_diagonal] at h1
    have h2 : mat (unitaryInvolution F 2 f) 4 y i j * (d i - d j) = 0 := by
      linear_combination h1
    rw [one_apply_ne hne]
    exact (mul_eq_zero.1 h2).resolve_right (sub_ne_zero.2 (hd.ne hne))

end Fpf

section Cartan

variable {F : Type} [Field F] [Finite F] {f : ℕ} [CharP F 2] (hF : Nat.card F = (2 ^ f) ^ 2)
  (ζ : traceZero (unitaryInvolution F 2 f)) [hζ : Fact ((ζ : F) ≠ 0)]

theorem exists_cartan_un (hf : 2 ≤ f) :
    ∃ h ∈ unB hF 4 ⊓ unN hF 4 ζ, ∀ y ∈ unU hF 4, h * y * h⁻¹ = y → y = 1 := by
  obtain ⟨c, hc0, hc1, hc2⟩ := exists_torus_param_un hF hf
  have hσ := unitaryInvolution_involutive hF
  have h0 : (0 : ℕ) + 1 < 4 / 2 := by norm_num
  set k : Fin (4 / 2) := ⟨0, by norm_num⟩ with hk
  have hmem := shortTorus_mem_levelTorus (σ := unitaryInvolution F 2 f) hσ
    (k := k) h0 (Units.mk0 c hc0)
  have hdiag := coe_shortTorus (unitaryInvolution F 2 f) hσ (lowIdx_ne_succ h0)
    (lowIdx_ne_rev k k) (lowIdx_ne_rev _ _) (lowIdx_ne_rev _ _) hc0
  have hT : (shortTorus (unitaryInvolution F 2 f) hσ (lowIdx_ne_succ h0) (lowIdx_ne_rev k k)
      (lowIdx_ne_rev _ _) c) ∈ unT (F := F) (p := 2) (f := f) 4 :=
    (le_iSup (fun i => levelTorus (unitaryInvolution F 2 f) i) k) hmem
  refine ⟨_, by rw [unB_inf_unN hF ζ]; exact hT, fun y hy hc => ?_⟩
  have hd : shortTorusFun (unitaryInvolution F 2 f) (lowIdx k) (lowIdx ⟨k.val + 1, h0⟩) c =
      ![c, c⁻¹, unitaryInvolution F 2 f c, (unitaryInvolution F 2 f c)⁻¹] := by
    funext s
    fin_cases s <;> simp [shortTorusFun, lowIdx, hk, Fin.ext_iff]
  rw [hd] at hdiag
  exact eq_one_of_comm_diagonal_un hF (injective_torusDiag_un hc0 hc1 hc2) hdiag hy hc

end Cartan

end CFSG.Quasithin.H13.F431.Un
