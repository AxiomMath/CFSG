module

public import CFSG.Quasithin.Vol2.Ch11SecAKB1
public import CFSG.Quasithin.Vol2.Ch11SecAFacts15c

public section

namespace CFSG.Quasithin.Vol2.KGNat

open CFSG.Open CFSG.Quasithin Matrix CFSG.ClassicalInvolution.ModelFacts.OddCover
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Assembly.LowTwoRank (StatedSL specialLinearGroupEquivStatedSL)

namespace PointStab

section Diag

variable {K : Type} [Field K]

@[expose] def dSL3 (t : Kˣ) : SpecialLinearGroup (Fin 3) K :=
  ⟨Matrix.diagonal ![(t : K), ((t⁻¹ : Kˣ) : K), 1], by
    simp [Matrix.det_diagonal, Fin.prod_univ_three]⟩

theorem coe_dSL3 (t : Kˣ) : ((dSL3 t : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
    Matrix.diagonal ![(t : K), ((t⁻¹ : Kˣ) : K), 1] := rfl

theorem dSL3_mul (s t : Kˣ) : dSL3 s * dSL3 t = dSL3 (s * t) := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_dSL3, coe_dSL3, coe_dSL3, Matrix.diagonal_mul_diagonal]
  fin_cases i <;> fin_cases j <;> simp [mul_comm]

theorem dSL3_one : dSL3 (1 : Kˣ) = 1 := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [coe_dSL3]
  fin_cases i <;> fin_cases j <;> simp

theorem dSL3_pow (t : Kˣ) (k : ℕ) : dSL3 t ^ k = dSL3 (t ^ k) := by
  induction k with
  | zero => rw [pow_zero, pow_zero, dSL3_one]
  | succ k ih => rw [pow_succ, ih, dSL3_mul, pow_succ]

theorem dSL3_inv (t : Kˣ) : (dSL3 t)⁻¹ = dSL3 t⁻¹ := by
  rw [inv_eq_of_mul_eq_one_right]
  rw [dSL3_mul, mul_inv_cancel, dSL3_one]

theorem dSL3_mulVec (t : Kˣ) (x : Fin 3 → K) :
    (dSL3 t : Matrix (Fin 3) (Fin 3) K) *ᵥ x = ![(t : K) * x 0, ((t⁻¹ : Kˣ) : K) * x 1, x 2] := by
  rw [coe_dSL3]
  funext i
  fin_cases i <;> simp [Matrix.mulVec_diagonal]

end Diag

section Point

variable {K : Type} [Field K] [Finite K] {W : Type*} [CommGroup W]
  {H : Subgroup (MulAut W)} {Z : Subgroup W} {π : ↥(StatedSL 3 K) →* ↥H} {f : W → (Fin 3 → K)}

omit [Finite K] in
theorem ginv_f_rho (hf : IsCoord (linModelNat (StatedSL 3 K)) H Z π f)
    (g B : SpecialLinearGroup (Fin 3) K) (w : W) :
    ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
        f (((rho3 π (g * B * g⁻¹) : ↥H) : MulAut W) w) =
      (B : Matrix (Fin 3) (Fin 3) K) *ᵥ
        (((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ f w) := by
  rw [hf.act3, gconj_mulVec, ginv_g_mulVec]

omit [Finite K] in
theorem mem_U1_iff (hf : IsCoord (linModelNat (StatedSL 3 K)) H Z π f)
    (g : SpecialLinearGroup (Fin 3) K) (w : W) :
    w ∈ hf.pre (gmap g (flagSpace 3 K 1)).toAddSubgroup ↔
      (((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ f w) 1 = 0 ∧
        (((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ f w) 2 = 0 := by
  show f w ∈ gmap g (flagSpace 3 K 1) ↔ _
  rw [mem_gmap, ← stdLine_eq_flagSpace]
  exact Iff.rfl

end Point

end PointStab

open PointStab in
theorem factPointTorusSL3_holds : Ch11.SecA.FactPointTorusSL3 := by
  intro K _ _ n hn hK W _ _ hW H Z π hπ P hP U hU
  have hSL := commutator_SL2_eq_top (four_le_card hn hK)
  obtain ⟨f, hf⟩ := exists_isCoord (linModelNat _) hπ
  obtain ⟨g, hg⟩ := exists_sylow_eq_conj_Usl hK (by omega) hf hP
  rw [← hK] at hU
  rw [eq_U1_of_isFlagW hW hf hg hU]
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hpow : ∀ x : Kˣ, ∃ k : ℕ, ζ ^ k = x := fun x =>
    (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr (hζ x))
  have hdpow : ∀ k : ℕ, ((rho3 π (g * dSL3 ζ * g⁻¹) : ↥H) : MulAut W) ^ k =
      ((rho3 π (g * dSL3 (ζ ^ k) * g⁻¹) : ↥H) : MulAut W) := by
    intro k
    rw [← Subgroup.coe_pow, ← map_pow, conj_pow, dSL3_pow]
  have hstab : ∀ B : Matrix.SpecialLinearGroup (Fin 3) K,
      (∀ x : Fin 3 → K, ((B : Matrix (Fin 3) (Fin 3) K) *ᵥ x) 1 = 0 ∧
        ((B : Matrix (Fin 3) (Fin 3) K) *ᵥ x) 2 = 0 ↔ x 1 = 0 ∧ x 2 = 0) →
      ((rho3 π (g * B * g⁻¹) : ↥H) : MulAut W) ∈
        Ch11.SecA.stabW (hf.pre (gmap g (flagSpace 3 K 1)).toAddSubgroup) := by
    intro B hB w
    rw [mem_U1_iff hf g, mem_U1_iff hf g, ginv_f_rho hf g B w]
    exact (hB _).symm
  have hdU : ((rho3 π (g * dSL3 ζ * g⁻¹) : ↥H) : MulAut W) ∈
      Ch11.SecA.stabW (hf.pre (gmap g (flagSpace 3 K 1)).toAddSubgroup) := by
    refine hstab _ fun x => ?_
    rw [dSL3_mulVec]
    simp
  refine ⟨_, ⟨(rho3 π _).2, hdU⟩, ?_, ?_, ?_⟩
  ·
    rintro h ⟨hhH, hhU⟩
    obtain ⟨A, hA⟩ := (rho3_bijective hf).2 ⟨h, hhH⟩
    have hhB : h = ((rho3 π (g * (g⁻¹ * A * g) * g⁻¹) : ↥H) : MulAut W) := by
      rw [show g * (g⁻¹ * A * g) * g⁻¹ = A by group, hA]
    set B := g⁻¹ * A * g with hB
    obtain ⟨w₀, hw₀⟩ := hf.surj ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0])
    have hgw₀ : ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
        f w₀ = ![1, 0, 0] := by rw [hw₀, ginv_g_mulVec]
    have hw₀U : w₀ ∈ hf.pre (gmap g (flagSpace 3 K 1)).toAddSubgroup :=
      (mem_U1_iff hf g w₀).mpr (by rw [hgw₀]; simp)
    have hBe : ((B : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0]) 1 = 0 ∧
        ((B : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0]) 2 = 0 := by
      have h1 := (mem_U1_iff hf g _).mp ((Ch11.SecA.mem_stabW.mp hhU w₀).mp hw₀U)
      rwa [hhB, ginv_f_rho hf g B w₀, hgw₀] at h1
    set l := ((B : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0]) 0 with hl
    have hBl : (B : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0] = ![l, 0, 0] :=
      vec3_eq (by simp [hl]) (by simp [hBe.1]) (by simp [hBe.2])
    have hl0 : l ≠ 0 := by
      intro h0
      have h1 : (B : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0] = 0 := by
        rw [hBl, h0]
        exact vec3_eq (by simp) (by simp) (by simp)
      have h2 := ginv_g_mulVec B ![1, 0, 0]
      rw [h1, Matrix.mulVec_zero] at h2
      simpa using congrFun h2 0
    obtain ⟨k, hk⟩ := hpow (Units.mk0 l hl0)
    refine ⟨k, (mem_perfectCore_HU1_iff hSL hf g _).mpr ⟨B * dSL3 (ζ ^ k)⁻¹, ?_, ?_⟩⟩
    · have e1 : ((dSL3 (ζ ^ k)⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0] = l⁻¹ • ![1, 0, 0] := by
        rw [dSL3_mulVec, hk]
        exact vec3_eq (by simp) (by simp) (by simp)
      rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, e1, Matrix.mulVec_smul, hBl]
      exact vec3_eq (by simp [hl0]) (by simp) (by simp)
    · rw [hhB, hdpow k, ← dSL3_inv, ← Subgroup.coe_inv, ← Subgroup.coe_mul, ← map_inv,
        ← map_mul]
      congr 2
      group
  ·
    refine ⟨Nat.card K - 1, ?_, ?_⟩
    · rw [hK]
      exact Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one
    · have hζm : ζ ^ (Nat.card K - 1) = 1 := by
        rw [← Nat.card_units K]
        exact pow_card_eq_one'
      rw [hdpow, hζm, dSL3_one, mul_one, mul_inv_cancel, map_one]
      exact Subgroup.one_mem _
  ·
    intro u hu w hw huZ hwZ
    obtain ⟨hu1, hu2⟩ := (mem_U1_iff hf g u).mp hu
    obtain ⟨hw1, hw2⟩ := (mem_U1_iff hf g w).mp hw
    have hcoord : ∀ {v : W}, (((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) *ᵥ f v) 1 = 0 →
        (((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ f v) 2 = 0 →
        v ∉ Z → ∃ s : K, s ≠ 0 ∧ ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K) *ᵥ f v = ![s, 0, 0] := by
      intro v h1 h2 hvZ
      refine ⟨_, ?_, vec3_eq rfl (by simpa using h1) (by simpa using h2)⟩
      intro h0
      apply hvZ
      rw [← hf.ker]
      have h3 : ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
          f v = 0 := vec3_eq (by rw [Pi.zero_apply]; exact h0) (by simpa using h1)
            (by simpa using h2)
      have h4 := congrArg (fun x => (g : Matrix (Fin 3) (Fin 3) K) *ᵥ x) h3
      simpa only [g_ginv_mulVec, Matrix.mulVec_zero] using h4
    obtain ⟨s, hs0, hsu⟩ := hcoord hu1 hu2 huZ
    obtain ⟨t, ht0, htw⟩ := hcoord hw1 hw2 hwZ
    obtain ⟨k, hk⟩ := hpow (Units.mk0 (t / s) (div_ne_zero ht0 hs0))
    refine ⟨k, (hf.eq_iff _ _).mp ?_⟩
    have h1 : ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
        f ((((rho3 π (g * dSL3 ζ * g⁻¹) : ↥H) : MulAut W) ^ k) u) =
        ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ f w := by
      rw [hdpow k, ginv_f_rho hf g _ u, hsu, htw, dSL3_mulVec, hk]
      exact vec3_eq (by simp [hs0]) (by simp) (by simp)
    have h2 := congrArg (fun x => (g : Matrix (Fin 3) (Fin 3) K) *ᵥ x) h1
    simpa only [g_ginv_mulVec] using h2

end CFSG.Quasithin.Vol2.KGNat
