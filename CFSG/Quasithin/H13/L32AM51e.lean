module

public import CFSG.Quasithin.H13.L32AC51b
public import CFSG.Quasithin.H13.L32AC51d
public import CFSG.Quasithin.Background.SmithB42LnL4Models
public import CFSG.Quasithin.Background.P4GLAut
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBXBinaryIndexThreeParabolics
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListFlag

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.L32A.C

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

namespace Lin

local notation "𝕄₄" => Matrix (Fin 4) (Fin 4) (ZMod 2)

theorem x4_mem_uni (s : Fin 3) : B42Ln.x4 s ∈ unitriangular 4 (ZMod 2) :=
  ⟨fun i j hij => ((B42Ln.isUp4_xM4 s) i j).1 hij, fun i => ((B42Ln.isUp4_xM4 s) i i).2 rfl⟩

theorem inv_mul_coe (g : SLn 4) : ((g⁻¹ : SLn 4) : 𝕄₄) * (g : 𝕄₄) = 1 := by
  rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]

theorem mul_inv_coe (g : SLn 4) : (g : 𝕄₄) * ((g⁻¹ : SLn 4) : 𝕄₄) = 1 := by
  rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]

theorem entry_eq_zero {n : ℕ} {K : Type*} [Field K] {i : ℕ} {g : SpecialLinearGroup (Fin n) K}
    (hg : g ∈ stabilizer (flagSpace n K i)) {a b : Fin n} (hb : (b : ℕ) < i) (ha : i ≤ (a : ℕ)) :
    (g : Matrix (Fin n) (Fin n) K) a b = 0 := by
  have h1 : (g : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single b 1 ∈ flagSpace n K i := by
    rw [← mem_stabilizer.mp hg]
    exact ⟨_, BinaryParabolic.single_mem_flagSpace hb, rfl⟩
  have h2 := mem_flagSpace.mp h1 a ha
  rwa [mulVec_single_one] at h2

theorem wedge_eq_of_fixU {w : Fin 6 → ZMod 2}
    (hw : ∀ u ∈ unitriangular 4 (ZMod 2), B42Ln.wedgeRep4' u w = w) :
    w = 0 ∨ w = Pi.single 0 1 :=
  B42Ln.fixed_checks.2.2 w fun s => by
    have h := hw _ (x4_mem_uni s)
    rwa [B42Ln.wedgeRep4'_apply, B42Ln.coe_x4] at h

theorem wedge_fix_stab2 {g : SLn 4} (hg : g ∈ stabilizer (flagSpace 4 (ZMod 2) 2)) :
    B42Ln.wedgeRep4' g (Pi.single 0 1) = Pi.single 0 1 := by
  have h20 : (g : 𝕄₄) 2 0 = 0 := entry_eq_zero hg (a := 2) (b := 0) (by decide) (by decide)
  have h21 : (g : 𝕄₄) 2 1 = 0 := entry_eq_zero hg (a := 2) (b := 1) (by decide) (by decide)
  have h30 : (g : 𝕄₄) 3 0 = 0 := entry_eq_zero hg (a := 3) (b := 0) (by decide) (by decide)
  have h31 : (g : 𝕄₄) 3 1 = 0 := entry_eq_zero hg (a := 3) (b := 1) (by decide) (by decide)
  set c := (g : 𝕄₄) 0 0 * (g : 𝕄₄) 1 1 - (g : 𝕄₄) 0 1 * (g : 𝕄₄) 1 0 with hc
  have hcol : B42Ln.wedgeRep4' g (Pi.single 0 1) = c • Pi.single 0 1 := by
    rw [B42Ln.wedgeRep4'_apply]
    ext k
    fin_cases k <;>
      simp [JonesParshall.wedgeMat4, JonesParshall.pr4, mulVec, dotProduct, Pi.single_apply, h20,
        h21, h30, h31, hc]
  have hc0 : c ≠ 0 := by
    intro h0
    have h1 : B42Ln.wedgeRep4' g⁻¹ (B42Ln.wedgeRep4' g (Pi.single 0 1)) = Pi.single 0 1 := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [hcol, h0, zero_smul, map_zero] at h1
    have := congrFun h1 0
    simp at this
  rw [hcol, BinaryParabolic.eq_one_of_ne_zero c hc0, one_smul]

theorem wedge_fix_of_fixU {w : Fin 6 → ZMod 2}
    (hw : ∀ u ∈ unitriangular 4 (ZMod 2), B42Ln.wedgeRep4' u w = w) {g : SLn 4}
    (hg : g ∈ stabilizer (flagSpace 4 (ZMod 2) 2)) : B42Ln.wedgeRep4' g w = w := by
  rcases wedge_eq_of_fixU hw with rfl | rfl
  · exact map_zero _
  · exact wedge_fix_stab2 hg

theorem mulVec_e0 {g : SLn 4} (hg : g ∈ stabilizer (flagSpace 4 (ZMod 2) 1)) :
    (g : 𝕄₄) *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
  have h1 : (g : 𝕄₄) 1 0 = 0 := entry_eq_zero hg (a := 1) (b := 0) (by decide) (by decide)
  have h2 : (g : 𝕄₄) 2 0 = 0 := entry_eq_zero hg (a := 2) (b := 0) (by decide) (by decide)
  have h3 : (g : 𝕄₄) 3 0 = 0 := entry_eq_zero hg (a := 3) (b := 0) (by decide) (by decide)
  have hcol : (g : 𝕄₄) *ᵥ Pi.single 0 1 = (g : 𝕄₄) 0 0 • Pi.single 0 1 := by
    ext k
    fin_cases k <;> simp [mulVec, dotProduct, Pi.single_apply, h1, h2, h3]
  have hc0 : (g : 𝕄₄) 0 0 ≠ 0 := by
    intro h0
    have h4 := congrArg (fun v => ((g⁻¹ : SLn 4) : 𝕄₄) *ᵥ v) hcol
    simp only [mulVec_mulVec, inv_mul_coe, one_mulVec, h0, zero_smul, mulVec_zero] at h4
    have := congrFun h4 0
    simp at this
  rw [hcol, BinaryParabolic.eq_one_of_ne_zero _ hc0, one_smul]

theorem invT_e3 {g : SLn 4} (hg : g ∈ stabilizer (flagSpace 4 (ZMod 2) 3)) :
    ((g⁻¹ : SLn 4) : 𝕄₄)ᵀ *ᵥ Pi.single 3 1 = Pi.single 3 1 := by
  have hg' : g⁻¹ ∈ stabilizer (flagSpace 4 (ZMod 2) 3) := inv_mem hg
  set h := g⁻¹ with hh
  have h0 : (h : 𝕄₄) 3 0 = 0 := entry_eq_zero hg' (a := 3) (b := 0) (by decide) (by decide)
  have h1 : (h : 𝕄₄) 3 1 = 0 := entry_eq_zero hg' (a := 3) (b := 1) (by decide) (by decide)
  have h2 : (h : 𝕄₄) 3 2 = 0 := entry_eq_zero hg' (a := 3) (b := 2) (by decide) (by decide)
  have hcol : (h : 𝕄₄)ᵀ *ᵥ Pi.single 3 1 = (h : 𝕄₄) 3 3 • Pi.single 3 1 := by
    ext k
    fin_cases k <;> simp [mulVec, dotProduct, Pi.single_apply, transpose_apply, h0, h1, h2]
  have hc0 : (h : 𝕄₄) 3 3 ≠ 0 := by
    intro hz
    have hT : ((h⁻¹ : SLn 4) : 𝕄₄)ᵀ * (h : 𝕄₄)ᵀ = 1 := by
      rw [← transpose_mul, mul_inv_coe, transpose_one]
    have h4 := congrArg (fun v => ((h⁻¹ : SLn 4) : 𝕄₄)ᵀ *ᵥ v) hcol
    simp only [mulVec_mulVec, hT, one_mulVec, hz, zero_smul, mulVec_zero] at h4
    have := congrFun h4 3
    simp at this
  rw [hcol, BinaryParabolic.eq_one_of_ne_zero _ hc0, one_smul]

theorem par2_le_stab1 : par 4 2 ≤ stabilizer (flagSpace 4 (ZMod 2) 1) := fun _ hg =>
  mem_flagStabilizer.mp hg 1 ⟨⟨le_rfl, by norm_num⟩, by simp⟩

theorem par2_le_stab3 : par 4 2 ≤ stabilizer (flagSpace 4 (ZMod 2) 3) := fun _ hg =>
  mem_flagStabilizer.mp hg 3 ⟨⟨by norm_num, by norm_num⟩, by simp⟩

theorem nat_fix_of_fixU (κ : SLn 4 ≃* SLn 4) {w : Fin 4 → ZMod 2}
    (hw : ∀ u ∈ unitriangular 4 (ZMod 2), B42Ln.natRep4 (κ u) w = w) {g : SLn 4}
    (hg : g ∈ par 4 2) : B42Ln.natRep4 (κ g) w = w := by
  have hAA : ∀ A : GL (Fin 4) (ZMod 2),
      ((A⁻¹ : GL (Fin 4) (ZMod 2)) : 𝕄₄) * (A : 𝕄₄) = 1 := fun A => by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  rcases CFSG.Quasithin.G11.P4GL.aut_SL_cases (by norm_num : 3 ≤ 4) κ with ⟨A, hA⟩ | ⟨A, hA⟩
  · have hκ : ∀ x : SLn 4, ((κ x : SLn 4) : 𝕄₄) =
        (A : 𝕄₄) * (x : 𝕄₄) * ((A⁻¹ : GL (Fin 4) (ZMod 2)) : 𝕄₄) := fun x => by
      rw [hA]
      exact coe_slConjugation A x
    set w' := ((A⁻¹ : GL (Fin 4) (ZMod 2)) : 𝕄₄) *ᵥ w with hw'
    have hww : w = (A : 𝕄₄) *ᵥ w' := by
      rw [hw', mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
    have hfix : ∀ s : Fin 3, B42Ln.xM4 s *ᵥ w' = w' := by
      intro s
      have h1 := hw _ (x4_mem_uni s)
      rw [B42Ln.natRep4_apply, hκ, B42Ln.coe_x4] at h1
      rw [hw']
      conv_rhs => rw [← h1]
      simp only [mulVec_mulVec, ← Matrix.mul_assoc, hAA, Matrix.one_mul]
    rw [B42Ln.natRep4_apply, hκ]
    rcases B42Ln.fixed_checks.1 w' hfix with h0 | h0
    · rw [hww, h0, mulVec_zero, mulVec_zero]
    · rw [hww, mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, hAA, Matrix.mul_one,
        ← mulVec_mulVec, h0, mulVec_e0 (par2_le_stab1 hg)]
  · have hκ : ∀ x : SLn 4, ((κ x : SLn 4) : 𝕄₄) =
        (A : 𝕄₄) * ((x⁻¹ : SLn 4) : 𝕄₄)ᵀ * ((A⁻¹ : GL (Fin 4) (ZMod 2)) : 𝕄₄) := fun x => by
      rw [hA, MulAut.mul_apply]
      exact coe_slConjugation A _
    set w' := ((A⁻¹ : GL (Fin 4) (ZMod 2)) : 𝕄₄) *ᵥ w with hw'
    have hww : w = (A : 𝕄₄) *ᵥ w' := by
      rw [hw', mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
    have hfix : ∀ s : Fin 3, (B42Ln.xM4 s)ᵀ *ᵥ w' = w' := by
      intro s
      have h1 := hw _ (x4_mem_uni s)
      have hinv : ((B42Ln.x4 s)⁻¹ : SLn 4) = B42Ln.x4 s :=
        inv_eq_of_mul_eq_one_right (B42Ln.x4_mul_self s)
      rw [B42Ln.natRep4_apply, hκ, hinv, B42Ln.coe_x4] at h1
      rw [hw']
      conv_rhs => rw [← h1]
      simp only [mulVec_mulVec, ← Matrix.mul_assoc, hAA, Matrix.one_mul]
    rw [B42Ln.natRep4_apply, hκ]
    rcases B42Ln.fixed_checks.2.1 w' hfix with h0 | h0
    · rw [hww, h0, mulVec_zero, mulVec_zero]
    · rw [hww, mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, hAA, Matrix.mul_one,
        ← mulVec_mulVec, h0, invT_e3 (par2_le_stab3 hg)]

theorem par_le_stab2 {j : ℕ} (hj : j = 1 ∨ j = 3) :
    par 4 j ≤ stabilizer (flagSpace 4 (ZMod 2) 2) := fun _ hg =>
  mem_flagStabilizer.mp hg 2 ⟨⟨by norm_num, by norm_num⟩, by rcases hj with rfl | rfl <;> simp⟩

theorem relIndex_par {j : ℕ} (hj : 1 ≤ j) (hjn : j < 4) :
    (unitriangular 4 (ZMod 2)).relIndex (par 4 j) = 3 :=
  BinaryParabolic.relIndex_parabolic hj hjn

theorem not_par_le_normalizer {j : ℕ} (hj : 1 ≤ j) (hjn : j < 4) :
    ¬ par 4 j ≤ Subgroup.normalizer (unitriangular 4 (ZMod 2) : Set (SLn 4)) := by
  intro h
  have h1 := h (BinaryParabolic.reflection_mem_parabolic hj hjn)
  rw [normalizer_unitriangular, BinaryParabolic.upperTriangular_eq_unitriangular] at h1
  exact BinaryParabolic.reflection_notMem_unitriangular hj hjn h1

@[expose] def c1 : SLn 4 :=
  SpecialLinearGroup.transvection (show (0 : Fin 4) ≠ 1 by decide) 1 *
    SpecialLinearGroup.transvection (show (1 : Fin 4) ≠ 0 by decide) 1

@[expose] def c3 : SLn 4 :=
  SpecialLinearGroup.transvection (show (2 : Fin 4) ≠ 3 by decide) 1 *
    SpecialLinearGroup.transvection (show (3 : Fin 4) ≠ 2 by decide) 1

theorem c_facts : c1 ^ 3 = 1 ∧ c3 ^ 3 = 1 ∧ c1 * c3 = c3 * c1 := by
  decide +kernel

theorem c_indep : ∀ a b : ZMod 3, c1 ^ a.val * c3 ^ b.val = 1 → a = 0 ∧ b = 0 := by
  decide +kernel

theorem c_entries : ∀ p : Fin 4 × Fin 4,
    (((p.2 : ℕ) < 2 → 2 ≤ (p.1 : ℕ) → (c1 : 𝕄₄) p.1 p.2 = 0) ∧
      ((p.2 : ℕ) < 3 → 3 ≤ (p.1 : ℕ) → (c1 : 𝕄₄) p.1 p.2 = 0)) ∧
    (((p.2 : ℕ) < 1 → 1 ≤ (p.1 : ℕ) → (c3 : 𝕄₄) p.1 p.2 = 0) ∧
      ((p.2 : ℕ) < 2 → 2 ≤ (p.1 : ℕ) → (c3 : 𝕄₄) p.1 p.2 = 0)) := by
  decide

theorem c1_cube : c1 ^ 3 = 1 := c_facts.1

theorem c3_cube : c3 ^ 3 = 1 := c_facts.2.1

theorem c1_c3_comm : Commute c1 c3 := c_facts.2.2

theorem c1_mem : c1 ∈ par 4 1 := by
  refine CFSG.QuasithinUnique.Vol2Native.A312L.mem_flagStabilizer_of_entries fun k l c hc hl hk =>
    ?_
  obtain ⟨⟨-, hc3⟩, hc1⟩ := hc
  have hc1' : c ≠ 1 := hc1
  have hc' : c = 2 ∨ c = 3 := by omega
  rcases hc' with rfl | rfl
  · exact (c_entries (k, l)).1.1 hl hk
  · exact (c_entries (k, l)).1.2 hl hk

theorem c3_mem : c3 ∈ par 4 3 := by
  refine CFSG.QuasithinUnique.Vol2Native.A312L.mem_flagStabilizer_of_entries fun k l c hc hl hk =>
    ?_
  obtain ⟨⟨hc0, hc3⟩, hc1⟩ := hc
  have hc1' : c ≠ 3 := hc1
  have hc' : c = 1 ∨ c = 2 := by omega
  rcases hc' with rfl | rfl
  · exact (c_entries (k, l)).2.1 hl hk
  · exact (c_entries (k, l)).2.2 hl hk

@[expose] def e9 : Multiplicative (ZMod 3 × ZMod 3) →* SLn 4 where
  toFun a := c1 ^ (Multiplicative.toAdd a).1.val * c3 ^ (Multiplicative.toAdd a).2.val
  map_one' := by simp
  map_mul' a b := by
    simp only [toAdd_mul, Prod.fst_add, Prod.snd_add]
    rw [pow_val_add3 c1_cube, pow_val_add3 c3_cube]
    have hc := (c1_c3_comm.pow_left (Multiplicative.toAdd b).1.val).pow_right
      (Multiplicative.toAdd a).2.val
    calc c1 ^ (Multiplicative.toAdd a).1.val * c1 ^ (Multiplicative.toAdd b).1.val *
          (c3 ^ (Multiplicative.toAdd a).2.val * c3 ^ (Multiplicative.toAdd b).2.val)
        = c1 ^ (Multiplicative.toAdd a).1.val *
          (c1 ^ (Multiplicative.toAdd b).1.val * c3 ^ (Multiplicative.toAdd a).2.val) *
          c3 ^ (Multiplicative.toAdd b).2.val := by simp only [mul_assoc]
      _ = c1 ^ (Multiplicative.toAdd a).1.val *
          (c3 ^ (Multiplicative.toAdd a).2.val * c1 ^ (Multiplicative.toAdd b).1.val) *
          c3 ^ (Multiplicative.toAdd b).2.val := by rw [hc.eq]
      _ = _ := by simp only [mul_assoc]

theorem e9_injective : Function.Injective e9 := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  obtain ⟨ha, hb⟩ := c_indep _ _ (MonoidHom.mem_ker.mp hx)
  rw [Subgroup.mem_bot]
  apply Multiplicative.toAdd.injective
  rw [toAdd_one]
  ext
  · exact ha
  · exact hb

theorem card_e9 : Nat.card e9.range = 9 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective e9_injective).toEquiv, Nat.card_eq_fintype_card]
  rfl

theorem e9_comm : ∀ x ∈ e9.range, ∀ y ∈ e9.range, x * y = y * x := by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  rw [← map_mul, ← map_mul, mul_comm]

theorem e9_cube : ∀ x ∈ e9.range, x ^ 3 = 1 := by
  rintro _ ⟨a, rfl⟩
  rw [← map_pow]
  have h3 : ∀ p : ZMod 3 × ZMod 3, 3 • p = 0 := by decide
  have : a ^ 3 = 1 := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one]
    exact h3 _
  rw [this, map_one]

end Lin

end CFSG.Quasithin.H13.L32A.C
