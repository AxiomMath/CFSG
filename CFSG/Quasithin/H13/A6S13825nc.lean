module

public import CFSG.Quasithin.H13.A6S13825e
public import CFSG.Quasithin.H13.A6S13825s
public import CFSG.Sporadic.Schreier.J4SFrattini

public section

namespace CFSG.Quasithin.H13.A6.L4Tw

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open L4Ind

theorem tauW_mul_conj (g : SL4) : tauW * MulAut.conj g = MulAut.conj (tauW g) * tauW := by
  refine MulEquiv.ext fun x => ?_
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]

theorem tauW_mul_self : tauW * tauW = 1 := MulEquiv.ext fun g => tauW_tauW g

@[expose] def nf (A : SL4) (ε : Bool) : MulAut SL4 := MulAut.conj A * cond ε tauW 1

theorem nf_false (A : SL4) : nf A false = MulAut.conj A := mul_one _

theorem nf_true (A : SL4) : nf A true = MulAut.conj A * tauW := rfl

theorem nf_mul (A B : SL4) (ε δ : Bool) :
    nf A ε * nf B δ = nf (A * cond ε (tauW B) B) (xor ε δ) := by
  cases ε <;> cases δ
  · simp only [nf, Bool.cond_false, Bool.xor_false, mul_one, map_mul]
  · simp only [nf, Bool.cond_false, Bool.cond_true, Bool.false_xor, mul_one, map_mul, mul_assoc]
  · simp only [nf, Bool.cond_false, Bool.cond_true, Bool.xor_false, mul_one, map_mul]
    rw [mul_assoc, tauW_mul_conj, ← mul_assoc]
  · simp only [nf, Bool.cond_false, Bool.cond_true, Bool.xor_self, mul_one, map_mul]
    rw [mul_assoc, ← mul_assoc tauW, tauW_mul_conj, mul_assoc, tauW_mul_self, mul_one]

theorem conj_nf (H A : SL4) (ε : Bool) :
    MulAut.conj H * nf A ε * (MulAut.conj H)⁻¹ =
      nf (H * A * cond ε (tauW H⁻¹) H⁻¹) ε := by
  rw [← map_inv, ← nf_false, ← nf_false, nf_mul, nf_mul]
  cases ε <;> rfl

theorem conj_injective : Function.Injective (MulAut.conj : SL4 → MulAut SL4) := by
  intro A B h
  have hc : A⁻¹ * B ∈ Subgroup.center SL4 := by
    rw [Subgroup.mem_center_iff]
    intro y
    have := congrArg (fun φ : MulAut SL4 => φ y) h
    simp only [MulAut.conj_apply] at this
    calc y * (A⁻¹ * B) = A⁻¹ * (A * y * A⁻¹) * B := by group
      _ = A⁻¹ * (B * y * B⁻¹) * B := by rw [this]
      _ = A⁻¹ * B * y := by group
  rw [← scalars_eq_center, G11.P4GL.scalars_trivial, Subgroup.mem_bot, inv_mul_eq_one] at hc
  exact hc

abbrev uM (a b c d f : ZMod 2) : M4 := !![1, a, b, c; 0, 1, 0, d; 0, 0, 1, f; 0, 0, 0, 1]

theorem uM_mul : ∀ a b c d f a' b' c' d' f' : ZMod 2,
    uM a b c d f * uM a' b' c' d' f' =
      uM (a + a') (b + b') (c + c' + a * d' + b * f') (d + d') (f + f') := by
  intro a b c d f a' b' c' d' f'
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem uM_mul_inv (a b c d f : ZMod 2) : uM a b c d f * uM a b (c + a * d + b * f) d f = 1 := by
  rw [uM_mul]
  have h : ∀ x : ZMod 2, x + x = 0 := by decide
  have h2 : ∀ x y z : ZMod 2, x + (x + y + z) + y + z = 0 := by decide
  rw [h, h, h, h, h2]
  decide

@[expose] def uSL (a b c d f : ZMod 2) : SL4 :=
  L4Ind.mkSL (uM a b c d f) (uM a b (c + a * d + b * f) d f) (uM_mul_inv a b c d f)

theorem coe_uSL (a b c d f : ZMod 2) : ((uSL a b c d f : SL4) : M4) = uM a b c d f := rfl

theorem uSL_mul (a b c d f a' b' c' d' f' : ZMod 2) :
    uSL a b c d f * uSL a' b' c' d' f' =
      uSL (a + a') (b + b') (c + c' + a * d' + b * f') (d + d') (f + f') :=
  Subtype.ext (uM_mul a b c d f a' b' c' d' f')

theorem coe_uSL_inv (a b c d f : ZMod 2) :
    (((uSL a b c d f)⁻¹ : SL4) : M4) = uM a b (c + a * d + b * f) d f :=
  L4Ind.coe_mkSL_inv _ _ _

theorem tauW_uM : ∀ a b c d f : ZMod 2,
    w0M * (uM a b (c + a * d + b * f) d f)ᵀ * w0M = uM f d (c + a * d + b * f) b a := by
  decide

theorem tauW_uSL (a b c d f : ZMod 2) :
    tauW (uSL a b c d f) = uSL f d (c + a * d + b * f) b a := by
  apply Subtype.ext
  rw [tauW_matrix, coe_uSL_inv, coe_uSL]
  exact tauW_uM a b c d f

abbrev q1M : M4 := !![1, 0, 0, 0; 0, 0, 1, 0; 0, 1, 0, 0; 0, 0, 0, 1]

abbrev q2M : M4 := !![1, 0, 0, 0; 0, 1, 0, 0; 0, 1, 1, 0; 0, 0, 0, 1]

@[expose] def q1 : SL4 := L4Ind.mkSL q1M q1M (by decide)

@[expose] def q2 : SL4 := L4Ind.mkSL q2M q2M (by decide)

theorem q1_mul_self : q1 * q1 = 1 := Subtype.ext (by decide)

theorem q2_mul_self : q2 * q2 = 1 := Subtype.ext (by decide)

abbrev Q13 : Subgroup SL4 := flagStabilizer 4 (ZMod 2) (L13825.minPar 4 2)

theorem flag_inf_Q13 :
    flagStabilizer 4 (ZMod 2) {2} ⊓ Q13 = unitriangular 4 (ZMod 2) := by
  rw [Q13, ← CFSG.Quasithin.SBd8.Flag.flagStabilizer_union, ← L13825.flagStabilizer_fullCuts]
  congr 1
  ext i
  simp only [Set.mem_union, Set.mem_singleton_iff, L13825.minPar, L13825.fullCuts,
    Set.mem_ofPred_eq]
  omega

theorem entry_eq_zero {g : SL4} {d : ℕ} (hg : g ∈ stabilizer (flagSpace 4 (ZMod 2) d))
    {i j : Fin 4} (hj : (j : ℕ) < d) (hi : d ≤ (i : ℕ)) : (g : M4) i j = 0 := by
  have h1 : (g : M4) *ᵥ Pi.single j 1 ∈ flagSpace 4 (ZMod 2) d := by
    rw [← mem_stabilizer.1 hg]
    exact ⟨Pi.single j 1, Submodule.subset_span ⟨j, hj, rfl⟩, rfl⟩
  have h2 := mem_flagSpace.1 h1 i hi
  simpa [mulVec_single_one] using h2

theorem entries_of_mem_Q13 {g : SL4} (hg : g ∈ Q13) :
    (g : M4) 1 0 = 0 ∧ (g : M4) 2 0 = 0 ∧ (g : M4) 3 0 = 0 ∧ (g : M4) 3 1 = 0 ∧
      (g : M4) 3 2 = 0 := by
  have h1 := mem_flagStabilizer.1 hg 1 ⟨le_rfl, by norm_num, by norm_num⟩
  have h3 := mem_flagStabilizer.1 hg 3 ⟨by norm_num, by norm_num, by norm_num⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact entry_eq_zero h1 (i := 1) (j := 0)
      (by norm_num) (by norm_num)
  · exact entry_eq_zero h1 (i := 2) (j := 0)
      (by norm_num) (by norm_num)
  · exact entry_eq_zero h1 (i := 3) (j := 0)
      (by norm_num) (by norm_num)
  · exact entry_eq_zero h3 (i := 3) (j := 1)
      (by norm_num) (by norm_num)
  · exact entry_eq_zero h3 (i := 3) (j := 2)
      (by norm_num) (by norm_num)

theorem mem_U_of_Q13 {g : SL4} (hg : g ∈ Q13) (h21 : (g : M4) 2 1 = 0) :
    g ∈ unitriangular 4 (ZMod 2) := by
  rw [← flag_inf_Q13]
  refine ⟨(mem_flag_iff g).2 ?_, hg⟩
  obtain ⟨-, a, b, c, -⟩ := entries_of_mem_Q13 hg
  exact ⟨a, b, h21, c⟩

theorem q1_mem : q1 ∈ Q13 := by
  refine CFSG.QuasithinUnique.Vol2Native.A312L.mem_flagStabilizer_of_entries ?_
  intro k l c hc hl hk
  obtain ⟨hc1, hc4, hc2⟩ := hc
  fin_cases k <;> fin_cases l <;> simp at hl hk ⊢ <;> first | rfl | omega

theorem q2_mem : q2 ∈ Q13 := by
  refine CFSG.QuasithinUnique.Vol2Native.A312L.mem_flagStabilizer_of_entries ?_
  intro k l c hc hl hk
  obtain ⟨hc1, hc4, hc2⟩ := hc
  fin_cases k <;> fin_cases l <;> simp at hl hk ⊢ <;> first | rfl | omega

theorem tri {g : SL4} (hg : g ∈ Q13) :
    g ∈ unitriangular 4 (ZMod 2) ∨ q1⁻¹ * g ∈ unitriangular 4 (ZMod 2) ∨
      q2⁻¹ * g ∈ unitriangular 4 (ZMod 2) := by
  have h1 : q1⁻¹ * g ∈ Q13 := Q13.mul_mem (Q13.inv_mem q1_mem) hg
  have h2 : q2⁻¹ * g ∈ Q13 := Q13.mul_mem (Q13.inv_mem q2_mem) hg
  have hq1 : q1⁻¹ = q1 := inv_eq_of_mul_eq_one_right q1_mul_self
  have hq2 : q2⁻¹ = q2 := inv_eq_of_mul_eq_one_right q2_mul_self
  have e1 : ((q1⁻¹ * g : SL4) : M4) 2 1 = (g : M4) 1 1 := by
    rw [hq1, Matrix.SpecialLinearGroup.coe_mul]
    simp [q1, L4Ind.coe_mkSL, Matrix.mul_apply, Fin.sum_univ_four]
  have e2 : ((q2⁻¹ * g : SL4) : M4) 2 1 = (g : M4) 1 1 + (g : M4) 2 1 := by
    rw [hq2, Matrix.SpecialLinearGroup.coe_mul]
    simp [q2, L4Ind.coe_mkSL, Matrix.mul_apply, Fin.sum_univ_four]
  have key : ∀ x y : ZMod 2, y = 0 ∨ x = 0 ∨ x + y = 0 := by decide
  rcases key ((g : M4) 1 1) ((g : M4) 2 1) with h | h | h
  · exact Or.inl (mem_U_of_Q13 hg h)
  · exact Or.inr (Or.inl (mem_U_of_Q13 h1 (e1.trans h)))
  · exact Or.inr (Or.inr (mem_U_of_Q13 h2 (e2.trans h)))


end CFSG.Quasithin.H13.A6.L4Tw
