module

public import CFSG.CGT.PushingUpLit.SolKNA.SzWeightDef

public section

open scoped CharTwo

namespace CFSG.RepresentationTheory.SzMartineau

open CFSG.Open CFSG.RankThree.GF2n.SzExplicit CFSG.CGT.PushingUpLit.SolKNA Matrix

variable (a : ℕ)

private lemma add_pow_one_add_theta {n : ℕ} (x y : F n) :
    (x + y) ^ (1 + 2 ^ (n + 1)) =
      x ^ (1 + 2 ^ (n + 1)) + x ^ 2 ^ (n + 1) * y + x * y ^ 2 ^ (n + 1) +
        y ^ (1 + 2 ^ (n + 1)) := by
  rw [pow_add, pow_one, add_pow_char_pow (p := 2) (n := n + 1)]
  rw [pow_add x 1 (2 ^ (n + 1)), pow_one, pow_add y 1 (2 ^ (n + 1)), pow_one]
  ring

private lemma add_pow_two_add_theta {n : ℕ} (x y : F n) :
    (x + y) ^ (2 + 2 ^ (n + 1)) =
      x ^ (2 + 2 ^ (n + 1)) + x ^ 2 * y ^ 2 ^ (n + 1) + y ^ 2 * x ^ 2 ^ (n + 1) +
        y ^ (2 + 2 ^ (n + 1)) := by
  rw [pow_add, CharTwo.add_sq, add_pow_char_pow (p := 2) (n := n + 1)]
  rw [pow_add x 2 (2 ^ (n + 1)), pow_add y 2 (2 ^ (n + 1))]
  ring

private lemma pow_theta_mul_theta {n : ℕ} (u : F n) :
    u ^ (2 ^ (n + 1) * 2 ^ (n + 1)) = u ^ 2 := by
  let _ : Fintype (F n) := Fintype.ofFinite _
  have hq : u ^ (2 ^ (2 * n + 1)) = u := by
    have h := FiniteField.pow_card u
    rwa [← Nat.card_eq_fintype_card, GaloisField.card 2 (2 * n + 1) (by omega)] at h
  have e : 2 ^ (n + 1) * 2 ^ (n + 1) = 2 * 2 ^ (2 * n + 1) := by
    rw [← pow_add, mul_comm 2 (2 ^ (2 * n + 1)), ← pow_succ]
    congr 1
    omega
  calc u ^ (2 ^ (n + 1) * 2 ^ (n + 1)) = u ^ (2 * 2 ^ (2 * n + 1)) := by rw [e]
    _ = (u ^ (2 ^ (2 * n + 1))) ^ 2 := by rw [mul_comm 2 (2 ^ (2 * n + 1)), pow_mul]
    _ = u ^ 2 := by rw [hq]

private lemma mul_pow_theta {n : ℕ} (x y : F n) :
    (x * y ^ 2 ^ (n + 1)) ^ 2 ^ (n + 1) = x ^ 2 ^ (n + 1) * y ^ 2 := by
  rw [mul_pow, ← pow_mul, pow_theta_mul_theta]

private lemma pow_succ_theta {n : ℕ} (x : F n) :
    x ^ (2 ^ (n + 1)) = x ^ (2 ^ n) * x ^ (2 ^ n) := by
  rw [show 2 ^ (n + 1) = 2 ^ n + 2 ^ n by rw [pow_succ']; ring, pow_add]

private lemma pow_one_add_theta_eq {n : ℕ} (x : F n) :
    x ^ (1 + 2 ^ (n + 1)) = x ^ (1 + 2 ^ n) * x ^ (2 ^ n) := by
  rw [show 1 + 2 ^ (n + 1) = (1 + 2 ^ n) + 2 ^ n by rw [pow_succ']; ring, pow_add]

private lemma pow_two_add_theta_eq {n : ℕ} (x : F n) :
    x ^ (2 + 2 ^ (n + 1)) = x ^ (2 + 2 ^ n) * x ^ (2 ^ n) := by
  rw [show 2 + 2 ^ (n + 1) = (2 + 2 ^ n) + 2 ^ n by rw [pow_succ']; ring, pow_add]

private lemma pow_one_add_theta_mul_theta {n : ℕ} (x : F n) :
    x ^ ((1 + 2 ^ (n + 1)) * 2 ^ (n + 1)) = x ^ (2 + 2 ^ (n + 1)) := by
  rw [show (1 + 2 ^ (n + 1)) * 2 ^ (n + 1) =
    2 ^ (n + 1) + 2 ^ (n + 1) * 2 ^ (n + 1) by ring]
  rw [pow_add, pow_theta_mul_theta, ← pow_add]
  congr 1
  ring

theorem rootMat_zero_zero {n : ℕ} : rootMat n 0 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rootMat]

theorem rootMat_mul_rootMat (α β γ δ : F a) :
    rootMat a α β * rootMat a γ δ =
      rootMat a (α + γ) (α * γ ^ 2 ^ (a + 1) + β + δ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rootMat, Matrix.mul_apply, Fin.sum_univ_four]
  · ring
  · ring
  · rw [add_pow_two_add_theta α γ]
    rw [add_pow_char_pow (p := 2) (n := a + 1)]
    rw [add_pow_char_pow (p := 2) (n := a + 1)]
    rw [mul_pow_theta α γ]
    ring_nf
    simp only [CharTwo.two_eq_zero, mul_zero]
    ring
  · rw [add_pow_char_pow (p := 2) (n := a + 1)]
    ring
  · rw [add_pow_one_add_theta α γ]
    ring_nf
    simp only [CharTwo.two_eq_zero, mul_zero]
    ring
  · ring

theorem torusMat_mul_rootMat (x : (F a)ˣ) (α β : F a) :
    torusMat a x * rootMat a α β =
      rootMat a (x * α) ((x : F a) ^ (1 + 2 ^ (a + 1)) * β) * torusMat a x := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [torusMat, rootMat, Matrix.mul_apply, Fin.sum_univ_four]
  · rw [pow_add, pow_one]
    ring
  · rw [pow_one_add_theta_eq, pow_add]
    field_simp
  · rw [mul_pow, mul_pow, ← pow_mul, pow_one_add_theta_mul_theta]
    simp only [pow_two_add_theta_eq, pow_one_add_theta_eq]
    field_simp
    ring
  · rw [mul_pow, pow_succ_theta]
    field_simp
    rw [pow_succ_theta]
    ring
  · rw [mul_pow, pow_one_add_theta_eq]
    field_simp
    ring
  · rw [pow_add, pow_one]
    field_simp

theorem wMat_mul_torusMat (x : (F a)ˣ) : wMat a * torusMat a x = torusMat a x⁻¹ * wMat a := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wMat, torusMat, Matrix.mul_apply, Fin.sum_univ_four]

theorem torusMat_mul_torusMat (x y : (F a)ˣ) :
    torusMat a x * torusMat a y = torusMat a (x * y) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [torusMat, Matrix.mul_apply, Fin.sum_univ_four, mul_pow]
  all_goals ring

theorem torusMat_one : torusMat a 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [torusMat]

theorem rootMat_one_zero_pow_four : rootMat a 1 0 ^ 4 = 1 := by
  have h2 : rootMat a 1 0 * rootMat a 1 0 = rootMat a 0 1 := by
    rw [rootMat_mul_rootMat]
    simp
  have h3 : rootMat a 0 1 * rootMat a 0 1 = rootMat a 0 0 := by
    rw [rootMat_mul_rootMat]
    simp
  calc rootMat a 1 0 ^ 4
      = (rootMat a 1 0 * rootMat a 1 0) * (rootMat a 1 0 * rootMat a 1 0) := by
        noncomm_ring
    _ = rootMat a 0 1 * rootMat a 0 1 := by rw [h2]
    _ = rootMat a 0 0 := h3
    _ = 1 := rootMat_zero_zero

theorem wMat_mul_rootMat_one_zero_mul_wMat :
    wMat a * rootMat a 1 0 * wMat a =
      rootMat a 1 0 * wMat a * rootMat a 1 0 ^ 2 := by
  rw [pow_two, rootMat_one_zero]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wMat, Matrix.mul_apply, Fin.sum_univ_four]
  all_goals ring_nf
  all_goals simp

theorem exists_pow_one_add_theta (β : F a) : ∃ y : F a, y ^ (1 + 2 ^ (a + 1)) = β := by
  let _ : Fintype (F a) := Fintype.ofFinite _
  have hθ : 1 ≤ 2 ^ (a + 1) := Nat.one_le_two_pow
  have hq : 1 ≤ 2 ^ (2 * a + 1) := Nat.one_le_two_pow
  have eNat : (2 ^ (a + 1) - 1) * (1 + 2 ^ (a + 1)) =
      2 * (2 ^ (2 * a + 1) - 1) + 1 := by
    zify [hθ, hq]
    have e' : (2 : ℤ) ^ (a + 1) * 2 ^ (a + 1) = 2 * 2 ^ (2 * a + 1) := by
      have e0 : (2 : ℕ) ^ (a + 1) * 2 ^ (a + 1) = 2 * 2 ^ (2 * a + 1) := by
        rw [← pow_add, mul_comm 2 (2 ^ (2 * a + 1)), ← pow_succ]
        congr 1
        omega
      exact_mod_cast e0
    linear_combination (-1 : ℤ) * e'
  refine ⟨β ^ (2 ^ (a + 1) - 1), ?_⟩
  rw [← pow_mul, eNat]
  rcases eq_or_ne β 0 with hβ | hβ
  · subst hβ
    rw [zero_pow (by positivity)]
  · have hcard : Fintype.card (F a) = 2 ^ (2 * a + 1) := by
      rw [← Nat.card_eq_fintype_card]
      exact GaloisField.card 2 (2 * a + 1) (by omega)
    have hpow : β ^ (Fintype.card (F a) - 1) = 1 :=
      FiniteField.pow_card_sub_one_eq_one β hβ
    rw [hcard] at hpow
    rw [pow_add, mul_comm 2 (2 ^ (2 * a + 1) - 1), pow_mul, hpow]
    ring

theorem rootMat_map_pow (c : ℕ) (α β : F a) :
    (rootMat a α β).map (· ^ 2 ^ c) = rootMat a (α ^ 2 ^ c) (β ^ 2 ^ c) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rootMat, Matrix.map_apply]
  · rw [add_pow_char_pow (p := 2) (n := c), add_pow_char_pow (p := 2) (n := c), mul_pow,
      pow_right_comm α (2 + 2 ^ (a + 1)) (2 ^ c), pow_right_comm β (2 ^ (a + 1)) (2 ^ c)]
  · rw [pow_right_comm α (2 ^ (a + 1)) (2 ^ c)]
  · rw [add_pow_char_pow (p := 2) (n := c), pow_right_comm α (1 + 2 ^ (a + 1)) (2 ^ c)]

theorem torusMat_map_pow (c : ℕ) (x : (F a)ˣ) :
    (torusMat a x).map (· ^ 2 ^ c) = torusMat a (x ^ 2 ^ c) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [torusMat, Matrix.map_apply]
  · rw [pow_right_comm (x : F a) (1 + 2 ^ a) (2 ^ c)]
  · rw [pow_right_comm (x : F a) (2 ^ a) (2 ^ c)]
  · rw [pow_right_comm (x : F a) (2 ^ a) (2 ^ c)]
  · rw [pow_right_comm (x : F a) (1 + 2 ^ a) (2 ^ c)]

theorem wMat_map_pow (c : ℕ) : (wMat a).map (· ^ 2 ^ c) = wMat a := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wMat]

private lemma coe_rootSz (α β : F a) :
    (((rootSz a α β : ↥(Sz a)) : GL (Fin 4) (F a)) : Matrix (Fin 4) (Fin 4) (F a)) =
      rootMat a α β := rfl

private lemma coe_torusSz (x : (F a)ˣ) :
    (((torusSz a x : ↥(Sz a)) : GL (Fin 4) (F a)) : Matrix (Fin 4) (Fin 4) (F a)) =
      torusMat a x := rfl

private lemma coe_w :
    (((w a : ↥(Sz a)) : GL (Fin 4) (F a)) : Matrix (Fin 4) (Fin 4) (F a)) = wMat a := rfl

theorem rootSz_mul_rootSz (α β γ δ : F a) :
    rootSz a α β * rootSz a γ δ = rootSz a (α + γ) (α * γ ^ 2 ^ (a + 1) + β + δ) := by
  refine Subtype.ext (Units.ext ?_)
  simpa [coe_rootSz] using rootMat_mul_rootMat a α β γ δ

theorem torusSz_mul_rootSz (x : (F a)ˣ) (α β : F a) :
    torusSz a x * rootSz a α β =
      rootSz a (x * α) ((x : F a) ^ (1 + 2 ^ (a + 1)) * β) * torusSz a x := by
  refine Subtype.ext (Units.ext ?_)
  simpa [coe_rootSz, coe_torusSz] using torusMat_mul_rootMat a x α β

theorem w_mul_torusSz (x : (F a)ˣ) : w a * torusSz a x = torusSz a x⁻¹ * w a := by
  refine Subtype.ext (Units.ext ?_)
  simpa [coe_torusSz, coe_w] using wMat_mul_torusMat a x

theorem torusSz_mul_torusSz (x y : (F a)ˣ) :
    torusSz a x * torusSz a y = torusSz a (x * y) := by
  refine Subtype.ext (Units.ext ?_)
  simpa [coe_torusSz] using torusMat_mul_torusMat a x y

theorem torusSz_one : torusSz a 1 = 1 := by
  refine Subtype.ext (Units.ext ?_)
  simpa [coe_torusSz] using torusMat_one a

theorem rootSz_one_zero_pow_four : rootSz a 1 0 ^ 4 = 1 := by
  refine Subtype.ext (Units.ext ?_)
  simpa [coe_rootSz] using rootMat_one_zero_pow_four a

theorem w_mul_rootSz_one_zero_mul_w :
    w a * rootSz a 1 0 * w a = rootSz a 1 0 * w a * rootSz a 1 0 ^ 2 := by
  refine Subtype.ext (Units.ext ?_)
  simpa [coe_rootSz, coe_w] using wMat_mul_rootMat_one_zero_mul_wMat a

theorem cases_of_mem_szGenerators {g : GL (Fin 4) (F a)}
    (hg : (g : Matrix (Fin 4) (Fin 4) (F a)) ∈ SzGenerators a) (hgSz : g ∈ Sz a) :
    (∃ α β, (⟨g, hgSz⟩ : ↥(Sz a)) = rootSz a α β) ∨
      (∃ x, (⟨g, hgSz⟩ : ↥(Sz a)) = torusSz a x) ∨
      (⟨g, hgSz⟩ : ↥(Sz a)) = w a := by
  simp only [SzGenerators, Set.mem_setOf_eq] at hg
  rcases hg with ⟨α, β, h⟩ | ⟨x, h⟩ | h
  · exact Or.inl ⟨α, β, Subtype.ext (Units.ext h)⟩
  · exact Or.inr (Or.inl ⟨x, Subtype.ext (Units.ext h)⟩)
  · exact Or.inr (Or.inr (Subtype.ext (Units.ext h)))

@[expose] noncomputable def natHom : ↥(Sz a) →* Matrix (Fin 4) (Fin 4) (F a) :=
  (Units.coeHom (Matrix (Fin 4) (Fin 4) (F a))).comp (Sz a).subtype

@[expose] noncomputable def twHom (c : ℕ) : ↥(Sz a) →* Matrix (Fin 4) (Fin 4) (F a) :=
  (RingHom.mapMatrix (iterateFrobenius (F a) 2 c)).toMonoidHom.comp (natHom a)

@[simp] theorem natHom_apply (g : ↥(Sz a)) :
    natHom a g = ((g : GL (Fin 4) (F a)) : Matrix (Fin 4) (Fin 4) (F a)) := rfl

@[simp] theorem twHom_apply (c : ℕ) (g : ↥(Sz a)) :
    twHom a c g = (natHom a g).map (· ^ 2 ^ c) := rfl

@[simp] theorem natHom_rootSz (α β : F a) : natHom a (rootSz a α β) = rootMat a α β := rfl

@[simp] theorem natHom_torusSz (x : (F a)ˣ) : natHom a (torusSz a x) = torusMat a x := rfl

@[simp] theorem natHom_w : natHom a (w a) = wMat a := rfl

@[simp] theorem twHom_rootSz (c : ℕ) (α β : F a) :
    twHom a c (rootSz a α β) = rootMat a (α ^ 2 ^ c) (β ^ 2 ^ c) := by
  rw [twHom_apply, natHom_rootSz, rootMat_map_pow]

@[simp] theorem twHom_torusSz (c : ℕ) (x : (F a)ˣ) :
    twHom a c (torusSz a x) = torusMat a (x ^ 2 ^ c) := by
  rw [twHom_apply, natHom_torusSz, torusMat_map_pow]

@[simp] theorem twHom_w (c : ℕ) : twHom a c (w a) = wMat a := by
  rw [twHom_apply, natHom_w, wMat_map_pow]

@[simp] theorem twHom_rootSz_one_zero (c : ℕ) :
    twHom a c (rootSz a 1 0) = rootMat a 1 0 := by
  rw [twHom_rootSz]
  simp

end CFSG.RepresentationTheory.SzMartineau
