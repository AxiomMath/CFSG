module

public import CFSG.Quasithin.Background.HSU3Beta
public import CFSG.ClassicalGroups.UnitaryFlag.OrderSylow
public import CFSG.Quasithin.Background.HTriSp4

public section

namespace CFSG.Quasithin

namespace H

namespace SU3

open CFSG.Open CFSG.Assembly.LowTwoRank Matrix CFSG.LocalAnalysis.ComponentInitial
open scoped Matrix Pointwise

section Witt

variable {K : Type} [Field K] [CharP K 2]

theorem two_eq_zero' : (2 : K) = 0 := CharTwo.two_eq_zero

@[expose] def wittMat : Matrix (Fin 3) (Fin 3) K := !![1, 1, 1; 1, 1, 0; 0, 1, 1]

@[expose] def wittInv : Matrix (Fin 3) (Fin 3) K := !![1, 0, 1; 1, 1, 1; 1, 1, 0]

@[expose] def antiJ : Matrix (Fin 3) (Fin 3) K := !![0, 0, 1; 0, 1, 0; 1, 0, 0]

theorem wittMat_mul_wittInv : (wittMat : Matrix (Fin 3) (Fin 3) K) * wittInv = 1 := by
  have h2 := (two_eq_zero' : (2 : K) = 0)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wittMat, wittInv, Matrix.mul_apply, Fin.sum_univ_three] <;>
    linear_combination h2

theorem wittInv_mul_wittMat : (wittInv : Matrix (Fin 3) (Fin 3) K) * wittMat = 1 :=
  mul_eq_one_comm.mp wittMat_mul_wittInv

theorem wittMat_gram : (wittMat : Matrix (Fin 3) (Fin 3) K)ᵀ * wittMat = antiJ := by
  have h2 := (two_eq_zero' : (2 : K) = 0)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wittMat, antiJ, Matrix.mul_apply, Fin.sum_univ_three] <;>
    linear_combination h2

@[expose] noncomputable def wittGL : GL (Fin 3) K :=
  ⟨wittMat, wittInv, wittMat_mul_wittInv, wittInv_mul_wittMat⟩

theorem coe_wittGL : ((wittGL : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = wittMat := rfl

theorem coe_wittGL_inv : ((wittGL⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = wittInv := rfl

@[expose] noncomputable def ujSub (n : ℕ) (K : Type) [Field K] [CharP K 2] :
    Subgroup (GL (Fin 3) K) :=
  (StatedSU 3 (2 ^ n) K).map (MulAut.conj (wittGL⁻¹ : GL (Fin 3) K)).toMonoidHom ⊓ Tri.uni3 K

theorem ujSub_le_uni3 {n : ℕ} : ujSub n K ≤ Tri.uni3 K := inf_le_right

@[expose] noncomputable def uiSub (n : ℕ) (K : Type) [Field K] [CharP K 2] :
    Subgroup (GL (Fin 3) K) :=
  (ujSub n K).map (MulAut.conj (wittGL : GL (Fin 3) K)).toMonoidHom

theorem uiSub_le {n : ℕ} : uiSub n K ≤ StatedSU 3 (2 ^ n) K := by
  rintro _ ⟨g, ⟨⟨x, hx, rfl⟩, -⟩, rfl⟩
  change wittGL * (wittGL⁻¹ * x * wittGL⁻¹⁻¹) * wittGL⁻¹ ∈ _
  have e : (wittGL : GL (Fin 3) K) * (wittGL⁻¹ * x * wittGL⁻¹⁻¹) * wittGL⁻¹ = x := by group
  rw [e]
  exact hx

theorem card_uiSub {n : ℕ} : Nat.card (uiSub n K) = Nat.card (ujSub n K) :=
  Subgroup.card_map_of_injective (MulAut.conj (wittGL : GL (Fin 3) K)).injective

end Witt

section Unitary

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

@[expose] noncomputable def traceHom (n : ℕ) : K →+ K where
  toFun b := b + bar n b
  map_zero' := by simp
  map_add' a b := by rw [map_add]; ring

theorem traceHom_apply (b : K) : traceHom n b = b + bar n b := rfl

theorem traceHom_eq_zero_iff {b : K} : traceHom n b = 0 ↔ bar n b = b := by
  rw [traceHom_apply, add_eq_zero_iff_eq_neg, CharTwo.neg_eq, eq_comm]

theorem bar_traceHom (hK : Nat.card K = (2 ^ n) ^ 2) (b : K) :
    bar n (traceHom n b) = traceHom n b := by
  rw [traceHom_apply, map_add, bar_bar hK, add_comm]

theorem exists_traceHom_eq (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) {c : K}
    (hc : bar n c = c) : ∃ b, traceHom n b = c := by
  obtain ⟨z, hz⟩ := exists_bar_ne hn hK
  set s := traceHom n z with hs
  have hs0 : s ≠ 0 := fun h => hz (traceHom_eq_zero_iff.mp h)
  have hsb : bar n s = s := bar_traceHom hK z
  refine ⟨c * s⁻¹ * z, ?_⟩
  rw [traceHom_apply, map_mul, map_mul, map_inv₀, hc, hsb, ← mul_add]
  rw [show z + bar n z = s from rfl, mul_assoc, inv_mul_cancel₀ hs0, mul_one]

theorem bar_mul_bar_self (hK : Nat.card K = (2 ^ n) ^ 2) (a : K) :
    bar n (a * bar n a) = a * bar n a := by
  rw [map_mul, bar_bar hK, mul_comm]

theorem card_fixed (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) :
    Nat.card {b : K // bar n b = b} = 2 ^ n := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hle : Nat.card {b : K // bar n b = b} ≤ 2 ^ n := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact card_filter_bar_le hn
  set T := traceHom (K := K) n with hT
  have hker : Nat.card T.ker = Nat.card {b : K // bar n b = b} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun b => by
      rw [AddMonoidHom.mem_ker]
      exact traceHom_eq_zero_iff)
  have hrange : Nat.card T.range ≤ Nat.card {b : K // bar n b = b} := by
    refine Nat.card_le_card_of_injective (fun x => ⟨x.1, ?_⟩) fun x y h => ?_
    · obtain ⟨b, hb⟩ := x.2
      rw [← hb]
      exact bar_traceHom hK b
    · exact Subtype.ext (congrArg (fun z : {b : K // bar n b = b} => z.val) h)
  have hmul : Nat.card T.ker * Nat.card T.range = (2 ^ n) ^ 2 := by
    rw [← hK, ← AddSubgroup.index_ker, AddSubgroup.card_mul_index]
  rw [hker] at hmul
  by_contra hne
  have hlt : Nat.card {b : K // bar n b = b} < 2 ^ n := lt_of_le_of_ne hle hne
  have h1 : Nat.card {b : K // bar n b = b} * Nat.card T.range <
      2 ^ n * 2 ^ n := by
    calc Nat.card {b : K // bar n b = b} * Nat.card T.range
        ≤ Nat.card {b : K // bar n b = b} * Nat.card {b : K // bar n b = b} :=
          Nat.mul_le_mul_left _ hrange
      _ < 2 ^ n * 2 ^ n := Nat.mul_self_lt_mul_self hlt
  rw [hmul, ← sq] at h1
  exact lt_irrefl _ h1

theorem card_params (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) :
    Nat.card {p : K × K // traceHom n p.2 = p.1 * bar n p.1} = (2 ^ n) ^ 3 := by
  classical
  choose b₀ hb₀ using fun a : K => exists_traceHom_eq hn hK (bar_mul_bar_self hK a)
  let e : {p : K × K // traceHom n p.2 = p.1 * bar n p.1} ≃ K × {b : K // bar n b = b} :=
    { toFun := fun p => (p.1.1, ⟨p.1.2 - b₀ p.1.1, by
        rw [← traceHom_eq_zero_iff, map_sub, p.2, hb₀, sub_self]⟩)
      invFun := fun x => ⟨(x.1, x.2.1 + b₀ x.1), by
        rw [map_add, hb₀, traceHom_eq_zero_iff.mpr x.2.2, zero_add]⟩
      left_inv := fun p => by
        apply Subtype.ext
        simp
      right_inv := fun x => by
        ext
        · rfl
        · simp }
  rw [Nat.card_congr e, Nat.card_prod, card_fixed hn hK, hK]
  ring

theorem conjM_of_zero_one {A : Matrix (Fin 3) (Fin 3) K} (h : ∀ i j, A i j = 0 ∨ A i j = 1) :
    conjM n A = A := by
  ext i j
  rcases h i j with h' | h' <;> simp [conjM, h']

theorem conjM_wittMat : conjM n (wittMat : Matrix (Fin 3) (Fin 3) K) = wittMat :=
  conjM_of_zero_one fun i j => by fin_cases i <;> fin_cases j <;> simp [wittMat]

theorem conjM_wittInv : conjM n (wittInv : Matrix (Fin 3) (Fin 3) K) = wittInv :=
  conjM_of_zero_one fun i j => by fin_cases i <;> fin_cases j <;> simp [wittInv]

@[expose] def IsUnitaryJ (n : ℕ) (A : Matrix (Fin 3) (Fin 3) K) : Prop :=
  (conjM n A)ᵀ * antiJ * A = antiJ

theorem isUnitaryM_conj_iff (A : Matrix (Fin 3) (Fin 3) K) :
    IsUnitaryM n (wittMat * A * wittInv) ↔ IsUnitaryJ n A := by
  have hPi : (wittInv : Matrix (Fin 3) (Fin 3) K)ᵀ * wittMatᵀ = 1 := by
    rw [← Matrix.transpose_mul, wittMat_mul_wittInv, Matrix.transpose_one]
  have hiP : (wittMat : Matrix (Fin 3) (Fin 3) K)ᵀ * wittInvᵀ = 1 := by
    rw [← Matrix.transpose_mul, wittInv_mul_wittMat, Matrix.transpose_one]
  have key : (conjM n (wittMat * A * wittInv))ᵀ * (wittMat * A * wittInv) =
      wittInvᵀ * ((conjM n A)ᵀ * antiJ * A) * wittInv := by
    rw [conjM_mul, conjM_mul, conjM_wittMat, conjM_wittInv, Matrix.transpose_mul,
      Matrix.transpose_mul, ← wittMat_gram]
    simp only [Matrix.mul_assoc]
  unfold IsUnitaryM IsUnitaryJ
  rw [key]
  constructor
  · intro h
    calc (conjM n A)ᵀ * antiJ * A
        = (wittMatᵀ * wittInvᵀ) * ((conjM n A)ᵀ * antiJ * A) * (wittInv * wittMat) := by
          rw [hiP, wittInv_mul_wittMat, Matrix.one_mul, Matrix.mul_one]
      _ = wittMatᵀ * (wittInvᵀ * ((conjM n A)ᵀ * antiJ * A) * wittInv) * wittMat := by
          simp only [Matrix.mul_assoc]
      _ = antiJ := by rw [h, Matrix.mul_one, wittMat_gram]
  · intro h
    rw [h, ← wittMat_gram, ← Matrix.mul_assoc _ _ (wittMat : Matrix (Fin 3) (Fin 3) K), hPi,
      Matrix.one_mul, wittMat_mul_wittInv]

theorem mem_ujSub_of {g : GL (Fin 3) K} (hg : g ∈ Tri.uni3 K)
    (hu : IsUnitaryJ n (g : Matrix (Fin 3) (Fin 3) K))
    (hdet : (g : Matrix (Fin 3) (Fin 3) K).det = 1) : g ∈ ujSub n K := by
  refine ⟨⟨wittGL * g * wittGL⁻¹, ?_, ?_⟩, hg⟩
  · refine mem_statedSU ?_ ?_
    · rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, hdet, mul_one,
        ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
    · rw [← conjM_eq_map_pow]
      have h := (isUnitaryM_conj_iff (n := n) (g : Matrix (Fin 3) (Fin 3) K)).mpr hu
      rw [Units.val_mul, Units.val_mul, coe_wittGL, coe_wittGL_inv]
      exact h
  · change wittGL⁻¹ * (wittGL * g * wittGL⁻¹) * wittGL⁻¹⁻¹ = g
    group

@[expose] noncomputable def uJMat (n : ℕ) (a b : K) : Matrix (Fin 3) (Fin 3) K :=
  !![1, a, b; 0, 1, bar n a; 0, 0, 1]

theorem uJMat_lower (a b : K) : ∀ i j : Fin 3, j < i → uJMat n a b i j = 0 := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | simp [uJMat]

theorem uJMat_diag (a b : K) : ∀ i : Fin 3, uJMat n a b i i = 1 := by
  intro i
  fin_cases i <;> simp [uJMat]

theorem det_uJMat (a b : K) : (uJMat n a b).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (fun i j hij => uJMat_lower a b i j hij)]
  simp [uJMat_diag]

@[expose] noncomputable def uJGL (n : ℕ) (a b : K) : GL (Fin 3) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (uJMat n a b) (by rw [det_uJMat]; exact one_ne_zero)

theorem coe_uJGL (a b : K) :
    ((uJGL n a b : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = uJMat n a b := rfl

theorem isUnitaryJ_uJMat (hK : Nat.card K = (2 ^ n) ^ 2) {a b : K}
    (hab : traceHom n b = a * bar n a) : IsUnitaryJ n (uJMat n a b) := by
  have h2 := (two_eq_zero' : (2 : K) = 0)
  have hbb := bar_bar (n := n) hK a
  rw [traceHom_apply] at hab
  unfold IsUnitaryJ
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [conjM, uJMat, antiJ, Matrix.mul_apply, Fin.sum_univ_three, hbb]
  all_goals first
    | linear_combination (bar n a) * h2
    | linear_combination a * h2
    | linear_combination hab + (a * bar n a) * h2

theorem uJGL_mem_ujSub (hK : Nat.card K = (2 ^ n) ^ 2) {a b : K}
    (hab : traceHom n b = a * bar n a) : uJGL n a b ∈ ujSub n K :=
  mem_ujSub_of (Tri.mem_uniGL_of (uJMat_lower a b) (uJMat_diag a b))
    (isUnitaryJ_uJMat hK hab) (det_uJMat a b)

theorem exists_ujSub_zero_one (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) (t : K) :
    ∃ u ∈ ujSub n K, (u : Matrix (Fin 3) (Fin 3) K) 0 1 = t := by
  obtain ⟨b, hb⟩ := exists_traceHom_eq hn hK (bar_mul_bar_self hK t)
  exact ⟨uJGL n t b, uJGL_mem_ujSub hK hb, by simp [coe_uJGL, uJMat]⟩

theorem exists_ujSub_one_two (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) (t : K) :
    ∃ u ∈ ujSub n K, (u : Matrix (Fin 3) (Fin 3) K) 1 2 = t := by
  obtain ⟨b, hb⟩ := exists_traceHom_eq hn hK (bar_mul_bar_self hK (bar n t))
  exact ⟨uJGL n (bar n t) b, uJGL_mem_ujSub hK hb, by simp [coe_uJGL, uJMat, bar_bar hK]⟩

theorem card_ujSub_inf_rootGL (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) :
    2 ^ n ≤ Nat.card ↥(ujSub n K ⊓ Tri.rootGL (0 : Fin 3) 2 (by decide)) := by
  rw [← card_fixed hn hK]
  have heq : ∀ b : K, Tri.trGL (0 : Fin 3) 2 (by decide) b = uJGL n 0 b := fun b => by
    apply Units.ext
    rw [Tri.coe_trGL, coe_uJGL]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [uJMat, transvection]
  refine Nat.card_le_card_of_injective (fun b => ⟨Tri.trGL 0 2 (by decide) b.1,
    Subgroup.mem_inf.mpr ⟨?_, Tri.mem_rootGL.mpr ⟨b.1, rfl⟩⟩⟩) fun b c h => ?_
  · rw [heq]
    exact uJGL_mem_ujSub (n := n) hK (by rw [traceHom_eq_zero_iff.mpr b.2, zero_mul])
  · have := congrArg (fun g : ↥(ujSub n K ⊓ Tri.rootGL (0 : Fin 3) 2 (by decide)) =>
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 2) h
    simp only [Tri.trGL_apply_same] at this
    exact Subtype.ext this

theorem card_ujSub (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) :
    (2 ^ n) ^ 3 ≤ Nat.card (ujSub n K) := by
  rw [← card_params hn hK]
  refine Nat.card_le_card_of_injective (fun p => ⟨uJGL n p.1.1 p.1.2, uJGL_mem_ujSub hK p.2⟩)
    fun p r h => ?_
  have h1 := congrArg (fun g : ↥(ujSub n K) => ((g : GL (Fin 3) K) :
    Matrix (Fin 3) (Fin 3) K) 0 1) h
  have h2 := congrArg (fun g : ↥(ujSub n K) => ((g : GL (Fin 3) K) :
    Matrix (Fin 3) (Fin 3) K) 0 2) h
  simp only [coe_uJGL, uJMat] at h1 h2
  simp at h1 h2
  exact Subtype.ext (Prod.ext h1 h2)

omit [Finite K] [CharP K 2] in
theorem card_statedSU_two (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) :
    2 ^ (Nat.card (StatedSU 3 (2 ^ n) K)).factorization 2 = (2 ^ n) ^ 3 := by
  have h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 n K :=
    ⟨Nat.prime_two, hn, by rw [hK, ← pow_mul, mul_comm]⟩
  obtain ⟨R, hR⟩ := CFSG.ClassicalGroups.UnitaryFlag.exists_isHypTransport (r := 1) (ε := 1) h
  have h1 := (CFSG.ClassicalGroups.UnitaryFlag.card_hypSU h (r := 1) (ε := 1) (by norm_num)).2
  have h2 : Nat.card (CFSG.ClassicalGroups.UnitaryFlag.hypSU h 1 1) =
      Nat.card (StatedSU 3 (2 ^ n) K) :=
    Nat.card_congr (CFSG.ClassicalGroups.UnitaryFlag.hypTransport h hR).toEquiv
  rw [h2] at h1
  rw [h1]

theorem isSylowIn_uiSub (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) :
    IsSylowIn 2 (uiSub n K) (StatedSU 3 (2 ^ n) K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 (uiSub n K) := (Tri.isPGroup_uni3.to_le ujSub_le_uni3).map _
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  refine isSylowIn_of_card_eq uiSub_le ?_
  have hdvd : 2 ^ k ∣ Nat.card (StatedSU 3 (2 ^ n) K) := hk ▸ Subgroup.card_dvd_of_le uiSub_le
  have hle : k ≤ (Nat.card (StatedSU 3 (2 ^ n) K)).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp hdvd
  have hge : (2 ^ n) ^ 3 ≤ 2 ^ k := by
    rw [← hk, card_uiSub]
    exact card_ujSub hn hK
  have h1 := card_statedSU_two (K := K) hn hK
  rw [hk]
  have h2 : 2 ^ k ≤ 2 ^ (Nat.card (StatedSU 3 (2 ^ n) K)).factorization 2 :=
    Nat.pow_le_pow_right (by norm_num) hle
  rw [h1] at h2 ⊢
  exact le_antisymm h2 hge

end Unitary

end SU3

end H

end CFSG.Quasithin
