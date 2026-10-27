module

public import CFSG.RankThree.PartTwo.Sec18.Item185InnerBase
import CFSG.RankThree.PartTwo.KFacts.KSListsProofCard
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFormFixed
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearInnerFixed
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item185Proof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSp)
open CFSG.RankThree.PartTwo.Sec4.Item434Kit (WreathFacts vecElt wreathW isPGroup_wreathW le_card_wreathW)
open CFSG.RankThree.PartTwo.Sec8.Item812Res12 (sgnV conj_vecElt_of_sgn)
open CFSG.RankThree.PartTwo.Sec4.Item434AltPerm
  (c1 c2 c3 tt wFacts_ten wFacts_eleven factorization_three_pow_mul)

theorem normIrred_alternatingGroup_nine :
    NormIrred (alternatingGroup (Fin 9)) :=
  fun E U hE hU hN =>
    Sec8.kF812E27NormIrred_holds _ (Or.inl ⟨MulEquiv.refl _⟩) E U hE.1 hE.2 hU hN

theorem normIrred_projSp_three_two :
    NormIrred (projSp 3 (GaloisField 2 1)) :=
  fun E U hE hU hN =>
    Sec8.kF812E27NormIrred_holds _ (Or.inr ⟨MulEquiv.refl _⟩) E U hE.1 hE.2 hU hN

private theorem card_wreathW_eq_81 {G : Type} [Group G] [Finite G] {z : Fin 3 → G} {t : G}
    (hW : WreathFacts z t) (hG : (Nat.card G).factorization 3 = 4) :
    Nat.card (wreathW z t) = 81 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hle := CFSG.RankThree.PartTwo.Sec4.Item434AltPerm.card_le_of_isPGroup (isPGroup_wreathW hW)
  rw [hG] at hle
  have := le_card_wreathW hW
  norm_num at hle
  omega

private theorem sylowSignModel_of_wreath {G : Type} [Group G] [Finite G] {z : Fin 3 → G} {t s : G}
    (hW : WreathFacts z t) (hs : ∀ w : Fin 3 → ZMod 3, s * vecElt z w * s⁻¹ = vecElt z (sgnV w))
    (hG : (Nat.card G).factorization 3 = 4) : SylowSignModel G := by
  unfold SylowSignModel
  refine ⟨z, t, s, hW, ?_, card_wreathW_eq_81 hW hG, hs⟩
  rw [hG]
  simpa using card_wreathW_eq_81 hW hG

section AlternatingTenEleven

open Equiv Equiv.Perm

private def zPerm10 : Fin 3 → Perm (Fin 10) := ![c1 10, c2 10, c3 10]

private theorem wreathFacts_perm10 : WreathFacts zPerm10 (tt 10) where
  pow_z := by
    intro i
    fin_cases i <;> decide
  comm_z := by
    intro i j
    fin_cases i <;> fin_cases j <;> decide
  inj := fun v hv => wFacts_ten.inj v hv
  pow_t := wFacts_ten.tt_pow
  conj0 := wFacts_ten.conj1
  conj1 := wFacts_ten.conj2
  conj2 := wFacts_ten.conj3
  t_ne := wFacts_ten.tt_ne

private theorem zPerm10_mem (i : Fin 3) : zPerm10 i ∈ alternatingGroup (Fin 10) := by
  fin_cases i
  · change c1 10 ∈ alternatingGroup (Fin 10)
    rw [mem_alternatingGroup, c1, Perm.sign_mul, sign_swap (show (0 : Fin 10) ≠ 1 by decide),
      sign_swap (show (1 : Fin 10) ≠ 2 by decide)]
    decide
  · change c2 10 ∈ alternatingGroup (Fin 10)
    rw [mem_alternatingGroup, c2, Perm.sign_mul, sign_swap (show (3 : Fin 10) ≠ 4 by decide),
      sign_swap (show (4 : Fin 10) ≠ 5 by decide)]
    decide
  · change c3 10 ∈ alternatingGroup (Fin 10)
    rw [mem_alternatingGroup, c3, Perm.sign_mul, sign_swap (show (6 : Fin 10) ≠ 7 by decide),
      sign_swap (show (7 : Fin 10) ≠ 8 by decide)]
    decide

private theorem tt_ten_mem : tt 10 ∈ alternatingGroup (Fin 10) := by
  rw [mem_alternatingGroup, tt]
  simp only [Perm.sign_mul, sign_swap (show (0 : Fin 10) ≠ 3 by decide),
    sign_swap (show (3 : Fin 10) ≠ 6 by decide), sign_swap (show (1 : Fin 10) ≠ 4 by decide),
    sign_swap (show (4 : Fin 10) ≠ 7 by decide), sign_swap (show (2 : Fin 10) ≠ 5 by decide),
    sign_swap (show (5 : Fin 10) ≠ 8 by decide)]
  decide

private def zA10 : Fin 3 → alternatingGroup (Fin 10) := fun i => ⟨zPerm10 i, zPerm10_mem i⟩

private def tA10 : alternatingGroup (Fin 10) := ⟨tt 10, tt_ten_mem⟩

private theorem wreathFacts_A10 : WreathFacts zA10 tA10 :=
  wreathFacts_perm10.subtype zPerm10_mem tt_ten_mem

private theorem factorization_card_A10 :
    (Nat.card (alternatingGroup (Fin 10))).factorization 3 = 4 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin,
    show Nat.factorial 10 / 2 = 3 ^ 4 * 22400 by decide,
    factorization_three_pow_mul 4 (m := 22400) (by norm_num)]

private def sPerm10 : Perm (Fin 10) := swap 0 1 * swap 3 4

private theorem sPerm10_mem : sPerm10 ∈ alternatingGroup (Fin 10) := by
  rw [mem_alternatingGroup, sPerm10, Perm.sign_mul, sign_swap (show (0 : Fin 10) ≠ 1 by decide),
    sign_swap (show (3 : Fin 10) ≠ 4 by decide)]
  decide

private def sA10 : alternatingGroup (Fin 10) := ⟨sPerm10, sPerm10_mem⟩

private theorem sPerm10_conj : sPerm10 * zPerm10 0 * sPerm10⁻¹ = zPerm10 0 ^ 2 ∧
    sPerm10 * zPerm10 1 * sPerm10⁻¹ = zPerm10 1 ^ 2 ∧
    sPerm10 * zPerm10 2 * sPerm10⁻¹ = zPerm10 2 := by
  decide

private theorem sA10_conj (w : Fin 3 → ZMod 3) :
    sA10 * vecElt zA10 w * sA10⁻¹ = vecElt zA10 (sgnV w) := by
  obtain ⟨h0, h1, h2⟩ := sPerm10_conj
  exact conj_vecElt_of_sgn wreathFacts_A10 (Subtype.ext h0) (Subtype.ext h1) (Subtype.ext h2) w

theorem sylowSignModel_alternatingGroup_ten : SylowSignModel (alternatingGroup (Fin 10)) :=
  sylowSignModel_of_wreath wreathFacts_A10 sA10_conj factorization_card_A10

private def zPerm11 : Fin 3 → Perm (Fin 11) := ![c1 11, c2 11, c3 11]

private theorem wreathFacts_perm11 : WreathFacts zPerm11 (tt 11) where
  pow_z := by
    intro i
    fin_cases i <;> decide
  comm_z := by
    intro i j
    fin_cases i <;> fin_cases j <;> decide
  inj := fun v hv => wFacts_eleven.inj v hv
  pow_t := wFacts_eleven.tt_pow
  conj0 := wFacts_eleven.conj1
  conj1 := wFacts_eleven.conj2
  conj2 := wFacts_eleven.conj3
  t_ne := wFacts_eleven.tt_ne

private theorem zPerm11_mem (i : Fin 3) : zPerm11 i ∈ alternatingGroup (Fin 11) := by
  fin_cases i
  · change c1 11 ∈ alternatingGroup (Fin 11)
    rw [mem_alternatingGroup, c1, Perm.sign_mul, sign_swap (show (0 : Fin 11) ≠ 1 by decide),
      sign_swap (show (1 : Fin 11) ≠ 2 by decide)]
    decide
  · change c2 11 ∈ alternatingGroup (Fin 11)
    rw [mem_alternatingGroup, c2, Perm.sign_mul, sign_swap (show (3 : Fin 11) ≠ 4 by decide),
      sign_swap (show (4 : Fin 11) ≠ 5 by decide)]
    decide
  · change c3 11 ∈ alternatingGroup (Fin 11)
    rw [mem_alternatingGroup, c3, Perm.sign_mul, sign_swap (show (6 : Fin 11) ≠ 7 by decide),
      sign_swap (show (7 : Fin 11) ≠ 8 by decide)]
    decide

private theorem tt_eleven_mem : tt 11 ∈ alternatingGroup (Fin 11) := by
  rw [mem_alternatingGroup, tt]
  simp only [Perm.sign_mul, sign_swap (show (0 : Fin 11) ≠ 3 by decide),
    sign_swap (show (3 : Fin 11) ≠ 6 by decide), sign_swap (show (1 : Fin 11) ≠ 4 by decide),
    sign_swap (show (4 : Fin 11) ≠ 7 by decide), sign_swap (show (2 : Fin 11) ≠ 5 by decide),
    sign_swap (show (5 : Fin 11) ≠ 8 by decide)]
  decide

private def zA11 : Fin 3 → alternatingGroup (Fin 11) := fun i => ⟨zPerm11 i, zPerm11_mem i⟩

private def tA11 : alternatingGroup (Fin 11) := ⟨tt 11, tt_eleven_mem⟩

private theorem wreathFacts_A11 : WreathFacts zA11 tA11 :=
  wreathFacts_perm11.subtype zPerm11_mem tt_eleven_mem

private theorem factorization_card_A11 :
    (Nat.card (alternatingGroup (Fin 11))).factorization 3 = 4 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin,
    show Nat.factorial 11 / 2 = 3 ^ 4 * 246400 by decide,
    factorization_three_pow_mul 4 (m := 246400) (by norm_num)]

private def sPerm11 : Perm (Fin 11) := swap 0 1 * swap 3 4

private theorem sPerm11_mem : sPerm11 ∈ alternatingGroup (Fin 11) := by
  rw [mem_alternatingGroup, sPerm11, Perm.sign_mul, sign_swap (show (0 : Fin 11) ≠ 1 by decide),
    sign_swap (show (3 : Fin 11) ≠ 4 by decide)]
  decide

private def sA11 : alternatingGroup (Fin 11) := ⟨sPerm11, sPerm11_mem⟩

private theorem sPerm11_conj : sPerm11 * zPerm11 0 * sPerm11⁻¹ = zPerm11 0 ^ 2 ∧
    sPerm11 * zPerm11 1 * sPerm11⁻¹ = zPerm11 1 ^ 2 ∧
    sPerm11 * zPerm11 2 * sPerm11⁻¹ = zPerm11 2 := by
  decide

private theorem sA11_conj (w : Fin 3 → ZMod 3) :
    sA11 * vecElt zA11 w * sA11⁻¹ = vecElt zA11 (sgnV w) := by
  obtain ⟨h0, h1, h2⟩ := sPerm11_conj
  exact conj_vecElt_of_sgn wreathFacts_A11 (Subtype.ext h0) (Subtype.ext h1) (Subtype.ext h2) w

theorem sylowSignModel_alternatingGroup_eleven : SylowSignModel (alternatingGroup (Fin 11)) :=
  sylowSignModel_of_wreath wreathFacts_A11 sA11_conj factorization_card_A11

end AlternatingTenEleven

section L44Monomial

variable {K : Type} [Field K]

private def l4b : Fin 3 → Fin 4 → ℕ := ![![2, 1, 1, 2], ![1, 2, 1, 2], ![1, 1, 2, 2]]

private theorem l4b_sum : ∀ i : Fin 3, ∑ j, l4b i j = 6 := by
  decide

private def l4τ : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 0 2

private def l4σ : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 2 3

private theorem l4τ_b0 : ∀ i : Fin 4, l4b 0 (l4τ i) % 3 = l4b 1 i % 3 := by
  decide

private theorem l4τ_b1 : ∀ i : Fin 4, l4b 1 (l4τ i) % 3 = l4b 2 i % 3 := by
  decide

private theorem l4τ_b2 : ∀ i : Fin 4, l4b 2 (l4τ i) % 3 = l4b 0 i % 3 := by
  decide

private theorem l4σ_b0 : ∀ i : Fin 4, l4b 0 (l4σ i) % 3 = (fun j => 2 * l4b 0 j) i % 3 := by
  decide

private theorem l4σ_b1 : ∀ i : Fin 4, l4b 1 (l4σ i) % 3 = (fun j => 2 * l4b 1 j) i % 3 := by
  decide

private theorem l4σ_b2 : ∀ i : Fin 4, l4b 2 (l4σ i) % 3 = l4b 2 i % 3 := by
  decide

private theorem l4τ_pow_three : l4τ ^ 3 = 1 := by
  decide

private theorem l4τ_one_zero : l4τ 1 = 0 := by
  decide

private theorem l4τ_sign : Equiv.Perm.sign l4τ = 1 := by
  rw [l4τ, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (show (0 : Fin 4) ≠ 1 by decide),
    Equiv.Perm.sign_swap (show (0 : Fin 4) ≠ 2 by decide)]
  decide

private theorem l4σ_sign : Equiv.Perm.sign l4σ = 1 := by
  rw [l4σ, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (show (0 : Fin 4) ≠ 1 by decide),
    Equiv.Perm.sign_swap (show (2 : Fin 4) ≠ 3 by decide)]
  decide

private def l4D (ω : K) (e : Fin 4 → ℕ) : Matrix (Fin 4) (Fin 4) K :=
  Matrix.diagonal fun i => ω ^ e i

private theorem l4_pow_mod {ω : K} (hω : ω ^ 3 = 1) (n : ℕ) : ω ^ n = ω ^ (n % 3) := by
  have h : ω ^ n = ω ^ (n % 3) * (ω ^ 3) ^ (n / 3) := by
    rw [← pow_mul, ← pow_add, Nat.mod_add_div]
  rw [h, hω, one_pow, mul_one]

private theorem l4_mod_of_pow_eq {ω : K} (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1) {m n : ℕ}
    (h : ω ^ m = ω ^ n) : m % 3 = n % 3 := by
  have hx : IsOfFinOrder ω := isOfFinOrder_iff_pow_eq_one.2 ⟨3, by norm_num, hω⟩
  have h3 : orderOf ω = 3 := orderOf_eq_prime hω hω1
  rw [hx.pow_inj_mod, h3] at h
  exact h

private theorem l4D_congr {ω : K} (hω : ω ^ 3 = 1) {e f : Fin 4 → ℕ}
    (h : ∀ i, e i % 3 = f i % 3) : l4D ω e = l4D ω f := by
  show Matrix.diagonal (fun i => ω ^ e i) = Matrix.diagonal (fun i => ω ^ f i)
  congr 1
  funext i
  show ω ^ e i = ω ^ f i
  rw [l4_pow_mod hω (e i), l4_pow_mod hω (f i), h i]

private theorem l4D_mul (ω : K) (e f : Fin 4 → ℕ) : l4D ω e * l4D ω f = l4D ω (e + f) := by
  show Matrix.diagonal (fun i => ω ^ e i) * Matrix.diagonal (fun i => ω ^ f i) =
    Matrix.diagonal (fun i => ω ^ (e + f) i)
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  show ω ^ e i * ω ^ f i = ω ^ (e i + f i)
  rw [pow_add]

private theorem l4D_pow (ω : K) (e : Fin 4 → ℕ) (k : ℕ) :
    l4D ω e ^ k = l4D ω (fun i => k * e i) := by
  show Matrix.diagonal (fun i => ω ^ e i) ^ k = Matrix.diagonal (fun i => ω ^ (k * e i))
  rw [Matrix.diagonal_pow]
  congr 1
  funext i
  show (ω ^ e i) ^ k = ω ^ (k * e i)
  rw [← pow_mul, mul_comm]

private theorem l4D_three {ω : K} (hω : ω ^ 3 = 1) (e : Fin 4 → ℕ) :
    l4D ω (fun i => 3 * e i) = 1 := by
  show Matrix.diagonal (fun i => ω ^ (3 * e i)) = 1
  have h : (fun i => ω ^ (3 * e i)) = fun _ => (1 : K) := by
    funext i
    show ω ^ (3 * e i) = 1
    rw [pow_mul, hω, one_pow]
  rw [h]
  exact Matrix.diagonal_one

private theorem l4D_det (ω : K) (e : Fin 4 → ℕ) : (l4D ω e).det = ω ^ (∑ i, e i) := by
  show (Matrix.diagonal fun i => ω ^ e i).det = _
  rw [Matrix.det_diagonal, Finset.prod_pow_eq_pow_sum]

private theorem l4_add_two (e : Fin 4 → ℕ) : e + (fun i => 2 * e i) = fun i => 3 * e i := by
  funext i
  simp only [Pi.add_apply]
  omega

private theorem l4_two_add (e : Fin 4 → ℕ) : (fun i => 2 * e i) + e = fun i => 3 * e i := by
  funext i
  simp only [Pi.add_apply]
  omega

private def l4gD {ω : K} (hω : ω ^ 3 = 1) (e : Fin 4 → ℕ) :
    Matrix.GeneralLinearGroup (Fin 4) K :=
  ⟨l4D ω e, l4D ω (fun i => 2 * e i), by
    rw [l4D_mul, l4_add_two]
    exact l4D_three hω e, by
    rw [l4D_mul, l4_two_add]
    exact l4D_three hω e⟩

private theorem l4gD_val {ω : K} (hω : ω ^ 3 = 1) (e : Fin 4 → ℕ) :
    ((l4gD hω e : Matrix.GeneralLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = l4D ω e :=
  rfl

private theorem l4gD_mul {ω : K} (hω : ω ^ 3 = 1) (e f : Fin 4 → ℕ) :
    l4gD hω e * l4gD hω f = l4gD hω (e + f) :=
  Units.ext (by rw [Units.val_mul, l4gD_val, l4gD_val, l4gD_val, l4D_mul])

private theorem l4gD_pow {ω : K} (hω : ω ^ 3 = 1) (e : Fin 4 → ℕ) (k : ℕ) :
    l4gD hω e ^ k = l4gD hω (fun i => k * e i) :=
  Units.ext (by rw [Units.val_pow_eq_pow_val, l4gD_val, l4gD_val, l4D_pow])

private theorem l4gD_three {ω : K} (hω : ω ^ 3 = 1) (e : Fin 4 → ℕ) :
    l4gD hω (fun i => 3 * e i) = 1 :=
  Units.ext (by rw [l4gD_val, Units.val_one, l4D_three hω e])

private theorem l4gD_congr {ω : K} (hω : ω ^ 3 = 1) {e f : Fin 4 → ℕ}
    (h : ∀ i, e i % 3 = f i % 3) : l4gD hω e = l4gD hω f :=
  Units.ext (by rw [l4gD_val, l4gD_val]; exact l4D_congr hω h)

private theorem l4gD_det {ω : K} (hω : ω ^ 3 = 1) {e : Fin 4 → ℕ} (he : ∑ i, e i = 6) :
    Matrix.GeneralLinearGroup.det (l4gD hω e) = 1 := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, l4gD_val, l4D_det, he, Units.val_one,
    show (6 : ℕ) = 3 * 2 from rfl, pow_mul, hω, one_pow]

private theorem l4_perm_mul_inv (σ : Equiv.Perm (Fin 4)) :
    σ.permMatrix K * (σ⁻¹).permMatrix K = 1 := by
  rw [← Matrix.permMatrix_mul, inv_mul_cancel, Matrix.permMatrix_one]

private theorem l4_inv_mul_perm (σ : Equiv.Perm (Fin 4)) :
    (σ⁻¹).permMatrix K * σ.permMatrix K = 1 := by
  rw [← Matrix.permMatrix_mul, mul_inv_cancel, Matrix.permMatrix_one]

private def l4gP (σ : Equiv.Perm (Fin 4)) : Matrix.GeneralLinearGroup (Fin 4) K :=
  ⟨σ.permMatrix K, (σ⁻¹).permMatrix K, l4_perm_mul_inv σ, l4_inv_mul_perm σ⟩

private theorem l4gP_val (σ : Equiv.Perm (Fin 4)) :
    ((l4gP σ : Matrix.GeneralLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      σ.permMatrix K :=
  rfl

private theorem l4gP_one : l4gP (K := K) 1 = 1 :=
  Units.ext (by rw [l4gP_val, Units.val_one, Matrix.permMatrix_one])

private theorem l4_permMatrix_pow (σ : Equiv.Perm (Fin 4)) (n : ℕ) :
    (σ.permMatrix K) ^ n = (σ ^ n).permMatrix K := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ (σ.permMatrix K) n, ih, pow_succ' σ n, Matrix.permMatrix_mul]

private theorem l4gP_pow (σ : Equiv.Perm (Fin 4)) (n : ℕ) :
    l4gP (K := K) σ ^ n = l4gP (σ ^ n) :=
  Units.ext (by rw [Units.val_pow_eq_pow_val, l4gP_val, l4gP_val, l4_permMatrix_pow])

private theorem l4_permMatrix_apply (σ : Equiv.Perm (Fin 4)) (i j : Fin 4) :
    σ.permMatrix K i j = if σ i = j then 1 else 0 := by
  rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
  by_cases h : σ i = j
  · subst h
    simp
  · have h' : ¬ j = σ i := fun e => h e.symm
    simp [h, h']

private theorem l4_permMatrix_mul_D {ω : K} (σ : Equiv.Perm (Fin 4)) (e : Fin 4 → ℕ) :
    σ.permMatrix K * l4D ω e = l4D ω (fun i => e (σ i)) * σ.permMatrix K := by
  ext i j
  simp only [l4D, Matrix.mul_diagonal, Matrix.diagonal_mul, l4_permMatrix_apply]
  by_cases h : σ i = j
  · subst h
    simp
  · simp [h]

private theorem l4gP_mul_gD {ω : K} (hω : ω ^ 3 = 1) (σ : Equiv.Perm (Fin 4)) (e : Fin 4 → ℕ) :
    l4gP (K := K) σ * l4gD hω e = l4gD hω (fun i => e (σ i)) * l4gP σ := by
  apply Units.ext
  simp only [Units.val_mul, l4gP_val, l4gD_val]
  exact l4_permMatrix_mul_D σ e

private theorem l4_conj_of_mul {G : Type*} [Group G] {a b c : G} (h : a * b = c * a) :
    a * b * a⁻¹ = c := by
  rw [mul_inv_eq_iff_eq_mul]
  exact h

private theorem l4gP_conj {ω : K} (hω : ω ^ 3 = 1) (σ : Equiv.Perm (Fin 4)) {e f : Fin 4 → ℕ}
    (h : ∀ i, e (σ i) % 3 = f i % 3) :
    l4gP (K := K) σ * l4gD hω e * (l4gP σ)⁻¹ = l4gD hω f := by
  apply l4_conj_of_mul
  rw [l4gP_mul_gD, l4gD_congr hω (e := fun i => e (σ i)) h]

private theorem mk_conj {g h : Matrix.GeneralLinearGroup (Fin 4) K} :
    Matrix.ProjGenLinGroup.mk g * Matrix.ProjGenLinGroup.mk h * (Matrix.ProjGenLinGroup.mk g)⁻¹ =
      Matrix.ProjGenLinGroup.mk (g * h * g⁻¹) := by
  rw [map_mul, map_mul, map_inv]

private theorem l4_conj_mk {ω : K} (hω : ω ^ 3 = 1) (σ : Equiv.Perm (Fin 4)) {e f : Fin 4 → ℕ}
    (h : ∀ i, e (σ i) % 3 = f i % 3) :
    Matrix.ProjGenLinGroup.mk (l4gP (K := K) σ) * Matrix.ProjGenLinGroup.mk (l4gD hω e) *
      (Matrix.ProjGenLinGroup.mk (l4gP σ))⁻¹ = Matrix.ProjGenLinGroup.mk (l4gD hω f) := by
  rw [mk_conj, l4gP_conj hω σ h]

private theorem mem_projSL_of_det {g : Matrix.GeneralLinearGroup (Fin 4) K}
    (hg : Matrix.GeneralLinearGroup.det g = 1) :
    Matrix.ProjGenLinGroup.mk g ∈ projSL 4 K :=
  Subgroup.mem_map_of_mem _ (MonoidHom.mem_ker.2 hg)

private theorem l4gP_det {σ : Equiv.Perm (Fin 4)} (hσ : Equiv.Perm.sign σ = 1) :
    Matrix.GeneralLinearGroup.det (l4gP (K := K) σ) = 1 := by
  apply Units.ext
  simp [Matrix.GeneralLinearGroup.val_det_apply, l4gP_val, Matrix.det_permutation, hσ]

private def l4z {ω : K} (hω : ω ^ 3 = 1) (i : Fin 3) : projSL 4 K :=
  ⟨Matrix.ProjGenLinGroup.mk (l4gD hω (l4b i)), mem_projSL_of_det (l4gD_det hω (l4b_sum i))⟩

private def l4t : projSL 4 K :=
  ⟨Matrix.ProjGenLinGroup.mk (l4gP l4τ), mem_projSL_of_det (l4gP_det l4τ_sign)⟩

private def l4s : projSL 4 K :=
  ⟨Matrix.ProjGenLinGroup.mk (l4gP l4σ), mem_projSL_of_det (l4gP_det l4σ_sign)⟩

private theorem l4_coe_pow {ω : K} (hω : ω ^ 3 = 1) (i : Fin 3) (k : ℕ) :
    ((l4z hω i ^ k : projSL 4 K) : Matrix.ProjGenLinGroup (Fin 4) K) =
      Matrix.ProjGenLinGroup.mk (l4gD hω (fun j => k * l4b i j)) := by
  rw [Subgroup.coe_pow]
  show (Matrix.ProjGenLinGroup.mk (l4gD hω (l4b i))) ^ k = _
  rw [← map_pow, l4gD_pow]

private def l4E (v : Fin 3 → ZMod 3) : Fin 4 → ℕ :=
  fun j => (v 0).val * l4b 0 j + (v 1).val * l4b 1 j + (v 2).val * l4b 2 j

private theorem l4_coe_vecElt {ω : K} (hω : ω ^ 3 = 1) (v : Fin 3 → ZMod 3) :
    ((vecElt (l4z hω) v : projSL 4 K) : Matrix.ProjGenLinGroup (Fin 4) K) =
      Matrix.ProjGenLinGroup.mk (l4gD hω (l4E v)) := by
  unfold vecElt
  rw [Subgroup.coe_mul, Subgroup.coe_mul, l4_coe_pow, l4_coe_pow, l4_coe_pow, ← map_mul,
    ← map_mul, l4gD_mul, l4gD_mul]
  rfl

private theorem l4_fin_exp : ∀ v : Fin 3 → ZMod 3,
    (∀ i : Fin 4, l4E v i % 3 = l4E v 0 % 3) → v = 0 := by
  decide

private theorem l4_inj {ω : K} (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1) (v : Fin 3 → ZMod 3)
    (h : vecElt (l4z hω) v = 1) : v = 0 := by
  have h1 : Matrix.ProjGenLinGroup.mk (l4gD hω (l4E v)) = 1 := by
    have := congrArg Subtype.val h
    rw [l4_coe_vecElt] at this
    exact this
  obtain ⟨u, hu⟩ :=
    Matrix.ProjGenLinGroup.mk_eq_mk_iff.1 (h1.trans Matrix.ProjGenLinGroup.mk_one.symm)
  have hm : l4D ω (l4E v) * Matrix.scalar (Fin 4) (u : K) = 1 := by
    have := congrArg (fun g : Matrix.GeneralLinearGroup (Fin 4) K =>
      (g : Matrix (Fin 4) (Fin 4) K)) hu
    simpa [l4gD_val, Matrix.GeneralLinearGroup.coe_scalar] using this
  apply l4_fin_exp
  intro i
  apply l4_mod_of_pow_eq hω hω1
  have hi := congrFun (congrFun hm i) i
  have hi0 := congrFun (congrFun hm 0) 0
  simp [l4D, Matrix.scalar_apply, Matrix.diagonal_mul_diagonal] at hi hi0
  exact mul_right_cancel₀ (Units.ne_zero u) (hi.trans hi0.symm)

private theorem l4_t_ne {ω : K} (hω : ω ^ 3 = 1) (v : Fin 3 → ZMod 3) :
    vecElt (l4z hω) v ≠ (l4t (K := K)) := by
  intro h
  have h1 : Matrix.ProjGenLinGroup.mk (l4gD hω (l4E v)) =
      Matrix.ProjGenLinGroup.mk (l4gP (K := K) l4τ) := by
    have := congrArg Subtype.val h
    rw [l4_coe_vecElt] at this
    exact this
  obtain ⟨u, hu⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.1 h1
  have hm : l4D ω (l4E v) * Matrix.scalar (Fin 4) (u : K) = l4τ.permMatrix K := by
    have := congrArg (fun g : Matrix.GeneralLinearGroup (Fin 4) K =>
      (g : Matrix (Fin 4) (Fin 4) K)) hu
    simpa [l4gD_val, l4gP_val, Matrix.GeneralLinearGroup.coe_scalar] using this
  have h10 := congrFun (congrFun hm 1) 0
  simp [l4D, Matrix.scalar_apply, Matrix.diagonal_mul_diagonal, l4_permMatrix_apply,
    l4τ_one_zero] at h10

private theorem l4_pow_three {ω : K} (hω : ω ^ 3 = 1) (i : Fin 3) : l4z hω i ^ 3 = 1 := by
  apply Subtype.ext
  rw [l4_coe_pow, l4gD_three, map_one, Subgroup.coe_one]

private theorem l4_t_pow_three : (l4t (K := K)) ^ 3 = 1 := by
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one]
  show Matrix.ProjGenLinGroup.mk (l4gP (K := K) l4τ) ^ 3 = 1
  rw [← map_pow, l4gP_pow, l4τ_pow_three, l4gP_one, map_one]

private theorem l4_comm {ω : K} (hω : ω ^ 3 = 1) (i j : Fin 3) :
    l4z hω i * l4z hω j = l4z hω j * l4z hω i := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul]
  show Matrix.ProjGenLinGroup.mk (l4gD hω (l4b i)) * Matrix.ProjGenLinGroup.mk (l4gD hω (l4b j)) =
    Matrix.ProjGenLinGroup.mk (l4gD hω (l4b j)) * Matrix.ProjGenLinGroup.mk (l4gD hω (l4b i))
  rw [← map_mul, ← map_mul, l4gD_mul, l4gD_mul, add_comm (l4b i) (l4b j)]

private theorem l4_conj0 {ω : K} (hω : ω ^ 3 = 1) :
    (l4t (K := K)) * l4z hω 0 * (l4t (K := K))⁻¹ = l4z hω 1 := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  exact l4_conj_mk hω l4τ (e := l4b 0) (f := l4b 1) l4τ_b0

private theorem l4_conj1 {ω : K} (hω : ω ^ 3 = 1) :
    (l4t (K := K)) * l4z hω 1 * (l4t (K := K))⁻¹ = l4z hω 2 := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  exact l4_conj_mk hω l4τ (e := l4b 1) (f := l4b 2) l4τ_b1

private theorem l4_conj2 {ω : K} (hω : ω ^ 3 = 1) :
    (l4t (K := K)) * l4z hω 2 * (l4t (K := K))⁻¹ = l4z hω 0 := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  exact l4_conj_mk hω l4τ (e := l4b 2) (f := l4b 0) l4τ_b2

private theorem l4_sign0 {ω : K} (hω : ω ^ 3 = 1) :
    (l4s (K := K)) * l4z hω 0 * (l4s (K := K))⁻¹ = l4z hω 0 ^ 2 := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, l4_coe_pow]
  exact l4_conj_mk hω l4σ (e := l4b 0) (f := fun j => 2 * l4b 0 j) l4σ_b0

private theorem l4_sign1 {ω : K} (hω : ω ^ 3 = 1) :
    (l4s (K := K)) * l4z hω 1 * (l4s (K := K))⁻¹ = l4z hω 1 ^ 2 := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, l4_coe_pow]
  exact l4_conj_mk hω l4σ (e := l4b 1) (f := fun j => 2 * l4b 1 j) l4σ_b1

private theorem l4_sign2 {ω : K} (hω : ω ^ 3 = 1) :
    (l4s (K := K)) * l4z hω 2 * (l4s (K := K))⁻¹ = l4z hω 2 := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  exact l4_conj_mk hω l4σ (e := l4b 2) (f := l4b 2) l4σ_b2

private theorem l4_wreath {ω : K} (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1) :
    WreathFacts (l4z hω) (l4t (K := K)) where
  pow_z := l4_pow_three hω
  comm_z := l4_comm hω
  inj := fun v hv => l4_inj hω hω1 v hv
  pow_t := l4_t_pow_three
  conj0 := l4_conj0 hω
  conj1 := l4_conj1 hω
  conj2 := l4_conj2 hω
  t_ne := fun v => l4_t_ne hω v

private theorem l4_sign {ω : K} (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1) (w : Fin 3 → ZMod 3) :
    (l4s (K := K)) * vecElt (l4z hω) w * (l4s (K := K))⁻¹ = vecElt (l4z hω) (sgnV w) :=
  conj_vecElt_of_sgn (l4_wreath hω hω1) (l4_sign0 hω) (l4_sign1 hω) (l4_sign2 hω) w

private theorem card_gf4 : Nat.card (GaloisField 2 2) = 4 := by
  have h := GaloisField.card 2 2 (by norm_num)
  simpa using h

private theorem l4_exists_omega : ∃ ω : GaloisField 2 2, ω ^ 3 = 1 ∧ ω ≠ 1 := by
  have hdvd : 3 ∣ Nat.card (GaloisField 2 2)ˣ := by
    rw [Nat.card_units, card_gf4]
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := (GaloisField 2 2)ˣ) 3 hdvd
  have hg3 : g ^ 3 = 1 := by
    rw [← hg]
    exact pow_orderOf_eq_one g
  refine ⟨(g : GaloisField 2 2), ?_, ?_⟩
  · rw [← Units.val_pow_eq_pow_val, hg3, Units.val_one]
  · intro h
    have hg1 : g = 1 := Units.ext h
    rw [hg1, orderOf_one] at hg
    norm_num at hg

private theorem l4_card : Nat.card (projSL 4 (GaloisField 2 2)) = 987033600 := by
  have h := CFSG.RankThree.PartTwo.Sec11.KSListsProof.card_projSL_four_mul (GaloisField 2 2)
  rw [card_gf4] at h
  norm_num at h
  exact h

private theorem l4_factorization :
    (Nat.card (projSL 4 (GaloisField 2 2))).factorization 3 = 4 := by
  rw [l4_card, show (987033600 : ℕ) = 3 ^ 4 * 12185600 by norm_num,
    factorization_three_pow_mul 4 (m := 12185600) (by norm_num)]

end L44Monomial

theorem sylowSignModel_projSL_four_four : SylowSignModel (projSL 4 (GaloisField 2 2)) := by
  obtain ⟨ω, hω3, hω1⟩ := l4_exists_omega
  exact sylowSignModel_of_wreath (l4_wreath hω3 hω1) (l4_sign hω3 hω1) l4_factorization

theorem normIrred_projSL_four_four : NormIrred (projSL 4 (GaloisField 2 2)) :=
  NormIrred.of_sylowSignModel sylowSignModel_projSL_four_four

theorem normIrred_alternatingGroup_ten : NormIrred (alternatingGroup (Fin 10)) :=
  NormIrred.of_sylowSignModel sylowSignModel_alternatingGroup_ten

theorem normIrred_alternatingGroup_eleven : NormIrred (alternatingGroup (Fin 11)) :=
  NormIrred.of_sylowSignModel sylowSignModel_alternatingGroup_eleven

end CFSG.RankThree.PartTwo.Sec18.Item185Proof
