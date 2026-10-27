module

public import CFSG.LocalAnalysis.StandardType.KGLangTorusMPartDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixLabel
public import CFSG.LocalAnalysis.StandardType.GGLFourFourThreeMarking
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45KGForms
public import CFSG.Assembly.GL83LieDefs
import CFSG.LocalAnalysis.StandardType.KGLangTorusSpanH90
import CFSG.LocalAnalysis.StandardType.KGLangTorusInnerModel
import CFSG.LocalAnalysis.StandardType.KGLangTorusClassicalInner
import CFSG.LocalAnalysis.StandardType.KGLangTorusDatumOfModels
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldSpUSpLabels
import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticBstar
import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic
import CFSG.LocalAnalysis.StandardType.KGLangTorusSpan

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.StandardType CFSG.RankThree.PerfectCover CFSG.HardMathSupport.C14Exc

private noncomputable def kgLangCSpAux_c {m : ℕ} (𝕂 : Type) [Field 𝕂] :
    LargeEvenSpGroup 𝕂 m →* MulAut (LargeEvenProj (LargeEvenSpGroup 𝕂 m)) :=
  (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.conjAut m 𝕂).comp
    (Subgroup.inclusion (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.statedSp_le_gsp
      (r := m) (K := 𝕂)))

private theorem kgLangCSpAux_c_apply {m : ℕ} (𝕂 : Type) [Field 𝕂]
    (A : LargeEvenSpGroup 𝕂 m) :
    kgLangCSpAux_c 𝕂 A =
      MulAut.conj (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj m 𝕂 A) := by
  rw [kgLangCSpAux_c]
  exact CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.conjAut_statedSp A

private theorem kgLangCSpAux_c_injective {m : ℕ} (𝕂 : Type) [Field 𝕂] [CharP 𝕂 2] [NeZero m] :
    Function.Injective (kgLangCSpAux_c (m := m) 𝕂) := by
  intro A B hAB
  have h1 : MulAut.conj (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj m 𝕂 A) =
      MulAut.conj (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj m 𝕂 B) := by
    rw [← kgLangCSpAux_c_apply 𝕂 A, ← kgLangCSpAux_c_apply 𝕂 B, hAB]
  have h2 := mulAut_conj_injective (TableBSymp.center_spProj_eq_bot (K := 𝕂) (m := m)) h1
  exact AutPSp.proj_injective h2

private theorem kgLangCSpAux_c_conjAut {m : ℕ} (𝕂 : Type) [Field 𝕂]
    (A : LargeEvenSpGroup 𝕂 m) :
    kgLangCSpAux_c (m := m) 𝕂 A =
      CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.conjAut m 𝕂
        ⟨A, CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.statedSp_le_gsp A.2⟩ :=
  rfl

private theorem kgLangCSpAux_conj_c {m : ℕ} (𝕂 : Type) [Field 𝕂]
    (σ : 𝕂 ≃+* 𝕂) (A : LargeEvenSpGroup 𝕂 m) :
    (MulAut.conj (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldAut m 𝕂 σ))
        (kgLangCSpAux_c (m := m) 𝕂 A) =
      kgLangCSpAux_c (m := m) 𝕂
        (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldSp m 𝕂 σ A) := by
  rw [kgLangCSpAux_c_conjAut 𝕂 A, kgLangCSpAux_c_conjAut 𝕂
    (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldSp m 𝕂 σ A)]
  change CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldAut m 𝕂 σ *
      CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.conjAut m 𝕂
        ⟨A, CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.statedSp_le_gsp A.2⟩ *
      (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldAut m 𝕂 σ)⁻¹ =
    CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.conjAut m 𝕂
      ⟨CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldSp m 𝕂 σ A,
        CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.statedSp_le_gsp
          (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldSp m 𝕂 σ A).2⟩
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldAut_mul_conjAut_mul_inv]
  congr 1

private theorem kgLangCSpAux_endPow_c {m : ℕ} (𝕂 : Type) [Field 𝕂]
    (σ : 𝕂 ≃+* 𝕂) (A : LargeEvenSpGroup 𝕂 m) (i : ℕ) :
    endPow ((MulAut.conj
        (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldAut m 𝕂 σ)).toMonoidHom) i
        (kgLangCSpAux_c (m := m) 𝕂 A) =
      kgLangCSpAux_c (m := m) 𝕂
        (endPow (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldSp m 𝕂 σ).toMonoidHom
          i A) := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [endPow_apply, Function.iterate_succ_apply', ← endPow_apply, ih]
      change (MulAut.conj (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldAut m 𝕂 σ))
          (kgLangCSpAux_c (m := m) 𝕂
            (endPow (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldSp m 𝕂 σ).toMonoidHom
              i A)) =
        kgLangCSpAux_c (m := m) 𝕂
          (endPow (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldSp m 𝕂 σ).toMonoidHom
            (i + 1) A)
      rw [kgLangCSpAux_conj_c]
      simp only [endPow_apply, Function.iterate_succ_apply']
      rfl

private theorem kgLangCSpAux_odd_card_of_isElemAbelian {p : ℕ} {G : Type*} [Group G] [Finite G]
    (hp : p.Prime) (hp2 : p ≠ 2) {E : Subgroup G} (hE : IsElemAbelian p E) :
    Odd (Nat.card E) := by
  rw [← Nat.not_even_iff_odd]
  intro heven
  have h2 : 2 ∣ Nat.card E := even_iff_two_dvd.mp heven
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hgp : g ^ p = 1 := Subtype.ext (hE.2 (g : G) g.2)
  have hdivp : orderOf g ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hgp
  have hdiv2 : orderOf g ∣ 2 := by rw [hg]
  have hcop : Nat.Coprime 2 p := by
    have hnotdvd : ¬ p ∣ 2 := by
      intro h
      have hple : p ≤ 2 := Nat.le_of_dvd (by norm_num) h
      have hpge : 2 ≤ p := hp.two_le
      omega
    exact (hp.coprime_iff_not_dvd.mpr hnotdvd).symm
  have h1 : orderOf g = 1 := by
    have hgcd := Nat.dvd_gcd hdiv2 hdivp
    rw [Nat.coprime_iff_gcd_eq_one.mp hcop] at hgcd
    exact Nat.dvd_one.mp hgcd
  rw [h1] at hg
  omega

private theorem kgLangCSpAux_map_scalar (m : ℕ) (𝕂 : Type) [Field 𝕂]
    (σ : 𝕂 ≃+* 𝕂) (r : 𝕂) :
    (Matrix.scalar (Fin m ⊕ Fin m) r).map σ =
      Matrix.scalar (Fin m ⊕ Fin m) (σ r) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.scalar_apply, Matrix.diagonal_apply, apply_ite σ, map_zero]

private theorem kgLangCSpAux_map_one (m : ℕ) (𝕂 : Type) [Field 𝕂]
    (σ : 𝕂 ≃+* 𝕂) :
    (1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂).map σ = 1 :=
  Matrix.map_one σ.toRingHom (map_zero σ) (map_one σ)

private theorem kgLangCSpAux_adjoin_comm {m : ℕ} {𝕂 : Type} [Field 𝕂]
    (P : Subgroup (GL (Fin m ⊕ Fin m) 𝕂))
    (hab : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) :
    ∀ x ∈ Algebra.adjoin 𝕂 ((fun g : GL (Fin m ⊕ Fin m) 𝕂 =>
        (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂)) '' (P : Set _)),
      ∀ y ∈ Algebra.adjoin 𝕂 ((fun g : GL (Fin m ⊕ Fin m) 𝕂 =>
        (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂)) '' (P : Set _)),
      x * y = y * x := by
  have hpair : ((fun g : GL (Fin m ⊕ Fin m) 𝕂 =>
      (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂)) '' (P : Set _)).Pairwise Commute := by
    intro a ha b hb _
    obtain ⟨g, hg, rfl⟩ := ha
    obtain ⟨h, hh, rfl⟩ := hb
    show Commute (↑g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂)
      (↑h : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂)
    rw [commute_iff_eq, ← Matrix.GeneralLinearGroup.coe_mul, ← Matrix.GeneralLinearGroup.coe_mul,
      hab g hg h hh]
  haveI : IsMulCommutative (Algebra.adjoin 𝕂 ((fun g : GL (Fin m ⊕ Fin m) 𝕂 =>
      (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂)) '' (P : Set _))) :=
    Algebra.isMulCommutative_adjoin 𝕂 hpair
  intro x hx y hy
  exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : _) (⟨y, hy⟩ : _))

private theorem kgLangCSpAux_coe_endPow {m : ℕ} (𝕂 : Type) [Field 𝕂] [CharP 𝕂 2]
    (σ : 𝕂 ≃+* 𝕂) (A : LargeEvenSpGroup 𝕂 m) (i : ℕ) :
    (((endPow (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldSp m 𝕂 σ).toMonoidHom i A :
        LargeEvenSpGroup 𝕂 m) : GL (Fin m ⊕ Fin m) 𝕂) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) =
      (((A : LargeEvenSpGroup 𝕂 m) : GL (Fin m ⊕ Fin m) 𝕂) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂).map (σ ^ i) := by
  induction i with
  | zero => rw [endPow_apply]; simp
  | succ i ih =>
      rw [endPow_apply, Function.iterate_succ_apply', ← endPow_apply]
      simp only [MulEquiv.coe_toMonoidHom]
      rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.coe_fieldSp, ih, pow_succ',
        Matrix.map_map]
      rfl

private abbrev kgLangCSpAux_J (m : ℕ) (𝕂 : Type) [Field 𝕂] :
    Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂 := LargeEvenSpForm 𝕂 m

private theorem kgLangCSpAux_J_eq_J (m : ℕ) (𝕂 : Type) [Field 𝕂] [CharP 𝕂 2] :
    kgLangCSpAux_J m 𝕂 = Matrix.J (Fin m) 𝕂 := by
  rw [kgLangCSpAux_J]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [largeEvenSpForm_def, Matrix.J, Matrix.fromBlocks, CharTwo.neg_eq]

private theorem kgLangCSpAux_J_isUnit (m : ℕ) (𝕂 : Type) [Field 𝕂] [CharP 𝕂 2] :
    IsUnit (kgLangCSpAux_J m 𝕂).det := by
  rw [kgLangCSpAux_J_eq_J]
  exact Matrix.isUnit_det_J (Fin m) 𝕂

private theorem kgLangCSpAux_J_mul_inv (m : ℕ) (𝕂 : Type) [Field 𝕂] [CharP 𝕂 2] :
    kgLangCSpAux_J m 𝕂 * (kgLangCSpAux_J m 𝕂)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ (kgLangCSpAux_J_isUnit m 𝕂)

private theorem kgLangCSpAux_J_inv_mul (m : ℕ) (𝕂 : Type) [Field 𝕂] [CharP 𝕂 2] :
    (kgLangCSpAux_J m 𝕂)⁻¹ * kgLangCSpAux_J m 𝕂 = 1 :=
  Matrix.nonsing_inv_mul _ (kgLangCSpAux_J_isUnit m 𝕂)

private theorem kgLangCSpAux_J_transpose (m : ℕ) (𝕂 : Type) [Field 𝕂] [CharP 𝕂 2] :
    Matrix.transpose (kgLangCSpAux_J m 𝕂) = kgLangCSpAux_J m 𝕂 := by
  rw [kgLangCSpAux_J]
  ext i j
  rw [Matrix.transpose_apply, largeEvenSpForm_def]
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.fromBlocks, Matrix.one_apply, eq_comm, CharTwo.neg_eq]

private theorem kgLangCSpAux_Jinv_transpose (m : ℕ) (𝕂 : Type) [Field 𝕂] [CharP 𝕂 2] :
    Matrix.transpose ((kgLangCSpAux_J m 𝕂)⁻¹) = (kgLangCSpAux_J m 𝕂)⁻¹ := by
  have h : Matrix.transpose ((kgLangCSpAux_J m 𝕂)⁻¹) * kgLangCSpAux_J m 𝕂 = 1 := by
    calc Matrix.transpose ((kgLangCSpAux_J m 𝕂)⁻¹) * kgLangCSpAux_J m 𝕂
        = Matrix.transpose ((kgLangCSpAux_J m 𝕂)⁻¹) *
            Matrix.transpose (kgLangCSpAux_J m 𝕂) := by rw [kgLangCSpAux_J_transpose m 𝕂]
      _ = Matrix.transpose (kgLangCSpAux_J m 𝕂 * (kgLangCSpAux_J m 𝕂)⁻¹) := by
            rw [← Matrix.transpose_mul]
      _ = 1 := by rw [kgLangCSpAux_J_mul_inv m 𝕂, Matrix.transpose_one]
  exact (Matrix.inv_eq_left_inv h).symm

private noncomputable def kgLangCSpAux_tau (m : ℕ) (𝕂 : Type) [Field 𝕂] :
    Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂 → Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂 :=
  fun x => (kgLangCSpAux_J m 𝕂)⁻¹ * Matrix.transpose x * kgLangCSpAux_J m 𝕂

private theorem kgLangCSpAux_tau_add (m : ℕ) (𝕂 : Type) [Field 𝕂] [CharP 𝕂 2]
    (a b : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) :
    kgLangCSpAux_tau m 𝕂 (a + b) = kgLangCSpAux_tau m 𝕂 a + kgLangCSpAux_tau m 𝕂 b := by
  simp only [kgLangCSpAux_tau, Matrix.transpose_add, mul_add, add_mul]

private theorem kgLangCSpAux_tau_mul (m : ℕ) (𝕂 : Type) [Field 𝕂] [CharP 𝕂 2]
    (a b : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) :
    kgLangCSpAux_tau m 𝕂 (a * b) = kgLangCSpAux_tau m 𝕂 b * kgLangCSpAux_tau m 𝕂 a := by
  have hJJ : kgLangCSpAux_J m 𝕂 * (kgLangCSpAux_J m 𝕂)⁻¹ = 1 := kgLangCSpAux_J_mul_inv m 𝕂
  simp only [kgLangCSpAux_tau, Matrix.transpose_mul]
  calc (kgLangCSpAux_J m 𝕂)⁻¹ * (Matrix.transpose b * Matrix.transpose a) * kgLangCSpAux_J m 𝕂
      = (kgLangCSpAux_J m 𝕂)⁻¹ * Matrix.transpose b * (kgLangCSpAux_J m 𝕂 * (kgLangCSpAux_J m 𝕂)⁻¹) *
          Matrix.transpose a * kgLangCSpAux_J m 𝕂 := by
          rw [hJJ, mul_one]
          simp only [Matrix.mul_assoc]
    _ = ((kgLangCSpAux_J m 𝕂)⁻¹ * Matrix.transpose b * kgLangCSpAux_J m 𝕂) *
          ((kgLangCSpAux_J m 𝕂)⁻¹ * Matrix.transpose a * kgLangCSpAux_J m 𝕂) := by
          simp only [Matrix.mul_assoc]

private theorem kgLangCSpAux_tau_one (m : ℕ) (𝕂 : Type) [Field 𝕂] [CharP 𝕂 2] :
    kgLangCSpAux_tau m 𝕂 1 = 1 := by
  simp only [kgLangCSpAux_tau, Matrix.transpose_one, Matrix.mul_one,
    kgLangCSpAux_J_inv_mul m 𝕂]

private theorem kgLangCSpAux_tau_tau (m : ℕ) (𝕂 : Type) [Field 𝕂] [CharP 𝕂 2]
    (a : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) :
    kgLangCSpAux_tau m 𝕂 (kgLangCSpAux_tau m 𝕂 a) = a := by
  have hinv : (kgLangCSpAux_J m 𝕂)⁻¹ * kgLangCSpAux_J m 𝕂 = 1 := kgLangCSpAux_J_inv_mul m 𝕂
  simp only [kgLangCSpAux_tau, Matrix.transpose_mul, Matrix.transpose_transpose,
    kgLangCSpAux_J_transpose m 𝕂, kgLangCSpAux_Jinv_transpose m 𝕂]
  calc (kgLangCSpAux_J m 𝕂)⁻¹ * (kgLangCSpAux_J m 𝕂 * (a * (kgLangCSpAux_J m 𝕂)⁻¹)) *
        kgLangCSpAux_J m 𝕂
      = ((kgLangCSpAux_J m 𝕂)⁻¹ * kgLangCSpAux_J m 𝕂) * a *
          ((kgLangCSpAux_J m 𝕂)⁻¹ * kgLangCSpAux_J m 𝕂) := by
          simp only [Matrix.mul_assoc]
    _ = a := by rw [hinv, one_mul, mul_one]

private theorem kgLangCSpAux_J_map (m : ℕ) (𝕂 : Type) [Field 𝕂]
    (σ : 𝕂 ≃+* 𝕂) : (kgLangCSpAux_J m 𝕂).map σ = kgLangCSpAux_J m 𝕂 := by
  rw [kgLangCSpAux_J]
  ext i j
  rw [Matrix.map_apply, largeEvenSpForm_def]
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.fromBlocks, Matrix.one_apply, apply_ite σ, map_neg, map_one, map_zero]

private theorem kgLangCSpAux_Jinv_map (m : ℕ) (𝕂 : Type) [Field 𝕂] [CharP 𝕂 2]
    (σ : 𝕂 ≃+* 𝕂) : ((kgLangCSpAux_J m 𝕂)⁻¹).map σ = (kgLangCSpAux_J m 𝕂)⁻¹ := by
  have h' : ((kgLangCSpAux_J m 𝕂)⁻¹).map σ * (kgLangCSpAux_J m 𝕂).map σ = 1 := by
    rw [← Matrix.map_mul, kgLangCSpAux_J_inv_mul m 𝕂]
    exact Matrix.map_one σ.toRingHom (map_zero σ) (map_one σ)
  have h2 := Matrix.inv_eq_left_inv h'
  rw [kgLangCSpAux_J_map m 𝕂 σ] at h2
  exact h2.symm

private theorem kgLangCSpAux_tau_map (m : ℕ) (𝕂 : Type) [Field 𝕂] [CharP 𝕂 2]
    (σ : 𝕂 ≃+* 𝕂) (a : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) :
    kgLangCSpAux_tau m 𝕂 (a.map σ) = (kgLangCSpAux_tau m 𝕂 a).map σ := by
  simp only [kgLangCSpAux_tau, Matrix.map_mul, Matrix.transpose_map, kgLangCSpAux_Jinv_map m 𝕂 σ,
    kgLangCSpAux_J_map m 𝕂 σ]

private theorem kgLangCSpAux_mapMatrix_iterate (m : ℕ) (𝕂 : Type) [Field 𝕂]
    (σ : 𝕂 ≃+* 𝕂) (n : ℕ) (a : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) :
    (⇑(RingHom.mapMatrix σ.toRingHom))^[n] a = a.map (σ ^ n) := by
  induction n with
  | zero => simp [Matrix.map_id]
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, RingHom.mapMatrix_apply, Matrix.map_map, pow_succ']
      rfl

private theorem kgLangCSpAux_coe_inv {m : ℕ} (𝕂 : Type) [Field 𝕂]
    (u : GL (Fin m ⊕ Fin m) 𝕂) :
    ((u⁻¹ : GL (Fin m ⊕ Fin m) 𝕂) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) =
      ((u : GL (Fin m ⊕ Fin m) 𝕂) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂)⁻¹ :=
  Matrix.GeneralLinearGroup.coe_inv u

private theorem kgLangCSpAux_tau_eq_inv {m : ℕ} (𝕂 : Type) [Field 𝕂] [CharP 𝕂 2]
    (A : LargeEvenSpGroup 𝕂 m) :
    kgLangCSpAux_tau m 𝕂 (((A : LargeEvenSpGroup 𝕂 m) : GL (Fin m ⊕ Fin m) 𝕂) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) =
      (((A⁻¹ : LargeEvenSpGroup 𝕂 m) : GL (Fin m ⊕ Fin m) 𝕂) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) := by
  let Am : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂 :=
    ((A : GL (Fin m ⊕ Fin m) 𝕂) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂)
  change kgLangCSpAux_tau m 𝕂 Am =
    (((A⁻¹ : LargeEvenSpGroup 𝕂 m) : GL (Fin m ⊕ Fin m) 𝕂) :
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂)
  have hsp : Matrix.transpose Am * kgLangCSpAux_J m 𝕂 * Am = kgLangCSpAux_J m 𝕂 := by
    simpa only [Am, kgLangCSpAux_J, largeEvenSpForm_def] using
      (CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff.mp A.2)
  have h : (kgLangCSpAux_J m 𝕂)⁻¹ * Matrix.transpose Am * kgLangCSpAux_J m 𝕂 * Am = 1 := by
    calc (kgLangCSpAux_J m 𝕂)⁻¹ * Matrix.transpose Am * kgLangCSpAux_J m 𝕂 * Am
        = (kgLangCSpAux_J m 𝕂)⁻¹ *
            (Matrix.transpose Am * kgLangCSpAux_J m 𝕂 * Am) := by
            simp only [Matrix.mul_assoc]
      _ = (kgLangCSpAux_J m 𝕂)⁻¹ * kgLangCSpAux_J m 𝕂 := by rw [hsp]
      _ = 1 := kgLangCSpAux_J_inv_mul m 𝕂
  have hinv := Matrix.inv_eq_left_inv h
  rw [kgLangCSpAux_tau, hinv.symm]
  rw [show (((A⁻¹ : LargeEvenSpGroup 𝕂 m) : GL (Fin m ⊕ Fin m) 𝕂) :
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) = Am⁻¹ from by
        rw [Subgroup.coe_inv]
        exact kgLangCSpAux_coe_inv 𝕂 (A : GL (Fin m ⊕ Fin m) 𝕂)]

private theorem kgLangCSpAux_tau_scalar {m : ℕ} (𝕂 : Type) [Field 𝕂] [CharP 𝕂 2]
    (r : 𝕂) : kgLangCSpAux_tau m 𝕂 (Matrix.scalar (Fin m ⊕ Fin m) r) =
      Matrix.scalar (Fin m ⊕ Fin m) r := by
  have htrans : Matrix.transpose (Matrix.scalar (Fin m ⊕ Fin m) r) =
      Matrix.scalar (Fin m ⊕ Fin m) r := by
    ext i j
    simp only [Matrix.transpose_apply, Matrix.scalar_apply, Matrix.diagonal_apply, eq_comm]
  have hcomm : Commute (Matrix.scalar (Fin m ⊕ Fin m) r) (kgLangCSpAux_J m 𝕂) :=
    Matrix.scalar_commute r (fun r' => Commute.all r r') (kgLangCSpAux_J m 𝕂)
  rw [kgLangCSpAux_tau, htrans]
  calc (kgLangCSpAux_J m 𝕂)⁻¹ * Matrix.scalar (Fin m ⊕ Fin m) r * kgLangCSpAux_J m 𝕂
      = (kgLangCSpAux_J m 𝕂)⁻¹ * (Matrix.scalar (Fin m ⊕ Fin m) r * kgLangCSpAux_J m 𝕂) := by
          rw [Matrix.mul_assoc]
    _ = (kgLangCSpAux_J m 𝕂)⁻¹ * (kgLangCSpAux_J m 𝕂 * Matrix.scalar (Fin m ⊕ Fin m) r) := by
          rw [hcomm.eq]
    _ = ((kgLangCSpAux_J m 𝕂)⁻¹ * kgLangCSpAux_J m 𝕂) * Matrix.scalar (Fin m ⊕ Fin m) r := by
          rw [Matrix.mul_assoc]
    _ = Matrix.scalar (Fin m ⊕ Fin m) r := by rw [kgLangCSpAux_J_inv_mul m 𝕂, one_mul]

theorem kgLangC_torusInput_symplectic {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {m n : ℕ} (hm : 2 ≤ m)
    (𝕂 : Type) [Field 𝕂] [Finite 𝕂] (h𝕂 : Nat.card 𝕂 = 2 ^ n)
    (J : Subgroup (MulAut (LargeEvenProj (LargeEvenSpGroup 𝕂 m))))
    (hJ : (J : Set (MulAut (LargeEvenProj (LargeEvenSpGroup 𝕂 m)))) =
      LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup 𝕂 m)) (LargeEvenGSpSet 𝕂 m))
    {f : MulAut (LargeEvenProj (LargeEvenSpGroup 𝕂 m))}
    (hf : f ∈ LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSpGroup 𝕂 m))) (hfp : orderOf f = p) :
    KGLangTorusInput p J (MulAut.conj f).toMonoidHom := by
  haveI : CharP 𝕂 2 := charP_two_of_card h𝕂
  haveI : NeZero m := ⟨by omega⟩
  obtain ⟨σ, hσ⟩ := RecipeFieldSp.exists_fieldAut_of_mem hf
  have hσo : orderOf σ = p := by
    have h1 := orderOf_injective
      (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldAut m 𝕂)
      (RecipeFieldSpU.fieldAut_injective (K := 𝕂) (m := m) (by omega)) σ
    rw [← hσ] at h1
    rw [hfp] at h1
    exact h1.symm
  intro E hEelem hEfix
  let mat : LargeEvenSpGroup 𝕂 m → Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂 :=
    fun x => ((x : GL (Fin m ⊕ Fin m) 𝕂) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂)
  let c : LargeEvenSpGroup 𝕂 m →* MulAut (LargeEvenProj (LargeEvenSpGroup 𝕂 m)) :=
    kgLangCSpAux_c (m := m) 𝕂
  let β : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂 →+*
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂 := RingHom.mapMatrix σ.toRingHom
  let τ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂 →
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂 := kgLangCSpAux_tau m 𝕂
  have hcinj : Function.Injective c := kgLangCSpAux_c_injective (m := m) 𝕂
  have hEinn : (E : Set (MulAut (LargeEvenProj (LargeEvenSpGroup 𝕂 m)))) ⊆
      Set.range (MulAut.conj : LargeEvenProj (LargeEvenSpGroup 𝕂 m) →* _) := by
    intro x hx
    have hxJ : x ∈ J := (hEfix x hx).1
    have hxI : x ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup 𝕂 m))
        (LargeEvenGSpSet 𝕂 m) := by rw [← hJ]; exact hxJ
    exact TableBSymp.sp_I_subset_inn (K := 𝕂) (m := m) hxI
  set Phat : Subgroup (LargeEvenSpGroup 𝕂 m) := E.comap c with hPhat
  have hErange : E ≤ c.range := by
    intro x hx
    obtain ⟨a, ha⟩ := hEinn hx
    obtain ⟨A, hA⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.proj_surjective (r := m) (K := 𝕂) a
    refine ⟨A, ?_⟩
    change kgLangCSpAux_c (m := m) 𝕂 A = x
    rw [kgLangCSpAux_c_apply (m := m) 𝕂 A, hA, ha]
  have hcP : Phat.map c = E := by
    rw [hPhat, Subgroup.map_comap_eq, inf_eq_right.mpr hErange]
  have hPhat_ab : ∀ a ∈ Phat, ∀ b ∈ Phat, a * b = b * a := by
    intro a ha b hb
    rw [hPhat] at ha hb
    apply hcinj
    rw [map_mul, map_mul]
    have hcomm : c a * c b = c b * c a := by
      letI : IsMulCommutative E := hEelem.1
      exact congrArg Subtype.val (mul_comm' (⟨c a, ha⟩ : E) (⟨c b, hb⟩ : E))
    exact hcomm
  have hcardPhat : Nat.card Phat = Nat.card E := by
    rw [← hcP]
    exact Nat.card_congr (Subgroup.equivMapOfInjective Phat c hcinj).toEquiv
  have hEodd : Odd (Nat.card E) := kgLangCSpAux_odd_card_of_isElemAbelian hp hp2 hEelem
  set P : Subgroup (GL (Fin m ⊕ Fin m) 𝕂) := Phat.map (LargeEvenSpGroup 𝕂 m).subtype with hP
  have hPab : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := by
    intro a ha b hb
    rw [hP] at ha hb
    obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hb
    exact congrArg (fun x : LargeEvenSpGroup 𝕂 m => (x : GL (Fin m ⊕ Fin m) 𝕂))
      (hPhat_ab a' ha' b' hb')
  have hcardP : Nat.card P = Nat.card E := by
    rw [hP, Subgroup.card_map_of_injective (LargeEvenSpGroup 𝕂 m).subtype_injective, hcardPhat]
  have hPodd : Odd (Nat.card P) := by rw [hcardP]; exact hEodd
  set B : Subalgebra 𝕂 (Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) :=
    Algebra.adjoin 𝕂 ((fun g : GL (Fin m ⊕ Fin m) 𝕂 =>
      (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂)) '' (P : Set _)) with hB
  have hBcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x :=
    kgLangCSpAux_adjoin_comm P hPab
  have hβsc : ∀ r : 𝕂, β (Matrix.scalar (Fin m ⊕ Fin m) r) =
      Matrix.scalar (Fin m ⊕ Fin m) (σ r) := by
    intro r
    change (Matrix.scalar (Fin m ⊕ Fin m) r).map σ = Matrix.scalar (Fin m ⊕ Fin m) (σ r)
    exact kgLangCSpAux_map_scalar m 𝕂 σ r
  have hβP : ∀ g ∈ P, β (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) ∈
      (fun g : GL (Fin m ⊕ Fin m) 𝕂 =>
        (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂)) '' (P : Set _) := by
    intro g hg
    rw [hP] at hg
    obtain ⟨A, hA, rfl⟩ := Subgroup.mem_map.mp hg
    have hcA : c A ∈ E := by rw [hPhat] at hA; exact hA
    have hfixA : (MulAut.conj f).toMonoidHom (c A) = c A := (hEfix (c A) hcA).2
    have hcompat : (MulAut.conj f).toMonoidHom (c A) =
        c (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldSp m 𝕂 σ A) := by
      rw [hσ]
      change (MulAut.conj
          (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldAut m 𝕂 σ)) (c A) =
        c (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldSp m 𝕂 σ A)
      exact kgLangCSpAux_conj_c 𝕂 σ A
    have hmem : CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldSp m 𝕂 σ A ∈ Phat := by
      rw [hPhat, Subgroup.mem_comap]
      rw [← hcompat, hfixA]
      exact hcA
    refine ⟨(CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldSp m 𝕂 σ A :
        GL (Fin m ⊕ Fin m) 𝕂),
      Subgroup.mem_map.mpr ⟨_, hmem, rfl⟩, ?_⟩
    change ((A : GL (Fin m ⊕ Fin m) 𝕂) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂).map σ =
      ((CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldSp m 𝕂 σ A :
        GL (Fin m ⊕ Fin m) 𝕂) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂)
    rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.coe_fieldSp]
  have hβp : ∀ a ∈ B, (⇑β)^[p] a = a := by
    intro a _
    rw [show ⇑β = ⇑(RingHom.mapMatrix σ.toRingHom) from rfl,
      kgLangCSpAux_mapMatrix_iterate m 𝕂 σ p a]
    have hσp : σ ^ p = 1 := by rw [← hσo]; exact pow_orderOf_eq_one σ
    rw [hσp]
    exact Matrix.map_id a
  have hβB : ∀ a ∈ B, β a ∈ B := by
    intro a ha
    rw [hB] at ha ⊢
    refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ ha
    · intro g hg
      obtain ⟨g₀, hg₀, rfl⟩ := hg
      exact Algebra.subset_adjoin (hβP g₀ hg₀)
    · intro r
      change β (algebraMap 𝕂 (Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) r) ∈ _
      rw [show algebraMap 𝕂 (Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) r =
          Matrix.scalar (Fin m ⊕ Fin m) r from rfl, hβsc]
      exact Subalgebra.algebraMap_mem _ (σ r)
    · intro x y hx hy hx' hy'
      rw [map_add]
      exact add_mem hx' hy'
    · intro x y hx hy hx' hy'
      rw [map_mul]
      exact mul_mem hx' hy'
  have hτB : ∀ a ∈ B, τ a ∈ B := by
    intro a ha
    rw [hB] at ha ⊢
    refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ ha
    · intro g hg
      obtain ⟨g₀, hg₀, rfl⟩ := hg
      rw [hP] at hg₀
      obtain ⟨A, hA, rfl⟩ := Subgroup.mem_map.mp hg₀
      change kgLangCSpAux_tau m 𝕂
        ((A : GL (Fin m ⊕ Fin m) 𝕂) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) ∈ _
      rw [kgLangCSpAux_tau_eq_inv 𝕂 A]
      exact Algebra.subset_adjoin
        ⟨((A⁻¹ : LargeEvenSpGroup 𝕂 m) : GL (Fin m ⊕ Fin m) 𝕂),
          Subgroup.mem_map.mpr ⟨A⁻¹, Phat.inv_mem hA, rfl⟩, rfl⟩
    · intro r
      change kgLangCSpAux_tau m 𝕂
        (algebraMap 𝕂 (Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) r) ∈ _
      rw [show algebraMap 𝕂 (Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) r =
          Matrix.scalar (Fin m ⊕ Fin m) r from rfl, kgLangCSpAux_tau_scalar (m := m) 𝕂 r]
      exact Subalgebra.algebraMap_mem _ r
    · intro x y hx hy hx' hy'
      change kgLangCSpAux_tau m 𝕂 (x + y) ∈ _
      rw [kgLangCSpAux_tau_add m 𝕂 x y]
      exact add_mem hx' hy'
    · intro x y hx hy hx' hy'
      change kgLangCSpAux_tau m 𝕂 (x * y) ∈ _
      rw [kgLangCSpAux_tau_mul m 𝕂 x y]
      exact mul_mem hy' hx'
  have hτadd : ∀ a ∈ B, ∀ b ∈ B, τ (a + b) = τ a + τ b :=
    fun a _ b _ => kgLangCSpAux_tau_add m 𝕂 a b
  have hτone : τ 1 = 1 := kgLangCSpAux_tau_one m 𝕂
  have hττ : ∀ a ∈ B, τ (τ a) = a := fun a _ => kgLangCSpAux_tau_tau m 𝕂 a
  have hτmul : ∀ a ∈ B, ∀ b ∈ B, τ (a * b) = τ a * τ b := by
    intro a ha b hb
    rw [show τ (a * b) = τ b * τ a from kgLangCSpAux_tau_mul m 𝕂 a b]
    exact hBcomm (τ b) (hτB b hb) (τ a) (hτB a ha)
  have hτβ : ∀ a ∈ B, τ (β a) = β (τ a) := by
    intro a _
    change kgLangCSpAux_tau m 𝕂 (a.map σ) = (kgLangCSpAux_tau m 𝕂 a).map σ
    exact kgLangCSpAux_tau_map m 𝕂 σ a
  have hH90 := kgLangC_span_h90_unitary (hp := hp) (hσ := hσo) P hPab hPodd B rfl β hβP hβsc
    hβp τ hτB hτadd hτmul hτone hττ hτβ
  let U : Subgroup (LargeEvenSpGroup 𝕂 m) :=
    { carrier := {x | mat x ∈ B ∧ mat x * τ (mat x) = 1}
      mul_mem' := by
        intro x y hx hy
        refine ⟨?_, ?_⟩
        · change mat (x * y) ∈ B
          rw [show mat (x * y) = mat x * mat y from by
            change (((x * y : LargeEvenSpGroup 𝕂 m) : GL (Fin m ⊕ Fin m) 𝕂) :
              Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) = _
            rw [Subgroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul]]
          exact mul_mem hx.1 hy.1
        · change mat (x * y) * τ (mat (x * y)) = 1
          rw [show mat (x * y) = mat x * mat y from by
            change (((x * y : LargeEvenSpGroup 𝕂 m) : GL (Fin m ⊕ Fin m) 𝕂) :
              Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) = _
            rw [Subgroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul]]
          rw [show τ (mat x * mat y) = τ (mat y) * τ (mat x) from
            kgLangCSpAux_tau_mul m 𝕂 (mat x) (mat y)]
          calc mat x * mat y * (τ (mat y) * τ (mat x))
              = mat x * (mat y * τ (mat y)) * τ (mat x) := by
                  simp only [Matrix.mul_assoc]
            _ = mat x * 1 * τ (mat x) := by rw [hy.2]
            _ = 1 := by rw [Matrix.mul_one, hx.2]
      one_mem' := by
        refine ⟨?_, ?_⟩
        · change mat 1 ∈ B
          rw [show mat 1 = (1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) from by
            change (((1 : LargeEvenSpGroup 𝕂 m) : GL (Fin m ⊕ Fin m) 𝕂) :
              Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) = 1
            rw [Subgroup.coe_one, Matrix.GeneralLinearGroup.coe_one]]
          exact B.one_mem
        · change mat 1 * τ (mat 1) = 1
          rw [show mat 1 = (1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) from by
            change (((1 : LargeEvenSpGroup 𝕂 m) : GL (Fin m ⊕ Fin m) 𝕂) :
              Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) = 1
            rw [Subgroup.coe_one, Matrix.GeneralLinearGroup.coe_one], hτone, Matrix.mul_one]
      inv_mem' := by
        intro x hx
        have hinv : mat x⁻¹ = τ (mat x) := by
          change (((x⁻¹ : LargeEvenSpGroup 𝕂 m) : GL (Fin m ⊕ Fin m) 𝕂) :
            Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) = τ (mat x)
          rw [Subgroup.coe_inv, Matrix.GeneralLinearGroup.coe_inv]
          exact Matrix.inv_eq_right_inv hx.2
        refine ⟨?_, ?_⟩
        · change mat x⁻¹ ∈ B
          rw [hinv]
          exact hτB (mat x) hx.1
        · change mat x⁻¹ * τ (mat x⁻¹) = 1
          rw [hinv, show τ (τ (mat x)) = mat x from kgLangCSpAux_tau_tau m 𝕂 (mat x)]
          rw [show τ (mat x) = (mat x)⁻¹ from (Matrix.inv_eq_right_inv hx.2).symm]
          exact Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp ⟨x, rfl⟩)
      }
  refine ⟨U.map c, ?_, ?_, ?_, ?_, ?_⟩
  · rintro n ⟨u, -, rfl⟩
    have hmem : c u ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup 𝕂 m))
        (LargeEvenGSpSet 𝕂 m) := by
      change kgLangCSpAux_c (m := m) 𝕂 u ∈ _
      rw [kgLangCSpAux_c_conjAut 𝕂 u]
      exact NbrGraphSymplectic.conjAut_mem
        (⟨u, CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.statedSp_le_gsp u.2⟩  : CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.gsp m 𝕂)
    show c u ∈ (J : Set (MulAut (LargeEvenProj (LargeEvenSpGroup 𝕂 m))))
    rw [hJ]
    exact hmem
  · rintro a ⟨x, hx, rfl⟩ b ⟨y, hy, rfl⟩
    have hxy : x * y = y * x := by
      apply CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.statedSp_ext
      change mat (x * y) = mat (y * x)
      rw [show mat (x * y) = mat x * mat y from by
        change (((x * y : LargeEvenSpGroup 𝕂 m) : GL (Fin m ⊕ Fin m) 𝕂) :
          Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) = _
        rw [Subgroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul],
        show mat (y * x) = mat y * mat x from by
        change (((y * x : LargeEvenSpGroup 𝕂 m) : GL (Fin m ⊕ Fin m) 𝕂) :
          Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) = _
        rw [Subgroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul]]
      exact hBcomm (mat x) hx.1 (mat y) hy.1
    rw [← map_mul, hxy, map_mul]
  · rintro n ⟨u, hu, rfl⟩
    refine ⟨CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldSp m 𝕂 σ u, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · change mat (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldSp m 𝕂 σ u) ∈ B
        rw [show mat (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldSp m 𝕂 σ u) =
            (mat u).map σ from by
          change (((CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldSp m 𝕂 σ u :
            LargeEvenSpGroup 𝕂 m) : GL (Fin m ⊕ Fin m) 𝕂) :
              Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) = _
          rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.coe_fieldSp]]
        exact hβB (mat u) hu.1
      · change mat (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldSp m 𝕂 σ u) *
            τ (mat (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldSp m 𝕂 σ u)) = 1
        rw [show mat (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldSp m 𝕂 σ u) =
            (mat u).map σ from by
          change (((CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldSp m 𝕂 σ u :
            LargeEvenSpGroup 𝕂 m) : GL (Fin m ⊕ Fin m) 𝕂) :
              Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) = _
          rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.coe_fieldSp],
          show τ ((mat u).map σ) = (τ (mat u)).map σ from kgLangCSpAux_tau_map m 𝕂 σ (mat u)]
        rw [← Matrix.map_mul, hu.2]
        exact kgLangCSpAux_map_one m 𝕂 σ
    · change c (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldSp m 𝕂 σ u) =
        (MulAut.conj f).toMonoidHom (c u)
      rw [hσ]
      change c (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldSp m 𝕂 σ u) =
        (MulAut.conj (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldAut m 𝕂 σ)) (c u)
      rw [kgLangCSpAux_conj_c 𝕂 σ u]
  · rintro n ⟨u, hu, rfl⟩ hnorm
    have hnormU : ((List.range p).map fun i => endPow
        (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldSp m 𝕂 σ).toMonoidHom i u).prod =
        1 := by
      apply hcinj
      rw [map_one, MonoidHom.map_list_prod, List.map_map, ← hnorm]
      apply congrArg List.prod
      apply List.map_congr_left
      intro i _
      rw [hσ]
      exact (kgLangCSpAux_endPow_c 𝕂 σ u i).symm
    have hnormMat : ((List.range p).map fun i => (⇑β)^[i] (mat u)).prod = 1 := by
      have h1 : (List.map (fun i => mat (endPow
          (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldSp m 𝕂 σ).toMonoidHom i u))
          (List.range p)).prod = 1 := by
        rw [show List.map (fun i => mat (endPow
            (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldSp m 𝕂 σ).toMonoidHom i u))
            (List.range p) = List.map ((Units.coeHom
              (Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂)).comp
                (LargeEvenSpGroup 𝕂 m).subtype)
            (List.map (fun i => endPow
              (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldSp m 𝕂 σ).toMonoidHom i u)
              (List.range p)) from by
          rw [List.map_map]; rfl]
        rw [← MonoidHom.map_list_prod, hnormU, map_one]
      have hcoe : List.map (fun i => mat (endPow
          (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldSp m 𝕂 σ).toMonoidHom i u))
          (List.range p) = List.map (fun i => (⇑β)^[i] (mat u)) (List.range p) := by
        apply List.map_congr_left
        intro i _
        rw [show (⇑β)^[i] (mat u) = (mat u).map (σ ^ i) from
          kgLangCSpAux_mapMatrix_iterate m 𝕂 σ i (mat u)]
        exact kgLangCSpAux_coe_endPow (m := m) 𝕂 σ u i
      rw [← hcoe]
      exact h1
    obtain ⟨s, hsB, hsτ, hsu⟩ := hH90 (u : GL (Fin m ⊕ Fin m) 𝕂) hu.1 hu.2 hnormMat
    have hsSp : s ∈ LargeEvenSpGroup 𝕂 m := by
      rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff]
      have hτs : τ (s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) =
          (s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂)⁻¹ :=
        (Matrix.inv_eq_right_inv hsτ).symm
      have hJ1 : Matrix.transpose (s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) *
            kgLangCSpAux_J m 𝕂 =
          kgLangCSpAux_J m 𝕂 * (s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂)⁻¹ := by
        have h : kgLangCSpAux_J m 𝕂 * ((kgLangCSpAux_J m 𝕂)⁻¹ *
            Matrix.transpose (s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) *
            kgLangCSpAux_J m 𝕂) =
            kgLangCSpAux_J m 𝕂 * (s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂)⁻¹ :=
          congrArg (fun x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂 =>
            kgLangCSpAux_J m 𝕂 * x) hτs
        rwa [← Matrix.mul_assoc, ← Matrix.mul_assoc, kgLangCSpAux_J_mul_inv m 𝕂,
          Matrix.one_mul] at h
      calc Matrix.transpose (s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) *
            kgLangCSpAux_J m 𝕂 * (s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂)
          = kgLangCSpAux_J m 𝕂 * (s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂)⁻¹ *
              (s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) := by rw [hJ1]
        _ = kgLangCSpAux_J m 𝕂 := by
            rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _
              ((Matrix.isUnit_iff_isUnit_det _).mp ⟨s, rfl⟩), Matrix.mul_one]
    have hmat_inj : Function.Injective mat := by
      intro a b h
      exact Subtype.ext (Units.ext h)
    have hsu' : u = (⟨s, hsSp⟩ : LargeEvenSpGroup 𝕂 m)⁻¹ *
        CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldSp m 𝕂 σ ⟨s, hsSp⟩ := by
      apply hmat_inj
      change ((u : GL (Fin m ⊕ Fin m) 𝕂) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) =
        mat ((⟨s, hsSp⟩ : LargeEvenSpGroup 𝕂 m)⁻¹ *
          CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldSp m 𝕂 σ ⟨s, hsSp⟩)
      rw [hsu]
      rw [show β s = (s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂).map σ from rfl]
      rw [show mat ((⟨s, hsSp⟩ : LargeEvenSpGroup 𝕂 m)⁻¹ *
            CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldSp m 𝕂 σ ⟨s, hsSp⟩) =
          ((s⁻¹ : GL (Fin m ⊕ Fin m) 𝕂) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) *
            (s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂).map σ from by
        change ((((⟨s, hsSp⟩ : LargeEvenSpGroup 𝕂 m)⁻¹ *
          CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldSp m 𝕂 σ ⟨s, hsSp⟩ :
            LargeEvenSpGroup 𝕂 m) : GL (Fin m ⊕ Fin m) 𝕂) :
            Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) = _
        simp only [Subgroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, Subgroup.coe_inv,
          Matrix.GeneralLinearGroup.coe_inv,
          CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.coe_fieldSp]]
    refine ⟨c ⟨s, hsSp⟩, ⟨⟨s, hsSp⟩, ⟨hsB, hsτ⟩, rfl⟩, ?_⟩
    rw [hsu']
    change c ((⟨s, hsSp⟩ : LargeEvenSpGroup 𝕂 m)⁻¹ *
        CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldSp m 𝕂 σ ⟨s, hsSp⟩) =
      (c ⟨s, hsSp⟩)⁻¹ * (MulAut.conj f).toMonoidHom (c ⟨s, hsSp⟩)
    rw [map_mul, map_inv, hσ, ← kgLangCSpAux_conj_c 𝕂 σ ⟨s, hsSp⟩]
    rfl
  · intro x hx
    rw [← hcP] at hx
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
    refine ⟨u, ?_, rfl⟩
    refine ⟨?_, ?_⟩
    · change mat u ∈ B
      exact Algebra.subset_adjoin
        ⟨(u : GL (Fin m ⊕ Fin m) 𝕂), Subgroup.mem_map.mpr ⟨u, hu, rfl⟩, rfl⟩
    · change mat u * τ (mat u) = 1
      rw [show τ (mat u) = (((u⁻¹ : LargeEvenSpGroup 𝕂 m) : GL (Fin m ⊕ Fin m) 𝕂) :
          Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) from kgLangCSpAux_tau_eq_inv 𝕂 u]
      rw [show mat u * (((u⁻¹ : LargeEvenSpGroup 𝕂 m) : GL (Fin m ⊕ Fin m) 𝕂) :
          Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) = 1 from by
        change (((u : LargeEvenSpGroup 𝕂 m) : GL (Fin m ⊕ Fin m) 𝕂) :
            Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) *
            (((u⁻¹ : LargeEvenSpGroup 𝕂 m) : GL (Fin m ⊕ Fin m) 𝕂) :
              Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) = 1
        rw [← Matrix.GeneralLinearGroup.coe_mul, ← Subgroup.coe_mul, mul_inv_cancel,
          Subgroup.coe_one, Matrix.GeneralLinearGroup.coe_one]]

theorem kgLangTorusDatumCont_symplectic {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {m n : ℕ} (hm : 2 ≤ m)
    (hpn : p ∣ n) (𝕂 : Type) [Field 𝕂] [Finite 𝕂] (h𝕂 : Nat.card 𝕂 = 2 ^ n)
    (hcyc : GGRawFieldCycW p (LargeEvenProj (LargeEvenSpGroup 𝕂 m))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup 𝕂 m)) (LargeEvenGSpSet 𝕂 m))
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSpGroup 𝕂 m))))
    (hZ : ∀ [Finite (HopfCover (LargeEvenProj (LargeEvenSpGroup 𝕂 m)))]
      (θ : HopfCover (LargeEvenProj (LargeEvenSpGroup 𝕂 m)) ⧸
        Subgroup.center (HopfCover (LargeEvenProj (LargeEvenSpGroup 𝕂 m))) ≃*
          LargeEvenProj (LargeEvenSpGroup 𝕂 m)),
      commutator (HopfCover (LargeEvenProj (LargeEvenSpGroup 𝕂 m))) = ⊤ →
      Nat.Coprime (Nat.card (Subgroup.center (HopfCover (LargeEvenProj (LargeEvenSpGroup 𝕂 m))))) p) :
    KGLangTorusDatumCont p (LargeEvenProj (LargeEvenSpGroup 𝕂 m))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup 𝕂 m)) (LargeEvenGSpSet 𝕂 m))
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSpGroup 𝕂 m))) := by
  haveI : CharP 𝕂 2 := charP_two_of_card h𝕂
  have hnpos : 0 < n := by
    by_contra h
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos h
    have h1 : 1 < Nat.card 𝕂 := Finite.one_lt_card
    rw [h𝕂, hn0, pow_zero] at h1
    omega
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hn3 : 3 ≤ n := le_trans hp3 (Nat.le_of_dvd hnpos hpn)
  have hF : (Infinite 𝕂 ∨ 4 ≤ Nat.card 𝕂) ∨ (Nat.card 𝕂 = 3 ∧ 2 ≤ m) ∨
      (Nat.card 𝕂 = 2 ∧ 3 ≤ m) := by
    refine Or.inl (Or.inr ?_)
    rw [h𝕂]
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hsimple : IsQuasisimple (LargeEvenSpGroup 𝕂 m) :=
    CFSG.LieType.Universal.Symplectic.isQuasisimple m 𝕂 (by omega) hF
  have hs : IsSimpleGroup (LargeEvenProj (LargeEvenSpGroup 𝕂 m)) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp 𝕂 m (by omega) hF
  have hna : ∃ a b : LargeEvenProj (LargeEvenSpGroup 𝕂 m), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hsimple.2.2
    refine ⟨(CFSG.LieType.Universal.Symplectic.centerQuotientEquiv m 𝕂) a,
      (CFSG.LieType.Universal.Symplectic.centerQuotientEquiv m 𝕂) b, ?_⟩
    intro h
    exact hab ((CFSG.LieType.Universal.Symplectic.centerQuotientEquiv m 𝕂).injective
      (by rw [map_mul, map_mul, h]))
  have hinn : ∀ r : LargeEvenProj (LargeEvenSpGroup 𝕂 m),
      MulAut.conj r ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup 𝕂 m))
        (LargeEvenGSpSet 𝕂 m) := fun r =>
    (RecipeFieldSp.mem_conjImage_iff_inn (m := m) (K := 𝕂)).mpr ⟨r, rfl⟩
  have hG1 : ∀ u ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup 𝕂 m))
        (LargeEvenGSpSet 𝕂 m),
      GGL45IsPElt p u → ∃ r : LargeEvenProj (LargeEvenSpGroup 𝕂 m), u = MulAut.conj r := by
    intro u hu _
    obtain ⟨r, hr⟩ := (RecipeFieldSp.mem_conjImage_iff_inn (m := m) (K := 𝕂)).mp hu
    exact ⟨r, hr.symm⟩
  have hconj : GGRawFieldConj p (LargeEvenProj (LargeEvenSpGroup 𝕂 m))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup 𝕂 m)) (LargeEvenGSpSet 𝕂 m))
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSpGroup 𝕂 m))) :=
    RecipeFieldSpU.ggRawFieldConj_symplectic (K := 𝕂) (m := m) (by omega) hp
  have hT : ∀ J' : Subgroup (MulAut (LargeEvenProj (LargeEvenSpGroup 𝕂 m))),
      (J' : Set (MulAut (LargeEvenProj (LargeEvenSpGroup 𝕂 m)))) =
        LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup 𝕂 m)) (LargeEvenGSpSet 𝕂 m) →
      ∀ f ∈ LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSpGroup 𝕂 m)), orderOf f = p →
        KGLangTorusInput p J' (MulAut.conj f).toMonoidHom := by
    intro J' hJ' f hf hfo
    exact kgLangC_torusInput_symplectic hp hp2 hm 𝕂 h𝕂 J' hJ' hf hfo
  have hM : KGLangTorusMPart p (LargeEvenProj (LargeEvenSpGroup 𝕂 m))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup 𝕂 m)) (LargeEvenGSpSet 𝕂 m))
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSpGroup 𝕂 m))) :=
    kgLangTorusMPart_of_inner hp hs hna hcyc hconj hinn hG1 hT (by
      intro hfin θ hcomm
      letI := hfin
      exact hZ θ hcomm)
  intro hfin θ hcomm A hA hAI hA0 α₀ hα₀ hα₀I
  letI := hfin
  have hcyc' := hcyc hs hna
  obtain ⟨J, S, hJI, hJS, hN, hcycS, hpS⟩ := hcyc'
  have hα₀J : kgInducedAut θ α₀ ∉ J := by
    intro h
    exact hα₀I (hJI ▸ h)
  have hAS : ∀ α ∈ A, kgInducedAut θ α ∈ S := by
    intro α hα
    obtain ⟨u, huI, f, hfF, huf⟩ := hAI α hα
    apply hpS (kgInducedAut θ α)
    · rw [huf]
      exact Subgroup.mul_mem _
        (Subgroup.subset_closure (Set.mem_union_left
          (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSpGroup 𝕂 m)) : Set _) huI))
        (Subgroup.closure_mono (fun _ hx => Set.mem_union_right
          (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup 𝕂 m)) (LargeEvenGSpSet 𝕂 m)) hx) hfF)
    · exact ⟨1, by rw [pow_one, ← map_pow, hA.2 α hα, map_one]⟩
  refine ⟨?_, hM θ hcomm A hA hAI hA0 α₀ hα₀ hα₀I⟩
  intro α hα
  obtain ⟨k, hk⟩ := kgLangLT1_decomp hp θ hJS hN hcycS hA hAS hα₀ hα₀J α hα
  exact ⟨k, hJI ▸ hk⟩

end CFSG.StandardType
