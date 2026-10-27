module

public import CFSG.Quasithin.Background.GoldschmidtAutM12Fam
public import CFSG.Quasithin.Background.GoldschmidtAutM12Transfer
public import CFSG.Quasithin.SteinbergCDLinearThreeSylowSixteen
public import CFSG.RankThree.SteinbergR3ELinearUnitaryOuterOrder
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GroupTheory.ABGLocalTools.PStabilityQSL2
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalSmallSourceLinear
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.Permutation.AlternatingAutomorphism
public import CFSG.Quasithin.Background.GoldschmidtAutM12Orders
public import CFSG.Quasithin.Background.GoldschmidtZ2D8Sylow
public import CFSG.Quasithin.H13.Statements
public import CFSG.Sporadic.Schreier.TitsOther

public section

namespace CFSG.Quasithin.F6

open Matrix CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

namespace AutM12Recog

section Unitriangular

variable {k : Type} [Field k]

@[expose] def uMat (a b c : k) : Matrix (Fin 3) (Fin 3) k := !![1, a, c; 0, 1, b; 0, 0, 1]

theorem det_uMat (a b c : k) : (uMat a b c).det = 1 := by
  simp [uMat, Matrix.det_fin_three]

theorem uMat_mul (a b c a' b' c' : k) :
    uMat a b c * uMat a' b' c' = uMat (a + a') (b + b') (c + c' + a * b') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uMat, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

@[expose] def uSL (a b c : k) : SpecialLinearGroup (Fin 3) k := ⟨uMat a b c, det_uMat a b c⟩

theorem uSL_mul (a b c a' b' c' : k) :
    uSL a b c * uSL a' b' c' = uSL (a + a') (b + b') (c + c' + a * b') :=
  Subtype.ext (uMat_mul a b c a' b' c')

theorem uSL_zero : uSL (0 : k) 0 0 = 1 :=
  Subtype.ext (by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [uSL, uMat])

theorem uSL_inj {a b c a' b' c' : k} (h : uSL a b c = uSL a' b' c') :
    a = a' ∧ b = b' ∧ c = c' := by
  have h1 := congrArg (fun x : SpecialLinearGroup (Fin 3) k => (x : Matrix (Fin 3) (Fin 3) k) 0 1) h
  have h2 := congrArg (fun x : SpecialLinearGroup (Fin 3) k => (x : Matrix (Fin 3) (Fin 3) k) 1 2) h
  have h3 := congrArg (fun x : SpecialLinearGroup (Fin 3) k => (x : Matrix (Fin 3) (Fin 3) k) 0 2) h
  exact ⟨by simpa [uSL, uMat] using h1, by simpa [uSL, uMat] using h2,
    by simpa [uSL, uMat] using h3⟩

variable [CharP k 2]

theorem uSL_mul_self (a b c : k) : uSL a b c * uSL a b c = uSL 0 0 (a * b) := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  rw [uSL_mul]
  have e1 : a + a = 0 := by rw [← two_mul, h2, zero_mul]
  have e2 : b + b = 0 := by rw [← two_mul, h2, zero_mul]
  have e3 : c + c + a * b = a * b := by rw [← two_mul, h2, zero_mul, zero_add]
  rw [e1, e2, e3]

theorem uSL_mul_inv (a b c : k) : uSL a b c * uSL a b (c + a * b) = 1 := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  rw [uSL_mul, ← uSL_zero]
  have e1 : a + a = 0 := by rw [← two_mul, h2, zero_mul]
  have e2 : b + b = 0 := by rw [← two_mul, h2, zero_mul]
  have e3 : c + (c + a * b) + a * b = 0 := by
    have : c + (c + a * b) + a * b = 2 * (c + a * b) := by ring
    rw [this, h2, zero_mul]
  rw [e1, e2, e3]

@[expose] def uSub : Subgroup (SpecialLinearGroup (Fin 3) k) where
  carrier := {x | ∃ a b c, x = uSL a b c}
  one_mem' := ⟨0, 0, 0, uSL_zero.symm⟩
  mul_mem' := by
    rintro _ _ ⟨a, b, c, rfl⟩ ⟨a', b', c', rfl⟩
    exact ⟨_, _, _, uSL_mul a b c a' b' c'⟩
  inv_mem' := by
    rintro _ ⟨a, b, c, rfl⟩
    exact ⟨a, b, c + a * b, inv_eq_of_mul_eq_one_right (uSL_mul_inv a b c)⟩

@[expose] def uSubOne : Subgroup (SpecialLinearGroup (Fin 3) k) where
  carrier := {x | ∃ b c, x = uSL 0 b c}
  one_mem' := ⟨0, 0, uSL_zero.symm⟩
  mul_mem' := by
    rintro _ _ ⟨b, c, rfl⟩ ⟨b', c', rfl⟩
    refine ⟨b + b', c + c', ?_⟩
    rw [uSL_mul]
    simp
  inv_mem' := by
    rintro _ ⟨b, c, rfl⟩
    refine ⟨b, c, inv_eq_of_mul_eq_one_right ?_⟩
    have := uSL_mul_inv (0 : k) b c
    simpa using this

@[expose] def uSubTwo : Subgroup (SpecialLinearGroup (Fin 3) k) where
  carrier := {x | ∃ a c, x = uSL a 0 c}
  one_mem' := ⟨0, 0, uSL_zero.symm⟩
  mul_mem' := by
    rintro _ _ ⟨a, c, rfl⟩ ⟨a', c', rfl⟩
    refine ⟨a + a', c + c', ?_⟩
    rw [uSL_mul]
    simp
  inv_mem' := by
    rintro _ ⟨a, c, rfl⟩
    refine ⟨a, c, inv_eq_of_mul_eq_one_right ?_⟩
    have := uSL_mul_inv a (0 : k) c
    simpa using this

theorem uSub_isPGroup : IsPGroup 2 (uSub : Subgroup (SpecialLinearGroup (Fin 3) k)) := by
  rintro ⟨_, a, b, c, rfl⟩
  refine ⟨2, Subtype.ext ?_⟩
  show (uSL a b c) ^ 2 ^ 2 = 1
  have hx2 : uSL a b c ^ 2 = uSL 0 0 (a * b) := by rw [sq, uSL_mul_self]
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  calc uSL a b c ^ 2 ^ 2 = (uSL a b c ^ 2) ^ 2 := by
        rw [show (2 : ℕ) ^ 2 = 2 * 2 by norm_num, pow_mul]
    _ = uSL 0 0 (a * b) ^ 2 := by rw [hx2]
    _ = 1 := by
      rw [sq, uSL_mul, ← uSL_zero]
      have e : a * b + a * b = 0 := by rw [← two_mul, h2, zero_mul]
      simp [e]

theorem uSubOne_le : (uSubOne : Subgroup (SpecialLinearGroup (Fin 3) k)) ≤ uSub := by
  rintro _ ⟨b, c, rfl⟩
  exact ⟨0, b, c, rfl⟩

theorem uSubTwo_le : (uSubTwo : Subgroup (SpecialLinearGroup (Fin 3) k)) ≤ uSub := by
  rintro _ ⟨a, c, rfl⟩
  exact ⟨a, 0, c, rfl⟩

theorem uSubOne_elemAbelian :
    IsElemAbelian 2 (uSubOne : Subgroup (SpecialLinearGroup (Fin 3) k)) := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  refine ⟨⟨⟨?_⟩⟩, ?_⟩
  · rintro ⟨_, b, c, rfl⟩ ⟨_, b', c', rfl⟩
    apply Subtype.ext
    show uSL 0 b c * uSL 0 b' c' = uSL 0 b' c' * uSL 0 b c
    rw [uSL_mul, uSL_mul]
    simp [add_comm]
  · rintro _ ⟨b, c, rfl⟩
    rw [sq, uSL_mul, ← uSL_zero]
    have e1 : b + b = 0 := by rw [← two_mul, h2, zero_mul]
    have e2 : c + c = 0 := by rw [← two_mul, h2, zero_mul]
    simp [e1, e2]

theorem uSubTwo_elemAbelian :
    IsElemAbelian 2 (uSubTwo : Subgroup (SpecialLinearGroup (Fin 3) k)) := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  refine ⟨⟨⟨?_⟩⟩, ?_⟩
  · rintro ⟨_, a, c, rfl⟩ ⟨_, a', c', rfl⟩
    apply Subtype.ext
    show uSL a 0 c * uSL a' 0 c' = uSL a' 0 c' * uSL a 0 c
    rw [uSL_mul, uSL_mul]
    simp [add_comm]
  · rintro _ ⟨a, c, rfl⟩
    rw [sq, uSL_mul, ← uSL_zero]
    have e1 : a + a = 0 := by rw [← two_mul, h2, zero_mul]
    have e2 : c + c = 0 := by rw [← two_mul, h2, zero_mul]
    simp [e1, e2]

theorem uSubOne_ne_uSubTwo :
    (uSubOne : Subgroup (SpecialLinearGroup (Fin 3) k)) ≠ uSubTwo := by
  intro h
  have h1 : uSL (0 : k) 1 0 ∈ (uSubOne : Subgroup (SpecialLinearGroup (Fin 3) k)) := ⟨1, 0, rfl⟩
  rw [h] at h1
  obtain ⟨a, c, hac⟩ := h1
  exact one_ne_zero (uSL_inj hac).2.1

theorem card_uSubOne (hk : Nat.card k = 4) :
    Nat.card (uSubOne : Subgroup (SpecialLinearGroup (Fin 3) k)) = 16 := by
  let f : k × k → ↥(uSubOne : Subgroup (SpecialLinearGroup (Fin 3) k)) :=
    fun p => ⟨uSL 0 p.1 p.2, p.1, p.2, rfl⟩
  have hf : Function.Bijective f := by
    constructor
    · intro p q h
      have := uSL_inj (congrArg Subtype.val h)
      exact Prod.ext this.2.1 this.2.2
    · rintro ⟨_, b, c, rfl⟩
      exact ⟨(b, c), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod, hk]

theorem card_uSubTwo (hk : Nat.card k = 4) :
    Nat.card (uSubTwo : Subgroup (SpecialLinearGroup (Fin 3) k)) = 16 := by
  let f : k × k → ↥(uSubTwo : Subgroup (SpecialLinearGroup (Fin 3) k)) :=
    fun p => ⟨uSL p.1 0 p.2, p.1, p.2, rfl⟩
  have hf : Function.Bijective f := by
    constructor
    · intro p q h
      have := uSL_inj (congrArg Subtype.val h)
      exact Prod.ext this.1 this.2.2
    · rintro ⟨_, a, c, rfl⟩
      exact ⟨(a, c), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod, hk]

theorem hasTwoE16_specialLinear_three (hk : Nat.card k = 4)
    (P : Sylow 2 (SpecialLinearGroup (Fin 3) k)) :
    HasTwoE16 ↥(P : Subgroup (SpecialLinearGroup (Fin 3) k)) := by
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; norm_num)
  have : Finite (SpecialLinearGroup (Fin 3) k) :=
    Finite.of_injective (fun x => (x : Matrix (Fin 3) (Fin 3) k)) Subtype.val_injective
  exact hasTwoE16_sylow uSub_isPGroup uSubOne_le uSubTwo_le uSubOne_elemAbelian uSubTwo_elemAbelian
    (card_uSubOne hk) (card_uSubTwo hk) uSubOne_ne_uSubTwo P

end Unitriangular

theorem excl_psl_three_four {S : Type} [Group S] [Finite S]
    (h : StatedClassicalModel S .PSL 3 2 2) : Excl S := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
  have hfin : Finite K := Nat.finite_of_card_ne_zero (by rw [hK4]; norm_num)
  have hchar : CharP K 2 := CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow Nat.prime_two hK
  let e' : S ≃* projectiveSL 3 K :=
    (e.trans (projectiveSpecialLinearGroupEquivStatedProj 3 K).symm).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 K)
  have : Finite (projectiveSL 3 K) := Finite.of_equiv S e'.toEquiv
  refine Excl.of_mulEquiv e' (excl_of_hasTwoE16 fun Q => ?_)
  exact Tab.hasTwoE16_of_surjective (proj 3 K) (proj_surjective 3 K)
    (fun z hz => CFSG.Quasithin.SteinbergCD.pow_three_eq_one_of_mem_scalars (proj_eq_one_iff.mp hz))
    (hasTwoE16_specialLinear_three hK4) Q

theorem excl_psl_three_two {S : Type} [Group S] [Finite S]
    (h : StatedClassicalModel S .PSL 3 2 1) : Excl S := by
  have hcard := (CFSG.Timmesfeld.card_statedClassicalModel_two h).1 rfl
  obtain ⟨-, hf, hn, -, -⟩ := h.1
  obtain ⟨r, hr, hmr⟩ := (CFSG.Timmesfeld.Orders.profile_ordA (n := 2) (by omega) hf).two
  have hout := (CFSG.RankThree.OuterOrder.higher_linear_unitary_outer_order_determinant_bound
    (τ := .PSL) (Or.inl rfl) (n := 3) (ℓ := 2) (f := 1) (by norm_num) Nat.prime_two le_rfl h).1
  have hout2 : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer S) ≤ 2 := by
    have h2 : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer S) ∣ 2 := by
      simpa [CFSG.RankThree.OuterOrder.determinantParameter] using hout
    exact Nat.le_of_dvd (by norm_num) h2
  refine excl_of_outer_le (a := 3) (c := 2) ⟨r, hr, ?_⟩ (by norm_num) (by norm_num) hout2
  have hcard' : Nat.card S = Open.ordA 2 (2 ^ 1) := hcard
  rw [hcard', hmr]

end AutM12Recog

end CFSG.Quasithin.F6
