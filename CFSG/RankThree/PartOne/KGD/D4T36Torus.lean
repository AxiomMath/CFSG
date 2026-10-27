module

public import CFSG.RankThree.PartOne.KGD.D4QTorus
public import CFSG.RankThree.Lattice.SteinbergBITrialityA2

public noncomputable section

namespace CFSG.RankThree.PartOne.KGD

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Lattice
  CFSG.RankThree.Chevalley.TrialityFold
open scoped Matrix Polynomial

section Torus

variable {L : Type} [Field L]

@[expose] def d4T36A : Matrix (Fin TwistTag.D4.tag.rank) (Fin TwistTag.D4.tag.rank) ℤ :=
  !![0, 0, 0, -1; 0, -1, 1, -1; 1, -1, 0, -1; 1, 0, 0, -1]

theorem d4T36A_eq : d4T36A = trialityAMat := rfl

@[expose] def d4T36M (ε : ℤ) :
    Matrix (Fin TwistTag.D4.tag.rank) (Fin TwistTag.D4.tag.rank) ℤ := ε • d4T36A

theorem d4T36M_eq (ε : ℤ) : d4T36M ε = ε • trialityA := by
  rw [trialityA_eq, ← d4T36A_eq]
  rfl

theorem d4T36_prod {M : Type*} [CommMonoid M] (f : Fin TwistTag.D4.tag.rank → M) :
    ∏ i, f i = f 0 * f 1 * f 2 * f 3 :=
  Fin.prod_univ_four f

theorem d4T36M_mulVec_single (ε : ℤ) (j i : Fin TwistTag.D4.tag.rank) :
    (d4T36M ε *ᵥ (Pi.single j 1 : Fin TwistTag.D4.tag.rank → ℤ)) i = ε * d4T36A i j := by
  simp [Matrix.mulVec, dotProduct, d4T36M, Pi.single_apply]

theorem d4T36A_col :
    (d4T36A 0 0 = 0 ∧ d4T36A 1 0 = 0 ∧ d4T36A 2 0 = 1 ∧ d4T36A 3 0 = 1) ∧
    (d4T36A 0 1 = 0 ∧ d4T36A 1 1 = -1 ∧ d4T36A 2 1 = -1 ∧ d4T36A 3 1 = 0) ∧
    (d4T36A 0 2 = 0 ∧ d4T36A 1 2 = 1 ∧ d4T36A 2 2 = 0 ∧ d4T36A 3 2 = 0) ∧
    (d4T36A 0 3 = -1 ∧ d4T36A 1 3 = -1 ∧ d4T36A 2 3 = -1 ∧ d4T36A 3 3 = -1) := by
  decide

theorem rootChar_d4T36M_single (a : Fin TwistTag.D4.tag.rank → Lˣ) (ε : ℤ) :
    rootChar a (d4T36M ε *ᵥ (Pi.single 0 1 : Fin TwistTag.D4.tag.rank → ℤ)) =
        (a 2 * a 3) ^ ε ∧
      rootChar a (d4T36M ε *ᵥ (Pi.single 1 1 : Fin TwistTag.D4.tag.rank → ℤ)) =
        (a 1 * a 2)⁻¹ ^ ε ∧
      rootChar a (d4T36M ε *ᵥ (Pi.single 2 1 : Fin TwistTag.D4.tag.rank → ℤ)) = a 1 ^ ε ∧
      rootChar a (d4T36M ε *ᵥ (Pi.single 3 1 : Fin TwistTag.D4.tag.rank → ℤ)) =
        (a 0 * a 1 * a 2 * a 3)⁻¹ ^ ε := by
  obtain ⟨⟨c00, c10, c20, c30⟩, ⟨c01, c11, c21, c31⟩, ⟨c02, c12, c22, c32⟩,
    ⟨c03, c13, c23, c33⟩⟩ := d4T36A_col
  simp only [rootChar, d4T36_prod, d4T36M_mulVec_single, c00, c10, c20, c30, c01, c11, c21,
    c31, c02, c12, c22, c32, c03, c13, c23, c33]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply Additive.ofMul.injective <;>
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow] <;> module

theorem d4T36_add_iff {A : Type*} [AddCommGroup A] {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (q : ℤ)
    (x₀ x₁ x₂ x₃ : A) :
    (ε • (x₂ + x₃) = q • x₀ ∧ ε • (-(x₁ + x₂)) = q • x₁ ∧ ε • x₁ = q • x₂ ∧
      ε • (-(x₀ + x₁ + x₂ + x₃)) = q • x₃) ↔
    (x₁ = (ε * q) • x₂ ∧ x₃ = (ε * q) • x₀ - x₂ ∧ (q ^ 2 + ε * q + 1) • x₂ = 0 ∧
      (q ^ 2 + ε * q + 1) • x₀ = 0) := by
  rcases hε with rfl | rfl
  · constructor
    · rintro ⟨e0, e1, e2, e3⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · linear_combination (norm := module) e2
      · linear_combination (norm := module) e0
      · linear_combination (norm := module) -e1 - (q + 1) • e2
      · linear_combination (norm := module) -(q + 1) • e0 - e2 - e3
    · rintro ⟨g1, g2, g3, g4⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · linear_combination (norm := module) g2
      · linear_combination (norm := module) -(q + 1) • g1 - g3
      · linear_combination (norm := module) g1
      · linear_combination (norm := module) -g1 - (q + 1) • g2 - g4
  · constructor
    · rintro ⟨e0, e1, e2, e3⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · linear_combination (norm := module) -e2
      · linear_combination (norm := module) -e0
      · linear_combination (norm := module) e1 + (1 - q) • e2
      · linear_combination (norm := module) (1 - q) • e0 + e2 + e3
    · rintro ⟨g1, g2, g3, g4⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · linear_combination (norm := module) -g2
      · linear_combination (norm := module) (1 - q) • g1 + g3
      · linear_combination (norm := module) -g1
      · linear_combination (norm := module) g1 + (1 - q) • g2 + g4

variable {Fr : L →+* L} {q : ℕ}

theorem d4T36_units_iff {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (a : Fin TwistTag.D4.tag.rank → Lˣ) :
    ((a 2 * a 3) ^ ε = a 0 ^ q ∧ (a 1 * a 2)⁻¹ ^ ε = a 1 ^ q ∧ a 1 ^ ε = a 2 ^ q ∧
      (a 0 * a 1 * a 2 * a 3)⁻¹ ^ ε = a 3 ^ q) ↔
    (a 1 = (a 2 ^ q) ^ ε ∧ a 3 = (a 0 ^ q) ^ ε * (a 2)⁻¹ ∧
      a 2 ^ ((q : ℤ) ^ 2 + ε * q + 1) = 1 ∧ a 0 ^ ((q : ℤ) ^ 2 + ε * q + 1) = 1) := by
  have key := d4T36_add_iff hε (q : ℤ) (Additive.ofMul (a 0)) (Additive.ofMul (a 1))
    (Additive.ofMul (a 2)) (Additive.ofMul (a 3))
  constructor
  · rintro ⟨e0, e1, e2, e3⟩
    have e0' := congrArg Additive.ofMul e0
    have e1' := congrArg Additive.ofMul e1
    have e2' := congrArg Additive.ofMul e2
    have e3' := congrArg Additive.ofMul e3
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, ← natCast_zsmul] at e0' e1' e2' e3'
    obtain ⟨h1, h2, h3, h4⟩ := key.1 ⟨by linear_combination (norm := module) e0',
      by linear_combination (norm := module) e1', by linear_combination (norm := module) e2',
      by linear_combination (norm := module) e3'⟩
    refine ⟨Additive.ofMul.injective ?_, Additive.ofMul.injective ?_, Additive.ofMul.injective ?_,
      Additive.ofMul.injective ?_⟩
    · simp only [ofMul_zpow, ofMul_pow, ← natCast_zsmul]
      linear_combination (norm := module) h1
    · simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, ← natCast_zsmul]
      linear_combination (norm := module) h2
    · simp only [ofMul_zpow, ofMul_one]
      linear_combination (norm := module) h3
    · simp only [ofMul_zpow, ofMul_one]
      linear_combination (norm := module) h4
  · rintro ⟨g1, g2, g3, g4⟩
    have g1' := congrArg Additive.ofMul g1
    have g2' := congrArg Additive.ofMul g2
    have g3' := congrArg Additive.ofMul g3
    have g4' := congrArg Additive.ofMul g4
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, ← natCast_zsmul] at g1' g2'
    simp only [ofMul_zpow, ofMul_one] at g3' g4'
    obtain ⟨e0, e1, e2, e3⟩ := key.2 ⟨by linear_combination (norm := module) g1',
      by linear_combination (norm := module) g2', by linear_combination (norm := module) g3',
      by linear_combination (norm := module) g4'⟩
    refine ⟨Additive.ofMul.injective ?_, Additive.ofMul.injective ?_, Additive.ofMul.injective ?_,
      Additive.ofMul.injective ?_⟩
    · simp only [ofMul_mul, ofMul_zpow, ofMul_pow, ← natCast_zsmul]
      linear_combination (norm := module) e0
    · simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, ← natCast_zsmul]
      linear_combination (norm := module) e1
    · simp only [ofMul_zpow, ofMul_pow, ← natCast_zsmul]
      linear_combination (norm := module) e2
    · simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, ← natCast_zsmul]
      linear_combination (norm := module) e3

theorem rootChar_sum_D4 (a : Fin TwistTag.D4.tag.rank → Lˣ) {ι : Type*} (s : Finset ι)
    (v : ι → (Fin TwistTag.D4.tag.rank → ℤ)) :
    rootChar a (∑ i ∈ s, v i) = ∏ i ∈ s, rootChar a (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [rootChar_zero]
  | insert x s hx ih => rw [Finset.sum_insert hx, Finset.prod_insert hx, rootChar_add, ih]

theorem rootChar_mulVec_eq_prod
    (M : Matrix (Fin TwistTag.D4.tag.rank) (Fin TwistTag.D4.tag.rank) ℤ)
    (a : Fin TwistTag.D4.tag.rank → Lˣ) (u : Fin TwistTag.D4.tag.rank → ℤ) :
    rootChar a (M *ᵥ u) =
      ∏ j, rootChar a (M *ᵥ (Pi.single j 1 : Fin TwistTag.D4.tag.rank → ℤ)) ^ u j := by
  have hu : u = ∑ j, u j • (Pi.single j 1 : Fin TwistTag.D4.tag.rank → ℤ) := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hu]
  rw [Matrix.mulVec_sum, rootChar_sum_D4]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Matrix.mulVec_smul, rootChar_zsmul]

theorem mem_fixedCharTuples_d4T36 {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (hFr : ∀ c, Fr c = c ^ q)
    (a : Fin TwistTag.D4.tag.rank → Lˣ) :
    a ∈ fixedCharTuples (d4T36M ε) Fr ↔
      (a 1 = (a 2 ^ q) ^ ε ∧ a 3 = (a 0 ^ q) ^ ε * (a 2)⁻¹ ∧
        a 2 ^ ((q : ℤ) ^ 2 + ε * q + 1) = 1 ∧ a 0 ^ ((q : ℤ) ^ 2 + ε * q + 1) = 1) := by
  rw [← d4T36_units_iff hε a, mem_fixedCharTuples_iff]
  obtain ⟨c0, c1, c2, c3⟩ := rootChar_d4T36M_single a ε
  constructor
  · intro h
    have h0 := h (Pi.single 0 1)
    have h1 := h (Pi.single 1 1)
    have h2 := h (Pi.single 2 1)
    have h3 := h (Pi.single 3 1)
    rw [c0, CTTorus.rootChar_single, CTTorus.map_units_eq_pow hFr] at h0
    rw [c1, CTTorus.rootChar_single, CTTorus.map_units_eq_pow hFr] at h1
    rw [c2, CTTorus.rootChar_single, CTTorus.map_units_eq_pow hFr] at h2
    rw [c3, CTTorus.rootChar_single, CTTorus.map_units_eq_pow hFr] at h3
    exact ⟨h0, h1, h2, h3⟩
  · rintro ⟨e0, e1, e2, e3⟩ u
    rw [rootChar_mulVec_eq_prod, CTTorus.map_units_eq_pow hFr, rootChar, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun j _ => ?_
    have hj : rootChar a (d4T36M ε *ᵥ (Pi.single j 1 : Fin TwistTag.D4.tag.rank → ℤ)) = a j ^ q := by
      fin_cases j
      · exact c0 ▸ e0
      · exact c1 ▸ e1
      · exact c2 ▸ e2
      · exact c3 ▸ e3
    rw [hj, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]

@[expose] def d4T36d (ε : ℤ) (q : ℕ) : ℕ := ((q : ℤ) ^ 2 + ε * q + 1).toNat

theorem d4T36d_cast {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {q : ℕ} (hq : 1 ≤ q) :
    ((d4T36d ε q : ℕ) : ℤ) = (q : ℤ) ^ 2 + ε * q + 1 := by
  rw [d4T36d, Int.toNat_of_nonneg]
  have h1 : (1 : ℤ) ≤ q := by exact_mod_cast hq
  rcases hε with rfl | rfl <;> nlinarith

theorem d4T36d_odd {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {q : ℕ} (hq : 1 ≤ q) : Odd (d4T36d ε q) := by
  have h := d4T36d_cast hε hq
  rw [← Int.odd_coe_nat, h]
  rcases hε with rfl | rfl
  · have := (Int.even_mul_succ_self (q : ℤ)).add_one
    convert this using 1
    ring
  · have := (Int.even_mul_pred_self (q : ℤ)).add_one
    convert this using 1
    ring

theorem eq_of_d4QCoord_eq_d4T36 {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (hFr : ∀ c, Fr c = c ^ q)
    {a b : Fin TwistTag.D4.tag.rank → Lˣ} (ha : a ∈ fixedCharTuples (d4T36M ε) Fr)
    (hb : b ∈ fixedCharTuples (d4T36M ε) Fr) (h : d4QCoord a = d4QCoord b) : a = b := by
  rw [d4QCoord_apply, d4QCoord_apply] at h
  have h0 : a 0 = b 0 := congrFun h 0
  have h2 : a 2 = b 2 := congrFun h 1
  obtain ⟨ha1, ha3, -, -⟩ := (mem_fixedCharTuples_d4T36 hε hFr a).1 ha
  obtain ⟨hb1, hb3, -, -⟩ := (mem_fixedCharTuples_d4T36 hε hFr b).1 hb
  funext j
  fin_cases j
  · exact h0
  · change a 1 = b 1
    rw [ha1, hb1, h2]
  · exact h2
  · change a 3 = b 3
    rw [ha3, hb3, h0, h2]

@[expose] def d4T36Tuple (ε : ℤ) (q : ℕ) (b c : Lˣ) : Fin TwistTag.D4.tag.rank → Lˣ :=
  ![c, (b ^ q) ^ ε, b, (c ^ q) ^ ε * b⁻¹]

theorem d4T36Tuple_mem {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (hFr : ∀ c, Fr c = c ^ q) {b c : Lˣ}
    (hb : b ^ ((q : ℤ) ^ 2 + ε * q + 1) = 1) (hc : c ^ ((q : ℤ) ^ 2 + ε * q + 1) = 1) :
    d4T36Tuple ε q b c ∈ fixedCharTuples (d4T36M ε) Fr := by
  rw [mem_fixedCharTuples_d4T36 hε hFr]
  exact ⟨rfl, rfl, hb, hc⟩

theorem d4T36Tuple_coord (ε : ℤ) (q : ℕ) (b c : Lˣ) :
    d4QCoord (d4T36Tuple ε q b c) = ![c, b] := by
  rw [d4QCoord_apply]
  rfl

theorem d4T36_card [IsAlgClosed L] {ℓ : ℕ} [CharP L ℓ] {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (hq1 : 1 ≤ q) (hℓq : ℓ ∣ q) (hFr : ∀ c, Fr c = c ^ q) :
    Nat.card (fixedCharTuples (d4T36M ε) Fr) = d4T36d ε q * d4T36d ε q := by
  have hdz := d4T36d_cast hε hq1
  have hq0 : (q : L) = 0 := (CharP.cast_eq_zero_iff L ℓ q).2 hℓq
  have hd1 : ((d4T36d ε q : ℕ) : L) = 1 := by
    have h := congrArg (Int.cast : ℤ → L) hdz
    rw [Int.cast_natCast] at h
    rw [h]
    push_cast
    rw [hq0]
    simp
  have : NeZero ((d4T36d ε q : ℕ) : L) := ⟨by rw [hd1]; exact one_ne_zero⟩
  have : NeZero (d4T36d ε q) := ⟨fun h => by
    rw [h, Nat.cast_zero] at hd1
    exact zero_ne_one hd1⟩
  have hexp : ∀ x : Lˣ, x ^ ((q : ℤ) ^ 2 + ε * q + 1) = 1 ↔ x ^ (d4T36d ε q) = 1 := by
    intro x
    rw [← hdz, zpow_natCast]
  let φ₁ : fixedCharTuples (d4T36M ε) Fr →* rootsOfUnity (d4T36d ε q) L :=
    ((Pi.evalMonoidHom (fun _ => Lˣ) 2).comp (fixedCharTuples (d4T36M ε) Fr).subtype).codRestrict _
      fun a => by
        rw [mem_rootsOfUnity]
        exact (hexp _).1 ((mem_fixedCharTuples_d4T36 hε hFr a.1).1 a.2).2.2.1
  let φ₂ : fixedCharTuples (d4T36M ε) Fr →* rootsOfUnity (d4T36d ε q) L :=
    ((Pi.evalMonoidHom (fun _ => Lˣ) 0).comp (fixedCharTuples (d4T36M ε) Fr).subtype).codRestrict _
      fun a => by
        rw [mem_rootsOfUnity]
        exact (hexp _).1 ((mem_fixedCharTuples_d4T36 hε hFr a.1).1 a.2).2.2.2
  have hbij : Function.Bijective (φ₁.prod φ₂) := by
    constructor
    · intro a a' h
      have h1 := congrArg (fun z => ((z.1 : Lˣ))) h
      have h2 := congrArg (fun z => ((z.2 : Lˣ))) h
      refine Subtype.ext (eq_of_d4QCoord_eq_d4T36 hε hFr a.2 a'.2 ?_)
      rw [d4QCoord_apply, d4QCoord_apply]
      funext k
      fin_cases k
      · exact h2
      · exact h1
    · rintro ⟨⟨b, hb⟩, ⟨c, hc⟩⟩
      rw [mem_rootsOfUnity] at hb hc
      exact ⟨⟨d4T36Tuple ε q b c, d4T36Tuple_mem hε hFr ((hexp _).2 hb) ((hexp _).2 hc)⟩, rfl⟩
  rw [Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_prod,
    HasEnoughRootsOfUnity.natCard_rootsOfUnity L (d4T36d ε q)]

@[expose] def d4T36Col (x₁ x₂ x₃ x₄ : Fin TwistTag.D4.tag.rank → ℤ) :
    Matrix (Fin TwistTag.D4.tag.rank) (Fin TwistTag.D4.tag.rank) ℤ :=
  Matrix.of fun r k => (![x₁, x₂, x₃, x₄] : Fin 4 → Fin TwistTag.D4.tag.rank → ℤ) k r

theorem d4T36Col_eq (x₁ x₂ x₃ x₄ : Fin TwistTag.D4.tag.rank → ℤ) :
    d4T36Col x₁ x₂ x₃ x₄ = trialityColMat x₁ x₂ x₃ x₄ := rfl

theorem eq_one_of_cols_det (a : Fin TwistTag.D4.tag.rank → Lˣ)
    (x₁ x₂ x₃ x₄ : Fin TwistTag.D4.tag.rank → ℤ)
    (hdet : (d4T36Col x₁ x₂ x₃ x₄).det = -1)
    (h : rootChar a x₁ = 1 ∧ rootChar a x₂ = 1 ∧ rootChar a x₃ = 1 ∧ rootChar a x₄ = 1) :
    a = 1 := by
  refine CTTorus.eq_one_of_rootChar_eq_one fun v => ?_
  set N := d4T36Col x₁ x₂ x₃ x₄ with hN
  have hv : N *ᵥ (-(N.adjugate *ᵥ v)) = v := by
    rw [Matrix.mulVec_neg, Matrix.mulVec_mulVec, Matrix.mul_adjugate, hdet]
    simp [Matrix.neg_mulVec]
  have hcol : N *ᵥ (-(N.adjugate *ᵥ v)) =
      ∑ k, (-(N.adjugate *ᵥ v)) k • (![x₁, x₂, x₃, x₄] : Fin 4 → Fin TwistTag.D4.tag.rank → ℤ) k := by
    funext r
    simp [hN, d4T36Col, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hk : ∀ k : Fin 4, rootChar a
      ((![x₁, x₂, x₃, x₄] : Fin 4 → Fin TwistTag.D4.tag.rank → ℤ) k) = 1 := by
    intro k
    match k with
    | 0 => exact h.1
    | 1 => exact h.2.1
    | 2 => exact h.2.2.1
    | 3 => exact h.2.2.2
  rw [← hv, hcol, rootChar_sum_D4]
  refine Finset.prod_eq_one fun k _ => ?_
  rw [rootChar_zsmul, hk k, one_zpow]

theorem rootChar_mulA_eq_one {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    {a : Fin TwistTag.D4.tag.rank → Lˣ} (ha : a ∈ fixedCharTuples (d4T36M ε) Fr)
    {u : Fin TwistTag.D4.tag.rank → ℤ} (hu : rootChar a u = 1) :
    rootChar a (d4T36A *ᵥ u) = 1 := by
  have h := ha u
  rw [hu, map_one] at h
  have hMu : d4T36M ε *ᵥ u = ε • (d4T36A *ᵥ u) := by
    rw [d4T36M, Matrix.smul_mulVec]
  rw [hMu, rootChar_zsmul] at h
  rcases hε with rfl | rfl
  · simpa using h
  · simpa using h

theorem rootChar_powA_eq_one {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    {a : Fin TwistTag.D4.tag.rank → Lˣ} (ha : a ∈ fixedCharTuples (d4T36M ε) Fr)
    {u : Fin TwistTag.D4.tag.rank → ℤ} (hu : rootChar a u = 1) (n : ℕ) :
    rootChar a ((d4T36A ^ n) *ᵥ u) = 1 := by
  induction n with
  | zero => simpa using hu
  | succ n ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec]
    exact rootChar_mulA_eq_one hε ha ih

theorem d4T36_sigma_orbit : ∀ i : Fin 4,
    ∀ α ∈ (trialitySigmaList i : List (Fin TwistTag.D4.tag.rank → ℤ)),
    ∀ β ∈ (trialitySigmaList i : List (Fin TwistTag.D4.tag.rank → ℤ)),
    ∃ n < 3, β = (d4T36A ^ n) *ᵥ α ∨ β = -((d4T36A ^ n) *ᵥ α) := by
  decide +kernel

theorem d4T36_rootCharKernel_cases {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) {a : Fin TwistTag.D4.tag.rank → Lˣ}
    (ha : a ∈ fixedCharTuples (d4T36M ε) Fr) (ha1 : a ≠ 1) :
    rootCharKernel a = ∅ ∨ ∃ i : Fin 4, rootCharKernel a = trialitySigma i := by
  rcases (rootCharKernel a).eq_empty_or_nonempty with h | ⟨α, hα⟩
  · exact Or.inl h
  right
  obtain ⟨hαr, hα1⟩ := hα
  have hcover : ∀ {v : Fin TwistTag.D4.tag.rank → ℤ}, IsRoot TwistTag.D4.tag v →
      ∃ i, v ∈ trialitySigma i := fun {v} hv => by
    have : v ∈ {v | IsRoot Tag.D4 v} := hv
    rw [isRoot_eq_iUnion_trialitySigma] at this
    exact Set.mem_iUnion.1 this
  obtain ⟨i, hi⟩ := hcover hαr
  refine ⟨i, Set.ext fun β => ⟨fun ⟨hβr, hβ1⟩ => ?_, fun hβ => ?_⟩⟩
  · obtain ⟨j, hj⟩ := hcover hβr
    by_cases hij : i = j
    · rw [hij]
      exact hj
    · exfalso
      have hdet := (trialityColMat_det hε hαr hβr).2 (by
        rintro ⟨k, hk1, hk2⟩
        have h1 : k = i := by
          by_contra hki
          exact (Set.disjoint_left.1 (pairwise_disjoint_trialitySigma hki)) hk1 hi
        have h2 : k = j := by
          by_contra hkj
          exact (Set.disjoint_left.1 (pairwise_disjoint_trialitySigma hkj)) hk2 hj
        exact hij (h1.symm.trans h2))
      refine ha1 (eq_one_of_cols_det a α (d4T36M ε *ᵥ α) β (d4T36M ε *ᵥ β) ?_
        ⟨hα1, ?_, hβ1, ?_⟩)
      · rw [d4T36Col_eq, d4T36M_eq]
        exact hdet
      · have h := ha α
        rw [hα1, map_one] at h
        exact h
      · have h := ha β
        rw [hβ1, map_one] at h
        exact h
  · refine ⟨(isRoot_of_mem_trialitySigmaList (mem_trialitySigma.1 hβ)), ?_⟩
    obtain ⟨n, -, hn | hn⟩ := d4T36_sigma_orbit i α (mem_trialitySigma.1 hi) β
      (mem_trialitySigma.1 hβ)
    · rw [hn]
      exact rootChar_powA_eq_one hε ha hα1 n
    · have h2 : rootChar a (-((d4T36A ^ n) *ᵥ α)) = 1 := by
        rw [d4Q_rootChar_neg, rootChar_powA_eq_one hε ha hα1 n, inv_one]
      rw [hn]
      exact h2

end Torus

section Arith

theorem d4T36_ordProj {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {p q : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hq : 2 ≤ q) (hpd : (p : ℤ) ∣ (q : ℤ) ^ 2 + ε * q + 1) :
    p ^ (q ^ 12 * (q ^ 2 - 1) * (q ^ 6 - 1) * (q ^ 8 + q ^ 4 + 1)).factorization p =
      p ^ (d4T36d ε q * d4T36d ε q).factorization p := by
  have hq1 : 1 ≤ q := by omega
  have hdz := d4T36d_cast hε hq1
  have hn₀ : d4T36d ε q * d4T36d ε q ≠ 0 := by
    have : 0 < d4T36d ε q := (d4T36d_odd hε hq1).pos
    positivity
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hp2 : ¬ (p : ℤ) ∣ 2 := by
    intro h
    have : p ∣ 2 := by exact_mod_cast h
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have hq0 : ¬ (p : ℤ) ∣ q := by
    intro h
    have h1 : (p : ℤ) ∣ 1 := by
      have e : (1 : ℤ) = ((q : ℤ) ^ 2 + ε * q + 1) - q * (q + ε) := by ring
      rw [e]
      exact dvd_sub hpd (dvd_mul_of_dvd_left h _)
    exact hpz.not_dvd_one h1
  have hsmall : ∀ m : ℤ, m = 1 ∨ m = 3 → ¬ (p : ℤ) ∣ m := by
    intro m hm h
    rcases hm with rfl | rfl
    · exact hpz.not_dvd_one h
    · have : p ∣ 3 := by exact_mod_cast h
      have := Nat.le_of_dvd (by norm_num) this
      omega
  have hqm1 : ¬ (p : ℤ) ∣ (q : ℤ) - 1 := by
    intro h
    have h3 : (p : ℤ) ∣ 2 + ε := by
      have e : (2 + ε : ℤ) = ((q : ℤ) ^ 2 + ε * q + 1) - ((q : ℤ) - 1) * (q + 1 + ε) := by ring
      rw [e]
      exact dvd_sub hpd (dvd_mul_of_dvd_left h _)
    refine hsmall (2 + ε) ?_ h3
    rcases hε with rfl | rfl <;> norm_num
  have hqp1 : ¬ (p : ℤ) ∣ (q : ℤ) + 1 := by
    intro h
    have h3 : (p : ℤ) ∣ 2 - ε := by
      have e : (2 - ε : ℤ) = ((q : ℤ) ^ 2 + ε * q + 1) - ((q : ℤ) + 1) * (q - 1 + ε) := by ring
      rw [e]
      exact dvd_sub hpd (dvd_mul_of_dvd_left h _)
    refine hsmall (2 - ε) ?_ h3
    rcases hε with rfl | rfl <;> norm_num
  have hq2 : ¬ (p : ℤ) ∣ (q : ℤ) ^ 2 - ε * q + 1 := by
    intro h
    have h2 : (p : ℤ) ∣ 2 * (ε * q) := by
      have e : (2 * (ε * (q : ℤ))) = ((q : ℤ) ^ 2 + ε * q + 1) - ((q : ℤ) ^ 2 - ε * q + 1) := by
        ring
      rw [e]
      exact dvd_sub hpd h
    rcases hpz.dvd_or_dvd h2 with h3 | h3
    · exact hp2 h3
    · rcases hε with rfl | rfl
      · exact hq0 (by simpa using h3)
      · exact hq0 (by simpa using h3)
  have hq4 : ¬ (p : ℤ) ∣ (q : ℤ) ^ 4 - (q : ℤ) ^ 2 + 1 := by
    intro h
    have e : (2 * (q : ℤ) ^ 2) = ((q : ℤ) ^ 2 + ε * q + 1) * ((q : ℤ) ^ 2 - ε * q + 1) -
        ((q : ℤ) ^ 4 - (q : ℤ) ^ 2 + 1) := by
      rcases hε with rfl | rfl <;> ring
    have h2 : (p : ℤ) ∣ 2 * (q : ℤ) ^ 2 := by
      rw [e]
      exact dvd_sub (dvd_mul_of_dvd_left hpd _) h
    rcases hpz.dvd_or_dvd h2 with h3 | h3
    · exact hp2 h3
    · exact hq0 (hpz.dvd_of_dvd_pow h3)
  refine CTTw.ordProj_eq_of_int_cofactor hn₀
    (R := (q : ℤ) ^ 12 * ((q : ℤ) - 1) ^ 2 * ((q : ℤ) + 1) ^ 2 * ((q : ℤ) ^ 2 - ε * q + 1) ^ 2 *
      ((q : ℤ) ^ 4 - (q : ℤ) ^ 2 + 1)) ?_ ?_
  · simp only [Nat.cast_mul, CTTw.cast_pow_sub_one hq1, Nat.cast_add, Nat.cast_pow, Nat.cast_one,
      hdz]
    rcases hε with rfl | rfl <;> ring
  · intro hR
    rcases hpz.dvd_or_dvd hR with h | h
    · rcases hpz.dvd_or_dvd h with h | h
      · rcases hpz.dvd_or_dvd h with h | h
        · rcases hpz.dvd_or_dvd h with h | h
          · exact hq0 (hpz.dvd_of_dvd_pow h)
          · exact hqm1 (hpz.dvd_of_dvd_pow h)
        · exact hqp1 (hpz.dvd_of_dvd_pow h)
      · exact hq2 (hpz.dvd_of_dvd_pow h)
    · exact hq4 h

end Arith


end CFSG.RankThree.PartOne.KGD
