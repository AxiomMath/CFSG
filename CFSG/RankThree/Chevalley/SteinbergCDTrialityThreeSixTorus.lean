module

public import CFSG.RankThree.Chevalley.SteinbergCDTrialityTwelveTorus
public import CFSG.RankThree.Lattice.SteinbergBITrialityA2

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.Lattice
open scoped Matrix

@[expose] def threeSixExp (ε : ℤ) : ℕ := if ε = 1 then 4 else 10

@[expose] def threeSixW (ε : ℤ) : Matrix (Fin TwistTag.D4.tag.rank) (Fin TwistTag.D4.tag.rank) ℤ :=
  twelveW ^ threeSixExp ε

theorem threeSixW_eq_smul {ε : ℤ} (hε : ε = 1 ∨ ε = -1) :
    threeSixW ε = ε • trialityCoxeter ^ 4 := by
  rcases hε with rfl | rfl
  · exact (triality_three_six_unimodular_A2_root_partition.2.2.2.2.2.1).symm
  · exact (triality_three_six_unimodular_A2_root_partition.2.2.2.2.2.2.1).symm

theorem twelveW_pow_six : twelveW ^ 6 = -1 := trialityCoxeter_pow_six

theorem twelveW_pow_four_mulVec (v : Fin TwistTag.D4.tag.rank → ℤ) :
    (twelveW ^ 4 *ᵥ v) 0 = -v 3 ∧ (twelveW ^ 4 *ᵥ v) 1 = -v 1 + v 2 - v 3 ∧
      (twelveW ^ 4 *ᵥ v) 2 = v 0 - v 1 - v 3 ∧ (twelveW ^ 4 *ᵥ v) 3 = v 0 - v 3 := by
  have h4 : twelveW ^ 4 *ᵥ v = twelveW *ᵥ (twelveW *ᵥ (twelveW *ᵥ (twelveW *ᵥ v))) := by
    simp only [pow_succ, pow_zero, Matrix.one_mul, ← Matrix.mulVec_mulVec]
  rw [h4]
  obtain ⟨a0, a1, a2, a3⟩ := twelveW_mulVec v
  obtain ⟨b0, b1, b2, b3⟩ := twelveW_mulVec (twelveW *ᵥ v)
  obtain ⟨c0, c1, c2, c3⟩ := twelveW_mulVec (twelveW *ᵥ (twelveW *ᵥ v))
  obtain ⟨d0, d1, d2, d3⟩ := twelveW_mulVec (twelveW *ᵥ (twelveW *ᵥ (twelveW *ᵥ v)))
  rw [d0, d1, d2, d3, c0, c1, c2, c3, b0, b1, b2, b3, a0, a1, a2, a3]
  refine ⟨by ring, by ring, by ring, by ring⟩

theorem threeSixW_mulVec {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (v : Fin TwistTag.D4.tag.rank → ℤ) :
    (threeSixW ε *ᵥ v) 0 = ε * -v 3 ∧ (threeSixW ε *ᵥ v) 1 = ε * (-v 1 + v 2 - v 3) ∧
      (threeSixW ε *ᵥ v) 2 = ε * (v 0 - v 1 - v 3) ∧ (threeSixW ε *ᵥ v) 3 = ε * (v 0 - v 3) := by
  obtain ⟨a0, a1, a2, a3⟩ := twelveW_pow_four_mulVec v
  rcases hε with rfl | rfl
  · rw [threeSixW, show threeSixExp 1 = 4 from rfl]
    rw [a0, a1, a2, a3]
    refine ⟨by ring, by ring, by ring, by ring⟩
  · have h10 : threeSixW (-1) *ᵥ v = -(twelveW ^ 4 *ᵥ v) := by
      rw [threeSixW, show threeSixExp (-1) = 6 + 4 from rfl, pow_add, twelveW_pow_six,
        neg_one_mul, Matrix.neg_mulVec]
    rw [h10]
    simp only [Pi.neg_apply]
    rw [a0, a1, a2, a3]
    refine ⟨by ring, by ring, by ring, by ring⟩

section Monomial

variable {L : Type} [Field L]

variable (L) in
abbrev trialityM : ModGL TwistTag.D4.tag L := trialityTwistN L * diagramMap TwistTag.D4 L

abbrev trialityPsi (b : Fin TwistTag.D4.tag.rank → Lˣ) : Fin TwistTag.D4.tag.rank → Lˣ :=
  twelveTwistTuple 1 b

theorem trialityM_conj_rootDiagUnit (b : Fin TwistTag.D4.tag.rank → Lˣ) :
    trialityM L * rootDiagUnit TwistTag.D4.tag b * (trialityM L)⁻¹ =
      rootDiagUnit TwistTag.D4.tag (trialityPsi b) := by
  have hF : ∀ c : L, (RingHom.id L) c = c ^ 1 := fun c => (pow_one c).symm
  have h := trialityTwist_conj_rootDiagUnit (RingHom.id L) hF b
  rw [trialityFrob_apply, entrywise_frob_rootDiagUnit (RingHom.id L) hF, pow_one] at h
  rw [← h, trialityM, mul_inv_rev]
  group

theorem trialityM_pow_conj_rootDiagUnit (k : ℕ) (b : Fin TwistTag.D4.tag.rank → Lˣ) :
    trialityM L ^ k * rootDiagUnit TwistTag.D4.tag b * (trialityM L ^ k)⁻¹ =
      rootDiagUnit TwistTag.D4.tag (trialityPsi^[k] b) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ← trialityM_conj_rootDiagUnit, ← ih, pow_succ', mul_inv_rev]
    group

theorem rootChar_trialityPsi (b : Fin TwistTag.D4.tag.rank → Lˣ)
    (v : Fin TwistTag.D4.tag.rank → ℤ) :
    rootChar (trialityPsi b) (twelveW *ᵥ v) = rootChar b v := by
  obtain ⟨w0, w1, w2, w3⟩ := twelveW_mulVec v
  obtain ⟨t0, t1, t2, t3⟩ := twelveTwistTuple_values 1 b
  show rootChar (twelveTwistTuple 1 b) _ = _
  rw [rootChar, rootChar, prod_D4, prod_D4, w0, w1, w2, w3, t0, t1, t2, t3]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
  module

theorem rootChar_trialityPsi_iterate (k : ℕ) (b : Fin TwistTag.D4.tag.rank → Lˣ)
    (v : Fin TwistTag.D4.tag.rank → ℤ) :
    rootChar (trialityPsi^[k] b) ((twelveW ^ k) *ᵥ v) = rootChar b v := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', pow_succ', ← Matrix.mulVec_mulVec, rootChar_trialityPsi, ih]

theorem trialityM_pow_mul_inv_mem (k : ℕ) :
    trialityM L ^ k * (diagramMap TwistTag.D4 L ^ k)⁻¹ ∈ adjointGroup TwistTag.D4.tag L := by
  have hn : trialityTwistN L ∈ adjointGroup TwistTag.D4.tag L :=
    mul_mem (weylElt_mem_adjointGroup 2 1) (weylElt_mem_adjointGroup 0 1)
  induction k with
  | zero => simp [one_mem]
  | succ k ih =>
    have hconj : diagramMap TwistTag.D4 L ^ (k : ℤ) * trialityTwistN L *
        (diagramMap TwistTag.D4 L ^ (k : ℤ))⁻¹ ∈ adjointGroup TwistTag.D4.tag L := by
      rw [← map_conj_diagramMap_zpow TwistTag.D4 L (k : ℤ)]
      exact ⟨_, hn, rfl⟩
    rw [zpow_natCast] at hconj
    have h := mul_mem ih hconj
    have heq : trialityM L ^ (k + 1) * (diagramMap TwistTag.D4 L ^ (k + 1))⁻¹ =
        trialityM L ^ k * (diagramMap TwistTag.D4 L ^ k)⁻¹ *
          (diagramMap TwistTag.D4 L ^ k * trialityTwistN L *
            (diagramMap TwistTag.D4 L ^ k)⁻¹) := by
      rw [trialityM, pow_succ, pow_succ]
      group
    rw [heq]
    exact h

variable (L) in
abbrev threeSixN (ε : ℤ) : ModGL TwistTag.D4.tag L :=
  trialityM L ^ threeSixExp ε * (diagramMap TwistTag.D4 L)⁻¹

theorem threeSixN_mem_adjointGroup
    {ε : ℤ} (hε : ε = 1 ∨ ε = -1) :
    threeSixN L ε ∈ adjointGroup TwistTag.D4.tag L := by
  have hP3 : diagramMap TwistTag.D4 L ^ 3 = 1 := diagramMap_pow_order TwistTag.D4 L
  have hPm : diagramMap TwistTag.D4 L ^ threeSixExp ε = diagramMap TwistTag.D4 L := by
    rcases hε with rfl | rfl
    · rw [show threeSixExp 1 = 3 + 1 from rfl, pow_add, hP3, one_mul, pow_one]
    · rw [show threeSixExp (-1) = 3 * 3 + 1 from rfl, pow_add, pow_mul, hP3, one_pow, one_mul,
        pow_one]
  have h := trialityM_pow_mul_inv_mem (L := L) (threeSixExp ε)
  rwa [hPm] at h

variable (L) in
abbrev threeSixFrob (F : L →+* L) (ε : ℤ) : ModGL TwistTag.D4.tag L →* ModGL TwistTag.D4.tag L :=
  (MulAut.conj (threeSixN L ε)).toMonoidHom.comp (trialityFrob L F)

theorem threeSixFrob_apply (F : L →+* L) (ε : ℤ) (g : ModGL TwistTag.D4.tag L) :
    threeSixFrob L F ε g = threeSixN L ε * trialityFrob L F g * (threeSixN L ε)⁻¹ :=
  rfl

theorem threeSixFrob_rootDiagUnit (F : L →+* L) {q : ℕ} (hF : ∀ c, F c = c ^ q) (ε : ℤ)
    (a : Fin TwistTag.D4.tag.rank → Lˣ) :
    threeSixFrob L F ε (rootDiagUnit TwistTag.D4.tag a) =
      rootDiagUnit TwistTag.D4.tag (trialityPsi^[threeSixExp ε] (a ^ q)) := by
  rw [threeSixFrob_apply, trialityFrob_apply, entrywise_frob_rootDiagUnit F hF,
    ← trialityM_pow_conj_rootDiagUnit, threeSixN]
  group

theorem threeSixFrob_rootDiagUnit_eq_iff (F : L →+* L) {q : ℕ} (hF : ∀ c, F c = c ^ q)
    {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (a : Fin TwistTag.D4.tag.rank → Lˣ) :
    threeSixFrob L F ε (rootDiagUnit TwistTag.D4.tag a) = rootDiagUnit TwistTag.D4.tag a ↔
      ∀ v : Fin TwistTag.D4.tag.rank → ℤ, rootChar a (threeSixW ε *ᵥ v) = rootChar a v ^ q := by
  rw [threeSixFrob_rootDiagUnit F hF, rootDiagUnit_injective.eq_iff, threeSixW]
  have hpsi := rootChar_trialityPsi_iterate (threeSixExp ε) (a ^ q)
  have hpow : ∀ v, rootChar (a ^ q) v = rootChar a v ^ q := rootChar_pow_tuple a q
  constructor
  · intro h v
    rw [← hpow, ← hpsi v, h]
  · intro h
    have h12 : twelveW ^ 12 = 1 := trialityCoxeter_pow_twelve
    have hm : threeSixExp ε ≤ 12 := by
      rcases hε with rfl | rfl <;> decide
    have hall : ∀ v, rootChar (trialityPsi^[threeSixExp ε] (a ^ q)) v = rootChar a v := by
      intro v
      have hv : v = (twelveW ^ threeSixExp ε) *ᵥ ((twelveW ^ (12 - threeSixExp ε)) *ᵥ v) := by
        rw [Matrix.mulVec_mulVec, ← pow_add, Nat.add_sub_cancel' hm, h12, Matrix.one_mulVec]
      rw [hv, hpsi, hpow, h]
    funext i
    have := hall (Pi.single i 1)
    rwa [rootChar_single, rootChar_single] at this

end Monomial

section Characters

variable {L : Type} [Field L]

@[expose] def threeSixVec (x₀ x₁ x₂ x₃ : ℤ) : Fin TwistTag.D4.tag.rank → ℤ := ![x₀, x₁, x₂, x₃]

theorem threeSixVec_values (x₀ x₁ x₂ x₃ : ℤ) :
    threeSixVec x₀ x₁ x₂ x₃ 0 = x₀ ∧ threeSixVec x₀ x₁ x₂ x₃ 1 = x₁ ∧
      threeSixVec x₀ x₁ x₂ x₃ 2 = x₂ ∧ threeSixVec x₀ x₁ x₂ x₃ 3 = x₃ :=
  ⟨rfl, rfl, rfl, rfl⟩

@[expose] def threeSixTuple (q ε : ℤ) : Lˣ × Lˣ →* (Fin TwistTag.D4.tag.rank → Lˣ) where
  toFun b := ![b.1, b.2, b.2 ^ (-ε * q - 1), b.1 ^ (ε * q) * b.2 ^ (ε * q + 1)]
  map_one' := by
    refine (fin_D4_eq_iff _ _).2 ⟨rfl, rfl, ?_, ?_⟩
    · change (1 : Lˣ) ^ (-ε * q - 1) = 1
      exact one_zpow _
    · change (1 : Lˣ) ^ (ε * q) * 1 ^ (ε * q + 1) = 1
      rw [one_zpow, one_zpow, one_mul]
  map_mul' b b' := by
    refine (fin_D4_eq_iff _ _).2 ⟨rfl, rfl, ?_, ?_⟩
    · change (b.2 * b'.2) ^ (-ε * q - 1) = b.2 ^ (-ε * q - 1) * b'.2 ^ (-ε * q - 1)
      exact mul_zpow _ _ _
    · change (b.1 * b'.1) ^ (ε * q) * (b.2 * b'.2) ^ (ε * q + 1) =
        b.1 ^ (ε * q) * b.2 ^ (ε * q + 1) * (b'.1 ^ (ε * q) * b'.2 ^ (ε * q + 1))
      rw [mul_zpow, mul_zpow, mul_mul_mul_comm]

theorem threeSixTuple_values (q ε : ℤ) (b₁ b₂ : Lˣ) :
    threeSixTuple q ε (b₁, b₂) 0 = b₁ ∧ threeSixTuple q ε (b₁, b₂) 1 = b₂ ∧
      threeSixTuple q ε (b₁, b₂) 2 = b₂ ^ (-ε * q - 1) ∧
      threeSixTuple q ε (b₁, b₂) 3 = b₁ ^ (ε * q) * b₂ ^ (ε * q + 1) :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem rootChar_threeSixTuple (q ε : ℤ) (b₁ b₂ : Lˣ) (v : Fin TwistTag.D4.tag.rank → ℤ) :
    rootChar (threeSixTuple q ε (b₁, b₂)) v =
      b₁ ^ (v 0 + ε * q * v 3) * b₂ ^ (v 1 + (-ε * q - 1) * v 2 + (ε * q + 1) * v 3) := by
  obtain ⟨t0, t1, t2, t3⟩ := threeSixTuple_values q ε b₁ b₂
  rw [rootChar, prod_D4, t0, t1, t2, t3]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow]
  module

theorem zpow_eq_of_eq_add_mul {G : Type*} [Group G] {b : G} {d x y k : ℤ} (hb : b ^ d = 1)
    (h : x = y + d * k) : b ^ x = b ^ y := by
  rw [h, zpow_add, zpow_mul, hb, one_zpow, mul_one]

theorem threeSix_char_iff (q : ℕ) {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (c : Fin TwistTag.D4.tag.rank → Lˣ) :
    (∀ v : Fin TwistTag.D4.tag.rank → ℤ, rootChar c (threeSixW ε *ᵥ v) = rootChar c v ^ q) ↔
      c = threeSixTuple q ε (c 0, c 1) ∧ c 0 ^ ((q : ℤ) ^ 2 + ε * q + 1) = 1 ∧
        c 1 ^ ((q : ℤ) ^ 2 + ε * q + 1) = 1 := by
  have hε2 : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hχ : ∀ v : Fin TwistTag.D4.tag.rank → ℤ,
      rootChar c v = c 0 ^ v 0 * c 1 ^ v 1 * c 2 ^ v 2 * c 3 ^ v 3 := fun v => by
    rw [rootChar, prod_D4]
  constructor
  · intro h
    have key : ∀ x₀ x₁ x₂ x₃ : ℤ,
        c 0 ^ (ε * -x₃) * c 1 ^ (ε * (-x₁ + x₂ - x₃)) * c 2 ^ (ε * (x₀ - x₁ - x₃)) *
            c 3 ^ (ε * (x₀ - x₃)) =
          (c 0 ^ x₀ * c 1 ^ x₁ * c 2 ^ x₂ * c 3 ^ x₃) ^ q := fun x₀ x₁ x₂ x₃ => by
      have := h (threeSixVec x₀ x₁ x₂ x₃)
      obtain ⟨w0, w1, w2, w3⟩ := threeSixW_mulVec hε (threeSixVec x₀ x₁ x₂ x₃)
      obtain ⟨v0, v1, v2, v3⟩ := threeSixVec_values x₀ x₁ x₂ x₃
      rwa [hχ, hχ, w0, w1, w2, w3, v0, v1, v2, v3] at this
    have a1 := congrArg Additive.ofMul (key 1 0 0 0)
    have a2 := congrArg Additive.ofMul (key 0 0 ε ε)
    have a3 := congrArg Additive.ofMul (key 0 1 0 0)
    have a4 := congrArg Additive.ofMul (key 0 (-ε) (-ε) 0)
    simp only [ofMul_mul, ofMul_zpow, ofMul_pow, ← natCast_zsmul] at a1 a2 a3 a4
    have h0 : ((q : ℤ) ^ 2 + ε * q + 1) • Additive.ofMul (c 0) = 0 := by
      rcases hε with rfl | rfl
      · linear_combination (norm := module) (-(1 + (q : ℤ))) • a1 - a2
      · linear_combination (norm := module) (1 - (q : ℤ)) • a1 - a2
    have h1 : ((q : ℤ) ^ 2 + ε * q + 1) • Additive.ofMul (c 1) = 0 := by
      rcases hε with rfl | rfl
      · linear_combination (norm := module) (-(1 + (q : ℤ))) • a3 - a4
      · linear_combination (norm := module) (1 - (q : ℤ)) • a3 - a4
    have h2 : Additive.ofMul (c 2) = (-ε * q - 1) • Additive.ofMul (c 1) := by
      rcases hε with rfl | rfl
      · linear_combination (norm := module) -a3
      · linear_combination (norm := module) a3
    have h3 : Additive.ofMul (c 3) =
        (ε * q) • Additive.ofMul (c 0) + (ε * q + 1) • Additive.ofMul (c 1) := by
      rcases hε with rfl | rfl
      · linear_combination (norm := module) a1 + a3
      · linear_combination (norm := module) -a1 - a3
    obtain ⟨-, -, t2, t3⟩ := threeSixTuple_values (q : ℤ) ε (c 0) (c 1)
    refine ⟨(fin_D4_eq_iff _ _).2 ⟨rfl, rfl, ?_, ?_⟩, ?_, ?_⟩
    · rw [t2]
      exact Additive.ofMul.injective (by rw [ofMul_zpow]; exact h2)
    · rw [t3]
      exact Additive.ofMul.injective (by rw [ofMul_mul, ofMul_zpow, ofMul_zpow]; exact h3)
    · exact Additive.ofMul.injective (by rw [ofMul_zpow, ofMul_one]; exact h0)
    · exact Additive.ofMul.injective (by rw [ofMul_zpow, ofMul_one]; exact h1)
  · rintro ⟨hc, hd0, hd1⟩ v
    rw [hc, rootChar_threeSixTuple, rootChar_threeSixTuple]
    obtain ⟨w0, w1, w2, w3⟩ := threeSixW_mulVec hε v
    rw [w0, w1, w2, w3, mul_pow, ← zpow_natCast, ← zpow_natCast, ← _root_.zpow_mul,
      ← _root_.zpow_mul]
    congr 1
    · refine zpow_eq_of_eq_add_mul (k := -ε * v 3) hd0 ?_
      linear_combination ((q : ℤ) * v 0) * hε2
    · refine zpow_eq_of_eq_add_mul (k := ε * (v 2 - v 3)) hd1 ?_
      linear_combination ((q : ℤ) * v 1 - (q : ℤ) * v 2 + (q : ℤ) * v 3) * hε2

end Characters

section Torus

variable {L : Type} [Field L]

variable (L) in
@[expose] def threeSixTorus (F : L →+* L) (ε : ℤ) : Subgroup (ModGL TwistTag.D4.tag L) :=
  torusGroup TwistTag.D4.tag L ⊓ (threeSixFrob L F ε).eqLocus (MonoidHom.id _)

theorem rootDiagUnit_mem_threeSixTorus_iff [IsAlgClosed L] (F : L →+* L) {q : ℕ}
    (hF : ∀ c, F c = c ^ q) {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (a : Fin TwistTag.D4.tag.rank → Lˣ) :
    rootDiagUnit TwistTag.D4.tag a ∈ threeSixTorus L F ε ↔
      ∀ v : Fin TwistTag.D4.tag.rank → ℤ,
        rootChar a ((ε • twelveW ^ 4) *ᵥ v) = rootChar a v ^ q := by
  have h := threeSixFrob_rootDiagUnit_eq_iff F hF hε a
  rw [threeSixW_eq_smul hε] at h
  rw [threeSixTorus, Subgroup.mem_inf]
  exact ⟨fun hm => h.1 hm.2, fun hm => ⟨rootDiagUnit_mem_torusGroup a, h.2 hm⟩⟩

theorem rootDiagUnit_mem_threeSixTorus_iff' [IsAlgClosed L] (F : L →+* L) {q : ℕ}
    (hF : ∀ c, F c = c ^ q) {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (a : Fin TwistTag.D4.tag.rank → Lˣ) :
    rootDiagUnit TwistTag.D4.tag a ∈ threeSixTorus L F ε ↔
      a = threeSixTuple q ε (a 0, a 1) ∧ a 0 ^ ((q : ℤ) ^ 2 + ε * q + 1) = 1 ∧
        a 1 ^ ((q : ℤ) ^ 2 + ε * q + 1) = 1 := by
  refine (rootDiagUnit_mem_threeSixTorus_iff F hF hε a).trans ?_
  have h := threeSix_char_iff q hε a
  rw [threeSixW_eq_smul hε] at h
  exact h

variable (L) in
@[expose] def threeSixParam (q ε : ℤ) : Lˣ × Lˣ →* ModGL TwistTag.D4.tag L :=
  (rootDiagUnitHom TwistTag.D4.tag L).comp (threeSixTuple q ε)

theorem threeSixParam_apply (q ε : ℤ) (b : Lˣ × Lˣ) :
    threeSixParam L q ε b = rootDiagUnit TwistTag.D4.tag (threeSixTuple q ε b) :=
  rfl

theorem injective_threeSixParam (q ε : ℤ) : Function.Injective (threeSixParam L q ε) := by
  intro b b' h
  have h' : threeSixTuple q ε b = threeSixTuple q ε b' := rootDiagUnit_injective h
  exact Prod.ext (congrFun h' 0) (congrFun h' 1)

theorem threeSixTorus_eq_map [IsAlgClosed L] (F : L →+* L) {q : ℕ} (hF : ∀ c, F c = c ^ q)
    {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {d : ℕ} (hd : (d : ℤ) = (q : ℤ) ^ 2 + ε * q + 1) :
    threeSixTorus L F ε =
      ((rootsOfUnity d L).prod (rootsOfUnity d L)).map (threeSixParam L q ε) := by
  ext h
  constructor
  · intro hh
    obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh.1
    obtain ⟨ha, h0, h1⟩ := (rootDiagUnit_mem_threeSixTorus_iff' F hF hε a).1 hh
    refine ⟨(a 0, a 1), Subgroup.mem_prod.2 ⟨?_, ?_⟩, ?_⟩
    · rw [mem_rootsOfUnity, ← zpow_natCast, hd]
      exact h0
    · rw [mem_rootsOfUnity, ← zpow_natCast, hd]
      exact h1
    · rw [threeSixParam_apply, ← ha]
  · rintro ⟨b, hb, rfl⟩
    obtain ⟨hb1, hb2⟩ := Subgroup.mem_prod.1 hb
    rw [threeSixParam_apply, rootDiagUnit_mem_threeSixTorus_iff' F hF hε]
    refine ⟨rfl, ?_, ?_⟩
    · change b.1 ^ _ = 1
      rw [← hd, zpow_natCast]
      exact (mem_rootsOfUnity _ _).1 hb1
    · change b.2 ^ _ = 1
      rw [← hd, zpow_natCast]
      exact (mem_rootsOfUnity _ _).1 hb2

variable (L) in
@[expose] def threeSixTorsion (F : L →+* L) (ε : ℤ) (p : ℕ) :
    Subgroup (ModGL TwistTag.D4.tag L) where
  carrier := {h | h ∈ threeSixTorus L F ε ∧ h ^ p = 1}
  mul_mem' := fun {x y} hx hy => by
    obtain ⟨hx1, hx2⟩ := hx
    obtain ⟨hy1, hy2⟩ := hy
    have hc : Commute x y :=
      (triangular_borel_structure.{0, 0} TwistTag.D4.tag L).1 x hx1.1 y hy1.1
    exact ⟨mul_mem hx1 hy1, by rw [hc.mul_pow, hx2, hy2, one_mul]⟩
  one_mem' := ⟨one_mem _, one_pow p⟩
  inv_mem' := fun {x} hx => by
    obtain ⟨hx1, hx2⟩ := hx
    exact ⟨inv_mem hx1, by rw [inv_pow, hx2, inv_one]⟩

theorem mem_threeSixTorsion {F : L →+* L} {ε : ℤ} {p : ℕ} {h : ModGL TwistTag.D4.tag L} :
    h ∈ threeSixTorsion L F ε p ↔ h ∈ threeSixTorus L F ε ∧ h ^ p = 1 :=
  Iff.rfl

theorem threeSixTorsion_le (F : L →+* L) (ε : ℤ) (p : ℕ) :
    threeSixTorsion L F ε p ≤ threeSixTorus L F ε :=
  fun _ h => h.1

theorem threeSixTorsion_eq_map [IsAlgClosed L] (F : L →+* L) {q : ℕ} (hF : ∀ c, F c = c ^ q)
    {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {d : ℕ} (hd : (d : ℤ) = (q : ℤ) ^ 2 + ε * q + 1) {p : ℕ}
    (hpd : p ∣ d) :
    threeSixTorsion L F ε p =
      ((rootsOfUnity p L).prod (rootsOfUnity p L)).map (threeSixParam L q ε) := by
  ext h
  rw [mem_threeSixTorsion, threeSixTorus_eq_map F hF hε hd]
  constructor
  · rintro ⟨⟨b, -, rfl⟩, hp⟩
    have hb : b ^ p = 1 := injective_threeSixParam q ε (by rw [map_pow, hp, map_one])
    refine ⟨b, Subgroup.mem_prod.2 ⟨(mem_rootsOfUnity _ _).2 ?_, (mem_rootsOfUnity _ _).2 ?_⟩, rfl⟩
    · simpa using congrArg Prod.fst hb
    · simpa using congrArg Prod.snd hb
  · rintro ⟨b, hb, rfl⟩
    obtain ⟨hb1, hb2⟩ := Subgroup.mem_prod.1 hb
    refine ⟨⟨b, Subgroup.mem_prod.2 ⟨rootsOfUnity_le_of_dvd hpd hb1,
      rootsOfUnity_le_of_dvd hpd hb2⟩, rfl⟩, ?_⟩
    have hb' : b ^ p = 1 := Prod.ext ((mem_rootsOfUnity _ _).1 hb1) ((mem_rootsOfUnity _ _).1 hb2)
    rw [← map_pow, hb', map_one]

end Torus

end CFSG.RankThree.Chevalley
