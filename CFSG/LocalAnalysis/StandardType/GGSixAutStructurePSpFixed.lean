module

public import CFSG.LocalAnalysis.StandardType.GGSixAutStructurePSp

public section

namespace CFSG.StandardType

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal.Symplectic CFSG.LieType.Universal.Symplectic.SpExtras
  TauCeti.GLSymplecticFin Matrix

namespace AutPSp

variable {n : ℕ} {K : Type} [Field K]

section Fixed

theorem fieldAut_proj_elt (σ : K ≃+* K) (ρ : RootSubgroupIndex n) (c : K) :
    fieldAut n K σ (proj n K (elt ρ c)) = proj n K (elt ρ (σ c)) := by
  rw [fieldAut_proj, fieldSp_elt]

theorem fieldAut_fixes_elt_one (σ : K ≃+* K) (ρ : RootSubgroupIndex n) :
    fieldAut n K σ (proj n K (elt ρ 1)) = proj n K (elt ρ 1) := by
  rw [fieldAut_proj_elt, map_one]

end Fixed

section Torus

variable [Finite K] [CharP K 2]

theorem exists_unit_mul_self (u : Kˣ) : ∃ s : Kˣ, s * s = u := by
  obtain ⟨s, hs⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) (u : K)
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hs
    exact u.ne_zero hs
  exact ⟨Units.mk0 s hs0, Units.ext (by rw [Units.val_mul, Units.val_mk0, hs])⟩

theorem exists_character_eq (ρ : RootSubgroupIndex n) (u : Kˣ) :
    ∃ d : Fin n → Kˣ, ρ.character d = u := by
  cases ρ with
  | positiveLong i =>
    obtain ⟨s, hs⟩ := exists_unit_mul_self u
    exact ⟨Pi.mulSingle i s, by simp [hs]⟩
  | negativeLong i =>
    obtain ⟨s, hs⟩ := exists_unit_mul_self u
    refine ⟨Pi.mulSingle i s⁻¹, ?_⟩
    simp only [RootSubgroupIndex.character_negativeLong, Pi.mulSingle_eq_same]
    rw [← mul_inv, hs, inv_inv]
  | difference i j hij =>
    refine ⟨Pi.mulSingle i u, ?_⟩
    simp [Pi.mulSingle_eq_of_ne hij.symm]
  | positiveSum i j hij =>
    refine ⟨Pi.mulSingle i u, ?_⟩
    simp [Pi.mulSingle_eq_of_ne hij.ne']
  | negativeSum i j hij =>
    refine ⟨Pi.mulSingle i u⁻¹, ?_⟩
    simp [Pi.mulSingle_eq_of_ne hij.ne']

theorem exists_conj_elt_one (ρ : RootSubgroupIndex n) {t : K} (ht : t ≠ 0) :
    ∃ h : StatedSp n K, elt ρ t = h * elt ρ 1 * h⁻¹ := by
  obtain ⟨d, hd⟩ := exists_character_eq ρ (Units.mk0 t ht)
  refine ⟨equivStatedSp n K (TauCeti.GLSymplecticFin.diagonal d), ?_⟩
  rw [elt, elt, ← map_inv, ← map_mul, ← map_mul,
    TauCeti.GLSymplecticFin.diagonal_mul_rootSubgroup_mul_inv, hd, Units.val_mk0, toAdd_ofAdd,
    mul_one]

end Torus

section OrdThree

@[expose] def idx : Fin n ⊕ Fin n → Fin n :=
  Sum.elim id id

@[expose] def Avoids (k : Fin n) : RootSubgroupIndex n → Prop
  | .positiveLong i => k ≠ i
  | .negativeLong i => k ≠ i
  | .difference i j _ => k ≠ i ∧ k ≠ j
  | .positiveSum i j _ => k ≠ i ∧ k ≠ j
  | .negativeSum i j _ => k ≠ i ∧ k ≠ j

theorem exists_ne_ne (hn : 3 ≤ n) (i j : Fin n) : ∃ k : Fin n, k ≠ i ∧ k ≠ j := by
  have hcard : ({i, j} : Finset (Fin n)).card < (Finset.univ : Finset (Fin n)).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact lt_of_le_of_lt Finset.card_le_two (by omega)
  obtain ⟨k, -, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
  exact ⟨k, hk⟩

theorem exists_avoids (hn : 3 ≤ n) (ρ : RootSubgroupIndex n) : ∃ k, Avoids k ρ := by
  cases ρ with
  | positiveLong i =>
    obtain ⟨k, hk, -⟩ := exists_ne_ne hn i i
    exact ⟨k, hk⟩
  | negativeLong i =>
    obtain ⟨k, hk, -⟩ := exists_ne_ne hn i i
    exact ⟨k, hk⟩
  | difference i j _ => exact exists_ne_ne hn i j
  | positiveSum i j _ => exact exists_ne_ne hn i j
  | negativeSum i j _ => exact exists_ne_ne hn i j

theorem E_apply_eq_zero_left {k : Fin n} {ρ : RootSubgroupIndex n} (hk : Avoids k ρ)
    {b : Fin n ⊕ Fin n} (hb : idx b = k) (y : Fin n ⊕ Fin n) : E K ρ b y = 0 := by
  subst hb
  cases ρ with
  | positiveLong i => rcases b with b | b <;> simp_all [Avoids, idx, E, eq_comm]
  | negativeLong i => rcases b with b | b <;> simp_all [Avoids, idx, E, eq_comm]
  | difference i j _ =>
    rcases b with b | b <;> simp_all [Avoids, idx, E, eq_comm]
  | positiveSum i j _ =>
    rcases b with b | b <;> simp_all [Avoids, idx, E, eq_comm]
  | negativeSum i j _ =>
    rcases b with b | b <;> simp_all [Avoids, idx, E, eq_comm]

theorem E_apply_eq_zero_right {k : Fin n} {ρ : RootSubgroupIndex n} (hk : Avoids k ρ)
    {a : Fin n ⊕ Fin n} (ha : idx a = k) (x : Fin n ⊕ Fin n) : E K ρ x a = 0 := by
  subst ha
  cases ρ with
  | positiveLong i => rcases a with a | a <;> simp_all [Avoids, idx, E, eq_comm]
  | negativeLong i => rcases a with a | a <;> simp_all [Avoids, idx, E, eq_comm]
  | difference i j _ =>
    rcases a with a | a <;> simp_all [Avoids, idx, E, eq_comm]
  | positiveSum i j _ =>
    rcases a with a | a <;> simp_all [Avoids, idx, E, eq_comm]
  | negativeSum i j _ =>
    rcases a with a | a <;> simp_all [Avoids, idx, E, eq_comm]

theorem single_mul_E {k : Fin n} {ρ : RootSubgroupIndex n} (hk : Avoids k ρ)
    {a b : Fin n ⊕ Fin n} (hb : idx b = k) : single a b (1 : K) * E K ρ = 0 := by
  ext x y
  by_cases hx : x = a
  · subst hx
    rw [Matrix.single_mul_apply_same, E_apply_eq_zero_left hk hb, mul_zero, Matrix.zero_apply]
  · rw [Matrix.single_mul_apply_of_ne _ _ _ _ _ hx, Matrix.zero_apply]

theorem E_mul_single {k : Fin n} {ρ : RootSubgroupIndex n} (hk : Avoids k ρ)
    {a b : Fin n ⊕ Fin n} (ha : idx a = k) : E K ρ * single a b (1 : K) = 0 := by
  ext x y
  by_cases hy : y = b
  · subst hy
    rw [Matrix.mul_single_apply_same, E_apply_eq_zero_right hk ha, zero_mul, Matrix.zero_apply]
  · rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hy, Matrix.zero_apply]

theorem elt_comm_of_E_mul {ρ ρ' : RootSubgroupIndex n} (h1 : E K ρ * E K ρ' = 0)
    (h2 : E K ρ' * E K ρ = 0) : elt ρ (1 : K) * elt ρ' 1 = elt ρ' 1 * elt ρ 1 := by
  apply mat_injective
  rw [map_mul, map_mul, mat_elt, mat_elt, one_smul, one_smul]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, h1, h2, add_zero]
  abel

theorem positiveLong_comm {k : Fin n} {ρ : RootSubgroupIndex n} (hk : Avoids k ρ) :
    elt (.positiveLong k) (1 : K) * elt ρ 1 = elt ρ 1 * elt (.positiveLong k) 1 :=
  elt_comm_of_E_mul (single_mul_E hk rfl) (E_mul_single hk rfl)

theorem negativeLong_comm {k : Fin n} {ρ : RootSubgroupIndex n} (hk : Avoids k ρ) :
    elt (.negativeLong k) (1 : K) * elt ρ 1 = elt ρ 1 * elt (.negativeLong k) 1 :=
  elt_comm_of_E_mul (single_mul_E hk rfl) (E_mul_single hk rfl)

noncomputable abbrev ordElt (k : Fin n) : StatedSp n K :=
  elt (.positiveLong k) 1 * elt (.negativeLong k) 1

theorem ordElt_comm {k : Fin n} {ρ : RootSubgroupIndex n} (hk : Avoids k ρ) :
    ordElt k * elt ρ (1 : K) = elt ρ 1 * ordElt k := by
  rw [ordElt, mul_assoc, negativeLong_comm hk, ← mul_assoc, positiveLong_comm hk, mul_assoc]

theorem fieldAut_fixes_ordElt (σ : K ≃+* K) (k : Fin n) :
    fieldAut n K σ (proj n K (ordElt k)) = proj n K (ordElt k) := by
  rw [ordElt, map_mul, map_mul, fieldAut_fixes_elt_one, fieldAut_fixes_elt_one]

theorem mat_ordElt (k : Fin n) :
    mat n K (ordElt k) = ((AutPSL.ordThree (K := K)
      (Sum.inl_ne_inr : (Sum.inl k : Fin n ⊕ Fin n) ≠ Sum.inr k) :
        SpecialLinearGroup (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) := by
  rw [ordElt, map_mul, mat_elt, mat_elt, one_smul, one_smul]
  rfl

theorem ordElt_pow_three [CharP K 2] (k : Fin n) : (ordElt k : StatedSp n K) ^ 3 = 1 := by
  apply mat_injective
  rw [map_pow, mat_ordElt, map_one]
  have h := congrArg (fun g : SpecialLinearGroup (Fin n ⊕ Fin n) K =>
    (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K))
    (AutPSL.ordThree_pow_three (K := K)
      (Sum.inl_ne_inr : (Sum.inl k : Fin n ⊕ Fin n) ≠ Sum.inr k))
  simpa using h

theorem ordElt_ne_one (k : Fin n) : (ordElt k : StatedSp n K) ≠ 1 := by
  intro h
  have h1 := congrArg (fun g => mat n K g *ᵥ Pi.single (Sum.inr k) (1 : K)) h
  simp only [mat_ordElt, AutPSL.ordThree_mulVec, map_one, Matrix.one_mulVec] at h1
  have h2 := congrFun h1 (Sum.inl k)
  simp at h2

theorem orderOf_proj_ordElt [CharP K 2] (k : Fin n) : orderOf (proj n K (ordElt k)) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : NeZero n := ⟨k.pos.ne'⟩
  refine orderOf_eq_prime ?_ ?_
  · rw [← map_pow, ordElt_pow_three, map_one]
  · intro h
    apply ordElt_ne_one (K := K) k
    apply proj_injective
    rw [h, map_one]

end OrdThree

section Good

variable [CharP K 2]

theorem goodAut_fieldAut (hn : 3 ≤ n) (σ : K ≃+* K) (ρ : RootSubgroupIndex n)
    (hO : ∀ Q : Subgroup (StatedProj (StatedSp n K)), (∀ q ∈ Q, fieldAut n K σ q = q) →
      IsPGroup 2 Q → (∀ y : StatedProj (StatedSp n K), fieldAut n K σ y = y →
        ∀ q ∈ Q, y * q * y⁻¹ ∈ Q) → Q = ⊥) :
    GGGoodAut (proj n K (elt ρ 1)) (fieldAut n K σ) := by
  obtain ⟨k, hk⟩ := exists_avoids hn ρ
  refine ⟨hO, 1, ?_, proj n K (ordElt k), fieldAut_fixes_ordElt σ k, ?_, ?_, ?_⟩
  · simp only [one_mul, inv_one, mul_one]
    exact fieldAut_fixes_elt_one σ ρ
  · simp only [one_mul, inv_one, mul_one]
    rw [← map_mul, ordElt_comm hk, map_mul]
  · intro h
    have := orderOf_proj_ordElt (K := K) k
    rw [h, orderOf_one] at this
    omega
  · rw [orderOf_proj_ordElt]
    decide

theorem goodAut_conj (hn : 3 ≤ n) (ρ : RootSubgroupIndex n)
    {c : MulAut (StatedProj (StatedSp n K))} (hc : c ∈ compl)
    (hO : ∀ Q : Subgroup (StatedProj (StatedSp n K)), (∀ q ∈ Q, c q = q) → IsPGroup 2 Q →
      (∀ y : StatedProj (StatedSp n K), c y = y → ∀ q ∈ Q, y * q * y⁻¹ ∈ Q) → Q = ⊥)
    {e : MulAut (StatedProj (StatedSp n K))}
    (he : e ∈ (MulAut.conj : StatedProj (StatedSp n K) →* MulAut _).range) :
    GGGoodAut (proj n K (elt ρ 1)) (e * c * e⁻¹) := by
  obtain ⟨σ, rfl⟩ := hc
  obtain ⟨x, rfl⟩ := he
  exact (goodAut_fieldAut hn σ ρ hO).conj _ ⟨x, rfl⟩

end Good

end AutPSp

end CFSG.StandardType
