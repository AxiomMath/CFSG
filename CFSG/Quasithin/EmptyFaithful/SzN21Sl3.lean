module

public import CFSG.Quasithin.EmptyFaithful.SzN21Tr
public import CFSG.Quasithin.EmptyFaithful.SzN2Lin

public section

namespace CFSG.Quasithin

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X7a CFSG.Quasithin.SzN2

namespace SzN21

section Sl3

variable (K : Type) [Field K]

@[expose] noncomputable def diagSL3 (a b : Kˣ) : SpecialLinearGroup (Fin 3) K :=
  ⟨Matrix.diagonal ![(a : K), (b : K), (((a * b)⁻¹ : Kˣ) : K)], by
    rw [Matrix.det_diagonal, Fin.prod_univ_three]
    have h1 := a.ne_zero
    have h2 := b.ne_zero
    simp
    field_simp⟩

theorem coe_diagSL3 (a b : Kˣ) :
    ((diagSL3 K a b : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      Matrix.diagonal ![(a : K), (b : K), (((a * b)⁻¹ : Kˣ) : K)] := rfl

theorem diagSL3_one : diagSL3 K 1 1 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_one, coe_diagSL3]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem diagSL3_mul (a b c d : Kˣ) : diagSL3 K (a * c) (b * d) = diagSL3 K a b * diagSL3 K c d := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_diagSL3, coe_diagSL3, coe_diagSL3,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i
  · simp
  · simp
  · simp
    ring

@[expose] noncomputable def torusSL3 : Kˣ × Kˣ →* SpecialLinearGroup (Fin 3) K where
  toFun p := diagSL3 K p.1 p.2
  map_one' := diagSL3_one K
  map_mul' p q := diagSL3_mul K p.1 p.2 q.1 q.2

theorem torusSL3_injective : Function.Injective (torusSL3 K) := by
  intro p q h
  have h' := congrArg (fun A : SpecialLinearGroup (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K)) h
  simp only [torusSL3, MonoidHom.coe_mk, OneHom.coe_mk, coe_diagSL3] at h'
  have h0 := congrFun (congrFun h' 0) 0
  have h1 := congrFun (congrFun h' 1) 1
  simp at h0 h1
  exact Prod.ext (Units.ext h0) (Units.ext h1)

theorem torusSL3_mem_upperTriangular (p : Kˣ × Kˣ) : torusSL3 K p ∈ upperTriangular 3 K := by
  intro i j hij
  show (Matrix.diagonal ![(p.1 : K), (p.2 : K), (((p.1 * p.2)⁻¹ : Kˣ) : K)]) i j = 0
  rw [Matrix.diagonal_apply_ne _ (ne_of_gt hij)]

variable {K}

omit [Field K] in
theorem exists_finset_card_four [Finite K] (h4 : 4 ≤ Nat.card K) : ∃ s : Finset K, s.card = 4 := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset K)) (n := 4)
    (by simpa [Finset.card_univ, Nat.card_eq_fintype_card] using h4)
  exact ⟨s, hs⟩

omit [Field K] in
theorem four_le_card_of_two_pow {e : ℕ} (hK : Nat.card K = 2 ^ e) (he : 2 ≤ e) : 4 ≤ Nat.card K := by
  rw [hK]
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he

theorem exists_units_orderThree [Finite K] (hK : ∃ k : ℕ, Nat.card K = 2 ^ k)
    {y : SpecialLinearGroup (Fin 3) K} (hy : y ∈ upperTriangular 3 K) (hy3 : orderOf y = 3) :
    ∃ ω : Kˣ, orderOf ω = 3 := by
  obtain ⟨k, hk⟩ := hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU : IsPGroup 2 (unitriangular 3 K) :=
    IsPGroup.of_card (n := k * (3 * (3 - 1) / 2)) (by rw [card_unitriangular, hk, pow_mul])
  let β : ↥(upperTriangular 3 K) := ⟨y, hy⟩
  have hβ : orderOf β = 3 := (Subgroup.orderOf_mk y hy).trans hy3
  have hβ3 : β ^ 3 = 1 := by
    have := pow_orderOf_eq_one β
    rwa [hβ] at this
  by_cases hd : diagHomLin 3 K β = 1
  · exfalso
    have hmem : β ∈ (diagHomLin 3 K).ker := hd
    rw [ker_diagHomLin, Subgroup.mem_subgroupOf] at hmem
    obtain ⟨j, hj⟩ := hU ⟨y, hmem⟩
    have hpow : y ^ 2 ^ j = 1 := congrArg Subtype.val hj
    have h32 : 3 ∣ 2 ^ j := hy3 ▸ orderOf_dvd_of_pow_eq_one hpow
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h32
    omega
  · have hex : ∃ i, diagHomLin 3 K β i ≠ 1 := by
      by_contra hno
      push Not at hno
      exact hd (funext hno)
    obtain ⟨i, hi⟩ := hex
    have h1 : (diagHomLin 3 K β i) ^ 3 = 1 := by
      have h' : (diagHomLin 3 K β) ^ 3 = 1 := by
        rw [← map_pow, hβ3, map_one]
      simpa using congrFun h' i
    refine ⟨diagHomLin 3 K β i, ?_⟩
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime h1 hi

theorem rbProp_unitriangular_three [Finite K] (hK : ∃ k : ℕ, Nat.card K = 2 ^ k)
    (hK4 : ∃ s : Finset K, s.card = 4) : RBProp (unitriangular 3 K) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h0
    have hc := card_unitriangular (K := K) 3
    rw [h0, Subgroup.card_bot] at hc
    obtain ⟨s, hs⟩ := hK4
    have : Fintype K := Fintype.ofFinite K
    have h4 : 4 ≤ Nat.card K := by
      rw [Nat.card_eq_fintype_card, ← hs]
      exact Finset.card_le_univ s
    have h5 : 1 < Nat.card K ^ (3 * (3 - 1) / 2) := Nat.one_lt_pow (by norm_num) (by omega)
    omega
  · intro R hUR hRs
    rw [normalizer_unitriangular]
    exact sl3_le_upperTriangular_of_solvable hK4 hUR hRs
  · rintro ⟨y, hy, hy3⟩
    rw [normalizer_unitriangular] at hy
    obtain ⟨ω, hω⟩ := exists_units_orderThree hK hy hy3
    obtain ⟨E, hE, hE3, hEe, hEc⟩ := exists_elemAbelian_nine (torusSL3 K) (torusSL3_injective K)
      (N := upperTriangular 3 K) (torusSL3_mem_upperTriangular K) hω
    exact ⟨E, by rw [normalizer_unitriangular]; exact hE, hE3, hEe, hEc⟩

theorem rankTwoBorel_sl3 {Ω : Type} [Group Ω] {X S : Subgroup Ω} [Finite K] {e : ℕ}
    (hK : Nat.card K = 2 ^ e) (he : 2 ≤ e)
    (iso : ↥X ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 K)) (hS : IsSylowTwoOf S X) :
    S ≠ ⊥ ∧
      (∀ R : Subgroup Ω, S ≤ R → R ≤ X → Group.IsSolvable ↥R →
        R ≤ Subgroup.normalizer (S : Set Ω)) ∧
      ((∃ y ∈ Subgroup.normalizer (S : Set Ω) ⊓ X, orderOf y = 3) →
        ∃ E : Subgroup Ω, E ≤ Subgroup.normalizer (S : Set Ω) ⊓ X ∧ IsPGroup 3 E ∧
          (∀ x ∈ E, x ^ 3 = 1) ∧ Nat.card E = 9) := by
  have hF : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 2 ^ e := by rw [← Nat.card_eq_fintype_card]; exact hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcp : CharP K 2 := charP_of_card_eq_prime_pow hcard
  have h4 := exists_finset_card_four (four_le_card_of_two_pow hK he)
  exact rankTwoBorel_of_model (iso.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K).symm) hS
    (isSylowTwoOf_unitriangular (by norm_num)) (rbProp_unitriangular_three ⟨e, hK⟩ h4)

end Sl3

end SzN21

end CFSG.Quasithin
