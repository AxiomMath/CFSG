module

public import CFSG.RankThree.PartOne.KC.UnitaryCoordBlocks
public import CFSG.RankThree.PartOne.KC.UnitaryLiftBlocks

public section

namespace CFSG.RankThree.PartOne.KCUnitaryCoord

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.KCUnitaryLift

variable {ℓ f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K)

section Exact

variable {n : ℕ}

theorem inv_mul_map_mul {U : Type*} [Group U] (c : MulAut U) {a b : U}
    (hab : Commute (a⁻¹ * c a) b⁻¹) : (a * b)⁻¹ * c (a * b) = (a⁻¹ * c a) * (b⁻¹ * c b) := by
  calc (a * b)⁻¹ * c (a * b) = b⁻¹ * (a⁻¹ * c a) * c b := by
        rw [_root_.mul_inv_rev, map_mul]
        group
    _ = (a⁻¹ * c a) * b⁻¹ * c b := by rw [← hab.eq]
    _ = (a⁻¹ * c a) * (b⁻¹ * c b) := by group

theorem idActU_eq_of_commute (hn : 3 ≤ n) (hq : 3 < ℓ ^ f)
    {F : Subgroup (primeFormUnitary h (idGram K n))} (hF : Group.IsPerfect F)
    {α : MulAut (primeFormP h (idGram K n))}
    (hα : ∀ A ∈ F, α * primeFormConjHom h (idGram K n) A =
      primeFormConjHom h (idGram K n) A * α) :
    ∀ A ∈ F, idActU h n hn hq α A = A := by
  set c := idActU h n hn hq α with hc
  have hz : ∀ A ∈ F, primeFormConjHom h (idGram K n) (A⁻¹ * c A) = 1 := by
    intro A hA
    have h1 : α * primeFormConjHom h (idGram K n) A * α⁻¹ =
        primeFormConjHom h (idGram K n) (c A) := conj_primeFormConjHom hn hq α A
    rw [hα A hA, mul_inv_cancel_right] at h1
    rw [map_mul, map_inv, ← h1, inv_mul_cancel]
  let ψ : F →* (primeFormConjHom h (idGram K n)).ker :=
    { toFun := fun A => ⟨(A : primeFormUnitary h (idGram K n))⁻¹ * c A,
        MonoidHom.mem_ker.mpr (hz A A.2)⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun A B => Subtype.ext
        (inv_mul_map_mul c (commute_of_mem_ker hn hq (hz A A.2) _)) }
  have hψ := eq_one_of_perfect_of_comm hF
    (fun a b : (primeFormConjHom h (idGram K n)).ker =>
      Subtype.ext (commute_of_mem_ker hn hq (MonoidHom.mem_ker.mp a.2) (b : _)).eq) ψ
  intro A hA
  have h1 := congrArg Subtype.val (hψ ⟨A, hA⟩)
  change A⁻¹ * c A = 1 at h1
  exact (inv_mul_eq_one.mp h1).symm

theorem matrix_eq_of_idActU_eq (hn : 3 ≤ n) (hq : 3 < ℓ ^ f) {M A : primeFormUnitary h (idGram K n)}
    {τ : K ≃+* K}
    (hA : idActU h n hn hq (primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := n))
      ⟨M, τ⟩) A = A) :
    ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map τ =
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  rw [idActU_primeFormPsi, idUAction_mk] at hA
  have h1 : M * primeFormFieldU h (isPrimeFormGram_idGram (K := K) (n := n)) τ A = A * M := by
    rw [← mul_inv_eq_iff_eq_mul]
    exact hA
  have h2 := congrArg (fun x : primeFormUnitary h (idGram K n) =>
    ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) h1
  exact h2

theorem entry_eq_of_diagonal {M : Matrix (Fin n) (Fin n) K} {τ : K ≃+* K} {d : Fin n → K}
    (hM : M * (diagonal d).map τ = diagonal d * M) (k l : Fin n) :
    M k l * τ (d l) = d k * M k l := by
  rw [Matrix.diagonal_map (map_zero τ)] at hM
  have := congrFun (congrFun hM k) l
  simpa [Matrix.mul_diagonal, Matrix.diagonal_mul] using this

end Exact

section Field

theorem eq_one_of_fixes_norm_one (τ : K ≃+* K)
    (hτ : ∀ v : Kˣ, h.norm (v : K) = 1 → τ (v : K) = v) : τ = RingEquiv.refl K := by
  by_contra hne
  have hfin := h.finite
  obtain ⟨σ, -, -, -, hcardAut, hsub⟩ := finite_field_automorphism_fixed_field_cardinality h.prime
    (n := 2 * f) (by have := h.one_le; omega) (by rw [h.card])
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by
    rw [hcardAut]
    have := h.one_le
    omega)
  obtain ⟨-, S, hS, hcard⟩ := hsub (Subgroup.zpowers τ)
  have h2 : 2 ≤ Nat.card (Subgroup.zpowers τ) := by
    have hne' : Subgroup.zpowers τ ≠ ⊥ := by
      rw [Ne, Subgroup.zpowers_eq_bot]
      exact hne
    exact (Subgroup.one_lt_card_iff_ne_bot _).mpr hne'
  have hfix : ∀ v : K, τ v = v → ∀ k : ℤ, (τ ^ k) v = v := by
    intro v hv k
    induction k using Int.induction_on with
    | zero => rfl
    | succ k ih =>
      rw [_root_.zpow_add_one, RingAut.mul_apply, hv, ih]
    | pred k ih =>
      rw [_root_.zpow_sub_one, RingAut.mul_apply]
      have : τ⁻¹ v = v := by
        have h3 : τ⁻¹ (τ v) = v := by
          rw [← RingAut.mul_apply, inv_mul_cancel]
          rfl
        rwa [hv] at h3
      rw [this, ih]
  have hinj : Nat.card (Units.map h.normHom).ker ≤ Nat.card S := by
    refine Nat.card_le_card_of_injective
      (fun u => ⟨(u : Kˣ), ?_⟩) ?_
    · rw [← SetLike.mem_coe, hS]
      intro τ' hτ'
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hτ'
      exact hfix _ (hτ _ ((h.mem_ker_normUnits).mp u.2)) k
    · intro a b hab
      exact Subtype.ext (Units.ext (congrArg Subtype.val hab))
  rw [(h.card_ker_normUnits_and_surjective).1, hcard] at hinj
  have h3 : 2 * f / Nat.card (Subgroup.zpowers τ) ≤ f := by
    calc 2 * f / Nat.card (Subgroup.zpowers τ) ≤ 2 * f / 2 :=
          Nat.div_le_div_left h2 (by norm_num)
      _ = f := by omega
  have h4 : ℓ ^ (2 * f / Nat.card (Subgroup.zpowers τ)) ≤ ℓ ^ f :=
    Nat.pow_le_pow_right h.prime.pos h3
  omega

end Field

section Matrix5

theorem exists_norm_one_ne_one (hq : 4 ≤ ℓ ^ f) : ∃ v : Kˣ, h.norm (v : K) = 1 ∧ v ≠ 1 := by
  obtain ⟨ζ, h1, h2⟩ := exists_norm_one_sq_ne_one h (by omega)
  have hζ : ζ ≠ 0 := by
    rintro rfl
    simp at h1
  refine ⟨Units.mk0 ζ hζ, ?_, ?_⟩
  · change ζ * h.bar ζ = 1
    rw [mul_comm]
    exact h1
  · intro h3
    apply h2
    have : ζ = 1 := congrArg Units.val h3
    rw [this, one_pow]

theorem matrix_core (hq : 4 ≤ ℓ ^ f) {Mm Minv : Matrix (Fin 5) (Fin 5) K} (hMinv : Mm * Minv = 1)
    {τ : K ≃+* K}
    (hD : ∀ i j : Fin 5, i ≠ j → ∀ v : Kˣ, h.norm (v : K) = 1 → ∀ k l : Fin 5,
      Mm k l * τ (if l = i then (v : K) else if l = j then ((v⁻¹ : Kˣ) : K) else 1) =
        (if k = i then (v : K) else if k = j then ((v⁻¹ : Kˣ) : K) else 1) * Mm k l)
    (hS : ∀ i j : Fin 5, i ≠ j → ∃ S : Matrix (Fin 5) (Fin 5) K, S i j = 1 ∧
      Mm * S.map τ = S * Mm) :
    τ = RingEquiv.refl K ∧ ∃ c : K, c ≠ 0 ∧ Mm = c • (1 : Matrix (Fin 5) (Fin 5) K) := by
  obtain ⟨v₀, hv₀, hv₀1⟩ := exists_norm_one_ne_one h hq
  have hv₀' : (v₀ : K) ≠ 1 := fun h' => hv₀1 (Units.ext h')
  have hoff : ∀ k l : Fin 5, k ≠ l → Mm k l = 0 := by
    intro k l hkl
    have hex : ∀ k l : Fin 5, ∃ m : Fin 5, m ≠ k ∧ m ≠ l := by decide
    obtain ⟨m, hmk, hml⟩ := hex k l
    have h1 := hD k m hmk.symm v₀ hv₀ k l
    have hlk : l ≠ k := Ne.symm hkl
    have hlm : l ≠ m := Ne.symm hml
    simp [hlk, hlm] at h1
    have h2 : (1 - (v₀ : K)) * Mm k l = 0 := by linear_combination h1
    exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hv₀'.symm)
  have hdiag_ne : ∀ k, Mm k k ≠ 0 := by
    intro k
    have h2 := congrFun (congrFun hMinv k) k
    rw [Matrix.mul_apply, Finset.sum_eq_single k, Matrix.one_apply_eq] at h2
    · exact left_ne_zero_of_mul_eq_one h2
    · intro m _ hm
      rw [hoff k m (Ne.symm hm), zero_mul]
    · simp
  have hτ : ∀ v : Kˣ, h.norm (v : K) = 1 → τ (v : K) = v := by
    intro v hv
    have h1 := hD 0 1 (by decide) v hv 0 0
    simp at h1
    exact mul_left_cancel₀ (hdiag_ne 0) (by rw [h1, mul_comm])
  have hτ1 : τ = RingEquiv.refl K := eq_one_of_fixes_norm_one h τ hτ
  refine ⟨hτ1, Mm 0 0, hdiag_ne 0, ?_⟩
  subst hτ1
  have hconst : ∀ i j : Fin 5, i ≠ j → Mm i i = Mm j j := by
    intro i j hij
    obtain ⟨S, hS1, hSeq⟩ := hS i j hij
    have h1 := congrFun (congrFun hSeq i) j
    have hmap : S.map (RingEquiv.refl K) = S := Matrix.ext fun _ _ => rfl
    rw [hmap, Matrix.mul_apply, Matrix.mul_apply, Finset.sum_eq_single i,
      Finset.sum_eq_single j, hS1] at h1
    · simpa using h1
    · intro m _ hm
      rw [hoff m j hm, mul_zero]
    · simp
    · intro m _ hm
      rw [hoff i m (Ne.symm hm), zero_mul]
    · simp
  ext k l
  by_cases hkl : k = l
  · subst hkl
    by_cases hk : k = 0
    · subst hk
      simp
    · simpa using hconst k 0 hk
  · simp [hoff k l hkl, Matrix.one_apply_ne hkl]

end Matrix5

section Final

theorem eq_one_of_commute_coordSU (hq : 4 ≤ ℓ ^ f) {α : MulAut (primeFormP h (idGram K 5))}
    (hα : ∀ (i j : Fin 5) (hij : i ≠ j), ∀ A ∈ coordSU h hij,
      α * primeFormConjHom h (idGram K 5) A = primeFormConjHom h (idGram K 5) A * α) :
    α = 1 := by
  have hn : 3 ≤ 5 := by norm_num
  have hq3 : 3 < ℓ ^ f := by omega
  obtain ⟨⟨M, τ⟩, rfl⟩ := surjective_primeFormPsi (h := h) (n := 5) hn hq3 α
  have hmat : ∀ (i j : Fin 5) (hij : i ≠ j), ∀ A ∈ coordSU h hij,
      ((M : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *
          ((A : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K).map τ =
        ((A : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *
          ((M : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) :=
    fun i j hij A hA => matrix_eq_of_idActU_eq h hn hq3
      (idActU_eq_of_commute h hn hq3 (isPerfect_coordSU h hq hij) (hα i j hij) A hA)
  have hMinv : ((M : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *
      (((M⁻¹ : primeFormUnitary h (idGram K 5)) : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
        1 := by simp
  obtain ⟨hτ, c, hc0, hMc⟩ := matrix_core h hq hMinv
    (fun i j hij v hv k l => by
      have h1 := hmat i j hij _ (diagonalCoord_mem_coordSU h hij v hv)
      rw [coe_diagonalCoord] at h1
      exact entry_eq_of_diagonal h1 k l)
    (fun i j hij => ⟨((swapCoord h hij : primeFormUnitary h (idGram K 5)) : GL (Fin 5) K),
      swapCoord_apply h hij, hmat i j hij _ (swapCoord_mem_coordSU h hij)⟩)
  have hc1 : h.norm c = 1 := by
    have hM := M.2
    rw [mem_primeFormUnitary] at hM
    simp only [Units.val_one, Matrix.mul_one] at hM
    rw [hMc] at hM
    have h1 := congrFun (congrFun hM 0) 0
    simp [Matrix.mul_apply, Matrix.smul_apply, Matrix.transpose_apply, Matrix.one_apply,
      apply_ite, Finset.sum_ite_eq'] at h1
    change c * h.bar c = 1
    rw [mul_comm]
    exact h1
  have hker : primeFormConjHom h (idGram K 5) M = 1 := by
    refine (primeFormConjHom_eq_one_iff hn hq3 M).mpr
      ⟨Units.mk0 c hc0, (pow_succ_eq_one_iff_norm h (Units.mk0 c hc0)).mpr hc1, ?_⟩
    apply Units.ext
    rw [hMc]
    simp [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  subst hτ
  rw [primeFormPsi_apply, hker, one_mul]
  exact map_one _

end Final

end CFSG.RankThree.PartOne.KCUnitaryCoord
