module

public import CFSG.LocalAnalysis.StandardType.GGRootDetectSUField
public import CFSG.LieType.Universal.Unitary.Extras.RankOneLast
public import CFSG.LieType.Universal.Unitary.Extras
import all CFSG.LieType.Universal.Unitary.Roots

public section

namespace CFSG.StandardType

namespace RootDetectSU

open Matrix CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.Universal.Unitary.SUExtras CFSG.LieType.RootSystem

variable {F : Type*} [Field F] (σ : F ≃+* F) {n : ℕ}

@[expose] def pairDiag (b : Fin n) (x : F) : Fin n → F :=
  fun a => if a = b then x else if a = Fin.rev b then (σ x)⁻¹ else 1

variable {σ}

theorem pairDiag_self (b : Fin n) (x : F) : pairDiag σ b x b = x := by
  simp [pairDiag]

theorem pairDiag_rev {b : Fin n} (hb : b ≠ Fin.rev b) (x : F) :
    pairDiag σ b x (Fin.rev b) = (σ x)⁻¹ := by
  have h : Fin.rev b ≠ b := fun h => hb h.symm
  simp [pairDiag, h]

theorem pairDiag_of_ne {b a : Fin n} (h1 : a ≠ b) (h2 : a ≠ Fin.rev b) (x : F) :
    pairDiag σ b x a = 1 := by
  simp [pairDiag, h1, h2]

theorem pairDiag_unitary (hσ : ∀ c, σ (σ c) = c) {b : Fin n} (hb : b ≠ Fin.rev b) {x : F}
    (hx : x ≠ 0) (a : Fin n) : σ (pairDiag σ b x a) * pairDiag σ b x (Fin.rev a) = 1 := by
  have hσx : σ x ≠ 0 := (map_ne_zero σ).mpr hx
  by_cases h1 : a = b
  · subst h1
    rw [pairDiag_self, pairDiag_rev hb]
    exact mul_inv_cancel₀ hσx
  · by_cases h2 : a = Fin.rev b
    · subst h2
      rw [pairDiag_rev hb, Fin.rev_rev, pairDiag_self, map_inv₀, hσ]
      exact inv_mul_cancel₀ hx
    · have h3 : Fin.rev a ≠ b := fun h => h2 (by rw [← h, Fin.rev_rev])
      have h4 : Fin.rev a ≠ Fin.rev b := fun h => h1 (Fin.rev_injective h)
      rw [pairDiag_of_ne h1 h2, pairDiag_of_ne h3 h4, map_one, one_mul]

theorem prod_pairDiag {b : Fin n} (hb : b ≠ Fin.rev b) (x : F) :
    ∏ a, pairDiag σ b x a = x * (σ x)⁻¹ := by
  rw [Finset.prod_eq_mul b (Fin.rev b) hb (fun a _ ha => pairDiag_of_ne ha.1 ha.2 x)
    (fun h => absurd (Finset.mem_univ b) h) (fun h => absurd (Finset.mem_univ _) h),
    pairDiag_self, pairDiag_rev hb]

theorem unitary_mul {t r : Fin n → F} (ht : ∀ a, σ (t a) * t (Fin.rev a) = 1)
    (hr : ∀ a, σ (r a) * r (Fin.rev a) = 1) (a : Fin n) :
    σ ((t * r) a) * (t * r) (Fin.rev a) = 1 := by
  rw [Pi.mul_apply, Pi.mul_apply, map_mul]
  calc σ (t a) * σ (r a) * (t (Fin.rev a) * r (Fin.rev a)) =
      (σ (t a) * t (Fin.rev a)) * (σ (r a) * r (Fin.rev a)) := by ring
    _ = 1 := by rw [ht a, hr a, one_mul]

theorem diagonal_mul_diagonal_inv {t : Fin n → F} (ht : ∀ a, t a ≠ 0) :
    diagonal t * diagonal t⁻¹ = 1 := by
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext a
  rw [Pi.inv_apply]
  exact mul_inv_cancel₀ (ht a)

theorem diagonal_inv_mul_diagonal {t : Fin n → F} (ht : ∀ a, t a ≠ 0) :
    diagonal t⁻¹ * diagonal t = 1 := by
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext a
  rw [Pi.inv_apply]
  exact inv_mul_cancel₀ (ht a)

@[expose] noncomputable def diagGL (t : Fin n → F) (ht : ∀ a, t a ≠ 0) : GL (Fin n) F :=
  ⟨diagonal t, diagonal t⁻¹, diagonal_mul_diagonal_inv ht, diagonal_inv_mul_diagonal ht⟩

theorem coe_diagGL (t : Fin n → F) (ht : ∀ a, t a ≠ 0) :
    ((diagGL t ht : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = diagonal t :=
  rfl

theorem diagGL_mul {t r : Fin n → F} (ht : ∀ a, t a ≠ 0) (hr : ∀ a, r a ≠ 0) :
    diagGL t ht * diagGL r hr = diagGL (t * r) fun a => mul_ne_zero (ht a) (hr a) :=
  Units.ext (by rw [Units.val_mul, coe_diagGL, coe_diagGL, coe_diagGL, diagonal_mul_diagonal]; rfl)

theorem conjTr_diagonal_mul (t : Fin n → F) (ht : ∀ a, σ (t a) * t (Fin.rev a) = 1) :
    conjTr σ (diagonal t) * antidiag n * diagonal t = antidiag n := by
  ext a b
  rw [mul_diagonal, conjTr, diagonal_map (map_zero σ), diagonal_transpose, diagonal_mul]
  simp only [antidiag, of_apply]
  split_ifs with h
  · subst h
    rw [mul_one, ht a]
  · rw [mul_zero, zero_mul]

variable (σ) in
@[expose] noncomputable def diagSU (t : Fin n → F) (ht : ∀ a, σ (t a) * t (Fin.rev a) = 1)
    (hdet : ∏ a, t a = 1) : SU σ n :=
  ⟨diagGL t (ne_zero_of_unitary ht), by
    refine ⟨?_, ?_⟩
    · rw [coe_diagGL, det_diagonal, hdet]
    · rw [coe_diagGL]
      exact conjTr_diagonal_mul t ht⟩

theorem coe_diagSU (t : Fin n → F) (ht : ∀ a, σ (t a) * t (Fin.rev a) = 1)
    (hdet : ∏ a, t a = 1) :
    ((diagSU σ t ht hdet : SU σ n) : GL (Fin n) F) = diagGL t (ne_zero_of_unitary ht) :=
  rfl

theorem diagSU_mem_diagSubgroup (t : Fin n → F) (ht : ∀ a, σ (t a) * t (Fin.rev a) = 1)
    (hdet : ∏ a, t a = 1) : diagSU σ t ht hdet ∈ diagSubgroup σ n :=
  ⟨t, rfl⟩

theorem mem_normalizer_rootGroup_of_mem_diagSubgroup (hσ : ∀ c, σ (σ c) = c) {h : SU σ n}
    (hh : h ∈ diagSubgroup σ n) (γ : Fin (n / 2) → ℤ) :
    h ∈ Subgroup.normalizer (rootGroup σ hσ n γ : Set (SU σ n)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => diag_conj_mem hσ hh γ x hx, fun hx => ?_⟩
  have h1 := diag_conj_mem hσ ((diagSubgroup σ n).inv_mem hh) γ _ hx
  have e : h⁻¹ * (h * x * h⁻¹) * h⁻¹⁻¹ = x := by group
  rwa [e] at h1

theorem diagonal_mul_comm_of_mem_rootGroup (hσ : ∀ c, σ (σ c) = c) {γ : Fin (n / 2) → ℤ}
    {r : Fin n → F}
    (hr : ∀ a b, (weight n a - weight n b = toStd n γ ∨
      weight n a - weight n b = 2 • toStd n γ) → r a = r b)
    {x : SU σ n} (hx : x ∈ rootGroup σ hσ n γ) :
    diagonal r * ((x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      ((x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * diagonal r := by
  ext a b
  rw [diagonal_mul, mul_diagonal]
  by_cases hab : a = b
  · subst hab
    ring
  by_cases hz : ((x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) a b = 0
  · rw [hz, mul_zero, zero_mul]
  have hw := hasWt_of_mem_rootGroup hσ hx a b (by
    rw [Matrix.sub_apply, mat_apply, one_apply_ne hab, sub_zero]
    exact hz)
  rw [hr a b (mem_wt2.mp hw), mul_comm]

theorem mul_map_eq_one_of_mul_self [CharP F 2] {μ ν : F} (hμ : μ * μ = ν) (hν : ν * σ ν = 1) :
    μ * σ μ = 1 := by
  apply HypSixTypeA.eq_one_of_mul_self_eq_one
  calc μ * σ μ * (μ * σ μ) = μ * μ * σ (μ * μ) := by rw [map_mul]; ring
    _ = 1 := by rw [hμ, hν]

theorem exists_unitaryDiag_of_mem_roots [CharP F 2] (hσ : ∀ c, σ (σ c) = c)
    (hsq : ∀ x : F, ∃ y, y * y = x)
    (h90 : ∀ u : F, u * σ u = 1 → ∃ ρ : F, ρ ≠ 0 ∧ ρ / σ ρ = u) (hn : 4 ≤ n)
    {γ : Fin (n / 2) → ℤ} (hγ : γ ∈ roots (isFiniteType_cartan n) (divisible n)) {ν : F}
    (hν : ν * σ ν = 1) :
    ∃ r : Fin n → F, (∀ a, σ (r a) * r (Fin.rev a) = 1) ∧ ∏ a, r a = ν ∧
      ∀ a b, (weight n a - weight n b = toStd n γ ∨
        weight n a - weight n b = 2 • toStd n γ) → r a = r b := by
  have hne := toStd_ne_zero_of_mem_roots hγ
  obtain ⟨μ, hμ⟩ := hsq ν
  have hμσ : μ * σ μ = 1 := mul_map_eq_one_of_mul_self hμ hν
  have hμ0 : μ ≠ 0 := left_ne_zero_of_mul_eq_one hμσ
  rw [roots_eq] at hγ
  rcases hγ with ⟨i, j, hij, hi, hj, hji, h⟩ | ⟨i, hi, h⟩ | ⟨he, i, hi, h⟩
  ·
    obtain ⟨ρ, hρ0, hρ⟩ := h90 μ hμσ
    have hirj : i ≠ Fin.rev j := fun e => hji (by rw [e, Fin.rev_rev])
    have hri : ∀ a, (pairDiag σ i ρ * pairDiag σ j ρ) a = pairDiag σ i ρ a * pairDiag σ j ρ a :=
      fun _ => rfl
    refine ⟨pairDiag σ i ρ * pairDiag σ j ρ,
      unitary_mul (pairDiag_unitary hσ hi hρ0) (pairDiag_unitary hσ hj hρ0), ?_, ?_⟩
    · simp only [Pi.mul_apply]
      rw [Finset.prod_mul_distrib, prod_pairDiag hi, prod_pairDiag hj, ← div_eq_mul_inv, hρ, hμ]
    · intro a b hab
      rcases hab with hab | hab
      · rcases eq_of_weight_sub_eq_sub hij hi hj hji (hab.trans h) with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · rw [ha, hb, hri, hri, pairDiag_self, pairDiag_of_ne hij hirj,
            pairDiag_of_ne (Ne.symm hij) hji, pairDiag_self, mul_one, one_mul]
        · rw [ha, hb, hri, hri, pairDiag_of_ne (Ne.symm hirj)
            (fun e => hij (Fin.rev_injective e).symm), pairDiag_rev hj, pairDiag_rev hi,
            pairDiag_of_ne (Ne.symm hji) (fun e => hij (Fin.rev_injective e)), one_mul, mul_one]
      · rw [h] at hab hne
        exact absurd (eq_rev_of_weight_sub_eq_two_smul hab hne).2 (weight_ne_weight_sub hij hi hj hji)
  ·
    have hσμ : (σ μ)⁻¹ = μ := by rw [eq_inv_of_mul_eq_one_right hμσ, inv_inv]
    refine ⟨pairDiag σ i μ, pairDiag_unitary hσ hi hμ0, ?_, ?_⟩
    · rw [prod_pairDiag hi, hσμ, hμ]
    · intro a b hab
      rcases hab with hab | hab
      · obtain ⟨ha, hb⟩ := eq_of_weight_sub_eq_two_smul hi (hab.trans h)
        rw [ha, hb, pairDiag_self, pairDiag_rev hi, hσμ]
      · exfalso
        have h4 : weight n a - weight n b = 4 • weight n i := by
          rw [hab, h, smul_smul]
          norm_num
        have h0 := eq_zero_of_weight_sub_eq_nsmul h4 (by norm_num)
        rw [h0, smul_zero] at h
        exact hne h
  ·
    set k := midIdx n he with hkdef
    have hk : Fin.rev k = k := rev_midIdx he
    obtain ⟨c, hc⟩ := exists_lowIdx hi
    have h2 : 2 ≤ n / 2 := by omega
    obtain ⟨c', hc'⟩ : ∃ c' : Fin (n / 2), c' ≠ c := by
      by_cases h0 : c.val = 0
      · exact ⟨⟨1, by omega⟩, fun e => by rw [← e] at h0; exact absurd h0 (by norm_num)⟩
      · exact ⟨⟨0, by omega⟩, fun e => h0 (by rw [← e])⟩
    set l : Fin n := lowIdx c' with hldef
    have hl : l ≠ Fin.rev l := lowIdx_ne_rev c' c'
    have hcc : lowIdx (n := n) c' ≠ lowIdx c := fun e => by
      have e' := congrArg Fin.val e
      simp only [val_lowIdx] at e'
      exact hc' (Fin.ext e')
    have hli : l ≠ i := by
      rcases hc with hc | hc <;> rw [hc]
      exacts [hcc, lowIdx_ne_rev c' c]
    have hlri : l ≠ Fin.rev i := by
      rcases hc with hc | hc <;> rw [hc]
      exacts [lowIdx_ne_rev c' c, by rw [Fin.rev_rev]; exact hcc]
    obtain ⟨ρ, hρ0, hρ⟩ := h90 ν hν
    have hri : pairDiag σ l ρ i = 1 :=
      pairDiag_of_ne (Ne.symm hli) (fun e => hlri (by rw [e, Fin.rev_rev])) ρ
    have hrk : pairDiag σ l ρ k = 1 :=
      pairDiag_of_ne (fun e => hl (by rw [← e, hk]))
        (fun e => hl (by rw [e, Fin.rev_rev] at hk; exact hk)) ρ
    have hrri : pairDiag σ l ρ (Fin.rev i) = 1 :=
      pairDiag_of_ne (Ne.symm hlri) (fun e => hli (Fin.rev_injective e).symm) ρ
    have hr1 : ∀ a, (a = i ∨ a = k ∨ a = Fin.rev i) → pairDiag σ l ρ a = 1 := by
      intro a ha
      rcases ha with ha | ha | ha <;> rw [ha]
      exacts [hri, hrk, hrri]
    refine ⟨pairDiag σ l ρ, pairDiag_unitary hσ hl hρ0, by
      rw [prod_pairDiag hl, ← div_eq_mul_inv, hρ], ?_⟩
    intro a b hab
    rcases hab with hab | hab
    · rcases eq_of_weight_sub_eq_weight hi hk (hab.trans h) with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · rw [hr1 a (Or.inl ha), hr1 b (Or.inr (Or.inl hb))]
      · rw [hr1 a (Or.inr (Or.inl ha)), hr1 b (Or.inr (Or.inr hb))]
    · rw [h] at hab
      obtain ⟨ha, hb⟩ := eq_of_weight_sub_eq_two_smul hi hab
      rw [hr1 a (Or.inl ha), hr1 b (Or.inr (Or.inr hb))]

theorem map_single_one (φ : F ≃+* F) (i j : Fin n) :
    (single i j (1 : F)).map φ = single i j 1 := by
  rw [Matrix.map_single, map_one]

theorem exists_rootElt [CharP F 2] (hσ : ∀ c, σ (σ c) = c) {γ : Fin (n / 2) → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartan n) (divisible n)) :
    ∃ E : Matrix (Fin n) (Fin n) F, E ≠ 0 ∧ (∀ φ : F ≃+* F, E.map φ = E) ∧
      ∀ t : F, σ t = t → ∃ x ∈ rootGroup σ hσ n γ,
        ((x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 + t • E ∧ x * x = 1 := by
  rw [roots_eq] at hγ
  rcases hγ with ⟨i, j, hij, hi, hj, hji, h⟩ | ⟨i, hi, h⟩ | ⟨he, i, hi, h⟩
  · have hirj : i ≠ Fin.rev j := fun e => hji (by rw [e, Fin.rev_rev])
    refine ⟨single i j 1 - single (Fin.rev j) (Fin.rev i) 1, fun h0 => ?_, fun φ => ?_,
      fun t ht => ?_⟩
    · have e := congrFun (congrFun h0 i) j
      simp [Matrix.sub_apply, (Ne.symm hirj : Fin.rev j ≠ i)] at e
    · rw [Matrix.map_sub _ (map_sub φ), map_single_one, map_single_one]
    · refine ⟨rootHom σ hσ hij hi hj (Multiplicative.ofAdd t),
        rootHom_mem hσ hij hi hj hji h.symm _, ?_, ?_⟩
      · rw [coe_rootHom, toAdd_ofAdd, rootMatrix, ht, smul_sub, smul_single, smul_single,
          smul_eq_mul, mul_one]
        abel
      · rw [← map_mul, ← ofAdd_add, CharTwo.add_self_eq_zero, ofAdd_zero, map_one]
  · refine ⟨single i (Fin.rev i) 1, fun h0 => ?_, fun φ => map_single_one φ _ _, fun t ht => ?_⟩
    · have e := congrFun (congrFun h0 i) (Fin.rev i)
      simp at e
    · have htz : t ∈ traceZero σ := by rw [mem_traceZero, ht, CharTwo.add_self_eq_zero]
      refine ⟨longRootHom σ hi (Multiplicative.ofAdd ⟨t, htz⟩),
        longRootHom_mem hσ hi h.symm _, ?_, ?_⟩
      · rw [coe_longRootHom, toAdd_ofAdd, longRootMatrix, smul_single, smul_eq_mul, mul_one]
      · rw [← map_mul, ← ofAdd_add]
        have e : (⟨t, htz⟩ : traceZero σ) + ⟨t, htz⟩ = 0 :=
          Subtype.ext (CharTwo.add_self_eq_zero t)
        rw [e, ofAdd_zero, map_one]
  · set k := midIdx n he
    have hk : Fin.rev k = k := rev_midIdx he
    have hik : i ≠ k := fun e => hi (by rw [e, hk])
    refine ⟨single i (Fin.rev i) 1, fun h0 => ?_, fun φ => map_single_one φ _ _, fun t ht => ?_⟩
    · have e := congrFun (congrFun h0 i) (Fin.rev i)
      simp at e
    · have htz : t ∈ traceZero σ := by rw [mem_traceZero, ht, CharTwo.add_self_eq_zero]
      refine ⟨longRootHom σ hi (Multiplicative.ofAdd ⟨t, htz⟩),
        heisenberg_le hσ hi hik hk h.symm ⟨0, t, ?_, ?_⟩, ?_, ?_⟩
      · rw [map_zero, zero_mul, add_zero]
        exact htz
      · rw [coe_longRootHom, toAdd_ofAdd]
        simp [longRootMatrix, heisenbergMatrix]
      · rw [coe_longRootHom, toAdd_ofAdd, longRootMatrix, smul_single, smul_eq_mul, mul_one]
      · rw [← map_mul, ← ofAdd_add]
        have e : (⟨t, htz⟩ : traceZero σ) + ⟨t, htz⟩ = 0 :=
          Subtype.ext (CharTwo.add_self_eq_zero t)
        rw [e, ofAdd_zero, map_one]

end RootDetectSU

end CFSG.StandardType
