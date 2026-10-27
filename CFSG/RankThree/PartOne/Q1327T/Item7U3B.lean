module

public import CFSG.RankThree.PartOne.Q1327T.Item7U3A

public section

namespace CFSG.RankThree.PartOne.Q1327T

open Matrix CFSG CFSG.RankThree.SubgroupLists CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU
  CFSG.Assembly.LowTwoRank

section Swap

variable {K : Type} [Field K]

@[expose] def sw12 : Matrix (Fin 3) (Fin 3) K := !![1, 0, 0; 0, 0, 1; 0, 1, 0]

@[expose] def sw02 : Matrix (Fin 3) (Fin 3) K := !![0, 0, 1; 0, 1, 0; 1, 0, 0]

theorem sw12_mul_self : (sw12 : Matrix (Fin 3) (Fin 3) K) * sw12 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sw12, Matrix.mul_apply, Fin.sum_univ_three]

theorem sw02_mul_self : (sw02 : Matrix (Fin 3) (Fin 3) K) * sw02 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sw02, Matrix.mul_apply, Fin.sum_univ_three]

@[expose] def swGL12 : GL (Fin 3) K := ⟨sw12, sw12, sw12_mul_self, sw12_mul_self⟩

@[expose] def swGL02 : GL (Fin 3) K := ⟨sw02, sw02, sw02_mul_self, sw02_mul_self⟩

theorem swGL12_inv : (swGL12 : GL (Fin 3) K)⁻¹ = swGL12 := Units.ext rfl

theorem swGL02_inv : (swGL02 : GL (Fin 3) K)⁻¹ = swGL02 := Units.ext rfl

theorem swGL12_conj (d : Fin 3 → Kˣ) :
    (swGL12 : GL (Fin 3) K)⁻¹ * diagU d * swGL12 = diagU ![d 0, d 2, d 1] := by
  rw [swGL12_inv]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, diagU_val, diagU_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [swGL12, sw12, Matrix.mul_apply, Fin.sum_univ_three, Matrix.vecMul_diagonal]

theorem swGL02_conj (d : Fin 3 → Kˣ) :
    (swGL02 : GL (Fin 3) K)⁻¹ * diagU d * swGL02 = diagU ![d 2, d 1, d 0] := by
  rw [swGL02_inv]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, diagU_val, diagU_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [swGL02, sw02, Matrix.mul_apply, Fin.sum_univ_three, Matrix.vecMul_diagonal]

variable {f : ℕ}

theorem swGL12_mem [CharP K 2] : (swGL12 : GL (Fin 3) K) ∈ StatedSU 3 (2 ^ f) K := by
  refine Subgroup.subset_closure ⟨?_, ?_⟩
  · change (sw12 : Matrix (Fin 3) (Fin 3) K).det = 1
    have h := CharTwo.neg_eq (1 : K)
    rw [Matrix.det_fin_three]
    simp [sw12, h]
  · change ((sw12 : Matrix (Fin 3) (Fin 3) K).map (· ^ 2 ^ f))ᵀ * sw12 = 1
    have hq0 : (0 : K) ^ 2 ^ f = 0 := zero_pow (by positivity)
    have h1 : (sw12 : Matrix (Fin 3) (Fin 3) K).map (· ^ 2 ^ f) = sw12 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [sw12, hq0]
    have h2 : (sw12 : Matrix (Fin 3) (Fin 3) K)ᵀ = sw12 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [sw12]
    rw [h1, h2, sw12_mul_self]

theorem swGL02_mem [CharP K 2] : (swGL02 : GL (Fin 3) K) ∈ StatedSU 3 (2 ^ f) K := by
  refine Subgroup.subset_closure ⟨?_, ?_⟩
  · change (sw02 : Matrix (Fin 3) (Fin 3) K).det = 1
    have h := CharTwo.neg_eq (1 : K)
    rw [Matrix.det_fin_three]
    simp [sw02, h]
  · change ((sw02 : Matrix (Fin 3) (Fin 3) K).map (· ^ 2 ^ f))ᵀ * sw02 = 1
    have hq0 : (0 : K) ^ 2 ^ f = 0 := zero_pow (by positivity)
    have h1 : (sw02 : Matrix (Fin 3) (Fin 3) K).map (· ^ 2 ^ f) = sw02 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [sw02, hq0]
    have h2 : (sw02 : Matrix (Fin 3) (Fin 3) K)ᵀ = sw02 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [sw02]
    rw [h1, h2, sw02_mul_self]

end Swap

section Conj

variable {Q : Type} [Group Q] {K : Type} [Field K] [Finite K] {p f : ℕ}

theorem u3_component_card_conj (hp : p.Prime) (hp5 : 5 ≤ p) (hf : 2 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) (π : StatedSU 3 (2 ^ f) K →* Q) (hπ : Function.Surjective π)
    (hscal : ∀ g, π g = 1 ↔ (g : GL (Fin 3) K) ∈ StatedScalars (Fin 3) K)
    {ct : StatedSU 3 (2 ^ f) K} (hc : ct ^ p = 1) (s : StatedSU 3 (2 ^ f) K) {d : Fin 3 → Kˣ}
    (hd : ((s⁻¹ * ct * s : StatedSU 3 (2 ^ f) K) : GL (Fin 3) K) = diagU d) (h01 : d 0 = d 1)
    (h02 : d 0 ≠ d 2) {Kb : Subgroup Q} (hKbc : Kb ≤ Subgroup.centralizer ({π ct} : Set Q))
    (hKbN : (Kb.subgroupOf (Subgroup.centralizer ({π ct} : Set Q))).Normal)
    (hKbp : ⁅Kb, Kb⁆ = Kb) (hKb1 : Kb ≠ ⊥) :
    Nat.card Kb = 2 ^ f * ((2 ^ f) ^ 2 - 1) := by
  let π' : StatedSU 3 (2 ^ f) K →* Q := π.comp (MulAut.conj s).toMonoidHom
  have hπ' : Function.Surjective π' := hπ.comp (MulAut.conj s).surjective
  have hπ'ct : π' (s⁻¹ * ct * s) = π ct := by
    change π (s * (s⁻¹ * ct * s) * s⁻¹) = π ct
    congr 1
    group
  have hscal' : ∀ g, π' g = 1 ↔ (g : GL (Fin 3) K) ∈ StatedScalars (Fin 3) K := by
    intro g
    change π (s * g * s⁻¹) = 1 ↔ _
    rw [hscal]
    constructor
    · intro h
      have := (StatedScalars.normal (Fin 3) K).conj_mem _ h (s : GL (Fin 3) K)⁻¹
      simpa [mul_assoc] using this
    · intro h
      have := (StatedScalars.normal (Fin 3) K).conj_mem _ h (s : GL (Fin 3) K)
      simpa [mul_assoc] using this
  have hc' : (s⁻¹ * ct * s) ^ p = 1 := by
    have h := conj_pow (a := s⁻¹) (b := ct) (i := p)
    rw [inv_inv] at h
    rw [h, hc]
    group
  have := u3_component_card (ct := s⁻¹ * ct * s) hp hp5 hf hK π' hπ' hscal' hc' hd h01 h02
    (Kb := Kb) (by rw [hπ'ct]; exact hKbc) (by rw [hπ'ct]; exact hKbN) hKbp hKb1
  exact this

end Conj

section Distinct

variable {K : Type} [Field K]

theorem offdiag_zero_of_commute_diagU {d : Fin 3 → Kˣ} (hd : Function.Injective d)
    {g : GL (Fin 3) K} (hg : g * diagU d = diagU d * g) {i j : Fin 3} (hij : i ≠ j) :
    (g : Matrix (Fin 3) (Fin 3) K) i j = 0 := by
  have hm : (g : Matrix (Fin 3) (Fin 3) K) * Matrix.diagonal (fun i => (d i : K)) =
      Matrix.diagonal (fun i => (d i : K)) * (g : Matrix (Fin 3) (Fin 3) K) := by
    have := congrArg (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K)) hg
    simpa [diagU_val] using this
  have key := congrFun (congrFun hm i) j
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at key
  have hne : (d j : K) - d i ≠ 0 := sub_ne_zero.2 fun h => hij (hd (Units.ext h)).symm
  have h : (g : Matrix (Fin 3) (Fin 3) K) i j * ((d j : K) - d i) = 0 := by
    linear_combination key
  exact (mul_eq_zero.1 h).resolve_right hne

theorem commute_of_offdiag_zero' {g h : GL (Fin 3) K}
    (hg : ∀ i j, i ≠ j → (g : Matrix (Fin 3) (Fin 3) K) i j = 0)
    (hh : ∀ i j, i ≠ j → (h : Matrix (Fin 3) (Fin 3) K) i j = 0) : g * h = h * g := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;>
    simp [hg 0 1, hg 0 2, hg 1 0, hg 1 2, hg 2 0, hg 2 1, hh 0 1, hh 0 2, hh 1 0, hh 1 2,
      hh 2 0, hh 2 1] <;> ring

end Distinct

section Diag

variable {Q : Type} [Group Q] {K : Type} [Field K] [Finite K] {p f : ℕ}

omit [Finite K] in
theorem ker_facts (hp5 : 5 ≤ p) (hK : Nat.card K = (2 ^ f) ^ 2)
    (π : StatedSU 3 (2 ^ f) K →* Q)
    (hscal : ∀ g, π g = 1 ↔ (g : GL (Fin 3) K) ∈ StatedScalars (Fin 3) K) :
    π.ker ≤ Subgroup.center (StatedSU 3 (2 ^ f) K) ∧ ¬ p ∣ Nat.card π.ker := by
  have hkerN : π.ker = (StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 (2 ^ f) K) := by
    ext x
    rw [MonoidHom.mem_ker, hscal, Subgroup.mem_subgroupOf]
  refine ⟨?_, ?_⟩
  · intro x hx
    rw [hkerN] at hx
    obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hc]
    exact (Subgroup.mem_center_iff.1 (by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨c, rfl⟩) (y : GL (Fin 3) K))
  · rw [hkerN, (CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hK
      (by norm_num : 1 ≤ 3)).2.2]
    intro hd
    have := Nat.le_of_dvd (by norm_num) (hd.trans (Nat.gcd_dvd_left 3 _))
    omega

theorem u3_card_of_diag (hp : p.Prime) (hp5 : 5 ≤ p) (hf : 2 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) (π : StatedSU 3 (2 ^ f) K →* Q) (hπ : Function.Surjective π)
    (hscal : ∀ g, π g = 1 ↔ (g : GL (Fin 3) K) ∈ StatedScalars (Fin 3) K)
    {ct : StatedSU 3 (2 ^ f) K} (hc : ct ^ p = 1) (hct1 : π ct ≠ 1) {d : Fin 3 → Kˣ}
    (hd : (ct : GL (Fin 3) K) = diagU d) {Kb : Subgroup Q}
    (hKbc : Kb ≤ Subgroup.centralizer ({π ct} : Set Q))
    (hKbN : (Kb.subgroupOf (Subgroup.centralizer ({π ct} : Set Q))).Normal)
    (hKbp : ⁅Kb, Kb⁆ = Kb) (hKb1 : Kb ≠ ⊥) :
    Nat.card Kb = 2 ^ f * ((2 ^ f) ^ 2 - 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : CharP K 2 := by
    have : Fintype K := Fintype.ofFinite K
    exact CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow Nat.prime_two
      (by rw [hK, ← pow_mul])
  by_cases h01 : d 0 = d 1
  · by_cases h02 : d 0 = d 2
    · exfalso
      apply hct1
      rw [hscal]
      refine ⟨d 0, ?_⟩
      have hd' : d = fun _ => d 0 := funext fun i => by
        fin_cases i
        · rfl
        · exact h01.symm
        · exact h02.symm
      apply Units.ext
      rw [hd, hd']
      simp [diagU_val, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
    · refine u3_component_card_conj hp hp5 hf hK π hπ hscal hc 1 (d := d) ?_ h01 h02 hKbc hKbN
        hKbp hKb1
      simpa using hd
  · by_cases h02 : d 0 = d 2
    · refine u3_component_card_conj hp hp5 hf hK π hπ hscal hc
        (⟨swGL12, swGL12_mem⟩ : StatedSU 3 (2 ^ f) K) (d := ![d 0, d 2, d 1]) ?_
        (by simpa using h02) (by simpa using h01) hKbc hKbN hKbp hKb1
      change (swGL12 : GL (Fin 3) K)⁻¹ * (ct : GL (Fin 3) K) * swGL12 = _
      rw [hd, swGL12_conj]
    · by_cases h12 : d 1 = d 2
      · refine u3_component_card_conj hp hp5 hf hK π hπ hscal hc
          (⟨swGL02, swGL02_mem⟩ : StatedSU 3 (2 ^ f) K) (d := ![d 2, d 1, d 0]) ?_
          (by simpa using h12.symm) (by
            simp only [Matrix.cons_val_zero, Matrix.cons_val]
            intro h
            exact h01 (h.symm.trans h12.symm))
          hKbc hKbN hKbp hKb1
        change (swGL02 : GL (Fin 3) K)⁻¹ * (ct : GL (Fin 3) K) * swGL02 = _
        rw [hd, swGL02_conj]
      · exfalso
        have hinj : Function.Injective d := by
          intro i j hij
          fin_cases i <;> fin_cases j <;> first | rfl | (exfalso; simp_all)
        obtain ⟨hker, hpk⟩ := ker_facts hp5 hK π hscal
        refine false_of_commutative_centralizer hp π hπ hker hpk hc hKbc hKbp hKb1 ?_
        intro a ha b hb
        have hoff : ∀ x : StatedSU 3 (2 ^ f) K, x ∈ Subgroup.centralizer ({ct} : Set _) →
            ∀ i j : Fin 3, i ≠ j → ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j = 0 := by
          intro x hx i j hij
          have h1 : x * ct = ct * x := Subgroup.mem_centralizer_singleton_iff.1 hx
          have h2 := congrArg (fun y : StatedSU 3 (2 ^ f) K => (y : GL (Fin 3) K)) h1
          simp only [Subgroup.coe_mul, hd] at h2
          exact offdiag_zero_of_commute_diagU hinj h2 hij
        apply Subtype.ext
        rw [Subgroup.coe_mul, Subgroup.coe_mul]
        exact commute_of_offdiag_zero' (hoff a ha) (hoff b hb)

end Diag

end CFSG.RankThree.PartOne.Q1327T
