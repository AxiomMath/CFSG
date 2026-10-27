module

public import CFSG.RankThree.PartTwo.Sec21.FF79KLemmaOP
public import CFSG.RankThree.Chevalley.SteinbergBIE7ThreeA1
public import CFSG.LieType.Chevalley.OrthogonalFixedOrbitMaps

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

section SL2

variable (K : Type) [Field K]

@[expose] def sl2Three : SL2 K := ⟨!![0, -1; 1, -1], by simp [Matrix.det_fin_two]⟩

@[expose] def sl2Trans : SL2 K := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩

theorem coe_sl2Three : (sl2Three K : Matrix (Fin 2) (Fin 2) K) = !![0, -1; 1, -1] := rfl

theorem coe_sl2Trans : (sl2Trans K : Matrix (Fin 2) (Fin 2) K) = !![1, 1; 0, 1] := rfl

theorem sl2Three_pow_three : sl2Three K ^ 3 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.coe_pow, coe_sl2Three, pow_succ, Matrix.mul_apply,
      Fin.sum_univ_two]

theorem sl2Three_ne_one : sl2Three K ≠ 1 := by
  intro h
  have := congrArg (fun A : SL2 K => (A : Matrix (Fin 2) (Fin 2) K) 0 0) h
  simp [coe_sl2Three] at this

theorem orderOf_sl2Three : orderOf (sl2Three K) = 3 :=
  orderOf_eq_prime (sl2Three_pow_three K) (sl2Three_ne_one K)

theorem sl2Three_mul_sl2Trans_ne : sl2Three K * sl2Trans K ≠ sl2Trans K * sl2Three K := by
  intro h
  have := congrArg (fun A : SL2 K => (A : Matrix (Fin 2) (Fin 2) K) 0 0) h
  simp [Matrix.SpecialLinearGroup.coe_mul, coe_sl2Three, coe_sl2Trans, Matrix.mul_apply,
    Fin.sum_univ_two] at this

theorem exists_orderOf_eq_two_sl2 : ∃ s : SL2 K, orderOf s = 2 := by
  by_cases hK : ringChar K = 2
  · haveI : CharP K 2 := ringChar.of_eq hK
    refine ⟨sl2Trans K, orderOf_eq_prime ?_ ?_⟩
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.SpecialLinearGroup.coe_pow, coe_sl2Trans, pow_succ, Matrix.mul_apply,
          Fin.sum_univ_two, CharTwo.add_self_eq_zero]
    · intro h
      have := congrArg (fun A : SL2 K => (A : Matrix (Fin 2) (Fin 2) K) 0 1) h
      simp [coe_sl2Trans] at this
  · refine ⟨-1, orderOf_eq_prime (by simp [pow_two]) ?_⟩
    intro h
    have := congrArg (fun A : SL2 K => (A : Matrix (Fin 2) (Fin 2) K) 0 0) h
    simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one] at this
    exact Ring.neg_one_ne_one_of_char_ne_two hK (by simpa using this)

end SL2

section Generic

variable {G : Type} [Group G] {K : Type} [Field K]

theorem not_threeRankLeOneInv_of_sl2 (ρ ρ' : SL2 K →* G) (hρ : Function.Injective ρ)
    (hρ' : Function.Injective ρ') (hc : ∀ a b, Commute (ρ a) (ρ' b)) (t : G)
    (ht : orderOf t = 2) (htρ : ∀ a, Commute t (ρ a)) (htρ' : ∀ a, Commute t (ρ' a)) :
    ¬ ThreeRankLeOneInv G := by
  intro hB
  have hv := hB t (ρ (sl2Three K)) (ρ' (sl2Three K)) ht (htρ _).eq (htρ' _).eq (hc _ _).eq
    (by rw [orderOf_injective ρ hρ, orderOf_sl2Three]) (by rw [orderOf_injective ρ' hρ',
      orderOf_sl2Three])
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hv
  apply sl2Three_mul_sl2Trans_ne K
  apply hρ'
  rw [map_mul, map_mul, ← hk, ← map_zpow]
  exact (hc _ _).eq

theorem not_threeRankLeOneInv_of_sl2_two (hK : ringChar K ≠ 2) (ρ ρ' : SL2 K →* G)
    (hρ : Function.Injective ρ) (hρ' : Function.Injective ρ') (hc : ∀ a b, Commute (ρ a) (ρ' b)) :
    ¬ ThreeRankLeOneInv G := by
  have hs : orderOf (-1 : SL2 K) = 2 := by
    refine orderOf_eq_prime (by simp [pow_two]) ?_
    intro h
    have := congrArg (fun A : SL2 K => (A : Matrix (Fin 2) (Fin 2) K) 0 0) h
    simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one] at this
    exact Ring.neg_one_ne_one_of_char_ne_two hK (by simpa using this)
  refine not_threeRankLeOneInv_of_sl2 ρ ρ' hρ hρ' hc (ρ (-1)) (by rw [orderOf_injective ρ hρ, hs])
    (fun a => ?_) (fun a => hc _ _)
  show ρ (-1) * ρ a = ρ a * ρ (-1)
  rw [← map_mul, ← map_mul, neg_one_mul, mul_neg_one]

theorem not_threeRankLeOneInv_of_sl2_three (ρ ρ' ρ'' : SL2 K →* G) (hρ : Function.Injective ρ)
    (hρ' : Function.Injective ρ') (hρ'' : Function.Injective ρ'')
    (hc : ∀ a b, Commute (ρ a) (ρ' b)) (hc' : ∀ a b, Commute (ρ'' a) (ρ b))
    (hc'' : ∀ a b, Commute (ρ'' a) (ρ' b)) : ¬ ThreeRankLeOneInv G := by
  obtain ⟨s, hs⟩ := exists_orderOf_eq_two_sl2 K
  exact not_threeRankLeOneInv_of_sl2 ρ ρ' hρ hρ' hc (ρ'' s) (by rw [orderOf_injective ρ'' hρ'', hs])
    (hc' s) (hc'' s)

end Generic

section Adjoint

set_option linter.unusedSectionVars false


variable {G : Type} [Group G] {τ : Tag} {K : Type} [Field K]

@[expose] noncomputable def rootSL2Through (ι : ↥(adjointGroup τ K) →* G)
    (β : Fin τ.rank → ℤ) : SL2 K →* G :=
  ι.comp ((rootSL2 τ K β).codRestrict (adjointGroup τ K)
    (CFSG.LieType.Chevalley.rootSL2_mem_adjointGroup β))

theorem rootSL2Through_injective {ι : ↥(adjointGroup τ K) →* G} (hι : Function.Injective ι)
    (β : Fin τ.rank → ℤ) : Function.Injective (rootSL2Through ι β) := by
  intro a b h
  apply CFSG.RankThree.Chevalley.rootSL2_injective_of_field (τ := τ) (K := K) β
  have := congrArg Subtype.val (hι h)
  simpa using this

theorem rootSL2Through_commute (ι : ↥(adjointGroup τ K) →* G) {β γ : Fin τ.rank → ℤ}
    (h : ∀ a b, Commute (rootSL2 τ K β a) (rootSL2 τ K γ b)) (a b : SL2 K) :
    Commute (rootSL2Through ι β a) (rootSL2Through ι γ b) := by
  refine Commute.map (f := ι) ?_
  exact Subtype.ext (h a b).eq

theorem not_threeRankLeOneInv_of_roots3 {ι : ↥(adjointGroup τ K) →* G}
    (hι : Function.Injective ι) {β₁ β₂ β₃ : Fin τ.rank → ℤ}
    (h12 : ∀ a b, Commute (rootSL2 τ K β₁ a) (rootSL2 τ K β₂ b))
    (h31 : ∀ a b, Commute (rootSL2 τ K β₃ a) (rootSL2 τ K β₁ b))
    (h32 : ∀ a b, Commute (rootSL2 τ K β₃ a) (rootSL2 τ K β₂ b)) : ¬ ThreeRankLeOneInv G :=
  not_threeRankLeOneInv_of_sl2_three _ _ _ (rootSL2Through_injective hι β₁)
    (rootSL2Through_injective hι β₂) (rootSL2Through_injective hι β₃)
    (rootSL2Through_commute ι h12) (rootSL2Through_commute ι h31) (rootSL2Through_commute ι h32)

theorem rootSL2_commute_of_lists {β γ : Fin τ.rank → ℤ} (hβ : List.ofFn β ∈ τ.artifactRoots)
    (hγ : List.ofFn γ ∈ τ.artifactRoots) (h0 : iform β γ = 0)
    (hp : List.ofFn (β + γ) ∉ τ.artifactRoots) (hm : List.ofFn (β - γ) ∉ τ.artifactRoots)
    (a b : SL2 K) : Commute (rootSL2 τ K β a) (rootSL2 τ K γ b) :=
  CFSG.RankThree.Chevalley.rootSL2_commute_of_orth (isRoot_iff_mem_artifactRoots.2 hβ)
    (isRoot_iff_mem_artifactRoots.2 hγ) h0 (fun h => hp (isRoot_iff_mem_artifactRoots.1 h))
    (fun h => hm (isRoot_iff_mem_artifactRoots.1 h)) a b

theorem not_threeRankLeOneInv_of_adjoint (hτ : τ ≠ .G2 ∨ ringChar K ≠ 2)
    {ι : ↥(adjointGroup τ K) →* G} (hι : Function.Injective ι) : ¬ ThreeRankLeOneInv G := by
  cases τ with
  | G2 =>
    have hK : ringChar K ≠ 2 := hτ.resolve_left (fun h => h rfl)
    exact not_threeRankLeOneInv_of_sl2_two hK _ _ (rootSL2Through_injective hι ![0, 1])
      (rootSL2Through_injective hι ![2, 3]) (rootSL2Through_commute ι
        (rootSL2_commute_of_lists (by decide +kernel) (by decide +kernel) (by decide +kernel)
          (by decide +kernel) (by decide +kernel)))
  | F4 =>
    exact not_threeRankLeOneInv_of_roots3 (β₁ := ![0, 0, 0, 1]) (β₂ := ![0, 1, 0, 0])
      (β₃ := ![2, 3, 4, 2]) hι
      (rootSL2_commute_of_lists (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) (by decide +kernel))
      (rootSL2_commute_of_lists (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) (by decide +kernel))
      (rootSL2_commute_of_lists (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) (by decide +kernel))
  | D4 =>
    exact not_threeRankLeOneInv_of_roots3 (β₁ := ![1, 0, 0, 0]) (β₂ := ![0, 1, 0, 0])
      (β₃ := ![0, 0, 0, 1]) hι
      (rootSL2_commute_of_lists (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) (by decide +kernel))
      (rootSL2_commute_of_lists (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) (by decide +kernel))
      (rootSL2_commute_of_lists (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) (by decide +kernel))
  | E6 =>
    exact not_threeRankLeOneInv_of_roots3 (β₁ := ![1, 0, 0, 0, 0, 0])
      (β₂ := ![0, 1, 0, 0, 0, 0]) (β₃ := ![0, 0, 0, 0, 0, 1]) hι
      (rootSL2_commute_of_lists (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) (by decide +kernel))
      (rootSL2_commute_of_lists (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) (by decide +kernel))
      (rootSL2_commute_of_lists (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) (by decide +kernel))
  | E7 =>
    exact not_threeRankLeOneInv_of_roots3 (β₁ := ![1, 0, 0, 0, 0, 0, 0])
      (β₂ := ![0, 1, 0, 0, 0, 0, 0]) (β₃ := ![0, 0, 0, 0, 0, 0, 1]) hι
      (rootSL2_commute_of_lists (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) (by decide +kernel))
      (rootSL2_commute_of_lists (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) (by decide +kernel))
      (rootSL2_commute_of_lists (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) (by decide +kernel))
  | E8 =>
    exact not_threeRankLeOneInv_of_roots3 (β₁ := ![1, 0, 0, 0, 0, 0, 0, 0])
      (β₂ := ![0, 1, 0, 0, 0, 0, 0, 0]) (β₃ := ![0, 0, 0, 0, 0, 0, 0, 1]) hι
      (rootSL2_commute_of_lists (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) (by decide +kernel))
      (rootSL2_commute_of_lists (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) (by decide +kernel))
      (rootSL2_commute_of_lists (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) (by decide +kernel))

theorem not_threeRankLeOneInv_of_mulEquiv_adjoint (hτ : τ ≠ .G2 ∨ ringChar K ≠ 2)
    (e : G ≃* ↥(adjointGroup τ K)) : ¬ ThreeRankLeOneInv G :=
  not_threeRankLeOneInv_of_adjoint hτ (ι := e.symm.toMonoidHom) e.symm.injective

end Adjoint

end CFSG.RankThree.PartTwo.Sec21.FF79
