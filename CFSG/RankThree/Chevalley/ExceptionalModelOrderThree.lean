module

public import CFSG.RankThree.Chevalley.EvenRealThreeCentralizingInvolution

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Assembly.LowTwoRank

@[expose] def orderThreeSL (F : Type*) [Field F] : SL2 F :=
  ⟨!![0, -1; 1, -1], by simp [Matrix.det_fin_two]⟩

theorem orderThreeSL_pow_three (F : Type*) [Field F] : orderThreeSL F ^ 3 = 1 := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;> simp [orderThreeSL, pow_succ, Matrix.mul_apply, Fin.sum_univ_two]

theorem orderThreeSL_ne_smul_one (F : Type*) [Field F] (l : F) :
    ((orderThreeSL F : SL2 F) : Matrix (Fin 2) (Fin 2) F) ≠ l • (1 : Matrix (Fin 2) (Fin 2) F) := by
  intro h
  have := congrFun (congrFun h 1) 0
  simp [orderThreeSL] at this

theorem orderOf_orderThreeSL_eq_three {F : Type*} [Field F] {G : Type*} [Group G]
    (ρ : SL2 F →* G)
    (hρ : ∀ g ∈ ρ.ker, ∃ l : Fˣ, (l : F) ^ 2 = 1 ∧
      (g : Matrix (Fin 2) (Fin 2) F) = (l : F) • (1 : Matrix (Fin 2) (Fin 2) F)) :
    orderOf (ρ (orderThreeSL F)) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime (by rw [← map_pow, orderThreeSL_pow_three, map_one]) fun h1 => ?_
  obtain ⟨l, -, hl⟩ := hρ _ (MonoidHom.mem_ker.2 h1)
  exact orderThreeSL_ne_smul_one F l hl

theorem exists_mulEquiv_graphFixedRootGroup_of_twisted_prime {S : Type} [Group S] {t : TwistTag}
    {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (h : TwistedChevalleyModel S t (p ^ f)) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (σ : K →+* K), Nat.card K = (p ^ f) ^ t.order ∧
      (∀ c, σ c = c ^ (p ^ f)) ∧ Nonempty (graphFixedRootGroup t K σ ≃* S) := by
  obtain ⟨K, _, _, hK, σ, hσ, ⟨e⟩⟩ := h
  have hperf := (finite_fixed_root_group_perfect t hp hf K hK σ hσ).2.2.1
  have hZ := center_graphFixedRootGroup_eq_bot (t := t) (K := K)
    (Finite.surjective_of_injective σ.injective)
  obtain ⟨E⟩ := nonempty_derivedCentralQuotient_mulEquiv_of_eq hperf hZ
  exact ⟨K, inferInstance, inferInstance, σ, hK, hσ, ⟨E.symm.trans e.symm⟩⟩

theorem exists_orderOf_eq_three_of_untwisted {S : Type} [Group S] {τ : Tag} {q : ℕ}
    (h : UntwistedChevalleyModel S τ q) : ∃ x : S, orderOf x = 3 := by
  obtain ⟨K, _, _, -, ⟨e⟩⟩ := exists_mulEquiv_adjointGroup_of_untwisted h
  let i : Fin τ.rank := ⟨0, τ.rank_pos⟩
  let ρ : SL2 K →* adjointGroup τ K :=
    (simpleRootSL2 τ K i).codRestrict _ (simpleRootSL2_mem_adjointGroup i)
  have hρ : ∀ g ∈ ρ.ker, ∃ l : Kˣ, (l : K) ^ 2 = 1 ∧
      (g : Matrix (Fin 2) (Fin 2) K) = (l : K) • (1 : Matrix (Fin 2) (Fin 2) K) := fun g hg =>
    (exceptional_ordinary_rank_one_central_image τ K i).choose_spec.2.2.2.2.2.1 g
      (MonoidHom.mem_ker.2 (congrArg Subtype.val (MonoidHom.mem_ker.1 hg)))
  refine ⟨e (ρ (orderThreeSL K)), ?_⟩
  rw [MulEquiv.orderOf_eq, orderOf_orderThreeSL_eq_three ρ hρ]

theorem exists_orderOf_eq_three_of_twisted {S : Type} [Group S] {t : TwistTag} {p f : ℕ}
    (hp : p.Prime) (hf : 1 ≤ f) (h : TwistedChevalleyModel S t (p ^ f)) :
    ∃ x : S, orderOf x = 3 := by
  obtain ⟨K, _, _, σ, -, -, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_of_twisted_prime hp hf h
  have ha : 0 < t.foldedTag.rank := by cases t <;> decide
  obtain ⟨R, -, -, -, -, -, hRrange, hRC, hRker, -⟩ :=
    exceptional_fixed_rank_one_central_image t K σ ⟨0, ha⟩
  have hRC' : R.range ≤ graphFixedRootGroup t K σ := hRrange ▸ hRC
  let ρ := R.codRestrict _ fun g => hRC' ⟨g, rfl⟩
  have hρ : ∀ g ∈ ρ.ker, ∃ l : (orbitField t K σ ⟨0, ha⟩)ˣ,
      (l : orbitField t K σ ⟨0, ha⟩) ^ 2 = 1 ∧
      (g : Matrix (Fin 2) (Fin 2) (orbitField t K σ ⟨0, ha⟩)) =
        (l : orbitField t K σ ⟨0, ha⟩) • (1 : Matrix (Fin 2) (Fin 2) _) := fun g hg =>
    hRker g (MonoidHom.mem_ker.2 (congrArg Subtype.val (MonoidHom.mem_ker.1 hg)))
  refine ⟨e (ρ (orderThreeSL _)), ?_⟩
  rw [MulEquiv.orderOf_eq, orderOf_orderThreeSL_eq_three ρ hρ]

theorem Chevalley_exceptional_models_order_divisible_by_three (T : Type) [Group T] [Finite T]
    (t : StatedLieTag) (ℓ f : ℕ) (h : ChevalleyExceptionalModel T t ℓ f) : 3 ∣ Nat.card T := by
  suffices hx : ∃ x : T, orderOf x = 3 by
    obtain ⟨x, hx⟩ := hx
    exact hx ▸ orderOf_dvd_natCard x
  obtain ⟨⟨hp, hf, -⟩, hm⟩ := h
  cases t
  case G2 => exact exists_orderOf_eq_three_of_untwisted hm
  case F4 => exact exists_orderOf_eq_three_of_untwisted hm
  case E6 => exact exists_orderOf_eq_three_of_untwisted hm
  case E7 => exact exists_orderOf_eq_three_of_untwisted hm
  case E8 => exact exists_orderOf_eq_three_of_untwisted hm
  case twistedE6 => exact exists_orderOf_eq_three_of_twisted hp hf hm
  case trialityD4 => exact exists_orderOf_eq_three_of_twisted hp hf hm
  all_goals exact (hm : False).elim

end CFSG.RankThree.Chevalley
