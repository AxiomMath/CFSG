module

public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFour
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogQuadraticNormalForms
public import CFSG.ClassicalGroups.Orthogonal.ProjectiveSimple
public import CFSG.ClassicalGroups.Orthogonal.CharTwoTransvection
public import CFSG.RankThree.OrthogonalInvolutions.Dickson

public section

namespace CFSG.RankThree.Classical

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.Classical2 (orthDerived ProjOrthDerived)
open CFSG.ComponentClassification.UnbalancedCatalog (even_finrank_of_charTwo
  exists_hypPairs_normal polar_self_charTwo)
open scoped commutatorElement

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem finrank_tailSpace_add [FiniteDimensional K V] {P : ℕ → HypPair Q} {r : ℕ}
    (hP : ∀ i j, i < r → j < r → i ≠ j → (P i).Orth (P j)) :
    ∀ j ≤ r, finrank K (tailSpace P j) + 2 * j = finrank K V := by
  intro j
  induction j with
  | zero => intro _; rw [tailSpace, finrank_top, mul_zero, add_zero]
  | succ j ih =>
    intro hj
    have h := finrank_inf_perp_add_two (P j) (e_mem_tailSpace hP le_rfl (by omega))
      (f_mem_tailSpace hP le_rfl (by omega))
    rw [← tailSpace_succ] at h
    have := ih (by omega)
    omega

theorem exists_hypPair_tail_decomposition [Finite K] [CharP K 2] [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) :
    ∃ (P : ℕ → HypPair Q) (r : ℕ), 3 ≤ r ∧ (∀ i j, i < r → j < r → i ≠ j → (P i).Orth (P j)) ∧
      (∀ x ∈ tailSpace P r, Q x = 0 → x = 0) ∧
      (finrank K (tailSpace P r) = 0 ∨ finrank K (tailSpace P r) = 2) := by
  classical
  obtain ⟨T, hT3, hTs⟩ := hT
  obtain ⟨P₁, P₂, P₃, h₁₂, h₁₃, h₂₃⟩ := exists_three_hypPairs hQ (T := T) hT3.ge hTs
  set P₀ : ℕ → HypPair Q := fun i => if i = 0 then P₁ else if i = 1 then P₂ else P₃ with hP₀
  have hP₀o : ∀ i j, i < 3 → j < 3 → i ≠ j → (P₀ i).Orth (P₀ j) := by
    intro i j hi hj hij
    interval_cases i <;> interval_cases j <;> simp_all [HypPair.Orth.symm]
  set C := tailSpace P₀ 3 with hCdef
  have hC : PolarNondegOn Q C := polarNondegOn_tailSpace hP₀o hQ le_rfl
  have hCV : finrank K C + 2 * 3 = finrank K V := finrank_tailSpace_add hP₀o 3 le_rfl
  obtain ⟨n₀, hn₀⟩ := even_finrank_of_charTwo Q hQ
  have hCn : finrank K C = 2 * (n₀ - 3) := by omega
  have key : ∀ (m : ℕ) (R : Fin m → HypPair Q), (∀ k, (R k).e ∈ C ∧ (R k).f ∈ C) →
      (∀ k l, k ≠ l → (R k).Orth (R l)) →
      ∃ P : ℕ → HypPair Q, (∀ i j, i < 3 + m → j < 3 + m → i ≠ j → (P i).Orth (P j)) ∧
        ∀ x, x ∈ tailSpace P (3 + m) ↔ x ∈ C ∧ ∀ k, x ∈ (R k).perp := by
    intro m R hRC hRo
    set P : ℕ → HypPair Q := fun i => if i < 3 then P₀ i else
      if h : i - 3 < m then R ⟨i - 3, h⟩ else P₁ with hP
    have hlow : ∀ i < 3, P i = P₀ i := fun i hi => by simp [hP, hi]
    have hhigh : ∀ k : Fin m, P (3 + k) = R k := fun k => by
      simp [hP, k.isLt]
    have hRperp : ∀ k : Fin m, ∀ i < 3, (P₀ i).Orth (R k) := fun k i hi =>
      ⟨(mem_tailSpace.mp (hRC k).1 i hi).1, (mem_tailSpace.mp (hRC k).2 i hi).1,
        (mem_tailSpace.mp (hRC k).1 i hi).2, (mem_tailSpace.mp (hRC k).2 i hi).2⟩
    have hPo : ∀ i j, i < 3 + m → j < 3 + m → i ≠ j → (P i).Orth (P j) := by
      intro i j hi hj hij
      rcases Nat.lt_or_ge i 3 with hi3 | hi3 <;> rcases Nat.lt_or_ge j 3 with hj3 | hj3
      · rw [hlow i hi3, hlow j hj3]
        exact hP₀o i j hi3 hj3 hij
      · obtain ⟨l, rfl⟩ : ∃ l, j = 3 + l := ⟨j - 3, by omega⟩
        rw [hlow i hi3, hhigh ⟨l, by omega⟩]
        exact hRperp _ i hi3
      · obtain ⟨k, rfl⟩ : ∃ k, i = 3 + k := ⟨i - 3, by omega⟩
        rw [hhigh ⟨k, by omega⟩, hlow j hj3]
        exact (hRperp _ j hj3).symm
      · obtain ⟨k, rfl⟩ : ∃ k, i = 3 + k := ⟨i - 3, by omega⟩
        obtain ⟨l, rfl⟩ : ∃ l, j = 3 + l := ⟨j - 3, by omega⟩
        rw [hhigh ⟨k, by omega⟩, hhigh ⟨l, by omega⟩]
        exact hRo _ _ fun h => hij (by simpa using congrArg Fin.val h)
    refine ⟨P, hPo, fun x => ?_⟩
    rw [hCdef, ← tailSpace_congr hlow, mem_tailSpace, mem_tailSpace]
    constructor
    · intro hx
      refine ⟨fun i hi => hx i (by omega), fun k => ?_⟩
      rw [← hhigh k]
      exact HypPair.mem_perp.mpr (hx (3 + k) (by omega))
    · rintro ⟨hx, hk⟩ i hi
      rcases Nat.lt_or_ge i 3 with hi3 | hi3
      · exact hx i hi3
      · obtain ⟨k, rfl⟩ : ∃ k, i = 3 + k := ⟨i - 3, by omega⟩
        rw [hhigh ⟨k, by omega⟩]
        exact HypPair.mem_perp.mp (hk _)
  rcases exists_hypPairs_normal (Q := Q) (n₀ - 3) C hC hCn with
    ⟨R, hRC, hRo⟩ | ⟨m, hm, R, u, v, hRC, hRo, huC, hvC, huv, hu, huv0, hroot⟩
  · obtain ⟨P, hPo, hmem⟩ := key (n₀ - 3) R hRC hRo
    have hdim := finrank_tailSpace_add hPo (3 + (n₀ - 3)) le_rfl
    have h0 : finrank K (tailSpace P (3 + (n₀ - 3))) = 0 := by omega
    refine ⟨P, 3 + (n₀ - 3), by omega, hPo, fun x hx _ => ?_, Or.inl h0⟩
    have := Submodule.finrank_eq_zero.mp h0
    rw [this] at hx
    exact (Submodule.mem_bot K).mp hx
  · obtain ⟨P, hPo, hmem⟩ := key m R hRC hRo
    have hdim := finrank_tailSpace_add hPo (3 + m) le_rfl
    have h2 : finrank K (tailSpace P (3 + m)) = 2 := by omega
    have hu' : u ∈ tailSpace P (3 + m) := (hmem u).mpr ⟨huC, fun k => (huv k).1⟩
    have hv' : v ∈ tailSpace P (3 + m) := (hmem v).mpr ⟨hvC, fun k => (huv k).2⟩
    have hli : LinearIndependent K ![u, v] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      have h1 := congrArg (polar Q u) hst
      rw [polar_add_right, polar_smul_right_eq, polar_smul_right_eq, polar_zero_right,
        polar_self_charTwo Q u, mul_zero, zero_add] at h1
      have ht : t = 0 := (mul_eq_zero.mp h1).resolve_right huv0
      subst ht
      rw [zero_smul, add_zero] at hst
      have hu0 : u ≠ 0 := by
        rintro rfl
        rw [map_zero] at hu
        exact zero_ne_one hu
      exact ⟨(smul_eq_zero.mp hst).resolve_right hu0, rfl⟩
    have hspan : Submodule.span K {u, v} = tailSpace P (3 + m) := by
      refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
      · rw [Submodule.span_le]
        intro y hy
        rcases hy with rfl | hy
        · exact hu'
        · rw [Set.mem_singleton_iff] at hy
          rw [hy]
          exact hv'
      · rw [h2]
        have h := finrank_span_eq_card hli
        rwa [Matrix.range_cons_cons_empty, Fintype.card_fin] at h
    refine ⟨P, 3 + m, by omega, hPo, fun x hx hQx => ?_, Or.inr h2⟩
    rw [← hspan] at hx
    obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hx
    rw [QuadraticMap.map_add Q, map_smul_eq_sq, map_smul_eq_sq, hu, polar_smul_left_eq,
      polar_smul_right_eq, mul_one] at hQx
    by_cases ht : t = 0
    · subst ht
      have hs : s ^ 2 = 0 := by rw [← hQx]; ring
      rw [pow_eq_zero_iff two_ne_zero] at hs
      subst hs
      simp
    · exfalso
      apply hroot (s / t)
      have ht2 : t ^ 2 ≠ 0 := pow_ne_zero 2 ht
      field_simp
      linear_combination hQx

section Finite

variable [Finite K] [FiniteDimensional K V]

theorem orthDerived_eq_and_le_closure (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) :
    orthDerived Q = elementaryGroup Q ∧
      TauCeti.QuadraticMap.orthogonalGroup Q ≤
        Subgroup.closure (Set.range (reflect Q) ∪ elementaryGroup Q) := by
  by_cases h2 : ringChar K = 2
  · have : CharP K 2 := ringChar.of_eq h2
    obtain ⟨P, r, hr, hP, hA, hdim⟩ := exists_hypPair_tail_decomposition hQ hT
    have h2' : (2 : K) = 0 := CharTwo.two_eq_zero
    have hA' : ∀ x ∈ tailSpace P r, x ≠ 0 → ∀ y ∈ tailSpace P r, polar Q x y = 0 →
        ∃ c : K, y = c • x := by
      intro x hx hx0 y hy hxy
      rcases hdim with h0 | h2''
      · exact absurd ((Submodule.finrank_eq_zero.1 h0) ▸ hx : x ∈ (⊥ : Submodule K V))
          (by rw [Submodule.mem_bot]; exact hx0)
      · exact eq_smul_of_polar_eq_zero_of_finrank_two h2'' (polarNondegOn_tailSpace hP hQ le_rfl)
          hx hx0 (by rw [polar_self_eq_two_mul, h2', zero_mul]) hy hxy
    exact ⟨orthogonal_char_two_derived_elementary hQ hP hr hA hdim,
      orthogonalGroup_le_closure_of_two_eq_zero hP hQ h2' hA hA' (by omega)⟩
  · refine ⟨orthogonal_odd_derived_elementary h2 hQ hT, fun g hg => ?_⟩
    obtain ⟨l, -, hl, rfl⟩ := orthogonal_odd_reflection_generation h2 hQ hg
    refine Subgroup.list_prod_mem _ fun x hx => ?_
    obtain ⟨v, -, rfl⟩ := List.mem_map.mp hx
    exact Subgroup.subset_closure (Or.inl ⟨v, rfl⟩)

end Finite

theorem sq_mem_orthDerived_of_mem_closure {S : Set (V ≃ₗ[K] V)}
    (hS : ∀ x ∈ S, x ∈ TauCeti.QuadraticMap.orthogonalGroup Q ∧ x ^ 2 ∈ orthDerived Q)
    {g : V ≃ₗ[K] V} (hg : g ∈ Subgroup.closure S) :
    g ∈ TauCeti.QuadraticMap.orthogonalGroup Q ∧ g ^ 2 ∈ orthDerived Q := by
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hS x hx
  | one => exact ⟨one_mem _, by rw [one_pow]; exact one_mem _⟩
  | mul x y _ _ hx hy =>
    refine ⟨mul_mem hx.1 hy.1, ?_⟩
    have h : (x * y) ^ 2 = x ^ 2 * ⁅x⁻¹, y⁆ * y ^ 2 := by
      rw [_root_.sq, _root_.sq, _root_.sq, commutatorElement_def]
      group
    rw [h]
    exact mul_mem (mul_mem hx.2 (Subgroup.commutator_mem_commutator (inv_mem hx.1) hy.1)) hy.2
  | inv x _ hx =>
    refine ⟨inv_mem hx.1, ?_⟩
    rw [inv_pow]
    exact inv_mem hx.2

theorem exists_sq_eq_one_of_mem_scalars {g : V ≃ₗ[K] V} (hg : g ∈ scalars K V)
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {a : V} (ha : Q a ≠ 0) :
    ∃ c : K, c ^ 2 = 1 ∧ ∀ v, g v = c • v := by
  obtain ⟨c, hc⟩ := mem_scalars.mp hg
  refine ⟨c, ?_, hc⟩
  have h := map_of_mem hgO a
  rw [hc, map_smul_eq_sq] at h
  have h1 : (c ^ 2 - 1) * Q a = 0 := by rw [sub_mul, h, one_mul, sub_self]
  exact sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_right ha)

@[expose] def zmodTwoSign : Multiplicative (ZMod 2) →* ℤˣ where
  toFun x := (-1 : ℤˣ) ^ (Multiplicative.toAdd x)
  map_one' := by rw [toAdd_one, uzpow_zero]
  map_mul' x y := by rw [toAdd_mul, uzpow_add]

theorem orthogonal_high_Witt_derived_quotient_and_odd_lifts [Finite K] [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) :
    Group.IsPerfect (orthDerived Q) ∧
    Subgroup.center (orthDerived Q) = (scalars K V).subgroupOf (orthDerived Q) ∧
    Nat.card ((scalars K V).subgroupOf (orthDerived Q)) ≤ 2 ∧
    IsSimpleGroup (ProjOrthDerived Q) ∧ (∃ a b : ProjOrthDerived Q, a * b ≠ b * a) ∧
    (∀ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q, g ^ 2 ∈ orthDerived Q) ∧
    (∀ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q, Odd (orderOf g) → g ∈ orthDerived Q) ∧
    (∃ χ : TauCeti.QuadraticMap.orthogonalGroup Q →* ℤˣ,
      (∀ g : TauCeti.QuadraticMap.orthogonalGroup Q, (g : V ≃ₗ[K] V) ∈ orthDerived Q →
        χ g = 1) ∧
      ∀ v : V, Q v ≠ 0 → χ ⟨reflect Q v, reflect_mem_orthogonalGroup Q v⟩ = -1) ∧
    ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ a : ProjOrthDerived Q, orderOf a = p →
      ∃ x : orthDerived Q, (QuotientGroup.mk x = a ∧ orderOf x = p) ∧
        (∀ x' : orthDerived Q, QuotientGroup.mk x' = a → orderOf x' = p → x' = x) ∧
        Subgroup.centralizer {a} = (Subgroup.centralizer {x}).map
          (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))) := by
  classical
  obtain ⟨hΩE, hgen⟩ := orthDerived_eq_and_le_closure hQ hT
  obtain ⟨T, hT3, hTs⟩ := hT
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have hperf : Group.IsPerfect (orthDerived Q) := by
    rw [hΩE]
    exact ⟨commutator_elementaryGroup_eq_top' hQ hT3.ge hTs⟩
  have hsimple : IsSimpleGroup (ProjOrthDerived Q) := by
    show IsSimpleGroup (↥(orthDerived Q) ⧸ (scalars K V).subgroupOf (orthDerived Q))
    rw [hΩE]
    exact isSimpleGroup_projElementary hQ hT3.ge hTs
  have hnonab : ∃ a b : ProjOrthDerived Q, a * b ≠ b * a := by
    by_contra h
    push Not at h
    exact Group.IsPerfect.not_isMulCommutative (ProjOrthDerived Q) ⟨⟨fun a b => h a b⟩⟩
  have hcenter : Subgroup.center (orthDerived Q) = (scalars K V).subgroupOf (orthDerived Q) := by
    refine le_antisymm (fun z hz => ?_) fun z hz => ?_
    · have hcen : (QuotientGroup.mk z : ProjOrthDerived Q) ∈
          Subgroup.center (ProjOrthDerived Q) := by
        rw [Subgroup.mem_center_iff]
        intro t
        obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective t
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.mp hz y]
      have hbot : Subgroup.center (ProjOrthDerived Q) = ⊥ := by
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (ProjOrthDerived Q)) with
          h | h
        · exact h
        · exfalso
          obtain ⟨a, b, hab⟩ := hnonab
          exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)
      rw [hbot, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hcen
      exact hcen
    · rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      exact (commute_of_mem_scalars (Subgroup.mem_subgroupOf.mp hz) y).symm
  have : Nontrivial V := by
    have hT0 : T ≠ ⊥ := fun h => by
      rw [h, finrank_bot] at hT3
      omega
    obtain ⟨x, -, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hT0
    exact ⟨⟨x, 0, hx0⟩⟩
  obtain ⟨a₀, ha₀⟩ := CFSG.RankThree.OrthogonalInvolutions.exists_map_ne_zero hQ
  have hscal : ∀ z : (scalars K V).subgroupOf (orthDerived Q),
      ∃ c : K, c ^ 2 = 1 ∧ ∀ v, (((z : orthDerived Q) : V ≃ₗ[K] V)) v = c • v := fun z =>
    exists_sq_eq_one_of_mem_scalars (Subgroup.mem_subgroupOf.mp z.2)
      (Subgroup.commutator_le_self (TauCeti.QuadraticMap.orthogonalGroup Q) (z : orthDerived Q).2)
      ha₀
  have hZcard : Nat.card ((scalars K V).subgroupOf (orthDerived Q)) ≤ 2 := by
    choose c hc1 hc using hscal
    have hpm : ∀ z, c z = 1 ∨ c z = -1 := fun z => by
      have h : (c z - 1) * (c z + 1) = 0 := by linear_combination hc1 z
      rcases mul_eq_zero.mp h with h1 | h1
      · exact Or.inl (sub_eq_zero.mp h1)
      · exact Or.inr (eq_neg_of_add_eq_zero_left h1)
    let F : (scalars K V).subgroupOf (orthDerived Q) → Bool := fun z => decide (c z = 1)
    have hF : Function.Injective F := by
      intro z₁ z₂ h
      have hiff : c z₁ = 1 ↔ c z₂ = 1 := decide_eq_decide.mp h
      have hceq : c z₁ = c z₂ := by
        by_cases h₁ : c z₁ = 1
        · rw [h₁, hiff.mp h₁]
        · have h₂ : c z₂ ≠ 1 := fun h₂ => h₁ (hiff.mpr h₂)
          rw [(hpm z₁).resolve_left h₁, (hpm z₂).resolve_left h₂]
      exact Subtype.ext (Subtype.ext (LinearEquiv.ext fun v => by rw [hc, hc, hceq]))
    calc Nat.card ((scalars K V).subgroupOf (orthDerived Q)) ≤ Nat.card Bool :=
          Nat.card_le_card_of_injective F hF
      _ = 2 := by rw [Nat.card_eq_fintype_card, Fintype.card_bool]
  have hsq : ∀ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q, g ^ 2 ∈ orthDerived Q := fun g hg =>
    (sq_mem_orthDerived_of_mem_closure (fun x hx => by
      rcases hx with ⟨v, rfl⟩ | hx
      · refine ⟨reflect_mem_orthogonalGroup Q v, ?_⟩
        rw [pow_two, reflect_mul_self]
        exact one_mem _
      · refine ⟨elementaryGroup_le_orthogonalGroup Q hx, ?_⟩
        rw [hΩE]
        exact pow_mem hx 2) (hgen hg)).2
  have hodd : ∀ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q, Odd (orderOf g) →
      g ∈ orthDerived Q := by
    intro g hg ⟨k, hk⟩
    have : g = (g ^ 2) ^ (k + 1) := by
      rw [← pow_mul, show 2 * (k + 1) = orderOf g + 1 by omega, pow_succ, pow_orderOf_eq_one,
        one_mul]
    rw [this]
    exact pow_mem (hsq g hg) _
  have hsign : ∃ χ : TauCeti.QuadraticMap.orthogonalGroup Q →* ℤˣ,
      (∀ g : TauCeti.QuadraticMap.orthogonalGroup Q, (g : V ≃ₗ[K] V) ∈ orthDerived Q →
        χ g = 1) ∧
      ∀ v : V, Q v ≠ 0 → χ ⟨reflect Q v, reflect_mem_orthogonalGroup Q v⟩ = -1 := by
    refine ⟨zmodTwoSign.comp (CFSG.RankThree.OrthogonalInvolutions.dicksonHom Q hQ),
      fun g hg => ?_, fun v hv => ?_⟩
    · have hg' : g ∈ commutator (TauCeti.QuadraticMap.orthogonalGroup Q) := by
        rw [orthDerived, ← Subgroup.map_subtype_commutator] at hg
        obtain ⟨g', hg', hgg'⟩ := hg
        rwa [← Subtype.ext hgg']
      exact Abelianization.commutator_subset_ker _ hg'
    · let _ : Invertible (Q v) := invertibleOfNonzero hv
      have h1 : finrank K (CFSG.RankThree.OrthogonalInvolutions.commSpace (reflect Q v)) = 1 := by
        rw [reflect_eq_reflection]
        exact CFSG.RankThree.OrthogonalInvolutions.finrank_commSpace_reflection hQ v
      rw [MonoidHom.comp_apply, CFSG.RankThree.OrthogonalInvolutions.dicksonHom_apply]
      change zmodTwoSign (Multiplicative.ofAdd ((finrank K
        (CFSG.RankThree.OrthogonalInvolutions.commSpace (reflect Q v)) : ℕ) : ZMod 2)) = -1
      rw [h1, Nat.cast_one]
      change (-1 : ℤˣ) ^ (1 : ZMod 2) = -1
      exact uzpow_one _
  have hZ2 : ∀ z ∈ (scalars K V).subgroupOf (orthDerived Q), z ^ 2 = 1 := by
    intro z hz
    have hpos : 0 < Nat.card ((scalars K V).subgroupOf (orthDerived Q)) := Nat.card_pos
    have hdvd : Nat.card ((scalars K V).subgroupOf (orthDerived Q)) ∣ 2 := by
      rcases (show Nat.card ((scalars K V).subgroupOf (orthDerived Q)) = 1 ∨
          Nat.card ((scalars K V).subgroupOf (orthDerived Q)) = 2 by omega) with h | h <;>
        rw [h]
      exact one_dvd 2
    have h1 : (⟨z, hz⟩ : (scalars K V).subgroupOf (orthDerived Q)) ^ 2 = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_natCard _).trans hdvd)
    simpa using congrArg Subtype.val h1
  have hlift : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ a : ProjOrthDerived Q, orderOf a = p →
      ∃ x : orthDerived Q, (QuotientGroup.mk x = a ∧ orderOf x = p) ∧
        (∀ x' : orthDerived Q, QuotientGroup.mk x' = a → orderOf x' = p → x' = x) := by
    intro p hp hp2 a ha
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨k, hk⟩ : Odd p := hp.odd_of_ne_two hp2
    have ha1 : a ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at ha
      exact hp.one_lt.ne ha
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective a
    have hap : (QuotientGroup.mk g : ProjOrthDerived Q) ^ p = 1 := by
      rw [← ha]
      exact pow_orderOf_eq_one _
    have hgp : g ^ p ∈ (scalars K V).subgroupOf (orthDerived Q) := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hap]
    have hmk : (QuotientGroup.mk (g ^ (p + 1)) : ProjOrthDerived Q) = QuotientGroup.mk g := by
      rw [QuotientGroup.mk_pow, pow_succ, hap, one_mul]
    have hgp1 : (g ^ (p + 1)) ^ p = 1 := by
      rw [← pow_mul, mul_comm (p + 1) p, pow_mul, show p + 1 = 2 * (k + 1) by omega, pow_mul,
        hZ2 _ hgp, one_pow]
    refine ⟨g ^ (p + 1), ⟨hmk, ?_⟩, ?_⟩
    · apply orderOf_eq_prime hgp1
      intro h1
      apply ha1
      rw [← hmk, h1, QuotientGroup.mk_one]
    · intro x' hx' hx'p
      have hw : x' * (g ^ (p + 1))⁻¹ ∈ (scalars K V).subgroupOf (orthDerived Q) := by
        rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hx', hmk,
          mul_inv_cancel]
      have hwc : x' * (g ^ (p + 1))⁻¹ ∈ Subgroup.center (orthDerived Q) := hcenter ▸ hw
      have hx'eq : x' = x' * (g ^ (p + 1))⁻¹ * g ^ (p + 1) := by rw [inv_mul_cancel_right]
      have hwp : (x' * (g ^ (p + 1))⁻¹) ^ p = 1 := by
        have h1 : x' ^ p = 1 := by rw [← hx'p]; exact pow_orderOf_eq_one x'
        have hcomm : Commute (x' * (g ^ (p + 1))⁻¹) (g ^ (p + 1)) :=
          (Subgroup.mem_center_iff.mp hwc (g ^ (p + 1))).symm
        rw [hx'eq, hcomm.mul_pow, hgp1, mul_one] at h1
        exact h1
      have hw2 := hZ2 _ hw
      have hw1 : x' * (g ^ (p + 1))⁻¹ = 1 := by
        have h' : ∀ w : orthDerived Q, w = (w ^ 2) ^ (k + 1) * (w ^ (2 * k + 1))⁻¹ := fun w => by
          group
        rw [h' (x' * (g ^ (p + 1))⁻¹), hw2, ← hk, hwp, one_pow, inv_one, mul_one]
      rw [hx'eq, hw1, one_mul]
  refine ⟨hperf, hcenter, hZcard, hsimple, hnonab, hsq, hodd, hsign, fun p hp hp2 a ha => ?_⟩
  obtain ⟨x, ⟨hxa, hxp⟩, huniq⟩ := hlift p hp hp2 a ha
  refine ⟨x, ⟨hxa, hxp⟩, huniq, le_antisymm (fun t ht => ?_) ?_⟩
  · obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective t
    refine ⟨g, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    have hconj : g * x * g⁻¹ = x := by
      refine huniq _ ?_ ?_
      · rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hxa]
        have := Subgroup.mem_centralizer_singleton_iff.mp ht
        rw [this, mul_inv_cancel_right]
      · rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hxp]
    calc g * x = g * x * g⁻¹ * g := by group
      _ = x * g := by rw [hconj]
  · rintro _ ⟨g, hg, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at hg
    rw [Subgroup.mem_centralizer_singleton_iff, ← hxa, QuotientGroup.mk'_apply,
      ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hg]

end CFSG.RankThree.Classical
