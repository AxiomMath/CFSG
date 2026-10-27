module

public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.Quasithin.ModG

theorem comm_235 {A : Type*} [CommGroup A] {x y : A} (hx : x ^ 2 = 1) (hy : y ^ 3 = 1)
    (hxy : (x * y) ^ 5 = 1) : x = 1 ∧ y = 1 := by
  have h1 : x * y ^ 2 = 1 := by
    have : (x * y) ^ 5 = x ^ 5 * y ^ 5 := mul_pow x y 5
    rw [this] at hxy
    have hx5 : x ^ 5 = x := by
      calc x ^ 5 = (x ^ 2) ^ 2 * x := by rw [← pow_mul, ← pow_succ]
        _ = x := by rw [hx]; simp
    have hy5 : y ^ 5 = y ^ 2 := by
      calc y ^ 5 = y ^ 3 * y ^ 2 := by rw [← pow_add]
        _ = y ^ 2 := by rw [hy]; simp
    rw [hx5, hy5] at hxy
    exact hxy
  have h2 : x = y := by
    have hy2 : y ^ 2 = y⁻¹ := by
      have : y ^ 2 * y = 1 := by rw [← pow_succ]; exact hy
      exact eq_inv_of_mul_eq_one_left this
    rw [hy2] at h1
    exact (mul_inv_eq_one.1 h1)
  subst h2
  have : x = 1 := by
    have h3 : x ^ 3 = x * x ^ 2 := by rw [pow_succ']
    rw [hx, mul_one] at h3
    rw [← h3]
    exact hy
  exact ⟨this, this⟩

theorem not_solvable_of_235 {G : Type*} [Group G] {a b : G} (ha : a ^ 2 = 1) (hb : b ^ 3 = 1)
    (hab : (a * b) ^ 5 = 1) (hb1 : b ≠ 1) :
    ¬ Group.IsSolvable ↥(Subgroup.closure ({a, b} : Set G)) := by
  intro hsolv
  set H := Subgroup.closure ({a, b} : Set G) with hH
  have haH : a ∈ H := Subgroup.subset_closure (Or.inl rfl)
  have hbH : b ∈ H := Subgroup.subset_closure (Or.inr rfl)
  set a' : ↥H := ⟨a, haH⟩ with ha'
  set b' : ↥H := ⟨b, hbH⟩ with hb'
  have hnt : Nontrivial ↥H := by
    refine ⟨⟨b', 1, ?_⟩⟩
    intro h
    apply hb1
    exact congrArg Subtype.val h
  have h1 := comm_235 (A := Abelianization ↥H) (x := Abelianization.of a') (y := Abelianization.of b')
    (by rw [← map_pow]; have : a' ^ 2 = 1 := Subtype.ext ha; rw [this, map_one])
    (by rw [← map_pow]; have : b' ^ 3 = 1 := Subtype.ext hb; rw [this, map_one])
    (by rw [← map_mul, ← map_pow]; have : (a' * b') ^ 5 = 1 := Subtype.ext hab; rw [this, map_one])
  have hca : a' ∈ commutator ↥H := by
    have := h1.1
    exact (QuotientGroup.eq_one_iff _).1 this
  have hcb : b' ∈ commutator ↥H := by
    have := h1.2
    exact (QuotientGroup.eq_one_iff _).1 this
  have htop : commutator ↥H = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨g, hg⟩ := x
    have key : ∀ (g : G) (hg : g ∈ H), (⟨g, hg⟩ : ↥H) ∈ commutator ↥H := by
      intro g hg
      induction hg using Subgroup.closure_induction with
      | mem x hx =>
        rcases hx with rfl | rfl
        · exact hca
        · exact hcb
      | one => exact one_mem _
      | mul x y hx hy ihx ihy => exact mul_mem ihx ihy
      | inv x hx ih => exact inv_mem ih
    exact key g hg
  have := Group.IsSolvable.commutator_lt_top_of_nontrivial ↥H
  rw [htop] at this
  exact lt_irrefl _ this

theorem isSolvable_of_cosets {P : Type*} [Group P] [Finite P] (S : Subgroup P) (hS : IsPGroup 2 ↥S)
    (n : ℕ) (hn : n ≤ 3) (reps : Fin n → P) (hcov : ∀ p : P, ∃ i, (reps i)⁻¹ * p ∈ S) :
    Group.IsSolvable P := by
  classical
  have hcard : Nat.card (P ⧸ S) ≤ 3 := by
    have hsurj : Function.Surjective (fun i : Fin n => ((reps i : P) : P ⧸ S)) := by
      intro q
      induction q using QuotientGroup.induction_on with
      | H p =>
        obtain ⟨i, hi⟩ := hcov p
        exact ⟨i, (QuotientGroup.eq.2 hi)⟩
    have h := Nat.card_le_card_of_surjective _ hsurj
    rw [Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin] at h
    omega
  have : Finite (P ⧸ S) := Nat.finite_of_card_ne_zero (by
    have : 0 < Nat.card (P ⧸ S) := Nat.card_pos
    omega)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let φ : P →* Equiv.Perm (P ⧸ S) := MulAction.toPermHom P (P ⧸ S)
  have hker : φ.ker ≤ S := by
    intro g hg
    have h1 : φ g = 1 := hg
    have h2 : g • ((1 : P) : P ⧸ S) = ((1 : P) : P ⧸ S) :=
      congrArg (fun f : Equiv.Perm (P ⧸ S) => f ((1 : P) : P ⧸ S)) h1
    have h3 : ((g * 1 : P) : P ⧸ S) = ((1 : P) : P ⧸ S) := h2
    have := QuotientGroup.eq.1 h3.symm
    simpa using this
  have hkp : IsPGroup 2 ↥φ.ker := hS.to_le hker
  have : Group.IsNilpotent ↥φ.ker := hkp.isNilpotent
  have : Group.IsSolvable (Equiv.Perm (P ⧸ S)) := Equiv.Perm.isSolvable (hcard.trans (by norm_num))
  exact Group.isSolvable_of_ker_le_range φ.ker.subtype φ (by simp)

theorem exists_coset_rep {G : Type*} [Group G] [Finite G] (D S : Subgroup G) (L : List G)
    (hL : ∀ x ∈ L, x ∈ D) (hpw : L.Pairwise (fun x y => x⁻¹ * y ∉ S))
    (hlen : L.length = (S.subgroupOf D).index) : ∀ x ∈ D, ∃ d ∈ L, d⁻¹ * x ∈ S := by
  classical
  intro x hx
  set S' := S.subgroupOf D with hS'
  have : Finite (↥D ⧸ S') := inferInstance
  let _ : Fintype (↥D ⧸ S') := Fintype.ofFinite _
  let f : Fin L.length → ↥D ⧸ S' := fun i => ((⟨L.get i, hL _ (List.get_mem L i)⟩ : ↥D) : ↥D ⧸ S')
  have hinj : Function.Injective f := by
    intro i j hij
    by_contra hne
    have hij' : (⟨L.get i, hL _ (List.get_mem L i)⟩ : ↥D)⁻¹ * ⟨L.get j, hL _ (List.get_mem L j)⟩ ∈ S' :=
      QuotientGroup.eq.1 hij
    have hmem : (L.get i)⁻¹ * L.get j ∈ S := hij'
    rcases lt_or_gt_of_ne hne with h | h
    · exact (List.pairwise_iff_get.1 hpw i j h) hmem
    · have h' := List.pairwise_iff_get.1 hpw j i h
      apply h'
      have := S.inv_mem hmem
      simpa using this
  have hcard : Fintype.card (Fin L.length) = Fintype.card (↥D ⧸ S') := by
    rw [Fintype.card_fin, hlen]
    rw [Subgroup.index, Nat.card_eq_fintype_card]
  have hbij : Function.Bijective f := (Fintype.bijective_iff_injective_and_card f).2 ⟨hinj, hcard⟩
  obtain ⟨i, hi⟩ := hbij.2 ((⟨x, hx⟩ : ↥D) : ↥D ⧸ S')
  refine ⟨L.get i, List.get_mem L i, ?_⟩
  have := QuotientGroup.eq.1 hi
  exact this

theorem nonempty_mulEquiv_of_exp_two {X : Type*} [CommGroup X] [Finite X] (hX : ∀ x : X, x * x = 1)
    {n : ℕ} (hc : Nat.card X = 2 ^ n) : Nonempty (X ≃* Multiplicative (Fin n → ZMod 2)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Fintype X := Fintype.ofFinite X
  have h2 : ∀ x : Additive X, 2 • x = 0 := fun x => by
    rw [two_nsmul]
    exact hX (Additive.toMul x)
  let _ : Module (ZMod 2) (Additive X) := AddCommGroup.zmodModule h2
  have hfr : Module.finrank (ZMod 2) (Additive X) = n := by
    have h := Module.card_eq_pow_finrank (K := ZMod 2) (V := Additive X)
    have hc' : Fintype.card (Additive X) = 2 ^ n := by
      rw [← Nat.card_eq_fintype_card, Nat.card_congr (Additive.ofMul : X ≃ Additive X).symm, hc]
    rw [hc', ZMod.card] at h
    exact (Nat.pow_right_injective (le_refl 2) h).symm
  let e : Additive X ≃ₗ[ZMod 2] (Fin n → ZMod 2) :=
    LinearEquiv.ofFinrankEq (Additive X) (Fin n → ZMod 2) (by rw [hfr, Module.finrank_fin_fun])
  exact ⟨{ toFun := fun x => Multiplicative.ofAdd (e (Additive.ofMul x))
           invFun := fun v => Additive.toMul (e.symm (Multiplicative.toAdd v))
           left_inv := fun x => by simp
           right_inv := fun v => by simp
           map_mul' := fun x y => by
             show Multiplicative.ofAdd (e (Additive.ofMul (x * y))) =
               Multiplicative.ofAdd (e (Additive.ofMul x)) * Multiplicative.ofAdd (e (Additive.ofMul y))
             rw [← ofAdd_add, ← map_add]
             rfl }⟩

end CFSG.Quasithin.ModG
