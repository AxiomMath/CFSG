module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmPlusWeyl
public import CFSG.LieType.Universal.Spin.Action
public import CFSG.LieType.Universal.Spin.Forms
public import Mathlib.LinearAlgebra.Matrix.Permutation
import CFSG.RankThree.OrthogonalInvolutions.OmegaClasses
import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalOmegaPlusModel
import CFSG.ClassicalGroups.Orthogonal.RootGroupStabilizerFour
public import CFSG.RankThree.OrthogonalInvolutions.Dickson
import CFSG.ClassicalGroups.Orthogonal.RootGroupNormalizer

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal.Spin CFSG.StandardType

open scoped BigOperators
open CFSG.RankThree.OrthogonalInvolutions
open QuadraticMap Module

variable {K : Type} [Field K]

private theorem ompInv_funCongrLeft_single {ι : Type*} [DecidableEq ι] (π : Equiv.Perm ι)
    (j : ι) :
    LinearEquiv.funCongrLeft K K π (Pi.single j (1:K) : ι → K) = Pi.single (π.symm j) 1 := by
  ext i
  rw [LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply, Pi.single_apply, Pi.single_apply]
  by_cases h : π i = j
  · have h' : i = π.symm j := by rw [← h, Equiv.symm_apply_apply]
    rw [if_pos h, if_pos h']
  · have h' : i ≠ π.symm j := fun hh => h (by rw [hh, Equiv.apply_symm_apply])
    rw [if_neg h, if_neg h']

private theorem ompInv_funCongrLeft_mul {ι : Type*} (π σ : Equiv.Perm ι) :
    LinearEquiv.funCongrLeft K K π * LinearEquiv.funCongrLeft K K σ =
      LinearEquiv.funCongrLeft K K (σ * π) := by
  ext y i
  rfl

private theorem ompInv_commSpace_funCongrLeft_of_involution {ι : Type*} [Fintype ι]
    [DecidableEq ι] (π : Equiv.Perm ι) (hπ : π * π = 1) :
    commSpace (LinearEquiv.funCongrLeft K K π) =
      Submodule.span K (Set.range fun j => Pi.single (π j) (1:K) - Pi.single j 1) := by
  have hπ' : π.symm = π := inv_eq_of_mul_eq_one_right hπ
  have hsingle : ∀ j : ι, LinearEquiv.funCongrLeft K K π (Pi.single j (1:K) : ι → K) =
      Pi.single (π j) 1 := by
    intro j
    rw [ompInv_funCongrLeft_single, hπ']
  rw [commSpace, LinearMap.range_eq_map, ← Module.Basis.span_eq (Pi.basisFun K ι),
    Submodule.map_span, ← Set.range_comp]
  congr 1
  apply congrArg Set.range
  funext j
  simp [Function.comp_apply, hsingle, Pi.basisFun_apply]

private theorem ompInv_linearIndependent_single_sub_single {ι' : Type*} [Fintype ι']
    {ι : Type*} [DecidableEq ι]
    (a b : ι' → ι) (hinj : Function.Injective a) (hne : ∀ i j, a i ≠ b j) :
    LinearIndependent K (fun i => (Pi.single (a i) (1:K) - Pi.single (b i) 1 : ι → K)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have hsingle : ∀ j : ι', j ≠ i →
      (c j • (Pi.single (a j) (1:K) - Pi.single (b j) 1 : ι → K)) (a i) = 0 := by
    intro j hji
    simp only [Pi.smul_apply, Pi.sub_apply, Pi.single_apply, smul_eq_mul]
    rw [if_neg (fun h : a i = a j => hji (hinj h).symm), if_neg (hne i j)]
    simp
  have h := congrArg (fun v : ι → K => v (a i)) hc
  simp only [Finset.sum_apply, Pi.zero_apply] at h
  rw [Finset.sum_eq_single i (fun j _ hji => hsingle j hji)
    (fun hi => absurd (Finset.mem_univ i) hi)] at h
  simpa [Pi.single_apply, hne i i] using h

private theorem ompInv_span_range_sub_single_eq_span_half {ι : Type*} [Fintype ι] [DecidableEq ι]
    (σ : Equiv.Perm ι) (hσ : σ * σ = 1) (e : ι ≃ Fin (Fintype.card ι)) :
    Submodule.span K (Set.range fun j => (Pi.single (σ j) (1:K) - Pi.single j 1 : ι → K)) =
      Submodule.span K (Set.range fun i :
        (Finset.univ.filter (fun j => σ j ≠ j ∧ e j < e (σ j)) : Finset ι) =>
        (Pi.single (σ i) (1:K) - Pi.single (i : ι) 1 : ι → K)) := by
  let g : ι → (ι → K) := fun j => (Pi.single (σ j) (1:K) - Pi.single j 1 : ι → K)
  change Submodule.span K (Set.range g) =
    Submodule.span K (Set.range fun i :
      (Finset.univ.filter (fun j => σ j ≠ j ∧ e j < e (σ j)) : Finset ι) => g i)
  have hσe : ∀ x, σ (σ x) = x := fun x => by rw [← Equiv.Perm.mul_apply, hσ]; rfl
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro x ⟨j, rfl⟩
    by_cases hj : σ j = j
    · rw [show g j = 0 from by simp [g, hj]]
      exact Submodule.zero_mem _
    · have hjS : j ∈ Finset.univ.filter (fun j => σ j ≠ j ∧ e j < e (σ j)) ↔ e j < e (σ j) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_iff_right hj]
      rcases lt_trichotomy (e j) (e (σ j)) with h | h | h
      · exact Submodule.subset_span ⟨⟨j, hjS.mpr h⟩, rfl⟩
      · exact absurd (e.injective h).symm hj
      · have hiS : σ j ∈ Finset.univ.filter (fun j => σ j ≠ j ∧ e j < e (σ j)) := by
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨?_, ?_⟩⟩
          · intro hh; rw [hσe] at hh; exact hj hh.symm
          · rw [hσe]; exact h
        have hgj : g j = -g (σ j) := by
          simp only [g]
          rw [hσe, neg_sub]
        rw [hgj]
        exact Submodule.neg_mem _ (Submodule.subset_span ⟨⟨σ j, hiS⟩, rfl⟩)
  · rw [Submodule.span_le]
    rintro x ⟨i, rfl⟩
    exact Submodule.subset_span ⟨i, rfl⟩

private theorem ompInv_linearIndependent_pair_sub_single {ι : Type*} [Fintype ι]
    [DecidableEq ι] (σ : Equiv.Perm ι) (hσ : σ * σ = 1) (e : ι ≃ Fin (Fintype.card ι)) :
    LinearIndependent K (fun i :
        (Finset.univ.filter (fun j => σ j ≠ j ∧ e j < e (σ j)) : Finset ι) =>
      (Pi.single (σ i) (1:K) - Pi.single (i : ι) 1 : ι → K)) := by
  have hσe : ∀ x, σ (σ x) = x := fun x => by rw [← Equiv.Perm.mul_apply, hσ]; rfl
  exact ompInv_linearIndependent_single_sub_single (K := K)
    (fun i : (Finset.univ.filter (fun j => σ j ≠ j ∧ e j < e (σ j)) : Finset ι) => σ i)
    (fun i => (i : ι))
    (fun i j h => Subtype.ext (σ.injective h))
    (by
      rintro ⟨i, hiS⟩ ⟨j, hjS⟩ heq
      have hi : e i < e (σ i) := (Finset.mem_filter.mp hiS).2.2
      have hj : e j < e (σ j) := (Finset.mem_filter.mp hjS).2.2
      have h1 : e i < e j := by simpa [heq] using hi
      have h2 : e j < e i := by
        have hsj : σ j = i := by
          have h2 := hσe i
          rwa [heq] at h2
        simpa [hsj] using hj
      exact absurd h1 (not_lt.mpr h2.le))

private theorem ompInv_image_filter_lt_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (σ : Equiv.Perm ι) (hσ : σ * σ = 1) (e : ι ≃ Fin (Fintype.card ι)) :
    (Finset.univ.filter (fun j => σ j ≠ j ∧ e j < e (σ j))).image σ =
      Finset.univ.filter (fun j => σ j ≠ j ∧ e (σ j) < e j) := by
  have hσe : ∀ x, σ (σ x) = x := fun x => by rw [← Equiv.Perm.mul_apply, hσ]; rfl
  ext j
  rw [Finset.mem_image]
  constructor
  · rintro ⟨i, hiS, rfl⟩
    have hi := Finset.mem_filter.mp hiS
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨by intro h; rw [hσe] at h; exact hi.2.1 h.symm, by rw [hσe]; exact hi.2.2⟩⟩
  · intro hjS'
    have hj := Finset.mem_filter.mp hjS'
    refine ⟨σ j, ?_, hσe j⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨?_, ?_⟩⟩
    · intro hh; rw [hσe] at hh; exact hj.2.1 hh.symm
    · rw [hσe]; exact hj.2.2

private theorem ompInv_card_filter_ne_eq_two_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (σ : Equiv.Perm ι) (hσ : σ * σ = 1) (e : ι ≃ Fin (Fintype.card ι)) :
    (Finset.univ.filter (fun i => σ i ≠ i)).card =
      2 * (Finset.univ.filter (fun j => σ j ≠ j ∧ e j < e (σ j))).card := by
  classical
  let T : Finset ι := Finset.univ.filter (fun i => σ i ≠ i)
  let S : Finset ι := Finset.univ.filter (fun j => σ j ≠ j ∧ e j < e (σ j))
  let S' : Finset ι := Finset.univ.filter (fun j => σ j ≠ j ∧ e (σ j) < e j)
  have hT : T = S ∪ S' := by
    ext j
    simp only [T, S, S', Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro hj
      rcases lt_trichotomy (e j) (e (σ j)) with h | h | h
      · exact Or.inl ⟨hj, h⟩
      · exact absurd (e.injective h).symm hj
      · exact Or.inr ⟨hj, h⟩
    · rintro (⟨hj, _⟩ | ⟨hj, _⟩) <;> exact hj
  have hdisj : Disjoint S S' := by
    rw [Finset.disjoint_left]
    intro j hjS hjS'
    exact absurd (Finset.mem_filter.mp hjS).2.2
      (not_lt.mpr (Finset.mem_filter.mp hjS').2.2.le)
  have hScard : S'.card = S.card := by
    have h := ompInv_image_filter_lt_eq σ hσ e
    change (Finset.univ.filter (fun j => σ j ≠ j ∧ e (σ j) < e j)).card =
      (Finset.univ.filter (fun j => σ j ≠ j ∧ e j < e (σ j))).card
    rw [← h, Finset.card_image_of_injective _ σ.injective]
  have hcard : T.card = 2 * S.card := by
    rw [hT, Finset.card_union_of_disjoint hdisj, hScard]
    ring
  simpa only [T, S] using hcard

private theorem ompInv_two_mul_finrank_commSpace_funCongrLeft {ι : Type*} [Fintype ι]
    [DecidableEq ι] (σ : Equiv.Perm ι) (hσ : σ * σ = 1) :
    2 * finrank K (commSpace (LinearEquiv.funCongrLeft K K σ)) =
      (Finset.univ.filter (fun i => σ i ≠ i)).card := by
  classical
  let e := Fintype.equivFin ι
  let T : Finset ι := Finset.univ.filter (fun i => σ i ≠ i)
  let S : Finset ι := Finset.univ.filter (fun j => σ j ≠ j ∧ e j < e (σ j))
  let g : ι → (ι → K) := fun j => (Pi.single (σ j) (1:K) - Pi.single j 1 : ι → K)
  have hspan1 : commSpace (LinearEquiv.funCongrLeft K K σ) = Submodule.span K (Set.range g) := by
    rw [ompInv_commSpace_funCongrLeft_of_involution σ hσ]
  have hspan2 : Submodule.span K (Set.range g) =
      Submodule.span K (Set.range (fun i : S => g i)) :=
    ompInv_span_range_sub_single_eq_span_half (K := K) σ hσ e
  have hind : LinearIndependent K (fun i : S => g i) :=
    ompInv_linearIndependent_pair_sub_single (K := K) σ hσ e
  have hcard : T.card = 2 * S.card := by
    simpa only [T, S] using ompInv_card_filter_ne_eq_two_mul σ hσ e
  rw [hspan1, hspan2, finrank_span_eq_card hind]
  have : Fintype.card S = S.card := Fintype.card_coe S
  rw [this, hcard]

private theorem ompInv_spMonoPerm_inl_ne_iff {n : ℕ} {π : Equiv.Perm (Fin n)} {s : Fin n → ℤ}
    (a : Fin n) :
    (spMonoPerm π s (Sum.inl a) ≠ Sum.inl a ↔ π a ≠ a ∨ s a ≠ 1) := by
  rw [spMonoPerm_inl]
  by_cases h : s a = 1
  · rw [if_pos h]
    constructor
    · intro hh
      left
      intro hpa
      exact hh (congrArg Sum.inl hpa)
    · rintro (hpa | hsne)
      · intro hh
        exact hpa (Sum.inl.inj hh)
      · exact absurd h hsne
  · rw [if_neg h]
    exact ⟨fun _ => Or.inr h, fun _ => Sum.inr_ne_inl⟩

private theorem ompInv_spMonoPerm_inr_ne_iff {n : ℕ} {π : Equiv.Perm (Fin n)} {s : Fin n → ℤ}
    (a : Fin n) :
    (spMonoPerm π s (Sum.inr a) ≠ Sum.inr a ↔ π a ≠ a ∨ s a ≠ 1) := by
  rw [spMonoPerm_inr]
  by_cases h : s a = 1
  · rw [if_pos h]
    constructor
    · intro hh
      left
      intro hpa
      exact hh (congrArg Sum.inr hpa)
    · rintro (hpa | hsne)
      · intro hh
        exact hpa (Sum.inr_injective hh)
      · exact absurd h hsne
  · rw [if_neg h]
    exact ⟨fun _ => Or.inr h, fun _ => Sum.inl_ne_inr⟩

private theorem ompInv_filter_spMonoPerm_ne_eq_image {n : ℕ} {π : Equiv.Perm (Fin n)}
    {s : Fin n → ℤ} :
    (Finset.univ.filter (fun x : Fin n ⊕ Fin n => spMonoPerm π s x ≠ x)) =
      (Finset.univ.filter (fun a : Fin n => π a ≠ a ∨ s a ≠ 1)).image Sum.inl ∪
        (Finset.univ.filter (fun a : Fin n => π a ≠ a ∨ s a ≠ 1)).image Sum.inr := by
  ext x
  rcases x with a | a
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      Finset.mem_image]
    constructor
    · intro hx
      exact Or.inl ⟨a, (ompInv_spMonoPerm_inl_ne_iff a).mp hx, rfl⟩
    · rintro (⟨b, hb, hbeq⟩ | ⟨b, hb, hbeq⟩)
      · exact (ompInv_spMonoPerm_inl_ne_iff a).mpr (by rwa [Sum.inl_injective hbeq] at hb)
      · exact absurd hbeq Sum.inr_ne_inl
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      Finset.mem_image]
    constructor
    · intro hx
      exact Or.inr ⟨a, (ompInv_spMonoPerm_inr_ne_iff a).mp hx, rfl⟩
    · rintro (⟨b, hb, hbeq⟩ | ⟨b, hb, hbeq⟩)
      · exact absurd hbeq Sum.inl_ne_inr
      · exact (ompInv_spMonoPerm_inr_ne_iff a).mpr (by rwa [Sum.inr_injective hbeq] at hb)

private theorem ompInv_moved_spMonoPerm_card {n : ℕ} {π : Equiv.Perm (Fin n)}
    {s : Fin n → ℤ} :
    (Finset.univ.filter (fun x : Fin n ⊕ Fin n => spMonoPerm π s x ≠ x)).card =
      2 * (Finset.univ.filter (fun a : Fin n => π a ≠ a ∨ s a ≠ 1)).card := by
  classical
  let A : Finset (Fin n) := Finset.univ.filter (fun a => π a ≠ a ∨ s a ≠ 1)
  have hset : (Finset.univ.filter (fun x : Fin n ⊕ Fin n => spMonoPerm π s x ≠ x)) =
      A.image Sum.inl ∪ A.image Sum.inr := by
    simpa only [A] using ompInv_filter_spMonoPerm_ne_eq_image (π := π) (s := s)
  have hdisj : Disjoint (A.image Sum.inl) (A.image Sum.inr) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, _, hb⟩ := Finset.mem_image.mp hy
    exact Sum.inr_ne_inl hb
  rw [hset, Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ Sum.inl_injective,
    Finset.card_image_of_injective _ Sum.inr_injective]
  ring

private theorem ompInv_xor_one_lt_of_lt_two_mul {a j : ℕ} (h : a < 2 * j) : a ^^^ 1 < 2 * j := by
  rcases Nat.even_or_odd a with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · rw [Nat.xor_one_of_even (show Even (k + k) from ⟨k, rfl⟩)]; omega
  · rw [Nat.xor_one_of_odd (show Odd (2 * k + 1) from ⟨k, rfl⟩)]; omega

private def ompInv_pairMap (n j : ℕ) (h : 2 * j ≤ n) (a : Fin n) : Fin n :=
  if ha : a.val < 2 * j then
    ⟨a.val ^^^ 1, lt_of_lt_of_le (ompInv_xor_one_lt_of_lt_two_mul ha) h⟩
  else a

private theorem ompInv_pairMap_involutive (n j : ℕ) (h : 2 * j ≤ n) :
    Function.Involutive (ompInv_pairMap n j h) := by
  intro a
  by_cases ha : a.val < 2 * j
  · have h1 : a.val ^^^ 1 < 2 * j := ompInv_xor_one_lt_of_lt_two_mul ha
    simp only [ompInv_pairMap, dif_pos ha, dif_pos h1]
    apply Fin.ext
    simp only [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  · simp only [ompInv_pairMap, dif_neg ha]

private def ompInv_pairPerm (n j : ℕ) (h : 2 * j ≤ n) : Equiv.Perm (Fin n) :=
  Function.Involutive.toPerm (ompInv_pairMap n j h) (ompInv_pairMap_involutive n j h)

private theorem ompInv_pairPerm_apply_of_lt {n j : ℕ} (h : 2 * j ≤ n) {a : Fin n}
    (ha : a.val < 2 * j) :
    ompInv_pairPerm n j h a =
      ⟨a.val ^^^ 1, lt_of_lt_of_le (ompInv_xor_one_lt_of_lt_two_mul ha) h⟩ := by
  show ompInv_pairMap n j h a = _
  rw [ompInv_pairMap, dif_pos ha]

private theorem ompInv_pairPerm_apply_of_not_lt {n j : ℕ} (h : 2 * j ≤ n) {a : Fin n}
    (ha : ¬ a.val < 2 * j) : ompInv_pairPerm n j h a = a := by
  show ompInv_pairMap n j h a = a
  rw [ompInv_pairMap, dif_neg ha]

private def ompInv_cidx {n : ℕ} : Fin n ⊕ Fin n → Fin n
  | Sum.inl i => i
  | Sum.inr i => i

private theorem ompInv_quadPlus_funCongrLeft_of_pair {n : ℕ} {π : Equiv.Perm (Fin n ⊕ Fin n)}
    (hπ : ∀ i : Fin n, π (Sum.inr i) = (π (Sum.inl i)).swap)
    (v : Fin n ⊕ Fin n → K) :
    quadPlus n K (LinearEquiv.funCongrLeft K K π v) = quadPlus n K v := by
  let σ : Fin n → Fin n := fun i => ompInv_cidx (π (Sum.inl i))
  have hσinj : Function.Injective σ := by
    intro i j hij
    by_contra hne
    have hπne : π (Sum.inl i) ≠ π (Sum.inl j) :=
      fun h => hne (Sum.inl.inj (π.injective h))
    rcases hi : π (Sum.inl i) with a | a <;> rcases hj : π (Sum.inl j) with b | b
    · have hab : a = b := by simpa [σ, ompInv_cidx, hi, hj] using hij
      exact hπne (by rw [hi, hj, hab])
    · have hab : a = b := by simpa [σ, ompInv_cidx, hi, hj] using hij
      have h1 : π (Sum.inr j) = Sum.inl a := by rw [hπ j, hj, hab]; rfl
      have h2 : π (Sum.inl i) = π (Sum.inr j) := by rw [hi, h1]
      exact Sum.inl_ne_inr (π.injective h2)
    · have hab : a = b := by simpa [σ, ompInv_cidx, hi, hj] using hij
      have h1 : π (Sum.inr i) = Sum.inl b := by rw [hπ i, hi, hab]; rfl
      have h2 : π (Sum.inr i) = π (Sum.inl j) := by rw [h1, hj]
      exact Sum.inr_ne_inl (π.injective h2)
    · have hab : a = b := by simpa [σ, ompInv_cidx, hi, hj] using hij
      exact hπne (by rw [hi, hj, hab])
  have hσ : Function.Bijective σ :=
    ⟨hσinj, Finite.injective_iff_surjective.mp hσinj⟩
  let eσ : Fin n ≃ Fin n := Equiv.ofBijective σ hσ
  have hterm : ∀ i : Fin n, v (π (Sum.inl i)) * v (π (Sum.inr i)) =
      v (Sum.inl (σ i)) * v (Sum.inr (σ i)) := by
    intro i
    rcases hi : π (Sum.inl i) with a | a
    · have h2 : π (Sum.inr i) = Sum.inr a := by rw [hπ i, hi]; rfl
      have hσa : σ i = a := by simp [σ, ompInv_cidx, hi]
      simp only [h2, hσa]
    · have h2 : π (Sum.inr i) = Sum.inl a := by rw [hπ i, hi]; rfl
      have hσa : σ i = a := by simp [σ, ompInv_cidx, hi]
      simp only [h2, hσa]
      rw [mul_comm]
  calc quadPlus n K (LinearEquiv.funCongrLeft K K π v)
      = ∑ i, v (π (Sum.inl i)) * v (π (Sum.inr i)) := by
        rw [quadPlus_apply]
        simp only [LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply]
    _ = ∑ i, v (Sum.inl (σ i)) * v (Sum.inr (σ i)) := by
        exact Finset.sum_congr rfl fun i _ => hterm i
    _ = ∑ i, v (Sum.inl i) * v (Sum.inr i) :=
        Equiv.sum_comp eσ (fun k : Fin n => v (Sum.inl k) * v (Sum.inr k))
    _ = quadPlus n K v := by rw [quadPlus_apply]

private theorem ompInv_toMatrix'_funCongrLeft {σ : Type*} [Fintype σ] [DecidableEq σ]
    (e : Equiv.Perm σ) :
    LinearMap.toMatrix' (LinearEquiv.funCongrLeft K K e : (σ → K) →ₗ[K] σ → K) =
      Equiv.Perm.permMatrix K e := by
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_toMatrix']
  apply LinearMap.ext
  intro v
  rw [Matrix.toLin'_apply, Matrix.permMatrix_mulVec]
  rfl

private def ompInv_sa (n : ℕ) : Fin n → ℤ := fun a => if a.val < 2 then -1 else 1

private theorem ompInv_spIsSign_sa (n : ℕ) : SpIsSign (ompInv_sa n) := fun a => by
  unfold ompInv_sa
  split_ifs <;> norm_num

private theorem ompInv_xor_one_lt_two {a : ℕ} : a ^^^ 1 < 2 ↔ a < 2 := by
  rcases Nat.even_or_odd a with ⟨k, hk⟩ | ⟨k, hk⟩
  · rw [hk, Nat.xor_one_of_even (show Even (k + k) from ⟨k, rfl⟩)]
    omega
  · rw [hk, Nat.xor_one_of_odd (show Odd (2 * k + 1) from ⟨k, rfl⟩)]
    omega

private theorem ompInv_two_le_xor_one {a : ℕ} : 2 ≤ a ^^^ 1 ↔ 2 ≤ a := by
  rcases Nat.even_or_odd a with ⟨k, hk⟩ | ⟨k, hk⟩
  · rw [hk, Nat.xor_one_of_even (show Even (k + k) from ⟨k, rfl⟩)]
    omega
  · rw [hk, Nat.xor_one_of_odd (show Odd (2 * k + 1) from ⟨k, rfl⟩)]
    omega

private theorem ompInv_sa_pairPerm {n r : ℕ} (h : 2 * r ≤ n) (c : Fin n) :
    ompInv_sa n (ompInv_pairPerm n r h c) = ompInv_sa n c := by
  unfold ompInv_sa
  by_cases hc : c.val < 2 * r
  · rw [ompInv_pairPerm_apply_of_lt h hc]
    by_cases h2 : c.val < 2
    · rw [if_pos (ompInv_xor_one_lt_two.mpr h2), if_pos h2]
    · rw [if_neg (fun hh => h2 (ompInv_xor_one_lt_two.mp hh)), if_neg h2]
  · rw [ompInv_pairPerm_apply_of_not_lt h hc]

private def ompInv_pairMapC (n r : ℕ) (h : 2 * r ≤ n) (a : Fin n) : Fin n :=
  if ha : 2 ≤ a.val ∧ a.val < 2 * r then
    ⟨a.val ^^^ 1, lt_of_lt_of_le (ompInv_xor_one_lt_of_lt_two_mul ha.2) h⟩
  else a

private theorem ompInv_pairMapC_apply_of_lt {n r : ℕ} (h : 2 * r ≤ n) {a : Fin n}
    (ha : 2 ≤ a.val ∧ a.val < 2 * r) :
    ompInv_pairMapC n r h a =
      ⟨a.val ^^^ 1, lt_of_lt_of_le (ompInv_xor_one_lt_of_lt_two_mul ha.2) h⟩ :=
  dif_pos ha

private theorem ompInv_pairMapC_apply_of_not_lt {n r : ℕ} (h : 2 * r ≤ n) {a : Fin n}
    (ha : ¬ (2 ≤ a.val ∧ a.val < 2 * r)) : ompInv_pairMapC n r h a = a :=
  dif_neg ha

private theorem ompInv_pairMapC_involutive (n r : ℕ) (h : 2 * r ≤ n) :
    Function.Involutive (ompInv_pairMapC n r h) := by
  intro a
  by_cases ha : 2 ≤ a.val ∧ a.val < 2 * r
  · have hx : a.val ^^^ 1 < 2 * r := ompInv_xor_one_lt_of_lt_two_mul ha.2
    have hy : 2 ≤ a.val ^^^ 1 := (ompInv_two_le_xor_one).mpr ha.1
    rw [ompInv_pairMapC_apply_of_lt h ha, ompInv_pairMapC_apply_of_lt h ⟨hy, hx⟩]
    apply Fin.ext
    simp only [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  · rw [ompInv_pairMapC_apply_of_not_lt h ha]
    exact ompInv_pairMapC_apply_of_not_lt h ha

private def ompInv_pairPermC (n r : ℕ) (h : 2 * r ≤ n) : Equiv.Perm (Fin n) :=
  Function.Involutive.toPerm (ompInv_pairMapC n r h) (ompInv_pairMapC_involutive n r h)

private theorem ompInv_pairPermC_apply_of_lt {n r : ℕ} (h : 2 * r ≤ n) {a : Fin n}
    (ha : 2 ≤ a.val ∧ a.val < 2 * r) :
    ompInv_pairPermC n r h a =
      ⟨a.val ^^^ 1, lt_of_lt_of_le (ompInv_xor_one_lt_of_lt_two_mul ha.2) h⟩ := by
  show ompInv_pairMapC n r h a = _
  rw [ompInv_pairMapC, dif_pos ha]

private theorem ompInv_pairPermC_apply_of_not_lt {n r : ℕ} (h : 2 * r ≤ n) {a : Fin n}
    (ha : ¬ (2 ≤ a.val ∧ a.val < 2 * r)) : ompInv_pairPermC n r h a = a := by
  show ompInv_pairMapC n r h a = a
  rw [ompInv_pairMapC, dif_neg ha]

private theorem ompInv_pairPermC_mul_self {n r : ℕ} (h : 2 * r ≤ n) :
    ompInv_pairPermC n r h * ompInv_pairPermC n r h = 1 := by
  apply Equiv.ext
  intro a
  exact ompInv_pairMapC_involutive n r h a

private theorem ompInv_sa_pairPermC {n r : ℕ} (h : 2 * r ≤ n) (c : Fin n) :
    ompInv_sa n (ompInv_pairPermC n r h c) = ompInv_sa n c := by
  unfold ompInv_sa
  by_cases hc : 2 ≤ c.val ∧ c.val < 2 * r
  · rw [ompInv_pairPermC_apply_of_lt h hc]
    by_cases h2 : c.val < 2
    · rw [if_pos (ompInv_xor_one_lt_two.mpr h2), if_pos h2]
    · rw [if_neg (fun hh => h2 (ompInv_xor_one_lt_two.mp hh)), if_neg h2]
  · rw [ompInv_pairPermC_apply_of_not_lt h hc]

private theorem ompInv_spMonoPerm_sq {n : ℕ} {π : Equiv.Perm (Fin n)} {s : Fin n → ℤ}
    (hs : SpIsSign s) (hπ : π * π = 1) (hinv : ∀ c, s c * s (π c) = 1) :
    spMonoPerm π s * spMonoPerm π s = 1 := by
  rw [← spMonoPerm_mul hs hs]
  have h1 : (fun c => s c * s (π c)) = 1 := funext hinv
  rw [hπ, h1, spMonoPerm_one]

private theorem ompInv_finrank_commSpace_spMonoPerm {n : ℕ} {π : Equiv.Perm (Fin n)}
    {s : Fin n → ℤ} (hsgn : SpIsSign s) (hπ : π * π = 1) (hsym : ∀ a, s (π a) = s a) :
    finrank K (commSpace (LinearEquiv.funCongrLeft K K (spMonoPerm π s))) =
      (Finset.univ.filter (fun a : Fin n => π a ≠ a ∨ s a ≠ 1)).card := by
  have hs2 : spMonoPerm π s * spMonoPerm π s = 1 :=
    ompInv_spMonoPerm_sq hsgn hπ (fun c => by rw [hsym c, SpIsSign.mul_self hsgn c])
  have h1 := ompInv_two_mul_finrank_commSpace_funCongrLeft (K := K) (spMonoPerm π s) hs2
  have h2 := ompInv_moved_spMonoPerm_card (π := π) (s := s)
  omega

private theorem ompInv_pairPerm_mul_self {n r : ℕ} (h : 2 * r ≤ n) :
    ompInv_pairPerm n r h * ompInv_pairPerm n r h = 1 := by
  apply Equiv.ext
  intro a
  exact ompInv_pairMap_involutive n r h a

private def ompInv_e1 {n r : ℕ} (h : 2 * r ≤ n) : Equiv.Perm (Fin n ⊕ Fin n) :=
  spMonoPerm (ompInv_pairPerm n r h) 1

private def ompInv_e2 {n r : ℕ} (h : 2 * r ≤ n) : Equiv.Perm (Fin n ⊕ Fin n) :=
  spMonoPerm (ompInv_pairPerm n r h) (ompInv_sa n)

private def ompInv_ec {n r : ℕ} (h : 2 * r ≤ n) : Equiv.Perm (Fin n ⊕ Fin n) :=
  spMonoPerm (ompInv_pairPermC n r h) (ompInv_sa n)

private theorem ompInv_e1_mul_self {n r : ℕ} (h : 2 * r ≤ n) :
    ompInv_e1 h * ompInv_e1 h = 1 :=
  ompInv_spMonoPerm_sq (spIsSign_one) (ompInv_pairPerm_mul_self h)
    (fun c => by simp)

private theorem ompInv_e2_mul_self {n r : ℕ} (h : 2 * r ≤ n) :
    ompInv_e2 h * ompInv_e2 h = 1 :=
  ompInv_spMonoPerm_sq (ompInv_spIsSign_sa n) (ompInv_pairPerm_mul_self h)
    (fun c => by rw [ompInv_sa_pairPerm h, SpIsSign.mul_self (ompInv_spIsSign_sa n) c])

private theorem ompInv_ec_mul_self {n r : ℕ} (h : 2 * r ≤ n) :
    ompInv_ec h * ompInv_ec h = 1 :=
  ompInv_spMonoPerm_sq (ompInv_spIsSign_sa n) (ompInv_pairPermC_mul_self h)
    (fun c => by rw [ompInv_sa_pairPermC h, SpIsSign.mul_self (ompInv_spIsSign_sa n) c])

private theorem ompInv_e1_inl {n r : ℕ} (h : 2 * r ≤ n) (a : Fin n) :
    ompInv_e1 h (Sum.inl a) = Sum.inl (ompInv_pairPerm n r h a) := by
  unfold ompInv_e1
  rw [spMonoPerm_inl]
  simp

private theorem ompInv_ec_inl {n r : ℕ} (h : 2 * r ≤ n) (a : Fin n) :
    ompInv_ec h (Sum.inl a) =
      if ompInv_sa n a = 1 then Sum.inl (ompInv_pairPermC n r h a)
      else Sum.inr (ompInv_pairPermC n r h a) := by
  unfold ompInv_ec
  rw [spMonoPerm_inl]

private theorem ompInv_funCongrLeft_one {ι : Type*} :
    LinearEquiv.funCongrLeft K K (1 : Equiv.Perm ι) = 1 := rfl

private theorem ompInv_funCongrLeft_injective {ι : Type*} [DecidableEq ι] :
    Function.Injective (fun e : Equiv.Perm ι => LinearEquiv.funCongrLeft K K e) := by
  intro e f h
  apply inv_injective
  ext x
  have hx := congrArg (fun L : (ι → K) ≃ₗ[K] (ι → K) => L (Pi.single x (1:K))) h
  simp only [ompInv_funCongrLeft_single] at hx
  by_cases h' : e.symm x = f.symm x
  · exact h'
  · have hc := congrFun hx (e.symm x)
    simp only [Pi.single_apply, if_true, if_neg h'] at hc
    exact (one_ne_zero hc).elim

private theorem ompInv_orderOf_funCongrLeft {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : Equiv.Perm ι) (he : e * e = 1) (he1 : e ≠ 1) :
    orderOf (LinearEquiv.funCongrLeft K K e) = 2 := by
  have hdvd : orderOf (LinearEquiv.funCongrLeft K K e) ∣ 2 :=
    orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two, ompInv_funCongrLeft_mul, he,
      ompInv_funCongrLeft_one])
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) (fun h1 =>
      he1 (ompInv_funCongrLeft_injective (by simpa [ompInv_funCongrLeft_one] using h1)))
  · exact h

private theorem ompInv_pairPerm_ne_iff {n r : ℕ} (h : 2 * r ≤ n) (a : Fin n) :
    ompInv_pairPerm n r h a ≠ a ↔ a.val < 2 * r := by
  constructor
  · intro hne
    by_contra hge
    exact hne (ompInv_pairPerm_apply_of_not_lt h hge)
  · intro hlt
    rw [ompInv_pairPerm_apply_of_lt h hlt]
    intro heq
    have h2 := congrArg Fin.val heq
    dsimp only at h2
    rcases Nat.even_or_odd a.val with ⟨k, hk⟩ | ⟨k, hk⟩
    · rw [hk, Nat.xor_one_of_even (show Even (k + k) from ⟨k, rfl⟩)] at h2; omega
    · rw [hk, Nat.xor_one_of_odd (show Odd (2 * k + 1) from ⟨k, rfl⟩)] at h2; omega

private theorem ompInv_pairPermC_ne_iff {n r : ℕ} (h : 2 * r ≤ n) (a : Fin n) :
    ompInv_pairPermC n r h a ≠ a ↔ 2 ≤ a.val ∧ a.val < 2 * r := by
  constructor
  · intro hne
    by_contra hnot
    exact hne (ompInv_pairPermC_apply_of_not_lt h hnot)
  · intro hlt
    rw [ompInv_pairPermC_apply_of_lt h hlt]
    intro heq
    have h2 := congrArg Fin.val heq
    dsimp only at h2
    rcases Nat.even_or_odd a.val with ⟨k, hk⟩ | ⟨k, hk⟩
    · rw [hk, Nat.xor_one_of_even (show Even (k + k) from ⟨k, rfl⟩)] at h2; omega
    · rw [hk, Nat.xor_one_of_odd (show Odd (2 * k + 1) from ⟨k, rfl⟩)] at h2; omega

private theorem ompInv_sa_eq_one {n : ℕ} {a : Fin n} (ha : ¬ a.val < 2) :
    ompInv_sa n a = 1 := by
  unfold ompInv_sa
  rw [if_neg ha]

private theorem ompInv_sa_ne_one {n : ℕ} {a : Fin n} (ha : a.val < 2) :
    ompInv_sa n a ≠ 1 := by
  unfold ompInv_sa
  rw [if_pos ha]
  norm_num

private theorem ompInv_sa_ne_one_iff {n : ℕ} (a : Fin n) :
    ompInv_sa n a ≠ 1 ↔ a.val < 2 := by
  constructor
  · intro h; by_contra hge; exact h (ompInv_sa_eq_one hge)
  · exact ompInv_sa_ne_one

private theorem ompInv_card_fin_lt {n m : ℕ} (h : m ≤ n) :
    (Finset.univ.filter (fun a : Fin n => a.val < m)).card = m := by
  rw [show (Finset.univ.filter (fun a : Fin n => a.val < m)) =
      (Finset.univ.filter (fun a : Fin n => a < m)) from by
    apply Finset.filter_congr; intro a _; rfl]
  rw [Fin.card_filter_val_lt, Nat.min_eq_right h]

private theorem ompInv_e1_mem_orthogonalGroup {n r : ℕ} (h : 2 * r ≤ n) :
    LinearEquiv.funCongrLeft K K (ompInv_e1 h) ∈
      TauCeti.QuadraticMap.orthogonalGroup (quadPlus n K) := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro v
  exact ompInv_quadPlus_funCongrLeft_of_pair (fun i => by
    simpa [ompInv_e1] using spMonoPerm_swap (ompInv_pairPerm n r h) 1 (Sum.inl i)) v

private theorem ompInv_ec_mem_orthogonalGroup {n r : ℕ} (h : 2 * r ≤ n) :
    LinearEquiv.funCongrLeft K K (ompInv_ec h) ∈
      TauCeti.QuadraticMap.orthogonalGroup (quadPlus n K) := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro v
  exact ompInv_quadPlus_funCongrLeft_of_pair (fun i => by
    simpa [ompInv_ec] using spMonoPerm_swap (ompInv_pairPermC n r h) (ompInv_sa n) (Sum.inl i)) v

private theorem ompInv_e1_ne_one {n r : ℕ} (h : 2 * r ≤ n) (hr : 1 ≤ r) :
    ompInv_e1 h ≠ 1 := by
  intro h1
  have hh := congrFun (congrArg DFunLike.coe h1) (Sum.inl ⟨0, by omega⟩)
  rw [ompInv_e1_inl, ompInv_pairPerm_apply_of_lt h (by show (0:ℕ) < 2 * r; omega)] at hh
  simp only [Equiv.Perm.one_apply] at hh
  have h2 := congrArg Fin.val (Sum.inl.inj hh)
  dsimp only at h2
  norm_num at h2

private theorem ompInv_ec_ne_one {n r : ℕ} (h : 2 * r ≤ n) (hr : 1 ≤ r) :
    ompInv_ec h ≠ 1 := by
  intro h1
  have hh := congrFun (congrArg DFunLike.coe h1) (Sum.inl ⟨0, by omega⟩)
  rw [ompInv_ec_inl, if_neg (ompInv_sa_ne_one (by show (0:ℕ) < 2; omega)),
    ompInv_pairPermC_apply_of_not_lt h (by show ¬ (2 ≤ (0:ℕ) ∧ (0:ℕ) < 2 * r); omega)]
    at hh
  simp only [Equiv.Perm.one_apply] at hh
  exact Sum.inr_ne_inl hh

private theorem ompInv_orderOf_e1 {n r : ℕ} (h : 2 * r ≤ n) (hr : 1 ≤ r) :
    orderOf (LinearEquiv.funCongrLeft K K (ompInv_e1 h)) = 2 :=
  ompInv_orderOf_funCongrLeft _ (ompInv_e1_mul_self h) (ompInv_e1_ne_one h hr)

private theorem ompInv_orderOf_ec {n r : ℕ} (h : 2 * r ≤ n) (hr : 1 ≤ r) :
    orderOf (LinearEquiv.funCongrLeft K K (ompInv_ec h)) = 2 :=
  ompInv_orderOf_funCongrLeft _ (ompInv_ec_mul_self h) (ompInv_ec_ne_one h hr)

private theorem ompInv_finrank_e1 {n r : ℕ} (h : 2 * r ≤ n) :
    finrank K (commSpace (LinearEquiv.funCongrLeft K K (ompInv_e1 h))) = 2 * r := by
  change finrank K (commSpace (LinearEquiv.funCongrLeft K K
    (spMonoPerm (ompInv_pairPerm n r h) 1))) = 2 * r
  rw [ompInv_finrank_commSpace_spMonoPerm (spIsSign_one) (ompInv_pairPerm_mul_self h)
    (fun a => rfl)]
  rw [show (Finset.univ.filter (fun a : Fin n =>
      ompInv_pairPerm n r h a ≠ a ∨ (1 : Fin n → ℤ) a ≠ 1)) =
      (Finset.univ.filter (fun a : Fin n => a.val < 2 * r)) from by
    apply Finset.filter_congr
    intro a _
    rw [ompInv_pairPerm_ne_iff h a]
    exact ⟨fun hh => hh.elim id (fun h1 => absurd rfl h1), fun hh => Or.inl hh⟩]
  exact ompInv_card_fin_lt h

private theorem ompInv_finrank_ec {n r : ℕ} (h : 2 * r ≤ n) (hr : 1 ≤ r) :
    finrank K (commSpace (LinearEquiv.funCongrLeft K K (ompInv_ec h))) = 2 * r := by
  change finrank K (commSpace (LinearEquiv.funCongrLeft K K
    (spMonoPerm (ompInv_pairPermC n r h) (ompInv_sa n)))) = 2 * r
  rw [ompInv_finrank_commSpace_spMonoPerm (ompInv_spIsSign_sa n) (ompInv_pairPermC_mul_self h)
    (ompInv_sa_pairPermC h)]
  rw [show (Finset.univ.filter (fun a : Fin n =>
      ompInv_pairPermC n r h a ≠ a ∨ ompInv_sa n a ≠ 1)) =
      (Finset.univ.filter (fun a : Fin n => a.val < 2 * r)) from by
    apply Finset.filter_congr
    intro a _
    rw [ompInv_pairPermC_ne_iff h a]
    constructor
    · rintro (⟨-, hlt⟩ | hsa)
      · exact hlt
      · exact lt_of_lt_of_le ((ompInv_sa_ne_one_iff a).mp hsa) (by omega)
    · intro hlt
      by_cases h2 : a.val < 2
      · exact Or.inr ((ompInv_sa_ne_one_iff a).mpr h2)
      · exact Or.inl ⟨by omega, hlt⟩]
  exact ompInv_card_fin_lt h

private theorem ompInv_polar_spMonoPerm_one [CharP K 2] {n : ℕ} {π : Equiv.Perm (Fin n)}
    (hπ : π * π = 1) (v : Fin n ⊕ Fin n → K) :
    polar (quadPlus n K) (LinearEquiv.funCongrLeft K K (spMonoPerm π 1) v) v = 0 := by
  have hπi : ∀ i, π (π i) = i := fun i => by rw [← Equiv.Perm.mul_apply, hπ]; rfl
  have h1 : ∀ a, LinearEquiv.funCongrLeft K K (spMonoPerm π 1) v (Sum.inl a) =
      v (Sum.inl (π a)) := by
    intro a
    rw [LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply, spMonoPerm_inl]
    simp
  have h2 : ∀ a, LinearEquiv.funCongrLeft K K (spMonoPerm π 1) v (Sum.inr a) =
      v (Sum.inr (π a)) := by
    intro a
    rw [LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply, spMonoPerm_inr]
    simp
  rw [polar_quadPlus]
  rw [Finset.sum_congr rfl fun i _ => by rw [h1 i, h2 i]]
  set S := ∑ i : Fin n, v (Sum.inl i) * v (Sum.inr (π i)) with hS
  have hre : (∑ i : Fin n, v (Sum.inl (π i)) * v (Sum.inr i)) = S := by
    rw [hS, ← Equiv.sum_comp π (fun i => v (Sum.inl i) * v (Sum.inr (π i)))]
    exact Finset.sum_congr rfl fun i _ => by rw [hπi i]
  rw [Finset.sum_add_distrib, hre, ← hS]
  exact CharTwo.add_self_eq_zero S

private theorem ompInv_suzukiLetter_e1 [CharP K 2] {n r : ℕ} (h : 2 * r ≤ n) :
    suzukiLetter (quadPlus n K) (LinearEquiv.funCongrLeft K K (ompInv_e1 h)) = .a := by
  have hπ : ompInv_pairPerm n r h * ompInv_pairPerm n r h = 1 := ompInv_pairPerm_mul_self h
  have hO : LinearEquiv.funCongrLeft K K (ompInv_e1 h) ∈
      TauCeti.QuadraticMap.orthogonalGroup (quadPlus n K) :=
    ompInv_e1_mem_orthogonalGroup (n := n) (r := r) h
  refine suzukiLetter_eq_a_iff.mpr ⟨?_, ?_⟩
  · rw [ompInv_finrank_e1 h]
    exact ⟨r, by ring⟩
  · intro x hx
    obtain ⟨v, rfl⟩ := mem_commSpace.mp hx
    change quadPlus n K (LinearEquiv.funCongrLeft K K (ompInv_e1 h) v - v) = 0
    rw [map_sub_eq_polar hO v]
    exact ompInv_polar_spMonoPerm_one hπ v

private theorem ompInv_quadPlus_sub_single {n : ℕ} (hn : 0 < n) :
    quadPlus n K (Pi.single (Sum.inr ⟨0, hn⟩) (1:K) - Pi.single (Sum.inl ⟨0, hn⟩) 1) = -1 := by
  rw [quadPlus_apply]
  rw [Finset.sum_eq_single (⟨0, hn⟩ : Fin n)]
  · simp
  · intro b _ hb
    have hb' : (Sum.inl b : Fin n ⊕ Fin n) ≠ Sum.inl (⟨0, hn⟩ : Fin n) :=
      fun h => hb (Sum.inl_injective h)
    have hx : (Pi.single (Sum.inr (⟨0, hn⟩ : Fin n)) (1:K)
        - Pi.single (Sum.inl (⟨0, hn⟩ : Fin n)) 1 : Fin n ⊕ Fin n → K) (Sum.inl b) = 0 := by
      simp only [Pi.sub_apply, Pi.single_apply]
      rw [if_neg (Sum.inl_ne_inr), if_neg hb']
      ring
    rw [hx, zero_mul]
  · intro hm
    exact absurd (Finset.mem_univ (⟨0, hn⟩ : Fin n)) hm

private theorem ompInv_suzukiLetter_ec [CharP K 2] {n r : ℕ} (h : 2 * r ≤ n) (hr : 1 ≤ r) :
    suzukiLetter (quadPlus n K) (LinearEquiv.funCongrLeft K K (ompInv_ec h)) = .c := by
  have hn0 : 0 < n := by omega
  refine suzukiLetter_eq_c_iff.mpr ⟨?_, ?_⟩
  · rw [ompInv_finrank_ec h hr]
    exact ⟨r, by ring⟩
  · refine ⟨LinearEquiv.funCongrLeft K K (ompInv_ec h) (Pi.single (Sum.inl ⟨0, hn0⟩) 1)
        - Pi.single (Sum.inl ⟨0, hn0⟩) 1, sub_mem_commSpace _ _, ?_⟩
    have hinv : (ompInv_ec h).symm = ompInv_ec h :=
      inv_eq_of_mul_eq_one_right (ompInv_ec_mul_self h)
    have hfix : ompInv_ec h (Sum.inl ⟨0, hn0⟩) = Sum.inr ⟨0, hn0⟩ := by
      rw [ompInv_ec_inl, if_neg (ompInv_sa_ne_one (by show (0:ℕ) < 2; omega)),
        ompInv_pairPermC_apply_of_not_lt h
          (by show ¬ (2 ≤ (0:ℕ) ∧ (0:ℕ) < 2 * r); omega)]
    have hz : LinearEquiv.funCongrLeft K K (ompInv_ec h) (Pi.single (Sum.inl ⟨0, hn0⟩) 1) =
        Pi.single (Sum.inr ⟨0, hn0⟩) 1 := by
      rw [ompInv_funCongrLeft_single, hinv, hfix]
    rw [hz, ompInv_quadPlus_sub_single hn0]
    exact fun h0 => one_ne_zero (neg_eq_zero.mp h0)

private def ompInv_d {n : ℕ} (hn : 2 ≤ n) : Equiv.Perm (Fin n ⊕ Fin n) :=
  spMonoPerm 1 (spSgn (⟨1, by omega⟩ : Fin n))

private theorem ompInv_d_mul_self {n : ℕ} (hn : 2 ≤ n) :
    ompInv_d hn * ompInv_d hn = 1 := by
  unfold ompInv_d
  exact ompInv_spMonoPerm_sq (spIsSign_spSgn _) (by simp) (fun c =>
    SpIsSign.mul_self (spIsSign_spSgn _) c)

private theorem ompInv_d_mem_orthogonalGroup {n : ℕ} (hn : 2 ≤ n) :
    LinearEquiv.funCongrLeft K K (ompInv_d hn) ∈
      TauCeti.QuadraticMap.orthogonalGroup (quadPlus n K) := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro v
  exact ompInv_quadPlus_funCongrLeft_of_pair (fun i => by
    simpa [ompInv_d] using
      spMonoPerm_swap (1 : Equiv.Perm (Fin n)) (spSgn (⟨1, by omega⟩ : Fin n)) (Sum.inl i)) v

private theorem ompInv_d_finrank {n : ℕ} (hn : 2 ≤ n) :
    finrank K (commSpace (LinearEquiv.funCongrLeft K K (ompInv_d hn))) = 1 := by
  have hn1 : 1 < n := by omega
  change finrank K (commSpace (LinearEquiv.funCongrLeft K K
    (spMonoPerm (1 : Equiv.Perm (Fin n)) (spSgn (⟨1, hn1⟩ : Fin n))))) = 1
  rw [ompInv_finrank_commSpace_spMonoPerm (spIsSign_spSgn _) (by simp) (fun c => by simp)]
  rw [show (Finset.univ.filter (fun a : Fin n =>
      (1 : Equiv.Perm (Fin n)) a ≠ a ∨ spSgn (⟨1, hn1⟩ : Fin n) a ≠ 1)) =
      {⟨1, hn1⟩} from by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro (h | h)
      · exact absurd rfl h
      · by_contra hx
        exact h (by rw [spSgn, if_neg hx])
    · intro hx
      right
      rw [hx, spSgn, if_pos rfl]
      norm_num]
  simp

private theorem ompInv_sgn_mul_sgn_pairPerm {n r : ℕ} (h : 2 * r ≤ n) (hr : 1 ≤ r) :
    (fun c : Fin n => spSgn (⟨1, by omega⟩ : Fin n) c *
      spSgn (⟨1, by omega⟩ : Fin n) (ompInv_pairPerm n r h c)) = ompInv_sa n := by
  funext c
  rw [ompInv_sa]
  by_cases hc : c.val < 2
  · rw [if_pos hc]
    have hc' : c.val = 0 ∨ c.val = 1 := by omega
    rcases hc' with h0 | h1
    · have hc0 : c = (⟨0, by omega⟩ : Fin n) := Fin.ext h0
      rw [hc0]
      rw [ompInv_pairPerm_apply_of_lt h (by show (0:ℕ) < 2 * r; omega)]
      norm_num [spSgn]
    · have hc1 : c = (⟨1, by omega⟩ : Fin n) := Fin.ext h1
      rw [hc1]
      rw [ompInv_pairPerm_apply_of_lt h (by show (1:ℕ) < 2 * r; omega)]
      norm_num [spSgn]
  · rw [if_neg hc]
    have hge : 2 ≤ (ompInv_pairPerm n r h c).val := by
      by_cases hlt : c.val < 2 * r
      · rw [ompInv_pairPerm_apply_of_lt h hlt]
        dsimp only
        rcases Nat.even_or_odd c.val with ⟨k, hk⟩ | ⟨k, hk⟩
        · rw [hk, Nat.xor_one_of_even (show Even (k + k) from ⟨k, rfl⟩)]; omega
        · rw [hk, Nat.xor_one_of_odd (show Odd (2 * k + 1) from ⟨k, rfl⟩)]; omega
      · rw [ompInv_pairPerm_apply_of_not_lt h hlt]; omega
    have hc1 : c ≠ (⟨1, by omega⟩ : Fin n) := by
      intro hh
      have := congrArg Fin.val hh
      dsimp only at this
      omega
    have hπ1 : ompInv_pairPerm n r h c ≠ (⟨1, by omega⟩ : Fin n) := by
      intro hh
      have := congrArg Fin.val hh
      dsimp only at this
      omega
    have hσc : spSgn (⟨1, by omega⟩ : Fin n) c = 1 := by
      unfold spSgn; rw [if_neg hc1]
    have hσπ : spSgn (⟨1, by omega⟩ : Fin n) (ompInv_pairPerm n r h c) = 1 := by
      unfold spSgn; rw [if_neg hπ1]
    rw [hσc, hσπ, one_mul]

private theorem ompInv_e2_eq_conj {n r : ℕ} (h : 2 * r ≤ n) (hr : 1 ≤ r) :
    ompInv_e2 h = ompInv_d (by omega) * ompInv_e1 h * ompInv_d (by omega) := by
  have hn2 : 2 ≤ n := by omega
  have hσ : SpIsSign (spSgn (⟨1, by omega⟩ : Fin n)) := spIsSign_spSgn _
  have hstep1 : ompInv_d hn2 * ompInv_e1 h = spMonoPerm (ompInv_pairPerm n r h)
      (fun c => spSgn (⟨1, by omega⟩ : Fin n) (ompInv_pairPerm n r h c)) := by
    unfold ompInv_d ompInv_e1
    rw [← spMonoPerm_mul (π₁ := 1) (π₂ := ompInv_pairPerm n r h) (s₁ := spSgn _)
      (s₂ := (1 : Fin n → ℤ)) hσ spIsSign_one]
    simp
  rw [hstep1]
  have hstep2 : spMonoPerm (ompInv_pairPerm n r h)
        (fun c => spSgn (⟨1, by omega⟩ : Fin n) (ompInv_pairPerm n r h c)) *
      ompInv_d hn2 = spMonoPerm (ompInv_pairPerm n r h)
        (fun c => spSgn (⟨1, by omega⟩ : Fin n) c *
          spSgn (⟨1, by omega⟩ : Fin n) (ompInv_pairPerm n r h c)) := by
    unfold ompInv_d
    rw [← spMonoPerm_mul (π₁ := ompInv_pairPerm n r h) (π₂ := 1)
      (s₁ := fun c => spSgn (⟨1, by omega⟩ : Fin n) (ompInv_pairPerm n r h c))
      (s₂ := spSgn (⟨1, by omega⟩ : Fin n))
      (fun c => spIsSign_spSgn _ _) hσ]
    simp
  rw [hstep2]
  unfold ompInv_e2
  rw [ompInv_sgn_mul_sgn_pairPerm h hr]

private theorem ompInv_prod_spSgn {n : ℕ} (i : Fin n) :
    ∏ a : Fin n, spSgn i a = -1 := by
  simp [spSgn]

private theorem ompInv_prod_sa {n : ℕ} (hn : 2 ≤ n) :
    ∏ a : Fin n, ompInv_sa n a = 1 := by
  have hsa : ∀ a : Fin n, ompInv_sa n a =
      spSgn (⟨0, by omega⟩ : Fin n) a * spSgn (⟨1, by omega⟩ : Fin n) a := by
    intro a
    unfold ompInv_sa spSgn
    by_cases h : a.val < 2
    · rw [if_pos h]
      have ha : a = (⟨0, by omega⟩ : Fin n) ∨ a = (⟨1, by omega⟩ : Fin n) := by
        rcases (by omega : a.val = 0 ∨ a.val = 1) with h0 | h1
        · exact Or.inl (Fin.ext h0)
        · exact Or.inr (Fin.ext h1)
      rcases ha with h0 | h1
      · rw [h0]; norm_num
      · rw [h1]; norm_num
    · rw [if_neg h]
      have h0 : a ≠ (⟨0, by omega⟩ : Fin n) := by
        intro hh; have := congrArg Fin.val hh; dsimp only at this; omega
      have h1 : a ≠ (⟨1, by omega⟩ : Fin n) := by
        intro hh; have := congrArg Fin.val hh; dsimp only at this; omega
      rw [if_neg h0, if_neg h1, one_mul]
  calc ∏ a : Fin n, ompInv_sa n a
      = ∏ a : Fin n, (spSgn (⟨0, by omega⟩ : Fin n) a * spSgn (⟨1, by omega⟩ : Fin n) a) :=
        Finset.prod_congr rfl fun a _ => hsa a
    _ = (∏ a : Fin n, spSgn (⟨0, by omega⟩ : Fin n) a) *
        (∏ a : Fin n, spSgn (⟨1, by omega⟩ : Fin n) a) := Finset.prod_mul_distrib
    _ = (-1) * (-1) := by rw [ompInv_prod_spSgn, ompInv_prod_spSgn]
    _ = 1 := by ring

private theorem ompInv_shape_e1 {n r : ℕ} (h : 2 * r ≤ n) (hr : 1 ≤ r) :
    (ompInv_pairPerm n r h ⟨0, by omega⟩ = ⟨1, by omega⟩ ∧
      ompInv_pairPerm n r h ⟨1, by omega⟩ = ⟨0, by omega⟩ ∧
      (1 : Fin n → ℤ) ⟨0, by omega⟩ = (1 : Fin n → ℤ) ⟨1, by omega⟩) := by
  refine ⟨?_, ?_, rfl⟩
  · rw [ompInv_pairPerm_apply_of_lt h (by show (0:ℕ) < 2 * r; omega)]
    norm_num
  · rw [ompInv_pairPerm_apply_of_lt h (by show (1:ℕ) < 2 * r; omega)]
    norm_num

private theorem ompInv_shape_ec {n r : ℕ} (h : 2 * r ≤ n) (hr : 1 ≤ r) :
    (ompInv_pairPermC n r h ⟨0, by omega⟩ = ⟨0, by omega⟩ ∧
      ompInv_sa n ⟨0, by omega⟩ = -1) := by
  refine ⟨?_, ?_⟩
  · rw [ompInv_pairPermC_apply_of_not_lt h (by show ¬ (2 ≤ (0:ℕ) ∧ (0:ℕ) < 2 * r); omega)]
  · unfold ompInv_sa; rw [if_pos (by norm_num)]

private theorem ompInv_shape_e2 {n r : ℕ} (h : 2 * r ≤ n) (hr : 1 ≤ r) :
    (ompInv_pairPerm n r h ⟨0, by omega⟩ = ⟨1, by omega⟩ ∧
      ompInv_pairPerm n r h ⟨1, by omega⟩ = ⟨0, by omega⟩ ∧
      ompInv_sa n ⟨0, by omega⟩ = ompInv_sa n ⟨1, by omega⟩) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ompInv_pairPerm_apply_of_lt h (by show (0:ℕ) < 2 * r; omega)]; norm_num
  · rw [ompInv_pairPerm_apply_of_lt h (by show (1:ℕ) < 2 * r; omega)]; norm_num
  · unfold ompInv_sa; rw [if_pos (by norm_num), if_pos (by norm_num)]

private theorem ompInv_half_e2 {n r : ℕ} (hn : 3 ≤ n) [Finite K] [CharP K 2]
    (hr : 1 ≤ r) (hnr : n = 2 * r)
    {t : (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K)}
    {A : (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K)}
    (hAO : A ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus n K))
    (hAconj : A * t * A⁻¹ =
      LinearEquiv.funCongrLeft K K (ompInv_e1 (n := n) (r := r) (le_of_eq hnr.symm)))
    (hAΩ : A ∉ omegaGroup (quadPlus n K) (nondegenerate_polarBilin_quadPlus n K)) :
    ∃ B ∈ omegaGroup (quadPlus n K) (nondegenerate_polarBilin_quadPlus n K),
      B * t * B⁻¹ =
        LinearEquiv.funCongrLeft K K (ompInv_e2 (n := n) (r := r) (le_of_eq hnr.symm)) := by
  have hQ := nondegenerate_polarBilin_quadPlus n K
  have hn2 : 2 ≤ n := by omega
  have h2r : 2 * r ≤ n := le_of_eq hnr.symm
  have hdO : LinearEquiv.funCongrLeft K K (ompInv_d hn2) ∈
      TauCeti.QuadraticMap.orthogonalGroup (quadPlus n K) :=
    ompInv_d_mem_orthogonalGroup (K := K) (n := n) hn2
  have hdFin : finrank K (commSpace (LinearEquiv.funCongrLeft K K (ompInv_d hn2))) = 1 :=
    ompInv_d_finrank (K := K) (n := n) hn2
  have hdOdd : Odd (finrank K (commSpace (LinearEquiv.funCongrLeft K K (ompInv_d hn2)))) := by
    rw [hdFin]; exact odd_one
  have hAOdd : Odd (finrank K (commSpace A)) := by
    by_contra h
    exact hAΩ ⟨hAO, Nat.not_odd_iff_even.mp h⟩
  have hd_inv : (LinearEquiv.funCongrLeft K K (ompInv_d hn2))⁻¹ =
      LinearEquiv.funCongrLeft K K (ompInv_d hn2) := by
    apply inv_eq_of_mul_eq_one_right
    rw [ompInv_funCongrLeft_mul, ompInv_d_mul_self hn2, ompInv_funCongrLeft_one]
  refine ⟨LinearEquiv.funCongrLeft K K (ompInv_d hn2) * A, ⟨mul_mem hdO hAO, ?_⟩, ?_⟩
  · rw [← ZMod.natCast_eq_zero_iff_even, natCast_finrank_commSpace_mul hQ hdO hAO,
      hdFin, (ZMod.natCast_eq_one_iff_odd).mpr hAOdd, Nat.cast_one]
    decide
  · calc LinearEquiv.funCongrLeft K K (ompInv_d hn2) * A * t *
          (LinearEquiv.funCongrLeft K K (ompInv_d hn2) * A)⁻¹
        = LinearEquiv.funCongrLeft K K (ompInv_d hn2) * (A * t * A⁻¹) *
          (LinearEquiv.funCongrLeft K K (ompInv_d hn2))⁻¹ := by group
      _ = LinearEquiv.funCongrLeft K K (ompInv_d hn2) *
          LinearEquiv.funCongrLeft K K (ompInv_e1 h2r) *
          (LinearEquiv.funCongrLeft K K (ompInv_d hn2))⁻¹ := by rw [hAconj]
      _ = LinearEquiv.funCongrLeft K K (ompInv_d hn2) *
          LinearEquiv.funCongrLeft K K (ompInv_e1 h2r) *
          LinearEquiv.funCongrLeft K K (ompInv_d hn2) := by rw [hd_inv]
      _ = LinearEquiv.funCongrLeft K K (ompInv_e2 h2r) := by
          rw [ompInv_funCongrLeft_mul, ompInv_funCongrLeft_mul,
            show ompInv_d hn2 * (ompInv_e1 h2r * ompInv_d hn2) = ompInv_e2 h2r from by
              rw [← mul_assoc, ← ompInv_e2_eq_conj h2r hr]]

private theorem ompInv_finish {n : ℕ} (hn : 3 ≤ n) [Finite K] [CharP K 2]
    {y : spinGroup (quadPlus n K)}
    {π : Equiv.Perm (Fin n)} {s : Fin n → ℤ} (hsgn : SpIsSign s)
    (hprod : ∏ a, s a = 1)
    (hshape : (π ⟨0, by omega⟩ = ⟨0, by omega⟩ ∧ s ⟨0, by omega⟩ = -1) ∨
      (π ⟨0, by omega⟩ = ⟨1, by omega⟩ ∧ π ⟨1, by omega⟩ = ⟨0, by omega⟩ ∧
        s ⟨0, by omega⟩ = s ⟨1, by omega⟩))
    (hinv : spMonoPerm π s * spMonoPerm π s = 1)
    {B : (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K)}
    (hBΩ : B ∈ omegaGroup (quadPlus n K) (nondegenerate_polarBilin_quadPlus n K))
    (hBconj : B * spinAction (quadPlus n K) y * B⁻¹ =
      LinearEquiv.funCongrLeft K K (spMonoPerm π s)) :
    ∃ (g : spinGroup (quadPlus n K)) (π' : Equiv.Perm (Fin n)) (s' : Fin n → ℤ),
      SpIsSign s' ∧ ∏ a, s' a = 1 ∧
      ((π' ⟨0, by omega⟩ = ⟨0, by omega⟩ ∧ s' ⟨0, by omega⟩ = -1) ∨
        (π' ⟨0, by omega⟩ = ⟨1, by omega⟩ ∧ π' ⟨1, by omega⟩ = ⟨0, by omega⟩ ∧
          s' ⟨0, by omega⟩ = s' ⟨1, by omega⟩)) ∧
      (spinMatrix (quadPlus n K) (g * y * g⁻¹) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
        Equiv.Perm.permMatrix K (spMonoPerm π' s').symm := by
  obtain ⟨g, hg⟩ :=
    CFSG.StandardType.GGOppRadOmega.exists_spinAction_eq_of_mem_omegaGroup_plus hn hBΩ
  refine ⟨g, π, s, hsgn, hprod, hshape, ?_⟩
  have hfix : spinAction (quadPlus n K) (g * y * g⁻¹) =
      LinearEquiv.funCongrLeft K K (spMonoPerm π s) := by
    rw [map_mul, map_mul, map_inv, hg, hBconj]
  rw [coe_spinMatrix, hfix, ompInv_toMatrix'_funCongrLeft,
    show (spMonoPerm π s).symm = spMonoPerm π s from inv_eq_of_mul_eq_one_right hinv]

private theorem ompInv_orderOf_spinAction {n : ℕ} [CharP K 2] {y : spinGroup (quadPlus n K)}
    (hy : y * y = 1) (hy1 : y ≠ 1) :
    orderOf (spinAction (quadPlus n K) y) = 2 := by
  have h1 : spinAction (quadPlus n K) y ≠ 1 := by
    intro hh
    apply hy1
    apply CFSG.StandardType.RootCentOmega.spinAction_quadPlus_injective
    rw [hh, map_one]
  have h2 : spinAction (quadPlus n K) y * spinAction (quadPlus n K) y = 1 := by
    rw [← map_mul, hy, map_one]
  have hdvd : orderOf (spinAction (quadPlus n K) y) ∣ 2 :=
    orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact h2)
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) h1
  · exact h

private theorem ompInv_spinAction_mem_omegaGroup {n : ℕ} [CharP K 2] (hn : 3 ≤ n)
    {y : spinGroup (quadPlus n K)} :
    spinAction (quadPlus n K) y ∈ omegaGroup (quadPlus n K)
      (nondegenerate_polarBilin_quadPlus n K) := by
  have ht_range : spinAction (quadPlus n K) y ∈ (spinAction (quadPlus n K)).range := ⟨y, rfl⟩
  rw [range_spinAction_quadPlus hn] at ht_range
  exact CFSG.ClassicalGroups.Orthogonal.elementaryGroup_le_omegaGroup
    (nondegenerate_polarBilin_quadPlus n K) ht_range

private theorem ompInv_suzukiLetter_eq_a_or_c {n : ℕ}
    {t : (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K)}
    (heven : Even (finrank K (commSpace t))) :
    suzukiLetter (quadPlus n K) t = .a ∨ suzukiLetter (quadPlus n K) t = .c := by
  obtain ⟨r, hr⟩ := heven
  rcases h : suzukiLetter (quadPlus n K) t with _ | _ | _
  · exact Or.inl rfl
  · exfalso
    rw [suzukiLetter_eq_b_iff] at h
    exact (Nat.not_odd_iff_even.mpr ⟨r, hr⟩) h
  · exact Or.inr rfl

private theorem ompInv_exists_conj_e1 {n r : ℕ} [Finite K] [CharP K 2]
    (h2r : 2 * r ≤ n) (hr1 : 1 ≤ r)
    {t : (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K)}
    (htO : t ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus n K))
    (htord : orderOf t = 2)
    (hta : suzukiLetter (quadPlus n K) t = .a)
    (hfin : finrank K (commSpace t) = 2 * r) :
    ∃ A ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus n K),
      A * t * A⁻¹ = LinearEquiv.funCongrLeft K K (ompInv_e1 (n := n) (r := r) h2r) := by
  refine (isConj_iff_suzukiLetter_eq (Q := quadPlus n K)
    (nondegenerate_polarBilin_quadPlus n K) htO htord
    (ompInv_e1_mem_orthogonalGroup (K := K) (n := n) (r := r) h2r)
    (ompInv_orderOf_e1 (K := K) (n := n) (r := r) h2r hr1)).mpr ⟨?_, ?_⟩
  · rw [ompInv_suzukiLetter_e1 (K := K) (n := n) (r := r) h2r, hta]
  · rw [ompInv_finrank_e1 (K := K) (n := n) (r := r) h2r, hfin]

private theorem ompInv_exists_conj_ec {n r : ℕ} [Finite K] [CharP K 2]
    (h2r : 2 * r ≤ n) (hr1 : 1 ≤ r)
    {t : (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K)}
    (htO : t ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus n K))
    (htord : orderOf t = 2)
    (htc : suzukiLetter (quadPlus n K) t = .c)
    (hfin : finrank K (commSpace t) = 2 * r) :
    ∃ A ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus n K),
      A * t * A⁻¹ = LinearEquiv.funCongrLeft K K (ompInv_ec (n := n) (r := r) h2r) := by
  refine (isConj_iff_suzukiLetter_eq (Q := quadPlus n K)
    (nondegenerate_polarBilin_quadPlus n K) htO htord
    (ompInv_ec_mem_orthogonalGroup (K := K) (n := n) (r := r) h2r)
    (ompInv_orderOf_ec (K := K) (n := n) (r := r) h2r hr1)).mpr ⟨?_, ?_⟩
  · rw [ompInv_suzukiLetter_ec (K := K) (n := n) (r := r) h2r hr1, htc]
  · rw [ompInv_finrank_ec (K := K) (n := n) (r := r) h2r hr1, hfin]

private theorem ompInv_case_a_half {n : ℕ} (hn : 3 ≤ n) [Finite K] [CharP K 2]
    {y : spinGroup (quadPlus n K)} {r : ℕ} (hr1 : 1 ≤ r) (hnr : n = 2 * r)
    (htO : spinAction (quadPlus n K) y ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus n K))
    (htord : orderOf (spinAction (quadPlus n K) y) = 2)
    (hta : suzukiLetter (quadPlus n K) (spinAction (quadPlus n K) y) = .a)
    (hfin : finrank K (commSpace (spinAction (quadPlus n K) y)) = 2 * r) :
    ∃ (g : spinGroup (quadPlus n K)) (π : Equiv.Perm (Fin n)) (s : Fin n → ℤ),
      SpIsSign s ∧ ∏ a, s a = 1 ∧
      ((π ⟨0, by omega⟩ = ⟨0, by omega⟩ ∧ s ⟨0, by omega⟩ = -1) ∨
        (π ⟨0, by omega⟩ = ⟨1, by omega⟩ ∧ π ⟨1, by omega⟩ = ⟨0, by omega⟩ ∧
          s ⟨0, by omega⟩ = s ⟨1, by omega⟩)) ∧
      (spinMatrix (quadPlus n K) (g * y * g⁻¹) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
        Equiv.Perm.permMatrix K (spMonoPerm π s).symm := by
  have h2r' : 2 * r ≤ n := le_of_eq hnr.symm
  obtain ⟨A, hAO, hAconj⟩ :=
    ompInv_exists_conj_e1 (K := K) (n := n) (r := r) h2r' hr1 htO htord hta hfin
  have hprod_sa : ∏ a : Fin n, ompInv_sa n a = 1 := ompInv_prod_sa (by omega)
  by_cases hAΩ : A ∈ omegaGroup (quadPlus n K) (nondegenerate_polarBilin_quadPlus n K)
  · exact ompInv_finish hn spIsSign_one (by simp)
      (Or.inr (ompInv_shape_e1 h2r' hr1)) (ompInv_e1_mul_self h2r') hAΩ hAconj
  · obtain ⟨B, hBΩ, hBconj⟩ := ompInv_half_e2 hn hr1 hnr hAO hAconj hAΩ
    exact ompInv_finish hn (ompInv_spIsSign_sa n) hprod_sa
      (Or.inr (ompInv_shape_e2 h2r' hr1)) (ompInv_e2_mul_self h2r') hBΩ hBconj

private theorem ompInv_case_a_not_half {n : ℕ} (hn : 3 ≤ n) [Finite K] [CharP K 2]
    {y : spinGroup (quadPlus n K)} {r : ℕ} (hr1 : 1 ≤ r) (h2r : 2 * r ≤ n)
    (hV : finrank K (Fin n ⊕ Fin n → K) = 2 * n)
    (htO : spinAction (quadPlus n K) y ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus n K))
    (htord : orderOf (spinAction (quadPlus n K) y) = 2)
    (htΩ : spinAction (quadPlus n K) y ∈ omegaGroup (quadPlus n K)
      (nondegenerate_polarBilin_quadPlus n K))
    (hta : suzukiLetter (quadPlus n K) (spinAction (quadPlus n K) y) = .a)
    (hnot : ¬ (suzukiLetter (quadPlus n K) (spinAction (quadPlus n K) y) = .a ∧
      finrank K (commSpace (spinAction (quadPlus n K) y)) = n))
    (hfin : finrank K (commSpace (spinAction (quadPlus n K) y)) = 2 * r) :
    ∃ (g : spinGroup (quadPlus n K)) (π : Equiv.Perm (Fin n)) (s : Fin n → ℤ),
      SpIsSign s ∧ ∏ a, s a = 1 ∧
      ((π ⟨0, by omega⟩ = ⟨0, by omega⟩ ∧ s ⟨0, by omega⟩ = -1) ∨
        (π ⟨0, by omega⟩ = ⟨1, by omega⟩ ∧ π ⟨1, by omega⟩ = ⟨0, by omega⟩ ∧
          s ⟨0, by omega⟩ = s ⟨1, by omega⟩)) ∧
      (spinMatrix (quadPlus n K) (g * y * g⁻¹) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
        Equiv.Perm.permMatrix K (spMonoPerm π s).symm := by
  obtain ⟨A, hAO, hAconj⟩ :=
    ompInv_exists_conj_e1 (K := K) (n := n) (r := r) h2r hr1 htO htord hta hfin
  have hmem : LinearEquiv.funCongrLeft K K (ompInv_e1 (n := n) (r := r) h2r) ∈
      {x | ∃ g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus n K),
        g * spinAction (quadPlus n K) y * g⁻¹ = x} := ⟨A, hAO, hAconj⟩
  rw [← omega_conj_eq_of_not_typeA_half (Q := quadPlus n K)
    (nondegenerate_polarBilin_quadPlus n K) (m := n) hV htΩ htord hnot] at hmem
  obtain ⟨B, hBΩ, hBconj⟩ := hmem
  exact ompInv_finish hn spIsSign_one (by simp)
    (Or.inr (ompInv_shape_e1 h2r hr1)) (ompInv_e1_mul_self h2r) hBΩ hBconj

private theorem ompInv_case_c {n : ℕ} (hn : 3 ≤ n) [Finite K] [CharP K 2]
    {y : spinGroup (quadPlus n K)} {r : ℕ} (hr1 : 1 ≤ r) (h2r : 2 * r ≤ n)
    (hV : finrank K (Fin n ⊕ Fin n → K) = 2 * n)
    (htO : spinAction (quadPlus n K) y ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus n K))
    (htord : orderOf (spinAction (quadPlus n K) y) = 2)
    (htΩ : spinAction (quadPlus n K) y ∈ omegaGroup (quadPlus n K)
      (nondegenerate_polarBilin_quadPlus n K))
    (htc : suzukiLetter (quadPlus n K) (spinAction (quadPlus n K) y) = .c)
    (hnot : ¬ (suzukiLetter (quadPlus n K) (spinAction (quadPlus n K) y) = .a ∧
      finrank K (commSpace (spinAction (quadPlus n K) y)) = n))
    (hfin : finrank K (commSpace (spinAction (quadPlus n K) y)) = 2 * r) :
    ∃ (g : spinGroup (quadPlus n K)) (π : Equiv.Perm (Fin n)) (s : Fin n → ℤ),
      SpIsSign s ∧ ∏ a, s a = 1 ∧
      ((π ⟨0, by omega⟩ = ⟨0, by omega⟩ ∧ s ⟨0, by omega⟩ = -1) ∨
        (π ⟨0, by omega⟩ = ⟨1, by omega⟩ ∧ π ⟨1, by omega⟩ = ⟨0, by omega⟩ ∧
          s ⟨0, by omega⟩ = s ⟨1, by omega⟩)) ∧
      (spinMatrix (quadPlus n K) (g * y * g⁻¹) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
        Equiv.Perm.permMatrix K (spMonoPerm π s).symm := by
  obtain ⟨A, hAO, hAconj⟩ :=
    ompInv_exists_conj_ec (K := K) (n := n) (r := r) h2r hr1 htO htord htc hfin
  have hmem : LinearEquiv.funCongrLeft K K (ompInv_ec (n := n) (r := r) h2r) ∈
      {x | ∃ g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus n K),
        g * spinAction (quadPlus n K) y * g⁻¹ = x} := ⟨A, hAO, hAconj⟩
  rw [← omega_conj_eq_of_not_typeA_half (Q := quadPlus n K)
    (nondegenerate_polarBilin_quadPlus n K) (m := n) hV htΩ htord hnot] at hmem
  obtain ⟨B, hBΩ, hBconj⟩ := hmem
  have hprod_sa : ∏ a : Fin n, ompInv_sa n a = 1 := ompInv_prod_sa (by omega)
  exact ompInv_finish hn (ompInv_spIsSign_sa n) hprod_sa
    (Or.inl (ompInv_shape_ec h2r hr1)) (ompInv_ec_mul_self h2r) hBΩ hBconj

private theorem ompInv_dispatch {n : ℕ} (hn : 3 ≤ n) [Finite K] [CharP K 2]
    {y : spinGroup (quadPlus n K)}
    {t : (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K)}
    (hyt : t = spinAction (quadPlus n K) y)
    {r : ℕ} (hr1 : 1 ≤ r) (h2r : 2 * r ≤ n)
    (hV : finrank K (Fin n ⊕ Fin n → K) = 2 * n)
    (htO : t ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus n K))
    (htord : orderOf t = 2)
    (htΩ : t ∈ omegaGroup (quadPlus n K) (nondegenerate_polarBilin_quadPlus n K))
    (hletter : suzukiLetter (quadPlus n K) t = .a ∨ suzukiLetter (quadPlus n K) t = .c)
    (hfin : finrank K (commSpace t) = 2 * r) :
    ∃ (g : spinGroup (quadPlus n K)) (π : Equiv.Perm (Fin n)) (s : Fin n → ℤ),
      SpIsSign s ∧ ∏ a, s a = 1 ∧
      ((π ⟨0, by omega⟩ = ⟨0, by omega⟩ ∧ s ⟨0, by omega⟩ = -1) ∨
        (π ⟨0, by omega⟩ = ⟨1, by omega⟩ ∧ π ⟨1, by omega⟩ = ⟨0, by omega⟩ ∧
          s ⟨0, by omega⟩ = s ⟨1, by omega⟩)) ∧
      (spinMatrix (quadPlus n K) (g * y * g⁻¹) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
        Equiv.Perm.permMatrix K (spMonoPerm π s).symm := by
  subst hyt
  rcases hletter with hta | htc
  · by_cases hln : finrank K (commSpace (spinAction (quadPlus n K) y)) = n
    · have hnr : n = 2 * r := by rw [← hln, hfin]
      exact ompInv_case_a_half hn hr1 hnr htO htord hta hfin
    · have hnot : ¬ (suzukiLetter (quadPlus n K) (spinAction (quadPlus n K) y) = .a ∧
          finrank K (commSpace (spinAction (quadPlus n K) y)) = n) := fun hh => hln hh.2
      exact ompInv_case_a_not_half hn hr1 h2r hV htO htord htΩ hta hnot hfin
  · have hnot : ¬ (suzukiLetter (quadPlus n K) (spinAction (quadPlus n K) y) = .a ∧
        finrank K (commSpace (spinAction (quadPlus n K) y)) = n) := by
      rintro ⟨h1, -⟩
      rw [htc] at h1
      exact absurd h1 (by decide)
    exact ompInv_case_c hn hr1 h2r hV htO htord htΩ htc hnot hfin

theorem exists_conj_spinMatrix_eq_spMonoPerm {n : ℕ} (hn : 3 ≤ n) {K : Type} [Field K]
    [Finite K] [CharP K 2] {y : spinGroup (quadPlus n K)} (hy : y * y = 1) (hy1 : y ≠ 1) :
    ∃ (g : spinGroup (quadPlus n K)) (π : Equiv.Perm (Fin n)) (s : Fin n → ℤ),
      SpIsSign s ∧ ∏ a, s a = 1 ∧
      ((π ⟨0, by omega⟩ = ⟨0, by omega⟩ ∧ s ⟨0, by omega⟩ = -1) ∨
        (π ⟨0, by omega⟩ = ⟨1, by omega⟩ ∧ π ⟨1, by omega⟩ = ⟨0, by omega⟩ ∧
          s ⟨0, by omega⟩ = s ⟨1, by omega⟩)) ∧
      (spinMatrix (quadPlus n K) (g * y * g⁻¹) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
        Equiv.Perm.permMatrix K (spMonoPerm π s).symm := by

  classical
  let Q := quadPlus n K
  let t : (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K) := spinAction Q y
  have ht2 : t * t = 1 := by dsimp [t]; rw [← map_mul, hy, map_one]
  have ht1 : t ≠ 1 := by
    intro h1
    apply hy1
    apply CFSG.StandardType.RootCentOmega.spinAction_quadPlus_injective
    change t = spinAction Q (1 : spinGroup (quadPlus n K))
    rw [h1, map_one]
  have htO : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (fun v => map_spinAction Q y v)
  have hQ : Q.polarBilin.Nondegenerate := nondegenerate_polarBilin_quadPlus n K
  have hV : finrank K (Fin n ⊕ Fin n → K) = 2 * n := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    ring
  have htord : orderOf t = 2 := by
    simpa only [t, Q] using ompInv_orderOf_spinAction (K := K) hy hy1
  have htΩ : t ∈ omegaGroup Q hQ := by
    simpa only [t, Q] using ompInv_spinAction_mem_omegaGroup (K := K) hn (y := y)
  set l := finrank K (commSpace t) with hl
  have hleven : Even l := by rw [hl]; exact htΩ.2
  have hl1 : 1 ≤ l := one_le_finrank_commSpace ht1
  have hl2n : 2 * l ≤ 2 * n := by
    have h := two_mul_finrank_commSpace_le (t := t) ht2
    rw [hV] at h
    exact h
  obtain ⟨r, hr⟩ := hleven
  have hl2r : l = 2 * r := by omega
  have hr1 : 1 ≤ r := by omega
  have h2r : 2 * r ≤ n := by omega
  have hletter : suzukiLetter (quadPlus n K) t = .a ∨ suzukiLetter (quadPlus n K) t = .c :=
    ompInv_suzukiLetter_eq_a_or_c (K := K) (n := n) (t := t) htΩ.2
  exact ompInv_dispatch (t := t) hn rfl hr1 h2r hV htO htord htΩ hletter
    (by rw [← hl]; exact hl2r)

end CFSG.LocalAnalysis.WeakClosure81
