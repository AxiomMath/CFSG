module

public import Mathlib.Data.Fintype.CardEmbedding
public import Mathlib.GroupTheory.GroupAction.Jordan
public import CFSG.ThirdParty.OddOrder.Isaacs.PermutationGroups.CycleCommutators
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG

namespace FiveTransitive.SupportEightInvolutionClosure

open Equiv Equiv.Perm MulAction Subgroup
open scoped BigOperators commutatorElement

section Counting

variable {G Ω : Type*} [Group G] [Fintype G] [Fintype Ω]
  [MulAction G Ω] [DecidableEq Ω]

private noncomputable def stabilizerEquivSmulFiber
    [MulAction.IsPretransitive G Ω] (x y : Ω) :
    MulAction.stabilizer G x ≃ {q : G // q • x = y} := by
  classical
  choose t ht using MulAction.IsPretransitive.exists_smul_eq (M := G) x y
  let f : MulAction.stabilizer G x → {q : G // q • x = y} := fun h =>
    ⟨t * h, by
      rw [mul_smul]
      rw [MulAction.mem_stabilizer_iff.mp h.property, ht]⟩
  apply Equiv.ofBijective f
  constructor
  · intro a b hab
    apply Subtype.ext
    exact mul_left_cancel (congrArg Subtype.val hab)
  · intro q
    let h : MulAction.stabilizer G x :=
      ⟨t⁻¹ * q, by
        rw [MulAction.mem_stabilizer_iff, mul_smul, q.property, ← ht,
          inv_smul_smul]⟩
    refine ⟨h, ?_⟩
    apply Subtype.ext
    simp [f, h]

theorem card_smul_mem_finset
    [MulAction.IsPretransitive G Ω] (x : Ω) (B : Finset Ω) :
    (Finset.univ.filter fun q : G => q • x ∈ B).card =
      B.card * Nat.card (MulAction.stabilizer G x) := by
  classical
  let E : {q : G // q • x ∈ B} ≃
      Σ y : B, {q : G // q • x = y.1} :=
    { toFun := fun q => ⟨⟨q.1 • x, q.2⟩, ⟨q.1, rfl⟩⟩
      invFun := fun z => ⟨z.2.1, z.2.2.symm ▸ z.1.2⟩
      left_inv := fun q => by cases q; rfl
      right_inv := fun z => by
        obtain ⟨⟨y, hy⟩, ⟨q, hq⟩⟩ := z
        change q • x = y at hq
        subst y
        rfl }
  have hcardSubtype :
      Nat.card {q : G // q • x ∈ B} =
        B.card * Nat.card (MulAction.stabilizer G x) := by
    rw [Nat.card_congr E, Nat.card_sigma]
    simp_rw [Nat.card_congr (stabilizerEquivSmulFiber x _).symm]
    simp [Nat.card_eq_fintype_card]
  rw [← hcardSubtype]
  exact (Nat.subtype_card _ (fun q => by simp)).symm

private theorem sum_card_filter_smul
    (htrans : MulAction.IsPretransitive G Ω)
    (x₀ : Ω) (B : Finset Ω) :
    Nat.card Ω *
        (∑ q : G, (B.filter fun x => q • x ∈ B).card) =
      Nat.card G * B.card ^ 2 := by
  classical
  let _ : MulAction.IsPretransitive G Ω := htrans
  have hstab (x : Ω) :
      Nat.card (MulAction.stabilizer G x) =
        Nat.card (MulAction.stabilizer G x₀) := by
    obtain ⟨q, hq⟩ :=
      MulAction.IsPretransitive.exists_smul_eq (M := G) x x₀
    exact Nat.card_congr
      (MulAction.stabilizerEquivStabilizer hq.symm).toEquiv
  have hswap :
      (∑ q : G, (B.filter fun x => q • x ∈ B).card) =
        (∑ x ∈ B, (Finset.univ.filter fun q : G => q • x ∈ B).card) := by
    simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
  rw [hswap]
  simp_rw [card_smul_mem_finset]
  simp_rw [hstab]
  rw [Finset.sum_const_nat (m :=
    B.card * Nat.card (MulAction.stabilizer G x₀)) (fun _ _ => rfl)]
  have horbit :=
    MulAction.card_orbit_mul_card_stabilizer_eq_card_group G x₀
  have horbit' :
      Fintype.card Ω * Fintype.card (MulAction.stabilizer G x₀) =
        Fintype.card G := by
    simpa [MulAction.orbit_eq_univ G x₀]
      using horbit
  simp only [Nat.card_eq_fintype_card]
  calc
    Fintype.card Ω *
        (B.card * (B.card * Fintype.card (MulAction.stabilizer G x₀))) =
        (Fintype.card Ω * Fintype.card (MulAction.stabilizer G x₀)) *
          B.card ^ 2 := by ring
    _ = Fintype.card G * B.card ^ 2 := by rw [horbit']

end Counting

section Embeddings

variable {X : Type*} [Fintype X] [DecidableEq X]

@[expose] noncomputable def embeddingsInto (j : ℕ) (S : Finset X) : Finset (Fin j ↪ X) :=
  Finset.univ.filter fun e => ∀ i, e i ∈ S

private noncomputable def embeddingIntoSubtypeEquiv (j : ℕ) (S : Finset X) :
    (Fin j ↪ S) ≃ {e : Fin j ↪ X // ∀ i, e i ∈ S} :=
  { toFun := fun e =>
      ⟨e.trans (Function.Embedding.subtype _), fun i => (e i).property⟩
    invFun := fun e =>
      ⟨fun i => ⟨e.1 i, e.2 i⟩,
        fun _ _ h => e.1.injective (congrArg Subtype.val h)⟩
    left_inv := fun e => by ext i; rfl
    right_inv := fun e => by ext i; rfl }

theorem card_embeddingsInto (j : ℕ) (S : Finset X) :
    (embeddingsInto j S).card = S.card.descFactorial j := by
  classical
  calc
    (embeddingsInto j S).card =
        Nat.card {e : Fin j ↪ X // ∀ i, e i ∈ S} := by
      rw [Nat.subtype_card (embeddingsInto j S)]
      simp [embeddingsInto]
    _ = Nat.card (Fin j ↪ S) :=
      Nat.card_congr (embeddingIntoSubtypeEquiv j S).symm
    _ = S.card.descFactorial j := by
      rw [Nat.card_eq_fintype_card, Fintype.card_embedding_eq,
        Fintype.card_fin, Fintype.card_coe]

private def overlapPreimage (S : Finset X) (q : Equiv.Perm X) : Finset X :=
  S.filter fun x => q x ∈ S

private theorem filter_embeddingsInto_eq (j : ℕ) (S : Finset X)
    (q : Equiv.Perm X) :
    (embeddingsInto j S).filter (fun e => q • e ∈ embeddingsInto j S) =
      embeddingsInto j (overlapPreimage S q) := by
  classical
  ext e
  simp only [embeddingsInto, overlapPreimage, Finset.mem_filter,
    Finset.mem_univ, true_and, Function.Embedding.smul_apply,
    Equiv.Perm.smul_def]
  constructor
  · rintro ⟨he, hqe⟩ i
    exact ⟨he i, hqe i⟩
  · intro he
    exact ⟨fun i => (he i).1, fun i => (he i).2⟩

private theorem overlap_moment
    (P : Subgroup (Equiv.Perm X))
    [Fintype P]
    (h4 : MulAction.IsMultiplyPretransitive P X 4)
    (S : Finset X) {j : ℕ} (hj : j ≤ 4)
    (hcard : 4 ≤ Fintype.card X) :
    (Fintype.card X).descFactorial j *
        (∑ q : P, (overlapPreimage S q).card.descFactorial j) =
      Nat.card P * (S.card.descFactorial j) ^ 2 := by
  classical
  have hNatCard : 4 ≤ Nat.card X := by
    simpa [Nat.card_eq_fintype_card] using hcard
  letI h4I : MulAction.IsMultiplyPretransitive P X 4 := h4
  letI hjI : MulAction.IsMultiplyPretransitive P X j :=
    MulAction.isMultiplyPretransitive_of_le hj hNatCard
  let B : Finset (Fin j ↪ X) := embeddingsInto j S
  have hcount := sum_card_filter_smul (G := P)
    (Ω := Fin j ↪ X) hjI (Classical.choice (Fintype.card_pos_iff.mp (by
      rw [Fintype.card_embedding_eq, Fintype.card_fin]
      exact Nat.descFactorial_pos.mpr (by omega)))) B
  rw [Nat.card_eq_fintype_card, Fintype.card_embedding_eq,
    Fintype.card_fin] at hcount
  simp only [B] at hcount
  have hfilter (q : P) :
      (embeddingsInto j S).filter
          (fun e => q • e ∈ embeddingsInto j S) =
        embeddingsInto j (overlapPreimage S q) :=
    filter_embeddingsInto_eq j S q
  have hsum :
      (∑ q : P,
          ((embeddingsInto j S).filter
            (fun e => q • e ∈ embeddingsInto j S)).card) =
        ∑ q : P, (overlapPreimage S q).card.descFactorial j := by
    apply Finset.sum_congr rfl
    intro q _
    rw [hfilter q, card_embeddingsInto]
  calc
    (Fintype.card X).descFactorial j *
        (∑ q : P, (overlapPreimage S q).card.descFactorial j) =
        (Fintype.card X).descFactorial j *
          (∑ q : P,
            ((embeddingsInto j S).filter
              (fun e => q • e ∈ embeddingsInto j S)).card) :=
      congrArg ((Fintype.card X).descFactorial j * ·) hsum.symm
    _ = Nat.card P * (embeddingsInto j S).card ^ 2 := hcount
    _ = Nat.card P * (S.card.descFactorial j) ^ 2 := by
      rw [card_embeddingsInto]

end Embeddings

section Arithmetic

private theorem descFactorial_quartic_nonnegative_of_ne_one (k : ℕ) (hk : k ≠ 1) :
    3 * k.descFactorial 3 + 6 * k ≤
      k.descFactorial 4 + 6 * k.descFactorial 2 := by
  by_cases hsmall : k < 5
  · interval_cases k <;> norm_num [Nat.descFactorial] at *
  · have hk5 : 5 ≤ k := by omega
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (show 4 ≤ k by omega)
    norm_num [Nat.descFactorial]
    have hsubTwo : 4 + m - 2 = 2 + m := by omega
    have hsubThree : 4 + m - 3 = 1 + m := by omega
    rw [hsubTwo, hsubThree]
    nlinarith [Nat.zero_le (m * (m + 1) * (m + 2) * (m + 4))]

private theorem exists_overlapPreimage_card_eq_one
    {X : Type*} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hdegree : 28 ≤ Fintype.card X)
    (h4 : MulAction.IsMultiplyPretransitive P X 4)
    (S : Finset X) (hS : S.card = 8) :
    ∃ q : P, (overlapPreimage S q).card = 1 := by
  classical
  letI : Fintype P := Fintype.ofFinite P
  by_contra hnone
  push Not at hnone
  have hm1 := overlap_moment P h4 S (j := 1) (by omega) (by omega)
  have hm2 := overlap_moment P h4 S (j := 2) (by omega) (by omega)
  have hm3 := overlap_moment P h4 S (j := 3) (by omega) (by omega)
  have hm4 := overlap_moment P h4 S (j := 4) (by omega) (by omega)
  have hsumRaw :
      (∑ q : P,
          (3 * (overlapPreimage S q).card.descFactorial 3 +
            6 * (overlapPreimage S q).card)) ≤
        ∑ q : P,
          ((overlapPreimage S q).card.descFactorial 4 +
            6 * (overlapPreimage S q).card.descFactorial 2) := by
    apply Finset.sum_le_sum
    intro q _
    exact descFactorial_quartic_nonnegative_of_ne_one _ (hnone q)
  have hsum :
      3 * (∑ q : P, (overlapPreimage S q).card.descFactorial 3) +
          6 * (∑ q : P, (overlapPreimage S q).card) ≤
        (∑ q : P, (overlapPreimage S q).card.descFactorial 4) +
          6 * (∑ q : P,
            (overlapPreimage S q).card.descFactorial 2) := by
    simpa only [Finset.sum_add_distrib, ← Finset.mul_sum] using hsumRaw
  rw [hS] at hm1 hm2 hm3 hm4
  norm_num [Nat.descFactorial] at hm1 hm2 hm3 hm4 hsum
  let n := Fintype.card X
  let p := Fintype.card P
  let T1 := ∑ q : P, (overlapPreimage S q).card
  let T2 := ∑ q : P,
    ((overlapPreimage S q).card - 1) * (overlapPreimage S q).card
  let T3 := ∑ q : P,
    ((overlapPreimage S q).card - 2) *
      (((overlapPreimage S q).card - 1) * (overlapPreimage S q).card)
  let T4 := ∑ q : P,
    ((overlapPreimage S q).card - 3) *
      (((overlapPreimage S q).card - 2) *
        (((overlapPreimage S q).card - 1) * (overlapPreimage S q).card))
  change n * T1 = p * 64 at hm1
  change (n - 1) * n * T2 = p * 3136 at hm2
  change (n - 2) * ((n - 1) * n) * T3 = p * 112896 at hm3
  change (n - 3) * ((n - 2) * ((n - 1) * n)) * T4 =
    p * 2822400 at hm4
  change 3 * T3 + 6 * T1 ≤ T4 + 6 * T2 at hsum
  have hn28 : 28 ≤ n := by simpa [n] using hdegree
  obtain ⟨r, hn⟩ := Nat.exists_eq_add_of_le hn28
  rw [hn] at hm1 hm2 hm3 hm4
  norm_num at hm1 hm2 hm3 hm4
  have hsub1 : 28 + r - 1 = 27 + r := by omega
  have hsub2 : 28 + r - 2 = 26 + r := by omega
  have hsub3 : 28 + r - 3 = 25 + r := by omega
  simp only [hsub2, hsub3] at hm2 hm3 hm4
  let D := (25 + r) * (26 + r) * (27 + r) * (28 + r)
  have hD1 : D * T1 =
      (25 + r) * (26 + r) * (27 + r) * (p * 64) := by
    calc
      D * T1 =
          ((25 + r) * (26 + r) * (27 + r)) * ((28 + r) * T1) := by
        simp only [D]
        ring
      _ = (25 + r) * (26 + r) * (27 + r) * (p * 64) := by
        rw [hm1]
  have hD2 : D * T2 =
      (25 + r) * (26 + r) * (p * 3136) := by
    calc
      D * T2 =
          ((25 + r) * (26 + r)) * (((27 + r) * (28 + r)) * T2) := by
        simp only [D]
        ring
      _ = (25 + r) * (26 + r) * (p * 3136) := by
        rw [hm2]
  have hD3 : D * T3 = (25 + r) * (p * 112896) := by
    calc
      D * T3 =
          (25 + r) * (((26 + r) * ((27 + r) * (28 + r))) * T3) := by
        simp only [D]
        ring
      _ = (25 + r) * (p * 112896) := by rw [hm3]
  have hD4 : D * T4 = p * 2822400 := by
    calc
      D * T4 =
          ((25 + r) * ((26 + r) * ((27 + r) * (28 + r)))) * T4 := by
        simp only [D]
        ring
      _ = p * 2822400 := hm4
  have hscaled := Nat.mul_le_mul_left D hsum
  have hscaled' :
      3 * (D * T3) + 6 * (D * T1) ≤
        D * T4 + 6 * (D * T2) := by
    calc
      3 * (D * T3) + 6 * (D * T1) =
          D * (3 * T3 + 6 * T1) := by ring
      _ ≤ D * (T4 + 6 * T2) := hscaled
      _ = D * T4 + 6 * (D * T2) := by ring
  rw [hD1, hD2, hD3, hD4] at hscaled'
  let L := 3 * (25 + r) * 112896 +
    6 * (25 + r) * (26 + r) * (27 + r) * 64
  let R := 2822400 + 6 * (25 + r) * (26 + r) * 3136
  have hp : 0 < p := by
    simpa [p] using Fintype.card_pos_iff.mpr (inferInstance : Nonempty P)
  have hpLR : p * L ≤ p * R := by
    calc
      p * L =
          3 * ((25 + r) * (p * 112896)) +
            6 * ((25 + r) * (26 + r) * (27 + r) * (p * 64)) := by
        simp only [L]
        ring
      _ ≤ p * 2822400 +
          6 * ((25 + r) * (26 + r) * (p * 3136)) := hscaled'
      _ = p * R := by
        simp only [R]
        ring
  have hLR : L ≤ R := Nat.le_of_mul_le_mul_left hpLR hp
  have hgap : L = R + 384 * (r ^ 3 + 29 * r ^ 2 + 410 * r + 400) := by
    simp only [L, R]
    ring
  rw [hgap] at hLR
  have hpositive : 0 < 384 * (r ^ 3 + 29 * r ^ 2 + 410 * r + 400) := by
    positivity
  omega

end Arithmetic

section Closure

variable {X : Type*} [Fintype X] [DecidableEq X]

private theorem mem_support_inv_mul_mul_iff
    (g q : Equiv.Perm X) (x : X) :
    x ∈ (q⁻¹ * g * q).support ↔ q x ∈ g.support := by
  rw [show q⁻¹ * g * q = q⁻¹ * g * (q⁻¹)⁻¹ by simp]
  rw [Equiv.Perm.support_conj]
  simp only [Finset.mem_map, Equiv.coe_toEmbedding,
    Equiv.Perm.mem_support, Equiv.Perm.inv_def]
  constructor
  · rintro ⟨a, ha, hax⟩
    have haqx : a = q x := by
      simpa using congrArg q hax
    rwa [haqx] at ha
  · intro hx
    exact ⟨q x, hx, q.symm_apply_apply x⟩

theorem alternatingGroup_le_of_support_card_eight
    (P : Subgroup (Equiv.Perm X))
    (hdegree : 28 ≤ Fintype.card X)
    (h4 : MulAction.IsMultiplyPretransitive P X 4)
    {g : Equiv.Perm X} (hg : g ∈ P)
    (hsupport : g.support.card = 8) :
    alternatingGroup X ≤ P := by
  classical
  obtain ⟨q, hqcard⟩ :=
    exists_overlapPreimage_card_eq_one P hdegree h4 g.support hsupport
  have hnonempty : (overlapPreimage g.support q).Nonempty :=
    Finset.card_pos.mp (by omega)
  obtain ⟨a, ha⟩ := hnonempty
  let y : Equiv.Perm X := q⁻¹ * g * q
  have hyP : y ∈ P := by
    exact P.mul_mem (P.mul_mem (P.inv_mem q.property) hg) q.property
  have haG : a ∈ g.support := by
    exact (Finset.mem_filter.mp ha).1
  have haY : a ∈ y.support := by
    apply (mem_support_inv_mul_mul_iff g q a).2
    exact (Finset.mem_filter.mp ha).2
  have hga : g a ≠ a := Equiv.Perm.mem_support.mp haG
  have hya : y a ≠ a := Equiv.Perm.mem_support.mp haY
  have huniq : ∀ b : X, b ≠ a → g b = b ∨ y b = b := by
    intro b hba
    by_cases hgb : g b = b
    · exact Or.inl hgb
    · right
      by_contra hyb
      have hbG : b ∈ g.support := Equiv.Perm.mem_support.mpr hgb
      have hbY : b ∈ y.support := Equiv.Perm.mem_support.mpr hyb
      have hbOverlap : b ∈ overlapPreimage g.support q := by
        rw [overlapPreimage, Finset.mem_filter]
        exact ⟨hbG, (mem_support_inv_mul_mul_iff g q b).1 hbY⟩
      have hba' : b = a :=
        (Finset.card_le_one.mp (by omega)) b hbOverlap a ha
      exact hba hba'
  have hthree : (⁅g, y⁆ : Equiv.Perm X).IsThreeCycle :=
    OddOrder.Isaacs.Ch08.isThreeCycle_commutator_of_unique_common_moved
      hga hya huniq
  have hcommP : ⁅g, y⁆ ∈ P :=
    P.commutator_le_self (Subgroup.commutator_mem_commutator hg hyP)
  have hX4 : 4 ≤ Nat.card X := by
    simpa [Nat.card_eq_fintype_card] using (show 4 ≤ Fintype.card X by omega)
  let _ : MulAction.IsMultiplyPretransitive P X 4 := h4
  have h2 : MulAction.IsMultiplyPretransitive P X 2 :=
    MulAction.isMultiplyPretransitive_of_le (by omega) hX4
  have hprimitive : MulAction.IsPreprimitive P X :=
    MulAction.isPreprimitive_of_is_two_pretransitive h2
  exact
    Equiv.Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem
      hprimitive hthree hcommP

end Closure

end FiveTransitive.SupportEightInvolutionClosure

end CFSG
