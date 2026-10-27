module

public import Mathlib.GroupTheory.RegularWreathProduct
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.RankThree.PartTwo.Sec11

abbrev W33 : Type := Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3)

theorem eq_const_of_mem_center {z : W33} (hz : z ∈ Subgroup.center W33) :
    z.right = 1 ∧ ∀ x, z.left x = z.left 1 := by
  rw [Subgroup.mem_center_iff] at hz
  set t : Multiplicative (ZMod 3) := Multiplicative.ofAdd 1 with ht
  have h1 := hz ⟨1, t⟩
  have hshift : ∀ x, z.left x = z.left (t⁻¹ * x) := by
    intro x
    have := congrArg (fun w : W33 => w.left x) h1
    simpa [RegularWreathProduct.mul_def] using this.symm
  have hconst : ∀ x, z.left x = z.left 1 := by
    intro x
    obtain ⟨k, rfl⟩ : ∃ k : ZMod 3, Multiplicative.ofAdd k = x := ⟨Multiplicative.toAdd x, rfl⟩
    have hstep : ∀ m : ℕ, z.left (Multiplicative.ofAdd (m : ZMod 3)) = z.left 1 := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [← ih, hshift (Multiplicative.ofAdd ((m + 1 : ℕ) : ZMod 3))]
        congr 1
        simp [ht, ← ofAdd_neg, ← ofAdd_add]
    have := hstep k.val
    rwa [ZMod.natCast_zmod_val] at this
  refine ⟨?_, hconst⟩
  by_contra hq
  let δ : Multiplicative (ZMod 3) → Multiplicative (ZMod 3) := fun x => if x = 1 then t else 1
  have h2 := hz ⟨δ, 1⟩
  have := congrArg (fun w : W33 => w.left z.right) h2
  simp only [RegularWreathProduct.mul_def, Pi.mul_apply, inv_one, one_mul] at this
  have hδq : δ z.right = 1 := by simp [δ, hq]
  rw [inv_mul_cancel, show δ 1 = t from by simp [δ]] at this
  rw [hδq, one_mul, mul_comm] at this
  have ht1 : t ≠ 1 := by
    rw [ht]
    decide
  exact ht1 (mul_eq_right.mp this.symm)

theorem card_center_wreath_le : Nat.card (Subgroup.center W33) ≤ 3 := by
  let F : Subgroup.center W33 → Multiplicative (ZMod 3) := fun z => (z : W33).left 1
  have hF : Function.Injective F := by
    rintro ⟨z, hz⟩ ⟨w, hw⟩ h
    obtain ⟨hz1, hz2⟩ := eq_const_of_mem_center hz
    obtain ⟨hw1, hw2⟩ := eq_const_of_mem_center hw
    apply Subtype.ext
    apply RegularWreathProduct.ext
    · funext x
      rw [hz2, hw2]
      exact h
    · rw [hz1, hw1]
  calc Nat.card (Subgroup.center W33) ≤ Nat.card (Multiplicative (ZMod 3)) :=
        Nat.card_le_card_of_injective F hF
    _ = 3 := by simp

theorem card_wreath : Nat.card W33 = 81 := by
  rw [RegularWreathProduct.card]
  simp

variable {G : Type*} [Group G]

theorem exists_zpow_triple_of_mem_closure {a c d : G} (hac : a * c = c * a)
    (had : a * d = d * a) (hcd : c * d = d * c) {z : G}
    (hz : z ∈ Subgroup.closure ({a, c, d} : Set G)) :
    ∃ i j k : ℤ, z = a ^ i * c ^ j * d ^ k := by
  have hac' : Commute a c := hac
  have had' : Commute a d := had
  have hcd' : Commute c d := hcd
  induction hz using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl | rfl
    · exact ⟨1, 0, 0, by simp⟩
    · exact ⟨0, 1, 0, by simp⟩
    · exact ⟨0, 0, 1, by simp⟩
  | one => exact ⟨0, 0, 0, by simp⟩
  | mul x w _ _ hx hw =>
    obtain ⟨i, j, k, rfl⟩ := hx
    obtain ⟨i', j', k', rfl⟩ := hw
    refine ⟨i + i', j + j', k + k', ?_⟩
    have h1 : d ^ k * a ^ i' = a ^ i' * d ^ k := ((had'.zpow_zpow i' k).eq).symm
    have h2 : c ^ j * a ^ i' = a ^ i' * c ^ j := ((hac'.zpow_zpow i' j).eq).symm
    have h3 : d ^ k * c ^ j' = c ^ j' * d ^ k := ((hcd'.zpow_zpow j' k).eq).symm
    rw [zpow_add, zpow_add, zpow_add]
    calc a ^ i * c ^ j * d ^ k * (a ^ i' * c ^ j' * d ^ k')
        = a ^ i * c ^ j * (d ^ k * a ^ i') * c ^ j' * d ^ k' := by group
      _ = a ^ i * (c ^ j * a ^ i') * d ^ k * c ^ j' * d ^ k' := by rw [h1]; group
      _ = a ^ i * a ^ i' * c ^ j * (d ^ k * c ^ j') * d ^ k' := by rw [h2]; group
      _ = a ^ i * a ^ i' * (c ^ j * c ^ j') * (d ^ k * d ^ k') := by rw [h3]; group
  | inv x _ hx =>
    obtain ⟨i, j, k, rfl⟩ := hx
    refine ⟨-i, -j, -k, ?_⟩
    have h1 : (a ^ i * c ^ j * d ^ k)⁻¹ = d ^ (-k) * c ^ (-j) * a ^ (-i) := by
      rw [mul_inv_rev, mul_inv_rev, zpow_neg, zpow_neg, zpow_neg, mul_assoc]
    rw [h1]
    have e1 : d ^ (-k) * c ^ (-j) = c ^ (-j) * d ^ (-k) := ((hcd'.zpow_zpow (-j) (-k)).eq).symm
    have e2 : d ^ (-k) * a ^ (-i) = a ^ (-i) * d ^ (-k) := ((had'.zpow_zpow (-i) (-k)).eq).symm
    have e3 : c ^ (-j) * a ^ (-i) = a ^ (-i) * c ^ (-j) := ((hac'.zpow_zpow (-i) (-j)).eq).symm
    rw [e1, mul_assoc, e2, ← mul_assoc, e3]

theorem injective_pow_triple [Finite G] {a c d : G} (hac : a * c = c * a) (had : a * d = d * a)
    (hcd : c * d = d * c) (ha : a ^ 3 = 1) (hc : c ^ 3 = 1) (hd : d ^ 3 = 1)
    (h27 : Nat.card (Subgroup.closure ({a, c, d} : Set G)) = 27) :
    Function.Injective (fun p : Fin 3 × Fin 3 × Fin 3 =>
      a ^ (p.1 : ℕ) * c ^ (p.2.1 : ℕ) * d ^ (p.2.2 : ℕ)) := by
  set K := Subgroup.closure ({a, c, d} : Set G)
  have haK : a ∈ K := Subgroup.subset_closure (by simp)
  have hcK : c ∈ K := Subgroup.subset_closure (by simp)
  have hdK : d ∈ K := Subgroup.subset_closure (by simp)
  let F : Fin 3 × Fin 3 × Fin 3 → K := fun p =>
    ⟨a ^ (p.1 : ℕ) * c ^ (p.2.1 : ℕ) * d ^ (p.2.2 : ℕ),
      K.mul_mem (K.mul_mem (K.pow_mem haK _) (K.pow_mem hcK _)) (K.pow_mem hdK _)⟩
  have hF : Function.Surjective F := by
    rintro ⟨z, hz⟩
    obtain ⟨i, j, k, rfl⟩ := exists_zpow_triple_of_mem_closure hac had hcd hz
    have h3 : ∀ x : G, x ^ 3 = 1 → x ^ (3 : ℤ) = 1 := fun x hx => by
      rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, hx]
    have hi : 0 ≤ i % 3 := Int.emod_nonneg _ (by norm_num)
    have hj : 0 ≤ j % 3 := Int.emod_nonneg _ (by norm_num)
    have hk : 0 ≤ k % 3 := Int.emod_nonneg _ (by norm_num)
    refine ⟨(⟨(i % 3).toNat, by omega⟩, ⟨(j % 3).toNat, by omega⟩, ⟨(k % 3).toNat, by omega⟩),
      Subtype.ext ?_⟩
    simp only [F]
    rw [zpow_eq_zpow_emod i (h3 a ha), zpow_eq_zpow_emod j (h3 c hc),
      zpow_eq_zpow_emod k (h3 d hd), ← zpow_natCast, ← zpow_natCast, ← zpow_natCast,
      Int.toNat_of_nonneg hi, Int.toNat_of_nonneg hj, Int.toNat_of_nonneg hk]
  have hbij : Function.Bijective F := by
    refine (Function.Surjective.bijective_of_nat_card_le hF ?_)
    rw [h27]
    simp
  intro p q hpq
  exact hbij.1 (Subtype.ext hpq)

theorem isEmpty_quotient_wreath {P : Type*} [Group P] [Finite P] {a c d : P}
    (h5 : Nat.card P = 3 ^ 5)
    (hd : ∀ K : Subgroup P, K.Normal → Nat.card K = 3 → K = Subgroup.zpowers d)
    (ha : ∀ x : P, x * a * x⁻¹ * a⁻¹ ∈ Subgroup.zpowers d)
    (hc : ∀ x : P, x * c * x⁻¹ * c⁻¹ ∈ Subgroup.zpowers d)
    (hac : a * c = c * a) (had : a * d = d * a) (hcd : c * d = d * c)
    (ha3 : a ^ 3 = 1) (hc3 : c ^ 3 = 1) (hd3 : d ^ 3 = 1)
    (h27 : Nat.card (Subgroup.closure ({a, c, d} : Set P)) = 27) :
    ∀ (K : Subgroup P) [K.Normal], IsEmpty (P ⧸ K ≃* W33) := by
  intro K _
  refine ⟨fun e => ?_⟩
  have hcardQ : Nat.card (P ⧸ K) = 81 := (Nat.card_congr e.toEquiv).trans card_wreath
  have hK3 : Nat.card K = 3 := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup K
    rw [h5, hcardQ] at this
    omega
  have hKd : K = Subgroup.zpowers d := hd K inferInstance hK3
  have hKn : (Subgroup.zpowers d).Normal := hKd ▸ inferInstance
  have hcen : ∀ y : P, (∀ x : P, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.zpowers d) →
      ((y : P ⧸ K)) ∈ Subgroup.center (P ⧸ K) := by
    intro y hy
    rw [Subgroup.mem_center_iff]
    intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, hKd]
      have h2 : (x * y)⁻¹ * (y * x) = y⁻¹ * (x⁻¹ * y * x⁻¹⁻¹ * y⁻¹) * y⁻¹⁻¹ := by group
      rw [h2]
      exact hKn.conj_mem _ (hy x⁻¹) y⁻¹
  have hcen_pow : ∀ i j : ℕ, ((a ^ i * c ^ j : P) : P ⧸ K) ∈ Subgroup.center (P ⧸ K) := by
    intro i j
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_pow, QuotientGroup.mk_pow]
    exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (hcen a ha) i) (Subgroup.pow_mem _ (hcen c hc) j)
  let φ : Fin 3 × Fin 3 → Subgroup.center (P ⧸ K) := fun p =>
    ⟨((a ^ (p.1 : ℕ) * c ^ (p.2 : ℕ) : P) : P ⧸ K), hcen_pow _ _⟩
  have hinj := injective_pow_triple hac had hcd ha3 hc3 hd3 h27
  have hφ : Function.Injective φ := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ h
    have h1 : ((a ^ (i : ℕ) * c ^ (j : ℕ) : P) : P ⧸ K) =
        ((a ^ (i' : ℕ) * c ^ (j' : ℕ) : P) : P ⧸ K) := congrArg Subtype.val h
    rw [QuotientGroup.eq, hKd] at h1
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
    have hk0 : 0 ≤ k % 3 := Int.emod_nonneg _ (by norm_num)
    have hd3' : d ^ (3 : ℤ) = 1 := by
      rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, hd3]
    set k' : Fin 3 := ⟨(k % 3).toNat, by omega⟩ with hk'
    have hdk : d ^ k = d ^ (k' : ℕ) := by
      rw [zpow_eq_zpow_emod k hd3', hk', Fin.val_mk, ← zpow_natCast, Int.toNat_of_nonneg hk0]
    have heq : a ^ (i' : ℕ) * c ^ (j' : ℕ) * d ^ ((0 : Fin 3) : ℕ) =
        a ^ (i : ℕ) * c ^ (j : ℕ) * d ^ (k' : ℕ) := by
      rw [← hdk, hk]
      simp only [Fin.val_zero, pow_zero, mul_one]
      group
    have h2 := @hinj (i', j', 0) (i, j, k') heq
    simp only [Prod.mk.injEq] at h2
    rw [h2.1, h2.2.1]
  have h9 : 9 ≤ Nat.card (Subgroup.center (P ⧸ K)) := by
    have := Nat.card_le_card_of_injective φ hφ
    simpa using this
  have h3 : Nat.card (Subgroup.center (P ⧸ K)) ≤ 3 := by
    rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    exact card_center_wreath_le
  omega

end CFSG.RankThree.PartTwo.Sec11
