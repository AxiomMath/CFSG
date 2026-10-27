module

public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.Quasithin

open CFSG.Open

variable {G : Type*} [Group G]

@[expose] def IsTwoChiefFactor (X A B : Subgroup G) : Prop :=
  B < A ∧ A ≤ X ∧ X ≤ Subgroup.normalizer (A : Set G) ∧ X ≤ Subgroup.normalizer (B : Set G) ∧
    (∀ C : Subgroup G, B < C → C < A → ¬ X ≤ Subgroup.normalizer (C : Set G)) ∧
    ∀ a ∈ A, ∃ k : ℕ, a ^ 2 ^ k ∈ B

@[expose] def AllTwoChiefFactorsCentral (X : Subgroup G) : Prop :=
  ∀ A B : Subgroup G, IsTwoChiefFactor X A B → ⁅A, X⁆ ≤ B

theorem isTwoChiefFactorOutsideO2_iff {X A B : Subgroup G} :
    IsTwoChiefFactorOutsideO2 X A B ↔ pCoreOf 2 X ≤ B ∧ IsTwoChiefFactor X A B := by
  unfold IsTwoChiefFactorOutsideO2 IsTwoChiefFactor
  tauto

section Sections

variable [Finite G]

omit [Finite G] in
theorem commutator_le_of_normalizes {K H : Subgroup G} (hKH : H ≤ Subgroup.normalizer (K : Set G)) :
    ⁅K, H⁆ ≤ K := by
  rw [Subgroup.commutator_le]
  intro k hk h hh
  have h1 : h * k⁻¹ * h⁻¹ ∈ K := by
    have := (Subgroup.mem_normalizer_iff.mp (hKH hh) k⁻¹).mp (K.inv_mem hk)
    simpa using this
  have : k * h * k⁻¹ * h⁻¹ = k * (h * k⁻¹ * h⁻¹) := by simp [mul_assoc]
  show k * h * k⁻¹ * h⁻¹ ∈ K
  rw [this]
  exact K.mul_mem hk h1

theorem exists_uniform_pow {N M : Subgroup G} (h : ∀ u ∈ N, ∃ k : ℕ, u ^ 2 ^ k ∈ M) :
    ∃ e : ℕ, ∀ u ∈ N, u ^ 2 ^ e ∈ M := by
  classical
  have : Fintype N := Fintype.ofFinite N
  choose f hf using fun u : N => h u.1 u.2
  refine ⟨Finset.univ.sup f, fun u hu => ?_⟩
  have hle : f ⟨u, hu⟩ ≤ Finset.univ.sup f := Finset.le_sup (Finset.mem_univ _)
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
  rw [hd, pow_add, pow_mul]
  exact M.pow_mem (hf ⟨u, hu⟩) _

omit [Finite G] in
theorem comm_pow_succ (p x : G) (n : ℕ) :
    p * x ^ (n + 1) * p⁻¹ * (x ^ (n + 1))⁻¹ =
      (p * x * p⁻¹ * x⁻¹) * (x * (p * x ^ n * p⁻¹ * (x ^ n)⁻¹) * x⁻¹) := by
  rw [pow_succ']
  group

theorem twoSection_central {H : Subgroup G} (hH : oTwoUpper H = H)
    (hCF : AllTwoChiefFactorsCentral H) :
    ∀ (d : ℕ) (M K : Subgroup G), Nat.card K - Nat.card M = d → M ≤ K → K ≤ H →
      H ≤ Subgroup.normalizer (K : Set G) → H ≤ Subgroup.normalizer (M : Set G) →
      (∀ x ∈ K, ∃ k : ℕ, x ^ 2 ^ k ∈ M) → ⁅K, H⁆ ≤ M := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro M K hd hMK hKH hKn hMn hK2
  by_cases hMKeq : M = K
  · subst hMKeq
    exact commutator_le_of_normalizes hKn
  have hlt : M < K := lt_of_le_of_ne hMK hMKeq
  set S : Set (Subgroup G) := {N | M < N ∧ N ≤ K ∧ H ≤ Subgroup.normalizer (N : Set G)} with hS
  have hSne : S.Nonempty := ⟨K, hlt, le_rfl, hKn⟩
  obtain ⟨N, hN, hNmin⟩ := Set.exists_min_image S (fun N => Nat.card N) (Set.toFinite S) hSne
  obtain ⟨hMN, hNK, hNn⟩ := hN
  have hcardlt : ∀ {X Y : Subgroup G}, X < Y → Nat.card X < Nat.card Y := by
    intro X Y hXY
    refine lt_of_le_of_ne (Subgroup.card_le_of_le hXY.le) fun h => ?_
    exact hXY.ne (Subgroup.eq_of_le_of_card_ge hXY.le h.ge)
  have hchief : IsTwoChiefFactor H N M := by
    refine ⟨hMN, hNK.trans hKH, hNn, hMn, fun C hMC hCN hCn => ?_,
      fun a ha => hK2 a (hNK ha)⟩
    have hCS : C ∈ S := ⟨hMC, hCN.le.trans hNK, hCn⟩
    have h1 := hNmin C hCS
    have h2 := hcardlt hCN
    omega
  have hNM : ⁅N, H⁆ ≤ M := hCF N M hchief
  have hMNc := hcardlt hMN
  have hNKc : Nat.card N ≤ Nat.card K := Subgroup.card_le_of_le hNK
  have hKN : ⁅K, H⁆ ≤ N := by
    refine ih (Nat.card K - Nat.card N) (by omega) N K rfl hNK hKH hKn hNn ?_
    intro x hx
    obtain ⟨k, hk⟩ := hK2 x hx
    exact ⟨k, hMN.le hk⟩
  have hconj : ∀ x ∈ H, ∀ m ∈ M, x * m * x⁻¹ ∈ M := fun x hx m hm =>
    (Subgroup.mem_normalizer_iff.mp (hMn hx) m).mp hm
  let C : Subgroup G :=
    { carrier := {x | x ∈ H ∧ ∀ p ∈ K, p * x * p⁻¹ * x⁻¹ ∈ M}
      one_mem' := ⟨H.one_mem, fun p _ => by simp⟩
      mul_mem' := fun {x y} hx hy => by
        refine ⟨H.mul_mem hx.1 hy.1, fun p hp => ?_⟩
        have h1 : p * (x * y) * p⁻¹ * (x * y)⁻¹ =
            (p * x * p⁻¹ * x⁻¹) * (x * (p * y * p⁻¹ * y⁻¹) * x⁻¹) := by group
        rw [h1]
        exact M.mul_mem (hx.2 p hp) (hconj x hx.1 _ (hy.2 p hp))
      inv_mem' := fun {x} hx => by
        refine ⟨H.inv_mem hx.1, fun p hp => ?_⟩
        have h1 : p * x⁻¹ * p⁻¹ * (x⁻¹)⁻¹ = x⁻¹ * (p * x * p⁻¹ * x⁻¹)⁻¹ * x := by group
        rw [h1]
        have := hconj x⁻¹ (H.inv_mem hx.1) _ (M.inv_mem (hx.2 p hp))
        simpa using this }
  have hHC : H ≤ C := by
    rw [← hH]
    refine oTwoUpper_le_of_pow_mem fun x hx => ?_
    obtain ⟨e, he⟩ := exists_uniform_pow (N := N) (M := M) fun u hu => hK2 u (hNK hu)
    refine ⟨e, H.pow_mem hx _, fun p hp => ?_⟩
    obtain ⟨u, hu⟩ : ∃ u : G, u = p * x * p⁻¹ * x⁻¹ := ⟨_, rfl⟩
    have hxH : x ∈ H := hx
    have huN : u ∈ N := by
      rw [hu]
      exact hKN (Subgroup.commutator_mem_commutator hp hxH)
    have hclaim : ∀ n : ℕ, ∃ m ∈ M, p * x ^ n * p⁻¹ * (x ^ n)⁻¹ = u ^ n * m := by
      intro n
      induction n with
      | zero => exact ⟨1, M.one_mem, by simp⟩
      | succ n ihn =>
        obtain ⟨m, hm, hmeq⟩ := ihn
        have hunN : u ^ n ∈ N := N.pow_mem huN n
        have h1 : (u ^ n)⁻¹ * x * (u ^ n)⁻¹⁻¹ * x⁻¹ ∈ M :=
          hNM (Subgroup.commutator_mem_commutator (N.inv_mem hunN) hxH)
        rw [inv_inv] at h1
        refine ⟨((u ^ n)⁻¹ * x * u ^ n * x⁻¹) * (x * m * x⁻¹),
          M.mul_mem h1 (hconj x hxH m hm), ?_⟩
        rw [comm_pow_succ, hmeq, ← hu, pow_succ']
        group
    obtain ⟨m, hm, hmeq⟩ := hclaim (2 ^ e)
    rw [hmeq]
    exact M.mul_mem (he u huN) hm
  rw [Subgroup.commutator_le]
  intro p hp x hx
  exact (hHC hx).2 p hp

end Sections

end CFSG.Quasithin
