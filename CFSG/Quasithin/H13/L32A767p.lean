module

public import CFSG.Quasithin.SteinbergCBAlternatingAut
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Recognition.RuTypeSL3

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Quasithin.RuType
open scoped MatrixGroups

theorem exists_eq_map_conj_of_sylow {Q : Type} [Group Q] [Finite Q] {S₀ S : Subgroup Q}
    (h₀ : IsPGroup 2 S₀) (h₀i : ¬ 2 ∣ S₀.index) (h : IsPGroup 2 S) (hi : ¬ 2 ∣ S.index) :
    ∃ g : Q, S = S₀.map (MulAut.conj g).toMonoidHom := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Q (h₀.toSylow h₀i) (h.toSylow hi)
  refine ⟨g, ?_⟩
  have := congrArg (fun P : Sylow 2 Q => (P : Subgroup Q)) hg
  simp only [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe] at this
  rw [← this]
  rfl

@[expose] def a5KleinSet : Finset (Equiv.Perm (Fin 5)) :=
  {1, Equiv.swap 0 1 * Equiv.swap 2 3, Equiv.swap 0 2 * Equiv.swap 1 3,
    Equiv.swap 0 3 * Equiv.swap 1 2}

theorem a5Klein_mul : ∀ a b : alternatingGroup (Fin 5), (a : Equiv.Perm (Fin 5)) ∈ a5KleinSet →
    (b : Equiv.Perm (Fin 5)) ∈ a5KleinSet → ((a * b : alternatingGroup (Fin 5)) :
      Equiv.Perm (Fin 5)) ∈ a5KleinSet := by
  decide +kernel

theorem a5Klein_inv : ∀ a : alternatingGroup (Fin 5), (a : Equiv.Perm (Fin 5)) ∈ a5KleinSet →
    ((a⁻¹ : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) ∈ a5KleinSet := by
  decide +kernel

@[expose] def a5Klein : Subgroup (alternatingGroup (Fin 5)) where
  carrier := {a | (a : Equiv.Perm (Fin 5)) ∈ a5KleinSet}
  mul_mem' {a b} ha hb := a5Klein_mul a b ha hb
  one_mem' := by decide +kernel
  inv_mem' {a} ha := a5Klein_inv a ha

instance : DecidablePred (· ∈ a5Klein) := fun a =>
  inferInstanceAs (Decidable ((a : Equiv.Perm (Fin 5)) ∈ a5KleinSet))

theorem card_a5Klein : Nat.card a5Klein = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem card_a5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  rfl

theorem a5Klein_exists_three : ∃ c : alternatingGroup (Fin 5), c ^ 3 = 1 ∧ c ≠ 1 ∧
    (∀ x ∈ a5Klein, c * x * c⁻¹ ∈ a5Klein) ∧ ∀ x ∈ a5Klein, c⁻¹ * x * c ∈ a5Klein := by
  decide +kernel

theorem a5Klein_two_elt : ∀ b : alternatingGroup (Fin 5),
    (∀ x ∈ a5Klein, b * x * b⁻¹ ∈ a5Klein) → b ^ 4 = 1 → b ∈ a5Klein := by
  decide +kernel

theorem a5_center : ∀ q : alternatingGroup (Fin 5), (∀ x, q * x = x * q) → q = 1 := by
  decide +kernel

theorem conj_injective_a5 :
    Function.Injective (MulAut.conj : alternatingGroup (Fin 5) →* MulAut _) := by
  rw [injective_iff_map_eq_one]
  intro q hq
  refine a5_center q fun x => ?_
  have := congrArg (fun φ : MulAut (alternatingGroup (Fin 5)) => φ x) hq
  simp only [MulAut.conj_apply, MulAut.one_apply] at this
  calc q * x = q * x * q⁻¹ * q := by group
    _ = x * q := by rw [this]

theorem card_mulAut_a5 : Nat.card (MulAut (alternatingGroup (Fin 5))) = 120 := by
  have e5 : Equiv.Perm (Fin 5) ≃* MulAut (alternatingGroup (Fin 5)) :=
    MulEquiv.ofBijective (SteinbergCB.conjPerm 5) ⟨SteinbergCB.conjPerm_injective (by norm_num),
      SteinbergCB.conjPerm_surjective (Or.inl rfl)⟩
  rw [← Nat.card_congr e5.toEquiv, Nat.card_perm, Nat.card_fin]
  rfl

theorem index_range_conj_a5 :
    (MulAut.conj : alternatingGroup (Fin 5) →* MulAut _).range.index = 2 := by
  have h1 := Subgroup.card_mul_index (MulAut.conj : alternatingGroup (Fin 5) →* MulAut _).range
  rw [← Nat.card_congr (MonoidHom.ofInjective conj_injective_a5).toEquiv, card_a5,
    card_mulAut_a5] at h1
  omega

theorem a5_pow_four {b : alternatingGroup (Fin 5)} {n : ℕ} (hb : b ^ 2 ^ n = 1) : b ^ 4 = 1 := by
  have h1 : orderOf b ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hb
  have h2 : orderOf b ∣ 4 * 15 := by
    rw [show (4 * 15 : ℕ) = Nat.card (alternatingGroup (Fin 5)) by rw [card_a5]]
    exact orderOf_dvd_natCard b
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  have hcop : Nat.Coprime (orderOf b) 15 := by
    rw [hk]
    exact Nat.Coprime.pow_left _ (by norm_num)
  exact orderOf_dvd_iff_pow_eq_one.mp (hcop.dvd_of_dvd_mul_right h2)

theorem a5_sylow_facts {S : Subgroup (alternatingGroup (Fin 5))} (hS : IsPGroup 2 S)
    (hSi : ¬ 2 ∣ S.index) :
    (∃ c ∈ Subgroup.normalizer (S : Set (alternatingGroup (Fin 5))), c ^ 3 = 1 ∧ c ≠ 1) ∧
      ∀ b ∈ Subgroup.normalizer (S : Set (alternatingGroup (Fin 5))), b ^ 4 = 1 → b ∈ S := by
  have h₀ : IsPGroup 2 a5Klein := IsPGroup.of_card (n := 2) (by rw [card_a5Klein]; norm_num)
  have h₀i : ¬ 2 ∣ a5Klein.index := by
    have := Subgroup.card_mul_index a5Klein
    rw [card_a5Klein, card_a5] at this
    omega
  obtain ⟨g, rfl⟩ := exists_eq_map_conj_of_sylow h₀ h₀i hS hSi
  have hmem : ∀ x, x ∈ a5Klein.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ a5Klein := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [mul_assoc] using hy
    · intro hx
      exact ⟨_, hx, by simp [mul_assoc]⟩
  obtain ⟨c, hc3, hc1, hcn, hcn'⟩ := a5Klein_exists_three
  refine ⟨⟨g * c * g⁻¹, ?_, ?_, ?_⟩, fun b hb hb4 => ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [hmem, hmem]
    constructor
    · intro hx
      have := hcn _ hx
      rwa [show c * (g⁻¹ * x * g) * c⁻¹ = g⁻¹ * (g * c * g⁻¹ * x * (g * c * g⁻¹)⁻¹) * g by
        group] at this
    · intro hx
      have := hcn' _ hx
      rwa [show c⁻¹ * (g⁻¹ * (g * c * g⁻¹ * x * (g * c * g⁻¹)⁻¹) * g) * c = g⁻¹ * x * g by
        group] at this
  · rw [conj_pow, hc3]
    group
  · intro h1
    apply hc1
    calc c = g⁻¹ * (g * c * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group
  · rw [hmem]
    refine a5Klein_two_elt _ (fun x hx => ?_) ?_
    · have hgx : g * x * g⁻¹ ∈ a5Klein.map (MulAut.conj g).toMonoidHom := by
        rw [hmem]
        simpa [mul_assoc] using hx
      have := (hmem _).mp ((Subgroup.mem_normalizer_iff.mp hb _).mp hgx)
      rwa [show g⁻¹ * (b * (g * x * g⁻¹) * b⁻¹) * g = g⁻¹ * b * g * x * (g⁻¹ * b * g)⁻¹ by
        group] at this
    · rw [show g⁻¹ * b * g = g⁻¹ * b * g⁻¹⁻¹ by rw [inv_inv], conj_pow, hb4]
      group

theorem sl3_two_elt_P0 : ∀ b : SL(3, ZMod 2), (∀ x ∈ SL3.P0, b * x * b⁻¹ ∈ SL3.P0) →
    b ^ 8 = 1 → b ∈ SL3.P0 := by
  decide +kernel

theorem sl3_exists_three_R0 : ∃ c : SL(3, ZMod 2), c ^ 3 = 1 ∧ c ≠ 1 ∧
    (∀ x ∈ SL3.R0, c * x * c⁻¹ ∈ SL3.R0) ∧ ∀ x ∈ SL3.R0, c⁻¹ * x * c ∈ SL3.R0 := by
  decide +kernel

theorem sl3_pow_eight {b : SL(3, ZMod 2)} {n : ℕ} (hb : b ^ 2 ^ n = 1) : b ^ 8 = 1 := by
  have h1 : orderOf b ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hb
  have h2 : orderOf b ∣ 8 * 21 := by
    rw [show (8 * 21 : ℕ) = Nat.card SL(3, ZMod 2) by rw [SL3.card_SL3]]
    exact orderOf_dvd_natCard b
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  have hcop : Nat.Coprime (orderOf b) 21 := by
    rw [hk]
    exact Nat.Coprime.pow_left _ (by norm_num)
  exact orderOf_dvd_iff_pow_eq_one.mp (hcop.dvd_of_dvd_mul_right h2)

theorem sl3_sylow_facts {S : Subgroup SL(3, ZMod 2)} (hS : IsPGroup 2 S) (hSi : ¬ 2 ∣ S.index) :
    ∃ W : Subgroup SL(3, ZMod 2), W ≤ S ∧ S ≤ Subgroup.normalizer (W : Set SL(3, ZMod 2)) ∧
      W.relIndex S = 2 ∧
      (∃ c ∈ Subgroup.normalizer (W : Set SL(3, ZMod 2)), c ^ 3 = 1 ∧ c ≠ 1) ∧
      ∀ b ∈ Subgroup.normalizer (S : Set SL(3, ZMod 2)), b ^ 8 = 1 → b ∈ S := by
  have h₀ : IsPGroup 2 SL3.P0 := IsPGroup.of_card (n := 3) (by rw [SL3.card_P0]; norm_num)
  have h₀i : ¬ 2 ∣ SL3.P0.index := by
    have := Subgroup.card_mul_index SL3.P0
    rw [SL3.card_P0, SL3.card_SL3] at this
    omega
  obtain ⟨g, rfl⟩ := exists_eq_map_conj_of_sylow h₀ h₀i hS hSi
  have hmem : ∀ (X : Subgroup SL(3, ZMod 2)) x,
      x ∈ X.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ X := by
    intro X x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [mul_assoc] using hy
    · intro hx
      exact ⟨_, hx, by simp [mul_assoc]⟩
  obtain ⟨c, hc3, hc1, hcn, hcn'⟩ := sl3_exists_three_R0
  refine ⟨SL3.R0.map (MulAut.conj g).toMonoidHom, Subgroup.map_mono SL3.R0_le_P0, ?_, ?_,
    ⟨g * c * g⁻¹, ?_, ?_, ?_⟩, fun b hb hb8 => ?_⟩
  · intro s hs
    rw [hmem] at hs
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [hmem, hmem]
    have hp := SL3.P0_le_Stab0 hs
    constructor
    · intro hx
      have := SL3.conj_mem_R0 _ hp _ hx
      rwa [show g⁻¹ * s * g * (g⁻¹ * x * g) * (g⁻¹ * s * g)⁻¹ = g⁻¹ * (s * x * s⁻¹) * g by
        group] at this
    · intro hx
      have := SL3.conj_mem_R0 _ (inv_mem hp) _ hx
      rwa [show (g⁻¹ * s * g)⁻¹ * (g⁻¹ * (s * x * s⁻¹) * g) * (g⁻¹ * s * g)⁻¹⁻¹ =
        g⁻¹ * x * g by group] at this
  · rw [Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]
    have e := Subgroup.relIndex_mul_card SL3.R0 SL3.P0
    rw [inf_eq_left.mpr SL3.R0_le_P0, SL3.card_R0, SL3.card_P0] at e
    omega
  · rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [hmem, hmem]
    constructor
    · intro hx
      have := hcn _ hx
      rwa [show c * (g⁻¹ * x * g) * c⁻¹ = g⁻¹ * (g * c * g⁻¹ * x * (g * c * g⁻¹)⁻¹) * g by
        group] at this
    · intro hx
      have := hcn' _ hx
      rwa [show c⁻¹ * (g⁻¹ * (g * c * g⁻¹ * x * (g * c * g⁻¹)⁻¹) * g) * c = g⁻¹ * x * g by
        group] at this
  · rw [conj_pow, hc3]
    group
  · intro h1
    apply hc1
    calc c = g⁻¹ * (g * c * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group
  · rw [hmem]
    refine sl3_two_elt_P0 _ (fun x hx => ?_) ?_
    · have hgx : g * x * g⁻¹ ∈ SL3.P0.map (MulAut.conj g).toMonoidHom := by
        rw [hmem]
        simpa [mul_assoc] using hx
      have := (hmem _ _).mp ((Subgroup.mem_normalizer_iff.mp hb _).mp hgx)
      rwa [show g⁻¹ * (b * (g * x * g⁻¹) * b⁻¹) * g = g⁻¹ * b * g * x * (g⁻¹ * b * g)⁻¹ by
        group] at this
    · rw [show g⁻¹ * b * g = g⁻¹ * b * g⁻¹⁻¹ by rw [inv_inv], conj_pow, hb8]
      group

end CFSG.Quasithin.H13.L32A
