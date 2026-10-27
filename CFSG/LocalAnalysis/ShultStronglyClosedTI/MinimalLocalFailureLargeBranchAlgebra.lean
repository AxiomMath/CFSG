module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAbelianNormalizer
public import CFSG.LocalAnalysis.ComponentInitial.FieldFiniteAutomorphism
public import Mathlib.GroupTheory.SchurZassenhaus

public section

namespace CFSG.ShultStronglyClosedTI.FinalChain.LargeBranch

open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

section Commutator

variable {Γ : Type*} [Group Γ]

theorem commutator_eq_one_of_odd_pow {x v : Γ} {n : ℕ} (hn : Odd n) (hxn : x ^ n = 1)
    (hw : x * (v⁻¹ * x * v * x⁻¹) = v⁻¹ * x * v * x⁻¹ * x)
    (hw2 : (v⁻¹ * x * v * x⁻¹) ^ 2 = 1) : v⁻¹ * x * v * x⁻¹ = 1 := by
  set w := v⁻¹ * x * v * x⁻¹ with hwdef
  have hxv : x * v * x⁻¹ = v * w := by
    rw [hwdef]
    group
  have hxw : ∀ k : ℕ, x * w ^ k * x⁻¹ = w ^ k := by
    intro k
    rw [← conj_pow, show x * w * x⁻¹ = w by rw [hw]; group]
  have key : ∀ k : ℕ, x ^ k * v * (x ^ k)⁻¹ = v * w ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc x ^ (k + 1) * v * (x ^ (k + 1))⁻¹ = x * (x ^ k * v * (x ^ k)⁻¹) * x⁻¹ := by group
        _ = x * v * x⁻¹ * (x * w ^ k * x⁻¹) := by rw [ih]; group
        _ = v * w ^ (k + 1) := by rw [hxv, hxw, pow_succ', mul_assoc]
  have hwn : w ^ n = 1 := by
    have h := key n
    rw [hxn, one_mul, inv_one, mul_one] at h
    exact mul_eq_left.mp h.symm
  obtain ⟨j, rfl⟩ := hn
  rwa [pow_succ, pow_mul, hw2, one_pow, one_mul] at hwn

theorem exists_commutator_subgroup (V : Subgroup Γ) (hVn : V.Normal)
    (hcomm : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v) (hsq : ∀ v ∈ V, v ^ 2 = 1) {x : Γ} {n : ℕ}
    (hn : Odd n) (hxn : x ^ n = 1) :
    ∃ L : Subgroup Γ, L ≤ V ∧ (∀ v ∈ V, v⁻¹ * x * v * x⁻¹ ∈ L) ∧
      (∀ c ∈ L, x * c = c * x → c = 1) ∧ (∀ g ∈ V, ∀ c ∈ L, g * c * g⁻¹ ∈ L) ∧
      ∀ g : Γ, ∀ k : ℕ, g * x * g⁻¹ = x ^ k → ∀ c ∈ L, g * c * g⁻¹ ∈ L := by
  have hD : ∀ v ∈ V, v⁻¹ * x * v * x⁻¹ ∈ V := fun v hv => by
    rw [show v⁻¹ * x * v * x⁻¹ = v⁻¹ * (x * v * x⁻¹) by group]
    exact V.mul_mem (V.inv_mem hv) (hVn.conj_mem v hv x)
  let L : Subgroup Γ :=
    { carrier := {c | ∃ v ∈ V, v⁻¹ * x * v * x⁻¹ = c}
      mul_mem' := by
        rintro _ _ ⟨v, hv, rfl⟩ ⟨w, hw, rfl⟩
        refine ⟨v * w, V.mul_mem hv hw, ?_⟩
        have h := hcomm _ (V.inv_mem hw) _ (hD v hv)
        calc (v * w)⁻¹ * x * (v * w) * x⁻¹ = w⁻¹ * (v⁻¹ * x * v * x⁻¹) * (x * w * x⁻¹) := by
              group
          _ = v⁻¹ * x * v * x⁻¹ * (w⁻¹ * x * w * x⁻¹) := by rw [h]; group
      one_mem' := ⟨1, V.one_mem, by group⟩
      inv_mem' := by
        rintro _ ⟨v, hv, rfl⟩
        refine ⟨v⁻¹, V.inv_mem hv, ?_⟩
        have h := hcomm _ hv _ (hVn.conj_mem _ (V.inv_mem hv) x)
        calc v⁻¹⁻¹ * x * v⁻¹ * x⁻¹ = v * (x * v⁻¹ * x⁻¹) := by group
          _ = x * v⁻¹ * x⁻¹ * v := h
          _ = (v⁻¹ * x * v * x⁻¹)⁻¹ := by group }
  have hmem : ∀ v ∈ V, v⁻¹ * x * v * x⁻¹ ∈ L := fun v hv => ⟨v, hv, rfl⟩
  have hpow : ∀ k : ℕ, ∀ w ∈ V, w⁻¹ * x ^ k * w * (x ^ k)⁻¹ ∈ L := by
    intro k
    induction k with
    | zero =>
      intro w _
      simp only [pow_zero, mul_one, inv_one, inv_mul_cancel]
      exact L.one_mem
    | succ k ih =>
      intro w hw
      have h := L.mul_mem (ih w hw) (hmem _ (hVn.conj_mem w hw (x ^ k)))
      have heq : w⁻¹ * x ^ (k + 1) * w * (x ^ (k + 1))⁻¹ = w⁻¹ * x ^ k * w * (x ^ k)⁻¹ *
          ((x ^ k * w * (x ^ k)⁻¹)⁻¹ * x * (x ^ k * w * (x ^ k)⁻¹) * x⁻¹) := by group
      rw [heq]
      exact h
  refine ⟨L, ?_, hmem, ?_, ?_, ?_⟩
  · rintro _ ⟨v, hv, rfl⟩
    exact hD v hv
  · rintro _ ⟨v, hv, rfl⟩ hc
    exact commutator_eq_one_of_odd_pow hn hxn hc (hsq _ (hD v hv))
  · rintro g hg _ ⟨v, hv, rfl⟩
    rw [hcomm g hg _ (hD v hv), mul_inv_cancel_right]
    exact hmem v hv
  · rintro g k hgk _ ⟨v, hv, rfl⟩
    have heq : g * (v⁻¹ * x * v * x⁻¹) * g⁻¹ =
        (g * v * g⁻¹)⁻¹ * (g * x * g⁻¹) * (g * v * g⁻¹) * (g * x * g⁻¹)⁻¹ := by group
    rw [heq, hgk]
    exact hpow k _ (hVn.conj_mem v hv g)

end Commutator

section IndexTwo

theorem exists_index_two_of_isCyclic {C : Type*} [Group C] [Finite C] [IsCyclic C]
    (h2 : 2 ∣ Nat.card C) : ∃ C₀ : Subgroup C, C₀.index = 2 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := C)
  have hord : orderOf g = Nat.card C := orderOf_eq_card_of_forall_mem_zpowers hg
  refine ⟨Subgroup.zpowers (g ^ 2), ?_⟩
  have hcard : Nat.card (Subgroup.zpowers (g ^ 2)) = Nat.card C / 2 := by
    rw [Nat.card_zpowers, orderOf_pow_of_dvd two_ne_zero (hord ▸ h2), hord]
  have h := (Subgroup.zpowers (g ^ 2)).card_mul_index
  rw [hcard] at h
  obtain ⟨m, hm⟩ := h2
  have hpos : 0 < Nat.card C := Nat.card_pos
  rw [hm, Nat.mul_div_cancel_left m two_pos] at h
  exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < m) (h.trans (mul_comm 2 m))

theorem isCyclic_ringAut (k : Type*) [Field k] [Finite k] : IsCyclic (RingAut k) := by
  let : Fintype k := Fintype.ofFinite k
  obtain ⟨p, -, n, hp, hcard⟩ := FiniteField.card' k
  obtain ⟨σ, -, -, hσ, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality (F := k)
      hp n.pos (by rw [Nat.card_eq_fintype_card, hcard])
  exact isCyclic_iff_exists_zpowers_eq_top.mpr ⟨σ, hσ⟩

theorem exists_index_two_of_semilinear {Γ : Type*} [Group Γ] [Finite Γ] {k : Type*} [Field k]
    [Finite k] (hk : Odd (Nat.card kˣ)) (ι : Γ →* kˣ ⋊[ringAutUnits k] RingAut k)
    (hker : Nat.card ι.ker = 2)
    (hinl : (SemidirectProduct.inl : kˣ →* kˣ ⋊[ringAutUnits k] RingAut k).range ≤ ι.range) :
    ∃ Γ₀ : Subgroup Γ, Γ₀.index = 2 := by
  let ρ : Γ →* RingAut k := SemidirectProduct.rightHom.comp ι
  have : IsCyclic (RingAut k) := isCyclic_ringAut k
  have : Finite ρ.range := Finite.of_surjective _ ρ.rangeRestrict_surjective
  by_cases h2 : 2 ∣ Nat.card ρ.range
  · obtain ⟨S₀, hS₀⟩ := exists_index_two_of_isCyclic h2
    exact ⟨S₀.comap ρ.rangeRestrict, by
      rw [Subgroup.index_comap_of_surjective _ ρ.rangeRestrict_surjective, hS₀]⟩
  · let r : ι.range →* RingAut k := SemidirectProduct.rightHom.domRestrict ι.range
    have hr_range : r.range = ρ.range := by
      rw [MonoidHom.domRestrict_range, MonoidHom.map_range]
    have hr_ker : Nat.card r.ker = Nat.card kˣ := by
      rw [MonoidHom.ker_domRestrict, ← SemidirectProduct.range_inl_eq_ker_rightHom,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hinl).toEquiv,
        ← Nat.card_congr (MonoidHom.ofInjective SemidirectProduct.inl_injective).toEquiv]
    have hcard : Nat.card ι.range = Nat.card kˣ * Nat.card ρ.range := by
      rw [← hr_ker, ← hr_range]
      exact (Subgroup.card_ker_mul_card_range r).symm
    have hodd : Odd (Nat.card ι.range) := by
      rw [hcard]
      exact hk.mul (Nat.odd_iff.mpr (by omega))
    have hcop : Nat.Coprime (Nat.card ι.ker) ι.ker.index := by
      rw [hker, Subgroup.index_ker]
      exact Nat.coprime_two_left.mpr hodd
    obtain ⟨Γ₀, hΓ₀⟩ := Subgroup.exists_right_complement'_of_coprime hcop
    refine ⟨Γ₀, ?_⟩
    have h1 := hΓ₀.card_mul_card
    have h3 := Γ₀.card_mul_index
    rw [hker] at h1
    have hpos : 0 < Nat.card Γ₀ := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hpos (h3.trans (h1.symm.trans (mul_comm 2 _)))

end IndexTwo

end CFSG.ShultStronglyClosedTI.FinalChain.LargeBranch
