module

public import CFSG.Quasithin.EmptyFaithful.SzN21Sl3
public import CFSG.Quasithin.EmptyFaithful.SzN2Sp

public section

namespace CFSG.Quasithin

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.QuasithinUnique CFSG.Quasithin.SzN2

namespace SzN21

section Sp4

variable {K : Type} [Field K]

theorem exists_units_orderThree_of_dvd [Finite K] (h : 3 ∣ Nat.card K - 1) :
    ∃ ω : Kˣ, orderOf ω = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h' : 3 ∣ Nat.card Kˣ := by rw [Nat.card_units]; exact h
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' 3 h'
  exact ⟨ω, hω⟩

theorem three_dvd_sub_one_of_dvd_mul {q a b e : ℕ} (hq : q = 2 ^ e) (h : 3 ∣ q ^ a * (q - 1) ^ b) :
    3 ∣ q - 1 := by
  rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h1 | h2
  · exfalso
    have h3 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h1
    rw [hq] at h3
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega
  · exact Nat.Prime.dvd_of_dvd_pow Nat.prime_three h2

@[expose] noncomputable def torusSp4 (K : Type) [Field K] [Finite K] : Kˣ × Kˣ →* StatedSp 2 K where
  toFun p := SymplecticTorusWeyl.torusHom (r := 2) (k := K) ![p.1, p.2]
  map_one' := by
    have : (![1, 1] : Fin 2 → Kˣ) = 1 := by
      ext i
      fin_cases i <;> rfl
    show SymplecticTorusWeyl.torusHom (r := 2) (k := K) ![1, 1] = 1
    rw [this, map_one]
  map_mul' p q := by
    have : (![p.1 * q.1, p.2 * q.2] : Fin 2 → Kˣ) = ![p.1, p.2] * ![q.1, q.2] := by
      ext i
      fin_cases i <;> rfl
    show SymplecticTorusWeyl.torusHom (r := 2) (k := K) ![p.1 * q.1, p.2 * q.2] = _
    rw [this, map_mul]

theorem torusSp4_injective [Finite K] : Function.Injective (torusSp4 K) := by
  intro p q h
  have h1 : (![p.1, p.2] : Fin 2 → Kˣ) = ![q.1, q.2] :=
    SymplecticTorusWeyl.torusHom_injective (r := 2) (k := K) h
  exact Prod.ext (congrFun h1 0) (congrFun h1 1)

theorem torusSp4_mem_borel [Finite K] (p : Kˣ × Kˣ) : torusSp4 K p ∈ borelSubgroup 2 K :=
  torus_le_borelSubgroup ⟨![p.1, p.2], rfl⟩

theorem rbProp_unipotent_two [Finite K] [CharP K 2] {e : ℕ} (hK : Nat.card K = 2 ^ e)
    (hK4 : ∃ s : Finset K, s.card = 4) : RBProp (unipotent 2 K) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h0
    have hc := card_unipotent (K := K) 2
    rw [h0, Subgroup.card_bot] at hc
    obtain ⟨s, hs⟩ := hK4
    have : Fintype K := Fintype.ofFinite K
    have h4 : 4 ≤ Nat.card K := by
      rw [Nat.card_eq_fintype_card, ← hs]
      exact Finset.card_le_univ s
    have h5 : 1 < Nat.card K ^ (2 ^ 2) := Nat.one_lt_pow (by norm_num) (by omega)
    omega
  · intro R hUR hRs
    exact sp4_solvable_overgroup_le_normalizer hK4 (unipotent 2 K) R isSylowTwoOf_unipotent hUR hRs
  · rintro ⟨y, hy, hy3⟩
    rw [normalizer_unipotent] at hy
    have hdvd : 3 ∣ Nat.card (borelSubgroup 2 K) := by
      have := orderOf_dvd_natCard (⟨y, hy⟩ : borelSubgroup 2 K)
      rwa [Subgroup.orderOf_mk, hy3] at this
    rw [card_borelSubgroup] at hdvd
    obtain ⟨ω, hω⟩ := exists_units_orderThree_of_dvd (three_dvd_sub_one_of_dvd_mul hK hdvd)
    obtain ⟨E, hE, hE3, hEe, hEc⟩ := exists_elemAbelian_nine (torusSp4 K) torusSp4_injective
      (N := borelSubgroup 2 K) torusSp4_mem_borel hω
    exact ⟨E, by rw [normalizer_unipotent]; exact hE, hE3, hEe, hEc⟩

theorem rankTwoBorel_sp4 {Ω : Type} [Group Ω] {X S : Subgroup Ω} [Finite K] {e : ℕ}
    (hK : Nat.card K = 2 ^ e) (he : 2 ≤ e) (iso : ↥X ≃* ↥(StatedSp 2 K)) (hS : IsSylowTwoOf S X) :
    S ≠ ⊥ ∧
      (∀ R : Subgroup Ω, S ≤ R → R ≤ X → Group.IsSolvable ↥R →
        R ≤ Subgroup.normalizer (S : Set Ω)) ∧
      ((∃ y ∈ Subgroup.normalizer (S : Set Ω) ⊓ X, orderOf y = 3) →
        ∃ E : Subgroup Ω, E ≤ Subgroup.normalizer (S : Set Ω) ⊓ X ∧ IsPGroup 3 E ∧
          (∀ x ∈ E, x ^ 3 = 1) ∧ Nat.card E = 9) := by
  have hF : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 2 ^ e := by rw [← Nat.card_eq_fintype_card]; exact hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcp : CharP K 2 := charP_of_card_eq_prime_pow hcard
  have h4 := exists_finset_card_four (four_le_card_of_two_pow hK he)
  exact rankTwoBorel_of_model iso hS isSylowTwoOf_unipotent (rbProp_unipotent_two hK h4)

end Sp4

end SzN21

end CFSG.Quasithin
