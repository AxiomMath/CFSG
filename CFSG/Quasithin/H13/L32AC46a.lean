module

public import CFSG.Quasithin.Recognition.F112J2Setup

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

theorem card_sq_eq_one_quaternion :
    Nat.card {q : QuaternionGroup 2 // q * q = 1} = 2 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem false_of_isQ8D8 {P : Type*} [Group P] [Finite P] (hP : IsQ8D8 P) {E : Subgroup P}
    (hE : ∀ x ∈ E, x * x = 1) (hc : 16 ≤ Nat.card E) : False := by
  classical
  obtain ⟨h32, A, -, -, ⟨eA⟩, -⟩ := hP
  have hA8 : Nat.card A = 8 := by
    rw [Nat.card_congr eA.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hEi := E.index_mul_card
  have hAi := A.index_mul_card
  have hIi := (E ⊓ A : Subgroup P).index_mul_card
  rw [h32] at hEi hAi hIi
  rw [hA8] at hAi
  have hEi2 : E.index ≤ 2 := by
    by_contra hlt
    push Not at hlt
    have : 3 * 16 ≤ E.index * Nat.card E := Nat.mul_le_mul hlt hc
    omega
  have hAi4 : A.index = 4 := by omega
  have hinf : (E ⊓ A : Subgroup P).index ≤ 8 :=
    (Subgroup.index_inf_le).trans (by rw [hAi4]; omega)
  have h4 : 4 ≤ Nat.card (E ⊓ A : Subgroup P) := by
    by_contra hlt
    push Not at hlt
    have : (E ⊓ A : Subgroup P).index * Nat.card (E ⊓ A : Subgroup P) ≤ 8 * 3 :=
      Nat.mul_le_mul hinf (by omega)
    omega
  let f : ↥(E ⊓ A : Subgroup P) → {q : QuaternionGroup 2 // q * q = 1} := fun x =>
    ⟨eA ⟨x, x.2.2⟩, by
      rw [← map_mul]
      have : (⟨x, x.2.2⟩ : ↥A) * ⟨x, x.2.2⟩ = 1 := Subtype.ext (hE x x.2.1)
      rw [this, map_one]⟩
  have hf : Function.Injective f := by
    intro a b h
    have h1 := eA.injective (congrArg Subtype.val h)
    exact Subtype.ext (congrArg (fun y : ↥A => (y : P)) h1)
  have := Nat.card_le_card_of_injective f hf
  rw [card_sq_eq_one_quaternion] at this
  omega

variable {G : Type} [Group G] [Finite G]

theorem borelOf_le_of_perm3 {I T : Subgroup G} (hS : IsSylowTwoOf (T ⊓ I) I)
    (hperm : Nonempty (oTwoQuot ↥I ≃* Equiv.Perm (Fin 3))) : borelOf I T ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hne : borelOf I T ≠ I := by
    intro h
    have hN : I ≤ Subgroup.normalizer ((T ⊓ I : Subgroup G) : Set G) := fun x hx => by
      have hx' : x ∈ borelOf I T := by rw [h]; exact hx
      exact hx'.2
    have hle : T ⊓ I ≤ pCoreOf 2 I := le_pCoreOf_of_le_normalizer 2 inf_le_right hN hS.2.1
    have h3 := F112J2.relIndex_inf_eq_three hS hperm
    have h6 := F112W.relIndex_pCoreOf_eq_six hperm
    have hdvd : (pCoreOf 2 I).relIndex I ∣ (T ⊓ I).relIndex I :=
      Subgroup.relIndex_dvd_of_le_left I hle
    rw [h3, h6] at hdvd
    omega
  rw [F112J2.borelOf_eq_inf_of_perm3 hS hperm hne]
  exact inf_le_left

end CFSG.Quasithin.H13.L32A.C
