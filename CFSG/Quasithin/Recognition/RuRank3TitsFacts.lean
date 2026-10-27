module

public import CFSG.Sporadic.Schreier.TitsAutD
public import CFSG.Quasithin.Recognition.RuRank3TitsSyl

public section

namespace CFSG.Quasithin.RuRank3

open CFSG.Sporadic.Schreier.Tits

theorem commutator_titsA_eq
    : commutator titsA = titsD.subgroupOf titsA := by
  apply Subgroup.map_injective titsA.subtype_injective
  rw [map_subtype_commutator', titsA_commutator, Subgroup.subgroupOf_map_subtype,
    inf_of_le_left titsD_le_titsA]

theorem eq_titsD_of_index_eq_two
    {H : Subgroup titsA} (hH : H.index = 2) :
    H = titsD.subgroupOf titsA := by
  have hN : H.Normal := Subgroup.normal_of_index_eq_two hH
  have hcomm : commutator titsA ≤ H := by
    rw [← Subgroup.Normal.quotient_commutative_iff_commutator_le]
    have hc2 : Nat.card (titsA ⧸ H) = 2 := by
      rw [← Subgroup.index_eq_card, hH]
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hcyc : IsCyclic (titsA ⧸ H) := isCyclic_of_prime_card hc2
    exact ⟨⟨fun a b => hcyc.commGroup.mul_comm a b⟩⟩
  rw [commutator_titsA_eq] at hcomm
  symm
  apply Subgroup.eq_of_le_of_card_ge hcomm
  have h1 := Subgroup.card_mul_index H
  have h2 := Subgroup.card_mul_index (titsD.subgroupOf titsA)
  rw [hH] at h1
  rw [titsD_index] at h2
  omega

theorem centralizer_titsD
    :
    Subgroup.centralizer ((titsD.subgroupOf titsA : Subgroup titsA) : Set titsA) = ⊥ := by
  rw [eq_bot_iff]
  intro a ha
  rw [Subgroup.mem_bot]
  apply titsConj_injective
  rw [map_one]
  apply MulEquiv.ext
  intro d
  apply Subtype.ext
  rw [coe_titsConj_apply]
  have hd : (⟨d, titsD_le_titsA d.2⟩ : titsA) ∈ titsD.subgroupOf titsA := by
    rw [Subgroup.mem_subgroupOf]
    exact d.2
  have e := congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 ha _ hd)
  rw [Subgroup.coe_mul, Subgroup.coe_mul] at e
  show (a : Equiv.Perm (Fin 1755)) * d * (a : Equiv.Perm (Fin 1755))⁻¹ = d
  rw [← e, mul_inv_cancel_right]

theorem isPreprimitive_titsA
    : MulAction.IsPreprimitive titsA (Fin 1755) := by
  have := titsA_pretransitive
  have hD := CERT_Tits_derived_primitive
  refine { isTrivialBlock_of_isBlock := fun {B} hB => ?_ }
  apply hD.isTrivialBlock_of_isBlock
  intro d₁ d₂ h
  exact hB (g₁ := ⟨d₁, titsD_le_titsA d₁.2⟩) (g₂ := ⟨d₂, titsD_le_titsA d₂.2⟩) h

theorem eq_or_eq_top_of_card_eq
    {Q K : Subgroup titsA} (hQ : Nat.card Q = 2 ^ 12 * 5)
    (hQK : Q ≤ K) : K = Q ∨ K = ⊤ := by
  obtain ⟨x, rfl⟩ := exists_eq_stabilizer_of_card (by rw [hQ]; norm_num)
  have := isPreprimitive_titsA
  have hco := MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive (G := titsA) x
  by_cases h : K = MulAction.stabilizer titsA x
  · exact Or.inl h
  · exact Or.inr (hco.2 K (lt_of_le_of_ne hQK (Ne.symm h)))

theorem eq_or_eq_top_of_card_eq'
    {F : Type*} [Group F] (ψ : F ≃* titsA) {Q K : Subgroup F}
    (hQ : Nat.card Q = 2 ^ 12 * 5) (hQK : Q ≤ K) : K = Q ∨ K = ⊤ := by
  have hQ' : Nat.card (Q.map ψ.toMonoidHom) = 2 ^ 12 * 5 := by
    rw [← Nat.card_congr (Subgroup.equivMapOfInjective Q _ ψ.injective).toEquiv, hQ]
  rcases eq_or_eq_top_of_card_eq hQ' (Subgroup.map_mono hQK) with h | h
  · left
    exact Subgroup.map_injective (f := ψ.toMonoidHom) ψ.injective h
  · right
    apply Subgroup.map_injective (f := ψ.toMonoidHom) ψ.injective
    rw [h, Subgroup.map_top_of_surjective _ ψ.surjective]

end CFSG.Quasithin.RuRank3
