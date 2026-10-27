module

public import CFSG.Quasithin.Vol2.F134Basic
public import CFSG.Quasithin.Recognition.CertOvergroup

public section

namespace CFSG.Quasithin.F134

open CFSG.Quasithin.P134 CFSG.QuasithinUnique
open scoped Pointwise

theorem E9Config.exists_model_sylow {A : Type} [Group A] [Finite A] {L P T : Subgroup A}
    (h : E9Config L P T) {Y : Type*} [Group Y] (e : ↥L ≃* Y) :
    ∃ H S : Subgroup Y, IsPGroup 2 S ∧ ¬ 2 ∣ S.index ∧ S ≤ H ∧ Nat.card H = 9 * Nat.card S := by
  have hS := E9Config.isSylowTwoOf_inf h
  refine ⟨((P ⊔ (T ⊓ L)).subgroupOf L).map e.toMonoidHom,
    ((T ⊓ L).subgroupOf L).map e.toMonoidHom, ?_, ?_, ?_, ?_⟩
  · exact (hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm).map _
  · have := Subgroup.index_map_equiv ((T ⊓ L).subgroupOf L) e
    erw [this]
    exact hS.2.2
  · exact Subgroup.map_mono (Subgroup.subgroupOf_mono L le_sup_right)
  · rw [← Nat.card_congr (((P ⊔ (T ⊓ L)).subgroupOf L).equivMapOfInjective _ e.injective).toEquiv,
      ← Nat.card_congr (((T ⊓ L).subgroupOf L).equivMapOfInjective _ e.injective).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (E9Config.sup_inf_le h)).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS.1).toEquiv]
    exact E9Config.card_sup_inf h

theorem card_eq_of_overgroupData {Y : Type*} [Group Y] [Finite Y] {ι κ : Type*}
    (d : OvergroupData Y ι κ) (hT : IsPGroup 2 d.T) (hTi : ¬ 2 ∣ d.T.index)
    {H S : Subgroup Y} (hS : IsPGroup 2 S) (hSi : ¬ 2 ∣ S.index) (hSH : S ≤ H) :
    Nat.card S = Nat.card d.T ∧ (Nat.card H = Nat.card d.T ∨ Nat.card H = Nat.card d.A ∨
      Nat.card H = Nat.card d.B ∨ Nat.card H = Nat.card Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Y (hS.toSylow hSi) (hT.toSylow hTi)
  have hTS : ∀ x ∈ d.T, (MulAut.conj g)⁻¹ x ∈ S := by
    intro x hx
    have hx' : x ∈ ((g • hS.toSylow hSi : Sylow 2 Y) : Subgroup Y) := by
      rw [hg]
      exact hx
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx'
    exact hx'
  have hcardS : Nat.card S = Nat.card d.T := by
    have := congrArg (fun Q : Sylow 2 Y => Nat.card (Q : Subgroup Y)) hg
    simp only [Sylow.coe_subgroup_smul, IsPGroup.toSylow] at this
    rw [← this, Subgroup.pointwise_smul_def]
    exact Nat.card_congr (S.equivMapOfInjective _ (MulAut.conj g).injective).toEquiv
  refine ⟨hcardS, ?_⟩
  set H' := H.map (MulAut.conj g).toMonoidHom
  have hH' : Nat.card H' = Nat.card H :=
    (Nat.card_congr (H.equivMapOfInjective _ (MulAut.conj g).injective).toEquiv).symm
  have hTH' : d.T ≤ H' := by
    intro x hx
    refine ⟨(MulAut.conj g)⁻¹ x, hSH (hTS x hx), ?_⟩
    change (MulAut.conj g) ((MulAut.conj g)⁻¹ x) = x
    rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
  rw [← hH']
  rcases d.lattice H' hTH' with h | h | h | h <;> rw [h]
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Subgroup.card_top)))

theorem noE9Config_of_overgroupData {Y : Type*} [Group Y] [Finite Y] {ι κ : Type*}
    (d : OvergroupData Y ι κ) (hT : IsPGroup 2 d.T) (hTi : ¬ 2 ∣ d.T.index)
    (hA : Nat.card d.A ≠ 9 * Nat.card d.T) (hB : Nat.card d.B ≠ 9 * Nat.card d.T)
    (hY : Nat.card Y ≠ 9 * Nat.card d.T) {F : ∀ (X : Type) [Group X], Prop}
    (hF : ∀ (X : Type) [Group X], F X → Nonempty (X ≃* Y)) : NoE9Config F := by
  intro A _ _ L P T hL hcfg
  obtain ⟨e⟩ := hF L hL
  obtain ⟨H, S, hS, hSi, hSH, hH⟩ := E9Config.exists_model_sylow hcfg e
  obtain ⟨hcS, hc⟩ := card_eq_of_overgroupData d hT hTi hS hSi hSH
  rw [hH, hcS] at hc
  have hT0 : 0 < Nat.card d.T := Nat.card_pos
  rcases hc with h | h | h | h
  · omega
  · exact hA h.symm
  · exact hB h.symm
  · exact hY h.symm

end CFSG.Quasithin.F134
