module

public import CFSG.Quasithin.Background.B4L3Fin

public section

namespace CFSG.Quasithin.SmithL3Res

open CFSG.Quasithin.L3

@[expose] def StabMaps (c d d' : Vec) : Prop := ∃ s : Γ, act s c = c ∧ act s d = d'

instance instDecidableStabMaps (c d d' : Vec) : Decidable (StabMaps c d d') := by
  unfold StabMaps
  infer_instance

set_option maxRecDepth 100000 in
theorem stab_trans : ∀ c : Vec, c ≠ 0 → ∀ d : Vec, d ≠ 0 → d ≠ c → ∀ d' : Vec, d' ≠ 0 →
    d' ≠ c → StabMaps c d d' := by
  decide +kernel

theorem act_ne_zero (g : Γ) {v : Vec} (hv : v ≠ 0) : act g v ≠ 0 := by
  intro h
  apply hv
  rw [← act_inv_act g v, h, act_zero]

@[reducible] def mulActionVec : MulAction Γ Vec where
  smul := act
  one_smul := act_one
  mul_smul := act_mul

theorem exists_fixed_vec {H : Subgroup Γ} (hH : IsPGroup 2 H) :
    ∃ e : Vec, e ≠ 0 ∧ ∀ g ∈ H, act g e = e := by
  let _ := mulActionVec
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : 2 ∣ Nat.card Vec := by
    rw [Nat.card_eq_fintype_card]
    decide
  have h0 : (0 : Vec) ∈ MulAction.fixedPoints H Vec := fun g => act_zero g
  obtain ⟨b, hb, hne⟩ := hH.exists_fixed_point_of_prime_dvd_card_of_fixed_point Vec hcard h0
  exact ⟨b, Ne.symm hne, fun g hg => hb ⟨g, hg⟩⟩

theorem le_of_stabChar {G : Type*} [Group G] {L K H : Subgroup G} {α : ↥L →* Γ}
    (hα : Function.Surjective α) {e₀ : Vec} (he₀ : e₀ ≠ 0) (hK : ∀ l : ↥L, (l : G) ∈ K ↔
      act (α l) e₀ = e₀) (hKH : K ≤ H) (hHL : H ≤ L) (hH : H ≠ L) : H ≤ K := by
  by_contra hcon
  obtain ⟨h, hhH, hhK⟩ := IsConcreteLE.not_le_iff_exists.mp hcon
  apply hH
  refine le_antisymm hHL fun l hl => ?_
  set lL : ↥L := ⟨l, hl⟩ with hlL
  set hL' : ↥L := ⟨h, hHL hhH⟩ with hhL'
  have hd' : act (α hL') e₀ ≠ e₀ := fun he => hhK ((hK hL').2 he)
  by_cases hd : act (α lL) e₀ = e₀
  · exact hKH ((hK lL).2 hd)
  obtain ⟨s, hs1, hs2⟩ := stab_trans e₀ he₀ (act (α hL') e₀) (act_ne_zero _ he₀) hd'
    (act (α lL) e₀) (act_ne_zero _ he₀) hd
  obtain ⟨ls, rfl⟩ := hα s
  have hlsK : (ls : G) ∈ K := (hK ls).2 hs1
  have hx : act (α (ls * hL')) e₀ = act (α lL) e₀ := by rw [map_mul, act_mul, hs2]
  have hy : (((ls * hL')⁻¹ * lL : ↥L) : G) ∈ K := by
    refine (hK _).2 ?_
    rw [map_mul, map_inv, act_mul, ← hx, act_inv_act]
  have heq : l = (ls : G) * h * (((ls * hL')⁻¹ * lL : ↥L) : G) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hlL, hhL']
    group
  rw [heq]
  exact H.mul_mem (H.mul_mem (hKH hlsK) hhH) (hKH hy)

end CFSG.Quasithin.SmithL3Res
