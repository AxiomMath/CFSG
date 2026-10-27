module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42LocGeom
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42LocE16

public section

namespace CFSG.Quasithin.H13.F431.U42

open CFSG.Quasithin CFSG.Open U42F431
open scoped Pointwise

theorem T_le_P1 : T ≤ P1 := T_le_B0.trans B0_le_P1

theorem isPGroup_two_of_sq {E : Subgroup Y} (hsq : ∀ a ∈ E, a * a = 1) : IsPGroup 2 E := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [IsPGroup.iff_orderOf]
  intro g
  have h2 : g ^ 2 = 1 := Subtype.ext (by rw [pow_two]; exact hsq g g.2)
  rcases (Nat.dvd_prime Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one h2) with h | h
  · exact ⟨0, by simp [h]⟩
  · exact ⟨1, by simp [h]⟩

@[expose] noncomputable def sylowTP1 :
    Sylow 2 ↥P1 :=
  (IsPGroup.of_equiv isSylow_T.2.1 (Subgroup.subgroupOfEquivOfLe T_le_P1).symm).toSylow (by
    have h := Subgroup.card_mul_index (T.subgroupOf P1)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe T_le_P1).toEquiv, card_T, card_P1] at h
    omega)

theorem coe_sylowTP1 :
    (sylowTP1 : Subgroup ↥P1) = T.subgroupOf P1 := rfl

theorem exists_P1_conj_of_elemAbelian
    {E : Subgroup Y} (hEP : E ≤ P1) (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hsq : ∀ a ∈ E, a * a = 1) (hcard : Nat.card Vsub ≤ Nat.card E) :
    ∃ m ∈ P1, E = Vconj m := by
  have hEk : IsPGroup 2 (E.subgroupOf P1) :=
    IsPGroup.of_equiv (isPGroup_two_of_sq hsq) (Subgroup.subgroupOfEquivOfLe hEP).symm
  obtain ⟨S, hS⟩ := hEk.exists_le_sylow
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq ↥P1 sylowTP1 S
  have hxS : (MulAut.conj x • (T.subgroupOf P1) : Subgroup ↥P1) = (S : Subgroup ↥P1) := by
    have h1 := congrArg (fun P : Sylow 2 ↥P1 => (P : Subgroup ↥P1)) hx
    simpa only [Sylow.coe_subgroup_smul, coe_sylowTP1] using h1
  have hET : E.map (MulAut.conj (x : Y)⁻¹).toMonoidHom ≤ T := by
    rintro _ ⟨e, he, rfl⟩
    have h1 : (⟨e, hEP he⟩ : ↥P1) ∈ (S : Subgroup ↥P1) := hS (Subgroup.mem_subgroupOf.2 he)
    rw [← hxS, Subgroup.mem_smul_pointwise_iff_exists] at h1
    obtain ⟨t, ht, hte⟩ := h1
    have ht' : (t : Y) ∈ T := Subgroup.mem_subgroupOf.1 ht
    have h2 : (x : Y) * (t : Y) * (x : Y)⁻¹ = e := congrArg Subtype.val hte
    simpa [MulAut.conj_apply, ← h2, mul_assoc] using ht'
  have hE' : E.map (MulAut.conj (x : Y)⁻¹).toMonoidHom = Vsub := by
    refine eq_Vsub_of_elemAbelian hET ?_ ?_ ?_
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      have := hcomm a ha b hb
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc (x : Y)⁻¹ * a * (x : Y)⁻¹⁻¹ * ((x : Y)⁻¹ * b * (x : Y)⁻¹⁻¹)
          = (x : Y)⁻¹ * (a * b) * (x : Y)⁻¹⁻¹ := by group
        _ = (x : Y)⁻¹ * (b * a) * (x : Y)⁻¹⁻¹ := by rw [this]
        _ = _ := by group
    · rintro _ ⟨a, ha, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc (x : Y)⁻¹ * a * (x : Y)⁻¹⁻¹ * ((x : Y)⁻¹ * a * (x : Y)⁻¹⁻¹)
          = (x : Y)⁻¹ * (a * a) * (x : Y)⁻¹⁻¹ := by group
        _ = 1 := by rw [hsq a ha]; group
    · rw [Subgroup.card_map_of_injective (MulAut.conj (x : Y)⁻¹).injective]
      exact hcard
  refine ⟨(x : Y), x.2, ?_⟩
  have h3 : E = (E.map (MulAut.conj (x : Y)⁻¹).toMonoidHom).map
      (MulAut.conj (x : Y)).toMonoidHom := by
    ext g
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · intro hg
      exact ⟨_, ⟨g, hg, rfl⟩, by group⟩
    · rintro ⟨_, ⟨e, he, rfl⟩, rfl⟩
      simpa [mul_assoc] using he
  rw [h3, hE']
  rfl

end CFSG.Quasithin.H13.F431.U42
