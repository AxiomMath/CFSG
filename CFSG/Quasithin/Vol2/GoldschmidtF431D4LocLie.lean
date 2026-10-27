module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4LocForest
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4LocCt

public section

namespace CFSG.Quasithin.D4Hex

open CFSG.LargeExtraspecial.S63 CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.D4Hex
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

theorem finite_D : Finite D :=
  Nat.finite_of_card_ne_zero (by rw [card_trialityGroup8]; norm_num)

theorem d4_sylow :
    IsSylowTwoOf d4U (⊤ : Subgroup D) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite D := finite_D
  refine ⟨le_top, IsPGroup.of_card (n := 12) (by rw [card_d4U']; norm_num), ?_⟩
  have h1 := d4U.card_mul_index
  rw [card_d4U', card_trialityGroup8] at h1
  have h2 : d4U.index = 51597 := by omega
  change ¬ 2 ∣ d4U.relIndex ⊤
  rw [Subgroup.relIndex_top_right, h2]
  decide

section Model


theorem d4U_le_centralizer_z : d4U ≤ Subgroup.centralizer ({d4z} : Set D) :=
  d4U_le_d4B.trans inf_le_left

theorem d4_not_conj_zt : ¬ IsConj d4z d4t := by
  have : Finite D := finite_D
  intro h
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  have hcard : Nat.card (Subgroup.centralizer ({d4z} : Set D)) =
      Nat.card (Subgroup.centralizer ({d4t} : Set D)) := by
    rw [← hc, card_centralizer_conj']
  have h1 : Nat.card d4U ≤ Nat.card (Subgroup.centralizer ({d4z} : Set D)) :=
    Subgroup.card_le_of_le d4U_le_centralizer_z
  rw [card_d4U', hcard, centralizer_d4t_eq, card_d4Ct] at h1
  omega

theorem d4_F431LieI : F431LieI d4U d4H d4N d4z d4t where
  sylow := d4_sylow
  T_le₁ := d4U_le_d4B.trans inf_le_left
  T_le₂ := d4U_le_d4B.trans inf_le_right
  z_mem := d4z_mem_d4U
  t_mem := d4t_mem_d4U
  hz := orderOf_d4z
  ht := orderOf_d4t
  not_conj := d4_not_conj_zt
  classes := fun x hx => by
    obtain ⟨c, hc | hc⟩ := exists_conj_of_orderOf_eq_two hx
    · exact Or.inl (isConj_iff.2 ⟨c, hc.symm⟩)
    · exact Or.inr (isConj_iff.2 ⟨c, hc.symm⟩)
  cent_z := rfl
  cent_t := centralizer_d4t_eq ▸ d4Ct_le_d4N
  center_T := fun w hw hc hw1 =>
    ⟨1, Subgroup.one_mem _, by rw [center_T_spec hw hc hw1]; group⟩
  inv_chain := inv_chain_spec

end Model

end CFSG.Quasithin.D4Hex
