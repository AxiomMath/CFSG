module

public import Mathlib.GroupTheory.Index
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

public section

namespace CFSG.StandardType.FF81.RootFusionLin

theorem index_comap_dvd_index {A H : Type*} [Group A] [Group H] (ψ : A →* H) (U : Subgroup H)
    [U.Normal] : (U.comap ψ).index ∣ U.index := by
  rw [Subgroup.index_comap]
  exact Subgroup.relIndex_dvd_index_of_normal U ψ.range

theorem padicValNat_card_le_comap {A H : Type*} [Group A] [Group H] [Finite A] [Finite H]
    (p : ℕ) [Fact p.Prime] (ψ : A →* H) (U : Subgroup H) [U.Normal] :
    padicValNat p (Nat.card A) ≤ padicValNat p (Nat.card (U.comap ψ)) + padicValNat p U.index := by
  have hK : Nat.card (U.comap ψ) ≠ 0 := Nat.card_pos.ne'
  have hKi : (U.comap ψ).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hUi : U.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hmul : Nat.card (U.comap ψ) * (U.comap ψ).index = Nat.card A :=
    Subgroup.card_mul_index (U.comap ψ)
  rw [← hmul, padicValNat.mul hK hKi]
  have h1 : padicValNat p (U.comap ψ).index ≤ padicValNat p U.index :=
    (padicValNat_dvd_iff_le hUi).mp
      ((pow_padicValNat_dvd (p := p) (n := (U.comap ψ).index)).trans
        (index_comap_dvd_index ψ U))
  omega

end CFSG.StandardType.FF81.RootFusionLin

end
