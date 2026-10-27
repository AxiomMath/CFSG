module

public import CFSG.Permutation.FiveTransitive.DegreeFourteenSevenSquare
public import CFSG.Permutation.FiveTransitive.DegreeFourteenAlternatingQuotient
public import CFSG.Permutation.FiveTransitive.PrimitiveNormalDegreeDivisor
public import CFSG.Permutation.FiveTransitive.A9SmallActionOrbits

public section

namespace CFSG

namespace FiveTransitive.DegreeFourteenPrimitiveQuotient
open MulAction

private theorem injective_of_surjective
    {E F : Type*} [Fintype E] [DecidableEq E] [Fintype F] [DecidableEq F]
    (hE : Nat.card E = 14) (hF : Nat.card F = 9)
    (B : Subgroup (Equiv.Perm E)) (hprim : IsPreprimitive B E)
    (tau : B →* alternatingGroup F) (hsur : Function.Surjective tau) :
    Function.Injective tau := by
  classical
  let _ : IsPreprimitive B E := hprim
  let _ : Nonempty E := Finite.card_pos_iff.mp (by omega)
  let _ : Nontrivial F := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have hAF : Nat.card (alternatingGroup F) = 181440 := by
    rw [nat_card_alternatingGroup,hF]; norm_num [Nat.factorial]
  have hn49 : ¬ 49 ∣ Nat.card B := by
    intro h49
    exact DegreeFourteenAlternatingQuotient.not_surjective hE hF B
      (DegreeFourteenSevenSquare.alternating_le B hprim hE h49) tau hsur
  apply (MonoidHom.ker_eq_bot_iff tau).mp
  by_contra hn
  have hN := PrimitiveNormalDegreeDivisor.degree_dvd_card (E := E) tau.ker hn
  rw [hE] at hN
  have h7 : 7 ∣ Nat.card tau.ker := dvd_trans (by decide : 7 ∣ 14) hN
  have hm := tau.ker.card_mul_index
  rw [Subgroup.index_ker,MonoidHom.range_eq_top.mpr hsur,Subgroup.card_top,hAF] at hm
  have h49 : 49 ∣ Nat.card tau.ker * 181440 :=
    Nat.mul_dvd_mul h7 (by decide : 7 ∣ 181440)
  exact hn49 (hm ▸ h49)

theorem not_surjective
    {E F : Type*} [Fintype E] [DecidableEq E] [Fintype F] [DecidableEq F]
    (hE : Nat.card E = 14) (hF : Nat.card F = 9)
    (B : Subgroup (Equiv.Perm E)) (hprim : IsPreprimitive B E)
    (tau : B →* alternatingGroup F) : ¬ Function.Surjective tau := by
  classical
  intro hsur
  let _ : IsPreprimitive B E := hprim
  let _ : Nonempty E := Finite.card_pos_iff.mp (by omega)
  have hi := injective_of_surjective hE hF B hprim tau hsur
  let e : B ≃* alternatingGroup F := MulEquiv.ofBijective tau ⟨hi,hsur⟩
  let _ : MulAction (alternatingGroup F) E := MulAction.compHom E e.symm.toMonoidHom
  let _ : IsPretransitive (alternatingGroup F) E := by
    constructor
    intro x y
    obtain ⟨b,hb⟩ := (inferInstance : IsPretransitive B E).exists_smul_eq x y
    refine ⟨e b,?_⟩
    change e.symm (e b) • x = y
    simpa using hb
  let x : E := Classical.choice inferInstance
  have hc := A9SmallActionOrbits.card_one_or_nine hF hE.le x
  rw [orbit_eq_univ] at hc
  simp only [Nat.card_coe_set_eq,Set.ncard_univ,hE] at hc
  omega

end FiveTransitive.DegreeFourteenPrimitiveQuotient

end CFSG
