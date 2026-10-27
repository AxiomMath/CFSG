module

public import CFSG.LocalAnalysis.StandardType.GGTriD4KnownInputs
public import CFSG.LieType.Steinberg.CentralExt.GriessTriality
import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResHopf

public section

namespace CFSG.StandardType

section SchurHolds


theorem ggTriD4SchurInput_holds : GGTriD4SchurInput := by
  intro n hn K _ _ hK _ X _ _ hX θ
  haveI : CharP K 2 := charP_two_of_card (m := n * 3) (by rw [hK, pow_mul])
  set σ := iterateFrobeniusEquiv K 2 n with hσdef
  have hσ : ∀ c, σ c = c ^ 2 ^ n := fun c => by
    rw [hσdef, iterateFrobeniusEquiv_apply, iterateFrobenius_def]
  obtain ⟨e⟩ := centerQuot_twistedH_equiv K .D4 n σ.toRingHom hσ
  obtain ⟨-, hM⟩ := CFSG.LieType.Steinberg.CentralExt.GriessExceptional.triality_hopfMultiplier
    (σ := σ.toRingHom) (q := 2 ^ n) (Nat.le_self_pow (by omega) 2) hK hσ
  let D := CFSG.Blueprint.DerivedCentralQuotient
    (CFSG.Blueprint.twistedFixedGroup .D4 K σ.toRingHom)
  let Θ : X ⧸ Subgroup.center X ≃* D := θ.trans e
  let π : X →* D := Θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))
  have hπ : Function.Surjective π := by
    change Function.Surjective
      (Θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X)))
    exact Θ.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center X))
  have hker : π.ker = Subgroup.center X := by
    change (Θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))).ker =
      Subgroup.center X
    rw [MonoidHom.ker_comp_of_injective (QuotientGroup.mk' (Subgroup.center X))
      Θ.toMonoidHom Θ.injective, QuotientGroup.ker_mk']
  obtain ⟨ψ, hψ⟩ :=
    CFSG.EvenSporadicStandard.M24Std.exists_surjective_hopfMultiplier hX π hπ hker.le
  haveI : Subsingleton (CFSG.Open.griessHopfMultiplier D) := hM
  haveI : Subsingleton π.ker := hψ.subsingleton
  rw [← hker]
  exact Subgroup.eq_bot_of_subsingleton π.ker

end SchurHolds

end CFSG.StandardType
