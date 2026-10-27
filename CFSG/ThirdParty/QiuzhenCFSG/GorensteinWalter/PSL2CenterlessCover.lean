module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OddCentralCoverAtCenterPrimes
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2CoprimeSylowCyclic

namespace CFSG
end CFSG
open CFSG

/-!
# Odd central covers of PSL(2,q)

A quasisimple central cover of `PSL(2,q)` has trivial odd center when the
center order is coprime to `q`.  At every prime in the center, coprimality
places the quotient Sylow subgroup in a cyclic torus; transfer then kills the
central kernel.
-/

noncomputable section

namespace CFSG.GorensteinWalter

open BenderSuzuki.MatrixGroups

universe u

/-- The odd-center `PSL₂` cover theorem in the coprime form used after
Section 4 equation (7). -/
public theorem center_eq_bot_of_quasisimple_psl2_quotient_coprime
    {E : Type u} [Group E] [Finite E]
    (hquasi : IsQuasisimple E)
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (hKseven : 7 ≤ Nat.card K)
    (hZodd : Odd (Nat.card (Subgroup.center E)))
    (hZcoprime : Nat.Coprime (Nat.card (Subgroup.center E)) (Nat.card K))
    (e : Nonempty ((E ⧸ Subgroup.center E) ≃* PSL2MatrixGroup K)) :
    Subgroup.center E = ⊥ := by
  rcases hK with ⟨p, f, hp, _hpodd, hf, hKcard⟩
  let : Fact p.Prime := ⟨hp⟩
  let Z : Subgroup E := Subgroup.center E
  let : Z.Normal := by
    dsimp [Z]
    infer_instance
  apply oddCentralCover_eq_bot_of_cyclic_sylow_at_center_primes
    hquasi.2.1 Z rfl hZodd
  intro r hrFact hrdiv hrne R
  have hrcop : Nat.Coprime r (Nat.card K) :=
    hZcoprime.coprime_dvd_left (by simpa [Z] using hrdiv)
  let Rbar : Sylow r (PSL2MatrixGroup K) :=
    Sylow.mapSurjective (f := e.some.toMonoidHom) e.some.surjective R
  have hbar : IsCyclic Rbar :=
    psl2_sylow_isCyclic_of_coprime_field_card K hKcard hKseven
      r hrne hrcop Rbar
  have hmap : (Rbar : Subgroup (PSL2MatrixGroup K)) =
      (R : Subgroup (E ⧸ Z)).map e.some.toMonoidHom := by
    exact Sylow.coe_mapSurjective (f := e.some.toMonoidHom) e.some.surjective R
  have hmapcyc : IsCyclic ((R : Subgroup (E ⧸ Z)).map e.some.toMonoidHom) := by
    change IsCyclic (Rbar : Subgroup (PSL2MatrixGroup K)) at hbar
    rw [hmap] at hbar
    exact hbar
  exact (e.some.subgroupMap (R : Subgroup (E ⧸ Z))).isCyclic.mpr hmapcyc

end CFSG.GorensteinWalter
