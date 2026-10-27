module

public import CFSG.Sporadic.Schreier.PairJ2Faithful
public import CFSG.Sporadic.Schreier.PairJ2Check

public noncomputable section

namespace CFSG.Sporadic.Schreier

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier.PairNative

theorem j2ChainArrays :
    ChainArrays j2Chain (j2StrongArrs.extract 0 2) j2StrongArrs PairJ2.baseArr j2Words :=
  chainArrays_ofArrays fun j hj => j2CertOK_parts.2.2.2.1 j (by simpa [j2StrongArrs] using hj)

theorem j2Chain_valid :
    ValidSchreier j2Chain ∧ ∀ i : Fin j2Chain.baseCount,
    j2Chain.orbitSize i = ((rawLevels 315 j2StrongArrs PairJ2.baseArr)[(i : ℕ)]!).pts.size :=
  validSchreier_of_chainOK j2ChainArrays (by norm_num) PairJ2.chain_check.1

theorem j2Chain_baseCount : j2Chain.baseCount = 3 := rfl

theorem j2Chain_orbitSizes :
    (List.finRange j2Chain.baseCount).map j2Chain.orbitSize = [315, 160, 12] := by
  rw [← PairJ2.chain_check.2, rawOrbitSizes]
  apply List.ext_getElem
  · rw [List.length_map, List.length_finRange, List.length_map, Array.length_toList, rawLevels,
      Array.size_ofFn]
    rfl
  · intro k h1 h2
    have hk : k < (rawLevels 315 j2StrongArrs PairJ2.baseArr).size := by simpa using h2
    simp only [List.getElem_map, List.getElem_finRange, Array.getElem_toList]
    rw [j2Chain_valid.2]
    show ((rawLevels 315 j2StrongArrs PairJ2.baseArr)[k]!).pts.size = _
    rw [getElem!_pos _ k hk]

theorem j2Chain_orbitSize
    (i : Fin j2Chain.baseCount) :
    j2Chain.orbitSize i = [315, 160, 12][(i : ℕ)]! := by
  rw [← j2Chain_orbitSizes, getElem!_pos _ (i : ℕ) (by simp)]
  simp

theorem card_j2P :
    Nat.card j2P = 604800 := by
  have h := (RawSchreierDatum.schreier_chain_order j2Chain j2Chain_valid.1).2.2.1
  rw [j2P_eq_original, h]
  simp only [← RawSchreierDatum.orbitSize_eq_card, j2Chain_orbitSize]
  rfl

theorem card_j2 :
    Nat.card Blueprint.NativeSporadic.J2 = 604800 := by
  rw [Nat.card_congr j2PermEquiv.toEquiv, card_j2P]

theorem FAM_J2_order :
    ValidSchreier j2Chain ∧ j2Chain.base.toList.map Fin.val = [1, 0, 2] ∧
      (List.finRange j2Chain.baseCount).map j2Chain.orbitSize = [315, 160, 12] ∧
      Nat.card j2P = 604800 ∧ Nat.card Blueprint.NativeSporadic.J2 = 604800 :=
  ⟨j2Chain_valid.1, j2Chain_base, j2Chain_orbitSizes, card_j2P, card_j2⟩

end CFSG.Sporadic.Schreier
