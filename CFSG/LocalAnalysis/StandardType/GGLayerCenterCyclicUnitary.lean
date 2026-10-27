module

public import CFSG.LocalAnalysis.StandardType.GGLayerCenterCyclicLinear
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryTorus
public import CFSG.LieType.Steinberg.CentralExt.SUCentrallyClosed
public import CFSG.LieType.Steinberg.CentralExt.SUOddClosed

public section

namespace CFSG.StandardType

open CFSG.Assembly

open LayerCC in
theorem ggPSections_su
    {d n : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hd : 3 ≤ d) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) : GGPSections p (LargeEvenSUGroup (Fin d) K (2 ^ n)) := by
  intro E _ _ η hη hker hpk
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := (TableBU.unitaryFieldData_of_card hK hn).charP
  have hEq : LargeEvenSUGroup (Fin d) K (2 ^ n) = LowTwoRank.StatedSU d (2 ^ n) K := rfl
  set e : ↥(LargeEvenSUGroup (Fin d) K (2 ^ n)) ≃*
      CFSG.LieType.Universal.Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution K 2 n) d :=
    (MulEquiv.subgroupCongr hEq).trans (CFSG.LieType.Universal.Unitary.equivStatedSU hK d).symm
    with he
  set η' := e.toMonoidHom.comp η with hη'def
  have hker' : η'.ker = η.ker := by
    ext x
    show e (η x) = 1 ↔ η x = 1
    exact map_eq_one_iff _ e.injective
  have hη' : Function.Surjective η' := e.surjective.comp hη
  have hcen' : η'.ker ≤ Subgroup.center E := hker' ▸ hker
  have hpk' : IsPGroup p η'.ker := hker' ▸ hpk
  obtain ⟨s, hs⟩ : ∃ s : CFSG.LieType.Universal.Unitary.SU
      (CFSG.LieType.BorelTits.unitaryInvolution K 2 n) d →* E, ∀ x, η' (s x) = x := by
    by_cases hev : Even d
    · refine CFSG.LieType.Steinberg.CentralExt.SUClosed.su_exists_section_of_coprime hK hev
        (by omega) hη' hcen' ?_
      have h2 := not_two_dvd_card_of_isPGroup hp hp2 hpk'
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2
    · exact CFSG.LieType.Steinberg.CentralExt.SUOdd.su_odd_exists_section_of_ne hK hn hp hp2 hd
        hev hη' hcen' hpk'
  refine ⟨s.comp e.toMonoidHom, fun y => ?_⟩
  apply e.injective
  exact hs (e y)

end CFSG.StandardType

end
