
module

public import CFSG.Sporadic.Schreier.RuOddCoreBase

public import CFSG.Sporadic.Schreier.RuAutInner
public import CFSG.Sporadic.Schreier.RuPair
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore
public import CFSG.GroupTheory.LocalCores.PrimeSetCore
public import CFSG.Sporadic.Schreier.RuCheckBasicInputs
public import CFSG.Sporadic.Schreier.RuCheckCentersInputs
public meta import CFSG.Sporadic.Schreier.RuCheckSylow
public import CFSG.Sporadic.Schreier.RuCheckChainsInputs
public import CFSG.Sporadic.Schreier.RuCheckInvInputs
public meta import CFSG.Sporadic.Schreier.RuTreeEltA
public meta import CFSG.Sporadic.Schreier.RuWitArrays
public meta import CFSG.Sporadic.Schreier.RuCheckChains
public meta import CFSG.Sporadic.Schreier.RuEnum
public import CFSG.Sporadic.Schreier.RuCheckIsoInputs
public import CFSG.Sporadic.Schreier.RuCheckLInputs
public import CFSG.Sporadic.Schreier.RuArrays
public import CFSG.Certificates.NativeSetOrbit
public import CFSG.Sporadic.Schreier.RuOrbLFacts
public import CFSG.Sporadic.Schreier.RuCheckOrbLBInputs
public meta import CFSG.Sporadic.Schreier.RuOrbLDefs
public import CFSG.Sporadic.Schreier.RuCheckTreeInputs
public import CFSG.Sporadic.Schreier.RuWitArrays
public import Certificates.Data.CFSGNative.Ru.Data

public noncomputable section

namespace CFSG.Sporadic.RuSchreier

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native

theorem noOddNormal_centralizer_ruA0 :
    NoOddNormal (ruP ⊓ Subgroup.centralizer {ruA0} : Subgroup _) :=
  NoOddNormal.of_mulEquiv (MulEquiv.subgroupCongr ruCentralizer_a.symm) ruL_noOddNormal

theorem noOddNormal_centralizer
    {t : Equiv.Perm (Fin 4060)} (ht : t ∈ ruP) (h2 : orderOf t = 2) :
    NoOddNormal (ruP ⊓ Subgroup.centralizer {t} : Subgroup _) := by
  have hinv : t ∈ {t | t ∈ ruP ∧ orderOf t = 2} := ⟨ht, h2⟩
  rw [ruInvolutions_eq] at hinv
  rcases hinv with ⟨g, hg, rfl⟩ | ⟨g, hg, rfl⟩
  · exact NoOddNormal.of_mulEquiv (conjCentralizerEquiv hg ruZ) noOddNormal_centralizer_ruZ
  · exact NoOddNormal.of_mulEquiv (conjCentralizerEquiv hg ruA0) noOddNormal_centralizer_ruA0

theorem CTUC_Ru_all_involution_centralizers_odd_core_free :
    ∀ t ∈ ruP, orderOf t = 2 →
      (∀ R : Subgroup (ruP ⊓ Subgroup.centralizer {t} : Subgroup (Equiv.Perm (Fin 4060))),
        R.Normal → Odd (Nat.card R) → R = ⊥) ∧
      CFSG.piCore {p : Nat.Primes | p.1 ≠ 2}
        (ruP ⊓ Subgroup.centralizer {t} : Subgroup (Equiv.Perm (Fin 4060))) = ⊥ ∧
      CFSG.pPrimeCore 2 (ruP ⊓ Subgroup.centralizer {t} : Subgroup (Equiv.Perm (Fin 4060))) = ⊥ ∧
      CFSG.oddCore (ruP ⊓ Subgroup.centralizer {t} : Subgroup (Equiv.Perm (Fin 4060))) = ⊥ :=
  fun _ ht h2 => ⟨noOddNormal_centralizer ht h2, (noOddNormal_centralizer ht h2).cores⟩

end CFSG.Sporadic.RuSchreier
