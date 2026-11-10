
module

public import CFSG.Quasithin.Recognition.RuRank3Tits13Base
public meta import CFSG.Quasithin.Recognition.RuRank3Tits13Base
public meta import CFSG.Sporadic.Schreier.TitsInv
public meta import CFSG.Sporadic.Schreier.TitsInvCheck
public meta import CFSG.Sporadic.Schreier.RuCheckChains
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import Certificates.Data.CFSGNative.Schreier.Check
public import CFSG.Sporadic.Schreier.TitsAbelCheckInputs
public meta import CFSG.Sporadic.Schreier.TitsData
public meta import CFSG.Sporadic.Schreier.TitsArrays
public meta import CFSG.Sporadic.Schreier.TitsBasic
public meta import CFSG.Sporadic.Schreier.TitsCertCheck
public meta import CFSG.Sporadic.Schreier.TitsLocalCheck
public meta import CFSG.Sporadic.Schreier.TitsEnum
public meta import CFSG.Sporadic.Schreier.TitsCentralCheck
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data
public import CFSG.Sporadic.Schreier.TitsActionCheckInputs
public import CFSG.Sporadic.Schreier.TitsCentralCheckInputs
public import CFSG.Sporadic.Schreier.TitsCertCheckInputs
public import CFSG.Sporadic.Schreier.TitsInvCheckInputs
public meta import CFSG.Sporadic.Schreier.TitsAbelCheck
public import CFSG.Sporadic.Schreier.TitsLocalCheckInputs
public import CFSG.Sporadic.Schreier.TitsStabCheckInputs
public meta import CFSG.Sporadic.Schreier.TitsActionCheck
public meta import CFSG.Sporadic.Schreier.TitsOrbit
public import CFSG.Quasithin.Recognition.RuRank3TitsClsInputs
public import CFSG.Quasithin.Recognition.RuRank3Tits13Inputs
public import CFSG.Quasithin.Recognition.RuRank3TitsSyl
public import CFSG.Quasithin.Recognition.RuRank3PSL
public import CFSG.Sporadic.Schreier.TitsAction
public import CFSG.Sporadic.Schreier.TitsChain
public import CFSG.Sporadic.Schreier.RuChainSpec
public import CFSG.Sporadic.Schreier.RuConj

@[expose] public section

namespace CFSG.Quasithin.RuRank3

open CFSG.Sporadic.Schreier.Tits CFSG.Sporadic.RuSchreier
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
open scoped MatrixGroups

attribute [local instance] fact_prime_five'

def titsK0Levels : Array Level :=
  rawLevels 1755 titsK0Strong (ruBaseArr 1755 [0, 12, 1])

theorem mem_titsD_iff_inTitsD {a : Array ℕ}
    {g : Equiv.Perm (Fin 1755)} (hg : Rep 1755 a g) :
    inTitsD a = true ↔ g ∈ titsD := by
  rw [← titsQD_original]
  exact siftA_iff_mem_ofArrays (n := 1755) (hn := by norm_num) (hk := by
      rw [titsDerivedArrs_size]; norm_num) (hb := by decide) (chunks := 4)
    titsChains_check.2.2.2.2.2.2.1 (by norm_num) titsChains_check.2.2.2.2.2.2.2.2.2.1 hg

noncomputable def titsAux : Equiv.Perm (Fin 1755) := permOfArr 1755 titsAuxArr

noncomputable def titsY12 : Equiv.Perm (Fin 1755) := permOfArr 1755 titsY12Arr

noncomputable def titsRep (i : ℕ) : Equiv.Perm (Fin 1755) := permOfArr 1755 (titsRepArr i)

noncomputable def titsK0Chain : RawSchreierDatum 1755 :=
  RawSchreierDatum.ofArrays 1755 (by norm_num) titsK0Strong 3 (by simp [titsK0Strong])
    (ruFinList 1755 (by norm_num) [0, 12, 1]) (by decide) (ruWordsArr 3 5 titsK0Words)

noncomputable def titsK0 : Subgroup (Equiv.Perm (Fin 1755)) :=
  titsK0Chain.originalSubgroup

theorem titsK0_eq_closure :
    titsK0 = Subgroup.closure {g | ∃ i < 3, permOfArr 1755 titsK0Strong[i]! = g} := by
  rw [titsK0, titsK0Chain, RawSchreierDatum.originalSubgroup]
  congr 1
  ext g
  exact RawSchreierDatum.mem_ofArrays_original

theorem titsK0_original_mem {i : ℕ} (hi : i < 3) : permOfArr 1755 titsK0Strong[i]! ∈ titsK0 :=
  Subgroup.subset_closure (RawSchreierDatum.mem_ofArrays_original.2 ⟨i, hi, rfl⟩)

theorem mem_titsCNt_of_mem_D
    {c : Equiv.Perm (Fin 1755)} (hcD : c ∈ titsD)
    (hc : c * titsTInv = titsTInv * c) : ∃ a ∈ titsCNt, permOfArr 1755 a = c := by
  have hmem : c ∈ titsCt := by
    rw [titsD_centralizer_t.1]
    exact ⟨hcD, Subgroup.mem_centralizer_singleton_iff.2 hc⟩
  have := (Set.ext_iff.1 titsCt_eq c).1 hmem
  simpa using this

theorem titsTInv_inv :
    titsTInv⁻¹ = titsTInv := by
  rw [inv_eq_iff_mul_eq_one]
  exact titsTInv_mul_self

theorem conj_zpow_eq {G : Type*} [Group G] (g x : G) (j : ℤ) :
    g * x ^ j * g⁻¹ = (g * x * g⁻¹) ^ j := by
  have := map_zpow (MulAut.conj g) x j
  simp only [MulAut.conj_apply] at this
  exact this

noncomputable def badGen (i : ℕ) (h : ℕ) : Equiv.Perm (Fin 1755) :=
  if h = 0 then titsX13 else if h = 1 then titsTInv else titsRep i

theorem badLetters_get {i h : ℕ} (hh : h < 3) : (badLetters i)[h]! =
    if h = 0 then titsX13Arr else if h = 1 then titsTArr else titsRepArr i := by
  rw [badLetters, getElem!_pos _ h (by simpa using hh), Array.getElem_ofFn]

theorem badLetters_size (i : ℕ) : (badLetters i).size = 3 := by
  rw [badLetters, Array.size_ofFn]

end CFSG.Quasithin.RuRank3
