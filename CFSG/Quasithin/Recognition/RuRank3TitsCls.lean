
module

public import CFSG.Quasithin.Recognition.RuRank3TitsClsBase

public import CFSG.Quasithin.Recognition.RuRank3Tits13
public meta import CFSG.Quasithin.Recognition.RuRank3Tits13
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
public import Certificates.Certificate7050
public import CFSG.Quasithin.Recognition.RuRank3Tits13Inputs
public import CFSG.Quasithin.Recognition.RuRank3TitsSyl
public import CFSG.Quasithin.Recognition.RuRank3PSL
public import CFSG.Sporadic.Schreier.TitsAction
public import CFSG.Sporadic.Schreier.TitsChain
public import CFSG.Sporadic.Schreier.RuChainSpec
public import CFSG.Sporadic.Schreier.RuConj

public section

namespace CFSG.Quasithin.RuRank3

open CFSG.Sporadic.Schreier.Tits CFSG.Sporadic.RuSchreier
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
open scoped MatrixGroups

attribute [local instance] fact_prime_five'

theorem titsCls_check :
    isInvA 1755 titsAuxArr (invCand 1755 titsAuxArr) = true ∧ inTitsA titsAuxArr = true ∧
    inTitsD titsAuxArr = false ∧
    eqA 1755 (compA 1755 titsAuxArr titsTArr) (compA 1755 titsTArr titsAuxArr) = true ∧
    isInvA 1755 titsY12Arr (invCand 1755 titsY12Arr) = true ∧ inTitsA titsY12Arr = true ∧
    eqA 1755 (compA 1755 titsY12Arr titsTArr) (compA 1755 titsTArr titsY12Arr) = true ∧
    eqA 1755 (compA 1755 titsY12Arr titsX13Arr)
      (compA 1755 (powArr 1755 titsX13Arr 11) titsY12Arr) = true ∧
    (allLt 12 fun k => isInvA 1755 (powArr 1755 titsY12Arr k)
      (invCand 1755 (powArr 1755 titsY12Arr k))) = true ∧
    (titsCNt.all fun c => classOK c && classOK (compA 1755 titsAuxArr c)) = true ∧
    (allLt 30 fun i => isInvA 1755 (titsRepArr i) (invCand 1755 (titsRepArr i))) = true ∧
    titsRepGood.length = 30 ∧ titsBadWords.length = 30 ∧
    (allLt 30 fun i => if titsRepGood.getD i false then inTitsK0 (titsRepArr i) else
      badOK i) = true ∧
    ruChainOK 1755 titsK0Strong 3 5 [0, 12, 1] titsK0Words = true ∧
    rawOrbitSizes 1755 titsK0Strong (ruBaseArr 1755 [0, 12, 1]) = [975, 4, 2] ∧
    eqA 1755 titsK0Strong[0]! titsX13Arr = true ∧ eqA 1755 titsK0Strong[1]! titsTArr = true ∧
    inTitsA titsK0Strong[2]! = true ∧
    isInvA 1755 titsTArr (invCand 1755 titsTArr) = true ∧
    eqA 1755 (compA 1755 (compA 1755 (compA 1755 titsTArr titsX13Arr) titsTArr) titsX13Arr)
      (idA 1755) = true :=
  Certificates.certificate7050

theorem clsAux :
    isInvA 1755 titsAuxArr (invCand 1755 titsAuxArr) = true ∧
    inTitsA titsAuxArr = true ∧ inTitsD titsAuxArr = false ∧
    eqA 1755 (compA 1755 titsAuxArr titsTArr) (compA 1755 titsTArr titsAuxArr) = true := by
  obtain ⟨h1, h2, h3, h4, -⟩ := titsCls_check
  exact ⟨h1, h2, h3, h4⟩

theorem clsY12 :
    isInvA 1755 titsY12Arr (invCand 1755 titsY12Arr) = true ∧
    inTitsA titsY12Arr = true ∧
    eqA 1755 (compA 1755 titsY12Arr titsTArr) (compA 1755 titsTArr titsY12Arr) = true ∧
    eqA 1755 (compA 1755 titsY12Arr titsX13Arr)
      (compA 1755 (powArr 1755 titsX13Arr 11) titsY12Arr) = true ∧
    (allLt 12 fun k => isInvA 1755 (powArr 1755 titsY12Arr k)
      (invCand 1755 (powArr 1755 titsY12Arr k))) = true := by
  obtain ⟨-, -, -, -, h5, h6, h7, h8, h9, -⟩ := titsCls_check
  exact ⟨h5, h6, h7, h8, h9⟩

theorem clsClassOK :
    (titsCNt.all fun c => classOK c && classOK (compA 1755 titsAuxArr c)) = true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, h, -⟩ := titsCls_check
  exact h

theorem clsReps :
    (allLt 30 fun i => isInvA 1755 (titsRepArr i) (invCand 1755 (titsRepArr i)))
    = true ∧ titsRepGood.length = 30 ∧ titsBadWords.length = 30 ∧
    (allLt 30 fun i => if titsRepGood.getD i false then inTitsK0 (titsRepArr i) else
      badOK i) = true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h11, h12, h13, h14, -⟩ := titsCls_check
  exact ⟨h11, h12, h13, h14⟩

theorem clsK0 :
    ruChainOK 1755 titsK0Strong 3 5 [0, 12, 1] titsK0Words = true ∧
    rawOrbitSizes 1755 titsK0Strong (ruBaseArr 1755 [0, 12, 1]) = [975, 4, 2] ∧
    eqA 1755 titsK0Strong[0]! titsX13Arr = true ∧ eqA 1755 titsK0Strong[1]! titsTArr = true ∧
    inTitsA titsK0Strong[2]! = true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, h15, h16, h17, h18, h19, -⟩ := titsCls_check
  exact ⟨h15, h16, h17, h18, h19⟩

theorem clsT : isInvA 1755 titsTArr (invCand 1755 titsTArr) = true ∧
    eqA 1755 (compA 1755 (compA 1755 (compA 1755 titsTArr titsX13Arr) titsTArr) titsX13Arr)
      (idA 1755) = true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h20, h21⟩ := titsCls_check
  exact ⟨h20, h21⟩

theorem rep_titsAux :
    Rep 1755 titsAuxArr titsAux := (rep_permOfArr clsAux.1).1

theorem rep_titsY12 :
    Rep 1755 titsY12Arr titsY12 := (rep_permOfArr clsY12.1).1

theorem rep_titsRep {i : ℕ} (hi : i < 30) :
    Rep 1755 (titsRepArr i) (titsRep i) :=
  (rep_permOfArr (allLt_spec clsReps.1 hi)).1

theorem titsAux_mem :
    titsAux ∈ titsA := mem_titsA_of_inTitsA rep_titsAux clsAux.2.1

theorem titsAux_not_mem_D :
    titsAux ∉ titsD := fun h => by
  have := (mem_titsD_iff_inTitsD rep_titsAux).2 h
  rw [clsAux.2.2.1] at this
  exact Bool.false_ne_true this

theorem titsAux_comm :
    titsAux * titsTInv = titsTInv * titsAux :=
  eq_of_eqA (rep_compA rep_titsAux titsTInv_rep) (rep_compA titsTInv_rep rep_titsAux)
    clsAux.2.2.2

theorem titsY12_mem :
    titsY12 ∈ titsA := mem_titsA_of_inTitsA rep_titsY12 clsY12.2.1

theorem titsY12_comm :
    titsY12 * titsTInv = titsTInv * titsY12 :=
  eq_of_eqA (rep_compA rep_titsY12 titsTInv_rep) (rep_compA titsTInv_rep rep_titsY12)
    clsY12.2.2.1

theorem titsY12_conj :
    titsY12 * titsX13 = titsX13 ^ 11 * titsY12 :=
  eq_of_eqA (rep_compA rep_titsY12 rep_titsX13)
    (rep_compA (rep_powArr rep_titsX13 11) rep_titsY12) clsY12.2.2.2.1

theorem titsT_inverts_X13 :
    titsTInv * titsX13 * titsTInv⁻¹ = titsX13⁻¹ := by
  have h := eq_of_eqA (rep_compA (rep_compA (rep_compA titsTInv_rep rep_titsX13) titsTInv_rep)
    rep_titsX13) rep_idA clsT.2
  have ht : titsTInv⁻¹ = titsTInv := by
    rw [inv_eq_iff_mul_eq_one]
    exact titsTInv_mul_self
  rw [ht]
  exact eq_inv_of_mul_eq_one_left h

theorem card_titsK0 : Nat.card titsK0 = 7800 := by
  have h := ruChain_card (n := 1755) (hn := by norm_num) (hpos := by norm_num) (k := 3) (s := 5)
    (hk := by simp [titsK0Strong]) (b := [0, 12, 1]) (hb := by decide) clsK0.1
  rw [clsK0.2.1] at h
  exact h

theorem mem_titsK0_of_sift {a : Array ℕ} {g : Equiv.Perm (Fin 1755)}
    (hg : Rep 1755 a g)
    (h : inTitsK0 a = true) : g ∈ titsK0 :=
  (ruChain_sift (n := 1755) (hn := by norm_num) (hpos := by norm_num) (k := 3) (s := 5)
    (hk := by simp [titsK0Strong]) (b := [0, 12, 1]) (hb := by decide) clsK0.1 hg).1 h

theorem titsK0_strong_inv {i : ℕ} (hi : i < 5) :
    isInvA 1755 titsK0Strong[i]! (invCand 1755 titsK0Strong[i]!) = true :=
  ruChain_strong_inv clsK0.1 (by simpa [titsK0Strong] using hi)

theorem titsX13_mem_K0 :
    titsX13 ∈ titsK0 := by
  have := titsK0_original_mem (i := 0) (by norm_num)
  rwa [eq_of_eqA (rep_permOfArr (titsK0_strong_inv (by norm_num))).1 rep_titsX13
    clsK0.2.2.1] at this

theorem titsTInv_mem_K0 :
    titsTInv ∈ titsK0 := by
  have := titsK0_original_mem (i := 1) (by norm_num)
  rwa [eq_of_eqA (rep_permOfArr (titsK0_strong_inv (by norm_num))).1 titsTInv_rep
    clsK0.2.2.2.1] at this

theorem titsK0_le :
    titsK0 ≤ titsA := by
  rw [titsK0, titsK0Chain, RawSchreierDatum.originalSubgroup, Subgroup.closure_le]
  intro g hg
  obtain ⟨i, hi, rfl⟩ := RawSchreierDatum.mem_ofArrays_original.1 hg
  interval_cases i
  · rw [eq_of_eqA (rep_permOfArr (titsK0_strong_inv (by norm_num))).1 rep_titsX13
      clsK0.2.2.1]
    exact titsX13_mem
  · rw [eq_of_eqA (rep_permOfArr (titsK0_strong_inv (by norm_num))).1 titsTInv_rep
      clsK0.2.2.2.1]
    exact titsD_le_titsA titsTInv_mem_titsD
  · exact mem_titsA_of_inTitsA (rep_permOfArr (titsK0_strong_inv (by norm_num))).1
      clsK0.2.2.2.2

theorem classOK_spec
    {a : Array ℕ}
    {c : Equiv.Perm (Fin 1755)} (ha : Rep 1755 a c)
    (h : classOK a = true) (hc2 : c * c = 1) (hc1 : c ≠ 1) (hct : c ≠ titsTInv) :
    ∃ k < 12, ∃ i < 30, titsY12 ^ k * c * (titsY12 ^ k)⁻¹ = titsRep i := by
  simp only [classOK, Bool.or_eq_true, Bool.not_eq_true'] at h
  rcases h with (h | h) | h
  · exfalso
    simp only [isInvolA, Bool.and_eq_false_iff, Bool.not_eq_false'] at h
    rcases h with h | h
    · rw [(eqA_iff (rep_compA ha ha) rep_idA).2 hc2] at h
      exact Bool.false_ne_true h.symm
    · exact hc1 ((eqA_iff ha rep_idA).1 h)
  · exact absurd ((eqA_iff ha titsTInv_rep).1 h) hct
  · obtain ⟨k, hk, hk'⟩ := List.any_eq_true.1 h
    obtain ⟨i, hi, hi'⟩ := List.any_eq_true.1 hk'
    rw [List.mem_range] at hk hi
    have hy := rep_powArr rep_titsY12 k
    have hyi := rep_inv_of_isInvA hy (allLt_spec clsY12.2.2.2.2 hk)
    exact ⟨k, hk, i, hi, eq_of_eqA (rep_compA (rep_compA hy ha) hyi) (rep_titsRep hi) hi'⟩

theorem involution_centralizer_classified
    {c : Equiv.Perm (Fin 1755)}
    (hcA : c ∈ titsA)
    (hc : c * titsTInv = titsTInv * c) (hc2 : c * c = 1) (hc1 : c ≠ 1) (hct : c ≠ titsTInv) :
    ∃ k < 12, ∃ i < 30, titsY12 ^ k * c * (titsY12 ^ k)⁻¹ = titsRep i := by
  by_cases hcD : c ∈ titsD
  · obtain ⟨a, haL, rfl⟩ := mem_titsCNt_of_mem_D hcD hc
    have hinv := (titsCNt_facts haL).1
    have h := List.all_eq_true.1 clsClassOK a haL
    rw [Bool.and_eq_true] at h
    exact classOK_spec (rep_permOfArr hinv).1 h.1 hc2 hc1 hct
  ·
    have hAc : (⟨titsAux, titsAux_mem⟩ : titsA)⁻¹ * ⟨c, hcA⟩ ∈ titsD.subgroupOf titsA := by
      rw [Subgroup.mul_mem_iff_of_index_two titsD_index, Subgroup.mem_subgroupOf,
        Subgroup.mem_subgroupOf]
      simp only [Subgroup.coe_inv]
      constructor
      · intro h
        exact absurd (by simpa using inv_mem h) titsAux_not_mem_D
      · intro h
        exact absurd h hcD
    rw [Subgroup.mem_subgroupOf] at hAc
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hAc
    have hcomm : titsAux⁻¹ * c * titsTInv = titsTInv * (titsAux⁻¹ * c) := by
      have h1 : titsAux⁻¹ * titsTInv = titsTInv * titsAux⁻¹ :=
        (Commute.inv_left (show Commute titsAux titsTInv from titsAux_comm)).eq
      rw [mul_assoc, hc, ← mul_assoc, h1, mul_assoc]
    obtain ⟨a, haL, ha⟩ := mem_titsCNt_of_mem_D hAc hcomm
    have hinv := (titsCNt_facts haL).1
    have hrep : Rep 1755 (compA 1755 titsAuxArr a) c := by
      have := rep_compA rep_titsAux (rep_permOfArr hinv).1
      rwa [ha, ← mul_assoc, mul_inv_cancel, one_mul] at this
    have h := List.all_eq_true.1 clsClassOK a haL
    rw [Bool.and_eq_true] at h
    exact classOK_spec hrep h.2 hc2 hc1 hct

theorem titsX13_zpow_mul (m : ℤ) : titsX13 ^ (13 * m) = 1 := by
  rw [zpow_mul]
  norm_cast
  rw [titsX13_pow, one_zpow]

theorem exists_zpow_conj_eq_titsT
    {S : Equiv.Perm (Fin 1755)} (hSA : S ∈ titsA)
    (hS : S * titsX13 * S⁻¹ = titsX13⁻¹) :
    ∃ l : ℤ, titsX13 ^ l * S * (titsX13 ^ l)⁻¹ = titsTInv := by
  have hcA : S * titsTInv ∈ titsA := mul_mem hSA (titsD_le_titsA titsTInv_mem_titsD)
  have hcomm : (⟨S * titsTInv, hcA⟩ : titsA) * titsX13A = titsX13A * ⟨S * titsTInv, hcA⟩ := by
    apply Subtype.ext
    show S * titsTInv * titsX13 = titsX13 * (S * titsTInv)
    have h1 : titsTInv * titsX13 = titsX13⁻¹ * titsTInv := by
      rw [← titsT_inverts_X13, titsTInv_inv, mul_assoc, mul_assoc, titsTInv_mul_self, mul_one]
    have h2 : S * titsX13⁻¹ = titsX13 * S := by
      calc S * titsX13⁻¹ = (S * titsX13 * S⁻¹)⁻¹ * S := by group
        _ = titsX13 * S := by rw [hS, inv_inv]
    rw [mul_assoc, h1, ← mul_assoc, h2, mul_assoc]
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 (mem_zpowers_of_commute_titsX13 hcomm)
  have hm' : titsX13 ^ m = S * titsTInv := by
    have := congrArg Subtype.val hm
    simpa [titsX13A] using this
  have hSm : S = titsX13 ^ m * titsTInv := by
    rw [hm', mul_assoc, titsTInv_mul_self, mul_one]
  refine ⟨6 * m, ?_⟩
  rw [hSm]
  have key : titsTInv * (titsX13 ^ (6 * m))⁻¹ = titsX13 ^ (6 * m) * titsTInv := by
    have := titsT_conj_zpow (-(6 * m))
    rw [← zpow_neg]
    calc titsTInv * titsX13 ^ (-(6 * m)) = titsTInv * titsX13 ^ (-(6 * m)) * titsTInv⁻¹ *
          titsTInv := by group
      _ = titsX13 ^ (6 * m) * titsTInv := by rw [this, neg_neg]
  calc titsX13 ^ (6 * m) * (titsX13 ^ m * titsTInv) * (titsX13 ^ (6 * m))⁻¹ =
        titsX13 ^ (6 * m) * titsX13 ^ m * (titsTInv * (titsX13 ^ (6 * m))⁻¹) := by group
    _ = titsX13 ^ (13 * m) * titsTInv := by
      rw [key, ← mul_assoc, ← zpow_add, ← zpow_add]
      ring_nf
    _ = titsTInv := by rw [titsX13_zpow_mul, one_mul]
where
  titsT_conj_zpow (j : ℤ) : titsTInv * titsX13 ^ j * titsTInv⁻¹ = titsX13 ^ (-j) := by
    rw [conj_zpow_eq, titsT_inverts_X13, inv_zpow']

theorem titsX13_mem_zpowers {Y : Equiv.Perm (Fin 1755)}
    (hY : Y ∈ Subgroup.zpowers titsX13)
    (hY1 : Y ≠ 1) : titsX13 ∈ Subgroup.zpowers Y := by
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have hle : Subgroup.zpowers Y ≤ Subgroup.zpowers titsX13 := Subgroup.zpowers_le.2 hY
  have hcard : Nat.card (Subgroup.zpowers titsX13) = 13 := by
    rw [Nat.card_zpowers, orderOf_titsX13]
  have hcardY : Nat.card (Subgroup.zpowers Y) = 13 := by
    rw [Nat.card_zpowers]
    have hdvd : orderOf Y ∣ 13 := by
      rw [← hcard, ← Nat.card_zpowers]
      exact Subgroup.card_dvd_of_le hle
    rcases (Nat.dvd_prime (by norm_num)).1 hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hY1
    · exact h
  have := Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hcardY])
  rw [this]
  exact Subgroup.mem_zpowers _

theorem rep_badLetters
    {i : ℕ}
    (hi : i < 30) :
    ∀ h < 3, Rep 1755 (badLetters i)[h]! (badGen i h) := by
  intro h hh
  rw [badLetters_get hh]
  interval_cases h
  · simpa [badGen] using rep_titsX13
  · simpa [badGen] using titsTInv_rep
  · simpa [badGen] using rep_titsRep hi

theorem rep_badLetters_inv
    {i : ℕ}
    (hi : i < 30) :
    ∀ h < 3, Rep 1755 ((badLetters i).map (invCand 1755))[h]! (badGen i h)⁻¹ := by
  intro h hh
  have hsz : h < (badLetters i).size := by rw [badLetters_size]; exact hh
  have hsz' : h < ((badLetters i).map (invCand 1755)).size := by
    rw [Array.size_map]
    exact hsz
  rw [getElem!_pos _ h hsz', Array.getElem_map, ← getElem!_pos (badLetters i) h hsz]
  apply rep_inv_of_isInvA (rep_badLetters hi h hh)
  rw [badLetters_get hh]
  interval_cases h
  · simpa using tits13_check.1
  · simpa using clsT.1
  · simpa using allLt_spec clsReps.1 hi

end CFSG.Quasithin.RuRank3
