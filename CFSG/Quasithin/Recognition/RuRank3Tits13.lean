
module

public import CFSG.Quasithin.Recognition.RuRank3Tits13Base

public import CFSG.Quasithin.Recognition.RuRank3TitsSyl
public import CFSG.Quasithin.Recognition.RuRank3PSL
public import CFSG.Sporadic.Schreier.TitsAction
public import CFSG.Sporadic.Schreier.TitsChain
public import CFSG.Sporadic.Schreier.RuChainSpec
public import CFSG.Sporadic.Schreier.RuConj
public meta import CFSG.Quasithin.Recognition.RuRank3TitsSyl
public meta import CFSG.Quasithin.Recognition.RuRank3PSL
public meta import CFSG.Sporadic.Schreier.TitsAction
public meta import CFSG.Sporadic.Schreier.TitsChain
public meta import CFSG.Sporadic.Schreier.RuChainSpec
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
public import CFSG.Quasithin.Recognition.RuRank3Tits13Inputs
public import Certificates.Certificate7049

public section

namespace CFSG.Quasithin.RuRank3

open CFSG.Sporadic.Schreier.Tits CFSG.Sporadic.RuSchreier
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
open scoped Pointwise

theorem tits13_check :
    isInvA 1755 titsX13Arr (invCand 1755 titsX13Arr) = true ∧ inTitsA titsX13Arr = true ∧
    eqA 1755 (powArr 1755 titsX13Arr 13) (idA 1755) = true ∧
    eqA 1755 titsX13Arr (idA 1755) = false ∧ ptFixCount titsX13Arr = 0 ∧
    lineFixCount titsX13Arr = 0 ∧
    ruChainOK 1755 titsP3Gens 3 3 [0] [] = true ∧
    rawOrbitSizes 1755 titsP3Gens (ruBaseArr 1755 [0]) = [27] ∧
    ruChainOK 1755 titsP5Gens 2 2 [0] [] = true ∧
    rawOrbitSizes 1755 titsP5Gens (ruBaseArr 1755 [0]) = [25] ∧
    (allLt 3 fun k => inTitsA titsP3Gens[k]! &&
      isInvA 1755 titsP3Gens[k]! (invCand 1755 titsP3Gens[k]!)) = true ∧
    (allLt 2 fun k => inTitsA titsP5Gens[k]! &&
      isInvA 1755 titsP5Gens[k]! (invCand 1755 titsP5Gens[k]!)) = true ∧
    listClosedA 1755 titsP3Gens (closureList 1755 titsP3Gens 30) = true ∧
    listClosedA 1755 titsP5Gens (closureList 1755 titsP5Gens 30) = true ∧
    ((closureList 1755 titsP3Gens 30).all fun e =>
      eqA 1755 e (idA 1755) || lineFixCount e == 9) = true ∧
    ((closureList 1755 titsP5Gens 30).all fun e =>
      eqA 1755 e (idA 1755) || ptFixCount e == 5) = true ∧
    lineFixCount titsZArr = 45 ∧ lineFixCount titsTArr = 61 :=
  Certificates.certificate7049

theorem rep_titsX13 :
    Rep 1755 titsX13Arr titsX13 := (rep_permOfArr tits13_check.1).1

theorem titsX13_mem :
    titsX13 ∈ titsA := mem_titsA_of_inTitsA rep_titsX13 tits13_check.2.1

theorem titsX13_pow : titsX13 ^ 13 = 1 :=
  eq_of_eqA (rep_powArr rep_titsX13 13) rep_idA tits13_check.2.2.1

theorem titsX13_ne_one : titsX13 ≠ 1 := by
  intro h
  have := tits13_check.2.2.2.1
  rw [(eqA_iff rep_titsX13 rep_idA).2 h] at this
  exact Bool.false_ne_true this.symm

theorem orderOf_titsX13 : orderOf titsX13 = 13 := by
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  exact orderOf_eq_prime titsX13_pow titsX13_ne_one

theorem titsX13_apply_ne (x : Fin 1755) : titsX13 x ≠ x := by
  intro h
  have hc := card_fixedPoints rep_titsX13
  rw [tits13_check.2.2.2.2.1] at hc
  have : 0 < Fintype.card {y // titsX13 y = y} := Fintype.card_pos_iff.2 ⟨⟨x, h⟩⟩
  omega

@[expose] noncomputable def titsX13A :
    titsA := ⟨titsX13, titsX13_mem⟩

theorem titsX13_lineHom_ne
    (v : Fin 2925) :
    titsLineHom titsX13A v ≠ v := by
  intro h
  have hc := card_fixedLines (g := titsX13A) rep_titsX13
  rw [tits13_check.2.2.2.2.2.1] at hc
  have : 0 < Fintype.card {w // titsLineHom titsX13A w = w} := Fintype.card_pos_iff.2 ⟨⟨v, h⟩⟩
  omega

theorem card_titsP3 : Nat.card titsP3 = 27 := by
  have h := ruChain_card (n := 1755) (hn := by norm_num) (hpos := by norm_num) (k := 3) (s := 3)
    (hk := by simp [titsP3Gens]) (b := [0]) (hb := by decide) tits13_check.2.2.2.2.2.2.1
  rw [tits13_check.2.2.2.2.2.2.2.1] at h
  rw [← titsP3_eq]
  exact h

theorem card_titsP5 : Nat.card titsP5 = 25 := by
  have h := ruChain_card (n := 1755) (hn := by norm_num) (hpos := by norm_num) (k := 2) (s := 2)
    (hk := by simp [titsP5Gens]) (b := [0]) (hb := by decide) tits13_check.2.2.2.2.2.2.2.2.1
  rw [tits13_check.2.2.2.2.2.2.2.2.2.1] at h
  rw [← titsP5_eq]
  exact h

theorem titsP3Gens_facts :
    ∀ k < titsP3Gens.size, inTitsA titsP3Gens[k]! = true ∧
    isInvA 1755 titsP3Gens[k]! (invCand 1755 titsP3Gens[k]!) = true := by
  intro k hk
  rw [titsP3Gens_size] at hk
  have := allLt_spec tits13_check.2.2.2.2.2.2.2.2.2.2.1 hk
  simpa only [Bool.and_eq_true] using this

theorem titsP5Gens_facts :
    ∀ k < titsP5Gens.size, inTitsA titsP5Gens[k]! = true ∧
    isInvA 1755 titsP5Gens[k]! (invCand 1755 titsP5Gens[k]!) = true := by
  intro k hk
  rw [titsP5Gens_size] at hk
  have := allLt_spec tits13_check.2.2.2.2.2.2.2.2.2.2.2.1 hk
  simpa only [Bool.and_eq_true] using this

theorem titsP3_le :
    titsP3 ≤ titsA := genSubgroup_le fun k hk =>
  mem_titsA_of_inTitsA (rep_permOfArr (titsP3Gens_facts k hk).2).1 (titsP3Gens_facts k hk).1

theorem titsP5_le :
    titsP5 ≤ titsA := genSubgroup_le fun k hk =>
  mem_titsA_of_inTitsA (rep_permOfArr (titsP5Gens_facts k hk).2).1 (titsP5Gens_facts k hk).1

theorem titsP3_lines {g : Equiv.Perm (Fin 1755)} (hg : g ∈ titsP3)
    (hg1 : g ≠ 1) :
    ∃ a : Array ℕ, Rep 1755 a g ∧ lineFixCount a = 9 := by
  obtain ⟨i, hi, hrep⟩ := mem_list_of_mem_genSubgroup (fun k _ => (rep_permOfArr
    (titsP3Gens_facts k ‹_›).2).1) (fun k hk => (titsP3Gens_facts k hk).2)
    tits13_check.2.2.2.2.2.2.2.2.2.2.2.2.1 g hg
  refine ⟨_, hrep, ?_⟩
  have := Array.all_eq_true.1 tits13_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 i hi
  rw [← getElem!_pos _ i hi] at this
  simp only [Bool.or_eq_true, beq_iff_eq] at this
  rcases this with h1 | h9
  · exact absurd ((eqA_iff hrep rep_idA).1 h1) hg1
  · exact h9

theorem titsP5_points {g : Equiv.Perm (Fin 1755)} (hg : g ∈ titsP5)
    (hg1 : g ≠ 1) :
    ∃ a : Array ℕ, Rep 1755 a g ∧ ptFixCount a = 5 := by
  obtain ⟨i, hi, hrep⟩ := mem_list_of_mem_genSubgroup (fun k _ => (rep_permOfArr
    (titsP5Gens_facts k ‹_›).2).1) (fun k hk => (titsP5Gens_facts k hk).2)
    tits13_check.2.2.2.2.2.2.2.2.2.2.2.2.2.1 g hg
  refine ⟨_, hrep, ?_⟩
  have := Array.all_eq_true.1 tits13_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 i hi
  rw [← getElem!_pos _ i hi] at this
  simp only [Bool.or_eq_true, beq_iff_eq] at this
  rcases this with h1 | h5
  · exact absurd ((eqA_iff hrep rep_idA).1 h1) hg1
  · exact h5

theorem exists_sylow_titsP3 :
    ∃ Q : Sylow 3 titsA, (Q : Subgroup titsA) = titsP3.subgroupOf titsA := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  apply exists_sylow_eq_of_card (e := 3)
  · rw [card_subgroupOf_eq titsP3_le, card_titsP3]
    norm_num
  · norm_num

theorem exists_sylow_titsP5 :
    ∃ Q : Sylow 5 titsA, (Q : Subgroup titsA) = titsP5.subgroupOf titsA := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  apply exists_sylow_eq_of_card (e := 2)
  · rw [card_subgroupOf_eq titsP5_le, card_titsP5]
    norm_num
  · norm_num

theorem not_commute_titsX13
    {y : titsA} {r : ℕ}
    (hr : r = 2 ∨ r = 3 ∨ r = 5)
    (hy : orderOf y = r) (hcomm : titsX13A * y = y * titsX13A) : False := by
  have h13 : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have hlines : 13 ∣ Fintype.card {v // titsLineHom y v = v} := by
    apply prime_dvd_card_fixedPoints_of_commute (σ := titsLineHom titsX13A)
    · rw [← map_pow]
      have : titsX13A ^ 13 = 1 := Subtype.ext titsX13_pow
      rw [this, map_one]
    · exact titsX13_lineHom_ne
    · rw [← map_mul, ← map_mul, hcomm]
  have hpts : 13 ∣ Fintype.card {x // (y : Equiv.Perm (Fin 1755)) x = x} := by
    apply prime_dvd_card_fixedPoints_of_commute (σ := titsX13)
    · exact titsX13_pow
    · exact titsX13_apply_ne
    · exact congrArg Subtype.val hcomm
  rcases hr with rfl | rfl | rfl
  ·
    have hyD : (y : Equiv.Perm (Fin 1755)) ∈ titsD := titsA_involution_mem_D y.2 (by
      rw [Subgroup.orderOf_coe]; exact hy)
    have hyP : orderOf (y : Equiv.Perm (Fin 1755)) = 2 := by
      rw [Subgroup.orderOf_coe]
      exact hy
    have hyD2 : orderOf (⟨y, hyD⟩ : titsD) = 2 := by
      rw [← Subgroup.orderOf_coe]
      exact hyP
    rcases titsD_involution_conj ⟨y, hyD⟩ hyD2 with h | h
    · obtain ⟨c, hc⟩ := isConj_iff.1 h
      let c' : titsA := ⟨c, titsD_le_titsA c.2⟩
      have hyc : y = c' * ⟨titsZ, titsD_le_titsA titsZ_mem_titsD⟩ * c'⁻¹ := by
        apply Subtype.ext
        have := congrArg Subtype.val hc
        simpa [c', titsZD] using this.symm
      rw [hyc, card_fixedLines_conj, card_fixedLines (a := titsZArr) titsZ_rep] at hlines
      rw [tits13_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1] at hlines
      norm_num at hlines
    · obtain ⟨c, hc⟩ := isConj_iff.1 h
      let c' : titsA := ⟨c, titsD_le_titsA c.2⟩
      have hyc : y = c' * ⟨titsTInv, titsD_le_titsA titsTInv_mem_titsD⟩ * c'⁻¹ := by
        apply Subtype.ext
        have := congrArg Subtype.val hc
        simpa [c', titsTD] using this.symm
      rw [hyc, card_fixedLines_conj, card_fixedLines (a := titsTArr) titsTInv_rep] at hlines
      rw [tits13_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2] at hlines
      norm_num at hlines
  ·
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨Q, hQ⟩ := exists_sylow_titsP3
    obtain ⟨c, hc⟩ := exists_conj_mem_sylow Q (IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, hy, pow_one]))
    rw [hQ, Subgroup.mem_subgroupOf] at hc
    have hne : ((c * y * c⁻¹ : titsA) : Equiv.Perm (Fin 1755)) ≠ 1 := by
      intro h1
      have : c * y * c⁻¹ = 1 := Subtype.ext h1
      have : y = 1 := by
        have := congrArg (fun w => c⁻¹ * w * c) this
        simpa [mul_assoc] using this
      rw [this, orderOf_one] at hy
      norm_num at hy
    obtain ⟨a, ha, h9⟩ := titsP3_lines hc hne
    rw [← card_fixedLines_conj c y, card_fixedLines ha, h9] at hlines
    norm_num at hlines
  ·
    have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    obtain ⟨Q, hQ⟩ := exists_sylow_titsP5
    obtain ⟨c, hc⟩ := exists_conj_mem_sylow Q (IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, hy, pow_one]))
    rw [hQ, Subgroup.mem_subgroupOf] at hc
    have hne : ((c * y * c⁻¹ : titsA) : Equiv.Perm (Fin 1755)) ≠ 1 := by
      intro h1
      have : c * y * c⁻¹ = 1 := Subtype.ext h1
      have : y = 1 := by
        have := congrArg (fun w => c⁻¹ * w * c) this
        simpa [mul_assoc] using this
      rw [this, orderOf_one] at hy
      norm_num at hy
    obtain ⟨a, ha, h5⟩ := titsP5_points hc hne
    have hconj : Fintype.card {x // ((c * y * c⁻¹ : titsA) : Equiv.Perm (Fin 1755)) x = x} =
        Fintype.card {x // (y : Equiv.Perm (Fin 1755)) x = x} := by
      apply Fintype.card_congr
      refine Equiv.subtypeEquiv ((c : Equiv.Perm (Fin 1755))⁻¹) fun x => ?_
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.mul_apply]
      constructor
      · intro h
        have := congrArg ((c : Equiv.Perm (Fin 1755))⁻¹ : Equiv.Perm (Fin 1755)) h
        simpa using this
      · intro h
        rw [h]
        simp
    rw [← hconj, card_fixedPoints ha, h5] at hpts
    norm_num at hpts

theorem mem_zpowers_of_commute_titsX13
    {c : titsA}
    (hc : c * titsX13A = titsX13A * c) :
    c ∈ Subgroup.zpowers titsX13A := by
  have h13 : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  set C := Subgroup.centralizer ({titsX13A} : Set titsA)
  set Z := Subgroup.zpowers titsX13A
  have hZC : Z ≤ C := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
  have hcC : c ∈ C := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hc
  have hZ : Nat.card Z = 13 := by
    rw [Nat.card_zpowers]
    rw [← orderOf_titsX13]
    exact (Subgroup.orderOf_coe titsX13A).symm
  by_contra hcZ
  obtain ⟨k, hk⟩ : 13 ∣ Nat.card C := by
    rw [← hZ]
    exact Subgroup.card_dvd_of_le hZC
  have hk2 : k ≠ 1 := by
    intro hk1
    rw [hk1, mul_one, ← hZ] at hk
    exact hcZ ((Subgroup.eq_of_le_of_card_ge hZC hk.le) ▸ hcC)
  have hk0 : k ≠ 0 := by
    intro hk0
    rw [hk0, mul_zero] at hk
    exact Nat.card_pos.ne' hk
  set r := k.minFac with hr
  have hrp : r.Prime := Nat.minFac_prime hk2
  have hrk : r ∣ k := Nat.minFac_dvd k
  have hrC : 13 * r ∣ 35942400 := by
    rw [← card_titsA]
    exact (Nat.mul_dvd_mul_left 13 hrk).trans (hk ▸ Subgroup.card_subgroup_dvd_card C)
  have hr235 : r = 2 ∨ r = 3 ∨ r = 5 := by
    have hrd : r ∣ 2 ^ 12 * 3 ^ 3 * 5 ^ 2 * 13 := by
      have := (Nat.dvd_mul_left r 13).trans hrC
      norm_num at this ⊢
      exact this
    rcases (Nat.Prime.dvd_mul hrp).1 hrd with h | h
    · rcases (Nat.Prime.dvd_mul hrp).1 h with h | h
      · rcases (Nat.Prime.dvd_mul hrp).1 h with h | h
        · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hrp Nat.prime_two).1
            (hrp.dvd_of_dvd_pow h))
        · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hrp Nat.prime_three).1
            (hrp.dvd_of_dvd_pow h)))
      · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hrp Nat.prime_five).1
          (hrp.dvd_of_dvd_pow h)))
    · have h13r : r = 13 := (Nat.prime_dvd_prime_iff_eq hrp (by norm_num)).1 h
      rw [h13r] at hrC
      norm_num at hrC
  have : Fact r.Prime := ⟨hrp⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := C) r (by
    rw [hk]
    exact Dvd.dvd.mul_left hrk 13)
  have hyc : titsX13A * (y : titsA) = (y : titsA) * titsX13A := by
    have := Subgroup.mem_centralizer_singleton_iff.1 y.2
    exact this.symm
  exact not_commute_titsX13 hr235 (by rw [Subgroup.orderOf_coe]; exact hy) hyc

end CFSG.Quasithin.RuRank3
