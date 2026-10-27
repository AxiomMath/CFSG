module

public import Certificates.Kernel.Misc.RuSyl8038.Checks
public import Certificates.Kernel.RuThree.Facts
public import CFSG.Certificates.Kernel.Misc.RuSyl8038Sound

public section

namespace CertificateChecks.Batch8038

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.Raw.Orb CFSG.KC.RuSyl8038 CFSG.KC.J2H
  CertificateChecks.KernelRuThree CertificateChecks.KernelMisc.RuSyl8038 CFSG.Sporadic.RuSchreier
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.EvenSporadicStandard.RuStd.S2
open scoped commutatorElement

noncomputable abbrev gw (wd : List Int) : Equiv.Perm (Fin 4060) :=
  sgnProd (fun h => permOfArr 4060 ruThreeArrs[h]!) wd

theorem wq {wd : List Int} (hl : lettersK 11 wd = true) :
    wordEqK 4060 12 (mask 12) (pidn 4060 12) S3R.S S3R.SI 11 wd (wv wd) = true := by
  have e : Nat.beq (wordK 4060 12 (mask 12) (pidn 4060 12) S3R.S S3R.SI wd) (wv wd) = true :=
    Nat.beq_refl _
  unfold wordEqK
  rw [sz, hl, e]

theorem prep_w {wd : List Int} (hl : lettersK 11 wd = true) : PRep 4060 12 (wv wd) (gw wd) :=
  prep_of_rep (word_rep binds kPerm (wq hl))

theorem gens2 : ∀ i < 2, permOfArr 4060 ruThreeArrs[i]! ∈ ruP := by
  intro i hi
  interval_cases i
  · rw [arr0]
    exact ruA0_mem
  · rw [arr1]
    exact ruA1_mem

theorem memU : gw uW ∈ ruP := sgnProd_mem (m := 2) gens2 uW (by decide +kernel)

theorem memH : gw hW ∈ ruP := sgnProd_mem (m := 2) gens2 hW (by decide +kernel)

theorem memHI : gw hWI ∈ ruP := sgnProd_mem (m := 2) gens2 hWI (by decide +kernel)

theorem memW : gw wW ∈ ruP := sgnProd_mem (m := 2) gens2 wW (by decide +kernel)

theorem lU : lettersK 11 uW = true := by decide +kernel

theorem lH : lettersK 11 hW = true := by decide +kernel

theorem lHI : lettersK 11 hWI = true := by decide +kernel

theorem lW : lettersK 11 wW = true := by decide +kernel

theorem core : core8038 (wv uW) (wv hW) (wv hWI) (wv wW) = true := by
  have h := ok8038
  unfold run8038 at h
  simp only [sB] at h
  exact h

theorem seven_dvd_one : 7 ∣ {p : Fin 4060 | (1 : Equiv.Perm (Fin 4060)) p = p}.ncard := by
  have e : {p : Fin 4060 | (1 : Equiv.Perm (Fin 4060)) p = p} = Set.univ := by
    ext p
    simp
  rw [e, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
  norm_num

end CertificateChecks.Batch8038

namespace Certificates

open CertificateChecks.Batch8038 CFSG.KC.RuSyl8038 CertificateChecks.KernelMisc.RuSyl8038
  CFSG.Sporadic.RuSchreier
open scoped commutatorElement

open CFSG.Sporadic.RuSchreier in
theorem certificate8038 :
    (∃ S : Subgroup (Equiv.Perm (Fin 4060)), S ≤ ruP ∧ Nat.card S = 27 ∧
      ∀ g ∈ S, g ≠ 1 → ¬ 7 ∣ {p : Fin 4060 | g p = p}.ncard) ∧
    (∃ w ∈ ruP, orderOf w = 7 ∧ ∀ p : Fin 4060, w p ≠ p) := by
  obtain ⟨hx3, hy3, hzx, hzy, hnf, hw7, hwfix⟩ :=
    core8038_sound (prep_w lU) (prep_w lH) (prep_w lHI) (prep_w lW) core
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  refine ⟨⟨Subgroup.closure {gw uW ^ 4, gw hW * gw uW ^ 4 * gw hWI}, ?_, ?_, ?_⟩, gw wW, memW,
    orderOf_eq_prime hw7 fun h1 => hwfix 0 (by simp [h1]), hwfix⟩
  · rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact ruP.pow_mem memU 4
    · exact ruP.mul_mem (ruP.mul_mem memH (ruP.pow_mem memU 4)) memHI
  · refine card_closure_eq_27 hx3 hy3 hzx hzy fun i j k hi hj hk he => ?_
    by_contra hne
    have h := hnf i j k hi hj hk fun hi0 hj0 hk0 => hne ⟨hi0, hj0, hk0⟩
    rw [he] at h
    exact h seven_dvd_one
  · intro g hg hg1
    obtain ⟨i, j, k, hi, hj, hk, rfl⟩ := CFSG.SectionRank.LocalWitness.mem_closure_normalForm
      (by norm_num) hx3 hy3 hzx hzy hg
    refine hnf i j k hi hj hk fun hi0 hj0 hk0 => hg1 ?_
    rw [hi0, hj0, hk0]
    simp

end Certificates
