module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20d
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma44bOrd
public import CFSG.Adapters.LieModelSimple

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Assembly.LowTwoRank CFSG.Quasithin
open CFSG.LocalAnalysis.UniquenessCase.UC22 (uc22p20d_outSolvable_of_isSolvable_outer)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  (linear_two_classical_model_schreier linear_higher_classical_model_schreier
    unitary_classical_model_schreier)
open CFSG.Blueprint (LieModel)

theorem exists_noncomm_of_simple_of_pow_three_dvd {X : Type} [Group X] [IsSimpleGroup X]
    {p g : ℕ} (hp : p.Prime) (hg : g = 1 ∨ g = 3) (hdvd : p ^ 3 ∣ Nat.card X * g) :
    ∃ a b : X, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  letI : CommGroup X := { ‹Group X› with mul_comm := fun a b => hcon a b }
  have hℓ : (Nat.card X).Prime := IsSimpleGroup.prime_card
  have hp2 := hp.two_le
  have hp3 : p ∣ p ^ 3 := dvd_pow_self p (by norm_num)
  have hpow : p ^ 3 = p * p ^ 2 := by ring
  rcases hg with rfl | rfl
  · rw [mul_one] at hdvd
    have hpℓ : p = Nat.card X := (Nat.prime_dvd_prime_iff_eq hp hℓ).1 (hp3.trans hdvd)
    rw [← hpℓ] at hdvd
    have := Nat.le_of_dvd hp.pos hdvd
    nlinarith
  · have hpm : p ∣ Nat.card X * 3 := hp3.trans hdvd
    rcases (Nat.Prime.dvd_mul hp).1 hpm with h | h
    · have hpℓ : p = Nat.card X := (Nat.prime_dvd_prime_iff_eq hp hℓ).1 h
      rw [← hpℓ, hpow] at hdvd
      have h2 : p ^ 2 ∣ 3 := Nat.dvd_of_mul_dvd_mul_left hp.pos hdvd
      have := Nat.le_of_dvd (by norm_num) h2
      nlinarith
    · have hp3' : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h
      subst hp3'
      have h27 : 9 ∣ Nat.card X := by
        have : 3 * 9 ∣ 3 * Nat.card X := by
          have h' : (3 : ℕ) ^ 3 ∣ 3 * Nat.card X := by
            rw [mul_comm] at hdvd
            exact hdvd
          simpa using h'
        exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
      have h3 : 3 ∣ Nat.card X := (dvd_trans (by norm_num) h27)
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hℓ).1 h3
      rw [← this] at h27
      omega

theorem asch5_simpOutSolv_holds : Asch5_SimpOutSolv := by
  intro X _ _ h
  rcases h with ⟨p, e, hp, hp2, h3, hL⟩ | ⟨p, f, hp, hp2, hX | hX⟩
  ·
    have hm : StatedClassicalModel X .PSL 2 p e := hL
    refine ⟨CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel hm, ?_,
      uc22p20d_outSolvable_of_isSolvable_outer (linear_two_classical_model_schreier hm).2⟩
    obtain ⟨-, F, _, _, hF, ⟨eF⟩⟩ := hm
    obtain ⟨x, y, hxy⟩ :=
      CFSG.ComponentClassification.CatalogueBSmallRee.projectiveSpecialLinear_two_nonabelian
        F (by rw [hF]; omega) (by rw [hF]; omega)
    let e' := eF.trans (projectiveSpecialLinearGroupEquivStatedProj 2 F).symm
    exact ⟨e'.symm x, e'.symm y, fun hc => hxy (by simpa using congrArg e' hc)⟩
  ·
    have hm : StatedClassicalModel X .PSL 3 p f := hX.statedClassicalModel (by decide)
    have hs := CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel hm
    refine ⟨hs, ?_, uc22p20d_outSolvable_of_isSolvable_outer
      (linear_higher_classical_model_schreier (by norm_num) hm).2⟩
    obtain ⟨⟨-, hf, -⟩, F, _, _, hF, ⟨eF⟩⟩ := hm
    have hcard : Nat.card X = Nat.card (StatedProj (StatedSL 3 F)) := Nat.card_congr eF.toEquiv
    have hord := CFSG.GH74.GLS.IVK.Proofs2.Lemma44bOrd.card_statedProj_statedSL_three_mul (F := F)
    refine exists_noncomm_of_simple_of_pow_three_dvd (X := X) hp
      (g := Nat.gcd 3 (Nat.card F - 1))
      ((Nat.dvd_prime Nat.prime_three).1 (Nat.gcd_dvd_left 3 _)) ?_
    rw [hcard, hord, hF]
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_right
      (pow_dvd_pow_of_dvd (dvd_pow_self p (by omega)) 3) _) _
  ·
    have hm : StatedClassicalModel X .PSU 3 p f := hX.statedClassicalModel (by decide)
    have hs := CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel hm
    refine ⟨hs, ?_, uc22p20d_outSolvable_of_isSolvable_outer
      (unitary_classical_model_schreier hm).2⟩
    obtain ⟨⟨hp', hf, -⟩, F, _, _, hF, ⟨eF⟩⟩ := hm
    have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f F :=
      ⟨hp', hf, by rw [hF, ← pow_mul, mul_comm]⟩
    have hcard : Nat.card X = Nat.card (StatedProj (StatedSU 3 (p ^ f) F)) :=
      Nat.card_congr eF.toEquiv
    have hord := CFSG.GH74.GLS.IVK.Proofs2.Lemma44bOrd.card_statedProj_statedSU_three_mul hU
    refine exists_noncomm_of_simple_of_pow_three_dvd (X := X) hp
      (g := Nat.gcd 3 (p ^ f + 1))
      ((Nat.dvd_prime Nat.prime_three).1 (Nat.gcd_dvd_left 3 _)) ?_
    rw [hcard, hord]
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_right
      (pow_dvd_pow_of_dvd (dvd_pow_self p (by omega)) 3) _) _

end CFSG.LocalAnalysis.WeakClosure81
