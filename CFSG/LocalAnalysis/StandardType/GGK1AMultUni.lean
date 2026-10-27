module

public import CFSG.LocalAnalysis.StandardType.GGK1ADefs
public import CFSG.LocalAnalysis.StandardType.GGK1AGlEnd
public import CFSG.Assembly.GL83StatedBridge
public import CFSG.RankThree.PartOne.KC.UnitaryPrimaryAlgebra
public import CFSG.RankThree.PartOne.KC.UnitaryRigidityBlock
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeModel
public import CFSG.RankThree.Classical.SteinbergBJSymplecticCrossPrimeBlocks
public import CFSG.RankThree.PartOne.KC.UnitaryGoodSetting

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open Polynomial
open CFSG.RankThree.PartOne.KCPrimary
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne
open CFSG.RankThree.PartOne.KCUnitary
open CFSG.RankThree.PartOne.KCUnitaryModel
open CFSG.RankThree.PartOne.KCUnitaryBlock

private lemma bar_eq_self_of_dvd {p nf : ℕ} {K : Type} [Field K]
    (hU : UnitaryFieldData 2 nf K) (hdvd : p ∣ 2 ^ nf - 1) {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) : hU.bar ζ = ζ := by
  obtain ⟨k, hk⟩ := hdvd
  have hpos : 0 < 2 ^ nf := pow_pos (by norm_num) _
  have hq : 2 ^ nf = p * k + 1 := by omega
  rw [hU.bar_apply, hq, pow_add, pow_mul, hζ.pow_eq_one]
  simp

private lemma dualPoly_X_sub_C_pow {p nf : ℕ} {K : Type} [Field K]
    (hU : UnitaryFieldData 2 nf K) (hp : p.Prime) (hdvd : p ∣ 2 ^ nf - 1)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) {j : ℕ} (hj : j < p) :
    dualPoly hU.bar (X - C (ζ ^ j) : K[X]) = X - C (ζ ^ ((p - j) % p)) := by
  have hbar : hU.bar (ζ ^ j) = ζ ^ j := by
    rw [map_pow, bar_eq_self_of_dvd hU hdvd hζ]
  have hne : hU.bar (ζ ^ j) ≠ 0 := by
    rw [hbar]
    exact pow_ne_zero j (hζ.ne_zero hp.ne_zero)
  have hinv : (ζ ^ j)⁻¹ = ζ ^ ((p - j) % p) := by
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simp
    · have hmod : (p - j) % p = p - j := Nat.mod_eq_of_lt (by omega)
      rw [hmod]
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← pow_add, Nat.add_sub_cancel' (le_of_lt hj), hζ.pow_eq_one]
  rw [dualPoly_X_sub_C hne, hbar, hinv]

private lemma primaryMultiplicity_eq_zero_of_not_mem {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {x : Module.End K V} {a : K[X]}
    (hirr : Irreducible a) (hmon : a.Monic) (ha : a ∉ primaryFactors x) :
    primaryMultiplicity x a = 0 := by
  have hbot := CFSG.RankThree.Classical.primaryComponent_eq_bot_of_not_mem hirr hmon ha
  have : Fact (Irreducible a) := ⟨hirr⟩
  have : Subsingleton ↥(primaryComponent x a) := by rw [hbot]; infer_instance
  exact Module.finrank_zero_of_subsingleton

private lemma unitaryPrimaryData_of_mem {nf N : ℕ} {K : Type} [Field K]
    (hU : UnitaryFieldData 2 nf K)
    {xhat : ↥(LargeEvenSUGroup (Fin N) K (2 ^ nf))}
    (hsq : Squarefree (minpoly K (ggK1A_glEnd (xhat : GL (Fin N) K)))) :
    UnitaryPrimaryData hU.bar (idForm hU N)
      (Matrix.GeneralLinearGroup.toLin (xhat : GL (Fin N) K)) := by
  have hxmem : (xhat : GL (Fin N) K) ∈ LargeEvenSUGroup (Fin N) K (2 ^ nf) := xhat.2
  have hxSU : (xhat : GL (Fin N) K) ∈ unitarySU 2 nf K N := by
    rw [show unitarySU 2 nf K N = StatedSU N (2 ^ nf) K from rfl,
      ← largeEvenSUGroup_eq_statedSU N (2 ^ nf)]
    exact hxmem
  have hxgram : (xhat : GL (Fin N) K) ∈ gramSU hU (1 : Matrix (Fin N) (Fin N) K) := by
    rw [← unitarySU_eq_gramSU hU N]
    exact hxSU
  have hxPU : (xhat : GL (Fin N) K) ∈ primeFormUnitary hU (idGram K N) := by
    have h := (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.mem_gramSU_iff_unitary
      (h := hU) (C := idGram K N) (g := (xhat : GL (Fin N) K))).mp
      (by simpa [idGram] using hxgram)
    exact h.1
  have hxH : ((Matrix.GeneralLinearGroup.toLin (xhat : GL (Fin N) K) :
      Module.End K (Fin N → K))) = ggK1A_glEnd (xhat : GL (Fin N) K) :=
    (ggK1A_glEnd_eq_toLin (xhat : GL (Fin N) K)).symm
  have hxisom : Matrix.GeneralLinearGroup.toLin (xhat : GL (Fin N) K) ∈
      sesqUnitaryGroup (idForm hU N) :=
    (toLin_mem_sesqUnitaryGroup_iff (h := hU) (g := (xhat : GL (Fin N) K))).mpr hxPU
  exact ⟨hU.bar_bar, idForm_isSymm hU N, idForm_separatingLeft hU N, hxisom, by
    rw [hxH]
    exact hsq⟩

private lemma primaryMultiplicity_dualPoly_X_sub_C {nf N : ℕ} {K : Type} [Field K]
    {hU : UnitaryFieldData 2 nf K} {p : ℕ}
    {xH : LinearMap.GeneralLinearGroup K (Fin N → K)}
    (H : UnitaryPrimaryData hU.bar (idForm hU N) xH)
    {ζ : K} {j : ℕ}
    (hdual : dualPoly hU.bar (X - C (ζ ^ j) : K[X]) = X - C (ζ ^ ((p - j) % p)))
    (h0 : (X - C (ζ ^ j) : K[X]).coeff 0 ≠ 0) :
    primaryMultiplicity (xH : Module.End K (Fin N → K)) (X - C (ζ ^ ((p - j) % p))) =
      primaryMultiplicity (xH : Module.End K (Fin N → K)) (X - C (ζ ^ j)) := by
  classical
  by_cases hmem : (X - C (ζ ^ j) : K[X]) ∈
      primaryFactors (xH : Module.End K (Fin N → K))
  · have hpd := primaryMultiplicity_dualPoly H hmem
    rw [hdual] at hpd
    exact hpd
  · have hbnot : (X - C (ζ ^ ((p - j) % p)) : K[X]) ∉
        primaryFactors (xH : Module.End K (Fin N → K)) := by
      intro hb
      have hba : dualPoly hU.bar (X - C (ζ ^ ((p - j) % p)) : K[X]) =
          X - C (ζ ^ j) := by
        rw [← hdual]
        exact dualPoly_dualPoly H.invol (monic_X_sub_C _) h0
      exact hmem (hba ▸ dualPoly_mem_primaryFactors H hb)
    have hzerob : primaryMultiplicity (xH : Module.End K (Fin N → K))
        (X - C (ζ ^ ((p - j) % p))) = 0 :=
      primaryMultiplicity_eq_zero_of_not_mem (irreducible_X_sub_C _) (monic_X_sub_C _) hbnot
    have hzeroj : primaryMultiplicity (xH : Module.End K (Fin N → K))
        (X - C (ζ ^ j)) = 0 :=
      primaryMultiplicity_eq_zero_of_not_mem (irreducible_X_sub_C _) (monic_X_sub_C _) hmem
    rw [hzerob, hzeroj]

theorem ggK1A_uni_primaryMultiplicity_symm {p nf N : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hK : Nat.card K = (2 ^ nf) ^ 2) (hdvd : p ∣ 2 ^ nf - 1)
    {xhat : ↥(LargeEvenSUGroup (Fin N) K (2 ^ nf))}
    (hx : ggK1A_glEnd (xhat : GL (Fin N) K) ^ p = 1)
    (hsq : Squarefree (minpoly K (ggK1A_glEnd (xhat : GL (Fin N) K))))
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) {j : ℕ} (hj : j < p) :
    primaryMultiplicity (ggK1A_glEnd (xhat : GL (Fin N) K)) (X - C (ζ ^ ((p - j) % p))) =
      primaryMultiplicity (ggK1A_glEnd (xhat : GL (Fin N) K)) (X - C (ζ ^ j)) := by
  classical
  have hnf : 1 ≤ nf := by
    rcases Nat.eq_zero_or_pos nf with h0 | h
    · subst h0
      have h1 : Nat.card K = 1 := by simpa using hK
      have h2 : 1 < Nat.card K := Finite.one_lt_card
      omega
    · exact h
  have hU : UnitaryFieldData 2 nf K :=
    ⟨Nat.prime_two, hnf, by rw [hK, ← pow_mul, mul_comm]⟩
  let xH : LinearMap.GeneralLinearGroup K (Fin N → K) :=
    Matrix.GeneralLinearGroup.toLin (xhat : GL (Fin N) K)
  have H : UnitaryPrimaryData hU.bar (idForm hU N) xH :=
    unitaryPrimaryData_of_mem hU hsq
  have hxH : (xH : Module.End K (Fin N → K)) = ggK1A_glEnd (xhat : GL (Fin N) K) :=
    (ggK1A_glEnd_eq_toLin (xhat : GL (Fin N) K)).symm
  have hdual : dualPoly hU.bar (X - C (ζ ^ j) : K[X]) = X - C (ζ ^ ((p - j) % p)) :=
    dualPoly_X_sub_C_pow hU hp hdvd hζ hj
  have h0 : (X - C (ζ ^ j) : K[X]).coeff 0 ≠ 0 := by
    rw [coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub]
    exact neg_ne_zero.mpr (pow_ne_zero j (hζ.ne_zero hp.ne_zero))
  have hmain := primaryMultiplicity_dualPoly_X_sub_C H hdual h0
  rw [hxH] at hmain
  exact hmain

end CFSG.StandardType

end
