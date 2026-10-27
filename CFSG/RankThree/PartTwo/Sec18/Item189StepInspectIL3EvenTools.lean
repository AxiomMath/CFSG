module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabHub
public import CFSG.Open.PGLModelDefs
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSL

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.AGLEmbedding.ParabHub
open CFSG.PGLModel (projSL)

section Borel

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

theorem pow_mem_posUnipotent189
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) {M : ℕ} (hM : ∀ i, ∀ g ∈ H i, g ^ M = 1) {b : K}
    (hb : b ∈ borel D H) : b ^ M ∈ posUnipotent D := by
  have hT := CFSG.ClassicalInvolution.WeakCT.torus_le_normalizer_posUnipotent hct
  have hb' : b ∈ posUnipotent D ⊔ ⨆ i, H i := by
    rwa [CFSG.LieType.Steinberg.borel, sup_comm] at hb
  obtain ⟨u, hu, t, ht, rfl⟩ :=
    (CFSG.ClassicalInvolution.ModelFacts.OddCover.mem_sup_iff_of_normalizes
      (Q := posUnipotent D) (A := ⨆ i, H i)
      fun a ha q hq => (Subgroup.mem_normalizer_iff.1 (hT ha) q).1 hq).1 hb'
  have hpow : ∀ j : ℕ, ∃ u' ∈ posUnipotent D, (u * t) ^ j = u' * t ^ j := by
    intro j
    induction j with
    | zero => exact ⟨1, Subgroup.one_mem _, by simp⟩
    | succ j ih =>
      obtain ⟨u', hu', h⟩ := ih
      have hc : t ^ j * u * (t ^ j)⁻¹ ∈ posUnipotent D :=
        (Subgroup.mem_normalizer_iff.1 (hT (Subgroup.pow_mem _ ht j)) u).1 hu
      refine ⟨u' * (t ^ j * u * (t ^ j)⁻¹), Subgroup.mul_mem _ hu' hc, ?_⟩
      rw [pow_succ, h]
      group
  obtain ⟨u', hu', h⟩ := hpow M
  rw [h, CFSG.ClassicalInvolution.WeakCT.pow_eq_one_of_mem_torus hext hM ht, mul_one]
  exact hu'

end Borel

section Quotient

variable {K Y : Type*} [Group K] [Finite K] [Group Y] [Finite Y] {D : UniversalRootDatum K}
  {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {π : K →* Y} {M : ℕ}

theorem eq_one_of_mem_normalizer189 (h : BorelQuotient D n H π M) (h3 : ¬ 3 ∣ M)
    (S : Sylow 2 Y) {y : Y} (hy : y ∈ Subgroup.normalizer ((S : Subgroup Y) : Set Y))
    (hy3 : y ^ 3 = 1) : y = 1 := by
  obtain ⟨π', hπ', hker, hS⟩ := h.exists_conj_eq S
  have hQ : BorelQuotient D n H π' M :=
    { ct := h.ct, extras := h.extras, pGroup := h.pGroup, surj := hπ', odd := h.odd
      torus_pow := h.torus_pow
      ker_central := fun z hz => h.ker_central z (hker ▸ hz)
      ker_pow := fun z hz => h.ker_pow z (hker ▸ hz) }
  rw [hS, hQ.normalizer_map_posUnipotent] at hy
  obtain ⟨b, hb, rfl⟩ := hy
  have hU : IsPGroup 2 (posUnipotent D) := isPGroup_iSup_pos h.extras h.pGroup
  obtain ⟨k, hk⟩ := hU ⟨b ^ M, pow_mem_posUnipotent189 h.ct h.extras h.torus_pow hb⟩
  have hk' : (b ^ M) ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hbk : π' b ^ (M * 2 ^ k) = 1 := by
    rw [← map_pow, pow_mul, hk', map_one]
  have hcop : Nat.Coprime 3 (M * 2 ^ k) :=
    Nat.Coprime.mul_right ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3)
      (Nat.Coprime.pow_right k (by norm_num))
  exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hy3)
    (orderOf_dvd_of_pow_eq_one hbk))

end Quotient

theorem eq_one_of_mem_normalizer_projSL189 {Y : Type} [Group Y] [Finite Y] {n : ℕ} (hn : Odd n)
    (e : Y ≃* projSL 3 (GaloisField 2 n)) (S : Sylow 2 Y) {y : Y}
    (hy : y ∈ Subgroup.normalizer ((S : Subgroup Y) : Set Y)) (hy3 : y ^ 3 = 1) : y = 1 := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact Nat.not_odd_zero hn
  have h2n : 2 ^ n % 3 = 2 := by
    obtain ⟨m, rfl⟩ := hn
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have h3 : ¬ 3 ∣ Nat.card (GaloisField 2 n) - 1 := by
    rw [GaloisField.card 2 n hn0]
    generalize 2 ^ n = N at h2n ⊢
    omega
  have hrange : projSL 3 (GaloisField 2 n) = (Matrix.SpecialLinearGroup.toPGL :
      Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 n) →* _).range := by
    rw [projSL, CFSG.PGLModel.projImage, Matrix.SpecialLinearGroup.toPGL, MonoidHom.range_comp,
      Matrix.SpecialLinearGroup.range_toGL_eq_ker_det]
  let e₁ : Matrix.ProjectiveSpecialLinearGroup (Fin 3) (GaloisField 2 n) ≃* Y :=
    ((QuotientGroup.quotientMulEquivOfEq Matrix.SpecialLinearGroup.toPGL_ker.symm).trans
      ((QuotientGroup.quotientKerEquivRange _).trans
        (MulEquiv.subgroupCongr hrange.symm))).trans e.symm
  exact eq_one_of_mem_normalizer189 (borelQuotient_sl (m := 2) e₁) h3 S hy hy3

end CFSG.RankThree.PartTwo.Sec18
