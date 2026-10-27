module

public import CFSG.Blueprint.Catalog
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate2261
public import Certificates.Certificate2262
public import Certificates.Certificate2263
public import Certificates.Certificate2264
public import Certificates.Certificate2265
public import Certificates.Certificate2266
public import Certificates.Certificate2267
public import Certificates.Certificate2268
public import Certificates.Certificate2269
public import Certificates.Certificate2270
public import Certificates.Certificate8033

import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndAutThreeOrders
import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrdersLie
import CFSG.GH74.GLS.IVK.Proofs2.Ivk47eOmega
import CFSG.LieType.Chevalley.AdjointCenter
import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuousG2
import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeKillAux
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarElimOrders
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogLargeReeModel
import CFSG.GroupTheory.ABGLocalTools.PStabilityQSL2
import CFSG.Sporadic.Schreier.TitsOuter
import CFSG.Sporadic.Schreier.TitsAutD
import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsGen
public import CFSG.Perm.ChainSpec
import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.Blueprint (LieModel)
open CFSG.Blueprint.Chevalley
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.Open

private lemma three_dvd_sq_sub_one {q : ℕ} (hq : ¬ 3 ∣ q) : 3 ∣ q ^ 2 - 1 := by
  have hq3 : q % 3 = 1 ∨ q % 3 = 2 := by
    have h := Nat.mod_lt q (by norm_num : 0 < 3)
    omega
  have h2 : q ^ 2 % 3 = 1 := by
    rcases hq3 with h | h <;> rw [Nat.pow_mod, h] <;> norm_num
  have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow 2 q (by omega)
  exact Nat.dvd_of_mod_eq_zero (by omega)

private lemma sq_sub_one_ne_zero {q : ℕ} (hq : 2 ≤ q) : q ^ 2 - 1 ≠ 0 := by
  have h : 1 < q ^ 2 := Nat.one_lt_pow (by norm_num) (by omega)
  omega

private lemma one_le_factorization_three_of_three_dvd {n : ℕ} (h : 3 ∣ n) (hn : n ≠ 0) :
    1 ≤ n.factorization 3 := by
  have h3 : (3 : ℕ).factorization 3 = 1 := Nat.Prime.factorization_self Nat.prime_three
  rw [← h3]
  exact (Nat.factorization_le_iff_dvd (by norm_num) hn).mpr h 3

private lemma four_le_factorization_three_of_eightyone_dvd {n : ℕ} (h : 81 ∣ n) (hn : n ≠ 0) :
    4 ≤ n.factorization 3 := by
  have h81 : (81 : ℕ).factorization 3 = 4 := by
    rw [show (81 : ℕ) = 3 ^ 4 by norm_num, Nat.factorization_pow, Finsupp.smul_apply,
      Nat.Prime.factorization_self Nat.prime_three]
    norm_num
  rw [← h81]
  exact (Nat.factorization_le_iff_dvd (by norm_num) hn).mpr h 3

private theorem mem_conj_range_of_congr {L H : Type} [Group L] [Group H] (ψ : L ≃* H)
    (α : MulAut L) (h : MulAut.congr ψ α ∈ (MulAut.conj : H →* MulAut H).range) :
    α ∈ (MulAut.conj : L →* MulAut L).range := by
  obtain ⟨g, hg⟩ := h
  refine ⟨ψ.symm g, ?_⟩
  ext y
  apply ψ.injective
  have hy : g * ψ y * g⁻¹ = ψ (α y) := by
    have h' := congrArg (fun φ : MulAut H => φ (ψ y)) hg
    simpa [MulAut.conj_apply, MulAut.congr_apply, MulEquiv.trans_apply] using h'
  simp only [MulAut.conj_apply, map_mul, map_inv, MulEquiv.apply_symm_apply]
  exact hy

private lemma two_pow_mod_three_of_odd {f : ℕ} (hf : Odd f) : 2 ^ f % 3 = 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, f = 2 * m + 1 := hf
  have h4 : (4 : ℕ) ^ m % 3 = 1 := by
    induction m with
    | zero => norm_num
    | succ m ih => rw [pow_succ, Nat.mul_mod, ih]
  have hpow : 2 ^ (2 * m + 1) = 2 * 4 ^ m := by
    rw [pow_succ, pow_mul]
    norm_num
    ring
  rw [hpow, Nat.mul_mod, h4]

section Certificate34


private lemma not_three_dvd_exponent_of_lieModel_G2 {L : Type} [Group L] [Finite L] {p f : ℕ}
    (h : LieModel L .G2 0 p f) (h27 : (Nat.card L).factorization 3 = 3) : ¬ 3 ∣ f := by
  obtain ⟨hp, hf1, -, hp3⟩ := h.admissible
  have hcard : Nat.card L = ordG2 (p ^ f) := by
    rw [CFSG.EvenSmallLie.CatalogOrders.card_eq_lieOrd_of_exceptional
      (h.chevalleyExceptionalModel (by decide))]
    rfl
  have hq3 : ¬ 3 ∣ p ^ f := by
    intro h3
    have hp_eq : p = 3 := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
      (Nat.prime_three.dvd_of_dvd_pow h3) |>.symm
    subst hp_eq
    have h81 : 81 ∣ Nat.card L := by
      rw [hcard]
      exact eightyone_dvd_ordG2 (dvd_pow_self 3 (by omega))
    have hle := four_le_factorization_three_of_eightyone_dvd h81 (Nat.card_pos.ne')
    omega
  have hp3' : ¬ 3 ∣ p := fun h3 => hq3 (h3.trans (dvd_pow_self p (by omega)))
  have h2q : 2 ≤ p ^ f := hp.two_le.trans (Nat.le_self_pow (by omega) p)
  have hord := factorization_three_ordG2 (q := p ^ f) hq3 h2q
  rw [hcard, hord] at h27
  have hone : ((p ^ f) ^ 2 - 1).factorization 3 = 1 := by omega
  have hsplit := factorization_three_pow_sq_sub_one (q := p) (f := f) hp3' hp.two_le
    (by omega)
  have hsum : (p ^ 2 - 1).factorization 3 + f.factorization 3 = 1 := by
    rw [← hsplit]
    exact hone
  have hpos : 1 ≤ (p ^ 2 - 1).factorization 3 :=
    one_le_factorization_three_of_three_dvd (three_dvd_sq_sub_one hp3')
      (sq_sub_one_ne_zero hp.two_le)
  intro h3f
  have hne : f ≠ 0 := by omega
  have hle := one_le_factorization_three_of_three_dvd h3f hne
  omega

theorem exists_eq_conj_of_lieModel_G2 {L : Type} [Group L] [Finite L] {p f : ℕ}
    (h : LieModel L .G2 0 p f) (h27 : (Nat.card L).factorization 3 = 3) (φ : MulAut L)
    (hφ : ∃ n : ℕ, φ ^ (3 ^ n) = 1) : ∃ k : L, φ = MulAut.conj k := by
  obtain ⟨hp, hf1, -, hp3⟩ := h.admissible
  have hf3 : ¬ 3 ∣ f := not_three_dvd_exponent_of_lieModel_G2 h h27
  obtain ⟨K, hKfield, hKfin, hKcard, ⟨e₀⟩⟩ :=
    CFSG.GH74.GLS.IVK.Proofs2.Ivk47.untwisted_of_lieModel_G2 h
  letI := hKfield
  letI := hKfin
  have hcen : Subgroup.center (adjointGroup Tag.G2 K) = ⊥ :=
    CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
  let e : L ≃* adjointGroup Tag.G2 K :=
    e₀.trans ((QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot)
  let q : TauCeti.PrimePower := ⟨p, f, hp, by omega⟩
  have hqcard : Nat.card K = q.card := hKcard.trans (TauCeti.PrimePower.card_def q).symm
  haveI : CharP K q.p := CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow hp hKcard
  obtain ⟨Q, hQgrp, hQcyc, Θ, hQdvd, hker⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_hom_cyclic_G2 q
      (by simpa [q, TauCeti.PrimePower.card_def] using hp3) K hqcard
  obtain ⟨n, hn⟩ := hφ
  have hQ3 : ¬ 3 ∣ Nat.card Q := by
    have hQdvd' : Nat.card Q ∣ 2 * f := by simpa [q] using hQdvd
    intro h3Q
    have h3 : 3 ∣ 2 * f := h3Q.trans hQdvd'
    rcases Nat.prime_three.dvd_mul.mp h3 with h | h
    · norm_num at h
    · exact hf3 h
  have hcop : Nat.Coprime (3 ^ n) (Nat.card Q) :=
    Nat.Coprime.pow_left n
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hQ3)
  have hinner : MulAut.congr e φ ∈ Θ.ker := by
    rw [MonoidHom.mem_ker]
    have h1 : (MulAut.congr e φ) ^ 3 ^ n = 1 := by
      rw [← map_pow, hn, map_one]
    have h2 : Θ (MulAut.congr e φ) ^ 3 ^ n = 1 := by
      rw [← map_pow, h1, map_one]
    have h3 : Θ (MulAut.congr e φ) ^ Nat.card Q = 1 := pow_card_eq_one'
    have h4 := pow_gcd_eq_one.mpr ⟨h2, h3⟩
    have hg : Nat.gcd (3 ^ n) (Nat.card Q) = 1 := hcop
    rwa [hg, pow_one] at h4
  rw [hker] at hinner
  obtain ⟨k, hk⟩ := mem_conj_range_of_congr e φ hinner
  exact ⟨k, hk.symm⟩

theorem factorization_three_card_ne_three_of_lieModel_trialityD4 {L : Type} [Group L] {p f : ℕ}
    (h : LieModel L .trialityD4 0 p f) : (Nat.card L).factorization 3 ≠ 3 := by
  obtain ⟨hp, hf1, -⟩ := h.admissible
  have hcard : Nat.card L = ordTrialityD4 (p ^ f) := by
    rw [CFSG.EvenSmallLie.CatalogOrders.card_eq_lieOrd_of_exceptional
      (h.chevalleyExceptionalModel (by decide))]
    rfl
  intro h3
  by_cases hN : Nat.card L = 0
  · rw [hN] at h3
    norm_num at h3
  by_cases hq : 3 ∣ p ^ f
  · have hp_eq : p = 3 := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
      (Nat.prime_three.dvd_of_dvd_pow hq) |>.symm
    subst hp_eq
    have h81 : 81 ∣ Nat.card L := by
      rw [hcard]
      exact eightyone_dvd_ordTrialityD4 (dvd_pow_self 3 (by omega))
    have hle := four_le_factorization_three_of_eightyone_dvd h81 hN
    omega
  · have hp3' : ¬ 3 ∣ p := fun h3p => hq (h3p.trans (dvd_pow_self p (by omega)))
    have h2q : 2 ≤ p ^ f := hp.two_le.trans (Nat.le_self_pow (by omega) p)
    have hord := factorization_three_ordTrialityD4 (q := p ^ f) hq h2q
    rw [hcard, hord] at h3
    have hdiv : 3 ∣ (p ^ f) ^ 2 - 1 := three_dvd_sq_sub_one hq
    have hge := one_le_factorization_three_of_three_dvd hdiv (sq_sub_one_ne_zero h2q)
    omega

theorem exists_eq_conj_of_lieModel_twistedF4 {L : Type} [Group L] [Finite L] {f : ℕ}
    (h : LieModel L .twistedF4 0 2 f) (h27 : (Nat.card L).factorization 3 = 3) (φ : MulAut L)
    (hφ : ∃ n : ℕ, φ ^ (3 ^ n) = 1) : ∃ k : L, φ = MulAut.conj k := by
  have hR : CFSG.Blueprint.ReeTitsModel L .twistedF4 2 f := (h.reeTitsModel (by decide)).2
  obtain ⟨-, hf3le, hodd, -, houtcard, -⟩ :=
    large_Ree_model_field_outer_group_and_inner_involutions L 2 f hR
  have hcard : Nat.card L = ordTwistedF4 (2 ^ f) :=
    CFSG.AGLEmbedding.card_of_reeTitsModel_twistedF4_exact hR
  have hqmod : 2 ^ f % 3 = 2 := two_pow_mod_three_of_odd hodd
  have hord := factorization_three_ordTwistedF4 (q := 2 ^ f) hqmod
  rw [hcard, hord] at h27
  have hone : (2 ^ f + 1).factorization 3 = 1 := by omega
  rw [factorization_three_two_pow_add_one hodd] at hone
  have hf3 : ¬ 3 ∣ f := by
    intro h3f
    have hne : f ≠ 0 := by omega
    have hle := one_le_factorization_three_of_three_dvd h3f hne
    omega
  have hOut3 : ¬ 3 ∣ Nat.card (Outer L) := by
    rw [houtcard]
    exact hf3
  obtain ⟨n, hn⟩ := hφ
  obtain ⟨k, hk⟩ :=
    CFSG.AGLEmbedding.mem_inner_of_pow_prime_pow_eq_one Nat.prime_three hOut3 hn
  exact ⟨k, hk.symm⟩

end Certificate34

section CertificateTits


theorem exists_eq_conj_of_lieModel_tits {L : Type} [Group L] [Finite L]
    (h : LieModel L .Tits 0 2 1) (φ : MulAut L) (hφ : ∃ n : ℕ, φ ^ (3 ^ n) = 1) :
    ∃ k : L, φ = MulAut.conj k := by
  have hR : CFSG.Blueprint.ReeTitsModel L .Tits 2 1 := (h.reeTitsModel (by decide)).2
  obtain ⟨e⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv L 2 1 hR
  have hout : Nat.card (Outer L) = 2 := by
    rw [Nat.card_congr (equivalence e).toEquiv]
    exact CFSG.Sporadic.Schreier.Tits.card_outer_titsD
  have hOut3 : ¬ 3 ∣ Nat.card (Outer L) := by
    rw [hout]
    norm_num
  obtain ⟨n, hn⟩ := hφ
  obtain ⟨k, hk⟩ :=
    CFSG.AGLEmbedding.mem_inner_of_pow_prime_pow_eq_one Nat.prime_three hOut3 hn
  exact ⟨k, hk.symm⟩

end CertificateTits

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
