module

public import CFSG.LocalAnalysis.StandardType.GGForkJrPumpLattice
import CFSG.LocalAnalysis.StandardType.GGNbrU63Setup
import CFSG.LocalAnalysis.StandardType.GGD4OddCentVocab
import CFSG.LocalAnalysis.StandardType.GGTableBTransport
import CFSG.LocalAnalysis.StandardType.GGNbrReflGenCore

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Assembly CFSG.Open CFSG.StandardType

section Ambient

variable {G : Type} [Group G] [Finite G]

theorem P9_Wa_card_range {Bs K : Subgroup G} {z : G} {n : ℕ} (hBs : IsElemAbelian 3 Bs)
    (hcard : Nat.card Bs = 3 ^ n) (hz : z ∈ Bs) (hz1 : z ≠ 1)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hker : Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers z) :
    Nat.card (ggGamma K hN).range = 3 ^ (n - 1) := by
  have hz3 : orderOf z = 3 := by
    have := Fact.mk Nat.prime_three
    exact orderOf_eq_prime (hBs.2 z hz) hz1
  have h := NbrU63.card_range_ggGamma_mul_card_inf hN
  rw [hker, Nat.card_zpowers, hz3, hcard] at h
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := by
    refine Nat.exists_eq_succ_of_ne_zero fun h0 => ?_
    rw [h0, pow_zero] at h
    have : Nat.card (ggGamma K hN).range = 0 := by omega
    exact absurd this Nat.card_pos.ne'
  rw [pow_succ] at h
  simpa using Nat.eq_of_mul_eq_mul_right (by norm_num) h

open CFSG.ClassicalGroups.UnitaryFlag in
theorem P9_Wa_tbGroup_twA {S : ℕ → LargeEvenLabel → Prop} {Bs K : Subgroup G} {z : G} {n : ℕ}
    (hBs : IsElemAbelian 3 Bs) (hcard : Nat.card Bs = 3 ^ n) (hn : n = 7 ∨ n = 8) (hz : z ∈ Bs)
    (hz1 : z ≠ 1) (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hker : Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers z)
    (hBstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hS : ∀ lab, S 3 lab → lab.tag = .twA ∧ lab.n = 1) (hK : GGInnerDiagOnLabel S 3 Bs K) :
    ∃ (k : ℕ) (F : Type) (_ : Field F) (_ : Finite F)
      (θ : K ⧸ Subgroup.center K ≃* LargeEvenProj (unitarySU 2 1 F (k + 1))),
      S 3 ⟨.twA, k, 1⟩ ∧ Nat.card F = 4 ∧ 3 ≤ k ∧
      GGTorusTBGroup 3 (n - 1) (LargeEvenProj (unitarySU 2 1 F (k + 1)))
        (LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 1 F (k + 1)))
          (LargeEvenGUSet (Fin (k + 1)) F (2 ^ 1))) K (ggQuotHom θ) (ggGamma K hN).range ∧
      Nat.card (ggGamma K hN).range = 3 ^ (n - 1) := by
  obtain ⟨hperf, lab, hlab, hraw⟩ := hK
  obtain ⟨_, _, _, _, hQ⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨_, _, _, hP⟩ := hQ
  obtain ⟨hSlab, _, _⟩ := hP
  obtain ⟨htag, hn1⟩ := hS lab hSlab
  have hlabeq : (⟨.twA, lab.rank, 1⟩ : LargeEvenLabel) = lab := by
    cases lab
    simp_all
  have hk : 3 ≤ lab.rank := by
    rw [CFSG.Assembly.LargeEvenInLambda2, htag] at hlab
    simp only at hlab
    omega
  rw [CFSG.Assembly.LargeEvenRawDatumLegacy, htag] at hraw
  rw [hn1] at hraw
  obtain ⟨F, hfield, hfin, hFcard, hQc⟩ := hraw
  letI := hfield
  letI := hfin
  obtain ⟨-, -, θ, hpred⟩ := hQc
  obtain ⟨-, hBsN, hind⟩ := hpred
  have hrk := P9_Wa_card_range hBs hcard hz hz1 hN hker
  refine ⟨lab.rank, F, hfield, hfin, θ, hlabeq ▸ hSlab, by rw [hFcard]; norm_num, hk, ?_, hrk⟩
  refine ggTorusTBGroup_of_marking Nat.prime_three hBs hBstar hperf θ hN
    (fun b hb => ggLAut_mem_of_induces K θ hBsN hind hb) (by rw [hrk]) ?_
  rw [hrk]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

end Ambient

section Dispatch

variable {M : Type} [Group M]

theorem P9_Wa_false_of_card_lt {W H : Subgroup M} {b : ℕ} (hb : 0 < b) (hWH : W ≤ H)
    (hdvd : Nat.card H ∣ b) (hlt : b < Nat.card W) : False := by
  have hH : Finite H := Nat.finite_of_card_ne_zero fun h0 => by
    rw [h0, zero_dvd_iff] at hdvd
    omega
  have := (Subgroup.card_le_of_le hWH).trans (Nat.le_of_dvd hb hdvd)
  omega

theorem P9_Wa_nonunitary_n8_false {W H : Subgroup M} (hWH : W ≤ H) (hW : Nat.card W = 2903040)
    (hdvd : Nat.card H ∣ 2 ^ 7 * Nat.factorial 7) : False :=
  P9_Wa_false_of_card_lt (by positivity) hWH hdvd (by rw [hW]; decide +kernel)

theorem P9_Wa_unitary_n7_false {W H : Subgroup M} (hWH : W ≤ H) (hW : Nat.card W = 23040)
    (hdvd : Nat.card H ∣ 2 * Nat.factorial 7) : False :=
  P9_Wa_false_of_card_lt (by positivity) hWH hdvd (by rw [hW]; decide +kernel)

theorem P9_Wa_unitary_n8_false {W H : Subgroup M} {m : ℕ} (hm : m = 8 ∨ m = 9) (hWH : W ≤ H)
    (hW : Nat.card W = 2903040) (hdvd : Nat.card H ∣ 2 * m.factorial) : False := by
  have h9 : Nat.card H ∣ 2 * Nat.factorial 9 :=
    hdvd.trans (Nat.mul_dvd_mul_left 2 (Nat.factorial_dvd_factorial (by omega)))
  exact P9_Wa_false_of_card_lt (by positivity) hWH h9 (by rw [hW]; decide +kernel)

end Dispatch

end CFSG.StandardType.FrameRoute

end
