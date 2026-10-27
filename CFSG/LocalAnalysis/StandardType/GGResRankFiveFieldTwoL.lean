module

public import CFSG.LocalAnalysis.StandardType.GGResUnitaryQPlusKProducers
import CFSG.ClassicalInvolution.ModelFacts.UnitaryAutMain
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FU3Card
import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutPSLRestOutdiag
import CFSG.LocalAnalysis.StandardType.GGStdSubSmallUnitDvdPair
import CFSG.Timmesfeld.Orders.Bang

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag

theorem ggPrime_dvd_card_center_quot_of_cover {G S : Type*} [Group G] [Group S]
    (hS : Group.IsPerfect S) {J L : Subgroup G} (hJL : J ≤ L) (δ : S →* ↥J)
    (hδ : Function.Surjective δ) (hker : δ.ker ≤ Subgroup.center S) {g : S} {ℓ : ℕ}
    (hℓ : ℓ.Prime) (hg : orderOf g = ℓ) (hgZ : g ∉ Subgroup.center S) :
    ℓ ∣ Nat.card (↥L ⧸ Subgroup.center ↥L) := by
  set u : ↥L := Subgroup.inclusion hJL (δ g) with hu
  have hv : (QuotientGroup.mk' (Subgroup.center ↥L) u) ≠ 1 := by
    intro h1
    have huZ : u ∈ Subgroup.center ↥L := (QuotientGroup.eq_one_iff u).mp h1
    have hδZ : δ g ∈ Subgroup.center ↥J := by
      rw [Subgroup.mem_center_iff]
      intro j
      apply Subgroup.inclusion_injective hJL
      rw [map_mul, map_mul]
      exact Subgroup.mem_center_iff.mp huZ (Subgroup.inclusion hJL j)
    have hgc : g ∈ (Subgroup.center ↥J).comap δ := hδZ
    rw [CFSG.LocalCores.comap_center_eq_of_perfect hS δ hδ hker] at hgc
    exact hgZ hgc
  have hvℓ : orderOf (QuotientGroup.mk' (Subgroup.center ↥L) u) ∣ ℓ := by
    rw [← hg]
    exact (orderOf_map_dvd _ u).trans
      ((orderOf_map_dvd (Subgroup.inclusion hJL) (δ g)).trans (orderOf_map_dvd δ g))
  rcases (Nat.dvd_prime hℓ).mp hvℓ with h1 | hℓv
  · exact absurd (orderOf_eq_one_iff.mp h1) hv
  · rw [← hℓv]
    exact orderOf_dvd_natCard _

theorem ggCard_largeEvenProj_dvd_card_GL {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (H : Subgroup (GL ι K)) : Nat.card (LargeEvenProj H) ∣ Nat.card (GL ι K) :=
  (Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_subgroup_dvd_card H)

theorem ggCard_center_quot_dvd_card_GL_of_fieldTwo {G : Type} [Group G] {p : ℕ}
    {Bs L : Subgroup G}
    (hL : GGInnerDiagOnLabel
      (fun _ lab => (lab.tag = .B ∨ lab.tag = .C ∨ lab.tag = .D) ∧ lab.rank = 4 ∧ lab.n = 1)
      p Bs L) :
    ∃ (K₂ : Type) (_ : Field K₂) (_ : Fintype K₂), Fintype.card K₂ = 2 ∧
      Nat.card (↥L ⧸ Subgroup.center ↥L) ∣ Nat.card (GL (Fin 4 ⊕ Fin 4) K₂) := by
  obtain ⟨-, ⟨t, r, n⟩, -, hraw⟩ := hL
  obtain ⟨R0, _, I0, F0, -, -, -, ⟨htag, hr, hn⟩, -⟩ := largeEvenRawDatum_exists hraw
  dsimp only at htag hr hn
  subst hr hn
  rcases htag with rfl | rfl | rfl <;>
  · dsimp only [LargeEvenRawDatumLegacy] at hraw
    obtain ⟨K₂, _, _, hK, -, -, θ, -⟩ := hraw
    refine ⟨K₂, inferInstance, Fintype.ofFinite K₂, ?_, ?_⟩
    · rw [Fintype.card_eq_nat_card, hK]
      norm_num
    · rw [Nat.card_congr θ.toEquiv]
      exact ggCard_largeEvenProj_dvd_card_GL _

section GammaCert

theorem GGResHyp.not_exactThree_K_of_rankFive_fieldTwo_L
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hU : GGInnerDiagOnLabel
      (fun p lab => lab.tag = .twA ∧ lab.rank = 5 ∧ 2 ≤ lab.n ∧ p ∣ 2 ^ lab.n + 1) p Bs K)
    (hL : GGInnerDiagOnLabel
      (fun _ lab => (lab.tag = .B ∨ lab.tag = .C ∨ lab.tag = .D) ∧ lab.rank = 4 ∧ lab.n = 1)
      p Bs L) :
    ¬ GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny := by
  intro h3
  obtain ⟨F, _, _, n, -, -, δ, -, -, -, hM, -, -, -, hn3, -⟩ :=
    hH.rankFiveK3_original_facts hU h3
  have hJL : J ≤ L := hH.1.2.2.1.2.2.2.2.2.1.1.trans inf_le_left
  have hUF := hM.field
  obtain ⟨ℓ, hℓ⟩ :=
    CFSG.Timmesfeld.exists_isPrimitivePrimeDivisor (k := 6 * n) (by omega) (by omega)
  have hℓp : ℓ.Prime := hℓ.prime
  have hℓq : ℓ ∣ (2 ^ n) ^ 3 + 1 := by
    rw [← pow_mul]
    refine (hℓ.dvd_add_one_iff (by omega) (n * 3)).2 ⟨⟨1, by ring⟩, fun h => ?_⟩
    have := Nat.le_of_dvd (by omega) h
    omega
  have hℓ3 : ℓ ≠ 3 := by
    rintro rfl
    have := hℓ.eq_two_of_dvd_three (by omega) dvd_rfl
    omega
  have hℓS : ℓ ∣ Nat.card (unitarySU 2 n F 3) := by
    rw [CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_unitarySU_three hUF]
    exact Dvd.dvd.mul_left hℓq _
  have : Fact ℓ.Prime := ⟨hℓp⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' ℓ hℓS
  have hq5 : 5 ≤ 2 ^ n :=
    (show 5 ≤ 2 ^ 3 by norm_num).trans (Nat.pow_le_pow_right (by norm_num) hn3)
  obtain ⟨hperf, hcen⟩ :=
    CFSG.ClassicalInvolution.ModelFacts.UnitaryAut.isPerfect_and_center_unitarySU hUF hq5
      (le_refl 3)
  have hgZ : g ∉ Subgroup.center (unitarySU 2 n F 3) := by
    rw [hcen]
    intro hz
    have h1 : orderOf (⟨g, hz⟩ : unitaryScalars hUF 3) ∣ Nat.card (unitaryScalars hUF 3) :=
      orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, hg, card_unitaryScalars hUF (n := 3) (by norm_num)] at h1
    exact hℓ3 ((Nat.prime_dvd_prime_iff_eq hℓp Nat.prime_three).mp
      (h1.trans (Nat.gcd_dvd_left 3 _)))
  have hker : δ.ker ≤ Subgroup.center (unitarySU 2 n F 3) := fun z hz => by
    obtain ⟨c, hc⟩ := hM.ker z (MonoidHom.mem_ker.mp hz)
    exact SmallU.mem_center_of_scalar hc
  have hℓL := ggPrime_dvd_card_center_quot_of_cover hperf hJL δ hM.surj hker hℓp hg hgZ
  obtain ⟨K₂, _, _, hK₂, hdvd⟩ := ggCard_center_quot_dvd_card_GL_of_fieldTwo hL
  exact OrdPRest.not_dvd_card_GL' (f := 1) (n := 6 * n) (by simpa using hℓ) le_rfl
    (by rw [hK₂, pow_one]) (by simp; omega) (hℓL.trans hdvd)

end GammaCert

end CFSG.StandardType
