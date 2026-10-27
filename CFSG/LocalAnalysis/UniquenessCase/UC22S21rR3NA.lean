module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
import CFSG.LocalAnalysis.EvenBN.GMSK.U3Facts
import CFSG.LocalAnalysis.UniquenessCase.UC22P20d
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214e2
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ParabolicTransfer
import CFSG.Quasithin.Background.B1MoreTwelveA
import CFSG.Quasithin.H13.NQCatUniqueModels
import CFSG.RankThree.GroupTheory.SteinbergCEMutualSupplementResidual

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22r3n_dvd_card_normalizer {X : Type} [Group X] [Finite X] {n : ℕ} (hX : IsU3 X n)
    (Q : Sylow 2 X) {r : ℕ} (hr : r.Prime) (hrn : r ∣ 2 ^ n + 1) (h3 : r ≠ 3 ∨ 9 ∣ 2 ^ n + 1) :
    r ∣ Nat.card (normalizer ((Q : Subgroup X) : Set X)) := by
  have h1 := uc22p2214_bor_card_normalizer (uc22p2214_bor_bender_U3 hX) Q
  rw [(CFSG.LocalAnalysis.EvenBN.GMSK.fusionBenderBorel_of_lieModel_PSU3 hX Q).2.2.2.2] at h1
  have h2 := CFSG.LocalAnalysis.EvenBN.GMSK.card_mul_gcd_of_lieModel_PSU3 hX
  rw [← h1] at h2
  set N := Nat.card ↥(normalizer ((Q : Subgroup X) : Set X))
  set d := Nat.gcd 3 (2 ^ n + 1)
  have h4 : N * d = (2 ^ n) ^ 3 * ((2 ^ n) ^ 2 - 1) := by
    refine Nat.eq_of_mul_eq_mul_right (by positivity : 0 < (2 ^ n) ^ 3 + 1) ?_
    rw [show N * d * ((2 ^ n) ^ 3 + 1) = N * ((2 ^ n) ^ 3 + 1) * d by ring, h2]
    ring
  obtain ⟨m, hm⟩ : ∃ m, 2 ^ n = m + 1 := ⟨2 ^ n - 1, (Nat.sub_add_cancel Nat.one_le_two_pow).symm⟩
  have hsq : (2 ^ n) ^ 2 - 1 = (2 ^ n - 1) * (2 ^ n + 1) := by
    rw [hm, Nat.add_sub_cancel, show (m + 1) ^ 2 = m * (m + 1 + 1) + 1 by ring, Nat.add_sub_cancel]
  rw [hsq] at h4
  by_cases hr3 : r = 3
  · subst hr3
    have h9 : 9 ∣ 2 ^ n + 1 := h3.resolve_left (· rfl)
    have hd : d = 3 := Nat.gcd_eq_left ((by norm_num : (3 : ℕ) ∣ 9).trans h9)
    rw [hd] at h4
    have h93 : 3 * 3 ∣ N * 3 := by
      rw [h4]
      exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right h9 _) _
    exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) h93
  · have hrd : ¬ r ∣ d := fun h =>
      hr3 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 (h.trans (Nat.gcd_dvd_left _ _)))
    have hrNd : r ∣ N * d := by
      rw [h4]
      exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right hrn _) _
    exact (hr.dvd_mul.1 hrNd).resolve_right hrd

theorem uc22r3n_ne_two {X : Type} [Group X] {n : ℕ} (hX : IsSU3 X n) {r : ℕ}
    (hrn : r ∣ 2 ^ n + 1) : r ≠ 2 :=
  Odd.ne_two_of_dvd_nat ((Nat.even_pow' (by
    have := CFSG.LocalAnalysis.EvenBN.GMSK.two_le_of_lieModel_PSU3 hX.2; omega)).2
    even_two).add_one hrn

theorem uc22r3n_normalizer_sylow {H K : Type} [Group H] [Finite H] [Group K] {π : H →* K}
    (hπ : Function.Surjective π) (hk : IsPGroup 2 ↥π.ker) {n : ℕ} (hK : IsSU3 K n)
    (Q : Sylow 2 H) {r : ℕ} (hr : r.Prime) (hrn : r ∣ 2 ^ n + 1) (h3 : r ≠ 3 ∨ 9 ∣ 2 ^ n + 1) :
    r ∣ Nat.card ↥(normalizer ((Q : Subgroup H) : Set H)) ∧
      (¬ r ∣ Nat.card ↥(center K) →
        ∀ P ≤ normalizer ((Q : Subgroup H) : Set H), IsPGroup r ↥P → IsCyclic ↥P) := by
  have : Fact r.Prime := ⟨hr⟩
  have : Finite K := Finite.of_surjective π hπ
  let φ : H →* K ⧸ center K := (QuotientGroup.mk' (center K)).comp π
  have hφ : Function.Surjective φ := (QuotientGroup.mk'_surjective _).comp hπ
  have hφk : ∀ x, φ x = 1 → π x ∈ center K := fun x hx => (QuotientGroup.eq_one_iff (π x)).1 hx
  have hB := normalizer_map_sylow_eq φ hφ Q
  refine ⟨?_, fun hZ P hPN hP => ?_⟩
  · have h := uc22r3n_dvd_card_normalizer hK.2 (Q.mapSurjective hφ) hr hrn h3
    rw [Sylow.coe_mapSurjective, hB] at h
    exact h.trans (card_map_dvd _ φ)
  have hr2 : r ≠ 2 := uc22r3n_ne_two hK hrn
  have hinj : Function.Injective (φ.subgroupMap P) := by
    rw [injective_iff_map_eq_one]
    rintro ⟨x, hx⟩ h1
    have hφx : φ x = 1 := congrArg Subtype.val h1
    obtain ⟨k, hk'⟩ := hP ⟨x, hx⟩
    have hxk : x ^ r ^ k = 1 := by simpa using congrArg Subtype.val hk'
    have hz : π x = 1 := by
      have h1 : π x ^ r ^ k = 1 := by rw [← map_pow, hxk, map_one]
      have h2 : π x ^ Nat.card ↥(center K) = 1 :=
        orderOf_dvd_iff_pow_eq_one.1 (Subgroup.orderOf_dvd_natCard _ (hφk x hφx))
      have h := pow_gcd_eq_one.2 ⟨h1, h2⟩
      rwa [(Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hr).2 hZ)).gcd_eq_one,
        pow_one] at h
    obtain ⟨j, hj⟩ := hk ⟨x, MonoidHom.mem_ker.2 hz⟩
    have h := pow_gcd_eq_one.2 ⟨hxk, (by simpa using congrArg Subtype.val hj : x ^ 2 ^ j = 1)⟩
    rw [(Nat.Coprime.pow k j ((Nat.coprime_primes hr Nat.prime_two).2 hr2)).gcd_eq_one,
      pow_one] at h
    exact Subtype.ext h
  have hodd : Odd (Nat.card ↥(P.map φ)) := by
    obtain ⟨m, hm⟩ := (hP.map φ).exists_card_eq
    rw [hm]
    exact (hr.odd_of_ne_two hr2).pow
  obtain ⟨-, ⟨D, hD, -, -, hQD⟩, -⟩ :=
    CFSG.LocalAnalysis.EvenBN.GMSK.fusionBenderBorel_of_lieModel_PSU3 hK.2 (Q.mapSurjective hφ)
  have := CFSG.Quasithin.H13.NQCat.isCyclic_of_le_of_odd (Q.isPGroup'.map φ) le_normalizer
    ((normal_subgroupOf_iff_le_normalizer le_normalizer).2 le_rfl) hD hQD
    ((map_mono hPN).trans hB.ge) hodd
  exact isCyclic_of_injective _ hinj

theorem uc22r3n_exists_solvable {M T L : Subgroup G} (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M)
    (hLM : L ≤ M) (hML : M ≤ normalizer (L : Set G)) {n : ℕ} (hL : IsSU3 (Bar2 L) n) {r : ℕ}
    (hr : r.Prime) (hrn : r ∣ 2 ^ n + 1) (h3 : r ≠ 3 ∨ 9 ∣ 2 ^ n + 1) :
    ∃ Y : Subgroup G, T ≤ Y ∧ Y ≤ M ∧ Group.IsSolvable ↥Y ∧ r ∣ Nat.card ↥Y ∧
      (¬ r ∣ Nat.card ↥(center (Bar2 L)) → ∀ P ≤ Y, IsPGroup r ↥P → IsCyclic ↥P) := by
  obtain ⟨Q, hQ⟩ := (hT.inf_of_le_normalizer hLM hML).exists_sylow_eq_subgroupOf
  have hsolY := uc22p20d_solvable_normalizer_sylow (hT.inf_of_le_normalizer hLM hML)
  obtain ⟨hdvd, hcyc⟩ := uc22r3n_normalizer_sylow
    (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L))
    (by rw [QuotientGroup.ker_mk']; exact CFSG.pCore_isPGroup) hL Q hr hrn h3
  set Y₀ : Subgroup G := normalizer ((T ⊓ L : Subgroup G) : Set G) ⊓ L with hY₀
  have hYL : Y₀ ≤ L := inf_le_right
  have hY₀Q : Y₀.subgroupOf L = normalizer ((Q : Subgroup ↥L) : Set ↥L) := by
    rw [hY₀, inf_subgroupOf_right, subgroupOf_normalizer_eq inf_le_right, hQ]
  have hTY : T ≤ normalizer (Y₀ : Set G) := fun t ht => by
    have htL := hML (hT.le ht)
    rw [hY₀]
    exact inf_normalizer_le_normalizer_inf
      ⟨le_normalizer (inf_normalizer_le_normalizer_inf ⟨le_normalizer ht, htL⟩), htL⟩
  rw [← hY₀Q] at hdvd hcyc
  have : Group.IsNilpotent ↥T := hT.isPGroup.isNilpotent
  refine ⟨Y₀ ⊔ T, le_sup_right, sup_le (hYL.trans hLM) hT.le,
    CFSG.RankThree.GroupTheory.isSolvable_sup_of_le_normalizer hTY hsolY inferInstance,
    ?_, fun hZ P hPY hP => ?_⟩
  · rw [Nat.card_congr (subgroupOfEquivOfLe hYL).toEquiv] at hdvd
    exact hdvd.trans (card_dvd_of_le le_sup_left)
  have hr2 : r ≠ 2 := uc22r3n_ne_two hL hrn
  have hPY₀ : P ≤ Y₀ := fun x hx => by
    obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
    have hxk : x ^ r ^ k = 1 := by simpa using congrArg Subtype.val hk
    exact CFSG.Quasithin.B1Red.mem_of_odd_orderOf_of_mem_sup hT.isPGroup hTY (hPY hx)
      ((hr.odd_of_ne_two hr2).pow.of_dvd_nat (orderOf_dvd_of_pow_eq_one hxk))
  have hPL : P ≤ L := hPY₀.trans hYL
  have : IsCyclic ↥(P.subgroupOf L) :=
    hcyc hZ (P.subgroupOf L) (fun x hx => mem_subgroupOf.2 (hPY₀ (mem_subgroupOf.1 hx)))
      (hP.comap_subtype (K := L))
  exact isCyclic_of_surjective (subgroupOfEquivOfLe hPL).toMonoidHom
    (subgroupOfEquivOfLe hPL).surjective

end CFSG.LocalAnalysis.UniquenessCase.UC22
