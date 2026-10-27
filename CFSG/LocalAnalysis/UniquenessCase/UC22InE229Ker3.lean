module

public import CFSG.LocalAnalysis.UniquenessCase.UCKPThreeRank
import CFSG.LocalAnalysis.RankFourTheoremC.PPointAutRank
import CFSG.LocalAnalysis.RankFourTheoremC.Nongeneration.Planes
import CFSG.LocalAnalysis.UniquenessCase.UCKPOut
import CFSG.LocalAnalysis.UniquenessCase.UCKPRank1
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionDefs
public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229ZB
public import CFSG.LocalAnalysis.UniquenessCase.UCFront10

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22ine229k_exists_kernel {M Y : Subgroup G} (hY : IsSubnormal Y M) {p : ℕ}
    (hp : p.Prime) {B : Subgroup G} (hBN : B ≤ normalizer (Y : Set G)) (hBel : IsElemAbelian p B)
    (hR : p ^ 2 * Nat.card ((B.subgroupOf (normalizer (Y : Set G))).map (UC6S846.rhoL Y)) ≤
      Nat.card B) :
    ∃ B₀ : Subgroup G, B₀ ≤ B ∧ IsElemAbelian p B₀ ∧ Nat.card B₀ = p ^ 2 ∧
      ∀ b ∈ B₀, ∀ y ∈ Y, b * y * b⁻¹ * y⁻¹ ∈ pCoreOf 2 M := by
  haveI : Fact p.Prime := ⟨hp⟩
  let BN : Subgroup ↥(normalizer (Y : Set G)) := B.subgroupOf (normalizer (Y : Set G))
  let φ : ↥BN →* MulAut (Bar2 Y) := (UC6S846.rhoL Y).comp BN.subtype
  have hφrange : φ.range = BN.map (UC6S846.rhoL Y) := by
    ext y
    simp only [φ, MonoidHom.mem_range, Subgroup.mem_map, MonoidHom.comp_apply,
      Subgroup.coe_subtype]
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a, a.2, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, rfl⟩
  have hBNcard : Nat.card BN = Nat.card B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBN).toEquiv
  have hker : Nat.card BN = Nat.card φ.range * Nat.card φ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
  let K : Subgroup G := (φ.ker.map BN.subtype).map (normalizer (Y : Set G)).subtype
  have hKB : K ≤ B :=
    calc K ≤ BN.map (normalizer (Y : Set G)).subtype :=
          Subgroup.map_mono (Subgroup.map_subtype_le _)
      _ = B := Subgroup.map_subgroupOf_eq_of_le hBN
  have hKc : p ^ 2 ≤ Nat.card K := by
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _),
      Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
    have h1 : Nat.card φ.range * p ^ 2 ≤ Nat.card φ.range * Nat.card φ.ker :=
      calc Nat.card φ.range * p ^ 2 = p ^ 2 * Nat.card (BN.map (UC6S846.rhoL Y)) := by
            rw [← hφrange, mul_comm]
        _ ≤ Nat.card B := hR
        _ = Nat.card φ.range * Nat.card φ.ker := hBNcard.symm.trans hker
    exact Nat.le_of_mul_le_mul_left h1 Nat.card_pos
  obtain ⟨B₀, hB₀K, hB₀el, hB₀c⟩ := UC6S846.exists_card_p_sq hp (hBel.mono hKB) hKc
  refine ⟨B₀, hB₀K.trans hKB, hB₀el, hB₀c, fun b hb y hy => ?_⟩
  obtain ⟨_, ⟨k, hk, rfl⟩, rfl⟩ := hB₀K hb
  have h1 : UC6S846.rhoL Y (k : ↥(normalizer (Y : Set G))) = 1 := (MonoidHom.mem_ker).1 hk
  exact uc22ine229_pCoreOf_le_of_isSubnormal hY
    ((UC6S846.rhoL_fix_iff Y (k : ↥(normalizer (Y : Set G))) ⟨y, hy⟩).1
      (by rw [h1, MulAut.one_apply]))

theorem uc22ine229k_card_le_of_not_dvd_simple (hOut : RankThreeTheoremC.KFactOutCyclic) {K : Type}
    [Group K] [Finite K] (hs : IsSimpleGroup K) (hnab : ∃ a b : K, a * b ≠ b * a)
    (hcat : IsCatalogGroup K) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpK : ¬ p ∣ Nat.card K)
    {R : Subgroup (MulAut K)} (hR : IsElemAbelian p R) : Nat.card R ≤ p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hrank : CFSG.Open.pRank p (⊤ : Subgroup K) ≤ 0 := by
    obtain ⟨E, -, -, hE⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (⊤ : Subgroup K)
    by_contra hne
    apply hpK
    refine Dvd.dvd.trans ?_ (Subgroup.card_subgroup_dvd_card E)
    rw [hE]
    exact dvd_pow_self p (by omega)
  obtain ⟨T⟩ : Nonempty (Sylow p K) := inferInstance
  have hout := hOut K hs hnab hcat p hp hp2 T
    (RankFourTheoremC.Nongeneration.isCyclic_sylow_of_pRank_le_one hp2 (by omega) T)
  have hZ : center K = ⊥ := by
    rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal K _ hs (center K) inferInstance with h | h
    · exact h
    · obtain ⟨a, b, hab⟩ := hnab
      exact absurd (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b) a) hab
  have hmul := RankFourTheoremC.pRank_mulAut_le_add_pRank_outer hp hZ
  obtain ⟨k, hk⟩ := hR.isPGroup.exists_card_eq
  rw [hk]
  calc p ^ k ≤ p ^ 1 :=
        Nat.pow_le_pow_right hp.pos
          ((CFSG.SectionRank.le_pRank hp.one_lt le_top hR hk).trans (by omega))
    _ = p := pow_one p

theorem uc22ine229k_not_dvd_two_pow_add_one_of_even {n : ℕ} (hn : Even n) :
    ¬ 3 ∣ 2 ^ n + 1 := by
  obtain ⟨k, rfl⟩ := hn
  have h4 : 2 ^ (k + k) = 4 ^ k := by rw [← two_mul, pow_mul]; norm_num
  have h41 : 4 ^ k % 3 = 1 := by rw [Nat.pow_mod]; norm_num
  omega

theorem uc22ine229k_dvd_two_pow_add_one_of_odd {n : ℕ} (hn : Odd n) : 3 ∣ 2 ^ n + 1 := by
  obtain ⟨k, rfl⟩ := hn
  have h4 : 2 ^ (2 * k + 1) = 2 * 4 ^ k := by rw [pow_succ, pow_mul]; norm_num; ring
  have h41 : 4 ^ k % 3 = 1 := by rw [Nat.pow_mod]; norm_num
  rw [h4]
  omega

private theorem exists_inner_index_le_three {X : Type} [Group X] [Finite X] {n : ℕ}
    (hX : IsSU3 X n) (hn : Even n) {R : Subgroup (MulAut X)} (hR : IsElemAbelian 3 R) :
    ∃ R₀ : Subgroup (MulAut X), R₀ ≤ R ∧ R₀ ≤ (MulAut.conj : X →* MulAut X).range ∧
      Nat.card R ≤ 3 * Nat.card R₀ := by
  obtain ⟨N, hNn, -, hcyc, -, hev⟩ := UCK.u3OutShape X n hX
  haveI := hNn
  haveI : IsCyclic (MulAut X ⧸ N) := hcyc
  let f : ↥R →* MulAut X ⧸ N := (QuotientGroup.mk' N).comp R.subtype
  have hpow : ∀ r : ↥R, r ^ 3 = 1 := fun r => Subtype.ext (by simpa using hR.2 r.1 r.2)
  have hrange : Nat.card f.range ≤ 3 := by
    have hexp : Monoid.exponent f.range ∣ 3 := by
      apply Monoid.exponent_dvd_of_forall_pow_eq_one
      rintro ⟨_, r, rfl⟩
      apply Subtype.ext
      rw [SubgroupClass.coe_pow, ← map_pow, hpow r, map_one, OneMemClass.coe_one]
    rw [← IsCyclic.exponent_eq_card]
    exact Nat.le_of_dvd (by norm_num) hexp
  refine ⟨f.ker.map R.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · rintro _ ⟨r, hr, rfl⟩
    exact hev hn ((QuotientGroup.eq_one_iff (r : MulAut X)).1 (MonoidHom.mem_ker.1 hr))
  · rw [Subgroup.card_map_of_injective R.subtype_injective,
      ← Subgroup.card_ker_mul_card_range f]
    calc Nat.card f.ker * Nat.card f.range ≤ Nat.card f.ker * 3 := Nat.mul_le_mul_left _ hrange
      _ = 3 * Nat.card f.ker := mul_comm _ _

theorem uc22ine229k_card_le_of_even {X : Type} [Group X] [Finite X] {n : ℕ} (hX : IsSU3 X n)
    (hn : Even n) {R : Subgroup (MulAut X)} (hR : IsElemAbelian 3 R) : Nat.card R ≤ 3 ^ 2 := by
  obtain ⟨R₀, hR₀R, hR₀inn, hcard⟩ := exists_inner_index_le_three hX hn hR
  have h1 : Nat.card R₀ ≤ 3 :=
    UCK.u3RankOne X n hX 3 Nat.prime_three (by norm_num)
      (uc22ine229k_not_dvd_two_pow_add_one_of_even hn) R₀ hR₀inn (hR.mono hR₀R)
  calc Nat.card R ≤ 3 * Nat.card R₀ := hcard
    _ ≤ 3 * 3 := Nat.mul_le_mul_left _ h1
    _ = 3 ^ 2 := by norm_num

theorem uc22ine229k_card_le_of_even_not_dvd {X : Type} [Group X] [Finite X] {n : ℕ}
    (hX : IsSU3 X n) (hn : Even n) (h3 : ¬ 3 ∣ Nat.card X) {R : Subgroup (MulAut X)}
    (hR : IsElemAbelian 3 R) : Nat.card R ≤ 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨R₀, hR₀R, hR₀inn, hcard⟩ := exists_inner_index_le_three hX hn hR
  have hR₀1 : Nat.card R₀ = 1 := by
    obtain ⟨k, hk⟩ := (hR.mono hR₀R).isPGroup.exists_card_eq
    have hdvd : Nat.card R₀ ∣ Nat.card X :=
      (Subgroup.card_dvd_of_le hR₀inn).trans
        (Subgroup.card_dvd_of_surjective (f := (MulAut.conj : X →* MulAut X).rangeRestrict)
          (MonoidHom.rangeRestrict_surjective _))
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simpa using hk
    · exact absurd ((dvd_pow_self 3 hk0.ne').trans (hk ▸ hdvd)) h3
  rw [hR₀1] at hcard
  omega

theorem uc22ine229k_card_map_le_nine (hKA : UCK.U3ThreeRank) {M Y : Subgroup G}
    (hN : M ≤ normalizer (Y : Set G)) {n : ℕ} (hX : IsSU3 (Bar2 Y) n)
    (hOp : F10.OpRes 3 M = M) {A : Subgroup G} (hAM : A ≤ M) (hAel : IsElemAbelian 3 A) :
    Nat.card ((A.subgroupOf (normalizer (Y : Set G))).map (UC6S846.rhoL Y)) ≤ 3 ^ 2 := by
  obtain ⟨Nsub, hNn, -, hcyc, hR⟩ := hKA (Bar2 Y) n hX
  haveI := hNn
  have hgen := UC6S846.closure_pPrime_map (UC6S846.rhoL Y) _
    (UC6S846.closure_pPrime_subgroupOf hN (p := 3) hOp)
  refine hR _ ?_ ((hAel.subgroupOf _).map _)
  rintro _ ⟨a, ha, rfl⟩
  have haA : (a : G) ∈ A := ha
  have hap : UC6S846.rhoL Y a ^ (3 ^ 1) = 1 := by
    rw [← map_pow]
    have : a ^ 3 ^ 1 = 1 := Subtype.ext (by simpa using hAel.2 _ haA)
    rw [this, map_one]
  exact UC6S846.mem_inner_of_pPow Nsub Nsub _ hcyc (fun φ hφ => Nsub.pow_mem hφ 3)
    Nat.prime_three (Or.inr le_rfl) hgen
    (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 (hAM haA))) hap

end CFSG.LocalAnalysis.UniquenessCase.UC22
