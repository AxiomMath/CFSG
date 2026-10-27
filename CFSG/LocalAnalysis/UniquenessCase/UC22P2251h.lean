module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P2251b
import CFSG.LocalAnalysis.UniquenessCase.UC22P21a
import CFSG.LocalAnalysis.UniquenessCase.UC22P21k
import CFSG.LocalAnalysis.UniquenessCase.UC22P22rs
import CFSG.LocalAnalysis.UniquenessCase.UC22Main1
import CFSG.LocalAnalysis.UniquenessCase.UC6Mod

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem uc22p2251h_isStronglyPEmbedded (D : Data G) (hk : D.k = 1) :
    CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M := by
  unfold Data.k CFSG.LocalAnalysis.RankThreeUC.kParam at hk
  split_ifs at hk with h
  · exact h
  · omega

namespace P2251h

theorem seven_le_of_dvd_two_pow_sub_one {n r : ℕ} (hn : 1 ≤ n) (h3 : ¬ 3 ∣ 2 ^ n - 1) (hr : r.Prime)
    (hrn : r ∣ 2 ^ n - 1) : 7 ≤ r := by
  have hodd : Odd n := by
    rcases Nat.even_or_odd n with ⟨k, rfl⟩ | h
    · exfalso
      apply h3
      have h4 : 2 ^ (k + k) = 4 ^ k := by rw [← two_mul, pow_mul]; norm_num
      rw [h4]
      have := Nat.sub_dvd_pow_sub_pow 4 1 k
      rw [one_pow] at this
      exact (show 3 ∣ 4 - 1 by norm_num).trans this
    · exact h
  have h5 : ¬ 5 ∣ 2 ^ n - 1 := by
    obtain ⟨k, rfl⟩ := hodd
    have key : ∀ k : ℕ, 2 ^ (2 * k + 1) % 5 = 2 ∨ 2 ^ (2 * k + 1) % 5 = 3 := by
      intro k
      induction k with
      | zero => norm_num
      | succ k ih =>
        rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by ring, pow_add, Nat.mul_mod]
        rcases ih with h | h <;> rw [h] <;> norm_num
    intro hd
    have hpos : 0 < 2 ^ (2 * k + 1) := by positivity
    have hk := key k
    generalize 2 ^ (2 * k + 1) = a at hd hpos hk
    omega
  have h2 : ¬ 2 ∣ 2 ^ n - 1 := by
    intro hd
    have h2n : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
    have hpos : 0 < 2 ^ n := by positivity
    generalize 2 ^ n = a at hd h2n hpos
    omega
  by_contra hlt
  push Not at hlt
  have := hr.two_le
  interval_cases r
  · exact h2 hrn
  · exact h3 hrn
  · exact absurd hr (by norm_num)
  · exact h5 hrn
  · exact absurd hr (by norm_num)

theorem exists_isChev {M K : Subgroup G} (hK : K ∈ calC M) (hbs : BadShape22 (Bar2 K)) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ IsChev (BarInf K) p := by
  obtain ⟨e⟩ := uc22p21k_barInf_equiv_of_center_bot hK.2.2 hbs.layerShape.center_eq_bot
  have key : ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ CFSG.Blueprint.LieModel (Bar2 K) .PSL 2 p 1 := by
    rcases hbs with h | h
    · refine ⟨5, Nat.prime_five, by norm_num, ?_⟩
      obtain ⟨eA⟩ := BadShape22.nonempty_mulEquiv_alt_five_of_isL2Ev_two h
      haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
      have hK5 : Nat.card (GaloisField 5 1) = 5 ^ 1 := GaloisField.card 5 1 one_ne_zero
      obtain ⟨e5⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five (GaloisField 5 1)
        (Or.inr (by rw [hK5, pow_one]))
      exact Or.inl ⟨by decide, ⟨Nat.prime_five, le_rfl, by decide⟩, GaloisField 5 1, inferInstance, inferInstance,
        hK5, ⟨eA.trans e5.symm⟩⟩
    · exact ⟨7, Nat.prime_seven, by norm_num,
        CFSG.LocalAnalysis.ComponentInitial.PSL3_two_PSL2_seven_paired_isomorphism _ h⟩
  obtain ⟨p, hp, hp2, hm⟩ := key
  exact ⟨p, hp, hp2, .PSL, 2, 1, hm.admissible, CFSG.Blueprint.LieModel.of_mulEquiv e.symm hm⟩

theorem conj_mem_opp {X : Subgroup G} {w : G} (hw : w ∈ normalizer (X : Set G)) (p : ℕ) {x : G}
    (hx : x ∈ Opp p X) : w * x * w⁻¹ ∈ Opp p X := by
  have h1 : X.map (MulAut.conj w).toMonoidHom = X := mem_normalizer_iff_map_conj_eq.mp hw
  have h2 := CFSG.RankThree.PartOne.Equivariance.pElementSubgroup_conjBy p w X
  unfold CFSG.RankThree.PartOne.conjBy at h2
  rw [h1] at h2
  have h3 : w * x * w⁻¹ ∈ (CFSG.RankThree.PartOne.pElementSubgroup p X).map (MulAut.conj w).toMonoidHom :=
    mem_map.2 ⟨x, hx, by simp [MulAut.conj_apply]⟩
  rw [← h2] at h3
  exact h3

theorem mem_pCoreOf_iff {K : Subgroup G} (x : ↥K) : (x : G) ∈ pCoreOf 2 K ↔ x ∈ CFSG.pCore 2 ↥K :=
  mem_map_iff_mem K.subtype_injective

theorem exists_mem_inf_centralizer {A K : Subgroup G} {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hA : IsPGroup r A)
    (hAK : A ≤ normalizer (K : Set G)) (hc : ⁅A, K⁆ ≤ pCoreOf 2 K) {b : G} (hb : b ∈ K) :
    ∃ y ∈ K ⊓ centralizer (A : Set G), b⁻¹ * y ∈ pCoreOf 2 K := by
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : ¬ r ∣ Nat.card (pCoreOf 2 K) := by
    intro hd
    obtain ⟨k, hk⟩ := (uc22main1_isPGroup_pCoreOf K).exists_card_eq
    rw [hk] at hd
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow hd))
  have hFX : ∀ x ∈ A, ∀ f ∈ pCoreOf 2 K, x * f * x⁻¹ ∈ pCoreOf 2 K := fun x hx f hf =>
    uc22main1_conj_mem_pCoreOf (fun n hn k hk => (mem_normalizer_iff.1 (hAK hn) k).1 hk) hx hf
  have hq : ∀ x ∈ A, b⁻¹ * (x * b * x⁻¹) ∈ pCoreOf 2 K := by
    intro x hx
    have h1 : ⁅b⁻¹, x⁆ ∈ ⁅A, K⁆ := by
      rw [Subgroup.commutator_comm]
      exact commutator_mem_commutator (inv_mem hb) hx
    have h2 := hc h1
    rw [commutatorElement_def, inv_inv] at h2
    simpa only [mul_assoc] using h2
  obtain ⟨y, hy, hyA⟩ := UC6.exists_fixed_in_coset_uc6 A (pCoreOf 2 K) hA hF hFX b hq
  refine ⟨y, mem_inf.2 ⟨?_, ?_⟩, hy⟩
  · have : y = b * (b⁻¹ * y) := by group
    rw [this]
    exact mul_mem hb (uc22main1_pCoreOf_le K hy)
  · rw [mem_centralizer_iff]
    intro x hx
    have := hyA x hx
    calc x * y = x * y * x⁻¹ * x := by group
      _ = y * x := by rw [this]

@[expose] def barMap {Y K : Subgroup G} (hYK : Y ≤ K) : ↥Y →* Bar2 K :=
  (QuotientGroup.mk' (CFSG.pCore 2 ↥K)).comp (inclusion hYK)

theorem barMap_surjective {Y K : Subgroup G} (hYK : Y ≤ K)
    (hcov : ∀ b ∈ K, ∃ y ∈ Y, b⁻¹ * y ∈ pCoreOf 2 K) : Function.Surjective (barMap hYK) := by
  intro z
  obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K) z
  obtain ⟨y, hy, hky⟩ := hcov k k.2
  refine ⟨⟨y, hy⟩, ?_⟩
  show QuotientGroup.mk' _ (inclusion hYK ⟨y, hy⟩) = QuotientGroup.mk' _ k
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, ← mem_pCoreOf_iff]
  have := inv_mem hky
  rw [mul_inv_rev, inv_inv] at this
  simpa using this

theorem nonempty_bar2_equiv {Y K : Subgroup G} (hYK : Y ≤ K) (hcov : ∀ b ∈ K, ∃ y ∈ Y, b⁻¹ * y ∈ pCoreOf 2 K)
    (hK : LayerShape22 (Bar2 K)) : Nonempty (Bar2 Y ≃* Bar2 K) := by
  haveI := hK.isSimpleGroup
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsurj := barMap_surjective hYK hcov
  have hker : (barMap hYK).ker = (CFSG.pCore 2 ↥K).comap (inclusion hYK) := by
    rw [barMap, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  have le1 : (barMap hYK).ker ≤ CFSG.pCore 2 ↥Y := by
    refine CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup (barMap hYK).normal_ker ?_
    rw [hker]
    exact (CFSG.pCore_isPGroup (p := 2) (G := ↥K)).comap_of_injective _ (inclusion_injective hYK)
  have le2 : CFSG.pCore 2 ↥Y ≤ (barMap hYK).ker := by
    have hn : ((CFSG.pCore 2 ↥Y).map (barMap hYK)).Normal :=
      (CFSG.pCore_normal (p := 2) (G := ↥Y)).map _ hsurj
    rcases hn.eq_bot_or_eq_top with h | h
    · exact (Subgroup.map_eq_bot_iff _).1 h
    · exfalso
      have hp : IsPGroup 2 ((CFSG.pCore 2 ↥Y).map (barMap hYK)) :=
        (CFSG.pCore_isPGroup (p := 2) (G := ↥Y)).map _
      rw [h] at hp
      obtain ⟨k, hk⟩ := hp.exists_card_eq
      rw [card_top] at hk
      have h3 := hK.three_dvd_card
      rw [hk] at h3
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
  exact ⟨(QuotientGroup.quotientMulEquivOfEq (le_antisymm le2 le1)).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ hsurj)⟩

theorem eq_opp_sup {Y K : Subgroup G} (hYK : Y ≤ K) (hcov : ∀ b ∈ K, ∃ y ∈ Y, b⁻¹ * y ∈ pCoreOf 2 K)
    (hK : LayerShape22 (Bar2 K)) : K = Opp 3 Y ⊔ pCoreOf 2 K := by
  haveI := hK.isSimpleGroup
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hXY : Opp 3 Y ≤ Y := by
    unfold Opp CFSG.RankThree.PartOne.pElementSubgroup
    exact (closure_le Y).2 fun x hx => hx.1
  set Xb : Subgroup (Bar2 K) := ((Opp 3 Y).subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) with hXb
  have hXn : Xb.Normal := by
    constructor
    intro z hz w
    obtain ⟨x, hx, rfl⟩ := mem_map.1 hz
    obtain ⟨⟨y, hy⟩, rfl⟩ := barMap_surjective hYK hcov w
    have hyx : ((inclusion hYK ⟨y, hy⟩ * x * (inclusion hYK ⟨y, hy⟩)⁻¹ : ↥K)) ∈ (Opp 3 Y).subgroupOf K := by
      simp only [mem_subgroupOf, coe_mul, coe_inv, coe_inclusion]
      exact conj_mem_opp (le_normalizer hy) 3 (mem_subgroupOf.1 hx)
    refine mem_map.2 ⟨_, hyx, ?_⟩
    simp only [barMap, MonoidHom.coe_comp, Function.comp_apply, map_mul, map_inv]
  rcases hXn.eq_bot_or_eq_top with h | h
  · exfalso
    have h3Y : 3 ∣ Nat.card Y := hK.three_dvd_card.trans (card_dvd_of_surjective _ (barMap_surjective hYK hcov))
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥Y) 3 h3Y
    have hyX : (y : G) ∈ Opp 3 Y := by
      unfold Opp CFSG.RankThree.PartOne.pElementSubgroup
      exact subset_closure ⟨y.2, 1, by rw [orderOf_coe, hy, pow_one]⟩
    have hyP : (y : G) ∈ pCoreOf 2 K := by
      have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥K) (⟨y, hYK y.2⟩ : ↥K) ∈ Xb :=
        mem_map_of_mem _ (show (⟨y, hYK y.2⟩ : ↥K) ∈ (Opp 3 Y).subgroupOf K from hyX)
      rw [h, mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact (mem_pCoreOf_iff (K := K) ⟨(y : G), hYK y.2⟩).2 h1
    obtain ⟨k, hk⟩ := (uc22main1_isPGroup_pCoreOf K) ⟨_, hyP⟩
    have h2 : orderOf (y : G) ∣ 2 ^ k :=
      orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
    rw [orderOf_coe, hy] at h2
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h2) (by norm_num)
  · refine le_antisymm (fun b hb => ?_) (sup_le (hXY.trans hYK) (uc22main1_pCoreOf_le K))
    have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥K) (⟨b, hb⟩ : ↥K) ∈ Xb := by
      rw [h]
      exact mem_top _
    obtain ⟨x, hx, hxb⟩ := mem_map.1 h1
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hxb
    have h2 : ((x⁻¹ * ⟨b, hb⟩ : ↥K) : G) ∈ pCoreOf 2 K := (mem_pCoreOf_iff _).2 hxb
    have h3 : b = (x : G) * ((x⁻¹ * ⟨b, hb⟩ : ↥K) : G) := by simp
    rw [h3]
    exact mul_mem (mem_sup_left (mem_subgroupOf.1 hx)) (mem_sup_right h2)

end P2251h

open P2251h

theorem uc22p2251h_exists_A (D : Data G) (Ch : Choice2011 G) (hH : H1930 D) (c : Ctx21 D Ch) (hk : D.k = 1)
    (hn : 3 ≤ c.n) (h2112 : S21_12 D Ch) {K : Subgroup G} (hK : K ∈ calC D.M) (hbs : BadShape22 (Bar2 K)) :
    ∃ A : Subgroup G, A ≤ c.B0 ∧ (Nat.card A).Prime ∧ 7 ≤ Nat.card A ∧ ¬ normalizer (A : Set G) ≤ D.M ∧
      normalizer (A : Set G) ≠ ⊤ ∧ ⁅A, K⁆ ≤ pCoreOf 2 K := by
  have hsp := uc22p2251h_isStronglyPEmbedded D hk
  let c' : Ctx21 D Ch := { c with B := c.B0, hB := c.hB0, hle := le_rfl }
  have h3 : ¬ 3 ∣ Nat.card c.B0 := by
    intro h3
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥c.B0) 3 h3
    have hcard : Nat.card (zpowers (x : G)) = 3 := by rw [Nat.card_zpowers, orderOf_coe, hx]
    have hAB : zpowers (x : G) ≤ c.B0 := zpowers_le.2 x.2
    have hne : zpowers (x : G) ≠ ⊥ := by
      intro h
      rw [h, card_bot] at hcard
      omega
    have hU := uc22p22r_mem_uniqueSet_of_sp D Nat.prime_three hsp (hAB.trans c.hBM)
      (IsPGroup.of_card (n := 1) (by rw [hcard, pow_one])) hne
    exact s21_2 D Ch hH c' _ hAB (normalizer_le_of_mem_uniqueSet D.maxLocal hU)
  have h3n : ¬ 3 ∣ 2 ^ c.n - 1 := fun h => h3 (by
    have h' : (3 : ℕ) ∈ etaSet c.n := ⟨Nat.prime_three, h⟩
    rw [← c.hpi] at h'
    exact h'.2)
  have hn1 : 2 ^ c.n - 1 ≠ 1 := by
    have h8 : 8 ≤ 2 ^ c.n := by
      calc (8 : ℕ) = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ c.n := Nat.pow_le_pow_right (by norm_num) hn
    generalize 2 ^ c.n = a at h8
    omega
  obtain ⟨r, hr, hrn⟩ := Nat.exists_prime_and_dvd hn1
  have hr7 : 7 ≤ r := seven_le_of_dvd_two_pow_sub_one (by omega) h3n hr hrn
  have hrB : r ∣ Nat.card c.B0 := by
    have h' : r ∈ etaSet c.n := ⟨hr, hrn⟩
    rw [← c.hpi] at h'
    exact h'.2
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥c.B0) r hrB
  have hxo : orderOf (x : G) = r := by rw [orderOf_coe, hx]
  have hAB : zpowers (x : G) ≤ c.B0 := zpowers_le.2 x.2
  have hAcard : Nat.card (zpowers (x : G)) = r := by rw [Nat.card_zpowers, hxo]
  refine ⟨zpowers (x : G), hAB, hAcard ▸ hr, hAcard ▸ hr7, s21_2 D Ch hH c' _ hAB, ?_, ?_⟩
  · intro htop
    haveI := D.standing.simple
    rcases (normalizer_eq_top_iff.1 htop).eq_bot_or_eq_top with h | h
    · rw [h, card_bot] at hAcard
      exact hr.one_lt.ne hAcard
    · exact hsp.1 (eq_top_iff.2 (by rw [← h]; exact hAB.trans c.hBM))
  · obtain ⟨p, hp, hp2, hch⟩ := exists_isChev hK hbs
    have hc := (h2112 hH c' K hK p hp hp2 hch).2
    have hle : zpowers (x : G) ≤ CFSG.Quasithin.opResidual 3 c.B0 :=
      zpowers_le.2 (CFSG.Quasithin.mem_opResidual_of_coprime x.2
        (by rw [hxo]; exact (Nat.coprime_primes hr Nat.prime_three).2 (by omega)))
    exact (commutator_mono hle le_rfl).trans hc

theorem uc22p2251h_cover {M A K : Subgroup G} (hKM : K ≤ M) (hKn : (K.subgroupOf M).Normal) (hAM : A ≤ M)
    (hA : (Nat.card A).Prime) (hA2 : Nat.card A ≠ 2) (hc : ⁅A, K⁆ ≤ pCoreOf 2 K) (hK : LayerShape22 (Bar2 K)) :
    (∀ b ∈ K, ∃ y ∈ K ⊓ centralizer (A : Set G), b⁻¹ * y ∈ pCoreOf 2 K) ∧
      K = (K ⊓ centralizer (A : Set G)) ⊔ pCoreOf 2 K ∧
      Nonempty (Bar2 (K ⊓ centralizer (A : Set G)) ≃* Bar2 K) ∧
      K = Opp 3 (K ⊓ centralizer (A : Set G)) ⊔ pCoreOf 2 K := by
  haveI : Fact (Nat.card A).Prime := ⟨hA⟩
  have hAK : A ≤ normalizer (K : Set G) := hAM.trans ((normal_subgroupOf_iff_le_normalizer hKM).1 hKn)
  have hcov : ∀ b ∈ K, ∃ y ∈ K ⊓ centralizer (A : Set G), b⁻¹ * y ∈ pCoreOf 2 K := fun b hb =>
    exists_mem_inf_centralizer hA hA2 (IsPGroup.of_card (n := 1) (pow_one _).symm) hAK hc hb
  have hYK : K ⊓ centralizer (A : Set G) ≤ K := inf_le_left
  refine ⟨hcov, le_antisymm (fun b hb => ?_) (sup_le hYK (uc22main1_pCoreOf_le K)),
    nonempty_bar2_equiv hYK hcov hK, eq_opp_sup hYK hcov hK⟩
  obtain ⟨y, hy, hby⟩ := hcov b hb
  have : b = y * (b⁻¹ * y)⁻¹ := by group
  rw [this]
  exact mul_mem (mem_sup_left hy) (mem_sup_right (inv_mem hby))

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
