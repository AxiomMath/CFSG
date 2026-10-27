module

public import CFSG.Quasithin.Background.Harris.R1.Q8Final
public import CFSG.Quasithin.Background.Harris.R1.R1bAbel
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CF67SBasic

public section

namespace CFSG.Quasithin.Background.Harris.R1.S8Aux

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F7
open CFSG.Quasithin.Background.Harris.R1 CFSG.Quasithin.Background.Harris.R1.SplitAux

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_pCoreOf_of_center_bot {K1 H : Subgroup G} (hN : H ≤ Subgroup.normalizer (K1 : Set G))
    (hc : Subgroup.center (OTwoQuot K1) = ⊥) {x : G} (hxH : x ∈ H)
    (hφ : conjOTwoQuot K1 H hN ⟨x, hxH⟩ = 1) (hxK : x ∈ K1) : x ∈ pCoreOf 2 K1 := by
  have hcen : (QuotientGroup.mk ⟨x, hxK⟩ : OTwoQuot K1) ∈ Subgroup.center (OTwoQuot K1) := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact mk_central hN hxH hφ hxK y
  rw [hc, Subgroup.mem_bot] at hcen
  exact (mem_pCoreOf_iff_mem_pCore (⟨x, hxK⟩ : ↥K1)).mpr ((QuotientGroup.eq_one_iff _).mp hcen)

theorem ker_two_power {K1 S : Subgroup G} (hc : Subgroup.center (OTwoQuot K1) = ⊥)
    (hS2 : IsPGroup 2 ↥S) (hN : K1 ⊔ S ≤ Subgroup.normalizer (K1 : Set G)) {x : G}
    (hx : x ∈ K1 ⊔ S) (hφ : conjOTwoQuot K1 (K1 ⊔ S) hN ⟨x, hx⟩ = 1) :
    ∃ n : ℕ, x ^ 2 ^ n = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := exists_pow_two_mem hS2 hN hx
  have hmem : x ^ 2 ^ a ∈ K1 ⊔ S := (K1 ⊔ S).pow_mem hx _
  have hφ' : conjOTwoQuot K1 (K1 ⊔ S) hN ⟨x ^ 2 ^ a, hmem⟩ = 1 := by
    have : (⟨x ^ 2 ^ a, hmem⟩ : ↥(K1 ⊔ S)) = (⟨x, hx⟩ : ↥(K1 ⊔ S)) ^ 2 ^ a := rfl
    rw [this, map_pow, hφ, one_pow]
  have hx' : x ^ 2 ^ a ∈ pCoreOf 2 K1 := mem_pCoreOf_of_center_bot hN hc hmem hφ' ha
  obtain ⟨b, hb⟩ := pCoreOf_isPGroup 2 K1 ⟨x ^ 2 ^ a, hx'⟩
  have hb' : (x ^ 2 ^ a) ^ 2 ^ b = 1 := by
    have := congrArg Subtype.val hb
    simpa using this
  refine ⟨a + b, ?_⟩
  rw [pow_add, pow_mul, hb']

theorem ker_le_pCore {K1 S : Subgroup G} (hc : Subgroup.center (OTwoQuot K1) = ⊥)
    (hS2 : IsPGroup 2 ↥S) (hN : K1 ⊔ S ≤ Subgroup.normalizer (K1 : Set G)) {x : G}
    (hx : x ∈ K1 ⊔ S) (hφ : conjOTwoQuot K1 (K1 ⊔ S) hN ⟨x, hx⟩ = 1) :
    x ∈ pCoreOf 2 (K1 ⊔ S) :=
  ker_le_pCore_of (conjOTwoQuot K1 (K1 ⊔ S) hN)
    (fun g hg => ker_two_power hc hS2 hN g.2 hg) hx hφ

theorem ker_iff_P {K1 S : Subgroup G} (hc : Subgroup.center (OTwoQuot K1) = ⊥)
    (hS2 : IsPGroup 2 ↥S) (hN : K1 ⊔ S ≤ Subgroup.normalizer (K1 : Set G))
    (hO : pCoreOf 2 (K1 ⊔ S) = pCoreOf 2 K1) (g : ↥(K1 ⊔ S)) :
    conjOTwoQuot K1 (K1 ⊔ S) hN g = 1 ↔ (g : G) ∈ pCoreOf 2 K1 := by
  constructor
  · intro hg
    have h := ker_le_pCore hc hS2 hN g.2 hg
    rwa [hO] at h
  · intro hg
    exact P_le_ker hN hg

theorem ker_eq_subgroupOf {K1 S : Subgroup G} (hc : Subgroup.center (OTwoQuot K1) = ⊥)
    (hS2 : IsPGroup 2 ↥S) (hN : K1 ⊔ S ≤ Subgroup.normalizer (K1 : Set G))
    (hO : pCoreOf 2 (K1 ⊔ S) = pCoreOf 2 K1) :
    (conjOTwoQuot K1 (K1 ⊔ S) hN).ker = (pCoreOf 2 K1).subgroupOf (K1 ⊔ S) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  exact ker_iff_P hc hS2 hN hO g

omit [Finite G] in
theorem relIndex_pCoreOf_K1 (K1 : Subgroup G) :
    (pCoreOf 2 K1).relIndex K1 = Nat.card (OTwoQuot K1) := by
  have hP : (pCoreOf 2 K1).subgroupOf K1 = CFSG.Open.pCore 2 ↥K1 := by
    ext z
    rw [Subgroup.mem_subgroupOf]
    exact mem_pCoreOf_iff_mem_pCore z
  rw [Subgroup.relIndex, hP, Subgroup.index_eq_card]

theorem relIndex_isPow_two {K1 S : Subgroup G} (hS2 : IsPGroup 2 ↥S)
    (hN : K1 ⊔ S ≤ Subgroup.normalizer (K1 : Set G)) :
    ∃ a : ℕ, K1.relIndex (K1 ⊔ S) = 2 ^ a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hconj : ∀ s ∈ S, ∀ k ∈ K1, s * k * s⁻¹ ∈ K1 := fun s hs k hk =>
    (Subgroup.mem_normalizer_iff.mp (hN ((show S ≤ K1 ⊔ S from le_sup_right) hs)) k).mp hk
  have : (K1.subgroupOf (K1 ⊔ S)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hN
  let ψ : ↥S →* (↥(K1 ⊔ S) ⧸ K1.subgroupOf (K1 ⊔ S)) :=
    (QuotientGroup.mk' _).comp (Subgroup.inclusion (show S ≤ K1 ⊔ S from le_sup_right))
  have hψ : Function.Surjective ψ := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, hk, s, hs, hys⟩ := mem_sup_mul hN y.2
    refine ⟨⟨s, hs⟩, ?_⟩
    refine (QuotientGroup.eq).mpr ?_
    refine Subgroup.mem_subgroupOf.mpr ?_
    show (s⁻¹ : G) * (y : G) ∈ K1
    rw [hys]
    simpa [mul_assoc] using hconj s⁻¹ (S.inv_mem hs) k hk
  have hQ := hS2.of_surjective ψ hψ
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card (p := 2)).mp hQ
  refine ⟨a, ?_⟩
  rw [Subgroup.relIndex, Subgroup.index_eq_card]
  exact ha

end CFSG.Quasithin.Background.Harris.R1.S8Aux

namespace CFSG.Quasithin.Background.Harris.R1

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F7
open CFSG.GH74.Uniqueness.Bender S8Aux
open scoped commutatorElement

theorem s8_of_N2 {G : Type} [Group G] [Finite G]
    {K1 L2 S Zs : Subgroup G} (hset : R1SettingLegacyBare K1 L2 S Zs) (hL : IsL2Quot 3 (OTwoQuot K1))
    (hO : pCoreOf 2 (K1 ⊔ S) = pCoreOf 2 K1) : S ≤ K1 := by
  classical
  obtain ⟨e⟩ := hL
  have hB : BenderType (OTwoQuot K1) 3 1 1 := BenderType.linear 3 (by norm_num) e
  have hc : Subgroup.center (OTwoQuot K1) = ⊥ := hB.center_eq_bot
  have hS2 : IsPGroup 2 ↥S := hset.hyp.h1.pgroup
  have hN : K1 ⊔ S ≤ Subgroup.normalizer (K1 : Set G) :=
    sup_le Subgroup.le_normalizer hset.hyp.h1.normalizes
  have hY : Nat.card (OTwoQuot K1) = 504 := by
    rw [hB.card_eq]; norm_num
  have hOut : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer (OTwoQuot K1)) = 3 :=
    hB.outer_linear.2
  have hA : Nat.card (MulAut (OTwoQuot K1)) = 1512 := by
    rw [CFSG.GH74.GLS.Stage2.Bender.Thm1.CF67S.card_mulAut_eq_outer_mul hc, hY, hOut]
  have hfin : Finite (MulAut (OTwoQuot K1)) := Nat.finite_of_card_ne_zero (by rw [hA]; norm_num)
  let φ := conjOTwoQuot K1 (K1 ⊔ S) hN
  have hidx : Nat.card φ.range = 504 * K1.relIndex (K1 ⊔ S) := by
    rw [← Subgroup.index_ker, ker_eq_subgroupOf hc hS2 hN hO]
    have hrel := Subgroup.relIndex_mul_relIndex (hHK := pCoreOf_le 2 K1)
      (hKL := (le_sup_left : K1 ≤ K1 ⊔ S))
    rw [relIndex_pCoreOf_K1 K1, hY] at hrel
    exact hrel.symm
  have hdvd : 504 * K1.relIndex (K1 ⊔ S) ∣ 1512 := by
    rw [← hidx, ← hA]
    exact Subgroup.card_subgroup_dvd_card _
  have hdvd3 : K1.relIndex (K1 ⊔ S) ∣ 3 := by
    have : 504 * K1.relIndex (K1 ⊔ S) ∣ 504 * 3 := by simpa using hdvd
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
  obtain ⟨a, ha⟩ := relIndex_isPow_two hS2 hN
  have h1 : K1.relIndex (K1 ⊔ S) = 1 := by
    rw [ha] at hdvd3 ⊢
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd3 with h | h
    · rw [h]
    · exfalso
      rcases a with _ | _ | a
      · simp at h
      · simp at h
      · rw [pow_succ, pow_succ] at h
        omega
  exact (show S ≤ K1 ⊔ S from le_sup_right).trans (Subgroup.relIndex_eq_one.mp h1)

theorem s8_holds :
    ∀ (G : Type) [Group G] [Finite G] (K1 L2 S Zs : Subgroup G), R1SettingLegacyBare K1 L2 S Zs →
      (⁅vBeta K1 L2 S Zs, vBeta K1 L2 S Zs⁆ ≠ ⊥ →
        ∀ u ∈ S, u * u = 1 → (∀ s ∈ S, u * s = s * u) → u ∈ Zs) →
      IsL2Quot 3 (OTwoQuot K1) → S ≤ K1 := by
  intro G _ _ K1 L2 S Zs hset hZS hL
  have hna : ⁅vBeta K1 L2 S Zs, vBeta K1 L2 S Zs⁆ ≠ ⊥ :=
    r1b_vBeta_nonabelian rankOneListedFacts hset hL
  exact s8_of_N2 hset hL (n2Loc8_holds G K1 L2 S Zs hset (hZS hna) hL hna)

end CFSG.Quasithin.Background.Harris.R1

