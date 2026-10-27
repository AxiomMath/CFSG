module

public import CFSG.LocalAnalysis.WeakClosure81.NineThreeHyp
public import CFSG.LocalAnalysis.WeakClosure81.NineTwoF

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {V T A K S X : Subgroup G} {p : ℕ}

theorem Nine3Seed.card (h763 : SevenSixThreeAbelian V) (h : Nine3Seed V T A K S X p)
    {Y : Subgroup G} (hY : Nine3Fam K S X A Y)
    (hmin : ∀ Y' : Subgroup G, Nine3Fam K S X A Y' → Y' ≤ Y → Y' = Y)
    (h1 : ¬ normalizer (E3.wClos V 1 T : Set G) ≤ normalizer (V : Set G)) :
    Nat.card ↥Y = p := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact p.Prime := ⟨h.two.prime⟩
  have hyp : Nine2Hyp V (S ⊔ Y) S Y p := h.hyp hY hmin h1
  have hcyc : IsCyclic ↥Y := nine_two_four h763 h.h9.hyp7 h.h9.rk_gt hyp
  have hYp : IsPGroup p Y := h.two.sylowP.isPGroup.to_le hY.1
  have hY1 : Y ≠ ⊥ := by
    rintro rfl
    exact hY.2.2 bot_le
  obtain ⟨a, haA, haR⟩ := SetLike.not_le_iff_exists.1 (h.not_le_pCoreOf hY)
  have hAS : A ≤ S := nineThree_A_le_S h.h9 h.conj h.leT h.tau
  have hAΩ : A ∈ nineOmegaIn V (S ⊔ Y) S :=
    ((nine_two_one h.h9.hyp7 h.h9.rk_gt hyp).2 A h.conj hAS).resolve_right h.ne
  have hSY : S ⊔ Y ≤ K := sup_le h.two.sylowTwo.le (hY.1.trans h.two.sylowP.le)
  have hRle : pCoreOf 2 K ≤ pCoreOf 2 (S ⊔ Y) := by
    have hRS : pCoreOf 2 K ≤ S := h.two.pCoreOf_le_sylowTwo
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hRS.trans le_sup_left)
      (hSY.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K))
      (h.two.sylowTwo.isPGroup.to_le hRS)
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥Y)
  have hordg : orderOf g = Nat.card ↥Y := orderOf_eq_card_of_forall_mem_zpowers hg
  have hYcard1 : Nat.card ↥Y ≠ 1 := by
    intro hc
    exact hY1 (Subgroup.eq_bot_of_card_eq Y hc)
  let y₀ : G := (g : G)
  let Z : Subgroup G := Subgroup.zpowers (y₀ ^ p)
  have hy₀p : y₀ ^ p ∈ Y := Y.pow_mem g.2 p
  have hZY : Z ≤ Y := Subgroup.zpowers_le.mpr hy₀p
  have hZτ : Z ≤ E1.tauOf K K A := by
    by_contra hZτ
    have hZfam : Nine3Fam K S X A Z := by
      refine ⟨hZY.trans hY.1, ?_, hZτ⟩
      intro s hs z hz
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      have hsy : s * y₀ * s⁻¹ ∈ Y := hY.2.1 s hs y₀ g.2
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨s * y₀ * s⁻¹, hsy⟩)
      have hj' : y₀ ^ j = s * y₀ * s⁻¹ := congrArg Subtype.val hj
      refine Subgroup.mem_zpowers_iff.mpr ⟨j * k, ?_⟩
      have e1 : ((s * y₀ * s⁻¹) ^ p) ^ k = s * (y₀ ^ p) ^ k * s⁻¹ := by
        rw [conj_pow, conj_zpow]
      have e2 : ((y₀ ^ j) ^ p) ^ k = (y₀ ^ p) ^ (j * k) := by group
      rw [← e1, ← hj', e2]
    have hZeq : Z = Y := hmin Z hZfam hZY
    have hy₀Z : y₀ ∈ Z := hZeq ▸ g.2
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy₀Z
    obtain ⟨c, hc⟩ := hYp.exists_card_eq
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact hYcard1 (by simpa using hc)
    have hpc : (p : ℤ) ∣ (Nat.card ↥Y : ℤ) := by
      rw [hc]
      exact_mod_cast dvd_pow_self p hc0
    have hmul : y₀ ^ ((p : ℤ) * k) = y₀ := by
      rw [zpow_mul, zpow_natCast]
      exact hk
    have hzg : g ^ ((p : ℤ) * k - 1) = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_zpow, zpow_sub, zpow_one, Subgroup.coe_one]
      show y₀ ^ ((p : ℤ) * k) * y₀⁻¹ = 1
      rw [hmul, mul_inv_cancel]
    have hdvd : (Nat.card ↥Y : ℤ) ∣ (p : ℤ) * k - 1 := by
      rw [← hordg]
      exact orderOf_dvd_iff_zpow_eq_one.mpr hzg
    have hp1 : (p : ℤ) ∣ 1 := by
      have h2 := hpc.trans hdvd
      have h3 : (p : ℤ) ∣ (p : ℤ) * k := dvd_mul_right _ _
      simpa using Int.dvd_sub h3 h2
    have hp1' : p ∣ 1 := by exact_mod_cast hp1
    exact h.two.prime.one_lt.ne' (Nat.dvd_one.mp hp1')
  have hy : y₀ ^ p ∈ E1.tauOf K K A := hZτ (Subgroup.mem_zpowers _)
  have hycomm : ∀ a' ∈ A, ⁅y₀ ^ p, a'⁆ ∈ pCoreOf 2 K := fun a' ha' =>
    (E1.mem_tauOf.mp hy).2.2 a' ha'
  have hinv := nine_two_inv h.h9.hyp7 h.h9.rk_gt hyp hAΩ haA haR hy₀p
  have hc2 : ⁅y₀ ^ p, a⁆ ∈ pCoreOf 2 (S ⊔ Y) := hRle (hycomm a haA)
  have hyy : (y₀ ^ p) * (y₀ ^ p) ∈ pCoreOf 2 (S ⊔ Y) := by
    have e : (y₀ ^ p) * (y₀ ^ p) =
        ⁅y₀ ^ p, a⁆ * (a * (y₀ ^ p) * a⁻¹ * (y₀ ^ p)) := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact (pCoreOf 2 (S ⊔ Y)).mul_mem hc2 hinv
  have hbot : Y ⊓ pCoreOf 2 (S ⊔ Y) = ⊥ :=
    TwoPTwo.sylowP_inf_pCoreOf hyp.base.toTwoPTwoIrred.toTwoPTwo
  have hyy1 : (y₀ ^ p) * (y₀ ^ p) = 1 := by
    have hmem : (y₀ ^ p) * (y₀ ^ p) ∈ Y ⊓ pCoreOf 2 (S ⊔ Y) :=
      ⟨Y.mul_mem hy₀p hy₀p, hyy⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hmem
  have hy1 : y₀ ^ p = 1 := by
    obtain ⟨n, hn⟩ := hYp ⟨y₀ ^ p, hy₀p⟩
    have hn' : (y₀ ^ p) ^ p ^ n = 1 := by simpa using congrArg Subtype.val hn
    have h2 : orderOf (y₀ ^ p) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hyy1)
    have h3 : orderOf (y₀ ^ p) ∣ p ^ n := orderOf_dvd_of_pow_eq_one hn'
    have hcop : Nat.Coprime 2 (p ^ n) :=
      ((Nat.coprime_primes Nat.prime_two h.two.prime).2 (Ne.symm h.two.odd)).pow_right n
    have h4 : orderOf (y₀ ^ p) ∣ 1 := by
      simpa [Nat.Coprime.gcd_eq_one hcop] using Nat.dvd_gcd h2 h3
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h4)
  have hgp : g ^ p = 1 := Subtype.ext (by simpa using hy1)
  have hdvd : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one hgp
  rw [← hordg]
  rcases (Nat.dvd_prime h.two.prime).mp hdvd with h2 | h2
  · exact absurd (hordg.symm.trans h2) hYcard1
  · exact h2

end CFSG.LocalAnalysis.WeakClosure81
