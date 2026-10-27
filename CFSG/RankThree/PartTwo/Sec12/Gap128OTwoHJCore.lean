module

public import CFSG.RankThree.PartTwo.Sec12.Gap128OTwoHJLinear
public import CFSG.RankThree.PartTwo.NotationBlocks
public import CFSG.RankThree.PartTwo.Sec3.AlternatingSLTwoLocalRank
public import CFSG.RankThree.PartTwo.KFacts.KS14MultJ2
import CFSG.RankThree.PartTwo.ExponentPrimeSmallRank
import CFSG.GroupTheory.ABGLocalTools.OddOrderLocal
import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44PartOne
import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.RankThree.PartTwo.Sec12.Gap128OTwoHJ

open CFSG CFSG.Blueprint CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4.Census (CriticalAt)
open scoped IsMulCommutative

theorem exists_frattiniModule {Y : Type} [Group Y] [Finite Y] {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) {D : Subgroup Y} (hD : CriticalAt p D) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V) (_ : FiniteDimensional (ZMod p) V)
      (ρ : Y →* Module.End (ZMod p) V),
      (∀ g, ρ g = 1 → g ∈ hD.frattiniKer) ∧
      CFSG.pRank p (D ⧸ frattini D) = Module.finrank (ZMod p) V ∧
      ∀ t : Y, t ^ 2 = 1 → CFSG.pRank p (fixedSubgroupOf (hD.conjD t)) ≤ 2 →
        Module.finrank (ZMod p) ((ρ t).eigenspace 1) ≤ 2 := by
  have hDp : IsPGroup p D := (pCore_isPGroup (p := p) (G := Y)).to_le hD.le
  have hexp : ∀ x : D, x ^ p = 1 := fun x => Subtype.ext (by
    rw [Subgroup.coe_pow, hD.exp x x.2, Subgroup.coe_one])
  obtain ⟨-, hVcomm, hVexp, hVelem, -, -, -⟩ := CFSG.GroupTheory.frattini_elementary_quotient hDp
  have : Finite (Additive (D ⧸ frattini D)) := inferInstanceAs (Finite (D ⧸ frattini D))
  have : FiniteDimensional (ZMod p) (Additive (D ⧸ frattini D)) := Module.Finite.of_finite
  let E : MulAut (D ⧸ frattini D) →* Module.End (ZMod p) (Additive (D ⧸ frattini D)) :=
    { toFun := fun σ => (MonoidHom.toAdditive σ.toMonoidHom).toZModLinearMap p
      map_one' := LinearMap.ext fun _ => rfl
      map_mul' := fun _ _ => LinearMap.ext fun _ => rfl }
  refine ⟨Additive (D ⧸ frattini D), inferInstance, inferInstance, inferInstance,
    E.comp hD.frattiniAct, fun g hg => ?_, ?_, fun t ht hrank => ?_⟩
  · rw [hD.mem_frattiniKer_iff]
    refine MulEquiv.ext fun x => ?_
    exact congrArg Additive.toMul (LinearMap.congr_fun hg (Additive.ofMul x))
  · have : Fintype (Additive (D ⧸ frattini D)) := Fintype.ofFinite _
    have hpow := Module.card_eq_pow_finrank (K := ZMod p) (V := Additive (D ⧸ frattini D))
    rw [ZMod.card, ← Nat.card_eq_fintype_card] at hpow
    exact pRank_eq_of_isMulCommutative hp.out hVexp hVcomm hpow
  · exact Sec3.finrank_eigenspace_le_two_of_pRank_le_two hp2 hDp hexp
      hD.commutator_le_center (σ := hD.conjD t) (by rw [← map_pow, ht, map_one]) hrank
      (E.comp hD.frattiniAct t) fun x =>
        congrArg Additive.ofMul
          (CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism_apply _ _ x)

theorem false_of_pRank_le_two {Y : Type} [Group Y] [Finite Y] (π : Y →* NativeSporadic.J2)
    (hπ : Function.Surjective π) {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {D : Subgroup Y}
    (hD : CriticalAt p D) (hDK : hD.frattiniKer ≤ π.ker) (hrank : CFSG.pRank p D ≤ 2) :
    False := by
  obtain ⟨V, _, _, _, ρ, hρ, hdim, -⟩ := exists_frattiniModule hp2 hD
  have hDp : IsPGroup p D := (pCore_isPGroup (p := p) (G := Y)).to_le hD.le
  have hexp : ∀ x : D, x ^ p = 1 := fun x => Subtype.ext (by
    rw [Subgroup.coe_pow, hD.exp x x.2, Subgroup.coe_one])
  have h1 := (class_two_small_rank_order_bounds hDp hexp hD.commutator_le_center).1 hrank
  have hfc := frattini_eq_commutator hDp hexp
  have h2 : CFSG.pRank p (D ⧸ frattini D) ≤ 2 := by
    rw [pRank_congr_mulEquiv hp.out.one_lt (QuotientGroup.quotientMulEquivOfEq hfc)]
    exact h1
  exact false_of_finrank_le_four π hπ (by omega) ρ fun g hg => hDK (hρ g hg)

theorem isSimpleGroup_quotient_ker {Y : Type} [Group Y]
    (π : Y →* NativeSporadic.J2) (hπ : Function.Surjective π) : IsSimpleGroup (Y ⧸ π.ker) :=
  @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.J2.isSimpleGroup_J2
    (QuotientGroup.quotientKerEquivOfSurjective π hπ)

theorem ker_ne_top {Y : Type} [Group Y]
    (π : Y →* NativeSporadic.J2) (hπ : Function.Surjective π) : π.ker ≠ ⊤ := by
  have := isSimpleGroup_quotient_ker π hπ
  exact QuotientGroup.nontrivial_iff.mp inferInstance

theorem exists_critical
    {Y : Type} [Group Y] [Finite Y] [hY : Group.IsPerfect Y]
    (π : Y →* NativeSporadic.J2) (hπ : Function.Surjective π) (hK : Group.IsSolvable π.ker)
    (h3 : ¬ 3 ∣ Nat.card π.ker) (hO2 : CFSG.pCore 2 Y = ⊥) (hne : π.ker ≠ ⊥) :
    ∃ p : ℕ, p.Prime ∧ 3 < p ∧ ∃ D : Subgroup Y, ∃ hD : CriticalAt p D,
      hD.frattiniKer ≤ π.ker := by
  have hs := isSimpleGroup_quotient_ker π hπ
  have htop := ker_ne_top π hπ
  by_cases hq : IsQuasisimple Y
  · exfalso
    obtain ⟨-, hZs, a, b, hab⟩ := hq
    have hKZ : π.ker ≤ Subgroup.center Y := by
      have hn : (π.ker.map (QuotientGroup.mk' (Subgroup.center Y))).Normal :=
        (MonoidHom.normal_ker π).map _ (QuotientGroup.mk'_surjective _)
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (π.ker.map (QuotientGroup.mk' (Subgroup.center Y))) with h | h
      · rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
      · have hsurj : Function.Surjective
            ((QuotientGroup.mk' (Subgroup.center Y)).comp π.ker.subtype) := by
          intro x
          have hx : x ∈ π.ker.map (QuotientGroup.mk' (Subgroup.center Y)) := by
            rw [h]
            trivial
          obtain ⟨k, hk, rfl⟩ := hx
          exact ⟨⟨k, hk⟩, rfl⟩
        have hsol : Group.IsSolvable (Y ⧸ Subgroup.center Y) :=
          Group.isSolvable_of_surjective hsurj
        exact absurd ((IsSimpleGroup.comm_iff_isSolvable).mpr hsol a b) hab
    have h2 : ¬ 2 ∣ Nat.card π.ker := by
      intro h2
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := π.ker) 2 h2
      have ht' : orderOf (t : Y) = 2 := by rw [Subgroup.orderOf_coe, ht]
      have hnorm : (Subgroup.zpowers (t : Y)).Normal :=
        Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr (hKZ t.2))
      have hpg : IsPGroup 2 (Subgroup.zpowers (t : Y)) :=
        IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht', pow_one])
      have hle : Subgroup.zpowers (t : Y) ≤ CFSG.pCore 2 Y := le_sSup ⟨hnorm, hpg⟩
      rw [hO2, le_bot_iff, Subgroup.zpowers_eq_bot] at hle
      rw [hle, orderOf_one] at ht'
      exact absurd ht' (by norm_num)
    have hcop : Nat.Coprime 6 (Nat.card π.ker) := by
      rw [show (6 : ℕ) = 2 * 3 by norm_num]
      exact Nat.Coprime.mul_left ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2)
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3)
    exact hne (KFacts.KS14.ks18Mult_j2 Y π.ker hY hKZ hcop
      ⟨QuotientGroup.quotientKerEquivOfSurjective π hπ⟩)
  · obtain ⟨p, hp, hpS⟩ := Sec4.Census.exists_centralizer_pCore_le hK hq
    have : Fact p.Prime := ⟨hp⟩
    have hPne : CFSG.pCore p Y ≠ ⊥ := by
      intro h
      apply htop
      refine top_le_iff.mp (le_trans (fun g _ => ?_) hpS)
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      rw [h, SetLike.mem_coe, Subgroup.mem_bot] at hx
      rw [hx, one_mul, mul_one]
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact hPne hO2
    have hp3 : p ≠ 3 := by
      rintro rfl
      apply hPne
      obtain ⟨k, hk⟩ := (pCore_isPGroup : IsPGroup 3 (CFSG.pCore 3 Y)).exists_card_eq
      have hdvd : 3 ^ k ∣ Nat.card π.ker := hk ▸ Subgroup.card_dvd_of_le (Sec4.Census.pCore_le 3)
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · rw [pow_zero] at hk
        exact Subgroup.eq_bot_of_card_eq _ hk
      · exact absurd ((dvd_pow_self 3 hk0.ne').trans hdvd) h3
    obtain ⟨D, hD⟩ := Sec4.Census.exists_criticalAt hp2 hPne
    exact ⟨p, hp, by have := hp.two_le; omega, D, hD, hD.frattiniKer_le hK hpS⟩

theorem ker_eq_bot_of_pRank_le_two
    {Y : Type} [Group Y] [Finite Y] [Group.IsPerfect Y]
    (π : Y →* NativeSporadic.J2) (hπ : Function.Surjective π) (hK : Group.IsSolvable π.ker)
    (h3 : ¬ 3 ∣ Nat.card π.ker) (hO2 : CFSG.pCore 2 Y = ⊥)
    (hrank : ∀ p : ℕ, p.Prime → 3 < p → CFSG.pRank p Y ≤ 2) : π.ker = ⊥ := by
  by_contra hne
  obtain ⟨p, hp, hp3, D, hD, hDK⟩ := exists_critical π hπ hK h3 hO2 hne
  have : Fact p.Prime := ⟨hp⟩
  have hDr : CFSG.pRank p D ≤ 2 := by
    have h1 := Sec4.Census.pRank_le_pRank_top hp D
    rw [← CFSG.SectionRank.pRank_eq_open_pRank_top] at h1
    exact h1.trans (hrank p hp hp3)
  exact false_of_pRank_le_two π hπ (by omega) hD hDK hDr

theorem ker_le_pCore_two_of_pRank_le_two
    {Y : Type} [Group Y] [Finite Y]
    [Group.IsPerfect Y] (π : Y →* NativeSporadic.J2) (hπ : Function.Surjective π)
    (hK : Group.IsSolvable π.ker) (h3 : ¬ 3 ∣ Nat.card π.ker)
    (hrank : ∀ p : ℕ, p.Prime → 3 < p → CFSG.pRank p Y ≤ 2) : π.ker ≤ CFSG.pCore 2 Y := by
  have hs := isSimpleGroup_quotient_ker π hπ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := CFSG.pCore 2 Y with hQ
  have : Q.Normal := pCore_normal
  have hQK : Q ≤ π.ker := Sec4.Census.pCore_le 2
  set π' : Y ⧸ Q →* NativeSporadic.J2 := QuotientGroup.lift Q π hQK with hπ'def
  have hπ' : Function.Surjective π' := by
    intro y
    obtain ⟨x, rfl⟩ := hπ y
    exact ⟨QuotientGroup.mk x, rfl⟩
  have hker' : π'.ker = π.ker.map (QuotientGroup.mk' Q) := QuotientGroup.ker_lift Q π hQK
  have hK' : Group.IsSolvable π'.ker := by
    rw [hker']
    exact Group.isSolvable_of_surjective ((QuotientGroup.mk' Q).subgroupMap_surjective π.ker)
  have h3' : ¬ 3 ∣ Nat.card π'.ker := by
    rw [hker']
    exact fun h => h3 (h.trans (Subgroup.card_map_dvd _ _))
  have hO2' : CFSG.pCore 2 (Y ⧸ Q) = ⊥ := CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot
  have hrank' : ∀ p : ℕ, p.Prime → 3 < p → CFSG.pRank p (Y ⧸ Q) ≤ 2 := by
    intro p hp hp3
    have : Fact p.Prime := ⟨hp⟩
    have hQp : ¬ p ∣ Nat.card Q := by
      obtain ⟨k, hk⟩ := (pCore_isPGroup : IsPGroup 2 Q).exists_card_eq
      rw [hk]
      intro h
      have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h)
      omega
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top, CFSG.SectionRank.pRank_quotient_eq Q hQp,
      ← CFSG.SectionRank.pRank_eq_open_pRank_top]
    exact hrank p hp hp3
  have hbot := ker_eq_bot_of_pRank_le_two π' hπ' hK' h3' hO2' hrank'
  rw [hker', Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
  exact hbot

end CFSG.RankThree.PartTwo.Sec12.Gap128OTwoHJ
