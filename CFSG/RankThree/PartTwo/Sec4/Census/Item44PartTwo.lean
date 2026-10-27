module

import CFSG.RankThree.Coprime.InvolutionFixedRankBound
import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut
import CFSG.RankThree.PartTwo.NotationBlocks
import CFSG.LocalAnalysis.SectionRank.SQT
import CFSG.RankThree.Classical2.TwoLocalRankCoprimeQuotient
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44Gaps
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44Linear
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic
import CFSG.LocalAnalysis.SectionRank.SubgroupRank

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

open CFSG Matrix CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (localRank)
open scoped MatrixGroups

theorem pRank_le_localRank_of_centralizes {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {H : Subgroup G} {t : G} (ht : orderOf t = 2)
    (hHt : ∀ h ∈ H, h * t = t * h) : CFSG.pRank p H ≤ localRank p G := by
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top, ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
  refine csSup_le' ?_
  rintro k ⟨E, hEH, hE, hEk⟩
  have hcard : Nat.card (Subgroup.zpowers t) = 2 := by
    rw [Nat.card_zpowers, ht]
  refine CFSG.RankThree.Classical2.le_localRank_of_normalizes hp (D := Subgroup.zpowers t) ?_ hE
    hEk ?_ ?_
  · intro e he
    have hte : ∀ s ∈ Subgroup.zpowers t, e * s = s * e := by
      rintro _ ⟨n, rfl⟩
      exact (Commute.zpow_right (hHt e (hEH he) : Commute e t) n).eq
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rw [hte h hh, mul_inv_cancel_right]
      exact hh
    · intro hh
      have h2 := hte _ hh
      have hx : e⁻¹ * (e * h * e⁻¹) * e = e * h * e⁻¹ := by
        rw [mul_assoc e⁻¹, ← h2, ← mul_assoc, inv_mul_cancel, one_mul]
      have : h = e * h * e⁻¹ := by
        rw [← hx]
        group
      rw [this]
      exact hh
  · rw [hcard]
    exact (Nat.coprime_primes hp Nat.prime_two).mpr hp2
  · rw [hcard]

theorem twoRank_le_three {G : Type*} [Group G] [Finite G]
    (hlocal : ∀ q : ℕ, q.Prime → 3 < q → localRank q G < 3) {p : ℕ} [hp : Fact p.Prime]
    (hp3 : 3 < p) {D : Subgroup G} (hD : CriticalAt p D)
    (hodd : Odd (Nat.card (Subgroup.centralizer (D : Set G)))) :
    CFSG.Open.pRank 2 (⊤ : Subgroup G) ≤ 3 := by
  have : D.Normal := hD.normal
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨E, -, hE, hEcard⟩ :=
    CFSG.SectionRank.exists_pRank (by norm_num : 1 < 2) (⊤ : Subgroup G)
  set n := CFSG.Open.pRank 2 (⊤ : Subgroup G) with hn
  obtain ⟨eE⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2) (W := E)
    (fun a b => hE.1.is_comm.comm a b) (fun a => Subtype.ext (hE.2 a a.2)) hEcard
  set ι : Multiplicative (Fin n → ZMod 2) →* G := E.subtype.comp eE.symm.toMonoidHom with hιdef
  have hι : Function.Injective ι := Subtype.val_injective.comp eE.symm.injective
  let act : MulDistribMulAction (Multiplicative (Fin n → ZMod 2)) D :=
    MulDistribMulAction.compHom D ((MulAut.conjNormal : G →* MulAut D).comp ι)
  have hsmul : ∀ (a : Multiplicative (Fin n → ZMod 2)) (d : D),
      ((a • d : D) : G) = ι a * d * (ι a)⁻¹ := fun a d => rfl
  have hA2 : ∀ a : Multiplicative (Fin n → ZMod 2), a ^ 2 = 1 := by
    intro a
    obtain ⟨e, rfl⟩ := eE.surjective a
    rw [← map_pow, show e ^ 2 = 1 from Subtype.ext (hE.2 e e.2), map_one]
  have hfaith : FaithfulSMul (Multiplicative (Fin n → ZMod 2)) D := by
    refine ⟨fun {a₁ a₂} h => hι ?_⟩
    set c := (ι a₁)⁻¹ * ι a₂ with hc
    have hcD : c ∈ Subgroup.centralizer (D : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro d hd
      have h1 := congrArg Subtype.val (h ⟨d, hd⟩)
      rw [hsmul, hsmul] at h1
      calc d * c = (ι a₁)⁻¹ * (ι a₁ * d * (ι a₁)⁻¹) * ι a₂ := by rw [hc]; group
        _ = (ι a₁)⁻¹ * (ι a₂ * d * (ι a₂)⁻¹) * ι a₂ := by rw [h1]
        _ = c * d := by rw [hc]; group
    have hc2 : c ^ 2 = 1 := by
      rw [hc, ← map_inv, ← map_mul, ← map_pow, hA2, map_one]
    have h1 : orderOf c ∣ 2 := orderOf_dvd_of_pow_eq_one hc2
    have h2 : orderOf c ∣ Nat.card (Subgroup.centralizer (D : Set G)) := by
      rw [← Subgroup.orderOf_mk c hcD]
      exact orderOf_dvd_natCard _
    have h3 : orderOf c = 1 :=
      Nat.eq_one_of_dvd_coprimes ((Nat.coprime_two_left).mpr hodd) h1 h2
    rw [orderOf_eq_one_iff, hc, inv_mul_eq_one] at h3
    exact h3
  have hexp : Monoid.exponent D ∣ p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
    Subtype.ext (by rw [Subgroup.coe_pow, hD.exp x x.2, Subgroup.coe_one])
  have hclass : (⊤ : Subgroup D).lowerCentralSeries 2 = ⊥ := by
    rw [Subgroup.lowerCentralSeries_succ, Subgroup.top_lowerCentralSeries_one,
      Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.coe_top, Subgroup.centralizer_univ]
    exact hD.commutator_le_center
  have hm : ∀ a : Multiplicative (Fin n → ZMod 2), a ≠ 1 →
      CFSG.pRank p (CFSG.fixedPointSubgroup (Subgroup.zpowers a) D) ≤ 2 := by
    intro a ha
    set C := CFSG.fixedPointSubgroup (Subgroup.zpowers a) D
    have ht : orderOf (ι a) = 2 := orderOf_eq_prime (by rw [← map_pow, hA2, map_one])
      (fun h => ha (hι (by rw [h, map_one])))
    have hC : ∀ c ∈ C.map D.subtype, c * ι a = ι a * c := by
      rintro _ ⟨c, hc, rfl⟩
      have hfix : a • c = c := hc ⟨a, Subgroup.mem_zpowers a⟩
      have h1 := congrArg Subtype.val hfix
      rw [hsmul] at h1
      change (c : G) * ι a = ι a * c
      calc (c : G) * ι a = ι a * c * (ι a)⁻¹ * ι a := by rw [h1]
        _ = ι a * c := by group
    have h1 := pRank_le_localRank_of_centralizes hp.out (by omega) ht hC
    have h2 := hlocal p hp.out hp3
    rw [← CFSG.RankThree.PartTwo.pRank_congr_mulEquiv hp.out.one_lt
      (C.equivMapOfInjective D.subtype D.subtype_injective)] at h1
    omega
  have hA : Nat.card (Multiplicative (Fin n → ZMod 2)) = 2 ^ n := by
    rw [← Nat.card_congr eE.toEquiv, hEcard]
  have h2x : ∀ x : Additive (Multiplicative (Fin n → ZMod 2)), 2 • x = 0 := fun x => by
    rw [← ofMul_toMul x, ← ofMul_pow]
    exact (congrArg Additive.ofMul (hA2 (Additive.toMul x))).trans ofMul_one
  have hbound := (@CFSG.RankThree.Coprime.class_two_involution_fixed_rank_bound p hp
    (hp.out.odd_of_ne_two (by omega)) D _ _ (pCore_isPGroup.to_le hD.le) hexp hclass
    (Multiplicative (Fin n → ZMod 2)) _ _ (AddCommGroup.zmodModule (n := 2) h2x) n 2 hA act
    hfaith hm).1
  omega

theorem mk'_injective_of_pCore_two_eq_bot {G : Type*} [Group G] [(pCore 2 G).Normal]
    (hO2 : pCore 2 G = ⊥) : Function.Injective (QuotientGroup.mk' (pCore 2 G)) := by
  rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hO2]

theorem oTwoFitting_eq_of_pCore_two_eq_bot {G : Type*} [Group G] [Finite G]
    (hO2 : pCore 2 G = ⊥) : oTwoFitting G = fittingSubgroup G := by
  have : (pCore 2 G).Normal := pCore_normal
  set f := QuotientGroup.mk' (pCore 2 G)
  have hf : Function.Surjective f := QuotientGroup.mk'_surjective _
  have hinj := mk'_injective_of_pCore_two_eq_bot hO2
  apply le_antisymm
  ·
    refine le_sSup ⟨inferInstance, ?_⟩
    have hmap : (oTwoFitting G).map f ≤ fittingSubgroup (G ⧸ pCore 2 G) :=
      Subgroup.map_comap_le _ _
    have e := (oTwoFitting G).equivMapOfInjective f hinj
    have : Group.IsNilpotent ((oTwoFitting G).map f) := by
      exact Group.nilpotent_of_mulEquiv
        (MonoidHom.ofInjective (Subgroup.inclusion_injective hmap)).symm
    exact Group.nilpotent_of_mulEquiv e.symm
  · rw [oTwoFitting, ← Subgroup.map_le_iff_le_comap]
    refine le_sSup ⟨Subgroup.Normal.map inferInstance f hf, ?_⟩
    exact Group.nilpotent_of_surjective (f.subgroupMap (fittingSubgroup G))
      (f.subgroupMap_surjective _)

theorem oTwoP_eq_of_pCore_two_eq_bot {G : Type*} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (hO2 : pCore 2 G = ⊥) : oTwoP p G = pCore p G := by
  have : (pCore 2 G).Normal := pCore_normal
  set f := QuotientGroup.mk' (pCore 2 G)
  have hf : Function.Surjective f := QuotientGroup.mk'_surjective _
  have hinj := mk'_injective_of_pCore_two_eq_bot hO2
  apply le_antisymm
  · refine le_sSup ⟨inferInstance, ?_⟩
    exact (pCore_isPGroup : IsPGroup p (pCore p (G ⧸ pCore 2 G))).comap_of_injective f hinj
  · rw [oTwoP, ← Subgroup.map_le_iff_le_comap]
    exact le_sSup ⟨Subgroup.Normal.map pCore_normal f hf, pCore_isPGroup.map f⟩

theorem rank3II_4_4_partTwo (h2 : PartTwoRankTwo) (h3e : PartTwoRankThreeNotQuasisimple)
    (h3f : PartTwoRankThreeEndgame) {G : Type} [Group G] [Finite G] (hG : SectionFourHyp G)
    [hperf : Group.IsPerfect G] {K : Subgroup G} [K.Normal] (hK : Group.IsSolvable K)
    [hsimple : IsSimpleGroup (G ⧸ K)] (hO2 : pCore 2 G = ⊥) (h3K : ¬ 3 ∣ Nat.card K)
    (hq : ¬ IsQuasisimple G) :
    Nonempty (G ⧸ oTwoFitting G ≃* SL(2, ZMod 5)) ∨
      (∃ p : ℕ, p.Prime ∧ 3 < p ∧ Nonempty (G ⧸ oTwoP p G ≃* SL(2, ZMod p))) ∨
      ((CFSG.Open.pRank 2 (⊤ : Subgroup G) ≤ 2 ∧
          (IsQuasisimple (G ⧸ oddCore G) ∨
            IsExtOf (G ⧸ oddCore G) (alternatingGroup (Fin 5)) Q8D8)) ∨
        (CFSG.Open.pRank 2 (⊤ : Subgroup G) = 3 ∧
          (IsExtOf (G ⧸ oddCore G) (alternatingGroup (Fin 5)) Q8D8 ∨
            IsExtOf (G ⧸ oddCore G) (alternatingGroup (Fin 5)) Z4Q8Q8 ∨
            IsExtOf (G ⧸ oddCore G) (alternatingGroup (Fin 6)) Z4Q8Q8))) := by
  obtain ⟨p₀, hp₀, hS₀⟩ := exists_centralizer_pCore_le hK hq
  have hSp : ∀ p : ℕ, p.Prime → Subgroup.centralizer (pCore p G : Set G) ≤ K →
      3 < p ∧ pCore p G ≠ ⊥ := by
    intro p hp hpS
    have : Fact p.Prime := ⟨hp⟩
    have hne : pCore p G ≠ ⊥ := by
      intro h
      have htop : (⊤ : Subgroup G) ≤ Subgroup.centralizer (pCore p G : Set G) := by
        intro g _
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        rw [h] at hx
        rw [(Subgroup.mem_bot).mp hx, one_mul, mul_one]
      exact (QuotientGroup.nontrivial_iff.mp inferInstance) (top_le_iff.mp (htop.trans hpS))
    refine ⟨?_, hne⟩
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact hne hO2
    have hp3 : p ≠ 3 := by
      rintro rfl
      apply hne
      obtain ⟨k, hk⟩ := (pCore_isPGroup : IsPGroup 3 (pCore 3 G)).exists_card_eq
      have hdvd : 3 ^ k ∣ Nat.card K := hk ▸ Subgroup.card_dvd_of_le (pCore_le 3)
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · rw [pow_zero] at hk
        exact Subgroup.eq_bot_of_card_eq _ hk
      · exact absurd ((dvd_pow_self 3 hk0.ne').trans hdvd) h3K
    have := hp.two_le
    omega
  by_cases hO : ∃ p : ℕ, p.Prime ∧ 3 < p ∧ Subgroup.centralizer (pCore p G : Set G) ≤ K ∧
      ∃ D : Subgroup G, CriticalAt p D ∧ Odd (Nat.card (Subgroup.centralizer (D : Set G)))
  ·
    obtain ⟨p, hp, hp3, hpS, D, hD, hodd⟩ := hO
    have : Fact p.Prime := ⟨hp⟩
    have hm := twoRank_le_three hG.localRank_lt hp3 hD hodd
    right
    right
    rcases Nat.lt_or_ge (CFSG.Open.pRank 2 (⊤ : Subgroup G)) 3 with h | h
    · exact Or.inl ⟨by omega, h2 G hG hperf K hK hsimple h3K hO2 hq (by omega)⟩
    · have h3 : CFSG.Open.pRank 2 (⊤ : Subgroup G) = 3 := by omega
      have hyp : PartTwoRankThreeHyp G K :=
        ⟨hG, hperf, hK, hsimple, h3K, hO2, hq, h3, p, hp, hp3, hpS, D, hD, hodd⟩
      exact Or.inr ⟨h3, h3f G K hyp (h3e G K hyp)⟩
  ·
    push Not at hO
    have hlin : ∀ p : ℕ, p.Prime → Subgroup.centralizer (pCore p G : Set G) ≤ K →
        ∃ (N : Subgroup G) (_ : N.Normal), LinearOutcome G p N := by
      intro p hp hpS
      have : Fact p.Prime := ⟨hp⟩
      obtain ⟨hp3, hne⟩ := hSp p hp hpS
      obtain ⟨D, hD⟩ := exists_criticalAt (by omega) hne
      have heven := hO p hp hp3 hpS D hD
      rw [Nat.not_odd_iff_even] at heven
      obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.centralizer (D : Set G)) 2
        (even_iff_two_dvd.mp heven)
      have ht' : orderOf (t : G) = 2 := by rwa [Subgroup.orderOf_coe]
      have hrank := pRank_le_localRank_of_centralizes hp (by omega) ht'
        (fun h hh => Subgroup.mem_centralizer_iff.mp t.2 h hh)
      have := hG.localRank_lt p hp hp3
      exact linearOutcome_of_criticalAt hK hp3 hpS hD (by omega)
    rcases linear_endgame hK hO2 hp₀ hS₀ hlin with ⟨⟨e⟩⟩ | ⟨p, hp, hp3, ⟨e⟩⟩ | ⟨⟨e⟩⟩
    · exact Or.inl
        ⟨(QuotientGroup.quotientMulEquivOfEq (oTwoFitting_eq_of_pCore_two_eq_bot hO2)).trans e⟩
    · have : Fact p.Prime := ⟨hp⟩
      exact Or.inr (Or.inl ⟨p, hp, hp3,
        ⟨(QuotientGroup.quotientMulEquivOfEq (oTwoP_eq_of_pCore_two_eq_bot p hO2)).trans e⟩⟩)
    ·
      exfalso
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have hO3 : pCore 3 G = ⊥ := by
        obtain ⟨k, hk⟩ := (pCore_isPGroup : IsPGroup 3 (pCore 3 G)).exists_card_eq
        have hdvd : 3 ^ k ∣ Nat.card K := hk ▸ Subgroup.card_dvd_of_le (pCore_le 3)
        rcases Nat.eq_zero_or_pos k with rfl | hk0
        · rw [pow_zero] at hk
          exact Subgroup.eq_bot_of_card_eq _ hk
        · exact absurd ((dvd_pow_self 3 hk0.ne').trans hdvd) h3K
      have e' : G ≃* SL(3, ZMod 3) := (QuotientGroup.quotientBot.symm.trans
        (QuotientGroup.quotientMulEquivOfEq hO3.symm)).trans e
      exact hq (LocalCores.isQuasisimple_of_mulEquiv e'.symm isQuasisimple_SL3_three)

end CFSG.RankThree.PartTwo.Sec4.Census
