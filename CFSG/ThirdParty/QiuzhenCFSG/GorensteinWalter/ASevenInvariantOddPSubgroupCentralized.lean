module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ASevenInvariantOddPSubgroupCertificateDefs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Classification
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CentralizerNormalizerConjugateMap
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ASevenFixedCyclicThreeCertificate
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ASevenFixedCyclicFiveCertificate
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ASevenFixedCyclicSevenCertificate
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ASevenNoOrderNineNormalizedCertificate
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ASevenCubeEqOneOfPowNine
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

namespace CFSG.GorensteinWalter

private theorem a7CentralizerGenerators_commute :
    ∀ c ∈ a7CentralizerGenerators, c * a7t = a7t * c := by
  intro c hc
  simp [a7CentralizerGenerators] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> decide

private abbrev A7 := ASevenCertificateGroup

private theorem a7t_involution : IsInvolution a7t := by
  unfold IsInvolution
  constructor <;> decide

private lemma aSeven_involution_cycleType
    (x : A7) (hx : IsInvolution x) :
    (x : Equiv.Perm (Fin 7)).cycleType = {2, 2} := by
  let g : Equiv.Perm (Fin 7) := x
  have hgpow : g ^ 2 = 1 := congrArg Subtype.val hx.2
  have htypes : ∀ n, n ∈ Equiv.Perm.cycleType g → n = 2 :=
    Equiv.Perm.pow_prime_eq_one_iff.mp hgpow
  rw [← Multiset.eq_replicate_card] at htypes
  have hsupport := g.support.card_le_univ
  rw [← Equiv.Perm.sum_cycleType, htypes, Multiset.sum_replicate,
    smul_eq_mul] at hsupport
  norm_num at hsupport
  have hcard : Multiset.card g.cycleType ≤ 3 := by omega
  have hsign : Equiv.Perm.sign g = 1 :=
    Equiv.Perm.mem_alternatingGroup.mp x.property
  rw [Equiv.Perm.sign_of_cycleType, htypes] at hsign
  simp at hsign
  rw [pow_add, pow_mul, Int.units_pow_two, one_mul,
    neg_one_pow_eq_one_iff_even] at hsign
  swap
  · decide
  interval_cases h : Multiset.card g.cycleType
  · exfalso
    apply hx.1
    apply Subtype.ext
    exact Equiv.Perm.card_cycleType_eq_zero.mp h
  · simp at hsign
  · simpa [g, h] using htypes
  · contradiction

public theorem aSeven_involutions_conjugate
    (x y : ASevenCertificateGroup)
    (hx : IsInvolution x) (hy : IsInvolution y) :
    ∃ g : ASevenCertificateGroup, g * x * g⁻¹ = y := by
  have hcx := aSeven_involution_cycleType x hx
  have hcy := aSeven_involution_cycleType y hy
  have hcPerm : IsConj (x : Equiv.Perm (Fin 7))
      (y : Equiv.Perm (Fin 7)) :=
    Equiv.Perm.isConj_iff_cycleType_eq.mpr (hcx.trans hcy.symm)
  have hsupp :
      (x : Equiv.Perm (Fin 7)).support.card + 2 ≤ Fintype.card (Fin 7) := by
    rw [← Equiv.Perm.sum_cycleType, hcx]
    decide
  have hc := alternatingGroup.isConj_of hcPerm hsupp
  exact isConj_iff.mp hc

private lemma card_aSeven : Nat.card A7 = 2520 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card]
  decide

public lemma odd_prime_eq_three_five_or_seven_of_dvd_2520
    {p : ℕ} (hp : p.Prime) (hpodd : Odd p) (hpdvd : p ∣ 2520) :
    p = 3 ∨ p = 5 ∨ p = 7 := by
  have hfactor : 2520 = 2 ^ 3 * (3 ^ 2 * (5 * 7)) := by norm_num
  rw [hfactor] at hpdvd
  rcases (hp.dvd_mul.mp hpdvd) with htwo | hrest
  · have hp2 : p = 2 := Nat.prime_eq_prime_of_dvd_pow hp Nat.prime_two htwo
    subst p
    exact False.elim (hpodd.not_two_dvd_nat (by norm_num))
  rcases (hp.dvd_mul.mp hrest) with hthree | hrest
  · exact Or.inl (Nat.prime_eq_prime_of_dvd_pow hp Nat.prime_three hthree)
  rcases (hp.dvd_mul.mp hrest) with hfive | hseven
  · rcases (Nat.dvd_prime Nat.prime_five).mp hfive with hp1 | hp5
    · exact False.elim (hp.ne_one hp1)
    · exact Or.inr (Or.inl hp5)
  · rcases (Nat.dvd_prime Nat.prime_seven).mp hseven with hp1 | hp7
    · exact False.elim (hp.ne_one hp1)
    · exact Or.inr (Or.inr hp7)

private lemma fixedSpanPow_of_mem_zpowers
    {q : ℕ} (hq : 0 < q) {x z : A7} (hx : x ^ q = 1)
    (hz : z ∈ Subgroup.zpowers x) : fixedSpanPow q x z := by
  rcases Subgroup.mem_zpowers_iff.mp hz with ⟨k, hk⟩
  have hqint : (q : ℤ) ≠ 0 := by omega
  have hnonneg : 0 ≤ k % (q : ℤ) := Int.emod_nonneg _ hqint
  have hlt : k % (q : ℤ) < (q : ℤ) := Int.emod_lt_of_pos _ (by omega)
  let i : Fin q := ⟨Int.toNat (k % (q : ℤ)), by
    rw [Int.toNat_lt hnonneg]
    exact hlt⟩
  refine ⟨i, ?_⟩
  rw [← hk, zpow_eq_zpow_emod' k hx]
  rw [← zpow_natCast]
  exact congrArg (x ^ ·) (Int.toNat_of_nonneg hnonneg).symm

private theorem card_sup_eq_mul_of_disjoint_of_le_normalizer
    {G : Type*} [Group G] (A B : Subgroup G)
    (hnormal : B ≤ Subgroup.normalizer (A : Set G))
    (hdisjoint : Disjoint A B) :
    Nat.card (A ⊔ B : Subgroup G) = Nat.card A * Nat.card B := by
  let toSup : A × B → ↥(A ⊔ B) := fun z =>
    ⟨(z.1 : G) * (z.2 : G), Subgroup.mul_mem_sup z.1.2 z.2.2⟩
  have hinjective : Function.Injective toSup := by
    intro x y hxy
    apply Subgroup.mul_injective_of_disjoint hdisjoint
    exact congrArg Subtype.val hxy
  have hsurjective : Function.Surjective toSup := by
    intro z
    have hz : (z : G) ∈ (A : Set G) * (B : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left A B hnormal]
      exact z.2
    rcases hz with ⟨a, ha, b, hb, hab⟩
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩
  calc
    Nat.card (A ⊔ B : Subgroup G) = Nat.card (A × B) :=
      Nat.card_congr (Equiv.ofBijective toSup ⟨hinjective, hsurjective⟩).symm
    _ = Nat.card A * Nat.card B := Nat.card_prod A B

private theorem disjoint_of_ne_of_card_eq_prime
    {G : Type*} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    {L K : Subgroup G} (hLcard : Nat.card L = p)
    (hKcard : Nat.card K = p) (hne : L ≠ K) : Disjoint L K := by
  rw [disjoint_iff]
  let I : Subgroup G := L ⊓ K
  have hIleL : I ≤ L := inf_le_left
  let IL : Subgroup L := I.subgroupOf L
  let : Fact (Nat.Prime (Nat.card L)) :=
    ⟨hLcard ▸ (Fact.out : Nat.Prime p)⟩
  change I = ⊥
  rcases IL.eq_bot_or_eq_top_of_prime_card with hbot | htop
  · apply le_antisymm
    · intro x hxI
      let xL : L := ⟨x, hIleL hxI⟩
      have hxIL : xL ∈ IL := hxI
      rw [hbot] at hxIL
      exact Subgroup.mem_bot.mpr
        (congrArg Subtype.val (Subgroup.mem_bot.mp hxIL))
    · exact bot_le
  · exfalso
    apply hne
    have hLK : L ≤ K :=
      (Subgroup.subgroupOf_eq_top.mp htop).trans inf_le_right
    apply Subgroup.eq_of_le_of_card_ge hLK
    rw [hLcard, hKcard]

private theorem aSeven_fixed_invariant_oddP_subgroup_centralized
    (p : ℕ) (hp : p.Prime) (hpodd : Odd p)
    (P : Subgroup A7) (hPp : IsPGroup p P)
    (hPinv : Subgroup.centralizer ({a7t} : Set A7) ≤
      Subgroup.normalizer (P : Set A7)) :
    P ≤ Subgroup.centralizer ({a7t} : Set A7) := by
  classical
  have hgenNorm : ∀ c ∈ a7CentralizerGenerators,
      c ∈ Subgroup.normalizer (P : Set A7) := by
    intro c hc
    apply hPinv
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact a7CentralizerGenerators_commute c hc
  have hcyclic : ∀ (q : ℕ), q.Prime → Nat.card P = q →
      (∀ x : A7,
        (x ≠ 1 ∧ x ^ q = 1 ∧
          ∀ c ∈ a7CentralizerGenerators,
            fixedSpanPow q x (c * x * c⁻¹)) →
        a7t * x = x * a7t) →
      P ≤ Subgroup.centralizer ({a7t} : Set A7) := by
    intro q hq hPcard hcertificate
    let : Fact q.Prime := ⟨hq⟩
    obtain ⟨xP, hxPorder⟩ :=
      exists_prime_orderOf_dvd_card' (G := P) q (by rw [hPcard])
    let x : A7 := xP
    have hxorder : orderOf x = q := by
      simpa [x, Subgroup.orderOf_coe] using hxPorder
    have hxne : x ≠ 1 := by
      intro hxone
      have : q = 1 := by rw [← hxorder, hxone, orderOf_one]
      exact hq.ne_one this
    have hxpow : x ^ q = 1 := by
      rw [← hxorder]
      exact pow_orderOf_eq_one x
    have hZle : Subgroup.zpowers x ≤ P :=
      Subgroup.zpowers_le.mpr xP.property
    have hZcard : Nat.card (Subgroup.zpowers x) = q := by
      rw [Nat.card_zpowers, hxorder]
    have hZeq : Subgroup.zpowers x = P := by
      apply Subgroup.eq_of_le_of_card_ge hZle
      rw [hZcard, hPcard]
    have hspans : ∀ c ∈ a7CentralizerGenerators,
        fixedSpanPow q x (c * x * c⁻¹) := by
      intro c hc
      have hconjP : c * x * c⁻¹ ∈ P :=
        (Subgroup.mem_normalizer_iff.mp (hgenNorm c hc) x).mp xP.property
      have hconjZ : c * x * c⁻¹ ∈ Subgroup.zpowers x := by
        rwa [hZeq]
      exact fixedSpanPow_of_mem_zpowers hq.pos hxpow hconjZ
    have htx : a7t * x = x * a7t :=
      hcertificate x ⟨hxne, hxpow, hspans⟩
    rw [← hZeq]
    exact Subgroup.zpowers_le.mpr
      (Subgroup.mem_centralizer_singleton_iff.mpr htx.symm)
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hPcard⟩ := hPp.exists_card_eq
  have hpowDvd : p ^ n ∣ 2520 := by
    rw [← card_aSeven, ← hPcard]
    exact Subgroup.card_subgroup_dvd_card P
  by_cases hnzero : n = 0
  · have hcardOne : Nat.card P = 1 := by simpa [hnzero] using hPcard
    have hPbot : P = ⊥ := Subgroup.eq_bot_of_card_eq (H := P) hcardOne
    rw [hPbot]
    exact bot_le
  have hnpos : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hnzero
  have hpDvd : p ∣ 2520 :=
    (dvd_pow_self p (Nat.ne_of_gt hnpos)).trans hpowDvd
  rcases odd_prime_eq_three_five_or_seven_of_dvd_2520 hp hpodd hpDvd with
      hp3 | hp5 | hp7
  · subst p
    have hnle : n ≤ 2 := by
      by_contra hn
      have hthree : 3 ≤ n := by omega
      have hbad : 27 ∣ 2520 := by
        exact (pow_dvd_pow 3 hthree).trans hpowDvd
      norm_num at hbad
    interval_cases n
    · apply hcyclic 3 Nat.prime_three (by simpa using hPcard)
      intro x hx
      exact a7_fixed_cyclic_three_certificate x
        ⟨hx.1, hx.2.1,
          hx.2.2 a7v (by simp [a7CentralizerGenerators])⟩
    · have hPnine : Nat.card P = 9 := by simpa using hPcard
      let : IsMulCommutative P := by
        apply IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3)
        simpa using hPnine
      have hPindex : P.index = 280 := by
        have hmul := P.card_mul_index
        rw [hPnine, card_aSeven] at hmul
        omega
      have hPnotIndex : ¬ 3 ∣ P.index := by
        rw [hPindex]
        norm_num
      have haNe : a7a ≠ 1 := by decide
      have haPow : a7a ^ 3 = 1 := by decide
      have haOrder : orderOf a7a = 3 :=
        orderOf_eq_prime haPow haNe
      let A : Subgroup A7 := Subgroup.zpowers a7a
      have hAcard : Nat.card A = 3 := by
        rw [Nat.card_zpowers, haOrder]
      have hAp : IsPGroup 3 A := by
        apply IsPGroup.of_card (n := 1)
        simpa using hAcard
      have haNorm : a7a ∈ Subgroup.normalizer (P : Set A7) :=
        hgenNorm a7a (by simp [a7CentralizerGenerators])
      have hAnormP : A ≤ Subgroup.normalizer (P : Set A7) :=
        Subgroup.zpowers_le.mpr haNorm
      have hsupP : IsPGroup 3 (P ⊔ A : Subgroup A7) :=
        IsPGroup.to_sup_of_normal_left' hPp hAp hAnormP
      let S : Sylow 3 A7 := hPp.toSylow hPnotIndex
      have hsupLeP : P ⊔ A ≤ P := by
        have hle : P ⊔ A ≤ (S : Subgroup A7) :=
          le_of_eq (S.is_maximal' hsupP le_sup_left)
        simpa [S, IsPGroup.toSylow_coe] using hle
      have hAleP : A ≤ P :=
        (le_sup_right : A ≤ P ⊔ A).trans hsupLeP
      have haP : a7a ∈ P := hAleP (Subgroup.mem_zpowers a7a)
      have hPnotA : ¬ P ≤ A := by
        intro hle
        have hdvd := Subgroup.card_dvd_of_le hle
        rw [hPnine, hAcard] at hdvd
        norm_num at hdvd
      obtain ⟨x, hxP, hxA⟩ := SetLike.not_le_iff_exists.mp hPnotA
      have hxne : x ≠ 1 := by
        intro hxone
        subst x
        exact hxA A.one_mem
      have hx9 : x ^ 9 = 1 := by
        apply orderOf_dvd_iff_pow_eq_one.mp
        have hdvd := Subgroup.orderOf_dvd_natCard P hxP
        rwa [hPnine] at hdvd
      have hxpow : x ^ 3 = 1 := a7_cube_eq_one_of_pow_nine x hx9
      have hxorder : orderOf x = 3 := orderOf_eq_prime hxpow hxne
      have hxa : x * a7a = a7a * x := by
        exact congrArg Subtype.val
          ((IsMulCommutative.is_comm (M := P)).comm ⟨x, hxP⟩ ⟨a7a, haP⟩)
      have hxneA : x ≠ a7a := by
        intro hxaEq
        subst x
        exact hxA (Subgroup.mem_zpowers a7a)
      have hxneA2 : x ≠ a7a ^ 2 := by
        intro hxaEq
        subst x
        exact hxA (Subgroup.pow_mem A (Subgroup.mem_zpowers a7a) 2)
      let X : Subgroup A7 := Subgroup.zpowers x
      have hXle : X ≤ P := Subgroup.zpowers_le.mpr hxP
      have hXcard : Nat.card X = 3 := by
        rw [Nat.card_zpowers, hxorder]
      have hXAne : X ≠ A := by
        intro hXA
        apply hxA
        rw [← hXA]
        exact Subgroup.mem_zpowers x
      have hdisjoint : Disjoint X A :=
        disjoint_of_ne_of_card_eq_prime 3 hXcard hAcard hXAne
      have hAnormX : A ≤ Subgroup.normalizer (X : Set A7) := by
        intro z hzA
        apply Subgroup.centralizer_le_normalizer (X : Set A7)
        rw [Subgroup.mem_centralizer_iff]
        intro w hwX
        have hzP : z ∈ P := hAleP hzA
        exact (congrArg Subtype.val
          ((IsMulCommutative.is_comm (M := P)).comm ⟨z, hzP⟩
            ⟨w, hXle hwX⟩)).symm
      have hjoinCard : Nat.card (X ⊔ A : Subgroup A7) = 9 := by
        rw [card_sup_eq_mul_of_disjoint_of_le_normalizer X A hAnormX hdisjoint,
          hXcard, hAcard]
      have hjoinLe : X ⊔ A ≤ P := sup_le hXle hAleP
      have hjoinEq : X ⊔ A = P := by
        apply Subgroup.eq_of_le_of_card_ge hjoinLe
        rw [hjoinCard, hPnine]
      have hspanOfMem : ∀ {z : A7}, z ∈ X ⊔ A → fixedSpanThree x a7a z := by
        intro z hz
        have hzprod : z ∈ (X : Set A7) * (A : Set A7) := by
          rw [← Subgroup.coe_mul_of_right_le_normalizer_left X A hAnormX]
          exact hz
        rcases hzprod with ⟨zx, hzx, zy, hzy, hprod⟩
        obtain ⟨i, hi⟩ := fixedSpanPow_of_mem_zpowers (q := 3)
          (by norm_num) hxpow hzx
        obtain ⟨j, hj⟩ := fixedSpanPow_of_mem_zpowers (q := 3)
          (by norm_num) haPow hzy
        exact ⟨i, j, hprod.symm.trans (congrArg₂ (· * ·) hi hj)⟩
      have htNorm : a7t ∈ Subgroup.normalizer (P : Set A7) :=
        hgenNorm a7t (by simp [a7CentralizerGenerators])
      have htSpan : fixedSpanThree x a7a (a7t * x * a7t⁻¹) := by
        apply hspanOfMem
        rw [hjoinEq]
        exact (Subgroup.mem_normalizer_iff.mp htNorm x).mp hxP
      let x3 : A7OrderThree := ⟨x, hxne, hxpow⟩
      exact (a7_no_order_nine_normalized_by_t_certificate x3
        ⟨hxa, hxneA, hxneA2, htSpan⟩).elim
  · subst p
    have hnle : n ≤ 1 := by
      by_contra hn
      have htwo : 2 ≤ n := by omega
      have hbad : 25 ∣ 2520 := by
        exact (pow_dvd_pow 5 htwo).trans hpowDvd
      norm_num at hbad
    have hnone : n = 1 := by omega
    apply hcyclic 5 Nat.prime_five (by simpa [hnone] using hPcard)
    intro x hx
    exact a7_fixed_cyclic_five_certificate x
      ⟨hx.1, hx.2.1,
        hx.2.2 a7a (by simp [a7CentralizerGenerators])⟩
  · subst p
    have hnle : n ≤ 1 := by
      by_contra hn
      have htwo : 2 ≤ n := by omega
      have hbad : 49 ∣ 2520 := by
        exact (pow_dvd_pow 7 htwo).trans hpowDvd
      norm_num at hbad
    have hnone : n = 1 := by omega
    apply hcyclic 7 Nat.prime_seven (by simpa [hnone] using hPcard)
    intro x hx
    exact a7_fixed_cyclic_seven_certificate x
      ⟨hx.1, hx.2.1,
        hx.2.2 a7t (by simp [a7CentralizerGenerators])⟩

/-- An odd-prime subgroup of `A₇` normalized by an involution centralizer
is centralized by that involution. -/
public theorem aSeven_invariant_oddP_subgroup_centralized
    (p : ℕ) (hp : p.Prime) (hpodd : Odd p)
    (P : Subgroup ASevenCertificateGroup) (hPp : IsPGroup p P)
    {t : ASevenCertificateGroup}
    (ht : IsInvolution t)
    (hPinv : Subgroup.centralizer ({t} : Set ASevenCertificateGroup) ≤
      Subgroup.normalizer (P : Set ASevenCertificateGroup)) :
    P ≤ Subgroup.centralizer ({t} : Set ASevenCertificateGroup) := by
  classical
  obtain ⟨g, hgt⟩ := aSeven_involutions_conjugate t a7t ht a7t_involution
  let e : A7 ≃* A7 := MulAut.conj g
  let P0 : Subgroup A7 := P.map e.toMonoidHom
  have hP0p : IsPGroup p P0 := IsPGroup.map hPp e.toMonoidHom
  have hP0inv : Subgroup.centralizer ({a7t} : Set A7) ≤
      Subgroup.normalizer (P0 : Set A7) := by
    exact centralizer_le_normalizer_map_conj_of_eq_conj P hgt hPinv
  have hP0cent : P0 ≤ Subgroup.centralizer ({a7t} : Set A7) :=
    aSeven_fixed_invariant_oddP_subgroup_centralized
      p hp hpodd P0 hP0p hP0inv
  intro x hxP
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hxP0 : e x ∈ P0 :=
    Subgroup.mem_map.mpr ⟨x, hxP, rfl⟩
  have hxcomm : e x * a7t = a7t * e x :=
    Subgroup.mem_centralizer_singleton_iff.mp (hP0cent hxP0)
  apply e.injective
  simpa [map_mul, e, hgt] using hxcomm

end CFSG.GorensteinWalter
