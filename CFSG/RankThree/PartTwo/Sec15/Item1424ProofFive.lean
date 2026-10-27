module

import CFSG.RankThree.PartTwo.Sec16.Item16TailEnd
import CFSG.RankThree.PartTwo.Sec3.Item38
import CFSG.RankThree.Classical2.TwoLocalRankCoprimeQuotient
import CFSG.GroupTheory.ABGLocalTools.OddOrderLocal
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerOddAvg
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LieType.BorelTits.Basic
public import CFSG.RankThree.PartTwo.Setup

public section

namespace CFSG.RankThree.PartTwo.Sec15.Proof1424

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (localRank)
open scoped commutatorElement Pointwise

theorem isElemAbelian_map1424 {M M' : Type*} [Group M] [Group M'] {p : ℕ} {E : Subgroup M}
    (hE : CFSG.Assembly.IsElemAbelian p E) (φ : M →* M') :
    CFSG.Assembly.IsElemAbelian p (E.map φ) := CFSG.Open.IsElemAbelian.map hE _

theorem eq_bot_or_eq_of_commutator_eq {Γ : Type*} [Group Γ] [Finite Γ] {A E F : Subgroup Γ}
    (hA3 : IsPGroup 3 A) (hE : CFSG.Assembly.IsElemAbelian 5 E) (hE25 : Nat.card E = 25)
    (hAE : A ≤ Subgroup.normalizer (E : Set Γ)) (hEA : E = ⁅E, A⁆) (hFE : F ≤ E)
    (hAF : A ≤ Subgroup.normalizer (F : Set Γ)) : F = ⊥ ∨ F = E := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdvd : Nat.card F ∣ 5 ^ 2 := by
    rw [show (5 : ℕ) ^ 2 = 25 by norm_num, ← hE25]
    exact Subgroup.card_dvd_of_le hFE
  obtain ⟨k, hk, hFk⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 5)).mp hdvd
  interval_cases k
  · left
    rw [pow_zero] at hFk
    exact Subgroup.eq_bot_of_card_eq F hFk
  · exfalso
    rw [pow_one] at hFk
    have hFc : IsCyclic F := isCyclic_of_prime_card hFk
    have hAut : Nat.card (MulAut F) = 4 := by
      rw [IsCyclic.card_mulAut F, hFk]
      decide
    set φ : A →* MulAut F := F.normalizerMonoidHom.comp (Subgroup.inclusion hAF) with hφ
    have hφ1 : ∀ a : A, φ a = 1 := by
      intro a
      obtain ⟨m, hm⟩ := hA3 a
      have h1 : orderOf (φ a) ∣ 3 ^ m :=
        orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hm, map_one])
      have h2 : orderOf (φ a) ∣ 4 := hAut ▸ orderOf_dvd_natCard (φ a)
      have h3 : Nat.gcd (3 ^ m) 4 = 1 := Nat.Coprime.pow_left m (by norm_num)
      have h4 := Nat.dvd_gcd h1 h2
      rw [h3, Nat.dvd_one] at h4
      exact orderOf_eq_one_iff.mp h4
    have hFC : F ≤ E ⊓ Subgroup.centralizer (A : Set Γ) := by
      refine le_inf hFE fun x hx => Subgroup.mem_centralizer_iff.mpr fun a ha => ?_
      have h1 := congrArg (fun σ : MulAut F => ((σ ⟨x, hx⟩ : F) : Γ)) (hφ1 ⟨a, ha⟩)
      simp only [hφ, MonoidHom.comp_apply, MulAut.one_apply] at h1
      have h2 : a * x * a⁻¹ = x := h1
      calc a * x = a * x * a⁻¹ * a := by group
        _ = x * a := by rw [h2]
    have hab : ∀ x y : E, x * y = y * x := fun x y => hE.1.is_comm.comm x y
    have hcop : Nat.Coprime (Nat.card A) (Nat.card E) := by
      obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hA3
      rw [hm, hE25, show (25 : ℕ) = 5 ^ 2 by norm_num]
      exact Nat.Coprime.pow m 2 (by norm_num)
    obtain ⟨-, hdisj⟩ := CFSG.QuasithinUnique.Setup.Layer.coprime_abelian_decomp E A hAE hab hcop
    rw [← hEA] at hdisj
    have hbot : E ⊓ Subgroup.centralizer (A : Set Γ) = ⊥ :=
      le_bot_iff.mp (hdisj le_rfl inf_le_left)
    have hF1 : F = ⊥ := le_bot_iff.mp (hbot ▸ hFC)
    rw [hF1, Subgroup.card_bot] at hFk
    omega
  · right
    exact Subgroup.eq_of_le_of_card_ge hFE (by rw [hE25, hFk]; norm_num)

theorem commutator_le_of_le1424 {Γ : Type*} [Group Γ] {X Y N : Subgroup Γ} (hX : X ≤ N)
    (hY : Y ≤ N) : ⁅X, Y⁆ ≤ N := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem (hX ha) (hY hb)) (inv_mem (hX ha))) (inv_mem (hY hb))

theorem false_of_commutator_action_five {Γ : Type} [Group Γ] [Finite Γ]
    (hloc : ∀ r : ℕ, r.Prime → 3 < r → localRank r Γ < 3) {q : ℕ} (hq : q.Prime) (hq3 : 3 < q)
    {A E U Q : Subgroup Γ} (hA3 : IsPGroup 3 A) (hE : CFSG.Assembly.IsElemAbelian 5 E)
    (hE25 : Nat.card E = 25) (hU2 : IsPGroup 2 U) (hUE : ⁅U, E⁆ = U)
    (hEU : E ≤ Subgroup.normalizer (U : Set Γ)) (hQ : IsPGroup q Q)
    (hUQ : U ≤ Subgroup.normalizer (Q : Set Γ)) (hEQ : E ≤ Subgroup.normalizer (Q : Set Γ))
    (hAQ : A ≤ Subgroup.normalizer (Q : Set Γ)) (hAU : A ≤ Subgroup.normalizer (U : Set Γ))
    (hAE : A ≤ Subgroup.normalizer (E : Set Γ)) (hEA : E = ⁅E, A⁆)
    (hUC : ¬ U ≤ Subgroup.centralizer (Q : Set Γ)) : False := by
  classical
  have : Fact q.Prime := ⟨hq⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := U ⊓ Subgroup.centralizer (Q : Set Γ) with hK
  set N := Subgroup.normalizer (K : Set Γ) with hN
  have hKU : K ≤ U := inf_le_left
  have hK2 : IsPGroup 2 K := hU2.to_le hKU
  have hCN : ∀ {Y : Subgroup Γ}, Y ≤ Subgroup.normalizer (U : Set Γ) →
      Y ≤ Subgroup.normalizer (Q : Set Γ) → Y ≤ N := fun h1 h2 =>
    (le_inf h1 (h2.trans (Sec16.Proof169.normalizer_le_normalizer_centralizer Q))).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hUN : U ≤ N := hCN Subgroup.le_normalizer hUQ
  have hEN : E ≤ N := hCN hEU hEQ
  have hAN : A ≤ N := hCN hAU hAQ
  have hQN : Q ≤ N :=
    (Subgroup.le_centralizer_iff.mp (inf_le_right : K ≤ _)).trans
      (Subgroup.centralizer_le_normalizer _)
  set K' : Subgroup ↥N := K.subgroupOf N with hK'
  set π := QuotientGroup.mk' K' with hπ
  set U' := (U.subgroupOf N).map π with hU'
  set E' := (E.subgroupOf N).map π with hE'
  set Q' := (Q.subgroupOf N).map π with hQ'
  set A' := (A.subgroupOf N).map π with hA'
  have hcop2 : ∀ {r : ℕ}, r.Prime → r ≠ 2 → Nat.Coprime r (Nat.card K) := by
    intro r hr hr2
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hK2
    rw [hk]
    exact Nat.Coprime.pow_right k ((Nat.coprime_primes hr Nat.prime_two).mpr hr2)
  have hK'card : Nat.card K' = Nat.card K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.le_normalizer : K ≤ N)).toEquiv
  have hlocq : localRank q (↥N ⧸ K') < 3 := by
    have hqK : ¬ q ∣ Nat.card K' := by
      rw [hK'card]
      exact (Nat.Prime.coprime_iff_not_dvd hq).mp (hcop2 hq (by omega))
    exact ((Classical2.localRank_quotient_le hq (by omega) K' hqK).trans
      (localRank_subgroup_le hq N)).trans_lt (hloc q hq hq3)
  have hcommap : ∀ {X Y : Subgroup Γ}, X ≤ N → Y ≤ N →
      ⁅(X.subgroupOf N).map π, (Y.subgroupOf N).map π⁆ = (⁅X, Y⁆.subgroupOf N).map π := by
    intro X Y hX hY
    rw [← Subgroup.map_commutator]
    congr 1
    apply Subgroup.map_injective N.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hX,
      Subgroup.map_subgroupOf_eq_of_le hY,
      Subgroup.map_subgroupOf_eq_of_le (commutator_le_of_le1424 hX hY)]
  have hmapN : ∀ {X Y : Subgroup Γ}, X ≤ Subgroup.normalizer (Y : Set Γ) →
      (X.subgroupOf N).map π ≤
        Subgroup.normalizer (((Y.subgroupOf N).map π : Subgroup (↥N ⧸ K')) : Set (↥N ⧸ K')) :=
    fun h => (Subgroup.map_mono (Sec16.Proof169.subgroupOf_le_normalizer_subgroupOf h)).trans
      (Subgroup.le_normalizer_map π)
  have hEK : E ⊓ K = ⊥ := (Subgroup.disjoint_of_coprime_natCard (by
    rw [hE25, show (25 : ℕ) = 5 ^ 2 by norm_num]
    exact Nat.Coprime.pow_left 2 (hcop2 (by norm_num) (by norm_num)))).eq_bot
  have hinj : Function.Injective (π.comp (E.subgroupOf N).subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxK : ((x : ↥N) : Γ) ∈ K := by
      have : (x : ↥N) ∈ K' := (QuotientGroup.eq_one_iff _).mp hx
      exact Subgroup.mem_subgroupOf.mp this
    have hxE : ((x : ↥N) : Γ) ∈ E := Subgroup.mem_subgroupOf.mp x.2
    have h1 : ((x : ↥N) : Γ) ∈ E ⊓ K := ⟨hxE, hxK⟩
    rw [hEK, Subgroup.mem_bot] at h1
    exact Subtype.ext (Subtype.ext h1)
  have hE'card : Nat.card E' = 25 := by
    have hE'eq : E' = (π.comp (E.subgroupOf N).subtype).range := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [hE'eq, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEN).toEquiv, hE25]
  have hE'e : CFSG.Assembly.IsElemAbelian 5 E' := by
    have hEs : CFSG.Assembly.IsElemAbelian 5 (E.subgroupOf N) := by
      have hcomm : ∀ y ∈ E, ∀ z ∈ E, y * z = z * y := fun y hy z hz =>
        congrArg Subtype.val (hE.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
      refine ⟨⟨⟨fun y z => Subtype.ext (Subtype.ext ?_)⟩⟩, fun y hy => ?_⟩
      · exact hcomm _ (Subgroup.mem_subgroupOf.mp y.2) _ (Subgroup.mem_subgroupOf.mp z.2)
      · exact Subtype.ext (by simpa using hE.2 _ (Subgroup.mem_subgroupOf.mp hy))
    exact isElemAbelian_map1424 hEs π
  have hE'1 : E' ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at hE'card
    omega
  have hU'2 : IsPGroup 2 U' := (hU2.comap_subtype (K := N)).map π
  have hQ'q : IsPGroup q Q' := (hQ.comap_subtype (K := N)).map π
  have hA'3 : IsPGroup 3 A' := (hA3.comap_subtype (K := N)).map π
  have hU'E' : ⁅U', E'⁆ = U' := by rw [hcommap hUN hEN, hUE]
  have hE'A' : E' = ⁅E', A'⁆ := by rw [hcommap hEN hAN, ← hEA]
  have hE'U' : E' ≤ Subgroup.normalizer (U' : Set (↥N ⧸ K')) := hmapN hEU
  have hU'Q' : U' ≤ Subgroup.normalizer (Q' : Set (↥N ⧸ K')) := hmapN hUQ
  have hE'Q' : E' ≤ Subgroup.normalizer (Q' : Set (↥N ⧸ K')) := hmapN hEQ
  have hA'U' : A' ≤ Subgroup.normalizer (U' : Set (↥N ⧸ K')) := hmapN hAU
  have hA'E' : A' ≤ Subgroup.normalizer (E' : Set (↥N ⧸ K')) := hmapN hAE
  have hU'1 : U' ≠ ⊥ := by
    intro hbot
    apply hUC
    rw [hU', Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
    intro u hu
    have hmem : (⟨u, hUN hu⟩ : ↥N) ∈ K' := hbot (Subgroup.mem_subgroupOf.mpr hu)
    exact (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hmem)).2
  have hQU : Q ⊓ U = ⊥ := (Subgroup.disjoint_of_coprime_natCard (by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQ
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hU2
    rw [hk, hm]
    exact Nat.Coprime.pow k m ((Nat.coprime_primes hq Nat.prime_two).mpr (by omega)))).eq_bot
  have hfaith : U' ⊓ Subgroup.centralizer (Q' : Set (↥N ⧸ K')) = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨⟨u, hu, rfl⟩, hc⟩
    rw [Subgroup.mem_bot]
    have huU : (u : Γ) ∈ U := Subgroup.mem_subgroupOf.mp hu
    have huC : (u : Γ) ∈ Subgroup.centralizer (Q : Set Γ) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have hzN : z ∈ N := hQN hz
      have h1 := Subgroup.mem_centralizer_iff.mp hc (π ⟨z, hzN⟩)
        ⟨⟨z, hzN⟩, Subgroup.mem_subgroupOf.mpr hz, rfl⟩
      have h2 : (⟨z, hzN⟩ * u : ↥N)⁻¹ * (u * ⟨z, hzN⟩) ∈ K' := by
        rw [← QuotientGroup.eq, QuotientGroup.mk_mul, QuotientGroup.mk_mul]
        exact h1
      have h3 : ((⟨z, hzN⟩ * u : ↥N)⁻¹ * (u * ⟨z, hzN⟩) : ↥N).1 ∈ K :=
        Subgroup.mem_subgroupOf.mp h2
      have hval : ((⟨z, hzN⟩ * u : ↥N)⁻¹ * (u * ⟨z, hzN⟩) : ↥N).1 =
          (u : Γ)⁻¹ * z⁻¹ * (u : Γ) * z := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev]
        group
      rw [hval] at h3
      have h4 : (u : Γ)⁻¹ * z⁻¹ * (u : Γ) * z ∈ Q := by
        have h5 : (u : Γ)⁻¹ * z⁻¹ * (u : Γ) ∈ Q := by
          have := (Subgroup.mem_normalizer_iff.mp (hUQ (inv_mem huU)) z⁻¹).mp (inv_mem hz)
          simpa using this
        exact mul_mem h5 hz
      have h6 : (u : Γ)⁻¹ * z⁻¹ * (u : Γ) * z ∈ Q ⊓ U := ⟨h4, hKU h3⟩
      rw [hQU, Subgroup.mem_bot] at h6
      have h7 : (u : Γ) * z = z * (u : Γ) := by
        calc (u : Γ) * z = z * (u : Γ) * ((u : Γ)⁻¹ * z⁻¹ * (u : Γ) * z) := by group
          _ = z * (u : Γ) := by rw [h6, mul_one]
      exact h7.symm
    exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr ⟨huU, huC⟩)
  have hEf : E' ⊓ Subgroup.centralizer (U' : Set (↥N ⧸ K')) = ⊥ := by
    have hAF : A' ≤ Subgroup.normalizer
        ((E' ⊓ Subgroup.centralizer (U' : Set (↥N ⧸ K')) : Subgroup (↥N ⧸ K')) :
          Set (↥N ⧸ K')) :=
      (le_inf hA'E' (hA'U'.trans (Sec16.Proof169.normalizer_le_normalizer_centralizer U'))).trans
        Subgroup.inf_normalizer_le_normalizer_inf
    rcases eq_bot_or_eq_of_commutator_eq hA'3 hE'e hE'card hA'E' hE'A' inf_le_left hAF with
      h | h
    · exact h
    · exfalso
      apply hU'1
      have hEC : E' ≤ Subgroup.centralizer (U' : Set (↥N ⧸ K')) := h ▸ inf_le_right
      rw [← hU'E']
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.le_centralizer_iff.mp hEC)
  have hEUN : E' ⊔ U' ≤ Subgroup.normalizer (U' : Set (↥N ⧸ K')) :=
    sup_le hE'U' Subgroup.le_normalizer
  have hESf : (E' ⊔ U') ⊓ Subgroup.centralizer (Q' : Set (↥N ⧸ K')) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨hzEU, hzC⟩ := Subgroup.mem_inf.mp hz
    have hzEU' : z ∈ (E' : Set (↥N ⧸ K')) * (U' : Set (↥N ⧸ K')) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right E' U' hE'U']
      exact hzEU
    obtain ⟨e, he, u, hu, rfl⟩ := hzEU'
    beta_reduce at hzEU hzC ⊢
    have hzU : e * u ∈ Subgroup.centralizer (U' : Set (↥N ⧸ K')) := by
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have hw1 : e * u * v * (e * u)⁻¹ * v⁻¹ ∈ U' :=
        mul_mem ((Subgroup.mem_normalizer_iff.mp (hEUN hzEU) v).mp hv) (inv_mem hv)
      have hvC : v * (e * u)⁻¹ * v⁻¹ ∈ Subgroup.centralizer (Q' : Set (↥N ⧸ K')) :=
        (Subgroup.mem_normalizer_iff.mp (Sec16.Proof169.normalizer_le_normalizer_centralizer Q'
          (hU'Q' hv)) _).mp (inv_mem hzC)
      have hw2 : e * u * v * (e * u)⁻¹ * v⁻¹ ∈ Subgroup.centralizer (Q' : Set (↥N ⧸ K')) := by
        have e1 : e * u * v * (e * u)⁻¹ * v⁻¹ = (e * u) * (v * (e * u)⁻¹ * v⁻¹) := by group
        rw [e1]
        exact mul_mem hzC hvC
      have hw : e * u * v * (e * u)⁻¹ * v⁻¹ = 1 := by
        have h1 : e * u * v * (e * u)⁻¹ * v⁻¹ ∈
            U' ⊓ Subgroup.centralizer (Q' : Set (↥N ⧸ K')) := ⟨hw1, hw2⟩
        rw [hfaith, Subgroup.mem_bot] at h1
        exact h1
      calc v * (e * u) = (e * u * v * (e * u)⁻¹ * v⁻¹)⁻¹ * (e * u * v) := by group
        _ = e * u * v := by rw [hw, inv_one, one_mul]
    have huz : Commute (e * u) u := (Subgroup.mem_centralizer_iff.mp hzU u hu).symm
    have he5 : e ^ 5 = 1 := hE'e.2 e he
    have hu5 : u ^ 5 ∈ Subgroup.centralizer (U' : Set (↥N ⧸ K')) := by
      have h2 : ((e * u) * u⁻¹) ^ 5 = (e * u) ^ 5 * u⁻¹ ^ 5 := huz.inv_right.mul_pow 5
      rw [show (e * u) * u⁻¹ = e by group, he5, inv_pow] at h2
      have h3 : u ^ 5 = (e * u) ^ 5 := (mul_inv_eq_one.mp h2.symm).symm
      rw [h3]
      exact pow_mem hzU 5
    obtain ⟨k, hk⟩ := hU'2 ⟨u, hu⟩
    have hord : orderOf u ∣ 2 ^ k :=
      orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
    have hgcd : Nat.gcd 5 (orderOf u) = 1 :=
      Nat.Coprime.coprime_dvd_right hord (Nat.Coprime.pow_right k (by norm_num))
    have huC : u ∈ Subgroup.centralizer (U' : Set (↥N ⧸ K')) :=
      Subgroup.zpowers_le.mpr hu5 (mem_zpowers_pow_iff.mpr hgcd)
    have heC : e ∈ Subgroup.centralizer (U' : Set (↥N ⧸ K')) := by
      rw [show e = (e * u) * u⁻¹ by group]
      exact mul_mem hzU (inv_mem huC)
    have he1 : e = 1 := by
      have h1 : e ∈ E' ⊓ Subgroup.centralizer (U' : Set (↥N ⧸ K')) := ⟨he, heC⟩
      rw [hEf, Subgroup.mem_bot] at h1
      exact h1
    rw [he1, one_mul] at hzC ⊢
    have h1 : u ∈ U' ⊓ Subgroup.centralizer (Q' : Set (↥N ⧸ K')) := ⟨hu, hzC⟩
    rwa [hfaith] at h1
  have h38 := Sec3.rank3II_3_8 (p := 5) (q := q) (by norm_num) hq (by norm_num) hq3 hE'e hE'1
    hU'2 hQ'q hE'U' hEf (sup_le hE'Q' hU'Q') hESf (fun _ => hE'card.ge)
  omega

theorem le_pCoreOf_two_of_commutator_action_five {Γ₀ : Type} [Group Γ₀] [Finite Γ₀]
    (hloc : ∀ r : ℕ, r.Prime → 3 < r → localRank r Γ₀ < 3) {A N U E : Subgroup Γ₀}
    (hNn : N.Normal) (hNs : Group.IsSolvable N) (hN3 : ¬ 3 ∣ Nat.card N)
    (hU2 : IsPGroup 2 U) (hUN : U ≤ N) (hE : CFSG.Assembly.IsElemAbelian 5 E)
    (hE25 : Nat.card E = 25) (hEU : E ≤ Subgroup.normalizer (U : Set Γ₀)) (hUE : ⁅U, E⁆ = U)
    (hA3 : IsPGroup 3 A) (hAU : A ≤ Subgroup.normalizer (U : Set Γ₀))
    (hAE : A ≤ Subgroup.normalizer (E : Set Γ₀)) (hEA : E = ⁅E, A⁆) :
    U ≤ CFSG.Open.pCoreOf 2 N := by
  by_contra hU
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O₂ := CFSG.Open.pCoreOf 2 N with hO₂
  have hO₂n : O₂.Normal := by
    have h := CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 N
    rw [Subgroup.normalizer_eq_top_iff.mpr hNn, top_le_iff,
      Subgroup.normalizer_eq_top_iff] at h
    exact h
  have hO₂2 : IsPGroup 2 O₂ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N
  set π := QuotientGroup.mk' O₂ with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective O₂
  have hlocΓ : ∀ r : ℕ, r.Prime → 3 < r → localRank r (Γ₀ ⧸ O₂) < 3 := by
    intro r hr hr3
    have hr2 : r ≠ 2 := by omega
    have hrP : ¬ r ∣ Nat.card O₂ := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hO₂2
      rw [hk]
      intro h
      exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h))
    exact (Classical2.localRank_quotient_le hr hr2 O₂ hrP).trans_lt (hloc r hr hr3)
  set N₁ := N.map π with hN₁
  have hN₁s : Group.IsSolvable N₁ := Group.isSolvable_of_surjective (π.subgroupMap_surjective N)
  have hN₁3 : ¬ 3 ∣ Nat.card N₁ := fun h => hN3 (h.trans (Subgroup.card_map_dvd N π))
  have hO2₁ : CFSG.pCore 2 ↥N₁ = ⊥ := by
    obtain ⟨η, -⟩ := exists_quotient_mulEquiv_map π N (CFSG.pCore 2 ↥N) fun l => by
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hO₂, CFSG.Open.pCoreOf]
      constructor
      · intro h
        exact ⟨l, h, rfl⟩
      · rintro ⟨x, hx, hxl⟩
        have : x = l := Subtype.ext hxl
        rwa [← this]
    have h1 := CFSG.pCore_map_iso 2 η
    rw [ABGLocalTools.pCore_quotient_pCore_eq_bot, Subgroup.map_bot] at h1
    exact h1.symm
  have hU₁1 : U.map π ≠ ⊥ := by
    intro h
    apply hU
    rw [Subgroup.map_eq_bot_iff, hπ, QuotientGroup.ker_mk'] at h
    exact h
  have hU₁2 : IsPGroup 2 (U.map π) := hU2.map π
  obtain ⟨r, hr, hr3, hrU⟩ := Sec16.Proof169.exists_prime_not_le_centralizer_pCore hN₁s hN₁3
    hO2₁ (Subgroup.map_mono hUN) hU₁2 hU₁1
  have : Fact r.Prime := ⟨hr⟩
  set Q₁ := (CFSG.pCore r ↥N₁).map N₁.subtype with hQ₁
  have hQ₁r : IsPGroup r Q₁ := CFSG.pCore_isPGroup.map _
  have hN₁n : N₁.Normal := hNn.map π hπs
  have hNQ : ∀ H : Subgroup (Γ₀ ⧸ O₂), H ≤ Subgroup.normalizer (Q₁ : Set (Γ₀ ⧸ O₂)) := by
    intro H
    have : (CFSG.pCore r ↥N₁).Characteristic := inferInstance
    have h := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (H := N₁) (CFSG.pCore r ↥N₁)
    rw [Subgroup.normalizer_eq_top_iff.mpr hN₁n] at h
    exact le_top.trans h
  have hEO : E ⊓ O₂ = ⊥ := (Subgroup.disjoint_of_coprime_natCard (by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hO₂2
    rw [hE25, hk, show (25 : ℕ) = 5 ^ 2 by norm_num]
    exact Nat.Coprime.pow 2 k (by norm_num))).eq_bot
  have hinj : Function.Injective (π.comp E.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxO : (x : Γ₀) ∈ O₂ := (QuotientGroup.eq_one_iff _).mp hx
    have h1 : (x : Γ₀) ∈ E ⊓ O₂ := ⟨x.2, hxO⟩
    rw [hEO, Subgroup.mem_bot] at h1
    exact Subtype.ext h1
  have hE₁card : Nat.card (E.map π) = 25 := by
    have hE'eq : E.map π = (π.comp E.subtype).range := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [hE'eq, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, hE25]
  exact false_of_commutator_action_five hlocΓ hr hr3 (hA3.map π) (isElemAbelian_map1424 hE π)
    hE₁card hU₁2 (by rw [← Subgroup.map_commutator, hUE])
    ((Subgroup.map_mono hEU).trans (Subgroup.le_normalizer_map π)) hQ₁r (hNQ _) (hNQ _) (hNQ _)
    ((Subgroup.map_mono hAU).trans (Subgroup.le_normalizer_map π))
    ((Subgroup.map_mono hAE).trans (Subgroup.le_normalizer_map π))
    (by rw [← Subgroup.map_commutator, ← hEA]) hrU

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem pCoreOf_subgroupOf_map {N M : Subgroup G} (hNM : N ≤ M) :
    (CFSG.Open.pCoreOf 2 (N.subgroupOf M)).map M.subtype = CFSG.Open.pCoreOf 2 N := by
  set e := Subgroup.subgroupOfEquivOfLe hNM
  have hcomp : M.subtype.comp (N.subgroupOf M).subtype = N.subtype.comp e.toMonoidHom := by
    ext x
    rfl
  rw [CFSG.Open.pCoreOf, CFSG.Open.pCoreOf, Subgroup.map_map, hcomp, ← Subgroup.map_map,
    CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 e]

end CFSG.RankThree.PartTwo.Sec15.Proof1424

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (localRank)
open scoped commutatorElement

theorem step1424Five :
    ∀ (G : Type) [Group G] [Finite G], (∀ r : ℕ, r.Prime → 3 < r → localRank r G < 3) →
      ∀ A N U E : Subgroup G, Group.IsSolvable N → ¬ 3 ∣ Nat.card N → IsPGroup 2 U → U ≤ N →
        E ≤ N → CFSG.Assembly.IsElemAbelian 5 E → Nat.card E = 25 →
        E ≤ Subgroup.normalizer (U : Set G) → ⁅U, E⁆ = U → IsPGroup 3 A →
        A ≤ Subgroup.normalizer (N : Set G) → A ≤ Subgroup.normalizer (U : Set G) →
        A ≤ Subgroup.normalizer (E : Set G) → E = ⁅E, A⁆ → U ≤ CFSG.Open.pCoreOf 2 N := by
  intro G _ _ hloc A N U E hNs hN3 hU2 hUN hEN hE hE25 hEU hUE hA3 hAN hAU hAE hEA
  set M := Subgroup.normalizer (N : Set G) with hM
  have hNM : N ≤ M := Subgroup.le_normalizer
  have hUM : U ≤ M := hUN.trans hNM
  have hEM : E ≤ M := hEN.trans hNM
  have hlocM : ∀ r : ℕ, r.Prime → 3 < r → localRank r M < 3 := fun r hr hr3 =>
    (localRank_subgroup_le hr M).trans_lt (hloc r hr hr3)
  have hNn : (N.subgroupOf M).Normal := Subgroup.normal_in_normalizer
  have hNs' : Group.IsSolvable (N.subgroupOf M) :=
    Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hNM).symm.toMonoidHom)
      (MulEquiv.surjective _)
  have hN3' : ¬ 3 ∣ Nat.card (N.subgroupOf M) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNM).toEquiv]
  have hcomm : ∀ y ∈ E, ∀ z ∈ E, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  have hE' : CFSG.Assembly.IsElemAbelian 5 (E.subgroupOf M) := by
    refine ⟨⟨⟨fun y z => Subtype.ext (Subtype.ext ?_)⟩⟩, fun y hy => ?_⟩
    · exact hcomm _ (Subgroup.mem_subgroupOf.mp y.2) _ (Subgroup.mem_subgroupOf.mp z.2)
    · exact Subtype.ext (by simpa using hE.2 _ (Subgroup.mem_subgroupOf.mp hy))
  have hE25' : Nat.card (E.subgroupOf M) = 25 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEM).toEquiv, hE25]
  have hcommap : ∀ {X Y : Subgroup G}, X ≤ M → Y ≤ M →
      ⁅X.subgroupOf M, Y.subgroupOf M⁆ = (⁅X, Y⁆).subgroupOf M := by
    intro X Y hX hY
    apply Subgroup.map_injective M.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hX,
      Subgroup.map_subgroupOf_eq_of_le hY,
      Subgroup.map_subgroupOf_eq_of_le (Proof1424.commutator_le_of_le1424 hX hY)]
  have hU2' : IsPGroup 2 (U.subgroupOf M) := hU2.comap_subtype
  have hA3' : IsPGroup 3 (A.subgroupOf M) := hA3.comap_subtype
  have hle := Proof1424.le_pCoreOf_two_of_commutator_action_five hlocM hNn hNs' hN3'
    hU2' (Subgroup.subgroupOf_mono _ hUN) hE' hE25'
    (Sec16.Proof169.subgroupOf_le_normalizer_subgroupOf hEU)
    (by rw [hcommap hUM hEM, hUE]) hA3'
    (Sec16.Proof169.subgroupOf_le_normalizer_subgroupOf hAU)
    (Sec16.Proof169.subgroupOf_le_normalizer_subgroupOf hAE)
    (by rw [hcommap hEM hAN, ← hEA])
  rw [← Proof1424.pCoreOf_subgroupOf_map hNM]
  intro u hu
  exact ⟨⟨u, hUM hu⟩, hle (Subgroup.mem_subgroupOf.mpr hu), rfl⟩

end CFSG.RankThree.PartTwo.Sec15
