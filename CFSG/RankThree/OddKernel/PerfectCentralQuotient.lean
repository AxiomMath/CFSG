module

public import CFSG.RankThree.OddKernel.RankTwoPowerStructure
public import CFSG.CharacterTheory.Semidihedral.Local.PowerFusionTransfer
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.CentralSylowTransferDerived
public import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Centralization

public section

namespace CFSG.RankThree.OddKernel

open Subgroup CFSG.SectionRank
open scoped commutatorElement Pointwise

universe u

section Perfect

variable {p : ℕ}

theorem isCyclic_of_le_center_of_perfect (hp : p.Prime) (hp3 : 3 < p) {Y : Type u} [Group Y]
    [Finite Y] [Group.IsPerfect Y] (hrank : pRank p Y ≤ 2) {Z : Subgroup Y}
    (hZ : Z ≤ center Y) (hZp : IsPGroup p Z) : IsCyclic Z := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨P⟩ : Nonempty (Sylow p Y) := inferInstance
  have hZn : Z.Normal := normal_of_le_center hZ
  have hZP : Z ≤ P := hZp.le_sylow_of_normal P
  have hPrank : pRank p (P : Subgroup Y) ≤ 2 := (pRank_sylow P).2 ▸ hrank
  have hPp : IsPGroup p (P : Subgroup Y) := P.isPGroup'
  obtain ⟨j, hj⟩ := (hPp.to_subgroup (omega₁ (P : Subgroup Y) (p := p))).exists_card_eq
  have htors := rank_two_large_prime_power_structure_and_section_bound hp hp3 hPp hPrank
  have hj3 : j ≤ 3 := by
    have h := htors.1.2
    rw [hj] at h
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 h
  rcases (show j ≤ 2 ∨ j = 3 by omega) with hj2 | rfl
  · have hE2 : Nat.card (omega₁ (P : Subgroup Y) (p := p)) ≤ p ^ 2 :=
      hj ▸ Nat.pow_le_pow_right hp.pos hj2
    have hcyc : IsCyclic (commutator (P : Subgroup Y)) := (htors.2.1 hE2).1
    have hle := (CFSG.ShultStronglyClosedTI.MiscAlgebra.central_sylow_transfer_derived P Z hZ
      hZp).2
    have : IsCyclic ((commutator (P : Subgroup Y)).map (P : Subgroup Y).subtype) :=
      isCyclic_of_surjective ((P : Subgroup Y).subtype.subgroupMap _)
        ((P : Subgroup Y).subtype.subgroupMap_surjective _)
    exact Subgroup.isCyclic_of_le hle
  · have hZPc : IsCyclic (center (P : Subgroup Y)) := (htors.2.2.1 hj).2.2.1
    have hle : Z.subgroupOf P ≤ center (P : Subgroup Y) := fun z hz =>
      mem_center_iff.2 fun g => Subtype.ext (mem_center_iff.1 (hZ hz) g)
    have : IsCyclic (Z.subgroupOf P) := Subgroup.isCyclic_of_le hle
    exact (subgroupOfEquivOfLe hZP).isCyclic.mp this

theorem inv_conj_pow {Y : Type*} [Group Y] (g b : Y) (n : ℕ) :
    (g⁻¹ * b * g) ^ n = g⁻¹ * b ^ n * g := by
  simpa using conj_pow (a := g⁻¹) (b := b) (i := n)

theorem omega₁_eq_top_of_perfect_of_cube (hp : p.Prime) (hp3 : 3 < p) {Y : Type u} [Group Y]
    [Finite Y] [Group.IsPerfect Y] (P : Sylow p Y) (hPrank : pRank p (P : Subgroup Y) ≤ 2)
    (hE : Nat.card (omega₁ (P : Subgroup Y) (p := p)) = p ^ 3) {A : Subgroup (P : Subgroup Y)}
    (hA : A ≠ ⊥) (hAZ : ∀ a ∈ A, (a : Y) ∈ center Y) :
    omega₁ (P : Subgroup Y) (p := p) = ⊤ := by
  have : Fact p.Prime := ⟨hp⟩
  have hPp : IsPGroup p (P : Subgroup Y) := P.isPGroup'
  have hcube := rank_two_large_prime_cube_torsion_structure hp hp3 hPp hPrank hE
  obtain ⟨-, -, -, -, -, -, -, -, hk⟩ := hcube
  obtain ⟨m, hm⟩ : ∃ m : ℕ, Monoid.exponent (P : Subgroup Y) = p ^ m := by
    obtain ⟨n, hn⟩ := hPp.exists_card_eq
    have hdvd : Monoid.exponent (P : Subgroup Y) ∣ p ^ n := hn ▸ Group.exponent_dvd_nat_card
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).1 hdvd
    exact ⟨k, hk⟩
  obtain ⟨-, hm2, hm1'⟩ := hk m hm
  rcases (show m ≤ 1 ∨ 2 ≤ m by omega) with h1 | h2
  · rcases (show m = 0 ∨ m = 1 by omega) with h0 | h1'
    · exfalso
      have hsub : Subsingleton (P : Subgroup Y) :=
        Monoid.exp_eq_one_iff.1 (by rw [hm, h0, pow_zero])
      have hle : Nat.card (omega₁ (P : Subgroup Y) (p := p)) ≤ 1 :=
        (card_le_card_group _).trans (Finite.card_le_one_iff_subsingleton.2 hsub)
      rw [hE] at hle
      have : 1 < p ^ 3 := Nat.one_lt_pow (by norm_num) hp.one_lt
      omega
    · exact hm1' h1'
  exfalso
  obtain ⟨⟨lam, hlam, hrange⟩, hZcard⟩ := hm2 h2
  have hlamx : ∀ x, lam x = x ^ p ^ (m - 1) := fun x => congrFun hlam x
  have hAdvd : p ∣ Nat.card A := by
    rcases (hPp.to_subgroup A).card_eq_or_dvd with h | h
    · exact absurd (card_eq_one.1 h) hA
    · exact h
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' p hAdvd
  have ha' : orderOf (a : (P : Subgroup Y)) = p := by rw [orderOf_coe, ha]
  have haZ : (a : (P : Subgroup Y)) ∈ (center (omega₁ (P : Subgroup Y) (p := p))).map
      (omega₁ (P : Subgroup Y) (p := p)).subtype := by
    rw [mem_map_center_iff]
    have hap : (a : (P : Subgroup Y)) ^ p = 1 := by
      have h := pow_orderOf_eq_one (a : (P : Subgroup Y))
      rwa [ha'] at h
    refine ⟨subset_closure (show (a : (P : Subgroup Y)) ^ (p ^ 1) = 1 by rw [pow_one]; exact hap),
      fun e _ => ?_⟩
    exact Subtype.ext (mem_center_iff.1 (hAZ a a.2) e)
  have hZc : Nat.card ((center (omega₁ (P : Subgroup Y) (p := p))).map
      (omega₁ (P : Subgroup Y) (p := p)).subtype) = p := by
    rw [card_map_of_injective (subtype_injective _), hZcard]
  have hZeq : zpowers (a : (P : Subgroup Y)) = (center (omega₁ (P : Subgroup Y) (p := p))).map
      (omega₁ (P : Subgroup Y) (p := p)).subtype :=
    eq_of_le_of_card_ge (zpowers_le.2 haZ) (by rw [hZc, Nat.card_zpowers, ha'])
  have hZA : zpowers (a : (P : Subgroup Y)) ≤ A := zpowers_le.2 a.2
  have hcen : ∀ x : (P : Subgroup Y), ((lam x : (P : Subgroup Y)) : Y) ∈ center Y := fun x => by
    have hx : lam x ∈ zpowers (a : (P : Subgroup Y)) := hZeq ▸ hrange ▸ ⟨x, rfl⟩
    exact hAZ _ (hZA hx)
  obtain ⟨x, hx⟩ : ∃ x, lam x ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : lam.range = ⊥ := MonoidHom.range_eq_bot_iff.2 (MonoidHom.ext hcon)
    rw [hrange] at hbot
    rw [hbot, card_bot] at hZc
    exact hp.one_lt.ne hZc
  have hcomm : IsMulCommutative ((P : Subgroup Y) ⧸ lam.ker) := by
    refine ⟨⟨fun u v => ?_⟩⟩
    induction u using QuotientGroup.induction_on with | H s => ?_
    induction v using QuotientGroup.induction_on with | H t => ?_
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, MonoidHom.mem_ker,
      map_mul, map_inv, map_mul, map_mul]
    have hst : lam s * lam t = lam t * lam s :=
      Subtype.ext (mem_center_iff.1 (hcen s) (lam t)).symm
    rw [hst, inv_mul_cancel]
  have hxN : x ∉ lam.ker := fun h => hx (MonoidHom.mem_ker.1 h)
  have hfus : ∀ (k : ℕ) (g : Y) (h : g⁻¹ * (x : Y) ^ k * g ∈ (P : Subgroup Y)),
      (QuotientGroup.mk' lam.ker ⟨g⁻¹ * (x : Y) ^ k * g, h⟩ : (P : Subgroup Y) ⧸ lam.ker) =
        QuotientGroup.mk' lam.ker (x ^ k) := by
    intro k g h
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, MonoidHom.mem_ker,
      map_mul, map_inv, inv_mul_eq_one]
    apply Subtype.ext
    have hc := mem_center_iff.1 (hcen (x ^ k)) g
    rw [hlamx, hlamx]
    rw [hlamx] at hc
    simp only [SubgroupClass.coe_pow] at hc ⊢
    rw [inv_conj_pow, mul_assoc, ← hc, inv_mul_cancel_left]
  have ht := CFSG.Semidihedral.Local.power_fusion_transfer_detection P lam.ker x hxN hfus
  obtain ⟨-, -, -, -, -, hnt, -, hcommQ⟩ := ht
  have h1 := CFSG.SectionRank.Ccomm.perfect_hom_eq_one_of_range_comm (QuotientGroup.mk' _)
    fun a _ b _ => hcommQ a b
  obtain ⟨u, v, huv⟩ := hnt
  obtain ⟨gu, rfl⟩ := QuotientGroup.mk'_surjective _ u
  obtain ⟨gv, rfl⟩ := QuotientGroup.mk'_surjective _ v
  rw [h1] at huv
  exact huv rfl

theorem perfect_rank_two_large_prime_center (hp : p.Prime) (hp3 : 3 < p) {Y : Type u}
    [Group Y] [Finite Y] [Group.IsPerfect Y] (hrank : pRank p Y ≤ 2) :
    (∀ S : Sylow p (center Y), IsCyclic (S : Subgroup (center Y))) ∧ pRank p (center Y) ≤ 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hcyc : ∀ B : Subgroup (center Y), IsPGroup p B → IsCyclic B := fun B hB => by
    have hB' : IsCyclic (B.map (center Y).subtype) :=
      isCyclic_of_le_center_of_perfect hp hp3 hrank (map_subtype_le B) (hB.map _)
    exact (B.equivMapOfInjective _ (subtype_injective _)).isCyclic.mpr hB'
  refine ⟨fun S => hcyc _ S.isPGroup', ?_⟩
  rw [pRank_eq_open_pRank_top]
  refine CFSG.SectionRank.pRank_le hp.one_lt fun B _ hB => ?_
  have hBp : IsPGroup p B := fun b => ⟨1, by rw [pow_one]; exact Subtype.ext (hB.2 b b.2)⟩
  have := hcyc B hBp
  rw [pow_one]
  refine CFSG.RankThree.SubgroupLists.card_le_of_pow_eq_one_of_isCyclic fun b => ?_
  exact Subtype.ext (hB.2 b b.2)

theorem perfect_rank_two_large_prime_central_quotient_sylow (hp : p.Prime) (hp3 : 3 < p)
    {Y : Type u} [Group Y] [Finite Y] [Group.IsPerfect Y] (hrank : pRank p Y ≤ 2)
    (A : Subgroup Y) [A.Normal] (hAZ : A ≤ center Y) (P : Sylow p Y) :
    (∃ Q : Sylow p (Y ⧸ A),
        (Q : Subgroup (Y ⧸ A)) = (P : Subgroup Y).map (QuotientGroup.mk' A)) ∧
      ((QuotientGroup.mk' A).domRestrict (P : Subgroup Y)).ker = A.subgroupOf P ∧
      (Nat.card (omega₁ (P : Subgroup Y) (p := p)) ≤ p ^ 2 →
        pRank p ((P : Subgroup Y) ⧸ A.subgroupOf P) ≤ 2) ∧
      (Nat.card (omega₁ (P : Subgroup Y) (p := p)) = p ^ 3 → A.subgroupOf P ≠ ⊥ →
        omega₁ (P : Subgroup Y) (p := p) = ⊤ ∧ Monoid.exponent (P : Subgroup Y) = p ∧
          Nat.card (P : Subgroup Y) = p ^ 3 ∧
          Nat.card ((P : Subgroup Y) ⧸ A.subgroupOf P) ≤ p ^ 2) ∧
      (A.subgroupOf P = ⊥ →
        ∃ e : (P : Subgroup Y) ≃* (P : Subgroup Y).map (QuotientGroup.mk' A),
          ∀ x, (e x : Y ⧸ A) = QuotientGroup.mk' A x) := by
  have : Fact p.Prime := ⟨hp⟩
  have hPp : IsPGroup p (P : Subgroup Y) := P.isPGroup'
  have hPrank : pRank p (P : Subgroup Y) ≤ 2 := (pRank_sylow P).2 ▸ hrank
  have htors := rank_two_large_prime_power_structure_and_section_bound hp hp3 hPp hPrank
  have hker : ((QuotientGroup.mk' A).domRestrict (P : Subgroup Y)).ker = A.subgroupOf P := by
    rw [MonoidHom.ker_domRestrict, QuotientGroup.ker_mk']
  refine ⟨⟨Sylow.mapSurjective (QuotientGroup.mk'_surjective A) P, Sylow.coe_mapSurjective _ _⟩,
    hker, fun hE2 => (htors.2.1 hE2).2 _, fun hE3 hA => ?_, fun hA => ?_⟩
  · have hEtop := omega₁_eq_top_of_perfect_of_cube hp hp3 P hPrank hE3 hA
      (fun a ha => hAZ (mem_subgroupOf.1 ha))
    have hexp1 : ∀ x : (P : Subgroup Y), x ^ p = 1 := fun x =>
      htors.1.1 x (hEtop ▸ mem_top x)
    have hcardP : Nat.card (P : Subgroup Y) = p ^ 3 := by
      rw [← hE3, hEtop, card_top]
    have hntriv : Nontrivial (P : Subgroup Y) := by
      rw [← Finite.one_lt_card_iff_nontrivial, hcardP]
      exact Nat.one_lt_pow (by norm_num) hp.one_lt
    have hexp : Monoid.exponent (P : Subgroup Y) = p := by
      have hdvd := Monoid.exponent_dvd_of_forall_pow_eq_one hexp1
      rcases hp.eq_one_or_self_of_dvd _ hdvd with h | h
      · exact absurd (Monoid.exp_eq_one_iff.1 h) (not_subsingleton _)
      · exact h
    refine ⟨hEtop, hexp, hcardP, ?_⟩
    have hAp : p ≤ Nat.card (A.subgroupOf (P : Subgroup Y)) := by
      rcases (hPp.to_subgroup (A.subgroupOf (P : Subgroup Y))).card_eq_or_dvd with h | h
      · exact absurd (card_eq_one.1 h) hA
      · exact Nat.le_of_dvd Nat.card_pos h
    have hmul := card_eq_card_quotient_mul_card_subgroup (A.subgroupOf (P : Subgroup Y))
    rw [hcardP] at hmul
    have hle : Nat.card ((P : Subgroup Y) ⧸ A.subgroupOf (P : Subgroup Y)) * p ≤ p ^ 2 * p := by
      calc _ ≤ Nat.card ((P : Subgroup Y) ⧸ A.subgroupOf (P : Subgroup Y)) *
            Nat.card (A.subgroupOf (P : Subgroup Y)) := Nat.mul_le_mul_left _ hAp
        _ = p ^ 2 * p := by rw [← hmul, pow_succ]
    exact Nat.le_of_mul_le_mul_right hle hp.pos
  · have hinj : Function.Injective ((QuotientGroup.mk' A).domRestrict (P : Subgroup Y)) := by
      rw [← MonoidHom.ker_eq_bot_iff, hker, hA]
    exact ⟨(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr
      (MonoidHom.domRestrict_range _ _)), fun x => rfl⟩

theorem perfect_rank_two_large_prime_quotient_pRank_le_two (hp : p.Prime) (hp3 : 3 < p)
    {Y : Type u} [Group Y] [Finite Y] [Group.IsPerfect Y] (hrank : pRank p Y ≤ 2)
    (A : Subgroup Y) [A.Normal] (hAZ : A ≤ center Y) : pRank p (Y ⧸ A) ≤ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨P⟩ : Nonempty (Sylow p Y) := inferInstance
  have hPp : IsPGroup p (P : Subgroup Y) := P.isPGroup'
  have hPrank : pRank p (P : Subgroup Y) ≤ 2 := (pRank_sylow P).2 ▸ hrank
  have hfacts := perfect_rank_two_large_prime_central_quotient_sylow hp hp3 hrank A hAZ P
  obtain ⟨⟨Q, hQ⟩, hker, hsmall, hcube, -⟩ := hfacts
  have e1 : (P : Subgroup Y) ⧸ A.subgroupOf P ≃* (Q : Subgroup (Y ⧸ A)) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      ((QuotientGroup.quotientKerEquivRange _).trans (MulEquiv.subgroupCongr
        ((MonoidHom.domRestrict_range _ _).trans hQ.symm)))
  have h1 : pRank p (Y ⧸ A) = pRank p ((P : Subgroup Y) ⧸ A.subgroupOf P) := by
    rw [← (pRank_sylow Q).2, pRank_eq_open_pRank_top, pRank_eq_open_pRank_top]
    exact (pRank_top_eq_of_mulEquiv hp.one_lt e1).symm
  rw [h1]
  have htors := (rank_two_large_prime_power_structure_and_section_bound hp hp3 hPp hPrank).1.2
  obtain ⟨j, hj⟩ := (hPp.to_subgroup (omega₁ (P : Subgroup Y) (p := p))).exists_card_eq
  have hj3 : j ≤ 3 := by
    rw [hj] at htors
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 htors
  rcases (show j ≤ 2 ∨ j = 3 by omega) with hj2 | rfl
  · exact hsmall (hj ▸ Nat.pow_le_pow_right hp.pos hj2)
  by_cases hA : A.subgroupOf (P : Subgroup Y) = ⊥
  · have e2 : (P : Subgroup Y) ⧸ A.subgroupOf P ≃* (P : Subgroup Y) :=
      (QuotientGroup.quotientMulEquivOfEq hA).trans QuotientGroup.quotientBot
    rw [pRank_eq_open_pRank_top, pRank_top_eq_of_mulEquiv hp.one_lt e2,
      ← pRank_eq_open_pRank_top]
    exact hPrank
  · exact CFSG.RankThree.PartTwo.pRank_le_of_card_le hp (hcube hj hA).2.2.2

end Perfect

end CFSG.RankThree.OddKernel
