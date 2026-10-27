module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SignalizerFunctor.InvariantSylowAmbient
import CFSG.LocalAnalysis.RankThreeEvenClassification.LocalRank

public section

namespace CFSG.RankThree.Classical2

open CFSG.Assembly CFSG.Assembly.RankThreeEven

variable {G : Type*} [Group G] [Finite G]

theorem exists_elemAbelian_lift {p : ℕ} [hp : Fact p.Prime] (N : Subgroup G) [N.Normal]
    (hN : ¬ p ∣ Nat.card N) {E : Subgroup (G ⧸ N)} (hE : IsElemAbelian p E) :
    ∃ S : Subgroup G, S ≤ E.comap (QuotientGroup.mk' N) ∧ IsElemAbelian p S ∧
      Nat.card S = Nat.card E := by
  have hEp : IsPGroup p E := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]
    exact hE.2 _ x.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hEp
  set P : Subgroup G := E.comap (QuotientGroup.mk' N)
  have hPcard : Nat.card P = Nat.card N * p ^ k := by
    rw [← hk]
    exact QuotientGroup.card_preimage_mk N (E : Set (G ⧸ N))
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow p P))
  have hScard : Nat.card S = p ^ k := by
    rw [Sylow.card_eq_multiplicity, hPcard, Nat.factorization_mul (Nat.card_pos.ne')
      (pow_ne_zero _ hp.out.ne_zero), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hN, Nat.Prime.factorization_pow hp.out,
      Finsupp.single_eq_same, zero_add]
  set S' : Subgroup G := (S : Subgroup P).map P.subtype with hS'
  have hS'card : Nat.card S' = p ^ k := by
    rw [hS', Subgroup.card_map_of_injective Subtype.val_injective, hScard]
  have hdisj : Disjoint S' N := Subgroup.disjoint_of_coprime_natCard (by
    rw [hS'card]
    exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hN))
  have hS'P : S' ≤ P := Subgroup.map_subtype_le _
  have hinj : ∀ a b : G, a ∈ S' → b ∈ S' →
      (QuotientGroup.mk' N) a = (QuotientGroup.mk' N) b → a = b := by
    intro a b ha hb hab
    have h1 : b⁻¹ * a ∈ N := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hab
      have := N.inv_mem hab
      rwa [mul_inv_rev, inv_inv] at this
    have h2 : b⁻¹ * a ∈ S' ⊓ N := ⟨S'.mul_mem (S'.inv_mem hb) ha, h1⟩
    rw [hdisj.eq_bot, Subgroup.mem_bot] at h2
    exact (eq_of_inv_mul_eq_one h2).symm
  refine ⟨S', hS'P, ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩, by rw [hS'card, hk]⟩
  · refine hinj _ _ (S'.mul_mem a.2 b.2) (S'.mul_mem b.2 a.2) ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
    have ha : (QuotientGroup.mk' N) a ∈ E := hS'P a.2
    have hb : (QuotientGroup.mk' N) b ∈ E := hS'P b.2
    exact congrArg Subtype.val (hE.1.is_comm.comm (⟨_, ha⟩ : E) ⟨_, hb⟩)
  · refine hinj _ _ (S'.pow_mem hx p) S'.one_mem ?_
    rw [map_pow, map_one]
    exact hE.2 _ (hS'P hx)

theorem le_localRank_of_normalizes {p : ℕ} (hp : p.Prime) {S D : Subgroup G}
    (hSD : S ≤ Subgroup.normalizer (D : Set G)) (hS : IsElemAbelian p S) {k : ℕ}
    (hSk : Nat.card S = p ^ k) (hcop : Nat.Coprime p (Nat.card D)) (h2 : 2 ∣ Nat.card D) :
    k ≤ localRank p G := by
  have : Fact p.Prime := ⟨hp⟩
  have hSp : IsPGroup p S := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]
    exact hS.2 _ x.2)⟩
  obtain ⟨T, hST, hT0⟩ :=
    CFSG.SignalizerFunctor.Helpers.normalized_subgroup_invariant_sylow_nontrivial
      p 2 hp Nat.prime_two S D hSp hSD hcop h2
  have hT2 : IsPGroup 2 ((T : Subgroup D).map D.subtype) := T.isPGroup'.map D.subtype
  have hloc : IsTwoLocal (Subgroup.normalizer
      (((T : Subgroup D).map D.subtype : Subgroup G) : Set G)) := ⟨_, hT0, hT2, rfl⟩
  have h1 := CFSG.SectionRank.le_pRank hp.one_lt hST hS hSk
  exact h1.trans (le_csSup (CFSG.RankThreeEvenClassification.Helpers.twoLocalRank_bddAbove p hp G)
    ⟨_, hloc, rfl⟩)

theorem localRank_quotient_le {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (N : Subgroup G) [N.Normal]
    (hN : ¬ p ∣ Nat.card N) : localRank p (G ⧸ N) ≤ localRank p G := by
  have : Fact p.Prime := ⟨hp⟩
  refine csSup_le' ?_
  rintro k ⟨H, ⟨U, hU0, hU2, rfl⟩, rfl⟩
  obtain ⟨E, hEH, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt
    (Subgroup.normalizer (U : Set (G ⧸ N)))
  obtain ⟨S, hSE, hS, hScard⟩ := exists_elemAbelian_lift N hN hE
  set D : Subgroup G := U.comap (QuotientGroup.mk' N) with hDdef
  have hSD : S ≤ Subgroup.normalizer (D : Set G) := by
    intro s hs
    have hsE : (QuotientGroup.mk' N) s ∈ Subgroup.normalizer (U : Set (G ⧸ N)) := hEH (hSE hs)
    rw [Subgroup.mem_normalizer_iff] at hsE ⊢
    intro d
    change (QuotientGroup.mk' N) d ∈ U ↔ (QuotientGroup.mk' N) (s * d * s⁻¹) ∈ U
    rw [map_mul, map_mul, map_inv]
    exact hsE _
  have hDcard : Nat.card D = Nat.card N * Nat.card U :=
    QuotientGroup.card_preimage_mk N (U : Set (G ⧸ N))
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hU2
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hm
    exact hU0 ((Subgroup.card_eq_one).mp hm)
  have hcop : Nat.Coprime p (Nat.card D) := by
    rw [hDcard, hm]
    refine Nat.Coprime.mul_right ((Nat.Prime.coprime_iff_not_dvd hp).2 hN) ?_
    exact Nat.Coprime.pow_right m ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  have h2 : 2 ∣ Nat.card D := by
    rw [hDcard, hm]
    exact Dvd.dvd.mul_left (dvd_pow_self 2 hm0) _
  have hSk : Nat.card S = p ^ CFSG.Assembly.pRank p (Subgroup.normalizer (U : Set (G ⧸ N))) := by
    rw [hScard, hEcard]
  exact le_localRank_of_normalizes hp hSD hS hSk hcop h2

theorem localRank_eq_pRank_of_even {p : ℕ} (hp : p.Prime) (_hp2 : p ≠ 2) (N : Subgroup G)
    [N.Normal] (hN : ¬ p ∣ Nat.card N) (heven : Even (Nat.card N)) :
    localRank p G = pRank p (⊤ : Subgroup G) ∧
      pRank p (⊤ : Subgroup G) = pRank p (⊤ : Subgroup (G ⧸ N)) := by
  have : Fact p.Prime := ⟨hp⟩
  refine ⟨le_antisymm ?_ ?_, (CFSG.SectionRank.pRank_quotient_eq N hN).symm⟩
  · exact CFSG.RankThreeEvenClassification.Helpers.twoLocalRank_le_pRank p hp G
  · obtain ⟨E, -, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (⊤ : Subgroup G)
    have hEN : E ≤ Subgroup.normalizer (N : Set G) := by
      rw [Subgroup.normalizer_eq_top]
      exact le_top
    exact le_localRank_of_normalizes hp hEN hE hEcard
      ((Nat.Prime.coprime_iff_not_dvd hp).2 hN) (even_iff_two_dvd.mp heven)

end CFSG.RankThree.Classical2
