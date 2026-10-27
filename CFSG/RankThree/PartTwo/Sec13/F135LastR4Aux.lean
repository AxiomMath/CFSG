module

public import CFSG.RankThree.PartTwo.Sec13.F135LastR5Facts

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped commutatorElement

theorem r4g_inj {M : Type*} [Group M] {p : ℕ} (hp : p.Prime) (R : Subgroup M) [R.Normal]
    (hR : ¬ p ∣ Nat.card R) {E : Subgroup M} (hE : IsPGroup p E) :
    Function.Injective ((QuotientGroup.mk' R).comp E.subtype) := by
  haveI := Fact.mk hp
  rw [injective_iff_map_eq_one]
  rintro ⟨e, he⟩ h
  have h' : (e : M ⧸ R) = 1 := h
  have heR : e ∈ R := (QuotientGroup.eq_one_iff e).mp h'
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hE) ⟨e, he⟩
  have h1 : orderOf (⟨e, heR⟩ : R) = orderOf e := Subgroup.orderOf_mk e heR
  have h2 : orderOf (⟨e, he⟩ : E) = orderOf e := Subgroup.orderOf_mk e he
  have hdvd : orderOf e ∣ Nat.card R := by
    rw [← h1]
    exact orderOf_dvd_natCard _
  have hord : orderOf e = p ^ k := by rw [← h2, hk]
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · have h1' : orderOf e = 1 := by rw [hord, hk0, pow_zero]
    apply Subtype.ext
    simpa using orderOf_eq_one_iff.mp h1'
  · have hpk : p ^ k ∣ Nat.card R := by
      rw [← hord]
      exact hdvd
    exact absurd ((dvd_pow_self p hk0.ne').trans hpk) hR

theorem r4g_card_map {M : Type*} [Group M] (R : Subgroup M) [R.Normal] {E : Subgroup M}
    (hinj : Function.Injective ((QuotientGroup.mk' R).comp E.subtype)) :
    Nat.card (E.map (QuotientGroup.mk' R)) = Nat.card E := by
  have hmap : E.map (QuotientGroup.mk' R) = ((QuotientGroup.mk' R).comp E.subtype).range := by
    have h := MonoidHom.map_range (QuotientGroup.mk' R) E.subtype
    rwa [Subgroup.range_subtype] at h
  rw [hmap]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

theorem r4g_card_image_le {M : Type*} [Group M] [Finite M] (R : Subgroup M) [R.Normal]
    (Y : Subgroup M) : Nat.card (Y.map (QuotientGroup.mk' R)) ≤ Nat.card Y := by
  have hmap : Y.map (QuotientGroup.mk' R) = ((QuotientGroup.mk' R).comp Y.subtype).range := by
    have h := MonoidHom.map_range (QuotientGroup.mk' R) Y.subtype
    rwa [Subgroup.range_subtype] at h
  rw [hmap]
  exact Nat.card_le_card_of_surjective _
    (MonoidHom.rangeRestrict_surjective ((QuotientGroup.mk' R).comp Y.subtype))

theorem r4g_arith {G : Type*} [Group G] (p : ℕ) (hp : p.Prime) (A Q : Subgroup G)
    (hAQ : A ≤ Q) (hAc : Nat.card A ≤ p) (hQ : p ^ 4 ≤ Nat.card Q) :
    p ^ 3 ≤ A.relIndex Q := by
  have hrel : A.relIndex Q * Nat.card (A ⊓ Q :) = Nat.card Q := Subgroup.relIndex_mul_card A Q
  rw [inf_eq_left.mpr hAQ] at hrel
  have h1 : A.relIndex Q * Nat.card A ≤ A.relIndex Q * p := Nat.mul_le_mul le_rfl hAc
  have h2 : p * p ^ 3 ≤ p * A.relIndex Q := by
    calc p * p ^ 3 = p ^ 4 := by ring
      _ ≤ Nat.card Q := hQ
      _ = A.relIndex Q * Nat.card A := hrel.symm
      _ ≤ A.relIndex Q * p := h1
      _ = p * A.relIndex Q := mul_comm _ _
  exact Nat.le_of_mul_le_mul_left h2 hp.pos

theorem r4_E_index {M : Type*} [Group M] [Finite M] {p : ℕ} (hp : p.Prime) (R : Subgroup M)
    [R.Normal] (hR : ¬ p ∣ Nat.card R) {E Y : Subgroup M} (hE : IsPGroup p E)
    (hY : Nat.card Y ≤ p) (h4 : p ^ 4 ≤ Nat.card E) (J : Subgroup (M ⧸ R))
    (hker : Subgroup.centralizer (J : Set (M ⧸ R)) ⊓ E.map (QuotientGroup.mk' R) ≤
      Y.map (QuotientGroup.mk' R)) :
    p ^ 3 ≤ (Subgroup.centralizer (J : Set (M ⧸ R)) ⊓ E.map (QuotientGroup.mk' R)).relIndex
      (E.map (QuotientGroup.mk' R)) := by
  have hinj := r4g_inj hp R hR hE
  have hQ : Nat.card (E.map (QuotientGroup.mk' R)) = Nat.card E := r4g_card_map R hinj
  have hYc : Nat.card (Y.map (QuotientGroup.mk' R)) ≤ p :=
    (r4g_card_image_le R Y).trans hY
  have hKc : Nat.card ↥(Subgroup.centralizer (J : Set (M ⧸ R)) ⊓
      E.map (QuotientGroup.mk' R)) ≤ p :=
    (Subgroup.card_le_of_le hker).trans hYc
  have hQ4 : p ^ 4 ≤ Nat.card (E.map (QuotientGroup.mk' R)) := by
    rw [hQ]
    exact h4
  exact r4g_arith p hp (Subgroup.centralizer (J : Set (M ⧸ R)) ⊓ E.map (QuotientGroup.mk' R))
    (E.map (QuotientGroup.mk' R)) inf_le_right hKc hQ4

theorem r4_E_comm_inf {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {D Y : Subgroup G}
    (hD : IsPGroup p D) (hexp : ∀ x ∈ D, x ^ p = 1) (hY : Nat.card Y = p)
    (hYΦ : ¬ Y ≤ frattiniOf D) :
    Y.subgroupOf (cM Y) ⊓ (commutator ↥(eOf D Y)).map (eOf D Y).subtype = ⊥ := by
  have hp : p.Prime := Fact.out
  have hmemD : ∀ x : ↥(eOf D Y), ((x : cM Y) : G) ∈ D := by
    intro x
    have hx : ((x : cM Y) : G) ∈ D ⊓ cM Y := Subgroup.mem_subgroupOf.mp x.2
    exact (Subgroup.mem_inf.mp hx).1
  have hcomm : commutator ↥(eOf D Y) ≤
      (frattiniOf D).comap ((cM Y).subtype.comp (eOf D Y).subtype) := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [Subgroup.mem_comap, map_commutatorElement]
    exact r2a_comm_mem hD hexp (hmemD x) (hmemD y)
  rw [Subgroup.eq_bot_iff_forall]
  intro a ha
  obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp ha
  obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp h2
  have hY' : (((eOf D Y).subtype e : cM Y) : G) ∈ Y := Subgroup.mem_subgroupOf.mp h1
  have hΦ : (((eOf D Y).subtype e : cM Y) : G) ∈ frattiniOf D := by
    have h0 := Subgroup.mem_comap.mp (hcomm he)
    exact h0
  have hinf : (((eOf D Y).subtype e : cM Y) : G) ∈ Y ⊓ frattiniOf D :=
    Subgroup.mem_inf.mpr ⟨hY', hΦ⟩
  rw [r5gl_Y_inf_eq_bot hp hY hYΦ, Subgroup.mem_bot] at hinf
  exact Subtype.ext hinf

theorem r4_normalizer_of_map {N : Type*} [Group N] (J : Subgroup N)
    (n : Subgroup.normalizer (J : Set N)) (T : Subgroup J)
    (hT : T.map (J.normalizerMonoidHom n).toMonoidHom = T) :
    (n : N) ∈ Subgroup.normalizer ((T.map J.subtype : Subgroup N) : Set N) := by
  have happ : ∀ x : J, (((J.normalizerMonoidHom n) x : J) : N) = (n : N) * (x : N) * (n : N)⁻¹ :=
    fun x => rfl
  have hstab : ∀ x : J, (J.normalizerMonoidHom n) x ∈ T ↔ x ∈ T := by
    intro x
    have key := Subgroup.mem_map_equiv (f := J.normalizerMonoidHom n) (K := T)
      (x := (J.normalizerMonoidHom n) x)
    rw [hT, MulEquiv.symm_apply_apply] at key
    exact key
  rw [Subgroup.mem_set_normalizer_iff]
  intro h
  constructor
  · intro hh
    rw [SetLike.mem_coe] at hh
    obtain ⟨x, hxT, hxh⟩ := Subgroup.mem_map.mp hh
    refine Subgroup.mem_map.mpr ⟨(J.normalizerMonoidHom n) x, (hstab x).mpr hxT, ?_⟩
    rw [← hxh]
    exact happ x
  · intro hh
    rw [SetLike.mem_coe] at hh
    obtain ⟨y, hyT, hyeq⟩ := Subgroup.mem_map.mp hh
    have hnh : (n : N) * h * (n : N)⁻¹ ∈ (J : Set N) := by
      rw [← hyeq]
      exact y.2
    have hhJ : h ∈ (J : Set N) := (Subgroup.mem_set_normalizer_iff.mp n.2 h).mpr hnh
    have hσx : (J.normalizerMonoidHom n) ⟨h, hhJ⟩ = y := by
      apply Subtype.ext
      rw [happ]
      exact hyeq.symm
    have hxT : (⟨h, hhJ⟩ : J) ∈ T := (hstab ⟨h, hhJ⟩).mp (by rw [hσx]; exact hyT)
    exact Subgroup.mem_map.mpr ⟨⟨h, hhJ⟩, hxT, rfl⟩

end CFSG.RankThree.PartTwo.Sec13.F135Last
