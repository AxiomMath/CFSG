module

public import CFSG.Quasithin.Vol2.Ch10SecQ9H46
public import CFSG.Quasithin.Vol2.Ch1Sec3Solvable
public import CFSG.LocalAnalysis.ComponentInitial.QTNQRLinearUnitaryOuterDerived
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdRank
public import CFSG.LieType.SteinbergBRSemidirectSLEven

public section

namespace CFSG.Quasithin.Vol2.Ch11.OE6

open CFSG.Open CFSG.Quasithin CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner equivalence)

theorem conj_eq_one_iff {X : Type*} [Group X] {x : X} :
    MulAut.conj x = 1 ↔ x ∈ Subgroup.center X := by
  rw [Subgroup.mem_center_iff]
  constructor
  · intro h y
    have h1 := congrArg (fun α : MulAut X => α y) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    calc y * x = (x * y * x⁻¹) * x := by rw [h1]
      _ = x * y := by group
  · intro h
    refine MulEquiv.ext fun y => ?_
    rw [MulAut.conj_apply, MulAut.one_apply, ← h y, mul_inv_cancel_right]

noncomputable def innerEquiv (X : Type*) [Group X] : ↥(inner X) ≃* X ⧸ Subgroup.center X :=
  (QuotientGroup.quotientKerEquivRange (MulAut.conj : X →* MulAut X)).symm.trans
    (QuotientGroup.quotientMulEquivOfEq (Subgroup.ext fun _ => conj_eq_one_iff))

theorem isCyclic_of_mulAut {X : Type*} [Group X] [Finite X] {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hout : Nat.Coprime p (Nat.card (Outer X)))
    (hrk : Open.pRank p (⊤ : Subgroup (X ⧸ Subgroup.center X)) ≤ 1)
    {U : Subgroup (MulAut X)} (hU : IsPGroup p U) : IsCyclic ↥U := by
  have hUI : U ≤ inner X := by
    intro u hu
    obtain ⟨k, hk⟩ := hU ⟨u, hu⟩
    have h1 : orderOf (QuotientGroup.mk u : Outer X) ∣ Nat.card (Outer X) :=
      orderOf_dvd_natCard _
    have h2 : orderOf (QuotientGroup.mk u : Outer X) ∣ p ^ k := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← QuotientGroup.mk_pow, show u ^ p ^ k = 1 from congrArg Subtype.val hk,
        QuotientGroup.mk_one]
    have h3 : orderOf (QuotientGroup.mk u : Outer X) = 1 :=
      Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left k hout) h2 h1
    exact (QuotientGroup.eq_one_iff u).mp (orderOf_eq_one_iff.mp h3)
  let f : ↥U →* X ⧸ Subgroup.center X :=
    (innerEquiv X).toMonoidHom.comp (Subgroup.inclusion hUI)
  have hf : Function.Injective f :=
    (innerEquiv X).injective.comp (Subgroup.inclusion_injective hUI)
  have hle := CFSG.SectionRank.pRank_top_le_of_injective hp.out.one_lt f hf
  exact Ch1Sec3.isCyclic_of_pRank_le_one hp2 hU (hle.trans hrk)

theorem isCyclic_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) {p : ℕ}
    (h : ∀ U : Subgroup (MulAut Y), IsPGroup p U → IsCyclic ↥U)
    {U : Subgroup (MulAut X)} (hU : IsPGroup p U) : IsCyclic ↥U := by
  have := h (U.map (MulAut.congr e).toMonoidHom) (hU.map _)
  exact isCyclic_of_surjective
    (U.equivMapOfInjective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective).symm.toMonoidHom
    (MulEquiv.surjective _)

theorem center_eq_bot_of_psl2 {X : Type*} [Group X] {K : Type*} [Field K] [Finite K]
    (e : X ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) : Subgroup.center X = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  have h1 : e x ∈ Subgroup.center (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨z, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx z]
  rw [CFSG.GorensteinWalter.psl2_center_eq_bot K, Subgroup.mem_bot] at h1
  exact e.injective (h1.trans (map_one e).symm)

theorem isCyclic_mulAut_psl2_model (K : Type) [Field K] [Finite K] {r f p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hr : r.Prime) (hK : Nat.card K = r ^ f)
    (hcop : Nat.Coprime p (f * Nat.gcd 2 (r ^ f - 1)))
    (hrk : Open.pRank p (⊤ : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)) ≤ 1)
    {U : Subgroup (MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K))} (hU : IsPGroup p U) :
    IsCyclic ↥U := by
  have hout := (CFSG.LocalAnalysis.ComponentInitial.linear_two_outer_order_divisor hr K hK).1
  refine isCyclic_of_mulAut hp2 (Nat.Coprime.coprime_dvd_right hout hcop) ?_ hU
  have hZ := center_eq_bot_of_psl2 (MulEquiv.refl (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K))
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.out.one_lt
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)]
  exact hrk

theorem isCyclic_mulAut_psl34 {X : Type} [Group X] [Finite X] (h : IsPSL 3 2 2 X) {p : ℕ}
    [hp : Fact p.Prime] (hp5 : 5 ≤ p) {U : Subgroup (MulAut X)} (hU : IsPGroup p U) :
    IsCyclic ↥U := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hU
  have hdvd : p ^ k ∣ 241920 := by
    rw [← hk]
    have h1 := Subgroup.card_subgroup_dvd_card U
    have h2 := Vol2.Ch10.SecC.C10P4F.card_mulAut_dvd_of_psl34 h
    rw [SecA.C11P9B.card_of_isPSL_three_two_two h] at h2
    exact h1.trans h2
  have hk1 : k ≤ 1 := by
    by_contra hk2
    have hp2 : p ^ 2 ∣ 241920 := (Nat.pow_dvd_pow p (by omega)).trans hdvd
    have hpd : p ∣ 2 ^ 8 * (3 ^ 3 * (5 * 7)) :=
      (by norm_num : (241920 : ℕ) = 2 ^ 8 * (3 ^ 3 * (5 * 7))) ▸
        (dvd_pow_self p two_ne_zero).trans hp2
    have hp57 : p = 5 ∨ p = 7 := by
      rcases (Nat.Prime.dvd_mul hp.out).mp hpd with h1 | h1
      · have := (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp (hp.out.dvd_of_dvd_pow h1)
        omega
      rcases (Nat.Prime.dvd_mul hp.out).mp h1 with h2 | h2
      · have := (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_three).mp
          (hp.out.dvd_of_dvd_pow h2)
        omega
      rcases (Nat.Prime.dvd_mul hp.out).mp h2 with h3 | h3
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp.out (by norm_num)).mp h3)
      · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp.out (by norm_num)).mp h3)
    rcases hp57 with rfl | rfl <;> norm_num at hp2
  interval_cases k
  · rw [pow_zero] at hk
    have : Subsingleton ↥U := (Nat.card_eq_one_iff_unique.mp hk).1
    infer_instance
  · rw [pow_one] at hk
    exact isCyclic_of_prime_card hk

theorem model_psl2 (K : Type) [Field K] [Finite K] {r f : ℕ} (hr : r.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = r ^ f) (h4 : 4 ≤ r ^ f) :
    CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) .PSL 2 r f := by
  refine ⟨⟨hr, hf, le_rfl, ?_, ?_⟩, K, inferInstance, inferInstance, hK,
    ⟨projectiveSpecialLinearGroupEquivStatedProj 2 K⟩⟩
  · intro h
    simp only [Prod.mk.injEq, true_and] at h
    omega
  · intro h
    simp only [Prod.mk.injEq, true_and] at h
    omega

theorem isCyclic_mulAut_psl2 {X : Type} [Group X] [Finite X] {q : ℕ} (hq : q.Prime)
    (hq3 : 3 < q) (h : IsPSL 2 q 1 X) {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    {U : Subgroup (MulAut X)} (hU : IsPGroup p U) : IsCyclic ↥U := by
  have hrkX := CFSG.QuasithinUnique.Id2519.pRank_le_one_psl_two_prime hq hq3 h hp.out hp2
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  let e' : X ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K :=
    e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
  have : Finite (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) := Finite.of_equiv X e'.toEquiv
  have hcop : Nat.Coprime p (1 * Nat.gcd 2 (q ^ 1 - 1)) :=
    Nat.Coprime.coprime_dvd_right (by rw [one_mul]; exact Nat.gcd_dvd_left 2 _)
      ((Nat.coprime_primes hp.out Nat.prime_two).2 hp2)
  refine isCyclic_of_mulEquiv e' (fun V hV => isCyclic_mulAut_psl2_model K hp2 hq hK hcop ?_ hV) hU
  rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.out.one_lt e']
  exact hrkX

theorem isCyclic_mulAut_sl2_four {X : Type} [Group X] [Finite X] {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 4) (e : X ≃* Matrix.SpecialLinearGroup (Fin 2) F) {p : ℕ}
    [hp : Fact p.Prime] (hp2 : p ≠ 2) {U : Subgroup (MulAut X)} (hU : IsPGroup p U) :
    IsCyclic ↥U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype F := Fintype.ofFinite F
  have hF' : Nat.card F = 2 ^ 2 := by rw [hF]; norm_num
  have : CharP F 2 := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  have hZ := CFSG.LieType.SteinbergBR.center_SL_eq_bot_of_charTwo (F := F) (m := 2) (by norm_num)
    (Or.inl rfl)
  let e₁ : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have hcop : Nat.Coprime p (2 * Nat.gcd 2 (2 ^ 2 - 1)) := by
    have h1 : 2 * Nat.gcd 2 (2 ^ 2 - 1) = 2 := by norm_num
    rw [h1]
    exact (Nat.coprime_primes hp.out Nat.prime_two).2 hp2
  have hrk : Open.pRank p (⊤ : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) ≤ 1 :=
    CFSG.QuasithinUnique.Id2519.pRank_le_one_psl_two_even
      (model_psl2 F Nat.prime_two (by norm_num) hF' (by norm_num)) hp.out hp2
  exact isCyclic_of_mulEquiv (e.trans e₁.symm)
    (fun V hV => isCyclic_mulAut_psl2_model F hp2 Nat.prime_two hF' hcop hrk hV) hU

theorem isCyclic_mulAut_sl2 {X : Type} [Group X] [Finite X] {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r)
    (e : X ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod r)) {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) {U : Subgroup (MulAut X)} (hU : IsPGroup p U) : IsCyclic ↥U := by
  have : Fact r.Prime := ⟨hr⟩
  set J := Matrix.SpecialLinearGroup (Fin 2) (ZMod r)
  have hcard : Nat.card (ZMod r) = r ^ 1 := by rw [Nat.card_zmod, pow_one]
  have : Group.IsPerfect J := by
    refine CFSG.LinearGroups.special_linear_dimension_two_perfect ?_
    have : Fintype (ZMod r) := ZMod.fintype r
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (ZMod r)))
      (n := 4) (by rw [Finset.card_univ, ZMod.card]; omega)
    exact ⟨s, hs⟩
  have hinj := CFSG.LocalAnalysis.ComponentInitial.OuterDerived.outer_comp_injective J
    (MulEquiv.refl (J ⧸ Subgroup.center J))
  have hdvd := Subgroup.card_dvd_of_injective _ hinj
  have hout := (CFSG.LocalAnalysis.ComponentInitial.linear_two_outer_order_divisor hr (ZMod r)
    hcard).1
  have hcop : Nat.Coprime p (Nat.card (Outer J)) := by
    refine Nat.Coprime.coprime_dvd_right (hdvd.trans hout) ?_
    exact Nat.Coprime.coprime_dvd_right (by rw [one_mul]; exact Nat.gcd_dvd_left 2 _)
      ((Nat.coprime_primes hp.out Nat.prime_two).2 hp2)
  have hrk : Open.pRank p (⊤ : Subgroup (J ⧸ Subgroup.center J)) ≤ 1 :=
    CFSG.QuasithinUnique.Id2519.pRank_le_one_psl_two_prime hr (by omega)
      (model_psl2 (ZMod r) hr le_rfl hcard (by rw [pow_one]; omega)) hp.out hp2
  exact isCyclic_of_mulEquiv e (fun V hV => isCyclic_of_mulAut hp2 hcop hrk hV) hU

end CFSG.Quasithin.Vol2.Ch11.OE6
