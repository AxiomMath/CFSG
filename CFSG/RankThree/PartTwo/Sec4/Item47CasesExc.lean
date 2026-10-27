module

public import CFSG.RankThree.PartTwo.KFacts.AutSzOrderThree
public import CFSG.RankThree.PartTwo.KFacts.AutTrialityOrderThree
public import CFSG.RankThree.PartTwo.KFacts.K71TrialityFix
public import CFSG.RankThree.PartTwo.KFacts.AutG2OrderThree
public import CFSG.RankThree.PartTwo.Sec4.Item47Bridges
public import CFSG.RankThree.PartTwo.Sec4.Item47Inputs
public import CFSG.RankThree.PartTwo.Sec4.Item47Kinds
public import CFSG.RankThree.PartTwo.Sec4.Item47Statement

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_lift_of_mem_barCentralizer {a : G} (ha : a ∈ Subgroup.normalizer (L : Set G))
    (ha3 : a ^ 3 = 1) {y : L ⧸ aschbacherSolvableCore 3 L}
    (hy : y ∈ Sec8.barCentralizer (Subgroup.zpowers a) L) (hy3 : orderOf y = 3) :
    ∃ (x : G) (hxL : x ∈ L), x * a = a * x ∧ orderOf x = 3 ∧
      QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨x, hxL⟩ = y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hE3 : IsPGroup 3 (Subgroup.zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy3, pow_one])
  have hle : Subgroup.zpowers y ≤ Sec8.barCentralizer (Subgroup.zpowers a) L :=
    Subgroup.zpowers_le.mpr hy
  obtain ⟨E, -, hEa, -, himE, -, hinj⟩ :=
    exists_lift_of_le_barCentralizer ha ⟨1, by rw [pow_one]; exact ha3⟩ hE3 hle
  have hyE : y ∈ Sec8.imageModTheta L E := by
    rw [himE]
    exact Subgroup.mem_zpowers y
  obtain ⟨l, hl, hly⟩ := hyE
  have hlE : (l : G) ∈ E := hl
  refine ⟨l, l.2, ?_, ?_, hly⟩
  · exact (Subgroup.mem_centralizer_singleton_iff.mp (hEa hlE))
  · have hl3 : l ^ 3 = 1 := by
      apply hinj
      · rw [Subgroup.coe_pow]
        exact E.pow_mem hlE 3
      · rw [map_pow, hly]
        have := pow_orderOf_eq_one y
        rwa [hy3] at this
    have hl1 : (l : G) ≠ 1 := by
      intro h1
      have : l = 1 := Subtype.ext h1
      rw [this, map_one] at hly
      rw [← hly, orderOf_one] at hy3
      norm_num at hy3
    refine orderOf_eq_prime ?_ hl1
    rw [← Subgroup.coe_pow, hl3, Subgroup.coe_one]

theorem alt47_of_g2_even
    (hin : Inputs47NoD4)
    (hG : SectionFourHyp G)
    (h3 : 3 ∣ Nat.card (Subgroup.center G)) {f : ℕ}
    (h : ChevalleyExceptionalModel (L ⧸ aschbacherSolvableCore 3 L) .G2 2 f) {a : G}
    (ha3 : a ^ 3 = 1) (hout : InducesOuterTheta a L) : Alt47 L a := by
  have hf3 : 3 ≤ 2 ^ f := h.1.2.2.2
  obtain ⟨K, _, _, hK, ⟨E⟩⟩ := exists_mulEquiv_adjointGroup_G2 h
  have : Fintype K := Fintype.ofFinite K
  have hf1 : 1 ≤ f := h.1.2.1
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hK])
  have hK3 : ringChar K ≠ 3 := by
    rw [ringChar.eq K 2]
    norm_num
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    rcases Nat.lt_or_ge f 2 with h2 | h2
    · obtain rfl : f = 1 := by omega
      norm_num at hf3
    · calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h2
  have hkind := inducesKindG2_field L hK3 hK4 ha3 hout E
  rcases Nat.even_or_odd f with hev | hodd
  · obtain ⟨k, rfl⟩ := hev
    have hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥ :=
      center_eq_bot_of_mulEquiv E (center_adjointGroup_eq_bot (τ := Tag.G2) (K := K))
    have h' : ChevalleyExceptionalModel (L ⧸ aschbacherSolvableCore 3 L) .G2 2 (2 * k) := by
      rwa [two_mul]
    exact (false_of_hasLocalWitness_inducedAutHom hG h3 ha3 hout hZ (MulEquiv.refl _) fun ha =>
      hin.witnessG2 _ k h' _ (inducedAutHom_pow_eq_one L _ ha ha3)
        ((not_isInnerAut_inducedAutHom_iff L _ ha).mpr hout)).elim
  · exact Or.inr (Or.inr (Or.inl ⟨Or.inr ⟨f, hodd, Or.inr (Or.inr (Or.inr (Or.inl h)))⟩,
      InducesStdKind.g2 K hK3 hK4 hkind⟩))

theorem alt47_of_suzuki {f : ℕ} (h : SuzukiModel (L ⧸ aschbacherSolvableCore 3 L) 2 f) {a : G}
    (ha3 : a ^ 3 = 1) (hout : InducesOuterTheta a L) : Alt47 L a := by
  obtain ⟨-, b, hb, K, _, _, hfb, hK, ⟨E⟩⟩ := id h
  have hK' : Nat.card K = 2 ^ (2 * b + 1) := by rw [hK, hfb]
  exact Or.inr (Or.inr (Or.inl ⟨Or.inr ⟨f, ⟨b, hfb⟩, Or.inl h⟩,
    InducesStdKind.sz b K hb hK' (inducesKindSz_field L hb hK' ha3 hout E)⟩))

theorem alt47_of_ree
    (hin : Inputs47NoD4) {f : ℕ}
    (h : ReeTitsModel (L ⧸ aschbacherSolvableCore 3 L) .twistedF4 2 f) {a : G}
    (ha3 : a ^ 3 = 1) (hout : InducesOuterTheta a L) : Alt47 L a := by
  obtain ⟨-, b, hb, hfb, K, _, _, _, hK, ⟨E⟩⟩ := exists_mulEquiv_reeGamma h
  exact Or.inr (Or.inr (Or.inl ⟨Or.inr ⟨f, ⟨b, hfb⟩, Or.inr (Or.inr (Or.inr (Or.inr h)))⟩,
    InducesStdKind.largeRee b hb K hK
      (inducesKindLargeRee_field L hb hK (hin.reeLang b K hb hK) ha3 hout E)⟩))

theorem false_of_tits
    (hin : Inputs47NoD4) {f : ℕ}
    (h : ReeTitsModel (L ⧸ aschbacherSolvableCore 3 L) .Tits 2 f) {a : G}
    (ha3 : a ^ 3 = 1) (hout : InducesOuterTheta a L) : False :=
  false_of_cubeInner (MulEquiv.refl _) (cubeInner_of_not_three_dvd_card_outer (hin.outTits _ f h))
    ha3 hout

section Triality

variable {K : Type} [Field K] [Finite K] {σ : K ≃+* K}

omit [Finite K] in
theorem ne_one_of_frobenius_cube {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 3)
    (hσ : ∀ c, σ c = c ^ 2 ^ f) : σ ≠ 1 := by
  obtain ⟨σ', hσ', hord, -⟩ :=
    finite_graph_field_parameter_fields TwistTag.D4 Nat.prime_two hf K hK
  have : σ = σ' := RingEquiv.ext fun c => by rw [hσ, hσ']
  intro h1
  rw [← this, h1, orderOf_one] at hord
  exact absurd hord (by decide)

theorem not_isInnerAut_of_isStdGraphFieldConj {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ 2 ^ f)
    {γ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)}
    (h : IsStdGraphFieldConj σ γ) : ¬ IsInnerAut γ := by
  have hσ1 := ne_one_of_frobenius_cube hf hK hσ
  have hin0 : ¬ IsInnerAut (fieldActor (t := TwistTag.D4) σ σ) := fun hin =>
    hσ1 ((isInnerAut_fieldActor_iff hf hK hσ).mp hin)
  obtain ⟨β, rfl | rfl⟩ := h
  · rw [isInnerAut_conj_iff]
    exact hin0
  · rw [isInnerAut_conj_iff]
    intro hin
    have h2 := Subgroup.inv_mem _ hin
    rw [inv_inv] at h2
    exact hin0 h2

end Triality

theorem alt47_of_trialityD4 (hin : Inputs47) (hG : SectionFourHyp G)
    (h3 : 3 ∣ Nat.card (Subgroup.center G)) {f : ℕ}
    (h : ChevalleyExceptionalModel (L ⧸ aschbacherSolvableCore 3 L) .trialityD4 2 f) {a : G}
    (ha3 : a ^ 3 = 1) (hout : InducesOuterTheta a L) : Alt47 L a := by
  have hf1 : 1 ≤ f := h.1.2.1
  obtain ⟨K, _, _, σ, hK, hσ, ⟨E⟩⟩ := exists_mulEquiv_graphFixedRootGroup_D4 h
  have hkind := inducesKindTriality_graphField hf1 hK hσ L ha3 hout E
  obtain ⟨ha, hnot⟩ := id hout
  set τ := inducedAutHom L E ⟨a, ha⟩ with hτdef
  have hτ3 : τ ^ 3 = 1 := inducedAutHom_pow_eq_one L E ha ha3
  have hτin : ¬ IsInnerAut τ := (not_isInnerAut_inducedAutHom_iff L E ha).mpr hout
  rcases Nat.even_or_odd f with hev | hodd
  ·
    obtain ⟨k, rfl⟩ := hev
    have hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥ :=
      center_eq_bot_of_mulEquiv E (exceptional_fixed_center_trivial TwistTag.D4 K σ)
    have h' : ChevalleyExceptionalModel (L ⧸ aschbacherSolvableCore 3 L) .trialityD4 2 (2 * k) :=
      by rwa [two_mul]
    exact (false_of_hasLocalWitness_inducedAutHom hG h3 ha3 hout hZ (MulEquiv.refl _) fun ha' =>
      hin.witnessD4 _ k h' _ (inducedAutHom_pow_eq_one L _ ha' ha3)
        ((not_isInnerAut_inducedAutHom_iff L _ ha').mpr hout)).elim
  ·
    refine Or.inr (Or.inr (Or.inr (Or.inr ⟨f, hodd, h,
      InducesStdKind.triality f hf1 K hK σ hσ hkind, ?_⟩)))
    rcases hin.classesD4 f hodd K σ hK hσ τ hτ3 hτin with ⟨β, hβ⟩ | ⟨γ, y, hγ, hγy, hy3, hτγ, hPGU⟩
    · exact Or.inl (isoGTwoEven_barCentralizer_of_conj_fieldActor hf1 hK hσ E ha β hβ)
    ·
      set ybar := E.symm y with hybar
      have hτy : τ y = y := by rw [hτγ, MulAut.mul_apply, MulAut.conj_apply, mul_inv_cancel_right,
        hγy]
      have hybarC : ybar ∈ Sec8.barCentralizer (Subgroup.zpowers a) L := by
        rw [mem_barCentralizer_zpowers_iff ha]
        have h1 : τ y = E (thetaQuotMulAut L (compAction L ⟨a, ha⟩) (E.symm y)) := rfl
        rw [hτy] at h1
        rw [hybar]
        exact (E.symm_apply_eq.mpr h1).symm
      have hybar3 : orderOf ybar = 3 := by
        rw [hybar, MulEquiv.orderOf_eq]
        exact hy3
      obtain ⟨x, hxL, hxa, hx3, hxy⟩ := exists_lift_of_mem_barCentralizer ha ha3 hybarC hybar3
      have hxN : x⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
        Subgroup.inv_mem _ (Subgroup.le_normalizer hxL)
      have hσN : a * x⁻¹ ∈ Subgroup.normalizer (L : Set G) := Subgroup.mul_mem _ ha hxN
      have hindx : inducedAutHom L E ⟨x⁻¹, hxN⟩ = (MulAut.conj y)⁻¹ := by
        rw [inducedAutHom_apply, thetaQuotMulAut_compAction_of_mem (Subgroup.inv_mem _ hxL) hxN,
          congr_mulAutConj, ← map_inv]
        congr 1
        have : (⟨x⁻¹, Subgroup.inv_mem _ hxL⟩ : L) = (⟨x, hxL⟩ : L)⁻¹ := rfl
        rw [this, map_inv, hxy, hybar, map_inv, MulEquiv.apply_symm_apply]
      have hindσ : inducedAutHom L E ⟨a * x⁻¹, hσN⟩ = γ := by
        have : (⟨a * x⁻¹, hσN⟩ : Subgroup.normalizer (L : Set G)) = ⟨a, ha⟩ * ⟨x⁻¹, hxN⟩ := rfl
        rw [this, map_mul, hindx, ← hτdef, hτγ, mul_inv_cancel_right]
      have hγin := not_isInnerAut_of_isStdGraphFieldConj hf1 hK hσ hγ
      have hσout : InducesOuterTheta (a * x⁻¹) L :=
        (not_isInnerAut_inducedAutHom_iff L E hσN).mp (by rw [hindσ]; exact hγin)
      have hσ3 : (a * x⁻¹) ^ 3 = 1 := by
        have hc : Commute a x⁻¹ := (show Commute x a from hxa).symm.inv_right
        have hx3' : x ^ 3 = 1 := by
          rw [← hx3]
          exact pow_orderOf_eq_one x
        rw [hc.mul_pow, ha3, one_mul, inv_pow, hx3', inv_one]
      obtain ⟨β, hβ⟩ := hγ
      refine Or.inr ⟨a * x⁻¹, x, by group, InducesStdKind.triality f hf1 K hK σ hσ
        (inducesKindTriality_graphField hf1 hK hσ L hσ3 hσout E),
        isoGTwoEven_barCentralizer_of_conj_fieldActor hf1 hK hσ E hσN β (by rw [hindσ]; exact hβ),
        hxL, hx3, ?_, ?_⟩
      · calc x * (a * x⁻¹) = x * a * x⁻¹ := by group
          _ = a * x * x⁻¹ := by rw [hxa]
          _ = a * x⁻¹ * x := by group
      · rw [barCentralizer_zpowers_eq_autFix ha]
        obtain ⟨K', hK'f, hK'fin, hK'c, ⟨φ⟩⟩ := hPGU
        exact ⟨K', hK'f, hK'fin, hK'c, ⟨(autFixCongrEquiv E _).symm.trans φ⟩⟩

end CFSG.RankThree.PartTwo.Sec4
