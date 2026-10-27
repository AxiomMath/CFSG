module

public import CFSG.RankThree.PartTwo.Sec18.Item185OuterCensus
public import CFSG.RankThree.PartTwo.Sec18.Item185OuterSpU4
import CFSG.RankThree.PartTwo.Sec18.Item185PGL3
import CFSG.RankThree.PartTwo.Sec8.Item812Res7ProofD4N
import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofEvenDesc
import CFSG.RankThree.PartTwo.Sec8.Item8KFactsProofOuterPair
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieG2
import CFSG.RankThree.PartTwo.Sec11.KS11Lie3ProofEight
import CFSG.Quasithin.Background.SmithC27RTypeU33
import CFSG.Mathlib.Arithmetic.TwoPowModThree

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item185Proof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.RankThree.PartTwo.Sec19.SimsC198 (RankHyp Alt42Seven)
open CFSG.RankThree.PartTwo.Sec4.RonanK429 (NoE27 AutNoE27)

@[expose] def GapReeF4 : Prop :=
  ∀ (m : ℕ) (hv : (TauCeti.LieTypeIndex.reeF4 m).Valid) (X : Type) [Group X]
    (_ : X ≃* (TauCeti.CFSGIndex.lie ⟨.reeF4 m, hv⟩).Group),
    ∀ σ : MulAut X, σ ∉ innerAut X → σ ^ 3 = 1 → FixedFactsAt σ

section Exceptional


private theorem exc_ringChar_two {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) : ringChar K = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := n) (by rwa [← Nat.card_eq_fintype_card])
  exact ringChar.eq K 2

private theorem exc_center_eq_bot_of_mulEquiv {G H : Type} [Group G] [Group H] (e : G ≃* H)
    (h : Subgroup.center G = ⊥) : Subgroup.center H = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  rw [Subgroup.mem_bot]
  have hx : e.symm y ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact Subgroup.mem_center_iff.mp hy (e g)
  rw [h, Subgroup.mem_bot] at hx
  have hy1 := congrArg e hx
  rwa [MulEquiv.apply_symm_apply, map_one] at hy1

private theorem exc_commutator_top_equiv {L : Type} [Group L] (G : Subgroup L) :
    Nonempty (↥(⁅(⊤ : Subgroup ↥G), (⊤ : Subgroup ↥G)⁆ : Subgroup ↥G) ≃*
      ↥(⁅G, G⁆ : Subgroup L)) := by
  have htop : (⊤ : Subgroup ↥G).map G.subtype = G := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hmap : (⁅(⊤ : Subgroup ↥G), (⊤ : Subgroup ↥G)⁆ : Subgroup ↥G).map G.subtype = ⁅G, G⁆ := by
    rw [Subgroup.map_commutator, htop]
  exact ⟨(Subgroup.equivMapOfInjective _ G.subtype Subtype.val_injective).trans
    (MulEquiv.subgroupCongr hmap)⟩

private theorem exc_derived_quasithin_two {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2) :
    ∃ D0 : Subgroup ↥(CFSG.Open.quasithinG2 F),
      D0 = ⁅(⊤ : Subgroup ↥(CFSG.Open.quasithinG2 F)), (⊤ : Subgroup ↥(CFSG.Open.quasithinG2 F))⁆ ∧
        D0.Normal ∧ IsSimpleGroup ↥D0 ∧ Nat.card ↥D0 = 6048 := by
  have hC : IsSimpleGroup ↥⁅CFSG.Open.quasithinG2 F, CFSG.Open.quasithinG2 F⁆ :=
    CFSG.Quasithin.SmithC27.isSimpleGroup_g2Derived hF
  have hCc : Nat.card ↥⁅CFSG.Open.quasithinG2 F, CFSG.Open.quasithinG2 F⁆ = 6048 :=
    CFSG.Quasithin.B42U33.card_of_b42TypeU33
      (CFSG.Quasithin.SmithC27.b42TypeU33_of_equiv hF (MulEquiv.refl _))
  obtain ⟨φ⟩ := exc_commutator_top_equiv (CFSG.Open.quasithinG2 F)
  exact ⟨⁅(⊤ : Subgroup ↥(CFSG.Open.quasithinG2 F)), (⊤ : Subgroup ↥(CFSG.Open.quasithinG2 F))⁆,
    rfl, inferInstance, φ.isSimpleGroup, (Nat.card_congr φ.toEquiv).trans hCc⟩

private theorem exc_not_isSimpleGroup_g2_two {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2)
    (hS : IsSimpleGroup ↥(CFSG.Open.quasithinG2 F)) : False := by
  obtain ⟨D0, -, hDn, -, hDc⟩ := exc_derived_quasithin_two hF
  have hG : Nat.card ↥(CFSG.Open.quasithinG2 F) = 12096 := by
    obtain ⟨φ⟩ :=
      CFSG.RankThree.PartTwo.Sec11.KS11Lie3Proof.nonempty_adjointGroup_g2_mulEquiv_quasithinG2 hF
    rw [← Nat.card_congr φ.toEquiv,
      CFSG.ComponentClassification.ExcSelector.card_adjointGroup_G2_two hF]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal D0 with h | h
  · rw [h, Subgroup.card_bot] at hDc
    norm_num at hDc
  · rw [h, Subgroup.card_top, hG] at hDc
    norm_num at hDc

private theorem exc_hnsc_quasithin_two {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2) :
    HasNormalSimpleCentralizer ↥(CFSG.Open.quasithinG2 F) := by
  obtain ⟨D0, hD, hDn, hDs, hDc⟩ := exc_derived_quasithin_two hF
  have hZ : Subgroup.center ↥(CFSG.Open.quasithinG2 F) = ⊥ := by
    obtain ⟨φ⟩ :=
      CFSG.RankThree.PartTwo.Sec11.KS11Lie3Proof.nonempty_adjointGroup_g2_mulEquiv_quasithinG2 hF
    exact exc_center_eq_bot_of_mulEquiv φ
      (CFSG.LieType.Chevalley.center_adjointGroup_eq_bot_field CFSG.Blueprint.Chevalley.Tag.G2 F)
  have hnab : ¬ ∀ x y : ↥D0, x * y = y * x := by
    intro hc
    letI : CommGroup ↥D0 := { (inferInstance : Group ↥D0) with mul_comm := fun a b => hc a b }
    have hp := Group.is_simple_iff_prime_card.mp hDs
    rw [hDc] at hp
    norm_num at hp
  have hZD0 : Subgroup.center ↥D0 = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥D0) with h | h
    · exact h
    · exfalso
      apply hnab
      intro x y
      have hy : y ∈ Subgroup.center ↥D0 := by
        rw [h]
        exact Subgroup.mem_top y
      exact Subgroup.mem_center_iff.mp hy x
  unfold HasNormalSimpleCentralizer
  refine ⟨D0, hDn, hDs, hnab, ?_⟩
  rw [eq_bot_iff]
  intro c hcC
  rw [Subgroup.mem_bot]
  have hcZ : c ∈ Subgroup.center ↥(CFSG.Open.quasithinG2 F) := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hgcg : g * c * g⁻¹ ∈ Subgroup.centralizer (D0 : Set ↥(CFSG.Open.quasithinG2 F)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have h' : g⁻¹ * h * g⁻¹⁻¹ ∈ D0 := hDn.conj_mem h hh g⁻¹
      have hcomm := Subgroup.mem_centralizer_iff.mp hcC (g⁻¹ * h * g⁻¹⁻¹) h'
      calc h * (g * c * g⁻¹) = g * ((g⁻¹ * h * g⁻¹⁻¹) * c) * g⁻¹ := by group
        _ = g * (c * (g⁻¹ * h * g⁻¹⁻¹)) * g⁻¹ := by rw [hcomm]
        _ = g * c * g⁻¹ * h := by group
    have hxC : g * c * g⁻¹ * c⁻¹ ∈ Subgroup.centralizer (D0 : Set ↥(CFSG.Open.quasithinG2 F)) :=
      mul_mem hgcg (inv_mem hcC)
    have hxD : g * c * g⁻¹ * c⁻¹ ∈ D0 := by
      rw [hD]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top c)
    have hx1 : g * c * g⁻¹ * c⁻¹ = 1 := by
      have hmem : (⟨g * c * g⁻¹ * c⁻¹, hxD⟩ : ↥D0) ∈ Subgroup.center ↥D0 := by
        rw [Subgroup.mem_center_iff]
        intro z
        apply Subtype.ext
        have hz := Subgroup.mem_centralizer_iff.mp hxC z.1 z.2
        simp only [Subgroup.coe_mul]
        exact hz
      rw [hZD0, Subgroup.mem_bot] at hmem
      exact congrArg Subtype.val hmem
    have h1 : g * c * g⁻¹ = c := mul_inv_eq_one.mp hx1
    calc g * c = g * c * g⁻¹ * g := by group
      _ = c * g := by rw [h1]
  rw [hZ, Subgroup.mem_bot] at hcZ
  exact hcZ

private theorem exc_hnsc_adjointG2 {F : Type} [Field F] [Finite F] (hF : 2 ≤ Nat.card F) :
    HasNormalSimpleCentralizer
      (CFSG.Blueprint.Chevalley.adjointGroup CFSG.Blueprint.Chevalley.Tag.G2 F) := by
  unfold HasNormalSimpleCentralizer
  by_cases h3 : 3 ≤ Nat.card F
  · haveI hs : IsSimpleGroup
        (CFSG.Blueprint.Chevalley.adjointGroup CFSG.Blueprint.Chevalley.Tag.G2 F) :=
      CFSG.QuasithinUnique.Id2519.isSimpleGroup_adjointGroup_g2 h3
    haveI : Group.IsPerfect
        (CFSG.Blueprint.Chevalley.adjointGroup CFSG.Blueprint.Chevalley.Tag.G2 F) :=
      CFSG.LieType.Steinberg.Adjoint.isPerfect_g2_of_three_le_card (K := F) h3
    haveI := hs.toNontrivial
    refine ⟨⊤, inferInstance, Subgroup.topEquiv.isSimpleGroup, ?_, ?_⟩
    · intro hc
      apply Group.IsPerfect.not_isMulCommutative
        (CFSG.Blueprint.Chevalley.adjointGroup CFSG.Blueprint.Chevalley.Tag.G2 F)
      exact ⟨⟨fun x y => congrArg Subtype.val
        (hc ⟨x, Subgroup.mem_top x⟩ ⟨y, Subgroup.mem_top y⟩)⟩⟩
    · rw [Subgroup.coe_top, Subgroup.centralizer_univ]
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center
          (CFSG.Blueprint.Chevalley.adjointGroup CFSG.Blueprint.Chevalley.Tag.G2 F)) with h0 | h0
      · exact h0
      · exfalso
        apply Group.IsPerfect.not_isMulCommutative
          (CFSG.Blueprint.Chevalley.adjointGroup CFSG.Blueprint.Chevalley.Tag.G2 F)
        have hy : ∀ y : ↥(CFSG.Blueprint.Chevalley.adjointGroup CFSG.Blueprint.Chevalley.Tag.G2 F),
            y ∈ Subgroup.center
              ↥(CFSG.Blueprint.Chevalley.adjointGroup CFSG.Blueprint.Chevalley.Tag.G2 F) := by
          intro y
          rw [h0]
          exact Subgroup.mem_top y
        exact ⟨⟨fun x y => Subgroup.mem_center_iff.mp (hy y) x⟩⟩
  · have hF2 : Nat.card F = 2 := by omega
    obtain ⟨φ⟩ :=
      CFSG.RankThree.PartTwo.Sec11.KS11Lie3Proof.nonempty_adjointGroup_g2_mulEquiv_quasithinG2 hF2
    exact HasNormalSimpleCentralizer.of_mulEquiv φ.symm (exc_hnsc_quasithin_two hF2)

private theorem exc_fixedSubgroup_conj {S : Type} [Group S] (κ γ : MulAut S) :
    Nonempty (fixedSubgroup (κ * γ * κ⁻¹) ≃* fixedSubgroup γ) := by
  have hmap : (fixedSubgroup γ).map κ.toMonoidHom = fixedSubgroup (κ * γ * κ⁻¹) := by
    ext x
    rw [Subgroup.mem_map_equiv]
    constructor
    · intro h
      have h' : γ (κ.symm x) = κ.symm x := h
      show κ (γ (κ.symm x)) = x
      rw [h', MulEquiv.apply_symm_apply]
    · intro h
      have h' : κ (γ (κ.symm x)) = x := h
      show γ (κ.symm x) = κ.symm x
      apply κ.injective
      rw [h', MulEquiv.apply_symm_apply]
  exact ⟨(MulEquiv.subgroupCongr hmap).symm.trans
    (Subgroup.equivMapOfInjective (fixedSubgroup γ) κ.toMonoidHom κ.injective).symm⟩

private theorem exc_fixedSubgroup_inv {S : Type} [Group S] (γ : MulAut S) :
    fixedSubgroup γ⁻¹ = fixedSubgroup γ := by
  ext x
  show γ.symm x = x ↔ γ x = x
  rw [MulEquiv.symm_apply_eq]
  exact eq_comm

private theorem exc_fixed_g2_iso {K : Type} [Field K] [Finite K] (hchar : ringChar K = 2)
    (τ : K ≃+* K) :
    Nonempty (fixedSubgroup (CFSG.RankThree.PartTwo.KFacts.g2FieldHom K τ) ≃*
      CFSG.Blueprint.Chevalley.adjointGroup CFSG.Blueprint.Chevalley.Tag.G2
        ↥(CFSG.LieType.Chevalley.fixSubfield τ)) := by
  have hrange : fixedSubgroup (CFSG.RankThree.PartTwo.KFacts.g2FieldHom K τ) =
      (CFSG.RankThree.PartTwo.KFacts.g2Incl τ).range := by
    ext h
    exact (CFSG.RankThree.PartTwo.KFacts.mem_range_g2Incl_iff hchar τ h).symm
  exact ⟨(MulEquiv.subgroupCongr hrange).trans
    (MonoidHom.ofInjective (CFSG.RankThree.PartTwo.KFacts.g2Incl_injective τ)).symm⟩

private theorem exc_two_le_card_fixSubfield {K : Type} [Field K] [Finite K] (τ : K ≃+* K) :
    2 ≤ Nat.card ↥(CFSG.LieType.Chevalley.fixSubfield τ) := by
  have : 1 < Nat.card ↥(CFSG.LieType.Chevalley.fixSubfield τ) := Finite.one_lt_card
  omega

private theorem exc_fixedFacts_of_mulEquiv {S : Type} [Group S] {σ : MulAut S} {G : Type} [Group G]
    (e : G ≃* fixedSubgroup σ) (h : HasNormalSimpleCentralizer G) : FixedFactsAt σ := by
  unfold FixedFactsAt
  left
  exact HasNormalSimpleCentralizer.of_mulEquiv e h

private theorem exc_triality_fixedFacts {K : Type} [Field K] [Finite K] {m : ℕ} {σ : K ≃+* K}
    (hn : 2 ≤ m) (hK : Nat.card K = (2 ^ m) ^ 3) (hσ : ∀ c, σ c = c ^ 2 ^ m)
    {β : MulAut ↥(CFSG.LieType.Chevalley.graphFixedRootGroup
      CFSG.Blueprint.Chevalley.TwistTag.D4 K σ.toRingHom)}
    (hβ : β ∉ innerAut _) (hβ3 : β ^ 3 = 1) : FixedFactsAt β := by
  have hf : 1 ≤ m := by omega
  have hq2 : 2 < 2 ^ m :=
    calc (2 : ℕ) < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hn
  have hchar : ringChar K = 2 := exc_ringChar_two (n := m * 3) (by rw [hK, pow_mul])
  rcases Sec8.Item8KFacts2Proof.isStdGraphFieldConj_or_nonempty_autFix_equiv hf hK hσ hβ3 hβ with
    ⟨b, hb | hb⟩ | hB
  · subst hb
    obtain ⟨φ1⟩ := exc_fixedSubgroup_conj b
      (CFSG.LieType.Chevalley.fieldActor (t := CFSG.Blueprint.Chevalley.TwistTag.D4) σ σ)
    obtain ⟨φ2⟩ :=
      CFSG.RankThree.PartTwo.KFacts.nonempty_fixedPoints_fieldActor_mulEquiv_g2 (σ := σ) hchar
    exact exc_fixedFacts_of_mulEquiv (φ1.trans φ2).symm
      (exc_hnsc_adjointG2 (exc_two_le_card_fixSubfield σ))
  · subst hb
    obtain ⟨φ1⟩ := exc_fixedSubgroup_conj b
      (CFSG.LieType.Chevalley.fieldActor (t := CFSG.Blueprint.Chevalley.TwistTag.D4) σ σ)⁻¹
    obtain ⟨φ2⟩ :=
      CFSG.RankThree.PartTwo.KFacts.nonempty_fixedPoints_fieldActor_mulEquiv_g2 (σ := σ) hchar
    exact exc_fixedFacts_of_mulEquiv
      (φ1.trans ((MulEquiv.subgroupCongr (exc_fixedSubgroup_inv
        (CFSG.LieType.Chevalley.fieldActor (t := CFSG.Blueprint.Chevalley.TwistTag.D4) σ σ))).trans
          φ2)).symm
      (exc_hnsc_adjointG2 (exc_two_le_card_fixSubfield σ))
  · obtain ⟨φ⟩ := hB
    have hfix : Sec4.autFix β = fixedSubgroup β := Subgroup.ext fun x => Iff.rfl
    rcases Nat.even_or_odd m with heven | hodd
    · obtain ⟨F, hF, hFin, hcard, ⟨e'⟩⟩ :=
        Sec8.kF82D4SecondCentY0Even_holds m heven hf K σ hK hσ
      have hPi : Sec4.PiField true 2 m F := ⟨Nat.prime_two, hf, hcard⟩
      have hP := hasNormalSimpleCentralizer_projImage_glPi hPi hq2
        (CFSG.two_pow_mod_three_of_even heven)
      exact exc_fixedFacts_of_mulEquiv (MulEquiv.subgroupCongr hfix)
        (HasNormalSimpleCentralizer.of_mulEquiv (φ.trans e').symm hP)
    · obtain ⟨F, hF, hFin, hcard, ⟨e'⟩⟩ :=
        Sec8.kF82D4SecondCentY0_holds m hodd K σ hK hσ
      have hPi : Sec4.PiField false 2 m F := ⟨Nat.prime_two, hf, hcard⟩
      have hP := hasNormalSimpleCentralizer_projImage_glPi hPi hq2
        (CFSG.two_pow_mod_three_of_odd hodd)
      exact exc_fixedFacts_of_mulEquiv (MulEquiv.subgroupCongr hfix)
        (HasNormalSimpleCentralizer.of_mulEquiv (φ.trans e').symm hP)

private theorem exc_fixedFacts_g2_big {K : Type} [Field K] [Finite K] (hchar : ringChar K = 2)
    (hbig : 4 ≤ Nat.card K)
    {σ : MulAut (CFSG.Blueprint.Chevalley.adjointGroup CFSG.Blueprint.Chevalley.Tag.G2 K)}
    (hσ : σ ∉ innerAut _) (hσ3 : σ ^ 3 = 1) : FixedFactsAt σ := by
  have hK3 : ringChar K ≠ 3 := by rw [hchar]; norm_num
  obtain ⟨τ, -, k, hk⟩ :=
    CFSG.RankThree.PartTwo.KFacts.g2_order_three_field_descent hK3 hbig hσ3 hσ
  subst hk
  obtain ⟨φ1⟩ := exc_fixedSubgroup_conj (MulAut.conj k)
    (CFSG.RankThree.PartTwo.KFacts.g2FieldHom K τ)
  obtain ⟨φ2⟩ := exc_fixed_g2_iso hchar τ
  exact exc_fixedFacts_of_mulEquiv (φ1.trans φ2).symm
    (exc_hnsc_adjointG2 (exc_two_le_card_fixSubfield τ))

theorem noOmega_isoGTwo_two {X : Type} [Group X] [Finite X] (hS : IsSimpleGroup X)
    {q : TauCeti.PrimePower} (hq2 : q.p = 2) (h : Sec4.IsoGTwo X q) : NoOmega X := by
  obtain ⟨K, hKf, hKfin, hKc, ⟨φ⟩⟩ := Sec8.Item8KFactsProof.isoGTwoEven_of_isoGTwo hq2 rfl h
  have hchar : ringChar K = 2 := exc_ringChar_two hKc
  have hn1 := q.exponent_pos
  rcases Nat.lt_or_ge (Nat.card K) 4 with hsmall | hbig
  ·
    have h1 : q.exponent = 1 := by
      by_contra hne
      have h2 : 2 ≤ q.exponent := by omega
      have h4 : 4 ≤ 2 ^ q.exponent :=
        calc (4 : ℕ) = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) h2
      rw [← hKc] at h4
      exact absurd h4 (not_le.mpr hsmall)
    have hF : Nat.card K = 2 := by rw [hKc, h1, pow_one]
    obtain ⟨ψ⟩ :=
      CFSG.RankThree.PartTwo.Sec11.KS11Lie3Proof.nonempty_adjointGroup_g2_mulEquiv_quasithinG2 hF
    exact (exc_not_isSimpleGroup_g2_two hF (φ.trans ψ).symm.isSimpleGroup).elim
  ·
    haveI := Finite.of_surjective φ φ.surjective
    exact NoOmega.of_mulEquiv φ (noOmega_of_fixed_facts fun σ hσ hσ3 =>
      exc_fixedFacts_g2_big hchar hbig hσ hσ3)

theorem noOmega_trialityD4_two {X : Type} [Group X] [Finite X] {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid) (hq2 : q.p = 2) (hn : 2 ≤ q.exponent)
    (e : X ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group) : NoOmega X := by
  obtain ⟨-, K, hKf, hKfin, σ, hK, hσ, ⟨eY⟩⟩ :=
    Sec8.Item812Res7.exists_trialityD4_model
      (⟨q, hv, hq2, rfl, ⟨e⟩⟩ : Sec8.IsoTrialityD4 X q.exponent)
  haveI := Finite.of_surjective eY eY.surjective
  exact NoOmega.of_mulEquiv eY (noOmega_of_fixed_facts fun β hβ hβ3 =>
    exc_triality_fixedFacts hn hK hσ hβ hβ3)

theorem noOmega_suzuki {X : Type} [Group X] [Finite X] {m : ℕ}
    (hv : (TauCeti.LieTypeIndex.suzuki m).Valid)
    (e : X ≃* (TauCeti.CFSGIndex.lie ⟨.suzuki m, hv⟩).Group) : NoOmega X := by
  intro σ _ _ B _ hBc _
  have h3 : ¬ 3 ∣ Nat.card X := by
    obtain ⟨-, a, -, F, _, _, hf, hK', ⟨θ⟩⟩ := Sec4.Census.suzukiModel_of_index m hv
    have hK : Nat.card F = 2 ^ (2 * a + 1) := by rw [hK', hf]
    rw [Nat.card_congr (e.trans θ).toEquiv]
    exact KFacts.not_three_dvd_card_suzukiGroup hK
  apply h3
  have h9 : Nat.card B ∣ Nat.card X := Subgroup.card_subgroup_dvd_card B
  rw [hBc] at h9
  exact (show 3 ∣ 9 by norm_num).trans h9

theorem noOmega_reeF4 (hK4 : GapReeF4) {X : Type} [Group X] [Finite X] {m : ℕ}
    (hv : (TauCeti.LieTypeIndex.reeF4 m).Valid)
    (e : X ≃* (TauCeti.CFSGIndex.lie ⟨.reeF4 m, hv⟩).Group) : NoOmega X :=
  noOmega_of_fixed_facts fun σ h1 h3 => hK4 m hv X e σ h1 h3

theorem not_three_dvd_outer_tits {X : Type} [Group X] (hv : TauCeti.LieTypeIndex.tits.Valid)
    (e : X ≃* (TauCeti.CFSGIndex.lie ⟨.tits, hv⟩).Group) : ¬ 3 ∣ Nat.card (Outer X) := by
  have hmodel : CFSG.Blueprint.ReeTitsModel X .Tits 2 1 :=
    CFSG.SectionRank.reeTitsModel_of_mulEquiv e ((Sec4.Census.bridgeExceptional46).tits hv)
  rw [Sec4.card_outer_tits X 1 hmodel]
  norm_num

theorem outerCase_seven (hK1 : GapU48) (hK2 : GapL3Field) (hK3 : GapU3Field) (hK4 : GapReeF4)
    (hU38 : ∀ (X : Type) [Group X] [Finite X],
      Nonempty (X ≃* projSU 3 2 3) → NoOuterData X)
    (hD42 : ∀ (X : Type) [Group X] [Finite X], Sec4.IsSmallTwoD42 X → NoOuterData X) :
    OuterCase Alt42Seven := by
  intro X _ _ hX P A B c hd hP
  have hq := hd.quotient hX
  have hZ := center_quotient_eq_bot hX
  have hS := isSimpleGroup_quotient hX
  rcases hP with ⟨n, hn, ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩⟩ | ⟨q, hq2, hG⟩ |
    ⟨q, hv, hq2, ⟨φ⟩⟩ | ⟨m, hv, ⟨φ⟩⟩ | ⟨m, hv, ⟨φ⟩⟩ | ⟨hv, ⟨φ⟩⟩
  ·
    by_cases h1 : n = 1
    · subst h1; exact not_isSimpleGroup_projSL_two_two_one φ.symm.isSimpleGroup
    · exact noOuterData_of_noOmega hZ (NoOmega.of_mulEquiv φ
        (noOmega_projSL_two (p := 2) (e := n) (by
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)))) _ _ _ _ hq
  ·
    rcases autNoE27_or_noOmega_projSL_three_two hK2 hn with h | h
    · exact noOuterData_of_autNoE27 (autNoE27_of_mulEquiv φ h) _ _ _ _ hq
    · exact noOuterData_of_noOmega hZ (NoOmega.of_mulEquiv φ h) _ _ _ _ hq
  ·
    by_cases h1 : n = 1
    · subst h1; exact not_isSimpleGroup_projSU_three_two_one φ.symm.isSimpleGroup
    · by_cases h3 : n = 3
      · subst h3; exact hU38 _ ⟨φ⟩ _ _ _ _ hq
      · rcases autNoE27_or_noOmega_projSU_three_two hK3 (by omega) h3 with h | h
        · exact noOuterData_of_autNoE27 (autNoE27_of_mulEquiv φ h) _ _ _ _ hq
        · exact noOuterData_of_noOmega hZ (NoOmega.of_mulEquiv φ h) _ _ _ _ hq
  ·
    by_cases h1 : n = 1
    · subst h1; exact not_isSimpleGroup_projSp_two_two_one φ.symm.isSimpleGroup
    · exact noOuterData_of_noOmega hZ (NoOmega.of_mulEquiv φ (noOmega_projSp_two_two (by omega)))
        _ _ _ _ hq
  ·
    by_cases h1 : n = 1
    · subst h1
      exact noOuterData_of_not_three_dvd_outer
        (not_three_dvd_outer_of_mulEquiv φ not_three_dvd_outer_projSU_four_two_one) _ _ _ _ hq
    · by_cases h3 : n = 3
      · subst h3
        exact noOuterData_of_noOmega hZ (NoOmega.of_mulEquiv φ (noOmega_projSU_four_two_three hK1))
          _ _ _ _ hq
      · exact Sec19.SimsC198.false_of_rankHyp_PSU4_two hX hn h1 h3 φ
  ·
    exact noOuterData_of_noOmega hZ (noOmega_isoGTwo_two hS hq2 hG) _ _ _ _ hq
  ·
    by_cases h1 : q.exponent = 1
    · exact hD42 _ ⟨q, hv, hq2, h1, ⟨φ⟩⟩ _ _ _ _ hq
    · have hpos : 1 ≤ q.exponent := by
        have := q.exponent_pos
        omega
      exact noOuterData_of_noOmega hZ (noOmega_trialityD4_two hv hq2 (by omega) φ) _ _ _ _ hq
  ·
    exact noOuterData_of_noOmega hZ (noOmega_suzuki hv φ) _ _ _ _ hq
  ·
    exact noOuterData_of_noOmega hZ (noOmega_reeF4 hK4 hv φ) _ _ _ _ hq
  ·
    exact noOuterData_of_not_three_dvd_outer
      (not_three_dvd_outer_tits hv φ) _ _ _ _ hq

end Exceptional

end CFSG.RankThree.PartTwo.Sec18.Item185Proof
