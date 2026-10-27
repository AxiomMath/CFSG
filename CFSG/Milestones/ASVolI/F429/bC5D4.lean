module

public import CFSG.Milestones.ASVolI.F429.bC5
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8D4Torus
public import CFSG.LieType.Chevalley.TrialityAllCharTorusCoordinates
public import CFSG.LieType.Chevalley.GraphFixedRankOneImage
public import CFSG.LieType.Chevalley.GraphFixedOrbitParametrization
public import CFSG.LieType.Chevalley.GraphFixedRankOneScalar
public import CFSG.LieType.Chevalley.GraphFixedParameterFields
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qLocBase
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsD4
public import Mathlib.FieldTheory.Finite.GaloisField
import CFSG.Milestones.ASVolI.F4
public import Certificates.Kernel.Sporadic.Fi22.C3151
public import CFSG.Milestones.ASVolI.F429.C8
public import CFSG.Milestones.ASVolI.F429.bC4
public import CFSG.Quasithin.Vol2.Ch5Sec1L34FiveA7
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4SpA

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.Quasithin.H13.Sec53F.BA

section Galois

theorem burnsideF429b_ringEquiv_eq_one {K : Type} [Field K] [Finite K] (F : Subfield K)
    (hF3 : Module.finrank F K = 3) {δ : K ≃+* K} (hδ : ∀ c ∈ F, δ c = c) {k : ℕ}
    (hk : δ ^ 2 ^ k = 1) : δ = 1 := by
  let δ' : K ≃ₐ[F] K := AlgEquiv.ofRingEquiv (f := δ) (fun x => hδ x x.2)
  have hcard : Nat.card (K ≃ₐ[F] K) = 3 := by rw [IsGalois.card_aut_eq_finrank, hF3]
  have h3' : δ' ^ 3 = 1 := by
    rw [← hcard]
    exact pow_card_eq_one'
  have h3 : δ ^ 3 = 1 := by
    refine RingEquiv.ext fun x => ?_
    have hx : (δ' ^ 3) x = x := by rw [h3']; rfl
    rw [pow_three, AlgEquiv.mul_apply, AlgEquiv.mul_apply] at hx
    rw [pow_three, RingAut.mul_apply, RingAut.mul_apply]
    exact hx
  have hd : orderOf δ ∣ Nat.gcd 3 (2 ^ k) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h3) (orderOf_dvd_of_pow_eq_one hk)
  have hg : Nat.gcd 3 (2 ^ k) = 1 := Nat.Coprime.pow_right k (by norm_num)
  rw [hg, Nat.dvd_one, orderOf_eq_one_iff] at hd
  exact hd

end Galois

section RankOne

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Quasithin.H13.F431.D4q.Struct


variable {K : Type} [Field K] (σ : K ≃+* K)

theorem burnsideF429b_D4_rankOne_oPPrime [CharP K 2] (a : Fin TwistTag.D4.foldedTag.rank)
    {x : ModGL TwistTag.D4.tag K} (hx : x ∈ orbitRankOneGroup TwistTag.D4 K σ.toRingHom a) :
    ∃ y ∈ oPPrime 2 ((graphFixedParabolic TwistTag.D4 K σ.toRingHom {a}).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)), (y : ModGL TwistTag.D4.tag K) = x := by
  have hPC : graphFixedParabolic TwistTag.D4 K σ.toRingHom {a} ≤
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom := graphFixedParabolic_le _ _ _ _
  have hgen : ∀ g ∈ orbitRankOneGroup TwistTag.D4 K σ.toRingHom a, g * g = 1 →
      g ∈ (oPPrime 2 ((graphFixedParabolic TwistTag.D4 K σ.toRingHom {a}).subgroupOf
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))).map
          (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype := by
    intro g hg hgg
    have hgP := CFSG.Quasithin.H13.F431.D4q.Loc.orbitRankOneGroup_le_graphFixedParabolic σ a hg
    exact ⟨⟨g, hPC hgP⟩, burnsideF429b_mem_oPPrime_of_mul_self
      (Subgroup.mem_subgroupOf.2 hgP) (Subtype.ext hgg), rfl⟩
  have hxx : ∀ c : orbitField TwistTag.D4 K σ.toRingHom a,
      (orbitX TwistTag.D4 K σ.toRingHom a c : ModGL TwistTag.D4.tag K) *
        (orbitX TwistTag.D4 K σ.toRingHom a c : ModGL TwistTag.D4.tag K) = 1 := by
    intro c
    have hc : c + c = 0 := Subtype.ext (by rw [Subfield.coe_add, CharTwo.add_self_eq_zero]; rfl)
    rw [← Subgroup.coe_mul, ← orbitX_add, hc, orbitX_zero, Subgroup.coe_one]
  have hle : orbitRankOneGroup TwistTag.D4 K σ.toRingHom a ≤
      (oPPrime 2 ((graphFixedParabolic TwistTag.D4 K σ.toRingHom {a}).subgroupOf
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))).map
          (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype := by
    rw [orbitRankOneGroup, Subgroup.closure_le]
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · exact hgen _ (Subgroup.subset_closure (Or.inl ⟨c, rfl⟩)) (hxx c)
    · refine hgen _ (Subgroup.subset_closure (Or.inr ⟨c, rfl⟩)) ?_
      show (orbitY TwistTag.D4 K σ.toRingHom a c : ModGL TwistTag.D4.tag K) *
        (orbitY TwistTag.D4 K σ.toRingHom a c : ModGL TwistTag.D4.tag K) = 1
      rw [← canonicalRep_orbitReflection_conj_orbitX]
      calc canonicalRep (coxeterSystem TwistTag.D4.tag) K (TwistTag.D4.orbitReflection a) *
            (orbitX TwistTag.D4 K σ.toRingHom a (-c) : ModGL TwistTag.D4.tag K) *
            (canonicalRep (coxeterSystem TwistTag.D4.tag) K (TwistTag.D4.orbitReflection a))⁻¹ *
          (canonicalRep (coxeterSystem TwistTag.D4.tag) K (TwistTag.D4.orbitReflection a) *
            (orbitX TwistTag.D4 K σ.toRingHom a (-c) : ModGL TwistTag.D4.tag K) *
            (canonicalRep (coxeterSystem TwistTag.D4.tag) K (TwistTag.D4.orbitReflection a))⁻¹) =
          canonicalRep (coxeterSystem TwistTag.D4.tag) K (TwistTag.D4.orbitReflection a) *
            ((orbitX TwistTag.D4 K σ.toRingHom a (-c) : ModGL TwistTag.D4.tag K) *
              (orbitX TwistTag.D4 K σ.toRingHom a (-c) : ModGL TwistTag.D4.tag K)) *
            (canonicalRep (coxeterSystem TwistTag.D4.tag) K (TwistTag.D4.orbitReflection a))⁻¹ := by
            group
        _ = 1 := by rw [hxx]; group
  obtain ⟨y, hy, hyx⟩ := hle hx
  exact ⟨y, hy, hyx⟩

theorem burnsideF429b_D4_ho_mem (hσ3 : σ ^ 3 = 1) (a : Kˣ) :
    trialityTorusHom σ (a, 1) ∈ orbitRankOneGroup TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩ := by
  rw [trialityTorusHom_eq_orbitH hσ3,
    show trialityMiddleParam (1 : (trialityFixedField K σ.toRingHom)ˣ) = 1 from Units.ext rfl,
    orbitH_one', mul_one, ← orbitRankOneHom_HSL, orbitRankOneGroup, ← orbitRankOneHom_range]
  exact ⟨_, rfl⟩

theorem burnsideF429b_D4_hm_mem (hσ3 : σ ^ 3 = 1) (b : (trialityFixedField K σ.toRingHom)ˣ) :
    trialityTorusHom σ (1, b) ∈ orbitRankOneGroup TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩ := by
  rw [trialityTorusHom_eq_orbitH hσ3,
    show trialityOuterParam hσ3 (1 : Kˣ) = 1 from Units.ext rfl,
    orbitH_one', one_mul, ← orbitRankOneHom_HSL, orbitRankOneGroup, ← orbitRankOneHom_range]
  exact ⟨_, rfl⟩

end RankOne

section Faithful

open CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.QuasithinUnique
  CFSG.QuasithinUnique.Setup.X6 CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


variable {K : Type} [Field K] [Finite K] (σ : K ≃+* K)

theorem burnsideF429b_D4_eq_one_of_fix_outer (hσ3 : σ ^ 3 = 1) [CharP K 2] (δ : K ≃+* K)
    (hfix : ∀ a : Kˣ, fieldActorHom (t := TwistTag.D4) σ δ
        ⟨trialityTorusHom σ (a, 1), trialityTorusHom_mem_graphFixedRootGroup hσ3 (a, 1)⟩ =
      ⟨trialityTorusHom σ (a, 1), trialityTorusHom_mem_graphFixedRootGroup hσ3 (a, 1)⟩) :
    δ = 1 := by
  have hsq : ∀ a : Kˣ, δ ((a : K) ^ 2) = (a : K) ^ 2 := by
    intro a
    have h1 := congrArg (fun x : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) =>
      (x : ModGL TwistTag.D4.tag K)) (hfix a)
    simp only [fieldActorHom_apply, coe_fieldActor] at h1
    have hone : trialityFixedUnit K σ 1 = 1 := map_one _
    rw [trialityTorusHom_apply, trialityOuter_mul_middle_eq, hone,
      CFSG.Quasithin.H13.Sec53F.TriD4.entry_rootDiagUnit] at h1
    have h2 := congrFun (CFSG.LieType.Chevalley.rootDiagUnit_injective h1)
      (⟨0, by decide⟩ : Fin TwistTag.D4.tag.rank)
    have h3 : Units.map δ.toRingHom.toMonoidHom (a ^ 2 * 1⁻¹) = a ^ 2 * 1⁻¹ := h2
    simpa using congrArg Units.val h3
  have hall : ∀ x : K, δ x = x := by
    intro x
    obtain ⟨r, rfl⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) x
    by_cases hr : r = 0
    · subst hr
      simp
    · simpa [sq] using hsq (Units.mk0 r hr)
  exact RingEquiv.ext hall

theorem burnsideF429b_D4_faithful_outer (hσ3 : σ ^ 3 = 1) [CharP K 2] :
    ∀ φ ∈ (fieldActorHom (t := TwistTag.D4) σ).range,
      (∀ a : Kˣ, φ ⟨trialityTorusHom σ (a, 1), trialityTorusHom_mem_graphFixedRootGroup hσ3 (a, 1)⟩ =
        ⟨trialityTorusHom σ (a, 1), trialityTorusHom_mem_graphFixedRootGroup hσ3 (a, 1)⟩) →
      φ = 1 := by
  rintro _ ⟨δ, rfl⟩ hfix
  rw [burnsideF429b_D4_eq_one_of_fix_outer σ hσ3 δ hfix, map_one]

theorem burnsideF429b_D4_fix_k (hσ3 : σ ^ 3 = 1) [CharP K 2] (δ : K ≃+* K)
    (hfix : ∀ b : (trialityFixedField K σ.toRingHom)ˣ, fieldActorHom (t := TwistTag.D4) σ δ
        ⟨trialityTorusHom σ (1, b), trialityTorusHom_mem_graphFixedRootGroup hσ3 (1, b)⟩ =
      ⟨trialityTorusHom σ (1, b), trialityTorusHom_mem_graphFixedRootGroup hσ3 (1, b)⟩) :
    ∀ c ∈ trialityFixedField K σ.toRingHom, δ c = c := by
  intro c hc
  by_cases hc0 : c = 0
  · subst hc0
    simp
  · let b : (trialityFixedField K σ.toRingHom)ˣ :=
      Units.mk0 ⟨c, hc⟩ fun h => hc0 (congrArg Subtype.val h)
    have h1 := congrArg (fun x : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) =>
      (x : ModGL TwistTag.D4.tag K)) (hfix b)
    simp only [fieldActorHom_apply, coe_fieldActor] at h1
    rw [← CFSG.ComponentClassification.RankTwoExceptional.D4.hm_eq_d4, trialityMiddleTorus,
      CFSG.Quasithin.H13.Sec53F.TriD4.entry_torusElt] at h1
    exact congrArg Units.val (burnsideF429b_torusElt_injective _ h1)

theorem burnsideF429b_D4_card_fixed {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 3)
    (hσq : ∀ c, σ.toRingHom c = c ^ (2 ^ f)) :
    Nat.card ↥(trialityFixedField K σ.toRingHom) = 2 ^ f := by
  obtain ⟨-, -, -, -, -, k, hk, hcard, -⟩ :=
    finite_graph_field_parameter_fields TwistTag.D4 Nat.prime_two hf K hK
  have hσ' : ∀ c, σ c = c ^ (2 ^ f) := hσq
  have hkeq : trialityFixedField K σ.toRingHom = k := by
    apply SetLike.ext'
    rw [hk]
    ext c
    simp [mem_trialityFixedField, hσ']
  rw [hkeq, hcard]

theorem burnsideF429b_D4_finrank {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 3)
    (hσq : ∀ c, σ.toRingHom c = c ^ (2 ^ f)) :
    Module.finrank (trialityFixedField K σ.toRingHom) K = 3 := by
  haveI := Fintype.ofFinite K
  haveI := Fintype.ofFinite ↥(trialityFixedField K σ.toRingHom)
  have h := Module.card_eq_pow_finrank (K := ↥(trialityFixedField K σ.toRingHom)) (V := K)
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK,
    burnsideF429b_D4_card_fixed σ hf hK hσq] at h
  have h2 : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  exact (Nat.pow_right_injective h2 h).symm

theorem burnsideF429b_D4_faithful_middle (hσ3 : σ ^ 3 = 1) [CharP K 2] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 3) (hσq : ∀ c, σ.toRingHom c = c ^ (2 ^ f)) :
    ∀ φ ∈ (fieldActorHom (t := TwistTag.D4) σ).range, ∀ k : ℕ, φ ^ 2 ^ k = 1 →
      (∀ b : (trialityFixedField K σ.toRingHom)ˣ,
        φ ⟨trialityTorusHom σ (1, b), trialityTorusHom_mem_graphFixedRootGroup hσ3 (1, b)⟩ =
          ⟨trialityTorusHom σ (1, b), trialityTorusHom_mem_graphFixedRootGroup hσ3 (1, b)⟩) →
      φ = 1 := by
  rintro _ ⟨δ, rfl⟩ k hk hfix
  have hk' : δ ^ 2 ^ k = 1 := burnsideF429b_D4_eq_one_of_fix_outer σ hσ3 (δ ^ 2 ^ k)
    fun a => by rw [map_pow, hk]; rfl
  have hδ := burnsideF429b_ringEquiv_eq_one _ (burnsideF429b_D4_finrank σ hf hK hσq)
    (burnsideF429b_D4_fix_k σ hσ3 δ hfix) hk'
  rw [hδ, map_one]

end Faithful

section D4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Quasithin.H13.F431.D4q.Struct


theorem burnsideF429b_D4_torus_le {K : Type} [Field K] (σ : K ≃+* K) :
    (graphFixedRootTorus TwistTag.D4 K σ.toRingHom).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ≤ Pst0 σ ⊓ Pst1 σ := by
  intro x hx
  have hxB : (x : ModGL TwistTag.D4.tag K) ∈ graphFixedRootBorel TwistTag.D4 K σ.toRingHom :=
    graphFixedRootTorus_le_graphFixedRootBorel (Subgroup.mem_subgroupOf.1 hx)
  exact ⟨Subgroup.mem_subgroupOf.2 (graphFixedRootBorel_le_graphFixedParabolic _ _ _ _ hxB),
    Subgroup.mem_subgroupOf.2 (graphFixedRootBorel_le_graphFixedParabolic _ _ _ _ hxB)⟩

theorem burnsideF429b_key1_D4tw {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .D4tw 2 f Gp M₁ M₂) :
    ∀ r ∈ M₁ ⊓ M₂, ∀ k : ℕ, r ^ 2 ^ k = 1 →
      (∀ b ∈ oPPrime 2 (Gp ⊓ M₁) ⊓ (M₁ ⊓ M₂),
        r * b * r⁻¹ * b⁻¹ ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) → r ∈ Gp := by
  haveI := hyp.normal
  obtain ⟨K, fK, finK, cK, σ, hσ3, hf1, hK, hσq, Ψ, h1, h2⟩ :=
    burnsideF429b_D4_chart hyp.toHypF_4_4g
  have hσ3' : σ ^ 3 = 1 := RingEquiv.ext fun c => (ringEquiv_pow_three_apply σ c).trans (hσ3 c)
  refine burnsideF429b_keyL_of_borelAutData hyp.centralizer_trivial Ψ
    (CFSG.Quasithin.H13.Sec53F.TriD4.borelAutData_d4 σ hf1 hK hσq)
    (burnsideF429b_inf_subgroupOf Ψ h1 h2) (burnsideF429b_D4_pCore_B σ hf1 hK hσq) h1
    (H₀ := Set.range fun a : Kˣ => (⟨trialityTorusHom σ (a, 1),
      trialityTorusHom_mem_graphFixedRootGroup hσ3' (a, 1)⟩ : Cm σ)) ?_ ?_
  · rintro _ ⟨a, rfl⟩
    have hT : (⟨trialityTorusHom σ (a, 1), trialityTorusHom_mem_graphFixedRootGroup hσ3' (a, 1)⟩ :
        Cm σ) ∈ (graphFixedRootTorus TwistTag.D4 K σ.toRingHom).subgroupOf
          (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
      Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨trialityTorusHom_mem_graphFixedTorus hσ3' (a, 1),
        trialityTorusHom_mem_graphFixedRootGroup hσ3' (a, 1)⟩)
    refine ⟨hT, ?_, burnsideF429b_D4_torus_le σ hT⟩
    obtain ⟨y, hy, hyx⟩ := burnsideF429b_D4_rankOne_oPPrime σ _ (burnsideF429b_D4_ho_mem σ hσ3' a)
    have e : y = ⟨trialityTorusHom σ (a, 1), trialityTorusHom_mem_graphFixedRootGroup hσ3' (a, 1)⟩ :=
      Subtype.ext hyx
    subst e
    exact hy
  · intro τ hτ _ _ hfix
    exact burnsideF429b_D4_faithful_outer σ hσ3' τ hτ fun a => hfix _ ⟨a, rfl⟩

theorem burnsideF429b_key2_D4tw {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .D4tw 2 f Gp M₁ M₂) :
    ∀ r ∈ M₁ ⊓ M₂, ∀ k : ℕ, r ^ 2 ^ k = 1 →
      (∀ b ∈ oPPrime 2 (Gp ⊓ M₂) ⊓ (M₁ ⊓ M₂),
        r * b * r⁻¹ * b⁻¹ ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) → r ∈ Gp := by
  haveI := hyp.normal
  obtain ⟨K, fK, finK, cK, σ, hσ3, hf1, hK, hσq, Ψ, h1, h2⟩ :=
    burnsideF429b_D4_chart hyp.toHypF_4_4g
  have hσ3' : σ ^ 3 = 1 := RingEquiv.ext fun c => (ringEquiv_pow_three_apply σ c).trans (hσ3 c)
  refine burnsideF429b_keyL_of_borelAutData hyp.centralizer_trivial Ψ
    (CFSG.Quasithin.H13.Sec53F.TriD4.borelAutData_d4 σ hf1 hK hσq)
    (burnsideF429b_inf_subgroupOf Ψ h1 h2) (burnsideF429b_D4_pCore_B σ hf1 hK hσq) h2
    (H₀ := Set.range fun b : (trialityFixedField K σ.toRingHom)ˣ =>
      (⟨trialityTorusHom σ (1, b), trialityTorusHom_mem_graphFixedRootGroup hσ3' (1, b)⟩ : Cm σ))
    ?_ ?_
  · rintro _ ⟨b, rfl⟩
    have hT : (⟨trialityTorusHom σ (1, b), trialityTorusHom_mem_graphFixedRootGroup hσ3' (1, b)⟩ :
        Cm σ) ∈ (graphFixedRootTorus TwistTag.D4 K σ.toRingHom).subgroupOf
          (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
      Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨trialityTorusHom_mem_graphFixedTorus hσ3' (1, b),
        trialityTorusHom_mem_graphFixedRootGroup hσ3' (1, b)⟩)
    refine ⟨hT, ?_, burnsideF429b_D4_torus_le σ hT⟩
    obtain ⟨y, hy, hyx⟩ := burnsideF429b_D4_rankOne_oPPrime σ _ (burnsideF429b_D4_hm_mem σ hσ3' b)
    have e : y = ⟨trialityTorusHom σ (1, b), trialityTorusHom_mem_graphFixedRootGroup hσ3' (1, b)⟩ :=
      Subtype.ext hyx
    subst e
    exact hy
  · intro τ hτ k hk hfix
    exact burnsideF429b_D4_faithful_middle σ hσ3' hf1 hK hσq τ hτ k hk fun b => hfix _ ⟨b, rfl⟩

end D4

section C5


theorem burnsideF429b_c5_D4tw {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .D4tw 2 f Gp M₁ M₂) {T : Subgroup E} (hT : ChF.IsSylowOf 2 T (M₁ ⊓ M₂)) :
    burnsideF429_C5 .D4tw Gp M₁ M₂ hyp T :=
  burnsideF429_c5i_of_keys hyp hT (burnsideF429b_key1_D4tw hyp) (burnsideF429b_key2_D4tw hyp)

end C5

end CFSG.ASVolI
