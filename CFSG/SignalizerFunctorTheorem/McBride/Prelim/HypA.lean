module

public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Projection
public import CFSG.SignalizerFunctorTheorem.Inheritance.HypB
public import CFSG.SignalizerFunctorTheorem.NearModels.Main
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.SemisimpleFactors

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride

variable {G : Type*} [Group G]

theorem signalizerMcBrideHypothesisA_of_mem_lcal [Finite G] {p : ℕ} {Y J : Subgroup G}
    (hY : signalizerMcBrideHypothesisB p Y) (hJ : J ∈ lcal Y) :
    signalizerMcBrideHypothesisA p ↥J := by
  obtain ⟨hJY, -, hs, hnc⟩ := mem_lcal_iff.mp hJ
  have : IsSimpleGroup J := hs
  have hnc' : ∃ x y : J, x * y ≠ y * x := by
    by_contra h
    push Not at h
    exact hnc (isMulCommutative_iff.mpr h)
  exact CFSG.SignalizerFunctorTheorem.signalizerMcBrideHypothesisA_of_isSectionOf hY
    ⟨J.subgroupOf Y, (Subgroup.subgroupOfEquivOfLe hJY).toMonoidHom,
      (Subgroup.subgroupOfEquivOfLe hJY).surjective⟩ hnc'

theorem card_range_conj_dvd [Finite G] {p : ℕ} (_hp : p.Prime) {A Y J B : Subgroup G}
    (hA : IsElemAbelian p A) (hY : signalizerMcBrideHypothesisB p Y) (hJ : J ∈ lcal Y)
    (hBA : B ≤ A) (hBJ : B ≤ Subgroup.normalizer (J : Set G)) :
    Nat.card (J.normalizerMonoidHom.comp (Subgroup.inclusion hBJ)).range ∣ p := by
  have hcyc := (signalizerMcBrideHypothesisA_of_mem_lcal hY hJ).2.2.2.2.1
  let ρ : B →* MulAut J := J.normalizerMonoidHom.comp (Subgroup.inclusion hBJ)
  have hpow : ∀ b : B, b ^ p = 1 := fun b => Subtype.ext (by simpa using hA.2 b (hBA b.2))
  have hRp : IsPGroup p ρ.range :=
    IsPGroup.of_surjective (fun b : B => ⟨1, by simpa using hpow b⟩) ρ.rangeRestrict
      ρ.rangeRestrict_surjective
  obtain ⟨g, hg⟩ := (hcyc ρ.range hRp).exists_ofOrder_eq_natCard
  have hgp : g ^ p = 1 := by
    obtain ⟨b, hb⟩ := g.2
    refine Subtype.ext ?_
    rw [Subgroup.coe_pow, ← hb, ← map_pow, hpow b, map_one]
    rfl
  exact hg ▸ orderOf_dvd_of_pow_eq_one hgp

private theorem nearSimpleModel_of_nearPSolvable {p : ℕ} {X : Type*} [Group X] [IsSimpleGroup X]
    (hnc : ∃ x y : X, x * y ≠ y * x) (h : signalizerNearPSolvable p X) :
    signalizerNearSimpleModel p X := by
  let e : (⊤ : Subgroup X) ⧸ (⊥ : Subgroup X).subgroupOf ⊤ ≃* X :=
    (QuotientGroup.quotientMulEquivOfEq (Subgroup.bot_subgroupOf (H := ⊤))).trans
      (QuotientGroup.quotientBot.trans Subgroup.topEquiv)
  have hs : IsSimpleGroup ((⊤ : Subgroup X) ⧸ (⊥ : Subgroup X).subgroupOf ⊤) :=
    e.isSimpleGroup
  obtain ⟨x, y, hxy⟩ := hnc
  have h2 := h.2 ⊤ ⊥ bot_le hs ⟨e.symm x, e.symm y, fun h => hxy (by simpa using congrArg e h)⟩
  exact TransportA.nearSimpleModel_of_mulEquiv e h2

private theorem exists_injective_smear_hom [Finite G] {A Y J : Subgroup G}
    (hAY : A ≤ Subgroup.normalizer (Y : Set G)) (hJ : J ∈ lcal Y) :
    ∃ ψ : ↥(smear J A) →* ↥J, Function.Injective ψ ∧ ∀ y : smear J A, ((ψ y : J) : G) ∈
      Subgroup.centralizer ((A ⊓ Subgroup.normalizer (J : Set G) : Subgroup G) : Set G) := by
  let S : Set (Subgroup G) := {K | ∃ a ∈ A, K = J.map (MulAut.conj a).toMonoidHom}
  have hL : IsDirectProduct S (orbitClosure J A) := isDirectProduct_orbit hAY hJ
  have hAS : ∀ a ∈ A, ∀ K ∈ S, K.map (MulAut.conj a).toMonoidHom ∈ S := by
    rintro a ha _ ⟨a', ha', rfl⟩
    refine ⟨a * a', mul_mem ha ha', ?_⟩
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp [mul_assoc]
  have hJS : J ∈ S := ⟨1, one_mem A, by ext x; simp⟩
  have htrans : ∀ K ∈ S, ∃ a ∈ A, K = J.map (MulAut.conj a).toMonoidHom := fun K hK => hK
  refine ⟨(hL.coord hJS).comp (Subgroup.inclusion (smear_le_orbitClosure J A)), ?_, fun y => ?_⟩
  · rw [injective_iff_map_eq_one]
    intro y hy
    have h1 : (y : G) ∈ sSup (S \ {J}) := (hL.coord_eq_one_iff hJS _).mp hy
    have h2 : (y : G) ∈ orbitClosure J A ⊓ Subgroup.centralizer (A : Set G) ⊓ sSup (S \ {J}) :=
      Subgroup.mem_inf.mpr ⟨y.2, h1⟩
    rw [inf_centralizer_inf_sSup_eq_bot_of_transitive hL hAS hJS htrans, Subgroup.mem_bot] at h2
    exact Subtype.ext h2
  · have hy : ((hL.coord hJS (Subgroup.inclusion (smear_le_orbitClosure J A) y) : J) : G) ∈
        projIn S J (orbitClosure J A ⊓ Subgroup.centralizer (A : Set G)) :=
      (hL.mem_projIn_iff hJS).mpr ⟨Subgroup.inclusion (smear_le_orbitClosure J A) y, y.2, rfl⟩
    rw [projIn_centralizer_eq hL hAS hJS] at hy
    exact (Subgroup.mem_inf.mp hy).2

theorem not_signalizerNearPSolvable_of_not_isSolvable_smear
    [Finite G] {p : ℕ} (hp : p.Prime)
    {A Y J : Subgroup G} (hA : IsElemAbelian p A) (hAY : A ≤ Subgroup.normalizer (Y : Set G))
    (hJ : J ∈ lcal Y) (hnon : ¬ Group.IsSolvable (smear J A))
    (hact : ¬ A ⊓ Subgroup.normalizer (J : Set G) ≤ Subgroup.centralizer (J : Set G)) :
    ¬ signalizerNearPSolvable p ↥J := by
  intro hnear
  obtain ⟨-, -, hs, hnc⟩ := mem_lcal_iff.mp hJ
  have hnc' : ∃ x y : J, x * y ≠ y * x := by
    by_contra h
    push Not at h
    exact hnc (isMulCommutative_iff.mpr h)
  have hmodel : signalizerNearSimpleModel p ↥J := nearSimpleModel_of_nearPSolvable hnc' hnear
  obtain ⟨b, hbB, hbC⟩ := IsConcreteLE.not_le_iff_exists.mp hact
  obtain ⟨hbA, hbN⟩ := Subgroup.mem_inf.mp hbB
  let f : MulAut ↥J := J.normalizerMonoidHom ⟨b, hbN⟩
  have hfc : ∀ t : J, ((f t : J) : G) = b * t * b⁻¹ :=
    Subgroup.normalizerMonoidHom_apply_apply_coe J ⟨b, hbN⟩
  have hf1 : f ≠ 1 := by
    intro h1
    refine hbC (Subgroup.mem_centralizer_iff.mpr fun t ht => ?_)
    have h2 : t = b * t * b⁻¹ := by simpa [h1] using hfc ⟨t, ht⟩
    calc t * b = b * t * b⁻¹ * b := by rw [← h2]
      _ = b * t := by group
  have hfp : f ^ p = 1 := by
    rw [← map_pow]
    have : (⟨b, hbN⟩ : Subgroup.normalizer (J : Set G)) ^ p = 1 :=
      Subtype.ext (by simpa using hA.2 b hbA)
    rw [this, map_one]
  have hf : orderOf f = p := by
    have := Fact.mk hp
    exact orderOf_eq_prime hfp hf1
  have := NearModels.nearSimpleModel_fixedSubgroup_solvable hp hmodel hnear.1 f hf
  obtain ⟨ψ, hψinj, hψc⟩ := exists_injective_smear_hom hAY hJ
  have hψfix : ∀ y, ψ y ∈ signalizerFixedSubgroup f := fun y => by
    refine Subtype.ext ?_
    rw [hfc, (Subgroup.mem_centralizer_iff.mp (hψc y) b hbB)]
    group
  exact hnon (Group.isSolvable_of_isSolvable_injective (f := ψ.codRestrict _ hψfix)
    fun x y h => hψinj (congrArg Subtype.val h))

theorem fittingSubgroup_fixedSubgroup_eq_bot {p : ℕ} {X : Type*} [Group X] [Finite X]
    (hA : signalizerMcBrideHypothesisA p X) (hnear : ¬ signalizerNearPSolvable p X)
    {f : MulAut X} (hf : orderOf f = p) :
    CFSG.fittingSubgroup ↥(signalizerFixedSubgroup f) = ⊥ := by
  have hloc := ((hA.2.2.2.2.2.resolve_left hnear) f hf).1
  by_contra hne
  set C := signalizerFixedSubgroup f with hC
  set T : Subgroup X := (CFSG.fittingSubgroup ↥C).map C.subtype with hT
  have hT1 : T ≠ ⊥ := fun h =>
    hne ((Subgroup.map_eq_bot_iff_of_injective _ C.subtype_injective).mp h)
  have hnil : Group.IsNilpotent (CFSG.fittingSubgroup ↥C) :=
    (CFSG.LocalCores.fitting_nilpotent (G := ↥C)).1
  have hTs : Group.IsSolvable T :=
    Group.isSolvable_of_surjective (f := C.subtype.subgroupMap (CFSG.fittingSubgroup ↥C))
      (MonoidHom.subgroupMap_surjective _ _)
  have hTC : T ≤ C := Subgroup.map_subtype_le _
  have hsub : T.subgroupOf C = CFSG.fittingSubgroup ↥C :=
    Subgroup.comap_map_eq_self_of_injective C.subtype_injective _
  have hCn : C ≤ Subgroup.normalizer (T : Set X) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hTC).mp (by rw [hsub]; infer_instance)
  exact hloc T hT1 hTs hCn

end CFSG.SignalizerFunctorTheorem.McBride
