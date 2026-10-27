module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiProj
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.LieType.Ree.LargeReeModelSchreier
public import CFSG.Open.PGLModelStated
public import CFSG.Adapters.RankTwoModelTransports

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open Matrix

section Linear

open CFSG.Assembly.LowTwoRank

theorem projSL_eq_map_statedSL (n : ℕ) (F : Type) [Field F] :
    projSL n F = (StatedSL n F).map (ProjGenLinGroup.mk : GL (Fin n) F →* _) :=
  (CFSG.PGLModel.projImage_statedSL n F).symm

@[expose] noncomputable def projSLEquivPSLn (n : ℕ) (F : Type) [Field F] :
    projSL n F ≃* ProjectiveSpecialLinearGroup (Fin n) F :=
  (MulEquiv.subgroupCongr (projSL_eq_map_statedSL n F)).trans
    ((CFSG.Adapters.RankTwoModelTransports.statedProjEquivMapMk (StatedSL n F)).symm.trans
      (projectiveSpecialLinearGroupEquivStatedProj n F).symm)

@[expose] noncomputable def projSLEquivProjectiveSL (n : ℕ) (F : Type) [Field F] :
    projSL n F ≃* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL n F :=
  (projSLEquivPSLn n F).trans
    (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL n F)

theorem center_specialLinearGroup_eq_bot {n : ℕ} {K : Type} [Field K]
    (h : ∀ r : K, r ^ n = 1 → r = 1) : Subgroup.center (SpecialLinearGroup (Fin n) K) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  rw [Fintype.card_fin] at hr
  rw [h r hr, map_one] at hrA
  rw [Subgroup.mem_bot]
  exact Subtype.ext hrA.symm

theorem eq_one_of_pow_three_eq_one {K : Type} [Field K] [Finite K]
    (h3 : ¬ 3 ∣ Nat.card K - 1) {r : K} (hr : r ^ 3 = 1) : r = 1 := by
  have hr0 : r ≠ 0 := by
    rintro rfl
    norm_num at hr
  set u : Kˣ := Units.mk0 r hr0
  have hu : u ^ 3 = 1 := Units.ext (by simp [u, hr])
  have hord : orderOf u ∣ 3 := orderOf_dvd_of_pow_eq_one hu
  have hord' : orderOf u ∣ Nat.card Kˣ := orderOf_dvd_natCard u
  rw [Nat.card_units] at hord'
  rcases (Nat.dvd_prime Nat.prime_three).1 hord with h1 | h1
  · have : u = 1 := orderOf_eq_one_iff.mp h1
    exact congrArg Units.val this
  · exact absurd (h1 ▸ hord') h3

theorem nonempty_statedSL_mulEquiv_projSL {K : Type} [Field K] [Finite K] {p f : ℕ}
    [Fact p.Prime] (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) (h3 : ¬ 3 ∣ p ^ f - 1) :
    Nonempty (StatedSL 3 K ≃* projSL 3 (GaloisField p f)) := by
  have hZ : Subgroup.center (SpecialLinearGroup (Fin 3) K) = ⊥ :=
    center_specialLinearGroup_eq_bot fun r hr => eq_one_of_pow_three_eq_one (by rwa [hK]) hr
  let _ : Fintype K := Fintype.ofFinite K
  let _ : Fintype (GaloisField p f) := Fintype.ofFinite _
  have hcard : Fintype.card K = Fintype.card (GaloisField p f) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK, GaloisField.card p f (by omega)]
  exact ⟨(specialLinearGroupEquivStatedSL 3 K).symm.trans
    (((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans
      ((CFSG.Adapters.RankTwoModelTransports.projectiveSpecialLinearGroupCongr (Fin 3)
        (FiniteField.ringEquivOfCardEq hcard)).trans (projSLEquivPSLn 3 _).symm))⟩

end Linear

section Symplectic

open CFSG.Assembly.LowTwoRank

theorem projSp_eq_map_statedSp (n : ℕ) (F : Type) [Field F] :
    projSp n F = (StatedSp n F).map (ProjGenLinGroup.mk : GL (Fin n ⊕ Fin n) F →* _) :=
  rfl

@[expose] noncomputable def projSpEquivStatedProj (n : ℕ) (F : Type) [Field F] :
    projSp n F ≃* StatedProj (StatedSp n F) :=
  CFSG.PGLModel.projSpEquivStatedProj n F

end Symplectic

section Unitary

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

theorem unitaryFieldData_galoisField (p e : ℕ) [Fact p.Prime] (he : 1 ≤ e) :
    UnitaryFieldData p e (GaloisField p (2 * e)) :=
  ⟨Fact.out, he, GaloisField.card p (2 * e) (by omega)⟩

@[expose] noncomputable def projSUEquivUnitaryPSU (p e : ℕ) [Fact p.Prime]
    (h : UnitaryFieldData p e (GaloisField p (2 * e))) : projSU 3 p e ≃* unitaryPSU h 3 :=
  (MulEquiv.subgroupCongr (projSU_eq_projImage p e)).trans (psuEquivUnitary h)

end Unitary

section Exceptional

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem exists_mulEquiv_adjointGroup_G2 {X : Type} [Group X] {p f : ℕ}
    (h : ChevalleyExceptionalModel X .G2 p f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = p ^ f ∧
      Nonempty (X ≃* adjointGroup Tag.G2 K) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  exact ⟨K, inferInstance, inferInstance, hK, ⟨e.trans ((QuotientGroup.quotientMulEquivOfEq
    (center_adjointGroup_eq_bot (τ := Tag.G2) (K := K))).trans QuotientGroup.quotientBot)⟩⟩

theorem exists_mulEquiv_graphFixedRootGroup_D4 {X : Type} [Group X] {p f : ℕ}
    (h : ChevalleyExceptionalModel X .trialityD4 p f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (σ : K ≃+* K), Nat.card K = (p ^ f) ^ 3 ∧
      (∀ c, σ c = c ^ (p ^ f)) ∧ Nonempty (X ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  obtain ⟨⟨hp, hf, -⟩, hm⟩ := h
  obtain ⟨K, _, _, hcard, σ, hσ, ⟨e⟩⟩ := hm
  obtain ⟨σ', hσ', -⟩ := finite_graph_field_parameter_fields TwistTag.D4 hp hf K hcard
  have hσσ' : σ'.toRingHom = σ := RingHom.ext fun c => by
    rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hσ', hσ]
  have hperf := (finite_fixed_root_group_perfect TwistTag.D4 hp hf K hcard σ hσ).2.2.1
  have hZ := exceptional_fixed_center_trivial TwistTag.D4 K σ'
  rw [hσσ'] at hZ
  set H := twistedFixedGroup TwistTag.D4 K σ
  set C := graphFixedRootGroup TwistTag.D4 K σ
  have hZ' : Subgroup.center ↥⁅H, H⁆ = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    have hxC : (x : ModGL TwistTag.D4.tag K) ∈ C := by
      rw [← hperf]
      exact x.2
    have hcen : (⟨x, hxC⟩ : C) ∈ Subgroup.center C := by
      rw [Subgroup.mem_center_iff]
      intro y
      have hyH : (y : ModGL TwistTag.D4.tag K) ∈ ⁅H, H⁆ := by
        rw [hperf]
        exact y.2
      have h1 := congrArg (Subtype.val : ↥⁅H, H⁆ → ModGL TwistTag.D4.tag K)
        (Subgroup.mem_center_iff.1 hx ⟨y, hyH⟩)
      exact Subtype.ext h1
    rw [hZ, Subgroup.mem_bot] at hcen
    exact Subgroup.mem_bot.2
      (Subtype.ext (congrArg (Subtype.val : C → ModGL TwistTag.D4.tag K) hcen))
  refine ⟨K, inferInstance, inferInstance, σ', hcard, hσ', ⟨?_⟩⟩
  rw [hσσ']
  exact e.trans ((QuotientGroup.quotientMulEquivOfEq hZ').trans
    (QuotientGroup.quotientBot.trans (MulEquiv.subgroupCongr hperf)))

theorem exists_mulEquiv_reeGamma {X : Type} [Group X] {p f : ℕ}
    (h : ReeTitsModel X .twistedF4 p f) :
    p = 2 ∧ ∃ a : ℕ, 1 ≤ a ∧ f = 2 * a + 1 ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K)
      (_ : CharP K CFSG.LieType.Ree.ReeTag.F4.prime), Nat.card K = 2 ^ (2 * a + 1) ∧
        Nonempty (X ≃* CFSG.LieType.Ree.ReeTag.F4.reeGamma K a) := by
  have hS := CFSG.LieType.Ree.ReeTag.large_Ree_model_Schreier X p f h
  obtain ⟨-, -, -, hp, ⟨a, ha, hfa⟩, hiso⟩ := hS
  subst hp
  obtain ⟨hadm, a', hfa', hmodel⟩ := h
  obtain ⟨K, _, _, hK, he⟩ := hmodel
  have : Fintype K := Fintype.ofFinite K
  have : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := charP_of_card_eq_prime_pow (f := f) (by
    rw [← Nat.card_eq_fintype_card, hK]
    rfl)
  have haa' : a' = a := by omega
  subst haa'
  exact ⟨rfl, a', ha, hfa, K, inferInstance, inferInstance, inferInstance, by rw [hK, hfa],
    hiso a' K hfa hK he⟩

end Exceptional

section Center

variable {X Y : Type*} [Group X] [Group Y]

theorem center_eq_bot_of_mulEquiv (e : X ≃* Y) (hY : Subgroup.center Y = ⊥) :
    Subgroup.center X = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hex : e x ∈ Subgroup.center Y := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨z, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hx z)]
  rw [hY, Subgroup.mem_bot] at hex
  exact Subgroup.mem_bot.mpr (e.injective (hex.trans (map_one e).symm))

theorem center_eq_bot_of_mulEquiv_isSimpleGroup (hX : CFSG.IsQuasisimple X) (e : X ≃* Y)
    [IsSimpleGroup Y] : Subgroup.center X = ⊥ := by
  have : IsSimpleGroup X := e.isSimpleGroup
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hX.2.2
    apply hab
    induction a using QuotientGroup.induction_on with
    | H x =>
    induction b using QuotientGroup.induction_on with
    | H y =>
    have hx : x ∈ Subgroup.center X := h ▸ Subgroup.mem_top x
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.mp hx y]

end Center

end CFSG.RankThree.PartTwo.Sec4
