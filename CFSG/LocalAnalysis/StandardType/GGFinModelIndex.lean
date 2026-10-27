module

public import CFSG.LocalAnalysis.StandardType.GGFinModelExists
import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.E6CartanIndexOne
public import CFSG.RankThree.PartOne.KE.EvenE7E8QPlusDescent
public import CFSG.LocalAnalysis.StandardType.GGUnitaryTwoResidual

public section

namespace CFSG.StandardType.GGFinModel

open CFSG.StandardType CFSG.Open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Universal CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Steinberg.Exceptional CFSG.LieType.Steinberg.Isogeny
  CFSG.HardMathSupport.Timmesfeld.LangTorus

@[expose] def GGCorner (t : StatedLieTag) (p f : ℕ) : Prop :=
  p = 3 ∧ ((t = .E6 ∧ 3 ∣ 2 ^ f - 1) ∨ (t = .twistedE6 ∧ 3 ∣ 2 ^ f + 1))

private theorem g4bRangeF4
    (n f : ℕ) (hf : 1 ≤ f) :
    (ggIota .F4 n f hf).range =
      (adjointGroup Tag.F4 (GaloisField 2 f)).map (baseChangeGL (ggRatEmb f)) := by
  change (((baseChangeGL (ggRatEmb f)).comp
      (adjointGroup Tag.F4 (GaloisField 2 f)).subtype).comp
        (ggKbEquivF4 n f).toMonoidHom).range =
    (adjointGroup Tag.F4 (GaloisField 2 f)).map (baseChangeGL (ggRatEmb f))
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (ggKbEquivF4 n f).surjective,
    Subgroup.map_top, MonoidHom.range_comp, Subgroup.range_subtype]

private theorem g4bRangeE6
    (n f : ℕ) (hf : 1 ≤ f) :
    (ggIota .E6 n f hf).range =
      (adjointGroup Tag.E6 (GaloisField 2 f)).map (baseChangeGL (ggRatEmb f)) := by
  change (((baseChangeGL (ggRatEmb f)).comp
      (adjointGroup Tag.E6 (GaloisField 2 f)).subtype).comp
        (ggKbEquivE6 n f).toMonoidHom).range =
    (adjointGroup Tag.E6 (GaloisField 2 f)).map (baseChangeGL (ggRatEmb f))
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (ggKbEquivE6 n f).surjective,
    Subgroup.map_top, MonoidHom.range_comp, Subgroup.range_subtype]

private theorem g4bRangeE7
    (n f : ℕ) (hf : 1 ≤ f) :
    (ggIota .E7 n f hf).range =
      (adjointGroup Tag.E7 (GaloisField 2 f)).map (baseChangeGL (ggRatEmb f)) := by
  change (((baseChangeGL (ggRatEmb f)).comp
      (adjointGroup Tag.E7 (GaloisField 2 f)).subtype).comp
        (ggKbEquivE7 n f).toMonoidHom).range =
    (adjointGroup Tag.E7 (GaloisField 2 f)).map (baseChangeGL (ggRatEmb f))
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (ggKbEquivE7 n f).surjective,
    Subgroup.map_top, MonoidHom.range_comp, Subgroup.range_subtype]

private theorem g4bRangeE8
    (n f : ℕ) (hf : 1 ≤ f) :
    (ggIota .E8 n f hf).range =
      (adjointGroup Tag.E8 (GaloisField 2 f)).map (baseChangeGL (ggRatEmb f)) := by
  change (((baseChangeGL (ggRatEmb f)).comp
      (adjointGroup Tag.E8 (GaloisField 2 f)).subtype).comp
        (ggKbEquivE8 n f).toMonoidHom).range =
    (adjointGroup Tag.E8 (GaloisField 2 f)).map (baseChangeGL (ggRatEmb f))
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (ggKbEquivE8 n f).surjective,
    Subgroup.map_top, MonoidHom.range_comp, Subgroup.range_subtype]

private theorem g4bRangeTwE6
    (n f : ℕ) (hf : 1 ≤ f) :
    (ggIota .twistedE6 n f hf).range =
      (graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)).map
        (baseChangeGL (ggRatEmb (2 * f))) := by
  change (((baseChangeGL (ggRatEmb (2 * f))).comp
      (graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)).subtype).comp
        (ggKbEquivTwE6 n f hf).toMonoidHom).range =
    (graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)).map
      (baseChangeGL (ggRatEmb (2 * f)))
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (ggKbEquivTwE6 n f hf).surjective,
    Subgroup.map_top, MonoidHom.range_comp, Subgroup.range_subtype]

private theorem g4bRelIndexF4
    {f : ℕ} (hf : 1 ≤ f) (D : LangDatum Tag.F4 GGL)
    (hΦ : D.Φ = Units.map (entrywiseHom (ggFrobT f))) :
    ((adjointGroup Tag.F4 (GaloisField 2 f)).map (baseChangeGL (ggRatEmb f))).relIndex D.fix =
      1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKcard : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hFr : ∀ c : GGL, ggFrobT f c = c ^ Nat.card (GaloisField 2 f) := fun c => by
    rw [hKcard]
    exact ggFrobT_apply f c
  letI : Algebra (GaloisField 2 f) GGL := (ggRatEmb f).toAlgebra
  haveI : IsScalarTower (ZMod 2) (GaloisField 2 f) GGL :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_zmod _ _)
  haveI : Algebra.IsAlgebraic (GaloisField 2 f) GGL :=
    Algebra.IsAlgebraic.tower_top (K := ZMod 2) (L := GaloisField 2 f) (A := GGL)
  haveI : IsAlgClosure (GaloisField 2 f) GGL :=
    ⟨IsAlgClosure.isAlgClosed (ZMod 2), inferInstance⟩
  have hex := (CFSG.RankThree.Chevalley.G2_F4_exact_finite_field_fixed_root_matrices
    Tag.F4 (Or.inr rfl) (GaloisField 2 f) GGL (ggFrobT f) hFr).1
  have hfix : D.fix = (adjointGroup Tag.F4 (GaloisField 2 f)).map
      (baseChangeGL (ggRatEmb f)) := by
    change D.fix = (adjointGroup Tag.F4 (GaloisField 2 f)).map
      (baseChangeGL (algebraMap (GaloisField 2 f) GGL))
    rw [← hex]
    ext x
    rw [LangDatum.mem_fix, hΦ]
    rfl
  rw [hfix, Subgroup.relIndex_self]

private theorem g4bRelIndexUntw
    {τ : Tag} (d : ℕ)
    (hτd : (τ = .E6 ∧ d = 3) ∨ (τ = .E7 ∧ d = 2) ∨ (τ = .E8 ∧ d = 1)) {f : ℕ}
    (hf : 1 ≤ f) (D : LangDatum τ GGL)
    (hΦ : D.Φ = Units.map (entrywiseHom (ggFrobT f))) :
    ((adjointGroup τ (GaloisField 2 f)).map (baseChangeGL (ggRatEmb f))).relIndex D.fix ∣ d := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKcard : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hFr : ∀ c : GGL, ggFrobT f c = c ^ Nat.card (GaloisField 2 f) := fun c => by
    rw [hKcard]
    exact ggFrobT_apply f c
  letI : Algebra (GaloisField 2 f) GGL := (ggRatEmb f).toAlgebra
  haveI : IsScalarTower (ZMod 2) (GaloisField 2 f) GGL :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_zmod _ _)
  haveI : Algebra.IsAlgebraic (GaloisField 2 f) GGL :=
    Algebra.IsAlgebraic.tower_top (K := ZMod 2) (L := GaloisField 2 f) (A := GGL)
  haveI : IsAlgClosure (GaloisField 2 f) GGL :=
    ⟨IsAlgClosure.isAlgClosed (ZMod 2), inferInstance⟩
  have hfixmem : ∀ x, x ∈ D.fix ↔ x ∈ adjointGroup τ GGL ∧
      Units.map (entrywiseHom (ggFrobT f)) x = x := fun x => by
    rw [LangDatum.mem_fix, hΦ]
  have hfin : Finite D.fix := by
    refine finite_of_entries_mem_range (K := GaloisField 2 f) D.fix fun g hg a b => ?_
    obtain ⟨-, hgF⟩ := (hfixmem g).1 hg
    have hcoord := congrArg (fun A : ModGL τ GGL =>
      (A : Module.End GGL (RootModule τ GGL)) (Finsupp.single b 1) a) hgF
    simp only [Units.coe_map] at hcoord
    change entrywise (ggFrobT f) _ (Finsupp.single b 1) a = _ at hcoord
    rw [entrywise_single, Finsupp.mapRange_apply, ggFrobT_apply] at hcoord
    exact CFSG.LieType.Chevalley.mem_range_algebraMap_of_pow_card_eq
      (k := GaloisField 2 f) (by rw [hKcard]; exact hcoord)
  have hidx := (CFSG.RankThree.PartOne.KE.finite_fixed_subgroup_rational
    (K := GaloisField 2 f) (L := GGL) (τ := τ) d hτd (ggFrobT f) hFr D.fix
    (fun x hx => ((hfixmem x).1 hx).1) (fun x hx => ((hfixmem x).1 hx).2)).1
  change ((adjointGroup τ (GaloisField 2 f)).map
    (baseChangeGL (algebraMap (GaloisField 2 f) GGL))).relIndex D.fix ∣ d
  exact hidx

private theorem g4bRelIndexE6
    {f : ℕ} (hf : 1 ≤ f) (D : LangDatum Tag.E6 GGL)
    (hΦ : D.Φ = Units.map (entrywiseHom (ggFrobT f))) (h3 : ¬ 3 ∣ 2 ^ f - 1) :
    ((adjointGroup Tag.E6 (GaloisField 2 f)).map (baseChangeGL (ggRatEmb f))).relIndex D.fix =
      1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKcard : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hFr : ∀ c : GGL, ggFrobT f c = c ^ Nat.card (GaloisField 2 f) := fun c => by
    rw [hKcard]
    exact ggFrobT_apply f c
  letI : Algebra (GaloisField 2 f) GGL := (ggRatEmb f).toAlgebra
  haveI : IsScalarTower (ZMod 2) (GaloisField 2 f) GGL :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_zmod _ _)
  haveI : Algebra.IsAlgebraic (GaloisField 2 f) GGL :=
    Algebra.IsAlgebraic.tower_top (K := ZMod 2) (L := GaloisField 2 f) (A := GGL)
  haveI : IsAlgClosure (GaloisField 2 f) GGL :=
    ⟨IsAlgClosure.isAlgClosed (ZMod 2), inferInstance⟩
  have hfixmem : ∀ x, x ∈ D.fix ↔ x ∈ adjointGroup Tag.E6 GGL ∧
      Units.map (entrywiseHom (ggFrobT f)) x = x := fun x => by
    rw [LangDatum.mem_fix, hΦ]
  have hfin : Finite D.fix := by
    refine finite_of_entries_mem_range (K := GaloisField 2 f) D.fix fun g hg a b => ?_
    obtain ⟨-, hgF⟩ := (hfixmem g).1 hg
    have hcoord := congrArg (fun A : ModGL Tag.E6 GGL =>
      (A : Module.End GGL (RootModule Tag.E6 GGL)) (Finsupp.single b 1) a) hgF
    simp only [Units.coe_map] at hcoord
    change entrywise (ggFrobT f) _ (Finsupp.single b 1) a = _ at hcoord
    rw [entrywise_single, Finsupp.mapRange_apply, ggFrobT_apply] at hcoord
    exact CFSG.LieType.Chevalley.mem_range_algebraMap_of_pow_card_eq
      (k := GaloisField 2 f) (by rw [hKcard]; exact hcoord)
  have hidx :=
    CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.relIndex_dvd_E6_of_not_three_dvd
      (GaloisField 2 f) (by rwa [hKcard]) GGL (ggFrobT f) hFr D.fix
      (fun x hx => ((hfixmem x).1 hx).1) (fun x hx => ((hfixmem x).1 hx).2)
  change ((adjointGroup Tag.E6 (GaloisField 2 f)).map
    (baseChangeGL (algebraMap (GaloisField 2 f) GGL))).relIndex D.fix = 1
  exact Nat.dvd_one.mp hidx

private theorem g4bRelIndexTwE6
    {f : ℕ} (hf : 1 ≤ f) (D : LangDatum Tag.E6 GGL)
    (hΦ : D.Φ = twistHom TwistTag.E6 GGL (ggFrobT f)) :
    ((graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)).map
        (baseChangeGL (ggRatEmb (2 * f)))).relIndex D.fix = Nat.gcd 3 (2 ^ f + 1) := by
  classical
  let F := GaloisField 2 (2 * f)
  let σ : F →+* F := frobQ 2 f
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Algebra F GGL := (ggRatEmb (2 * f)).toAlgebra
  haveI : IsScalarTower (ZMod 2) F GGL :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_zmod _ _)
  haveI : Algebra.IsAlgebraic F GGL :=
    Algebra.IsAlgebraic.tower_top (K := ZMod 2) (L := F) (A := GGL)
  haveI : IsAlgClosure F GGL := ⟨IsAlgClosure.isAlgClosed (ZMod 2), inferInstance⟩
  let R : Subgroup (ModGL TwistTag.E6.tag GGL) := twistedFixedGroup TwistTag.E6 GGL (ggFrobT f)
  let C : Subgroup (ModGL TwistTag.E6.tag GGL) :=
    (graphFixedRootGroup TwistTag.E6 F σ).map (baseChangeGL (algebraMap F GGL))
  change C.relIndex D.fix = Nat.gcd 3 (2 ^ f + 1)
  have hcard_R : Nat.card R = CFSG.SeitzReduction.E6Pilot.numTwistedE6 (2 ^ f) := by
    have h := (CFSG.RankThree.Classical2.twisted_E6_full_rational_fixed_group_order
      (ℓ := 2) (f := f) Nat.prime_two hf F (card_galoisField_two_mul 2 f hf) σ
      (frobQ_apply 2 f) GGL (ggFrobT f) (ggFrobT_apply f)).2.2.2.2.2.1
    simpa only [R, CFSG.SeitzReduction.E6Pilot.numTwistedE6] using h
  have hder : ⁅R, R⁆ = C := by
    have h := (CFSG.RankThree.Classical2.twisted_E6_full_rational_fixed_group_order
      (ℓ := 2) (f := f) Nat.prime_two hf F (card_galoisField_two_mul 2 f hf) σ
      (frobQ_apply 2 f) GGL (ggFrobT f) (ggFrobT_apply f)).2.2.1
    simpa only [R, C] using h
  have hfixD : D.fix = R := by
    ext x
    rw [LangDatum.mem_fix, hΦ]
    rfl
  rw [hfixD]
  have hC0card : Nat.card (graphFixedRootGroup TwistTag.E6 F σ) = ordTwistedE6 (2 ^ f) :=
    CFSG.ClassicalInvolution.card_graphFixedRootGroup_E6 (K := F) Nat.prime_two hf
      (card_galoisField_two_mul 2 f hf) σ (frobQ_apply 2 f)
  have hCcard : Nat.card C = Nat.card (graphFixedRootGroup TwistTag.E6 F σ) :=
    Subgroup.card_map_of_injective (baseChangeGL_injective (algebraMap F GGL))
  have hnum : Nat.card (graphFixedRootGroup TwistTag.E6 F σ) * Nat.gcd 3 (2 ^ f + 1) =
      CFSG.SeitzReduction.E6Pilot.numTwistedE6 (2 ^ f) := by
    rw [hC0card]
    exact CFSG.SeitzReduction.E6Pilot.ordTwistedE6_mul_gcd (2 ^ f)
  have hle : C ≤ R := by
    rw [← hder]
    simpa using Subgroup.commutator_le_sup (H₁ := R) (H₂ := R)
  have hrel : C.relIndex R * Nat.card ↥(C ⊓ R) = Nat.card R :=
    Subgroup.relIndex_mul_card (H := C) (K := R)
  have hinf : C ⊓ R = C := inf_eq_left.mpr hle
  have hkey : C.relIndex R * Nat.card C = Nat.card R := by
    rw [← hrel, hinf]
  have hkey2 : C.relIndex R * Nat.card (graphFixedRootGroup TwistTag.E6 F σ) =
      CFSG.SeitzReduction.E6Pilot.numTwistedE6 (2 ^ f) := by
    rw [← hCcard, hkey, hcard_R]
  have hC0pos : 0 < Nat.card (graphFixedRootGroup TwistTag.E6 F σ) := Nat.card_pos
  have hrel_eq : C.relIndex R * Nat.card (graphFixedRootGroup TwistTag.E6 F σ) =
      Nat.gcd 3 (2 ^ f + 1) * Nat.card (graphFixedRootGroup TwistTag.E6 F σ) := by
    rw [hkey2, ← hnum, mul_comm]
  exact Nat.eq_of_mul_eq_mul_right hC0pos hrel_eq

private theorem g4bRelIndexE7
    {f : ℕ} (hf : 1 ≤ f) (D : LangDatum Tag.E7 GGL)
    (hΦ : D.Φ = Units.map (entrywiseHom (ggFrobT f))) :
    ((adjointGroup Tag.E7 (GaloisField 2 f)).map (baseChangeGL (ggRatEmb f))).relIndex D.fix =
      1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKcard : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hFr : ∀ c : GGL, ggFrobT f c = c ^ Nat.card (GaloisField 2 f) := fun c => by
    rw [hKcard]
    exact ggFrobT_apply f c
  let : Algebra (GaloisField 2 f) GGL := (ggRatEmb f).toAlgebra
  have : IsScalarTower (ZMod 2) (GaloisField 2 f) GGL :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_zmod _ _)
  have : Algebra.IsAlgebraic (GaloisField 2 f) GGL :=
    Algebra.IsAlgebraic.tower_top (K := ZMod 2) (L := GaloisField 2 f) (A := GGL)
  have hfixmem : ∀ x, x ∈ D.fix ↔ x ∈ adjointGroup Tag.E7 GGL ∧
      Units.map (entrywiseHom (ggFrobT f)) x = x := fun x => by
    rw [LangDatum.mem_fix, hΦ]
  have hle : D.fix ≤ (adjointGroup Tag.E7 (GaloisField 2 f)).map
      (baseChangeGL (ggRatEmb f)) := by
    intro x hx
    obtain ⟨hxC, hxF⟩ := (hfixmem x).1 hx
    exact CFSG.RankThree.PartOne.KE.qplus_frobenius_fixed_mem
      (Or.inl rfl) (ggFrobT f) hFr hxC hxF
  exact Subgroup.relIndex_eq_one.mpr hle

namespace GGDatumModel

theorem ggIota_range_relIndex_fix_odd
    {t : StatedLieTag} {f p : ℕ} {ht : GGExcFive t}
    (M : GGDatumModel t f p ht) {n : ℕ}
    (hf : 1 ≤ f) :
    Odd ((ggIota t n f hf).range.relIndex M.D.fix) := by
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · rw [g4bRangeF4 n f hf]
    have hidx : ((adjointGroup Tag.F4 (GaloisField 2 f)).map
        (baseChangeGL (ggRatEmb f))).relIndex M.D.fix = 1 :=
      g4bRelIndexF4 hf M.D M.hΦ
    exact hidx.symm ▸ (show Odd (1 : ℕ) by norm_num)
  · rw [g4bRangeE6 n f hf]
    exact Odd.of_dvd_nat (by decide : Odd (3 : ℕ))
      (g4bRelIndexUntw (f := f) 3 (Or.inl ⟨rfl, rfl⟩) hf M.D M.hΦ)
  · rw [g4bRangeE7 n f hf]
    have hidx : ((adjointGroup Tag.E7 (GaloisField 2 f)).map
        (baseChangeGL (ggRatEmb f))).relIndex M.D.fix = 1 :=
      g4bRelIndexE7 (f := f) hf M.D M.hΦ
    exact hidx.symm ▸ (show Odd (1 : ℕ) by norm_num)
  · rw [g4bRangeE8 n f hf]
    have hidx : ((adjointGroup Tag.E8 (GaloisField 2 f)).map
        (baseChangeGL (ggRatEmb f))).relIndex M.D.fix = 1 :=
      Nat.dvd_one.mp (g4bRelIndexUntw (f := f) 1 (Or.inr (Or.inr ⟨rfl, rfl⟩)) hf M.D M.hΦ)
    exact hidx.symm ▸ (show Odd (1 : ℕ) by norm_num)
  · rw [g4bRangeTwE6 n f hf]
    have hidx : ((graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)).map
        (baseChangeGL (ggRatEmb (2 * f)))).relIndex M.D.fix = Nat.gcd 3 (2 ^ f + 1) :=
      g4bRelIndexTwE6 (f := f) hf M.D M.hΦ
    exact hidx.symm ▸ (Odd.of_dvd_nat (by decide) (Nat.gcd_dvd_left 3 (2 ^ f + 1)))

theorem ggSu_range_le_model_Γ
    {t : StatedLieTag} {f p : ℕ} {ht : GGExcFive t}
    (M : GGDatumModel t f p ht) {n : ℕ}
    (hf : 1 ≤ f) (hp : p.Prime) (hp2 : p ≠ 2) (hreg : GGExcRegime p f)
    {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = (2 ^ f) ^ 2)
    (θ : CFSG.ClassicalInvolution.Phan.Su K 2 f 3 →* ModGL (langTag t) GGL)
    (hθ : θ.range ≤ M.D.model) :
    θ.range ≤ M.D.Γ := by
  classical
  have : NeZero p := ⟨hp.ne_zero⟩
  let c : ModGL (langTag t) GGL →* ModGL (langTag t) GGL :=
    (MulAut.conj M.D.g0).toMonoidHom
  let θ' : CFSG.ClassicalInvolution.Phan.Su K 2 f 3 →* ModGL (langTag t) GGL := c.comp θ
  let N : Subgroup (ModGL (langTag t) GGL) := (ggIota t n f hf).range
  have hpkg := (M.torusData (n := n) hf hp hp2 hreg).pkg
  have hθ' : θ'.range ≤ M.D.fix := by
    change ((MulAut.conj M.D.g0).toMonoidHom.comp θ).range ≤ M.D.fix
    rw [MonoidHom.range_comp, ← LangDatum.map_conj_model M.D]
    exact Subgroup.map_mono hθ
  have hNnormal : (N.subgroupOf M.D.fix).Normal := by
    have hN : N = ⁅M.D.fix, M.D.fix⁆ := hpkg.desc.derived.symm
    rw [hN]
    have hcomm : (⁅M.D.fix, M.D.fix⁆.subgroupOf (M.D.fix ⊔ M.D.fix)).Normal := inferInstance
    rw [sup_idem M.D.fix] at hcomm
    exact hcomm
  have : (N.subgroupOf M.D.fix).Normal := hNnormal
  have hOdd : Odd (N.relIndex M.D.fix) :=
    ggIota_range_relIndex_fix_odd M hf
  have hle : θ'.range ≤ N :=
    ggSu_range_le_of_odd_relIndex hK (by norm_num : 2 ≤ 3) θ' M.D.fix N hθ' hOdd
  have hNΓ : N = M.D.Γ.map c := by
    rw [show N = ⁅M.D.fix, M.D.fix⁆ from hpkg.desc.derived.symm]
    rw [← LangDatum.map_conj_Γ M.D]
  have hθ'range : θ'.range = θ.range.map c := by
    change ((MulAut.conj M.D.g0).toMonoidHom.comp θ).range = θ.range.map c
    rw [MonoidHom.range_comp]
  have hmap : θ.range.map c ≤ M.D.Γ.map c := by
    rw [← hθ'range, ← hNΓ]
    exact hle
  exact (Subgroup.map_le_map_iff_of_injective (f := c)
    (MulAut.conj M.D.g0).injective).mp hmap

theorem coprime_relIndex_of_not_corner
    {t : StatedLieTag} {f p : ℕ} {ht : GGExcFive t} (M : GGDatumModel t f p ht) {n : ℕ}
    [NeZero p] (hf : 1 ≤ f) (hp : p.Prime) (hp2 : p ≠ 2) (hreg : GGExcRegime p f)
    (hnc : ¬ GGCorner t p f) :
    Nat.Coprime p ((ggIota t n f hf).range.relIndex M.D.fix) := by
  set N := (ggIota t n f hf).range.relIndex M.D.fix with hN
  have hle : N ≤ 3 := by
    rw [hN]
    exact (M.torusData (n := n) hf hp hp2 hreg).pkg.index_le
  haveI : Nonempty M.D.fix := ⟨1⟩
  haveI : Finite M.D.fix := (M.torusData (n := n) hf hp hp2 hreg).pkg.desc.finite_fix
  have hcard : 0 < Nat.card M.D.fix := Nat.card_pos
  have hne : N ≠ 0 := by
    intro h0
    have hrel := Subgroup.relIndex_mul_card (H := (ggIota t n f hf).range) (K := M.D.fix)
    rw [← hN, h0, zero_mul] at hrel
    exact hcard.ne' hrel.symm
  by_cases hp3 : p = 3
  · rw [hp3]
    rcases ht with rfl | rfl | rfl | rfl | rfl
    ·
      have hr : (ggIota .F4 n f hf).range =
          (adjointGroup Tag.F4 (GaloisField 2 f)).map (baseChangeGL (ggRatEmb f)) :=
        g4bRangeF4 n f hf
      have hidx : ((adjointGroup Tag.F4 (GaloisField 2 f)).map
          (baseChangeGL (ggRatEmb f))).relIndex M.D.fix = 1 :=
        g4bRelIndexF4 hf M.D M.hΦ
      rw [hN, hr]
      change Nat.Coprime 3
        (((adjointGroup Tag.F4 (GaloisField 2 f)).map
          (baseChangeGL (ggRatEmb f))).relIndex M.D.fix)
      rw [hidx]
      exact Nat.coprime_one_right 3
    ·
      have h3 : ¬ 3 ∣ 2 ^ f - 1 := by
        intro h
        exact hnc (by rw [hp3]; exact ⟨rfl, Or.inl ⟨rfl, h⟩⟩)
      have hr : (ggIota .E6 n f hf).range =
          (adjointGroup Tag.E6 (GaloisField 2 f)).map (baseChangeGL (ggRatEmb f)) :=
        g4bRangeE6 n f hf
      have hidx : ((adjointGroup Tag.E6 (GaloisField 2 f)).map
          (baseChangeGL (ggRatEmb f))).relIndex M.D.fix = 1 :=
        g4bRelIndexE6 hf M.D M.hΦ h3
      rw [hN, hr]
      change Nat.Coprime 3
        (((adjointGroup Tag.E6 (GaloisField 2 f)).map
          (baseChangeGL (ggRatEmb f))).relIndex M.D.fix)
      rw [hidx]
      exact Nat.coprime_one_right 3
    ·
      have hr : (ggIota .E7 n f hf).range =
          (adjointGroup Tag.E7 (GaloisField 2 f)).map (baseChangeGL (ggRatEmb f)) :=
        g4bRangeE7 n f hf
      have hidx : ((adjointGroup Tag.E7 (GaloisField 2 f)).map
          (baseChangeGL (ggRatEmb f))).relIndex M.D.fix ∣ 2 :=
        g4bRelIndexUntw 2 (Or.inr (Or.inl ⟨rfl, rfl⟩)) hf M.D M.hΦ
      rw [hN, hr]
      change Nat.Coprime 3
        (((adjointGroup Tag.E7 (GaloisField 2 f)).map
          (baseChangeGL (ggRatEmb f))).relIndex M.D.fix)
      rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
      intro h3dvd
      exact absurd (h3dvd.trans hidx) (by norm_num)
    ·
      have hr : (ggIota .E8 n f hf).range =
          (adjointGroup Tag.E8 (GaloisField 2 f)).map (baseChangeGL (ggRatEmb f)) :=
        g4bRangeE8 n f hf
      have hidx : ((adjointGroup Tag.E8 (GaloisField 2 f)).map
          (baseChangeGL (ggRatEmb f))).relIndex M.D.fix = 1 :=
        Nat.dvd_one.mp (g4bRelIndexUntw (f := f) 1 (Or.inr (Or.inr ⟨rfl, rfl⟩)) hf M.D M.hΦ)
      rw [hN, hr]
      change Nat.Coprime 3
        (((adjointGroup Tag.E8 (GaloisField 2 f)).map
          (baseChangeGL (ggRatEmb f))).relIndex M.D.fix)
      rw [hidx]
      exact Nat.coprime_one_right 3
    ·
      have h3 : ¬ 3 ∣ 2 ^ f + 1 := by
        intro h
        exact hnc (by rw [hp3]; exact ⟨rfl, Or.inr ⟨rfl, h⟩⟩)
      have hr : (ggIota .twistedE6 n f hf).range =
          (graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)).map
            (baseChangeGL (ggRatEmb (2 * f))) :=
        g4bRangeTwE6 n f hf
      have hidx : ((graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)).map
          (baseChangeGL (ggRatEmb (2 * f)))).relIndex M.D.fix = Nat.gcd 3 (2 ^ f + 1) :=
        g4bRelIndexTwE6 hf M.D M.hΦ
      have hcop : Nat.Coprime 3 (2 ^ f + 1) :=
        (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3
      have hgcd : Nat.gcd 3 (2 ^ f + 1) = 1 := hcop
      rw [hN, hr]
      change Nat.Coprime 3
        (((graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)).map
          (baseChangeGL (ggRatEmb (2 * f)))).relIndex M.D.fix)
      rw [hidx, hgcd]
      exact Nat.coprime_one_right 3
  · rw [hp.coprime_iff_not_dvd]
    intro hpdvd
    have hple : p ≤ N := Nat.le_of_dvd (Nat.pos_iff_ne_zero.mpr hne) hpdvd
    have hpge2 : 2 ≤ p := hp.two_le
    have hp23 : p = 2 ∨ p = 3 := by omega
    rcases hp23 with h | h
    · exact hp2 h
    · exact hp3 h

end GGDatumModel

end CFSG.StandardType.GGFinModel
