module

public import CFSG.LocalAnalysis.StandardType.GGFinModelPkg
import CFSG.HardMathSupport.Timmesfeld.LangTorus.TorusAtExact
import CFSG.HardMathSupport.Timmesfeld.LangTorus.FiniteCentralizerRegular
import CFSG.LieType.Chevalley.SingleEdgePerfect

public section

namespace CFSG.StandardType.GGFinModel

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE

section Adjoint


private theorem ggLangPkg_adjoint_F4 {f : ℕ} (hf : 1 ≤ f) (D : LangDatum Tag.F4 GGL)
    (hΦ : D.Φ = Units.map (entrywiseHom (ggFrobT f))) :
    GGLangPkg D
      ((baseChangeGL (ggRatEmb f)).comp (adjointGroup Tag.F4 (GaloisField 2 f)).subtype) := by
  haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hKcard : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hFr : ∀ c : GGL, ggFrobT f c = c ^ Nat.card (GaloisField 2 f) := fun c => by
    rw [hKcard]
    exact ggFrobT_apply f c
  letI : Algebra (GaloisField 2 f) GGL := (ggRatEmb f).toAlgebra
  have hcomm : ∀ r : ZMod 2,
      ggRatEmb f (algebraMap (ZMod 2) (GaloisField 2 f) r) = algebraMap (ZMod 2) GGL r :=
    fun r => (IsAlgClosed.lift (R := ZMod 2) (S := GaloisField 2 f) (M := GGL)).commutes r
  haveI : Module.IsTorsionFree (GaloisField 2 f) GGL := {
    isSMulRegular := by
      intro r hr
      have hr0 : r ≠ 0 := hr.ne_zero
      have hfr0 : ggRatEmb f r ≠ 0 :=
        fun h => hr0 ((ggRatEmb f).injective (by rw [h, map_zero]))
      intro x y hxy
      change ggRatEmb f r * x = ggRatEmb f r * y at hxy
      exact mul_left_cancel₀ hfr0 hxy }
  have hcomp : RingHom.comp (algebraMap (GaloisField 2 f) GGL)
        (algebraMap (ZMod 2) (GaloisField 2 f)) =
      RingHom.comp (RingHom.id GGL) (algebraMap (ZMod 2) GGL) := by
    ext r
    exact hcomm r
  haveI : IsAlgClosure (GaloisField 2 f) GGL :=
    { isAlgClosed := inferInstance
      isAlgebraic := Algebra.IsAlgebraic.ringHom_of_comp_eq
        (f := algebraMap (ZMod 2) (GaloisField 2 f)) (g := RingHom.id GGL)
        (algebraMap (ZMod 2) (GaloisField 2 f)).injective Function.surjective_id hcomp }
  have hperf : commutator ↥(adjointGroup Tag.F4 (GaloisField 2 f)) = ⊤ :=
    single_edge_perfect Tag.F4 (GaloisField 2 f) (Or.inl rfl)
  have hex := (CFSG.RankThree.Chevalley.G2_F4_exact_finite_field_fixed_root_matrices
    Tag.F4 (Or.inr rfl) (GaloisField 2 f) GGL (ggFrobT f) hFr).1
  have hfix : D.fix = (adjointGroup Tag.F4 (GaloisField 2 f)).map
      (baseChangeGL (algebraMap (GaloisField 2 f) GGL)) := by
    rw [← hex]
    ext x
    rw [LangDatum.mem_fix, hΦ]
    rfl
  have hrange : ((baseChangeGL (ggRatEmb f)).comp
        (adjointGroup Tag.F4 (GaloisField 2 f)).subtype).range =
      (adjointGroup Tag.F4 (GaloisField 2 f)).map (baseChangeGL (ggRatEmb f)) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hfixr : D.fix = ((baseChangeGL (ggRatEmb f)).comp
        (adjointGroup Tag.F4 (GaloisField 2 f)).subtype).range := by
    rw [hfix]
    exact hrange.symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (baseChangeGL_injective (ggRatEmb f)).comp (Subgroup.subtype_injective _)
  · exact langDescent_exact (K := GaloisField 2 f) (L := GGL) (τ := Tag.F4) (Or.inr rfl)
      hFr D hΦ (p := 5) hperf
  · intro z hz hc
    refine eq_one_of_commute_image (K := GaloisField 2 f) (L := GGL) (ggRatEmb f) hz ?_
    rintro h ⟨y, hy, rfl⟩
    exact hc ⟨y, hy⟩
  · rw [hfixr, Subgroup.relIndex_self]
    norm_num

private theorem ggLangPkg_adjoint_untw {τ : Tag} (d : ℕ)
    (hτd : (τ = .E6 ∧ d = 3) ∨ (τ = .E7 ∧ d = 2) ∨ (τ = .E8 ∧ d = 1)) {f : ℕ}
    (hf : 1 ≤ f) (D : LangDatum τ GGL)
    (hΦ : D.Φ = Units.map (entrywiseHom (ggFrobT f))) :
    GGLangPkg D
      ((baseChangeGL (ggRatEmb f)).comp (adjointGroup τ (GaloisField 2 f)).subtype) := by
  haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hKcard : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hFr : ∀ c : GGL, ggFrobT f c = c ^ Nat.card (GaloisField 2 f) := fun c => by
    rw [hKcard]
    exact ggFrobT_apply f c
  letI : Algebra (GaloisField 2 f) GGL := (ggRatEmb f).toAlgebra
  have hcomm : ∀ r : ZMod 2,
      ggRatEmb f (algebraMap (ZMod 2) (GaloisField 2 f) r) = algebraMap (ZMod 2) GGL r :=
    fun r => (IsAlgClosed.lift (R := ZMod 2) (S := GaloisField 2 f) (M := GGL)).commutes r
  haveI : Module.IsTorsionFree (GaloisField 2 f) GGL := {
    isSMulRegular := by
      intro r hr
      have hr0 : r ≠ 0 := hr.ne_zero
      have hfr0 : ggRatEmb f r ≠ 0 :=
        fun h => hr0 ((ggRatEmb f).injective (by rw [h, map_zero]))
      intro x y hxy
      change ggRatEmb f r * x = ggRatEmb f r * y at hxy
      exact mul_left_cancel₀ hfr0 hxy }
  have hcomp : RingHom.comp (algebraMap (GaloisField 2 f) GGL)
        (algebraMap (ZMod 2) (GaloisField 2 f)) =
      RingHom.comp (RingHom.id GGL) (algebraMap (ZMod 2) GGL) := by
    ext r
    exact hcomm r
  haveI : IsAlgClosure (GaloisField 2 f) GGL :=
    { isAlgClosed := inferInstance
      isAlgebraic := Algebra.IsAlgebraic.ringHom_of_comp_eq
        (f := algebraMap (ZMod 2) (GaloisField 2 f)) (g := RingHom.id GGL)
        (algebraMap (ZMod 2) (GaloisField 2 f)).injective Function.surjective_id hcomp }
  have hτ' : τ = .F4 ∨ τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
    rcases hτd with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  have hd3 : d ≤ 3 := by rcases hτd with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> omega
  have hd0 : 0 < d := by rcases hτd with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> omega
  have hperf : commutator ↥(adjointGroup τ (GaloisField 2 f)) = ⊤ :=
    single_edge_perfect τ (GaloisField 2 f) hτ'
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
    exact mem_range_algebraMap_of_pow_card_eq (k := GaloisField 2 f) (by
      rw [hKcard]
      exact hcoord)
  have hidx := (finite_fixed_subgroup_rational (K := GaloisField 2 f) (L := GGL) (τ := τ) d hτd
    (ggFrobT f) hFr D.fix (fun x hx => ((hfixmem x).1 hx).1)
    (fun x hx => ((hfixmem x).1 hx).2)).1
  have hrange : ((baseChangeGL (ggRatEmb f)).comp
        (adjointGroup τ (GaloisField 2 f)).subtype).range =
      (adjointGroup τ (GaloisField 2 f)).map (baseChangeGL (ggRatEmb f)) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (baseChangeGL_injective (ggRatEmb f)).comp (Subgroup.subtype_injective _)
  · exact langDescent_untw (K := GaloisField 2 f) (L := GGL) (τ := τ) d hτd hFr D hΦ
      (p := 5) (by decide) (by decide) hperf
  · intro z hz hc
    refine eq_one_of_commute_image (K := GaloisField 2 f) (L := GGL) (ggRatEmb f) hz ?_
    rintro h ⟨y, hy, rfl⟩
    exact hc ⟨y, hy⟩
  · rw [hrange]
    exact (Nat.le_of_dvd hd0 hidx).trans hd3

theorem ggLangPkg_adjoint {τ : Tag} (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {f : ℕ}
    (hf : 1 ≤ f) (D : LangDatum τ GGL) (hΦ : D.Φ = Units.map (entrywiseHom (ggFrobT f))) :
    GGLangPkg D
      ((baseChangeGL (ggRatEmb f)).comp (adjointGroup τ (GaloisField 2 f)).subtype) := by
  rcases hτ with rfl | rfl | rfl | rfl
  · exact ggLangPkg_adjoint_F4 hf D hΦ
  · exact ggLangPkg_adjoint_untw 3 (Or.inl ⟨rfl, rfl⟩) hf D hΦ
  · exact ggLangPkg_adjoint_untw 2 (Or.inr (Or.inl ⟨rfl, rfl⟩)) hf D hΦ
  · exact ggLangPkg_adjoint_untw 1 (Or.inr (Or.inr ⟨rfl, rfl⟩)) hf D hΦ

end Adjoint

end CFSG.StandardType.GGFinModel
