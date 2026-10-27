module

public import CFSG.Assembly.LargeEvenDefs
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagBridgeTypeA
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoKGroup
import CFSG.Assembly.GL83LieDefs
import CFSG.LocalAnalysis.StandardType.GGReverseMarking
import CFSG.LinearAlgebra.LinearGroups.Perfect
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_6_13

public section

namespace CFSG.StandardType

open CFSG.Assembly Matrix

namespace KGND

variable {m : ℕ} {F : Type} [Field F]

@[expose] def slConjSet {X : Type} [Group X]
    (φ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* X) : Set (MulAut X) :=
  {α | ∃ A : GL (Fin (m + 1)) F, ∀ B, α (φ B) = φ (InnerDiagA.conjSL A B)}

private theorem conjSL_slEquiv (B₀ B : Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
    InnerDiagA.conjSL (InnerDiagA.slEquiv m F B₀ : GL (Fin (m + 1)) F) B =
      B₀ * B * B₀⁻¹ := by
  apply (InnerDiagA.slEquiv m F).injective
  rw [InnerDiagA.slEquiv_conjSL, map_mul, map_mul, map_inv]
  apply Subtype.ext
  rw [MulAut.conjNormal_apply]
  rfl

theorem conj_mem_slConjSet {X : Type} [Group X]
    (φ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* X)
    (B₀ : Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
    MulAut.conj (φ B₀) ∈ slConjSet φ := by
  refine ⟨(InnerDiagA.slEquiv m F B₀ : GL (Fin (m + 1)) F), fun B => ?_⟩
  rw [MulAut.conj_apply, conjSL_slEquiv, map_mul, map_mul, map_inv]

theorem largeEvenMarking_slConjSet {m : ℕ} {F : Type} [Field F] [Finite F] {f : ℕ}
    (hF : Nat.card F = 2 ^ f) (hf : 1 ≤ f) (hm : 1 ≤ m) (hm1 : m = 1 → 2 ≤ f)
    {X : Type} [Group X] (φ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* X)
    (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F)) :
    LargeEvenMarking X (fun lab R _ I _ θ => GGChevStTag lab ∧
      ∀ α ∈ slConjSet φ, ∃ ψ ∈ I, ∀ y : X,
        ψ (θ (QuotientGroup.mk y)) = θ (QuotientGroup.mk (α y))) := by
  classical
  let H := LargeEvenSLGroup (Fin (m + 1)) F
  let q₁ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* X ⧸ Subgroup.center X :=
    (QuotientGroup.mk' _).comp φ
  let q₂ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* LargeEvenProj H :=
    (LargeEvenProjMk H).comp (InnerDiagA.slEquiv m F).toMonoidHom
  have hq₁ : Function.Surjective q₁ := (QuotientGroup.mk'_surjective _).comp hφ
  have hq₂ : Function.Surjective q₂ :=
    (QuotientGroup.mk'_surjective _).comp (InnerDiagA.slEquiv m F).surjective
  have h4of : m = 1 → 4 ≤ Nat.card F := fun hm' => by
    have hf2 : 2 ≤ f := hm1 hm'
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
  have hperf : commutator (Matrix.SpecialLinearGroup (Fin (m + 1)) F) = ⊤ := by
    haveI : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin (m + 1)) F) := by
      refine CFSG.LinearGroups.special_linear_isPerfect (by omega) ?_
      rcases Nat.lt_or_ge m 2 with hlt | hge
      · right
        haveI : Fintype F := Fintype.ofFinite F
        have hcard : 4 ≤ (Finset.univ : Finset F).card := by
          rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
          exact h4of (by omega)
        obtain ⟨t, -, ht⟩ :=
          Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4) hcard
        exact ⟨t, ht⟩
      · left; omega
    exact Group.IsPerfect.commutator_eq_top
  have hk₁ : q₁.ker = Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F) := by
    ext u
    rw [MonoidHom.mem_ker]
    show (QuotientGroup.mk (φ u) : X ⧸ Subgroup.center X) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff]
    constructor
    · intro hu
      refine InnerDiagA.mem_center_of_rangeRestrict_mem_center hperf φ hker ?_
      rw [Subgroup.mem_center_iff]
      intro l
      apply Subtype.ext
      exact Subgroup.mem_center_iff.mp hu l
    · intro hu
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨s, rfl⟩ := hφ y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hu s]
  have hk₂ : q₂.ker = Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F) := by
    ext u
    rw [MonoidHom.mem_ker]
    show (QuotientGroup.mk ((InnerDiagA.slEquiv m F) u) : LargeEvenProj H) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, largeEvenScalars_def,
      MonoidHom.mem_range]
    constructor
    · rintro ⟨c, hc⟩
      have hmat : (u : Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
          Matrix.scalar (Fin (m + 1)) (c : F) := by
        rw [← InnerDiagA.coe_slEquiv, ← hc, Matrix.GeneralLinearGroup.coe_scalar]
      rw [Subgroup.mem_center_iff]
      intro v
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hmat]
      exact (Matrix.scalar_commute (c : F) (fun r => Commute.all _ r) _).eq.symm
    · intro hu
      obtain ⟨r, hr, hru⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hu
      have hr0 : r ≠ 0 := by
        rintro rfl
        rw [zero_pow (by simp)] at hr
        exact zero_ne_one hr
      exact ⟨Units.mk0 r hr0, Units.ext (by
        rw [Matrix.GeneralLinearGroup.coe_scalar, InnerDiagA.coe_slEquiv]
        exact hru)⟩
  let θ : X ⧸ Subgroup.center X ≃* LargeEvenProj H :=
    (QuotientGroup.quotientKerEquivOfSurjective q₁ hq₁).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq (hk₁.trans hk₂.symm)).trans
        (QuotientGroup.quotientKerEquivOfSurjective q₂ hq₂))
  have hθ : ∀ u, θ (q₁ u) = q₂ u := fun u => by
    have h1 : (QuotientGroup.quotientKerEquivOfSurjective q₁ hq₁).symm (q₁ u) =
        (u : Matrix.SpecialLinearGroup (Fin (m + 1)) F ⧸ q₁.ker) :=
      (MulEquiv.symm_apply_eq _).mpr rfl
    simp only [θ, MulEquiv.trans_apply, h1, QuotientGroup.quotientMulEquivOfEq_mk]
    rfl
  have hcomm : commutator X = ⊤ := by
    have h1 := congrArg (Subgroup.map φ) hperf
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective _ hφ] at h1
    rw [commutator_def]
    exact h1
  let e : LargeEvenProj H ≃* Matrix.ProjectiveSpecialLinearGroup (Fin (m + 1)) F :=
    (QuotientGroup.quotientKerEquivOfSurjective q₂ hq₂).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hk₂)
  have hPSL : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin (m + 1)) F) := by
    refine CFSG.BenderSuzuki.External.huppert_II_6_13 (m + 1) (by omega) ?_ ?_
    · rcases Nat.lt_or_ge m 2 with hlt | hge
      · right
        have := h4of (by omega)
        omega
      · left; omega
    · rcases Nat.lt_or_ge m 2 with hlt | hge
      · right
        have := h4of (by omega)
        omega
      · left; omega
  have hsimple : IsSimpleGroup (LargeEvenProj H) :=
    (MulEquiv.isSimpleGroup_congr e).mpr hPSL
  have hnonab : ∃ a b : LargeEvenProj H, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := exists_mul_ne_mul_centerQuot_of_perfect hperf hPSL.toNontrivial
    refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
    simpa using congrArg e h
  have hkey : GGChevStTag ⟨.A, m, f⟩ ∧
      ∀ α ∈ slConjSet φ, ∃ ψ ∈ LargeEvenMatConjImage (LargeEvenProjMk H) Set.univ,
        ∀ y : X, ψ (θ (QuotientGroup.mk y)) = θ (QuotientGroup.mk (α y)) := by
    refine ⟨by simp [GGChevStTag], ?_⟩
    intro α hα
    obtain ⟨A, hA⟩ := hα
    refine ⟨TableB.linConjAut (Fin (m + 1)) F A, InnerDiagA.linConjAut_mem A, ?_⟩
    intro y
    obtain ⟨u, rfl⟩ := hφ y
    rw [hA u]
    change TableB.linConjAut (Fin (m + 1)) F A (θ (q₁ u)) =
      θ (q₁ (InnerDiagA.conjSL A u))
    rw [hθ u, hθ (InnerDiagA.conjSL A u)]
    change TableB.linConjAut (Fin (m + 1)) F A
        (((InnerDiagA.slEquiv m F) u : ↥H) : LargeEvenProj H) =
      (((InnerDiagA.slEquiv m F) (InnerDiagA.conjSL A u) : ↥H) : LargeEvenProj H)
    rw [TableB.linConjAut_mk, InnerDiagA.slEquiv_conjSL]
  exact ⟨hcomm, ⟨.A, m, f⟩, ⟨hf, hm, hm1⟩, F, inferInstance, inferInstance, hF,
    hsimple, hnonab, θ, hkey⟩

end KGND

end CFSG.StandardType
