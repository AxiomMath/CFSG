module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutTrialityBridgeLang
public import CFSG.RankThree.PartTwo.Sec21.LangTwistedProofD4Geom
public import CFSG.RankThree.PartTwo.Sec21.LangTwistedProofD4Cent
public import CFSG.RankThree.PartTwo.Sec21.LangTwistedProofD4SecIrred

public section

namespace CFSG.StandardType

namespace TriBridge

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.StandardType.Triality CFSG.RankThree.PartTwo.Sec8

set_option linter.unusedSectionVars false


section Lang

variable {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]

theorem frobTwistGL_one_mem [Fact (Nat.Prime 2)] (e : ℕ) {g : ModGL TwistTag.D4.tag L}
    (hg : g ∈ adjointGroup TwistTag.D4.tag L) :
    frobTwistGL TwistTag.D4.tag L 2 e 1 g ∈ adjointGroup TwistTag.D4.tag L := by
  rw [frobTwistGL_apply, one_mul, inv_one, mul_one]
  exact entrywiseFrobGL_mem 2 e hg

theorem exists_inv_mul_frob_untw [Fact (Nat.Prime 2)] {e : ℕ} (he : 1 ≤ e)
    {A : ModGL TwistTag.D4.tag L} (hA : frobTwistGL TwistTag.D4.tag L 2 e 1 A = A)
    (hirr : IsPointIrreducible L (transportPoints (modGLPoint TwistTag.D4.tag L)
      (graphCentralizer TwistTag.D4.tag L A))) :
    ∀ c ∈ graphCentralizer TwistTag.D4.tag L A, ∃ z ∈ graphCentralizer TwistTag.D4.tag L A,
      z⁻¹ * frobTwistGL TwistTag.D4.tag L 2 e 1 z = c := by
  obtain ⟨hZ, -, -, -⟩ := graphCentralizer_realization A hirr
  have hFZ : ∀ g ∈ graphCentralizer TwistTag.D4.tag L A,
      frobTwistGL TwistTag.D4.tag L 2 e 1 g ∈ graphCentralizer TwistTag.D4.tag L A := by
    intro g hg
    obtain ⟨hgG, hgc⟩ := Subgroup.mem_inf.1 hg
    rw [Subgroup.mem_centralizer_singleton_iff] at hgc
    refine Subgroup.mem_inf.2 ⟨frobTwistGL_one_mem e hgG, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    conv_lhs => rw [← hA]
    conv_rhs => rw [← hA]
    rw [← map_mul, ← map_mul, hgc]
  obtain ⟨-, -, -, hlang⟩ := exists_frobTwist_restriction 2 hZ he 1 hFZ
  exact hlang

theorem exists_fixed_conj_of_lang_untw [Fact (Nat.Prime 2)] {e : ℕ} (he : 1 ≤ e)
    {A s x : ModGL TwistTag.D4.tag L} (hA : frobTwistGL TwistTag.D4.tag L 2 e 1 A = A)
    (hs : frobTwistGL TwistTag.D4.tag L 2 e 1 s = s)
    (hirr : IsPointIrreducible L (transportPoints (modGLPoint TwistTag.D4.tag L)
      (graphCentralizer TwistTag.D4.tag L A)))
    (hx : x ∈ adjointGroup TwistTag.D4.tag L) (hxs : x * s * x⁻¹ = A) :
    ∃ y ∈ adjointGroup TwistTag.D4.tag L,
      frobTwistGL TwistTag.D4.tag L 2 e 1 y = y ∧ y * s * y⁻¹ = A := by
  set F := frobTwistGL TwistTag.D4.tag L 2 e 1 with hFdef
  have hFx : F x * s * (F x)⁻¹ = A := by
    have h := congrArg F hxs
    rwa [map_mul, map_mul, map_inv, hs, hA] at h
  have hcZ : x * (F x)⁻¹ ∈ graphCentralizer TwistTag.D4.tag L A := by
    refine Subgroup.mem_inf.2 ⟨mul_mem hx (inv_mem (frobTwistGL_one_mem e hx)), ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc x * (F x)⁻¹ * A = x * ((F x)⁻¹ * A * F x) * (F x)⁻¹ := by group
      _ = x * s * x⁻¹ * (x * (F x)⁻¹) := by rw [← hFx]; group
      _ = A * (x * (F x)⁻¹) := by rw [hxs]
  obtain ⟨z, hzZ, hzc⟩ := exists_inv_mul_frob_untw he hA hirr _ hcZ
  have hzc' : z⁻¹ * F z = x * (F x)⁻¹ := hzc
  obtain ⟨hzG, hzA⟩ := Subgroup.mem_inf.1 hzZ
  rw [Subgroup.mem_centralizer_singleton_iff] at hzA
  refine ⟨z * x, mul_mem hzG hx, ?_, ?_⟩
  · have hFz : F z = z * (x * (F x)⁻¹) := by rw [← hzc']; group
    rw [map_mul, hFz]
    group
  · calc z * x * s * (z * x)⁻¹ = z * (x * s * x⁻¹) * z⁻¹ := by group
      _ = A := by rw [hxs, hzA]; group

end Lang

section Classes

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_conj_classes_D4 {x : ModGL TwistTag.D4.tag K}
    (hx : x ∈ adjointGroup TwistTag.D4.tag K)
    (hx3 : (x * (diagramMap TwistTag.D4 K)⁻¹) ^ 3 = 1) :
    ∃ y ∈ adjointGroup TwistTag.D4.tag K,
      y * (x * (diagramMap TwistTag.D4 K)⁻¹) * y⁻¹ = (diagramMap TwistTag.D4 K)⁻¹ ∨
        y * (x * (diagramMap TwistTag.D4 K)⁻¹) * y⁻¹ =
          d4TrialityY0 K * (diagramMap TwistTag.D4 K)⁻¹ := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  set f : ℕ := (n : ℕ) with hfdef
  have hf : 1 ≤ f := n.pos
  have hK : Nat.card K = 2 ^ f := by rw [Nat.card_eq_fintype_card, hn]
  set L := AlgebraicClosure K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  have hιP : baseChangeGL (algebraMap K L) (diagramMap TwistTag.D4 K) =
      diagramMap TwistTag.D4 L := baseChangeGL_diagramMap _ TwistTag.D4
  have hιs : baseChangeGL (algebraMap K L) (x * (diagramMap TwistTag.D4 K)⁻¹) =
      baseChangeGL (algebraMap K L) x * (diagramMap TwistTag.D4 L)⁻¹ := by
    rw [map_mul, map_inv, hιP]
  have hs3 : (baseChangeGL (algebraMap K L) x * (diagramMap TwistTag.D4 L)⁻¹) ^ 3 = 1 := by
    rw [← hιs, ← map_pow, hx3, map_one]
  have halg := LangTwistedProof.isAlgebraic_zmod_algebraicClosure K 2
  obtain ⟨g, hg, hgA⟩ := d4TrialityGeomClasses_holds L halg (baseChangeGL (algebraMap K L) x)
    (baseChangeGL_mem_adjointGroup (algebraMap K L) hx) hs3
  have hFr : ∀ c : L, iterateFrobenius L 2 f c = c ^ Nat.card K := fun c => by
    rw [iterateFrobenius_def, hK]
  have hFι : ∀ h : ModGL TwistTag.D4.tag K,
      frobTwistGL TwistTag.D4.tag L 2 f 1 (baseChangeGL (algebraMap K L) h) =
        baseChangeGL (algebraMap K L) h := by
    intro h
    rw [frobTwistGL_apply, one_mul, inv_one, mul_one]
    exact units_map_entrywiseHom_baseChangeGL_algebraMap _ hFr h
  have hs : frobTwistGL TwistTag.D4.tag L 2 f 1
      (baseChangeGL (algebraMap K L) x * (diagramMap TwistTag.D4 L)⁻¹) =
        baseChangeGL (algebraMap K L) x * (diagramMap TwistTag.D4 L)⁻¹ := by
    rw [← hιs, hFι]
  have hy0 : baseChangeGL (algebraMap K L) (d4TrialityY0 K) = d4TrialityY0 L :=
    LangTwistedProof.baseChangeGL_d4TrialityY0 _
  have hdesc : ∀ {A₀ : ModGL TwistTag.D4.tag K}
      (hirr : IsPointIrreducible L (transportPoints (modGLPoint TwistTag.D4.tag L)
        (graphCentralizer TwistTag.D4.tag L (baseChangeGL (algebraMap K L) A₀)))),
      g * (baseChangeGL (algebraMap K L) x * (diagramMap TwistTag.D4 L)⁻¹) * g⁻¹ =
        baseChangeGL (algebraMap K L) A₀ →
      ∃ y ∈ adjointGroup TwistTag.D4.tag K, y * (x * (diagramMap TwistTag.D4 K)⁻¹) * y⁻¹ = A₀ := by
    intro A₀ hirr hA
    obtain ⟨y, hy, hyF, hys⟩ := exists_fixed_conj_of_lang_untw hf (hFι A₀) hs hirr hg hA
    have hyF' : Units.map (entrywiseHom (iterateFrobenius L 2 f)) y = y := by
      rw [frobTwistGL_apply, one_mul, inv_one, mul_one] at hyF
      exact hyF
    obtain ⟨yK, hyK, rfl⟩ := mem_range_of_frobenius_fixed_D4 (K := K) L _ hFr hy hyF'
    refine ⟨yK, hyK, baseChangeGL_injective (algebraMap K L) ?_⟩
    rw [map_mul, map_mul, map_inv, hιs]
    exact hys
  rcases hgA with hA | hA
  · have hA' : g * (baseChangeGL (algebraMap K L) x * (diagramMap TwistTag.D4 L)⁻¹) * g⁻¹ =
        baseChangeGL (algebraMap K L) (diagramMap TwistTag.D4 K)⁻¹ := by
      rw [map_inv, hιP]
      exact hA
    have hirr := d4DiagramCentIrred_holds L
    rw [← hιP, ← map_inv] at hirr
    obtain ⟨y, hy, hys⟩ := hdesc hirr hA'
    exact ⟨y, hy, Or.inl hys⟩
  · have hA' : g * (baseChangeGL (algebraMap K L) x * (diagramMap TwistTag.D4 L)⁻¹) * g⁻¹ =
        baseChangeGL (algebraMap K L) (d4TrialityY0 K * (diagramMap TwistTag.D4 K)⁻¹) := by
      rw [map_mul, map_inv, hιP, hy0]
      exact hA
    have hirr := d4SecondCentIrred_holds L
    rw [← hιP, ← hy0, ← map_inv, ← map_mul] at hirr
    obtain ⟨y, hy, hys⟩ := hdesc hirr hA'
    exact ⟨y, hy, Or.inr hys⟩

end Classes

section Input

theorem coe_bridge_theta {K : Type} [Field K] [Finite K] [CharP K 2] (z : Om8 K) :
    (bridge (theta z) : ModGL TwistTag.D4.tag K) =
      diagramMap TwistTag.D4 K * bridge z * (diagramMap TwistTag.D4 K)⁻¹ := by
  have h1 := coe_bridge_theta_fieldAutP (K := K) 1 z
  rw [map_one, MulAut.one_apply] at h1
  rw [h1, ← twistHom_id_eq]
  rfl

theorem diagramMap_inv_conj_mem {K : Type} [Field K] {w : ModGL TwistTag.D4.tag K}
    (hw : w ∈ adjointGroup TwistTag.D4.tag K) :
    (diagramMap TwistTag.D4 K)⁻¹ * w * diagramMap TwistTag.D4 K ∈
      adjointGroup TwistTag.D4.tag K := by
  have h := conj_mem_adjointGroup_of_map_eq (map_conj_diagramMap_zpow TwistTag.D4 K (-1)) w hw
  rwa [zpow_neg_one, inv_inv] at h

end Input

end TriBridge

namespace TriBridge

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.StandardType.Triality CFSG.RankThree.PartTwo.Sec8

@[expose] def GGD4SecondCentPGLInput :
    Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 3 ∣ Nat.card K - 1 →
    Nonempty (↥(CFSG.LieType.AlgebraicGroups.graphCentralizer TwistTag.D4.tag K
      (CFSG.RankThree.PartTwo.Sec8.d4TrialityY0 K * (diagramMap TwistTag.D4 K)⁻¹)) ≃*
        Matrix.ProjGenLinGroup (Fin 3) K)

end TriBridge

end CFSG.StandardType
