module

public import CFSG.LocalAnalysis.StandardType.GGHalfFiveInnAll
public import CFSG.LocalAnalysis.StandardType.GGExcCompFieldInput
public import CFSG.LocalAnalysis.StandardType.GGReverseMarking

public section

namespace CFSG.StandardType

open CFSG.Blueprint

private def innerConjSet {G : Type} [Group G] (X : Subgroup G) : Subgroup G where
  carrier := {c : G | c ∈ Subgroup.normalizer (X : Set G) ∧
    ∃ n ∈ X, ∀ l ∈ X, c⁻¹ * l * c = n⁻¹ * l * n}
  one_mem' := by
    refine ⟨(Subgroup.normalizer (X : Set G)).one_mem, 1, X.one_mem, ?_⟩
    intro l _
    simp
  mul_mem' := by
    intro c1 c2 h1 h2
    obtain ⟨hn1, n1, hn1X, hc1⟩ := h1
    obtain ⟨hn2, n2, hn2X, hc2⟩ := h2
    refine ⟨(Subgroup.normalizer (X : Set G)).mul_mem hn1 hn2, n1 * n2,
      X.mul_mem hn1X hn2X, ?_⟩
    intro l hl
    have hmem : n1⁻¹ * l * n1 ∈ X := X.mul_mem (X.mul_mem (X.inv_mem hn1X) hl) hn1X
    calc (c1 * c2)⁻¹ * l * (c1 * c2)
        = c2⁻¹ * (c1⁻¹ * l * c1) * c2 := by group
      _ = c2⁻¹ * (n1⁻¹ * l * n1) * c2 := by rw [hc1 l hl]
      _ = n2⁻¹ * (n1⁻¹ * l * n1) * n2 := hc2 _ hmem
      _ = (n1 * n2)⁻¹ * l * (n1 * n2) := by group
  inv_mem' := by
    intro c h
    obtain ⟨hn, n, hnX, hc⟩ := h
    refine ⟨(Subgroup.normalizer (X : Set G)).inv_mem hn, n⁻¹, X.inv_mem hnX, ?_⟩
    intro l hl
    have hmem : c * l * c⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hn l).mp hl
    have hkey : c⁻¹ * (c * l * c⁻¹) * c = n⁻¹ * (c * l * c⁻¹) * n := hc _ hmem
    have hkey2 : n⁻¹ * (c * l * c⁻¹) * n = l := by rw [← hkey]; group
    have hmain : c * l * c⁻¹ = n * l * n⁻¹ := by
      calc c * l * c⁻¹ = n * (n⁻¹ * (c * l * c⁻¹) * n) * n⁻¹ := by group
        _ = n * l * n⁻¹ := by rw [hkey2]
    simpa using hmain

theorem ggInnerDiagOn_of_fieldAt {G : Type} [Group G] [Finite G] {X' : Subgroup G} {a : G} {Q : ℕ}
    (hq : CFSG.IsQuasisimple ↥X') (hQ : GGCompFieldAt Q X')
    (hnorm : a ∈ Subgroup.normalizer (X' : Set G))
    (hinn : ∃ k ∈ X', ∀ l ∈ X', a⁻¹ * l * a = k⁻¹ * l * k) :
    GGInnerDiagOn (Subgroup.zpowers a) X' := by
  obtain ⟨lab, -, hc, -, -, -, -, -, R, instR, hR, ⟨θ⟩⟩ := hQ
  letI : Group R := instR
  have hR2 : LieModel R (markTag lab) (markRank lab) 2 (markDeg lab) := by
    unfold MarkedModel at hR
    rwa [hc] at hR
  have hR3 : LieModel (↥X' ⧸ Subgroup.center ↥X') (markTag lab) (markRank lab) 2
      (markDeg lab) :=
    CFSG.LieType.CurtisTits.lieModel_of_mulEquiv θ.symm hR2
  have hmark : LargeEvenMarking ↥X' (fun _ _ _ _ _ _ => True) :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ _ => trivial)
      (largeEvenMarking_of_lieModel_centerQuot (Group.isPerfect_def.mp hq.1) hR3)
  have hT : Subgroup.zpowers a ≤ innerConjSet X' :=
    Subgroup.zpowers_le.mpr ⟨hnorm, hinn⟩
  have hinner : ∀ c ∈ Subgroup.zpowers a,
      ∃ n ∈ X', ∀ l ∈ X', c⁻¹ * l * c = n⁻¹ * l * n :=
    fun c hc => (hT hc).2
  exact ggInnerDiagOn_of_inner hmark (Subgroup.zpowers_le.mpr hnorm) hinner

end CFSG.StandardType
