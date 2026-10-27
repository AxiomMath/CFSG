module

public import CFSG.LocalAnalysis.StandardType.GGLinearTorusCompBlock
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotRootSL2Aut
public import CFSG.LieType.Universal.SpecialLinear

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint Matrix CFSG.SeitzReduction.LinearPilot

namespace LinTorus

variable {m : ℕ} {F : Type} [Field F] {G : Type} [Group G]

@[expose] noncomputable def blockSLMulEquiv (V : Finset (Fin (m + 1))) {k : ℕ} (hk : V.card = k) :
    blockSpecialLinear (K := F) V ≃* Matrix.SpecialLinearGroup (Fin k) F :=
  ((MonoidHom.ofInjective (blockEmbed_injective (K := F) V)).trans
    (MulEquiv.subgroupCongr (range_blockEmbed V))).symm.trans
    (reindexSpecialLinear (Finset.equivFinOfCardEq hk))

theorem commutator_blockSpecialLinear_eq_top {V : Finset (Fin (m + 1))} (hV : 3 ≤ V.card) :
    commutator (blockSpecialLinear (K := F) V) = ⊤ := by
  have h1 : (commutator (blockSpecialLinear (K := F) V)).map (blockSpecialLinear V).subtype =
      (⊤ : Subgroup (blockSpecialLinear (K := F) V)).map (blockSpecialLinear V).subtype := by
    rw [Subgroup.map_subtype_commutator, commutator_blockSpecialLinear_eq_of_three_le hV,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  exact Subgroup.map_injective (blockSpecialLinear V).subtype_injective h1

theorem ker_comp_subtype_le {ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G}
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F))
    (V : Finset (Fin (m + 1))) :
    (ψ.comp (blockSpecialLinear (K := F) V).subtype).ker ≤
      Subgroup.center (blockSpecialLinear (K := F) V) := by
  intro u hu
  have hz : (u : Matrix.SpecialLinearGroup (Fin (m + 1)) F) ∈ Subgroup.center _ := hker hu
  rw [Subgroup.mem_center_iff] at hz ⊢
  intro g
  exact Subtype.ext (hz g)

theorem range_comp_subtype (ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G)
    (V : Finset (Fin (m + 1))) :
    (ψ.comp (blockSpecialLinear (K := F) V).subtype).range = (blockSpecialLinear V).map ψ := by
  rw [MonoidHom.range_comp, Subgroup.range_subtype]

theorem nonempty_mulEquiv_quotient_center {ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G}
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F))
    {V : Finset (Fin (m + 1))} (hV : 3 ≤ V.card) {k : ℕ} (hk : V.card = k) :
    Nonempty (Matrix.ProjectiveSpecialLinearGroup (Fin k) F ≃*
      ↥((blockSpecialLinear (K := F) V).map ψ) ⧸
        Subgroup.center ↥((blockSpecialLinear (K := F) V).map ψ)) := by
  rw [← range_comp_subtype]
  set φ := ψ.comp (blockSpecialLinear (K := F) V).subtype with hφ
  have hU := commutator_blockSpecialLinear_eq_top (F := F) hV
  have hkerU := ker_comp_subtype_le hker V
  let q : blockSpecialLinear (K := F) V →* ↥φ.range ⧸ Subgroup.center ↥φ.range :=
    (QuotientGroup.mk' _).comp φ.rangeRestrict
  have hq : Function.Surjective q :=
    (QuotientGroup.mk'_surjective _).comp φ.rangeRestrict_surjective
  have hqk : q.ker = Subgroup.center _ := by
    ext u
    rw [MonoidHom.mem_ker]
    show (QuotientGroup.mk (φ.rangeRestrict u) : ↥φ.range ⧸ Subgroup.center ↥φ.range) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff]
    refine ⟨InnerDiagA.mem_center_of_rangeRestrict_mem_center hU φ hkerU, fun hu => ?_⟩
    rw [Subgroup.mem_center_iff]
    intro l
    obtain ⟨s, rfl⟩ := φ.rangeRestrict_surjective l
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hu s]
  let e₁ : (blockSpecialLinear (K := F) V ⧸ Subgroup.center (blockSpecialLinear (K := F) V)) ≃*
      ↥φ.range ⧸ Subgroup.center ↥φ.range :=
    (QuotientGroup.quotientMulEquivOfEq hqk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective q hq)
  let e₀ := (blockSLMulEquiv (F := F) V hk).symm
  let e₂ : Matrix.ProjectiveSpecialLinearGroup (Fin k) F ≃*
      (blockSpecialLinear (K := F) V ⧸ Subgroup.center (blockSpecialLinear (K := F) V)) :=
    QuotientGroup.congr _ _ e₀ (Subgroup.map_center_eq e₀)
  exact ⟨e₂.trans e₁⟩

theorem isQuasisimple_map_blockSpecialLinear
    {ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G}
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F))
    {V : Finset (Fin (m + 1))} (hV : 3 ≤ V.card) :
    CFSG.Assembly.IsQuasisimple ↥((blockSpecialLinear (K := F) V).map ψ) := by
  obtain ⟨θ⟩ := nonempty_mulEquiv_quotient_center hker hV rfl
  have hsimple : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin V.card) F) :=
    CFSG.BenderSuzuki.External.huppert_II_6_13 V.card (by omega) (.inl (by omega))
      (.inl (by omega))
  refine ⟨?_, θ.symm.isSimpleGroup⟩
  rw [← range_comp_subtype]
  set φ := ψ.comp (blockSpecialLinear (K := F) V).subtype with hφ
  have hU := commutator_blockSpecialLinear_eq_top (F := F) hV
  calc commutator ↥φ.range = ⁅(⊤ : Subgroup φ.range), ⊤⁆ := commutator_def _
    _ = ⁅(⊤ : Subgroup (blockSpecialLinear (K := F) V)).map φ.rangeRestrict,
        (⊤ : Subgroup (blockSpecialLinear (K := F) V)).map φ.rangeRestrict⁆ := by
      rw [Subgroup.map_top_of_surjective _ φ.rangeRestrict_surjective]
    _ = Subgroup.map φ.rangeRestrict
        ⁅(⊤ : Subgroup (blockSpecialLinear (K := F) V)), (⊤ : Subgroup _)⁆ :=
      (Subgroup.map_commutator _ _ _).symm
    _ = ⊤ := by
      rw [← commutator_def, hU, Subgroup.map_top_of_surjective _ φ.rangeRestrict_surjective]

theorem lieModel_map_blockSpecialLinear [Finite F] {f : ℕ} (hF : Nat.card F = 2 ^ f)
    (hf : 1 ≤ f) {ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G}
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F))
    {V : Finset (Fin (m + 1))} (hV : 3 ≤ V.card) :
    LieModel (↥((blockSpecialLinear (K := F) V).map ψ) ⧸
      Subgroup.center ↥((blockSpecialLinear (K := F) V).map ψ)) .PSL V.card 2 f := by
  obtain ⟨k, hk⟩ : ∃ k, V.card = k + 1 := ⟨V.card - 1, by omega⟩
  obtain ⟨θ⟩ := nonempty_mulEquiv_quotient_center hker hV hk
  have hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL (k + 1) 2 f := by
    refine ⟨Nat.prime_two, hf, by omega, ?_, ?_⟩
    · intro h
      simp only [Prod.mk.injEq] at h
      omega
    · intro h
      simp only [Prod.mk.injEq] at h
      omega
  rw [hk]
  exact Or.inl ⟨by decide, CFSG.LieType.CurtisTits.statedClassicalModel_of_mulEquiv θ
    (CFSG.LieType.Universal.SpecialLinear.statedClassicalModel_center_quotient k F hadm hF)⟩

end LinTorus

end CFSG.StandardType
