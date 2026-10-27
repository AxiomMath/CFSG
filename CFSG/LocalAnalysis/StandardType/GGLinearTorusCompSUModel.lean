module

public import CFSG.LocalAnalysis.StandardType.GGLinearTorusCompSUComp
public import CFSG.LocalAnalysis.StandardType.GGLinearTorusCompModel

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint Matrix CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank

namespace SUTorus

variable {K : Type} [Field K] {f n : ℕ} {G : Type} [Group G]

theorem isPerfect_blockSU (h : UnitaryFieldData 2 f K) {V : Finset (Fin n)} (hV : 3 ≤ V.card)
    (hVq : (V.card, 2 ^ f) ≠ (3, 2)) :
    Group.IsPerfect ↥(TableBUE.blockSU (K := K) (n := f) V) := by
  have : Finite K := h.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hperf : Group.IsPerfect ↥(unitarySU 2 f K V.card) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU h.card_eq_sq hV hVq
  exact Group.IsPerfect.ofSurjective (f := (TableBUE.blockSUEquiv V h).toMonoidHom)
    (TableBUE.blockSUEquiv V h).surjective

theorem ker_comp_subtype_blockSU_le {ψ : ↥(unitarySU 2 f K n) →* G}
    (hker : ψ.ker ≤ Subgroup.center ↥(unitarySU 2 f K n)) (V : Finset (Fin n)) :
    (ψ.comp (TableBUE.blockSU (K := K) (n := f) V).subtype).ker ≤
      Subgroup.center ↥(TableBUE.blockSU (K := K) (n := f) V) := by
  intro u hu
  have hz : (u : ↥(unitarySU 2 f K n)) ∈ Subgroup.center _ := hker hu
  rw [Subgroup.mem_center_iff] at hz ⊢
  intro g
  exact Subtype.ext (hz g)

theorem range_comp_subtype_blockSU (ψ : ↥(unitarySU 2 f K n) →* G) (V : Finset (Fin n)) :
    (ψ.comp (TableBUE.blockSU (K := K) (n := f) V).subtype).range =
      (TableBUE.blockSU (K := K) (n := f) V).map ψ := by
  rw [MonoidHom.range_comp, Subgroup.range_subtype]

theorem nonempty_mulEquiv_quotient_center_blockSU (h : UnitaryFieldData 2 f K)
    {ψ : ↥(unitarySU 2 f K n) →* G} (hker : ψ.ker ≤ Subgroup.center ↥(unitarySU 2 f K n))
    {V : Finset (Fin n)} (hV : 3 ≤ V.card) (hVq : (V.card, 2 ^ f) ≠ (3, 2)) :
    Nonempty (↥((TableBUE.blockSU (K := K) (n := f) V).map ψ) ⧸
        Subgroup.center ↥((TableBUE.blockSU (K := K) (n := f) V).map ψ) ≃*
      StatedProj (StatedSU V.card (2 ^ f) K)) := by
  have : Finite K := h.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← range_comp_subtype_blockSU]
  set U := TableBUE.blockSU (K := K) (n := f) V with hU
  set φ := ψ.comp U.subtype with hφ
  have hUp : commutator ↥U = ⊤ := Group.isPerfect_def.mp (isPerfect_blockSU h hV hVq)
  have hkerU := ker_comp_subtype_blockSU_le hker V
  let q : ↥U →* ↥φ.range ⧸ Subgroup.center ↥φ.range :=
    (QuotientGroup.mk' _).comp φ.rangeRestrict
  have hq : Function.Surjective q :=
    (QuotientGroup.mk'_surjective _).comp φ.rangeRestrict_surjective
  have hqk : q.ker = Subgroup.center _ := by
    ext u
    rw [MonoidHom.mem_ker]
    show (QuotientGroup.mk (φ.rangeRestrict u) : ↥φ.range ⧸ Subgroup.center ↥φ.range) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff]
    refine ⟨InnerDiagA.mem_center_of_rangeRestrict_mem_center hUp φ hkerU, fun hu => ?_⟩
    rw [Subgroup.mem_center_iff]
    intro l
    obtain ⟨s, rfl⟩ := φ.rangeRestrict_surjective l
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hu s]
  let e₁ : (↥U ⧸ Subgroup.center ↥U) ≃* ↥φ.range ⧸ Subgroup.center ↥φ.range :=
    (QuotientGroup.quotientMulEquivOfEq hqk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective q hq)
  let e₀ := (TableBUE.blockSUEquiv V h).symm
  let e₂ : (↥U ⧸ Subgroup.center ↥U) ≃*
      (↥(unitarySU 2 f K V.card) ⧸ Subgroup.center ↥(unitarySU 2 f K V.card)) :=
    QuotientGroup.congr _ _ e₀ (Subgroup.map_center_eq e₀)
  have hZ := (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card
    (F := K) (p := 2) (f := f) h.card_eq_sq hV hVq).2
  let e₃ : (↥(unitarySU 2 f K V.card) ⧸ Subgroup.center ↥(unitarySU 2 f K V.card)) ≃*
      StatedProj (StatedSU V.card (2 ^ f) K) :=
    QuotientGroup.quotientMulEquivOfEq hZ
  exact ⟨e₁.symm.trans (e₂.trans e₃)⟩

theorem isQuasisimple_map_blockSU (h : UnitaryFieldData 2 f K)
    {ψ : ↥(unitarySU 2 f K n) →* G} (hker : ψ.ker ≤ Subgroup.center ↥(unitarySU 2 f K n))
    {V : Finset (Fin n)} (hV : 3 ≤ V.card) (hVq : (V.card, 2 ^ f) ≠ (3, 2)) :
    CFSG.Assembly.IsQuasisimple ↥((TableBUE.blockSU (K := K) (n := f) V).map ψ) := by
  have : Finite K := h.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨θ⟩ := nonempty_mulEquiv_quotient_center_blockSU h hker hV hVq
  have hsimple : IsSimpleGroup (StatedProj (StatedSU V.card (2 ^ f) K)) :=
    CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K 2 f h.card_eq_sq V.card hV
      hVq
  refine ⟨?_, θ.isSimpleGroup⟩
  rw [← range_comp_subtype_blockSU]
  set φ := ψ.comp (TableBUE.blockSU (K := K) (n := f) V).subtype with hφ
  have hU : commutator ↥(TableBUE.blockSU (K := K) (n := f) V) = ⊤ :=
    Group.isPerfect_def.mp (isPerfect_blockSU h hV hVq)
  calc commutator ↥φ.range = ⁅(⊤ : Subgroup φ.range), ⊤⁆ := commutator_def _
    _ = ⁅(⊤ : Subgroup (TableBUE.blockSU (K := K) (n := f) V)).map φ.rangeRestrict,
        (⊤ : Subgroup (TableBUE.blockSU (K := K) (n := f) V)).map φ.rangeRestrict⁆ := by
      rw [Subgroup.map_top_of_surjective _ φ.rangeRestrict_surjective]
    _ = Subgroup.map φ.rangeRestrict
        ⁅(⊤ : Subgroup (TableBUE.blockSU (K := K) (n := f) V)), (⊤ : Subgroup _)⁆ :=
      (Subgroup.map_commutator _ _ _).symm
    _ = ⊤ := by
      rw [← commutator_def, hU, Subgroup.map_top_of_surjective _ φ.rangeRestrict_surjective]

theorem lieModel_map_blockSU (h : UnitaryFieldData 2 f K)
    {ψ : ↥(unitarySU 2 f K n) →* G} (hker : ψ.ker ≤ Subgroup.center ↥(unitarySU 2 f K n))
    {V : Finset (Fin n)} (hV : 3 ≤ V.card) (hVq : (V.card, 2 ^ f) ≠ (3, 2)) :
    LieModel (↥((TableBUE.blockSU (K := K) (n := f) V).map ψ) ⧸
      Subgroup.center ↥((TableBUE.blockSU (K := K) (n := f) V).map ψ)) .PSU V.card 2 f := by
  have : Finite K := h.finite
  obtain ⟨θ⟩ := nonempty_mulEquiv_quotient_center_blockSU h hker hV hVq
  exact Or.inl ⟨by decide, ⟨Nat.prime_two, h.one_le, hV, hVq⟩, K, inferInstance, inferInstance,
    h.card_eq_sq, ⟨θ⟩⟩

end SUTorus

end CFSG.StandardType
