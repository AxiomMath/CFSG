module

public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsBasic
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerExcModel

public section

namespace CFSG.StandardType

open CFSG.Assembly

section General

variable {C : Type*} [Group C]

@[expose] def GGRootCentQL (z : C) : Prop :=
  ∃ Q L : Subgroup C, IsPGroup 2 Q ∧ Q ⊔ L = Subgroup.centralizer ({z} : Set C) ∧
    L ≤ Subgroup.normalizer (Q : Set C) ∧ CFSG.IsQuasisimple L ∧
    L ≤ ggOTwoPrime (Subgroup.centralizer ({z} : Set C))

theorem GGRootCentQL.map {C' : Type*} [Group C'] {z : C} (h : GGRootCentQL z) (α : C ≃* C') :
    GGRootCentQL (α z) := by
  obtain ⟨Q, L, hQ2, hQL, hLQ, hL, hL2⟩ := h
  refine ⟨Q.map α.toMonoidHom, L.map α.toMonoidHom, hQ2.map _, ?_, ?_, ?_, ?_⟩
  · rw [← Subgroup.map_sup, hQL, RootCentExc.centralizer_map_mulEquiv]
  · rw [← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hLQ
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (L.equivMapOfInjective α.toMonoidHom α.injective) hL
  · rw [RootCentExc.centralizer_map_mulEquiv]
    exact (Subgroup.map_mono hL2).trans (LinFusion.map_ggOTwoPrime_le _ _)

theorem GGRootCentQL.conj {z : C} (h : GGRootCentQL z) (g : C) : GGRootCentQL (g * z * g⁻¹) :=
  h.map (MulAut.conj g)

theorem GGRootCentQL.of_conj {z g : C} (h : GGRootCentQL (g * z * g⁻¹)) : GGRootCentQL z := by
  have h' := h.conj g⁻¹
  rwa [show g⁻¹ * (g * z * g⁻¹) * g⁻¹⁻¹ = z by group] at h'

end General

section InG

variable {G : Type} [Group G]

theorem ggRCQL_range_inf_centralizer {C : Type*} [Group C] {φ : C →* G}
    (hφ : Function.Injective φ) (z : C) :
    φ.range ⊓ Subgroup.centralizer {φ z} = (Subgroup.centralizer ({z} : Set C)).map φ := by
  apply le_antisymm
  · rintro _ ⟨⟨s, rfl⟩, hs⟩
    refine ⟨s, ?_, rfl⟩
    have hs2 : φ s * φ z = φ z * φ s := Subgroup.mem_centralizer_singleton_iff.mp hs
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact hφ (by rw [map_mul, map_mul, hs2])
  · rintro _ ⟨s, hs, rfl⟩
    have hs2 : s * z = z * s := Subgroup.mem_centralizer_singleton_iff.mp hs
    refine Subgroup.mem_inf.mpr ⟨⟨s, rfl⟩, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, hs2, map_mul]

theorem ggRootCentDerivedAt_of_sup_eq [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {G₀ : Subgroup G} {r : G} {Q L : Subgroup G} (hQ2 : IsPGroup 2 Q)
    (hQL : Q ⊔ L = G₀ ⊓ Subgroup.centralizer {r}) (hLQ : L ≤ Subgroup.normalizer (Q : Set G))
    (hL : CFSG.IsQuasisimple L) (hL2 : L ≤ ggOTwoPrime (G₀ ⊓ Subgroup.centralizer {r})) :
    GGRootCentDerivedAt p G₀ r := by
  have hXC : ggRCSX G₀ r ≤ Q ⊔ L := (ggOTwoPrime_le _).trans hQL.ge
  exact ggRootCentDerivedAt_of_quasisimple hp hp2
    (OTwoGen.le_ggOTwoPrime_of_isPGroup ((le_sup_left : Q ≤ Q ⊔ L).trans hQL.le) hQ2) hQ2
    (hXC.trans (sup_le Subgroup.le_normalizer hLQ)) hL2 hL
    ((CFSG.Quasithin.perfectCore_le _).trans hXC) fun _ hy _ => hXC hy

theorem ggRootCentDerivedAt_of_model [Finite G] {U C : Type*} [Group U] [Group C]
    {ψ : U →* G} {π : U →* C} (hπ : Function.Surjective π) (hker : π.ker = ψ.ker) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {w : U} (hw : GGRootCentQL (π w)) :
    GGRootCentDerivedAt p ψ.range (ψ w) := by
  set Θ := AutSt.modelEquiv ψ π hπ hker with hΘ
  let Θ' : C →* G := ψ.range.subtype.comp Θ.toMonoidHom
  have hΘ' : Θ' (π w) = ψ w := AutSt.modelEquiv_apply ψ π hπ hker w
  have hinj : Function.Injective Θ' := Subtype.val_injective.comp Θ.injective
  have hrange : Θ'.range = ψ.range := by
    ext x
    constructor
    · rintro ⟨c, rfl⟩
      exact (Θ c).2
    · intro hx
      exact ⟨Θ.symm ⟨x, hx⟩, by simp [Θ']⟩
  obtain ⟨Q, L, hQ2, hQL, hLQ, hL, hL2⟩ := hw
  have hC := ggRCQL_range_inf_centralizer hinj (π w)
  rw [hrange, hΘ'] at hC
  refine ggRootCentDerivedAt_of_sup_eq hp hp2 (hQ2.map Θ') ?_ (ggRCST_map_le_normalizer Θ' hLQ)
    (CFSG.LocalCores.isQuasisimple_of_mulEquiv (L.equivMapOfInjective Θ' hinj) hL) ?_
  · rw [hC, ← hQL, Subgroup.map_sup]
  · rw [hC]
    exact (Subgroup.map_mono hL2).trans (LinFusion.map_ggOTwoPrime_le Θ' _)

end InG

end CFSG.StandardType
