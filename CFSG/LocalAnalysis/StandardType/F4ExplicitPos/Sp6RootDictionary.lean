module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.RationalC3Part2
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.B3AlgebraicPart3

@[expose] public section

public noncomputable section

namespace CFSG.StandardType.F4ExplicitPos.Sp6RootDictionary

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Chevalley
  CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Universal CFSG.LieType.Universal.Symplectic
  CFSG.SeitzReduction.F4Pilot CFSG.Timmesfeld.LieEmbed
  C3Range C3Algebraic B3Algebraic
  CFSG.StandardType.F4ExplicitPos.B3Pinned CFSG.StandardType.F4ExplicitPos.RationalC3

noncomputable abbrev phiC
    (Ω : Type) [Field Ω] [CharP Ω 2] [Algebra (ZMod 2) Ω]
    [Algebra.IsAlgebraic (ZMod 2) Ω] (v : WeylGroup .F4) : ↥(StatedSp 3 Ω) →* ModGL .F4 Ω :=
  (MulAut.conj (canonicalRep (coxeterSystem .F4) Ω v)).toMonoidHom.comp
    ((adjointGroup .F4 Ω).subtype.comp (CFSG.StandardType.F4ExplicitPos.C3Algebraic.iOmega Ω))

noncomputable abbrev phiB
    (Ω : Type) [Field Ω] [CharP Ω 2] [Algebra (ZMod 2) Ω]
    [Algebra.IsAlgebraic (ZMod 2) Ω] (v : WeylGroup .F4) : ↥(StatedSp 3 Ω) →* ModGL .F4 Ω :=
  (MulAut.conj (canonicalRep (coxeterSystem .F4) Ω v)).toMonoidHom.comp
    ((adjointGroup .F4 Ω).subtype.comp (iBΩ Ω))

theorem phiC_eq_conjIM
    (Ω : Type) [Field Ω] [CharP Ω 2] [Algebra (ZMod 2) Ω]
    [Algebra.IsAlgebraic (ZMod 2) Ω] (v : WeylGroup .F4) :
    phiC Ω v = RationalC3.conjIM Ω (canonicalRep (coxeterSystem .F4) Ω v) := by
  apply MonoidHom.ext
  intro g
  simp only [phiC, MonoidHom.comp_apply]
  rw [CFSG.StandardType.F4ExplicitPos.RationalC3.conjIM_apply]
  change canonicalRep (coxeterSystem .F4) Ω v * ((C3Algebraic.iOmega Ω) g : ModGL .F4 Ω)
      * (canonicalRep (coxeterSystem .F4) Ω v)⁻¹ = _
  rfl

def dualRootF4 (γ : Fin 3 → ℤ) : Fin (Tag.rank .F4) → ℤ :=
  F4.dualRoot (c3ToF4 γ)

theorem map_c3RootSubgroup_phiC
    (Ω : Type) [Field Ω] [CharP Ω 2] [Algebra (ZMod 2) Ω]
    [Algebra.IsAlgebraic (ZMod 2) Ω] (v : WeylGroup .F4) {γ : Fin 3 → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartanC 3) ∅) :
    (CFSG.StandardType.F4ExplicitPos.C3Range.c3RootSubgroup (K := Ω) γ).map (phiC Ω v)
      = CFSG.Blueprint.Chevalley.rootSubgroup .F4 Ω (v • c3ToF4 γ) := by
  rw [← Subgroup.map_map]
  rw [CFSG.StandardType.F4ExplicitPos.C3Algebraic.map_c3RootSubgroup_eq_rootSubgroup_alg (K := Ω)
    (CFSG.StandardType.F4ExplicitPos.C3Algebraic.iOmega Ω)
    (fun γ c => CFSG.StandardType.F4ExplicitPos.C3Algebraic.iOmega_x Ω γ c) hγ]
  exact (canonical_weyl_root_transport .F4 Ω).2.1 v (c3ToF4 γ) (isRoot_c3ToF4 hγ)

theorem map_c3RootSubgroup_phiB
    (Ω : Type) [Field Ω] [CharP Ω 2] [Algebra (ZMod 2) Ω]
    [Algebra.IsAlgebraic (ZMod 2) Ω] (v : WeylGroup .F4) {γ : Fin 3 → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartanC 3) ∅) :
    (CFSG.StandardType.F4ExplicitPos.C3Range.c3RootSubgroup (K := Ω) γ).map (phiB Ω v)
      = CFSG.Blueprint.Chevalley.rootSubgroup .F4 Ω (v • dualRootF4 γ) := by
  rw [← Subgroup.map_map]
  rw [iBΩ_c3RootSubgroup Ω hγ]
  exact (canonical_weyl_root_transport .F4 Ω).2.1 v (dualRootF4 γ)
    (F4.isRoot_dualRoot (isRoot_c3ToF4 hγ))

theorem exists_rootGroup_map_eq_rootSubgroup_c3
    (Ω : Type) [Field Ω] [CharP Ω 2]
    [Algebra (ZMod 2) Ω] [Algebra.IsAlgebraic (ZMod 2) Ω] (v : WeylGroup .F4)
    {α : Fin (Tag.rank .F4) → ℤ} (hα : α ∈ (fun γ => v • γ) '' C3Range.c3RootSet) :
    ∃ β ∈ (CFSG.LieType.Universal.Symplectic.rootDatum 3 Ω).roots,
      ((CFSG.LieType.Universal.Symplectic.rootDatum 3 Ω).rootGroup β).map (phiC Ω v)
        = CFSG.Blueprint.Chevalley.rootSubgroup .F4 Ω α := by
  obtain ⟨γ, hγ, rfl⟩ := hα
  rw [CFSG.StandardType.F4ExplicitPos.C3Range.c3RootSet] at hγ
  obtain ⟨γ₀, hγ₀, rfl⟩ := hγ
  refine ⟨γ₀, ?_, ?_⟩
  · change γ₀ ∈ roots (isFiniteType_cartanC 3) ∅
    exact hγ₀
  · rw [← CFSG.StandardType.F4ExplicitPos.C3Algebraic.c3RootSubgroup_eq_rootGroup_alg (K := Ω) hγ₀]
    exact map_c3RootSubgroup_phiC Ω v hγ₀

theorem exists_rootGroup_map_eq_rootSubgroup_b3
    (Ω : Type) [Field Ω] [CharP Ω 2]
    [Algebra (ZMod 2) Ω] [Algebra.IsAlgebraic (ZMod 2) Ω] (v : WeylGroup .F4)
    {α : Fin (Tag.rank .F4) → ℤ} (hα : α ∈ (fun γ =>
        v • γ) '' CFSG.SeitzReduction.F4Pilot.b3LeviRoots) :
    ∃ β ∈ (CFSG.LieType.Universal.Symplectic.rootDatum 3 Ω).roots,
      ((CFSG.LieType.Universal.Symplectic.rootDatum 3 Ω).rootGroup β).map (phiB Ω v)
        = CFSG.Blueprint.Chevalley.rootSubgroup .F4 Ω α := by
  obtain ⟨δ, hδ, rfl⟩ := hα
  have hδroot : IsRoot .F4 δ := hδ.1
  have hdual : F4.dualRoot δ ∈ CFSG.StandardType.F4ExplicitPos.C3Range.c3RootSet := by
    rw [c3RootSet_eq_c3LeviRoots]
    have hrootd : IsRoot .F4 (F4.dualRoot δ) := F4.isRoot_dualRoot hδroot
    exact (dualRoot_mem_b3LeviRoots_iff hrootd).1
      (by rw [F4.dualRoot_dualRoot hδroot]; exact hδ)
  rw [CFSG.StandardType.F4ExplicitPos.C3Range.c3RootSet] at hdual
  obtain ⟨γ₀, hγ₀, hγ₀eq⟩ := hdual
  refine ⟨γ₀, ?_, ?_⟩
  · change γ₀ ∈ roots (isFiniteType_cartanC 3) ∅
    exact hγ₀
  · have hΨ : F4.dualRoot (c3ToF4 γ₀) = δ := by
      rw [hγ₀eq, F4.dualRoot_dualRoot hδroot]
    rw [← CFSG.StandardType.F4ExplicitPos.C3Algebraic.c3RootSubgroup_eq_rootGroup_alg (K := Ω) hγ₀]
    rw [map_c3RootSubgroup_phiB Ω v hγ₀]
    unfold dualRootF4
    rw [hΨ]

end CFSG.StandardType.F4ExplicitPos.Sp6RootDictionary

end

end
