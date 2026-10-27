module

public import CFSG.RankThree.PartTwo.Sec11.FieldCentRigid82
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.RationalC3Part1

@[expose] public section

public noncomputable section

namespace CFSG.StandardType.F4ExplicitPos.RationalC3
open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType
  CFSG.LieType.Chevalley CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Universal.Symplectic CFSG.Timmesfeld.LieEmbed
  CFSG.SeitzReduction.F4Pilot
  CFSG.StandardType.F4ExplicitPos.BaseChange CFSG.StandardType.F4ExplicitPos.RootBaseChange
  CFSG.StandardType.F4ExplicitPos.PinnedBaseChange
  CFSG.HardMathSupport.Timmesfeld.LangTorus
open scoped Matrix

section Naturality

theorem map_Phi_c3RootSubgroup
    (Ω : Type) [Field Ω] [CharP Ω 2] [Algebra (ZMod 2) Ω]
    [Algebra.IsAlgebraic (ZMod 2) Ω] {K : Type} [Field K] [Algebra K Ω]
    (n z : ModGL .F4 Ω) {γ : Fin 3 → ℤ} (hγ : γ ∈ roots (isFiniteType_cartanC 3) ∅) :
    (CFSG.StandardType.F4ExplicitPos.C3Range.c3RootSubgroup (K := K) γ).map
        (((MulAut.conj z).toMonoidHom.comp (conjIM Ω n)).comp
          (statedSpMap (algebraMap K Ω) 3)) =
      (finitePinnedRoot (K := K) Ω γ).map (MulAut.conj (z * n)).toMonoidHom := by
  have hset : ((fun g => (((MulAut.conj z).toMonoidHom.comp (conjIM Ω n)).comp
        (statedSpMap (algebraMap K Ω) 3)) g) '' Set.range (Sp.x 3 K γ)) =
      (MulAut.conj (z * n)).toMonoidHom '' Set.range (fun c : K =>
        pinnedX .F4 Ω (c3ToF4 γ)
          (((rootOperatorFamily .F4).pinnedFamilySign (c3ToF4 γ) : Ω) * algebraMap K Ω c)) := by
    ext x
    constructor
    · rintro ⟨y, ⟨c, rfl⟩, rfl⟩
      refine ⟨pinnedX .F4 Ω (c3ToF4 γ)
        (((rootOperatorFamily .F4).pinnedFamilySign (c3ToF4 γ) : Ω) * algebraMap K Ω c),
        ⟨c, rfl⟩, ?_⟩
      change MulAut.conj (z * n)
          (pinnedX .F4 Ω (c3ToF4 γ)
            (((rootOperatorFamily .F4).pinnedFamilySign (c3ToF4 γ) : Ω) * algebraMap K Ω c)) =
        (((MulAut.conj z).toMonoidHom.comp (conjIM Ω n)).comp
          (statedSpMap (algebraMap K Ω) 3)) (Sp.x 3 K γ c)
      rw [Phi_x_pinned (Ω := Ω) (hγ := hγ) (c := c), MulAut.conj_apply]
      group
    · rintro ⟨p, ⟨c, rfl⟩, rfl⟩
      refine ⟨Sp.x 3 K γ c, ⟨c, rfl⟩, ?_⟩
      change (((MulAut.conj z).toMonoidHom.comp (conjIM Ω n)).comp
          (statedSpMap (algebraMap K Ω) 3)) (Sp.x 3 K γ c) =
        MulAut.conj (z * n)
          (pinnedX .F4 Ω (c3ToF4 γ)
            (((rootOperatorFamily .F4).pinnedFamilySign (c3ToF4 γ) : Ω) * algebraMap K Ω c))
      rw [Phi_x_pinned (Ω := Ω) (hγ := hγ) (c := c), MulAut.conj_apply]
      group
  rw [C3Range.c3RootSubgroup, MonoidHom.map_closure, finitePinnedRoot,
    MonoidHom.map_closure, hset]

theorem conjIM_natural
    (Ω : Type) [Field Ω] [CharP Ω 2] [Algebra (ZMod 2) Ω]
    [Algebra.IsAlgebraic (ZMod 2) Ω] (Fr : Ω →+* Ω) (n : ModGL .F4 Ω)
    (hn : bcGL (τ := .F4) Fr n = n) :
    (bcGL (τ := .F4) Fr).comp (conjIM Ω n) =
      (conjIM Ω n).comp (statedSpMap Fr 3) := by
  apply hom_ext_x3_alg (K := Ω)
  intro γ c
  simp only [MonoidHom.comp_apply]
  change bcGL (τ := .F4) Fr
      (n * (C3Algebraic.iOmega Ω (Sp.x 3 Ω γ c) : ModGL .F4 Ω) * n⁻¹) =
    n * (CFSG.StandardType.F4ExplicitPos.C3Algebraic.iOmega Ω (statedSpMap Fr 3 (Sp.x 3 Ω γ c)) :
      ModGL .F4 Ω) * n⁻¹
  rw [map_mul, map_mul, map_inv, hn, ← j_apply (τ := .F4) Fr
    (CFSG.StandardType.F4ExplicitPos.C3Algebraic.iOmega Ω (Sp.x 3 Ω γ c)), iOmega_natural_apply]

theorem range_conjIM
    (Ω : Type) [Field Ω] [CharP Ω 2] [Algebra (ZMod 2) Ω]
    [Algebra.IsAlgebraic (ZMod 2) Ω] (n : ModGL .F4 Ω) :
    MonoidHom.range (conjIM Ω n) =
      (rootSpan .F4 Ω CFSG.StandardType.F4ExplicitPos.C3Range.c3RootSet).map
        (MulAut.conj n).toMonoidHom := by
  have hrange : MonoidHom.range ((adjointGroup .F4 Ω).subtype.comp
      (C3Algebraic.iOmega Ω)) = rootSpan .F4 Ω C3Range.c3RootSet :=
    C3Algebraic.range_eq_rootSpan_alg (C3Algebraic.iOmega Ω)
      (fun γ c => CFSG.StandardType.F4ExplicitPos.C3Algebraic.iOmega_x Ω γ c)
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    exact Subgroup.mem_map.mpr ⟨(C3Algebraic.iOmega Ω g : ModGL .F4 Ω),
      by rw [← hrange]; exact MonoidHom.mem_range.mpr ⟨g, rfl⟩, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    have hy' : y ∈ MonoidHom.range ((adjointGroup .F4 Ω).subtype.comp
        (CFSG.StandardType.F4ExplicitPos.C3Algebraic.iOmega Ω)) := by rw [hrange]; exact hy
    obtain ⟨g, hg⟩ := hy'
    exact ⟨g, by rw [← hg]; rfl⟩

theorem range_conjIM_canonicalRep
    (Ω : Type) [Field Ω] [CharP Ω 2] [Algebra (ZMod 2) Ω]
    [Algebra.IsAlgebraic (ZMod 2) Ω] (w : WeylGroup .F4) :
    MonoidHom.range (conjIM Ω (canonicalRep (coxeterSystem .F4) Ω w)) =
      rootSpan .F4 Ω ((fun α => w • α) '' CFSG.StandardType.F4ExplicitPos.C3Range.c3RootSet) := by
  rw [range_conjIM]
  exact (canonical_weyl_root_transport .F4 Ω).1 w CFSG.StandardType.F4ExplicitPos.C3Range.c3RootSet
    (fun α hα => CFSG.StandardType.F4ExplicitPos.C3Range.isRoot_of_mem_c3RootSet hα)

theorem range_comp_eq_inf_eqLocus {G S A : Type*} [Group G] [Group S] [Group A]
    (i : G →* A) (β : G →* G) (F : A →* A) (s : S →* G)
    (hi : Function.Injective i) (hβF : ∀ g, i (β g) = F (i g))
    (hs : MonoidHom.range s = β.eqLocus (MonoidHom.id G)) :
    MonoidHom.range (i.comp s) = MonoidHom.range i ⊓ F.eqLocus (MonoidHom.id A) := by
  apply le_antisymm
  · rintro x ⟨t, rfl⟩
    refine ⟨⟨s t, rfl⟩, ?_⟩
    have ht : β (s t) = s t := by
      have hmem : s t ∈ β.eqLocus (MonoidHom.id G) := by rw [← hs]; exact ⟨t, rfl⟩
      exact hmem
    change F (i (s t)) = i (s t)
    rw [← hβF]
    exact congrArg i ht
  · rintro x ⟨⟨g, rfl⟩, hx⟩
    change F (i g) = i g at hx
    have hg : β g = g := hi (hβF g |>.trans hx)
    have hgs : g ∈ MonoidHom.range s := by rw [hs]; exact hg
    obtain ⟨t, rfl⟩ := hgs
    exact ⟨t, rfl⟩

theorem range_Phi_eq_inf_model
    (Ω : Type) [Field Ω] [CharP Ω 2] [Algebra (ZMod 2) Ω]
    [Algebra.IsAlgebraic (ZMod 2) Ω]
    {K : Type} [Field K] [Finite K] [Algebra K Ω]
    (D : LangDatum .F4 Ω) (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (n z : ModGL .F4 Ω) (hn_adj : n ∈ adjointGroup .F4 Ω) (hz_adj : z ∈ adjointGroup .F4 Ω)
    (hn : bcGL (τ := .F4) Fr n = n)
    (hzH : ∀ g, g ∈ MonoidHom.range (conjIM Ω n) ↔
      z * g * z⁻¹ ∈ MonoidHom.range (conjIM Ω n))
    (hzF : ∀ g ∈ MonoidHom.range (conjIM Ω n),
      D.step (z * g * z⁻¹) = z * bcGL (τ := .F4) Fr g * z⁻¹) :
    MonoidHom.range (((MulAut.conj z).toMonoidHom.comp (conjIM Ω n)).comp
        (statedSpMap (algebraMap K Ω) 3)) =
      MonoidHom.range (conjIM Ω n) ⊓ D.model := by
  have hi : Function.Injective
      ((MulAut.conj z).toMonoidHom.comp (conjIM Ω n)) :=
    (MulAut.conj z).injective.comp (conjIM_injective Ω n)
  have hs : MonoidHom.range (statedSpMap (algebraMap K Ω) 3) =
      (statedSpMap Fr 3).eqLocus (MonoidHom.id _) :=
    statedSpMap_range_eq_eqLocus (K := K) (Ω := Ω) Fr hFr 3
  have hβF : ∀ g, ((MulAut.conj z).toMonoidHom.comp (conjIM Ω n))
        (statedSpMap Fr 3 g) =
      D.step (((MulAut.conj z).toMonoidHom.comp (conjIM Ω n)) g) := by
    intro g
    have hnat := DFunLike.congr_fun (conjIM_natural Ω Fr n hn) g
    simp only [MonoidHom.comp_apply] at hnat
    have hgH : conjIM Ω n g ∈ MonoidHom.range (conjIM Ω n) :=
      MonoidHom.mem_range.mpr ⟨g, rfl⟩
    change MulAut.conj z (conjIM Ω n (statedSpMap Fr 3 g)) =
      D.step (MulAut.conj z (conjIM Ω n g))
    rw [← hnat, MulAut.conj_apply, MulAut.conj_apply,
      hzF (conjIM Ω n g) hgH]
  have hrange_i : MonoidHom.range
      ((MulAut.conj z).toMonoidHom.comp (conjIM Ω n)) =
      MonoidHom.range (conjIM Ω n) := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      change z * conjIM Ω n g * z⁻¹ ∈ MonoidHom.range (conjIM Ω n)
      exact (hzH (conjIM Ω n g)).mp (MonoidHom.mem_range.mpr ⟨g, rfl⟩)
    · intro hx
      have hx' : z⁻¹ * x * z ∈ MonoidHom.range (conjIM Ω n) := by
        refine (hzH (z⁻¹ * x * z)).mpr ?_
        have hconj : z * (z⁻¹ * x * z) * z⁻¹ = x := by group
        rw [hconj]; exact hx
      obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp hx'
      refine ⟨g, ?_⟩
      change z * conjIM Ω n g * z⁻¹ = x
      rw [hg]
      group
  have hH_adj : MonoidHom.range (conjIM Ω n) ≤ adjointGroup .F4 Ω := by
    rintro x ⟨g, rfl⟩
    rw [conjIM_apply]
    exact mul_mem (mul_mem hn_adj (C3Algebraic.iOmega Ω g).2) (inv_mem hn_adj)
  have hrange_i_adj : MonoidHom.range
      ((MulAut.conj z).toMonoidHom.comp (conjIM Ω n)) ≤ adjointGroup .F4 Ω := by
    rintro x ⟨g, rfl⟩
    change z * conjIM Ω n g * z⁻¹ ∈ adjointGroup .F4 Ω
    exact mul_mem (mul_mem hz_adj
      (hH_adj (MonoidHom.mem_range.mpr ⟨g, rfl⟩))) (inv_mem hz_adj)
  have hmain := range_comp_eq_inf_eqLocus
    ((MulAut.conj z).toMonoidHom.comp (conjIM Ω n)) (statedSpMap Fr 3) D.step
    (statedSpMap (algebraMap K Ω) 3) hi hβF hs
  rw [hmain, hrange_i]
  rw [show D.model = adjointGroup .F4 Ω ⊓ D.step.eqLocus (MonoidHom.id _) from rfl,
    ← inf_assoc, inf_eq_left.mpr hH_adj]

theorem Phi_injective
    (Ω : Type) [Field Ω] [CharP Ω 2] [Algebra (ZMod 2) Ω]
    [Algebra.IsAlgebraic (ZMod 2) Ω] {K : Type} [Field K] [Algebra K Ω]
    (n z : ModGL .F4 Ω) :
    Function.Injective (((MulAut.conj z).toMonoidHom.comp (conjIM Ω n)).comp
        (statedSpMap (algebraMap K Ω) 3)) :=
  ((MulAut.conj z).injective.comp (conjIM_injective Ω n)).comp
    (statedSpMap_injective (algebraMap K Ω) 3)

theorem isQuasisimple_range_Phi
    (Ω : Type) [Field Ω] [CharP Ω 2] [Algebra (ZMod 2) Ω]
    [Algebra.IsAlgebraic (ZMod 2) Ω] {K : Type} [Field K] [Finite K] [CharP K 2]
    [Algebra K Ω] (n z : ModGL .F4 Ω) :
    CFSG.IsQuasisimple ↥(MonoidHom.range
      (((MulAut.conj z).toMonoidHom.comp (conjIM Ω n)).comp
        (statedSpMap (algebraMap K Ω) 3))) :=
  isQuasisimple_range _ (Phi_injective Ω n z)

theorem isPerfect_range_Phi
    (Ω : Type) [Field Ω] [CharP Ω 2] [Algebra (ZMod 2) Ω]
    [Algebra.IsAlgebraic (ZMod 2) Ω] {K : Type} [Field K] [Finite K] [CharP K 2]
    [Algebra K Ω] (n z : ModGL .F4 Ω) :
    Group.IsPerfect ↥(MonoidHom.range
      (((MulAut.conj z).toMonoidHom.comp (conjIM Ω n)).comp
        (statedSpMap (algebraMap K Ω) 3))) :=
  (isQuasisimple_range_Phi Ω n z).1

end Naturality

end CFSG.StandardType.F4ExplicitPos.RationalC3

end

end
