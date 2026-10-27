module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.RationalC3Part2
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.B3Naturality

@[expose] public section

public noncomputable section

namespace CFSG.StandardType.F4ExplicitPos.RationalB3

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType
  CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Universal.Symplectic CFSG.Timmesfeld.LieEmbed
  CFSG.SeitzReduction.F4Pilot
  CFSG.StandardType.F4ExplicitPos.BaseChange CFSG.StandardType.F4ExplicitPos.RootBaseChange
  CFSG.StandardType.F4ExplicitPos.PinnedBaseChange
  CFSG.StandardType.F4ExplicitPos.B3Exact CFSG.StandardType.F4ExplicitPos.B3Pinned
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  C3Range C3Algebraic B2Finite
  CFSG.StandardType.F4ExplicitPos.B3Algebraic

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

open CFSG.StandardType.F4ExplicitPos.RationalC3

open scoped Matrix

theorem hom_ext_x3_roots {K H : Type} [Field K] [CharP K 2] [Group H]
    {Ψ Ψ' : ↥(StatedSp 3 K) →* H}
    (h : ∀ γ c, γ ∈ roots (isFiniteType_cartanC 3) ∅ →
        Ψ (Sp.x 3 K γ c) = Ψ' (Sp.x 3 K γ c)) : Ψ = Ψ' :=
  B3Naturality.hom_ext_x3_alg_b3 (K := K) (H := H) fun γ hγ c => h γ c hγ

theorem iBΩ_natural_apply
    (Ω : Type) [Field Ω] [CharP Ω 2] [Algebra (ZMod 2) Ω]
    [Algebra.IsAlgebraic (ZMod 2) Ω] (Fr : Ω →+* Ω) (g : ↥(StatedSp 3 Ω)) :
    j (τ := .F4) Fr ((iBΩ Ω) g) = (iBΩ Ω) (statedSpMap Fr 3 g) :=
  CFSG.StandardType.F4ExplicitPos.B3Naturality.iBΩ_natural_apply (Ω := Ω) Fr g

noncomputable def conjBM
    (Ω : Type) [Field Ω] [CharP Ω 2] [Algebra (ZMod 2) Ω]
    [Algebra.IsAlgebraic (ZMod 2) Ω] (n : ModGL .F4 Ω) : ↥(StatedSp 3 Ω) →* ModGL .F4 Ω :=
  (MulAut.conj n).toMonoidHom.comp
    ((adjointGroup .F4 Ω).subtype.comp (iBΩ Ω))

theorem conjBM_apply
    (Ω : Type) [Field Ω] [CharP Ω 2] [Algebra (ZMod 2) Ω]
    [Algebra.IsAlgebraic (ZMod 2) Ω] (n : ModGL .F4 Ω) (g : ↥(StatedSp 3 Ω)) :
    conjBM Ω n g = n * (((iBΩ Ω) g : adjointGroup .F4 Ω) : ModGL .F4 Ω) * n⁻¹ := by
  change MulAut.conj n (((iBΩ Ω) g : adjointGroup .F4 Ω) : ModGL .F4 Ω) =
    n * (((iBΩ Ω) g : adjointGroup .F4 Ω) : ModGL .F4 Ω) * n⁻¹
  rw [MulAut.conj_apply]

theorem conjBM_injective
    (Ω : Type) [Field Ω] [CharP Ω 2] [Algebra (ZMod 2) Ω]
    [Algebra.IsAlgebraic (ZMod 2) Ω] (n : ModGL .F4 Ω) :
    Function.Injective (conjBM Ω n) :=
  (MulAut.conj n).injective.comp
    ((adjointGroup .F4 Ω).subtype_injective.comp (iBΩ_injective Ω))

theorem conjBM_x_pinned
    (Ω : Type) [Field Ω] [CharP Ω 2] [Algebra (ZMod 2) Ω]
    [Algebra.IsAlgebraic (ZMod 2) Ω] (n : ModGL .F4 Ω) {γ : Fin 3 → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartanC 3) ∅) (c : Ω) :
    conjBM Ω n (Sp.x 3 Ω γ c) =
      n * pinnedX .F4 Ω (F4.dualRoot (c3ToF4 γ))
        (c ^ F4.exponent (pinnedData .F4 (c3ToF4 γ)).1) * n⁻¹ := by
  rw [conjBM_apply, iBΩ_x_pinnedX Ω hγ c]
  rfl

theorem conjBM_natural
    (Ω : Type) [Field Ω] [CharP Ω 2] [Algebra (ZMod 2) Ω]
    [Algebra.IsAlgebraic (ZMod 2) Ω] (Fr : Ω →+* Ω) (n : ModGL .F4 Ω)
    (hn : bcGL (τ := .F4) Fr n = n) :
    (bcGL (τ := .F4) Fr).comp (conjBM Ω n) =
      (conjBM Ω n).comp (statedSpMap Fr 3) := by
  apply hom_ext_x3_roots (K := Ω)
  intro γ c hγ
  simp only [MonoidHom.comp_apply]
  change (bcGL (τ := .F4) Fr)
      (n * (((iBΩ Ω) (Sp.x 3 Ω γ c) : adjointGroup .F4 Ω) : ModGL .F4 Ω) * n⁻¹) =
    n * (((iBΩ Ω) (statedSpMap Fr 3 (Sp.x 3 Ω γ c)) :
      adjointGroup .F4 Ω) : ModGL .F4 Ω) * n⁻¹
  rw [map_mul, map_mul, map_inv, hn, ← j_apply (τ := .F4) Fr ((iBΩ Ω) (Sp.x 3 Ω γ c)),
    iBΩ_natural_apply]

theorem range_conjBM
    (Ω : Type) [Field Ω] [CharP Ω 2] [Algebra (ZMod 2) Ω]
    [Algebra.IsAlgebraic (ZMod 2) Ω] (n : ModGL .F4 Ω) :
    MonoidHom.range (conjBM Ω n) =
      (rootSpan .F4 Ω b3LeviRoots).map (MulAut.conj n).toMonoidHom := by
  rw [conjBM, MonoidHom.range_comp, iBΩ_map_range]

theorem range_conjBM_canonicalRep
    (Ω : Type) [Field Ω] [CharP Ω 2] [Algebra (ZMod 2) Ω]
    [Algebra.IsAlgebraic (ZMod 2) Ω] (w : WeylGroup .F4) :
    MonoidHom.range (conjBM Ω (canonicalRep (coxeterSystem .F4) Ω w)) =
      rootSpan .F4 Ω ((fun α => w • α) '' b3LeviRoots) := by
  rw [range_conjBM]
  exact (canonical_weyl_root_transport .F4 Ω).1 w b3LeviRoots (fun α hα => hα.1)

noncomputable def PhiB
    (Ω : Type) [Field Ω] [CharP Ω 2] [Algebra (ZMod 2) Ω]
    [Algebra.IsAlgebraic (ZMod 2) Ω] {K : Type} [Field K] [Algebra K Ω]
    (n z : ModGL .F4 Ω) : ↥(StatedSp 3 K) →* ModGL .F4 Ω :=
  ((MulAut.conj z).toMonoidHom.comp (conjBM Ω n)).comp (statedSpMap (algebraMap K Ω) 3)

theorem PhiB_x_pinned
    (Ω : Type) [Field Ω] [CharP Ω 2] [Algebra (ZMod 2) Ω]
    [Algebra.IsAlgebraic (ZMod 2) Ω] {K : Type} [Field K] [Algebra K Ω]
    (n z : ModGL .F4 Ω) {γ : Fin 3 → ℤ} (hγ : γ ∈ roots (isFiniteType_cartanC 3) ∅)
    (c : K) :
    PhiB (K := K) Ω n z (Sp.x 3 K γ c) =
      z * n * pinnedX .F4 Ω (F4.dualRoot (c3ToF4 γ))
        (((algebraMap K Ω c) ^ F4.exponent (pinnedData .F4 (c3ToF4 γ)).1))
        * n⁻¹ * z⁻¹ := by
  change MulAut.conj z
    (conjBM Ω n (statedSpMap (algebraMap K Ω) 3 (Sp.x 3 K γ c))) = _
  rw [statedSpMap_x]
  rw [conjBM_x_pinned (hγ := hγ) (c := algebraMap K Ω c), MulAut.conj_apply]
  group

theorem range_PhiB_eq_inf_model
    (Ω : Type) [Field Ω] [CharP Ω 2] [Algebra (ZMod 2) Ω]
    [Algebra.IsAlgebraic (ZMod 2) Ω]
    {K : Type} [Field K] [Finite K] [Algebra K Ω]
    (D : LangDatum .F4 Ω) (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (n z : ModGL .F4 Ω) (hn_adj : n ∈ adjointGroup .F4 Ω) (hz_adj : z ∈ adjointGroup .F4 Ω)
    (hn : bcGL (τ := .F4) Fr n = n)
    (hzH : ∀ g, g ∈ MonoidHom.range (conjBM Ω n) ↔
      z * g * z⁻¹ ∈ MonoidHom.range (conjBM Ω n))
    (hzF : ∀ g ∈ MonoidHom.range (conjBM Ω n),
      D.step (z * g * z⁻¹) = z * bcGL (τ := .F4) Fr g * z⁻¹) :
    MonoidHom.range (PhiB (K := K) Ω n z) = MonoidHom.range (conjBM Ω n) ⊓ D.model := by
  have hi : Function.Injective
      ((MulAut.conj z).toMonoidHom.comp (conjBM Ω n)) :=
    (MulAut.conj z).injective.comp (conjBM_injective Ω n)
  have hs : MonoidHom.range (statedSpMap (algebraMap K Ω) 3) =
      (statedSpMap Fr 3).eqLocus (MonoidHom.id _) :=
    RationalC3.statedSpMap_range_eq_eqLocus (K := K) (Ω := Ω) Fr hFr 3
  have hβF : ∀ g, ((MulAut.conj z).toMonoidHom.comp (conjBM Ω n))
        (statedSpMap Fr 3 g) =
      D.step (((MulAut.conj z).toMonoidHom.comp (conjBM Ω n)) g) := by
    intro g
    have hnat := DFunLike.congr_fun (conjBM_natural Ω Fr n hn) g
    simp only [MonoidHom.comp_apply] at hnat
    have hgH : conjBM Ω n g ∈ MonoidHom.range (conjBM Ω n) :=
      MonoidHom.mem_range.mpr ⟨g, rfl⟩
    change MulAut.conj z (conjBM Ω n (statedSpMap Fr 3 g)) =
      D.step (MulAut.conj z (conjBM Ω n g))
    rw [← hnat, MulAut.conj_apply, MulAut.conj_apply, hzF (conjBM Ω n g) hgH]
  have hrange_i : MonoidHom.range
      ((MulAut.conj z).toMonoidHom.comp (conjBM Ω n)) =
      MonoidHom.range (conjBM Ω n) := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      change z * conjBM Ω n g * z⁻¹ ∈ MonoidHom.range (conjBM Ω n)
      exact (hzH (conjBM Ω n g)).mp (MonoidHom.mem_range.mpr ⟨g, rfl⟩)
    · intro hx
      have hx' : z⁻¹ * x * z ∈ MonoidHom.range (conjBM Ω n) := by
        refine (hzH (z⁻¹ * x * z)).mpr ?_
        have hconj : z * (z⁻¹ * x * z) * z⁻¹ = x := by group
        rw [hconj]; exact hx
      obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp hx'
      refine ⟨g, ?_⟩
      change z * conjBM Ω n g * z⁻¹ = x
      rw [hg]
      group
  have hH_adj : MonoidHom.range (conjBM Ω n) ≤ adjointGroup .F4 Ω := by
    rintro x ⟨g, rfl⟩
    rw [conjBM_apply]
    exact mul_mem (mul_mem hn_adj (iBΩ Ω g).2) (inv_mem hn_adj)
  have hrange_i_adj : MonoidHom.range
      ((MulAut.conj z).toMonoidHom.comp (conjBM Ω n)) ≤ adjointGroup .F4 Ω := by
    rintro x ⟨g, rfl⟩
    change z * conjBM Ω n g * z⁻¹ ∈ adjointGroup .F4 Ω
    exact mul_mem (mul_mem hz_adj
      (hH_adj (MonoidHom.mem_range.mpr ⟨g, rfl⟩))) (inv_mem hz_adj)
  have hmain := CFSG.StandardType.F4ExplicitPos.RationalC3.range_comp_eq_inf_eqLocus
    ((MulAut.conj z).toMonoidHom.comp (conjBM Ω n)) (statedSpMap Fr 3) D.step
    (statedSpMap (algebraMap K Ω) 3) hi hβF hs
  change MonoidHom.range (((MulAut.conj z).toMonoidHom.comp (conjBM Ω n)).comp
      (statedSpMap (algebraMap K Ω) 3)) =
      MonoidHom.range (conjBM Ω n) ⊓ D.model
  rw [hmain, hrange_i]
  rw [show D.model = adjointGroup .F4 Ω ⊓ D.step.eqLocus (MonoidHom.id _) from rfl,
    ← inf_assoc, inf_eq_left.mpr hH_adj]

theorem PhiB_injective
    (Ω : Type) [Field Ω] [CharP Ω 2] [Algebra (ZMod 2) Ω]
    [Algebra.IsAlgebraic (ZMod 2) Ω] {K : Type} [Field K] [Algebra K Ω]
    (n z : ModGL .F4 Ω) :
    Function.Injective (PhiB (K := K) Ω n z) :=
  ((MulAut.conj z).injective.comp (conjBM_injective Ω n)).comp
    (statedSpMap_injective (algebraMap K Ω) 3)

theorem isQuasisimple_range_PhiB
    (Ω : Type) [Field Ω] [CharP Ω 2] [Algebra (ZMod 2) Ω]
    [Algebra.IsAlgebraic (ZMod 2) Ω] {K : Type} [Field K] [Finite K] [CharP K 2]
    [Algebra K Ω] (n z : ModGL .F4 Ω) :
    CFSG.IsQuasisimple ↥(MonoidHom.range (PhiB (K := K) Ω n z)) :=
  CFSG.StandardType.F4ExplicitPos.RationalC3.isQuasisimple_range _ (PhiB_injective Ω n z)

theorem isPerfect_range_PhiB
    (Ω : Type) [Field Ω] [CharP Ω 2] [Algebra (ZMod 2) Ω]
    [Algebra.IsAlgebraic (ZMod 2) Ω] {K : Type} [Field K] [Finite K] [CharP K 2]
    [Algebra K Ω] (n z : ModGL .F4 Ω) :
    Group.IsPerfect ↥(MonoidHom.range (PhiB (K := K) Ω n z)) :=
  (isQuasisimple_range_PhiB (K := K) Ω n z).1

noncomputable def finitePinnedRootF4
    (Ω : Type) [Field Ω] [CharP Ω 2] [Algebra (ZMod 2) Ω]
    [Algebra.IsAlgebraic (ZMod 2) Ω] {K : Type} [Field K] [Algebra K Ω]
    (α : Fin (Tag.rank .F4) → ℤ) : Subgroup (ModGL .F4 Ω) :=
  Subgroup.closure (Set.range (fun c : K => pinnedX .F4 Ω α (algebraMap K Ω c)))

end CFSG.StandardType.F4ExplicitPos.RationalB3
end

end
