module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.RationalC3Part2
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.RationalB2Part1

@[expose] public section

public noncomputable section

namespace CFSG.StandardType.F4ExplicitPos.RationalB2
open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType
  CFSG.LieType.Chevalley CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Universal CFSG.LieType.Universal.Symplectic
  CFSG.LieType.Universal.Symplectic.SpExtras
  CFSG.Timmesfeld.LieEmbed CFSG.SeitzReduction.F4Pilot
  CFSG.StandardType.F4ExplicitPos.BaseChange CFSG.StandardType.F4ExplicitPos.RootBaseChange
  CFSG.StandardType.F4ExplicitPos.PinnedBaseChange
  CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.ClassicalInvolution.Models.SymplecticPairs (spEmbed spEmbed_injective)
open CFSG.StandardType.F4ExplicitPos.C3Range (c3RootSubgroup c3RootSubgroup_eq_rootGroup)
open scoped Matrix

section FixedRange
variable (Ω : Type) [Field Ω] [CharP Ω 2] [Algebra (ZMod 2) Ω] [Algebra.IsAlgebraic (ZMod 2) Ω]

theorem conjIMB2_natural
    (Fr : Ω →+* Ω) (n : ModGL .F4 Ω)
    (hn : bcGL (τ := .F4) Fr n = n) :
    (bcGL (τ := .F4) Fr).comp (conjIMB2 Ω n) =
      (conjIMB2 Ω n).comp (statedSpMap Fr 2) := by
  apply hom_ext_x2_alg (K := Ω)
  rintro v hv c
  simp only [MonoidHom.comp_apply]
  change bcGL (τ := .F4) Fr
      (n * (iOmegaB2 Ω (Sp.x 2 Ω v c) : ModGL .F4 Ω) * n⁻¹) =
    n * (iOmegaB2 Ω (statedSpMap Fr 2 (Sp.x 2 Ω v c)) : ModGL .F4 Ω) * n⁻¹
  rw [map_mul, map_mul, map_inv, hn, ← j_apply (τ := .F4) Fr
    (iOmegaB2 Ω (Sp.x 2 Ω v c))]
  exact congrArg (fun x : ModGL .F4 Ω => n * x * n⁻¹)
    (congrArg (fun x : ↥(adjointGroup .F4 Ω) => (x : ModGL .F4 Ω))
      (DFunLike.congr_fun (iOmegaB2_natural (Ω := Ω) Fr) (Sp.x 2 Ω v c)))

theorem range_conjIMB2
    (n : ModGL .F4 Ω) :
    MonoidHom.range (conjIMB2 Ω n) =
      (rootSpan .F4 Ω b2LeviRoots).map (MulAut.conj n).toMonoidHom := by
  have hrange : MonoidHom.range ((adjointGroup .F4 Ω).subtype.comp (iOmegaB2 Ω)) =
      rootSpan .F4 Ω b2LeviRoots := by
    rw [MonoidHom.range_comp]
    exact range_iOmegaB2 (Ω := Ω)
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    exact Subgroup.mem_map.mpr ⟨(iOmegaB2 Ω g : ModGL .F4 Ω),
      by rw [← hrange]; exact MonoidHom.mem_range.mpr ⟨g, rfl⟩, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    have hy' : y ∈ MonoidHom.range ((adjointGroup .F4 Ω).subtype.comp (iOmegaB2 Ω)) := by
      rw [hrange]; exact hy
    obtain ⟨g, hg⟩ := hy'
    exact ⟨g, by rw [← hg]; rfl⟩

theorem range_PhiB2_eq_inf_model
    {K : Type} [Field K] [Finite K] [Algebra K Ω]
    (D : LangDatum .F4 Ω) (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (n z : ModGL .F4 Ω) (hn_adj : n ∈ adjointGroup .F4 Ω) (_hz_adj : z ∈ adjointGroup .F4 Ω)
    (hn : bcGL (τ := .F4) Fr n = n)
    (hzH : ∀ g, g ∈ MonoidHom.range (conjIMB2 Ω n) ↔
      z * g * z⁻¹ ∈ MonoidHom.range (conjIMB2 Ω n))
    (hzF : ∀ g ∈ MonoidHom.range (conjIMB2 Ω n),
      D.step (z * g * z⁻¹) = z * bcGL (τ := .F4) Fr g * z⁻¹) :
    MonoidHom.range (((MulAut.conj z).toMonoidHom.comp (conjIMB2 Ω n)).comp
        (statedSpMap (algebraMap K Ω) 2)) =
      MonoidHom.range (conjIMB2 Ω n) ⊓ D.model := by
  have hi : Function.Injective
      ((MulAut.conj z).toMonoidHom.comp (conjIMB2 Ω n)) :=
    (MulAut.conj z).injective.comp (conjIMB2_injective Ω n)
  have hs : MonoidHom.range (statedSpMap (algebraMap K Ω) 2) =
      (statedSpMap Fr 2).eqLocus (MonoidHom.id _) :=
    RationalC3.statedSpMap_range_eq_eqLocus (K := K) (Ω := Ω) Fr hFr 2
  have hβF : ∀ g, ((MulAut.conj z).toMonoidHom.comp (conjIMB2 Ω n))
        (statedSpMap Fr 2 g) =
      D.step (((MulAut.conj z).toMonoidHom.comp (conjIMB2 Ω n)) g) := by
    intro g
    have hnat := DFunLike.congr_fun (conjIMB2_natural Ω Fr n hn) g
    simp only [MonoidHom.comp_apply] at hnat
    have hgH : conjIMB2 Ω n g ∈ MonoidHom.range (conjIMB2 Ω n) :=
      MonoidHom.mem_range.mpr ⟨g, rfl⟩
    change MulAut.conj z (conjIMB2 Ω n (statedSpMap Fr 2 g)) =
      D.step (MulAut.conj z (conjIMB2 Ω n g))
    rw [← hnat, MulAut.conj_apply, MulAut.conj_apply, hzF (conjIMB2 Ω n g) hgH]
  have hrange_i : MonoidHom.range
      ((MulAut.conj z).toMonoidHom.comp (conjIMB2 Ω n)) =
      MonoidHom.range (conjIMB2 Ω n) := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      change z * conjIMB2 Ω n g * z⁻¹ ∈ MonoidHom.range (conjIMB2 Ω n)
      exact (hzH (conjIMB2 Ω n g)).mp (MonoidHom.mem_range.mpr ⟨g, rfl⟩)
    · intro hx
      have hx' : z⁻¹ * x * z ∈ MonoidHom.range (conjIMB2 Ω n) := by
        refine (hzH (z⁻¹ * x * z)).mpr ?_
        have hconj : z * (z⁻¹ * x * z) * z⁻¹ = x := by group
        rw [hconj]; exact hx
      obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp hx'
      refine ⟨g, ?_⟩
      change z * conjIMB2 Ω n g * z⁻¹ = x
      rw [hg]
      group
  have hH_adj : MonoidHom.range (conjIMB2 Ω n) ≤ adjointGroup .F4 Ω := by
    rintro x ⟨g, rfl⟩
    rw [conjIMB2_apply]
    exact mul_mem (mul_mem hn_adj (iOmegaB2 Ω g).2) (inv_mem hn_adj)
  have hmain := CFSG.StandardType.F4ExplicitPos.RationalC3.range_comp_eq_inf_eqLocus
    ((MulAut.conj z).toMonoidHom.comp (conjIMB2 Ω n)) (statedSpMap Fr 2) D.step
    (statedSpMap (algebraMap K Ω) 2) hi hβF hs
  rw [hmain, hrange_i]
  rw [show D.model = adjointGroup .F4 Ω ⊓ D.step.eqLocus (MonoidHom.id _) from rfl,
    ← inf_assoc, inf_eq_left.mpr hH_adj]

theorem PhiB2_injective
    {K : Type} [Field K] [Algebra K Ω]
    (n z : ModGL .F4 Ω) :
    Function.Injective (((MulAut.conj z).toMonoidHom.comp (conjIMB2 Ω n)).comp
        (statedSpMap (algebraMap K Ω) 2)) :=
  ((MulAut.conj z).injective.comp (conjIMB2_injective Ω n)).comp
    (statedSpMap_injective (algebraMap K Ω) 2)

end FixedRange

section Quasisimple

theorem isQuasisimple_range_sp4 {K A : Type} [Field K] [Finite K] [CharP K 2] [Group A]
    (i : ↥(StatedSp 2 K) →* A) (hi : Function.Injective i) (hq : 4 ≤ Nat.card K) :
    CFSG.IsQuasisimple ↥(MonoidHom.range i) := by
  have hsp : CFSG.IsQuasisimple ↥(StatedSp 2 K) :=
    CFSG.LieType.Universal.Symplectic.isQuasisimple (n := 2) (F := K)
      (hn := by norm_num) (hF := Or.inl (Or.inr hq))
  exact CFSG.IsQuasisimple.of_mulEquiv (MonoidHom.ofInjective hi).symm hsp

variable (Ω : Type) [Field Ω] [CharP Ω 2] [Algebra (ZMod 2) Ω] [Algebra.IsAlgebraic (ZMod 2) Ω]

theorem isQuasisimple_range_PhiB2
    {K : Type} [Field K] [Finite K] [CharP K 2]
    [Algebra K Ω] (n z : ModGL .F4 Ω) (hq : 4 ≤ Nat.card K) :
    CFSG.IsQuasisimple ↥(MonoidHom.range
      (((MulAut.conj z).toMonoidHom.comp (conjIMB2 Ω n)).comp
        (statedSpMap (algebraMap K Ω) 2))) :=
  isQuasisimple_range_sp4 _ (PhiB2_injective Ω n z) hq

end Quasisimple

end CFSG.StandardType.F4ExplicitPos.RationalB2

end

end
