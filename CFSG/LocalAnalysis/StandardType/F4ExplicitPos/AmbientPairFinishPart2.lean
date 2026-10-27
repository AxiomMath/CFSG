module

public import CFSG.LieType.AlgebraicGroups.ConvolutionPoints
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.AmbientPairFinishPart1

@[expose] public section

public noncomputable section
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
open CFSG.LieType.Steinberg.Adjoint
open CFSG.LieType.Universal
open CFSG.StandardType.F4ExplicitPos.BaseChange
open CFSG.StandardType.F4ExplicitPos.RootBaseChange
open CFSG.StandardType.F4ExplicitPos.PinnedBaseChange
open CFSG.StandardType.F4ExplicitPos.PairStabilizerNative
open CFSG.StandardType.F4ExplicitPos.FixedImage
open CFSG.StandardType.F4ExplicitPos.AmbientAction
open CFSG.StandardType.F4ExplicitPos.AmbientPairDescent
open CFSG.StandardType
open CFSG.SeitzReduction
open CFSG.SeitzReduction.F4Pilot
open CFSG.LieType.Ree.ReeTag
open CFSG.StandardType.GGFinModel.G5
open scoped CFSG.ConvolutionPoints

namespace CFSG.StandardType.F4ExplicitPos.AmbientPairFinish
variable {K Ω : Type} [Field K] [Finite K] [Field Ω] [Algebra K Ω]

section Combined
variable [IsAlgClosed Ω] [CharP Ω 2] [Algebra (ZMod 2) Ω] [Algebra.IsAlgebraic (ZMod 2) Ω]

theorem f4_arbitrary_root_finite_endpoint
    (f : ℕ) (hf : 1 ≤ f) (hcard : Nat.card K = 2 ^ f)
    {α : Fin Tag.F4.rank → ℤ} (hα : IsRoot Tag.F4 α)
    {g : ModGL Tag.F4 Ω} (hgA : g ∈ adjointGroup Tag.F4 Ω)
    (hstabplus : (rootSubgroup Tag.F4 Ω α).map
        (MulAut.conj (entrywiseFrobGL Tag.F4 Ω 2 f g)).toMonoidHom =
      (rootSubgroup Tag.F4 Ω α).map (MulAut.conj g).toMonoidHom)
    (hstabminus : (rootSubgroup Tag.F4 Ω (-α)).map
        (MulAut.conj (entrywiseFrobGL Tag.F4 Ω 2 f g)).toMonoidHom =
      (rootSubgroup Tag.F4 Ω (-α)).map (MulAut.conj g).toMonoidHom)
    {P Pm : Subgroup (ModGL Tag.F4 Ω)}
    (hPle : P ≤ (rootSubgroup Tag.F4 Ω α).map (MulAut.conj g).toMonoidHom)
    (hPmle : Pm ≤ (rootSubgroup Tag.F4 Ω (-α)).map (MulAut.conj g).toMonoidHom)
    (hPfix : ∀ x ∈ P, entrywiseFrobGL Tag.F4 Ω 2 f x = x)
    (hPmfix : ∀ x ∈ Pm, entrywiseFrobGL Tag.F4 Ω 2 f x = x)
    (hPcard : Nat.card P = Nat.card K)
    (hPmcard : Nat.card Pm = Nat.card K) :
    ∃ (β : Fin Tag.F4.rank → ℤ) (uK : adjointGroup Tag.F4 K),
      (β = highRoot Tag.F4 ∨ β = deltaF4) ∧
      P = ((rootSubgroup Tag.F4 K β).map
            (bcGL (τ := Tag.F4) (algebraMap K Ω))).map
            (MulAut.conj (bcGL (τ := Tag.F4) (algebraMap K Ω)
              (uK : ModGL Tag.F4 K))).toMonoidHom ∧
      Pm = ((rootSubgroup Tag.F4 K (-β)).map
            (bcGL (τ := Tag.F4) (algebraMap K Ω))).map
            (MulAut.conj (bcGL (τ := Tag.F4) (algebraMap K Ω)
              (uK : ModGL Tag.F4 K))).toMonoidHom := by
  obtain ⟨β, w, hβmem, hw⟩ := f4_exists_weyl_highRoot_or_dualRoot hα
  have hβ : IsRoot Tag.F4 β := by
    rcases hβmem with rfl | rfl
    · exact isRoot_highRoot Tag.F4
    · exact isRoot_dualRoot_highRoot
  let nw : ModGL Tag.F4 Ω := canonicalRep (coxeterSystem Tag.F4) Ω w
  let g' : ModGL Tag.F4 Ω := g * nw
  have hg'A : g' ∈ adjointGroup Tag.F4 Ω :=
    Subgroup.mul_mem _ hgA (canonicalRep_mem_adjointGroup (coxeterSystem Tag.F4) Ω w)
  have hFw : entrywiseFrobGL Tag.F4 Ω 2 f nw = nw :=
    f4_entrywiseFrobGL_canonicalRep f w
  have htransport : (rootSubgroup Tag.F4 Ω α).map (MulAut.conj g).toMonoidHom =
      (rootSubgroup Tag.F4 Ω β).map (MulAut.conj g').toMonoidHom :=
    f4_rootSubgroup_conj_weyl_transport (Ω := Ω) w hβ hw g
  have htransport_neg : (rootSubgroup Tag.F4 Ω (-α)).map (MulAut.conj g).toMonoidHom =
      (rootSubgroup Tag.F4 Ω (-β)).map (MulAut.conj g').toMonoidHom :=
    f4_rootSubgroup_conj_weyl_transport_neg (Ω := Ω) w hβ hw g
  have hweyl : (rootSubgroup Tag.F4 Ω β).map (MulAut.conj nw).toMonoidHom =
      rootSubgroup Tag.F4 Ω α := by
    rw [← hw]
    exact (canonical_weyl_root_transport Tag.F4 Ω).2.1 w β hβ
  have hweyl_neg : (rootSubgroup Tag.F4 Ω (-β)).map (MulAut.conj nw).toMonoidHom =
      rootSubgroup Tag.F4 Ω (-α) := by
    have hw' : w • (-β) = -α := by rw [smul_neg, hw]
    rw [← hw']
    exact (canonical_weyl_root_transport Tag.F4 Ω).2.1 w (-β) (IsRoot.neg hβ)
  have hstabplus' : (rootSubgroup Tag.F4 Ω β).map
      (MulAut.conj (entrywiseFrobGL Tag.F4 Ω 2 f g')).toMonoidHom =
      (rootSubgroup Tag.F4 Ω β).map (MulAut.conj g').toMonoidHom := by
    have hFg' : entrywiseFrobGL Tag.F4 Ω 2 f g' =
        entrywiseFrobGL Tag.F4 Ω 2 f g * nw := by
      rw [show g' = g * nw from rfl, map_mul, hFw]
    have hcomp : (MulAut.conj (entrywiseFrobGL Tag.F4 Ω 2 f g * nw)).toMonoidHom =
        ((MulAut.conj (entrywiseFrobGL Tag.F4 Ω 2 f g)).toMonoidHom).comp
          ((MulAut.conj nw).toMonoidHom) := by
      ext x
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [hFg', hcomp, ← Subgroup.map_map, hweyl, hstabplus]
    exact htransport
  have hstabminus' : (rootSubgroup Tag.F4 Ω (-β)).map
      (MulAut.conj (entrywiseFrobGL Tag.F4 Ω 2 f g')).toMonoidHom =
      (rootSubgroup Tag.F4 Ω (-β)).map (MulAut.conj g').toMonoidHom := by
    have hFg' : entrywiseFrobGL Tag.F4 Ω 2 f g' =
        entrywiseFrobGL Tag.F4 Ω 2 f g * nw := by
      rw [show g' = g * nw from rfl, map_mul, hFw]
    have hcomp : (MulAut.conj (entrywiseFrobGL Tag.F4 Ω 2 f g * nw)).toMonoidHom =
        ((MulAut.conj (entrywiseFrobGL Tag.F4 Ω 2 f g)).toMonoidHom).comp
          ((MulAut.conj nw).toMonoidHom) := by
      ext x
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [hFg', hcomp, ← Subgroup.map_map, hweyl_neg, hstabminus]
    exact htransport_neg
  have hPle' : P ≤ (rootSubgroup Tag.F4 Ω β).map (MulAut.conj g').toMonoidHom := by
    rw [← htransport]; exact hPle
  have hPmle' : Pm ≤ (rootSubgroup Tag.F4 Ω (-β)).map (MulAut.conj g').toMonoidHom := by
    rw [← htransport_neg]; exact hPmle
  refine ⟨β, ?_⟩
  rcases hβmem with rfl | rfl
  · obtain ⟨uK, hP, hPm⟩ :=
      f4_long_pair_finite_endpoint (K := K) (Ω := Ω) f hf hcard hg'A
        hstabplus' hstabminus' hPle' hPmle' hPfix hPmfix hPcard hPmcard
    exact ⟨uK, Or.inl rfl, hP, hPm⟩
  · obtain ⟨uK, hP, hPm⟩ :=
      f4_short_pair_finite_endpoint (K := K) (Ω := Ω) f hf hcard hg'A
        hstabplus' hstabminus' hPle' hPmle' hPfix hPmfix hPcard hPmcard
    exact ⟨uK, Or.inr rfl, hP, hPm⟩

end Combined

section Guard

open CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos

theorem f4_ggRootPosG0_of_pair
    {X : Type} [Group X] (n f p : ℕ) (ψ : (ggU .F4 n f).K →* X) (R Rm : Subgroup X)
    (β : Fin Tag.F4.rank → ℤ) (hβ : IsRoot Tag.F4 β)
    (h2β : ¬ IsRoot Tag.F4 (2 • β))
    (u : (ggU .F4 n f).K)
    (hR : R = ggRootSub (ggU .F4 n f).D ψ β u)
    (hRm : Rm = ggRootSub (ggU .F4 n f).D ψ (-β) u) :
    GGRootPosG0 .F4 n f p ψ R Rm := by
  refine ⟨β, ?_, ?_, u, hR, hRm⟩
  · exact (mem_adjDatum_roots_no117 (rootOperatorFamily Tag.F4)
      (GaloisField 2 f)).2 hβ
  · right
    refine ⟨Or.inr (Or.inl rfl), ?_⟩
    intro h
    exact h2β ((mem_adjDatum_roots_no117 (rootOperatorFamily Tag.F4)
      (GaloisField 2 f)).1 h)

end Guard

section Final

variable [IsAlgClosed Ω] [CharP Ω 2] [Algebra (ZMod 2) Ω] [Algebra.IsAlgebraic (ZMod 2) Ω]

open CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos

theorem f4_ggRootPosG0_of_arbitrary_root
    {X : Type} [Group X]
    (n f p : ℕ) (hf : 1 ≤ f) [Algebra (GaloisField 2 f) Ω]
    (ψ : adjointGroup Tag.F4 (GaloisField 2 f) →* X)
    (G0 : Subgroup X) (hG0 : ψ.range = G0)
    (hker : ψ.ker ≤ Subgroup.center (adjointGroup Tag.F4 (GaloisField 2 f)))
    (hcenter : Subgroup.center (adjointGroup Tag.F4 (GaloisField 2 f)) = ⊥)
    (R Rm : Subgroup X) (hRJ : R ≤ G0) (hRmJ : Rm ≤ G0)
    {α : Fin Tag.F4.rank → ℤ} (hα : IsRoot Tag.F4 α)
    {g : ModGL Tag.F4 Ω} (hgA : g ∈ adjointGroup Tag.F4 Ω)
    (hstabplus : (rootSubgroup Tag.F4 Ω α).map
        (MulAut.conj (entrywiseFrobGL Tag.F4 Ω 2 f g)).toMonoidHom =
      (rootSubgroup Tag.F4 Ω α).map (MulAut.conj g).toMonoidHom)
    (hstabminus : (rootSubgroup Tag.F4 Ω (-α)).map
        (MulAut.conj (entrywiseFrobGL Tag.F4 Ω 2 f g)).toMonoidHom =
      (rootSubgroup Tag.F4 Ω (-α)).map (MulAut.conj g).toMonoidHom)
    (hRle : (R.subgroupOf G0).map (etaG0 (Ω := Ω) f ψ G0 hG0 hker hcenter) ≤
      (rootSubgroup Tag.F4 Ω α).map (MulAut.conj g).toMonoidHom)
    (hRmle : (Rm.subgroupOf G0).map (etaG0 (Ω := Ω) f ψ G0 hG0 hker hcenter) ≤
      (rootSubgroup Tag.F4 Ω (-α)).map (MulAut.conj g).toMonoidHom)
    (hRfix : ∀ x ∈ (R.subgroupOf G0).map (etaG0 (Ω := Ω) f ψ G0 hG0 hker hcenter),
      entrywiseFrobGL Tag.F4 Ω 2 f x = x)
    (hRmfix : ∀ x ∈ (Rm.subgroupOf G0).map (etaG0 (Ω := Ω) f ψ G0 hG0 hker hcenter),
      entrywiseFrobGL Tag.F4 Ω 2 f x = x)
    (hRcard : Nat.card ((R.subgroupOf G0).map
        (etaG0 (Ω := Ω) f ψ G0 hG0 hker hcenter)) = Nat.card (GaloisField 2 f))
    (hRmcard : Nat.card ((Rm.subgroupOf G0).map
        (etaG0 (Ω := Ω) f ψ G0 hG0 hker hcenter)) = Nat.card (GaloisField 2 f)) :
    GGRootPosG0 .F4 n f p ψ R Rm := by
  have hcard : Nat.card (GaloisField 2 f) = 2 ^ f :=
    GaloisField.card 2 f (by omega)
  obtain ⟨β, uK, hβmem, hP, hPm⟩ :=
    f4_arbitrary_root_finite_endpoint (K := GaloisField 2 f) (Ω := Ω) f hf hcard hα hgA
      hstabplus hstabminus hRle hRmle hRfix hRmfix hRcard hRmcard
  have hβ : IsRoot Tag.F4 β := by
    rcases hβmem with rfl | rfl
    · exact isRoot_highRoot Tag.F4
    · exact isRoot_dualRoot_highRoot
  have h2β : ¬ IsRoot Tag.F4 (2 • β) := by
    rcases hβmem with rfl | rfl
    · intro h
      have h1 := eq_one_of_isRoot_nsmul_no117 h
      norm_num at h1
    · intro h
      have h1 := eq_one_of_isRoot_nsmul_no117 h
      norm_num at h1
  obtain ⟨u, hRu, hRmu⟩ :=
    f4_g0_pairLift_adapter (Ω := Ω) n f ψ G0 hG0 hker hcenter β hβ
      (Subgroup.mem_map_of_mem _ uK.2) R Rm hRJ hRmJ hP hPm
  exact f4_ggRootPosG0_of_pair n f p ψ R Rm β hβ h2β u hRu hRmu

end Final

end CFSG.StandardType.F4ExplicitPos.AmbientPairFinish

end

end
