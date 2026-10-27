module

public import CFSG.LieType.AlgebraicGroups.ConvolutionPoints
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.ComponentAttachPart1
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.SelectedPair
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.AmbientPairFinishPart1

@[expose] public section

public noncomputable section

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType
  CFSG.LieType.Chevalley CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.StandardType.F4ExplicitPos.BaseChange

open CFSG.StandardType.F4ExplicitPos.PinnedBaseChange

open CFSG.StandardType.F4ExplicitPos.AmbientAction

open CFSG.StandardType.F4ExplicitPos.AmbientPairDescent

open CFSG.StandardType.F4ExplicitPos.AmbientPairFinish

open CFSG.StandardType.F4ExplicitPos.ComponentAttach

open CFSG.StandardType.F4ExplicitPos.RationalA2Finish

open CFSG.StandardType.F4ExplicitPos.NativePinFinal

open CFSG.StandardType.F4ExplicitPos.SelectedPair

open CFSG.StandardType

open CFSG.StandardType.S2MathFi1035Pos

open scoped Matrix

open scoped CFSG.ConvolutionPoints

namespace CFSG.StandardType.F4ExplicitPos.SelectedPairAmbient

variable {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharP Ω 2]

variable [Algebra (ZMod 2) Ω] [Algebra.IsAlgebraic (ZMod 2) Ω]

variable {X : Type} [Group X] [Finite X]

theorem etaG0_eq_conj_etaF4
    {f : ℕ} [Algebra (GaloisField 2 f) Ω]
    (ψ : adjointGroup Tag.F4 (GaloisField 2 f) →* X) (G0 : Subgroup X) (hG0 : ψ.range = G0)
    (hker : ψ.ker ≤ Subgroup.center (adjointGroup Tag.F4 (GaloisField 2 f)))
    (hcenter : Subgroup.center (adjointGroup Tag.F4 (GaloisField 2 f)) = ⊥)
    (g0 : ModGL Tag.F4 Ω) :
    etaG0 (Ω := Ω) f ψ G0 hG0 hker hcenter =
      (MulAut.conj g0).toMonoidHom.comp
        (etaF4 ψ G0 hG0 hker hcenter g0) := by
  apply MonoidHom.ext
  intro y
  rw [MonoidHom.comp_apply, etaF4_apply, etaG0_apply, iotaF4_apply]
  change (jF4 (K := GaloisField 2 f) (L := Ω)
      ((psiEquiv ψ G0 hG0 hker hcenter).symm y) : ModGL Tag.F4 Ω) =
    g0 * (g0⁻¹ * (jF4 (K := GaloisField 2 f) (L := Ω)
      ((psiEquiv ψ G0 hG0 hker hcenter).symm y) : ModGL Tag.F4 Ω) * g0) * g0⁻¹
  group

theorem iotaF4_injective_local
    {f : ℕ} [Algebra (GaloisField 2 f) Ω]
    (ψ : adjointGroup Tag.F4 (GaloisField 2 f) →* X) (G0 : Subgroup X) (hG0 : ψ.range = G0)
    (hker : ψ.ker ≤ Subgroup.center (adjointGroup Tag.F4 (GaloisField 2 f)))
    (hcenter : Subgroup.center (adjointGroup Tag.F4 (GaloisField 2 f)) = ⊥) :
    Function.Injective (iotaF4 ψ G0 hG0 hker hcenter : G0 →* adjointGroup Tag.F4 Ω) := by
  intro x y hxy
  obtain ⟨u, rfl⟩ := (eF4 ψ G0 hG0 hker hcenter).surjective x
  obtain ⟨v, rfl⟩ := (eF4 ψ G0 hG0 hker hcenter).surjective y
  rw [iotaF4_e, iotaF4_e] at hxy
  rw [jF4_injective hxy]

theorem etaF4_injective_local
    {f : ℕ} [Algebra (GaloisField 2 f) Ω]
    (ψ : adjointGroup Tag.F4 (GaloisField 2 f) →* X) (G0 : Subgroup X) (hG0 : ψ.range = G0)
    (hker : ψ.ker ≤ Subgroup.center (adjointGroup Tag.F4 (GaloisField 2 f)))
    (hcenter : Subgroup.center (adjointGroup Tag.F4 (GaloisField 2 f)) = ⊥)
    (g0 : ModGL Tag.F4 Ω) :
    Function.Injective (etaF4 ψ G0 hG0 hker hcenter g0) := by
  intro x y hxy
  let i : G0 →* adjointGroup Tag.F4 Ω := iotaF4 ψ G0 hG0 hker hcenter
  rw [etaF4_apply, etaF4_apply] at hxy
  have h1 : (i x : ModGL Tag.F4 Ω) = (i y : ModGL Tag.F4 Ω) := by
    calc (i x : ModGL Tag.F4 Ω)
        = g0 * (g0⁻¹ * (i x : ModGL Tag.F4 Ω) * g0) * g0⁻¹ := by group
      _ = g0 * (g0⁻¹ * (i y : ModGL Tag.F4 Ω) * g0) * g0⁻¹ := by
          exact congrArg (fun z => g0 * z * g0⁻¹) hxy
      _ = (i y : ModGL Tag.F4 Ω) := by group
  exact iotaF4_injective_local ψ G0 hG0 hker hcenter (Subtype.ext h1)

theorem conjugatedRootRange_le_conj_rootSubgroup
    {k : Type} [Field k] [Algebra k Ω]
    (wD : ModGL Tag.F4 Ω) (α : Fin Tag.F4.rank → ℤ) (ε : Ωˣ) :
    conjugatedRootRange (k := k) wD α ε ≤
      (rootSubgroup Tag.F4 Ω α).map (MulAut.conj wD).toMonoidHom := by
  intro y hy
  rw [mem_conjugatedRootRange_iff] at hy
  obtain ⟨t, rfl⟩ := hy
  exact Subgroup.mem_map.2 ⟨pinnedX Tag.F4 Ω α ((ε : Ω) * algebraMap k Ω t),
    Subgroup.subset_closure ⟨_, rfl⟩, rfl⟩

theorem f4_frob_conj_step_commute
    (f : ℕ) [Algebra (GaloisField 2 f) Ω] {Fr : Ω →+* Ω}
    (hFr : ∀ c, Fr c = c ^ Nat.card (GaloisField 2 f))
    (hFr_eq : Fr = iterateFrobenius Ω 2 f)
    (w : WeylGroup Tag.F4) {g0 : ModGL Tag.F4 Ω}
    (hg0C : g0 ∈ adjointGroup Tag.F4 Ω)
    (hg0 : ((frobF4 (K := GaloisField 2 f) (L := Ω) Fr hFr ⟨g0, hg0C⟩ : adjointGroup Tag.F4 Ω) :
      ModGL Tag.F4 Ω) = g0 * canonicalRep (coxeterSystem Tag.F4) Ω w)
    (y : ModGL Tag.F4 Ω) :
    entrywiseFrobGL Tag.F4 Ω 2 f (g0 * y * g0⁻¹) =
      g0 * (langDatumF4 (K := GaloisField 2 f) (L := Ω) Fr hFr w hg0C hg0).step y * g0⁻¹ := by
  have hPhi : (langDatumF4 (K := GaloisField 2 f) (L := Ω) Fr hFr w hg0C hg0).Φ =
      entrywiseFrobGL Tag.F4 Ω 2 f := by
    rw [langDatumF4_Phi, hFr_eq]
  have hFg0 : entrywiseFrobGL Tag.F4 Ω 2 f g0 =
      g0 * (langDatumF4 (K := GaloisField 2 f) (L := Ω) Fr hFr w hg0C hg0).n := by
    change Units.map (entrywiseHom (iterateFrobenius Ω 2 f)) g0 = _
    rw [← hFr_eq, ← frobF4_coe_eq_unitsMap Fr hFr ⟨g0, hg0C⟩, hg0, langDatumF4_n]
  rw [map_mul, map_mul, map_inv, hFg0]
  rw [show (langDatumF4 (K := GaloisField 2 f) (L := Ω) Fr hFr w hg0C hg0).step y =
      (langDatumF4 (K := GaloisField 2 f) (L := Ω) Fr hFr w hg0C hg0).n *
        (langDatumF4 (K := GaloisField 2 f) (L := Ω) Fr hFr w hg0C hg0).Φ y *
        (langDatumF4 (K := GaloisField 2 f) (L := Ω) Fr hFr w hg0C hg0).n⁻¹ from rfl, hPhi]
  group

theorem map_entrywiseFrobGL_rootSubgroup
    (f : ℕ) (hf : 1 ≤ f)
    (α : Fin Tag.F4.rank → ℤ) :
    (rootSubgroup Tag.F4 Ω α).map (entrywiseFrobGL Tag.F4 Ω 2 f) = rootSubgroup Tag.F4 Ω α := by
  have hbij : Function.Bijective (iterateFrobenius Ω 2 f) :=
    frobenius_bijective (k := GaloisField 2 f) (L := Ω) (iterateFrobenius Ω 2 f)
      (fun c => by rw [iterateFrobenius_def, GaloisField.card 2 f (by omega)])
  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [mem_rootSubgroup] at hy ⊢
    obtain ⟨c, rfl⟩ := hy
    exact ⟨iterateFrobenius Ω 2 f c,
      (LangPosition.entrywiseFrobGL_pinnedX_no117 (τ := Tag.F4) (k := Ω) 2 f α c).symm⟩
  · intro x hx
    rw [mem_rootSubgroup] at hx
    obtain ⟨c, rfl⟩ := hx
    obtain ⟨d, hd⟩ := hbij.surjective c
    rw [Subgroup.mem_map]
    refine ⟨pinnedX Tag.F4 Ω α d, Subgroup.subset_closure ⟨d, rfl⟩, ?_⟩
    rw [LangPosition.entrywiseFrobGL_pinnedX_no117 (τ := Tag.F4) (k := Ω) 2 f α d, hd]

theorem f4_frob_stable_of_step_stable
    (f : ℕ) (hf : 1 ≤ f) [Algebra (GaloisField 2 f) Ω] {Fr : Ω →+* Ω}
    (hFr : ∀ c, Fr c = c ^ Nat.card (GaloisField 2 f))
    (hFr_eq : Fr = iterateFrobenius Ω 2 f)
    (w : WeylGroup Tag.F4) {g0 : ModGL Tag.F4 Ω}
    (hg0C : g0 ∈ adjointGroup Tag.F4 Ω)
    (hg0 : ((frobF4 (K := GaloisField 2 f) (L := Ω) Fr hFr ⟨g0, hg0C⟩ : adjointGroup Tag.F4 Ω) :
      ModGL Tag.F4 Ω) = g0 * canonicalRep (coxeterSystem Tag.F4) Ω w)
    {wD : ModGL Tag.F4 Ω} {α : Fin Tag.F4.rank → ℤ}
    (hstep : ((rootSubgroup Tag.F4 Ω α).map (MulAut.conj wD).toMonoidHom).map
        (langDatumF4 (K := GaloisField 2 f) (L := Ω) Fr hFr w hg0C hg0).step =
      (rootSubgroup Tag.F4 Ω α).map (MulAut.conj wD).toMonoidHom) :
    (rootSubgroup Tag.F4 Ω α).map
        (MulAut.conj (entrywiseFrobGL Tag.F4 Ω 2 f (g0 * wD))).toMonoidHom =
      (rootSubgroup Tag.F4 Ω α).map (MulAut.conj (g0 * wD)).toMonoidHom := by
  have hmap : ((rootSubgroup Tag.F4 Ω α).map
      (MulAut.conj (g0 * wD)).toMonoidHom).map (entrywiseFrobGL Tag.F4 Ω 2 f) =
      (rootSubgroup Tag.F4 Ω α).map (MulAut.conj (g0 * wD)).toMonoidHom := by
    have hcurve : (rootSubgroup Tag.F4 Ω α).map (MulAut.conj (g0 * wD)).toMonoidHom =
        ((rootSubgroup Tag.F4 Ω α).map (MulAut.conj wD).toMonoidHom).map
          (MulAut.conj g0).toMonoidHom := by
      rw [show (MulAut.conj (g0 * wD)).toMonoidHom =
          ((MulAut.conj g0).toMonoidHom).comp ((MulAut.conj wD).toMonoidHom) from by
        ext x
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group,
        Subgroup.map_map]
    have hcomp : (entrywiseFrobGL Tag.F4 Ω 2 f).comp (MulAut.conj g0).toMonoidHom =
        (MulAut.conj g0).toMonoidHom.comp
          (langDatumF4 (K := GaloisField 2 f) (L := Ω) Fr hFr w hg0C hg0).step := by
      apply MonoidHom.ext
      intro y
      change (entrywiseFrobGL Tag.F4 Ω 2 f) (g0 * y * g0⁻¹) =
        g0 * (langDatumF4 (K := GaloisField 2 f) (L := Ω) Fr hFr w hg0C hg0).step y * g0⁻¹
      exact f4_frob_conj_step_commute f hFr hFr_eq w hg0C hg0 y
    rw [hcurve, Subgroup.map_map, hcomp, ← Subgroup.map_map, hstep]
  have hcomp : (entrywiseFrobGL Tag.F4 Ω 2 f).comp (MulAut.conj (g0 * wD)).toMonoidHom =
      (MulAut.conj (entrywiseFrobGL Tag.F4 Ω 2 f (g0 * wD))).toMonoidHom.comp
        (entrywiseFrobGL Tag.F4 Ω 2 f) := by
    apply MonoidHom.ext
    intro y
    change (entrywiseFrobGL Tag.F4 Ω 2 f) ((g0 * wD) * y * (g0 * wD)⁻¹) =
      (entrywiseFrobGL Tag.F4 Ω 2 f) (g0 * wD) * (entrywiseFrobGL Tag.F4 Ω 2 f) y *
        ((entrywiseFrobGL Tag.F4 Ω 2 f) (g0 * wD))⁻¹
    rw [map_mul, map_mul, map_inv]
  have hkey : (rootSubgroup Tag.F4 Ω α).map
        (MulAut.conj (entrywiseFrobGL Tag.F4 Ω 2 f (g0 * wD))).toMonoidHom =
      ((rootSubgroup Tag.F4 Ω α).map (MulAut.conj (g0 * wD)).toMonoidHom).map
        (entrywiseFrobGL Tag.F4 Ω 2 f) := by
    rw [Subgroup.map_map]
    rw [hcomp]
    rw [← Subgroup.map_map]
    rw [map_entrywiseFrobGL_rootSubgroup f hf]
  rw [hkey, hmap]

end CFSG.StandardType.F4ExplicitPos.SelectedPairAmbient
end

end
