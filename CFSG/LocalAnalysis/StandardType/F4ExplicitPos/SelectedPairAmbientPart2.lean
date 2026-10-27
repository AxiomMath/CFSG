module

public import CFSG.LieType.AlgebraicGroups.ConvolutionPoints
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.NativePinFinalPart2
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.AmbientPairFinishPart2
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.SelectedPairAmbientPart1

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

theorem f4_selected_pair_lower_endpoint
    (n f p : ℕ) (hf : 1 ≤ f) [Algebra (GaloisField 2 f) Ω]
    (ψ : adjointGroup Tag.F4 (GaloisField 2 f) →* X)
    (G0 : Subgroup X) (hG0 : ψ.range = G0)
    (hker : ψ.ker ≤ Subgroup.center (adjointGroup Tag.F4 (GaloisField 2 f)))
    (hcenter : Subgroup.center (adjointGroup Tag.F4 (GaloisField 2 f)) = ⊥)
    {Fr : Ω →+* Ω} (hFr : ∀ c, Fr c = c ^ Nat.card (GaloisField 2 f))
    (hFr_eq : Fr = iterateFrobenius Ω 2 f)
    (w : WeylGroup Tag.F4) {g0 : ModGL Tag.F4 Ω}
    (hg0C : g0 ∈ adjointGroup Tag.F4 Ω)
    (hg0 : ((frobF4 (K := GaloisField 2 f) (L := Ω) Fr hFr ⟨g0, hg0C⟩ : adjointGroup Tag.F4 Ω) :
      ModGL Tag.F4 Ω) = g0 * canonicalRep (coxeterSystem Tag.F4) Ω w)
    (J : Subgroup X) (hJG0 : J ≤ G0)
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin Tag.F4.rank → ℤ) →* M}
    {i : KernelComponent χ}
    {α : Fin Tag.F4.rank → ℤ} (hα : α ∈ componentRoots χ i)
    {wD : ModGL Tag.F4 Ω} (hwD : wD ∈ Zsub χ) (ε εm : Ωˣ)
    (hP : conjugatedRootRange (k := GaloisField 2 f) wD α ε ≤
      (J.subgroupOf G0).map (etaF4 ψ G0 hG0 hker hcenter g0))
    (hPm : conjugatedRootRange (k := GaloisField 2 f) wD (-α) εm ≤
      (J.subgroupOf G0).map (etaF4 ψ G0 hG0 hker hcenter g0))
    (hstepplus : ((rootSubgroup Tag.F4 Ω α).map (MulAut.conj wD).toMonoidHom).map
        (langDatumF4 (K := GaloisField 2 f) (L := Ω) Fr hFr w hg0C hg0).step =
      (rootSubgroup Tag.F4 Ω α).map (MulAut.conj wD).toMonoidHom)
    (hstepminus : ((rootSubgroup Tag.F4 Ω (-α)).map (MulAut.conj wD).toMonoidHom).map
        (langDatumF4 (K := GaloisField 2 f) (L := Ω) Fr hFr w hg0C hg0).step =
      (rootSubgroup Tag.F4 Ω (-α)).map (MulAut.conj wD).toMonoidHom) :
    ∃ R Rm : Subgroup X,
      R ≤ J ∧ Rm ≤ J ∧
      (R.subgroupOf G0).map (etaF4 ψ G0 hG0 hker hcenter g0) =
        conjugatedRootRange (k := GaloisField 2 f) wD α ε ∧
      (Rm.subgroupOf G0).map (etaF4 ψ G0 hG0 hker hcenter g0) =
        conjugatedRootRange (k := GaloisField 2 f) wD (-α) εm ∧
      GGRootPosG0 .F4 n f p ψ R Rm := by
  let η : G0 →* ModGL Tag.F4 Ω := etaF4 ψ G0 hG0 hker hcenter g0
  let Pbar : Subgroup (ModGL Tag.F4 Ω) := conjugatedRootRange (k := GaloisField 2 f) wD α ε
  let Pmbar : Subgroup (ModGL Tag.F4 Ω) := conjugatedRootRange (k := GaloisField 2 f) wD (-α) εm
  let Jbar : Subgroup (ModGL Tag.F4 Ω) := (J.subgroupOf G0).map η
  let R0 : Subgroup G0 := Pbar.comap η
  let Rm0 : Subgroup G0 := Pmbar.comap η
  let R : Subgroup X := R0.map G0.subtype
  let Rm : Subgroup X := Rm0.map G0.subtype
  have hη : Function.Injective η := etaF4_injective_local ψ G0 hG0 hker hcenter g0
  have hPbar_range : Pbar ≤ η.range := by
    intro x hx
    obtain ⟨y, -, hy⟩ := Subgroup.mem_map.1 (hP hx)
    exact ⟨y, hy⟩
  have hPmbar_range : Pmbar ≤ η.range := by
    intro x hx
    obtain ⟨y, -, hy⟩ := Subgroup.mem_map.1 (hPm hx)
    exact ⟨y, hy⟩
  have hRsub : R.subgroupOf G0 = R0 := by
    change (R0.map G0.subtype).comap G0.subtype = R0
    exact Subgroup.comap_map_eq_self_of_injective G0.subtype_injective R0
  have hRmsub : Rm.subgroupOf G0 = Rm0 := by
    change (Rm0.map G0.subtype).comap G0.subtype = Rm0
    exact Subgroup.comap_map_eq_self_of_injective G0.subtype_injective Rm0
  have hRη : (R.subgroupOf G0).map η = Pbar := by
    rw [hRsub]
    exact Subgroup.map_comap_eq_self hPbar_range
  have hRmη : (Rm.subgroupOf G0).map η = Pmbar := by
    rw [hRmsub]
    exact Subgroup.map_comap_eq_self hPmbar_range
  have hJbar_comap : Jbar.comap η = J.subgroupOf G0 := by
    change ((J.subgroupOf G0).map η).comap η = J.subgroupOf G0
    exact Subgroup.comap_map_eq_self_of_injective hη (J.subgroupOf G0)
  have hR0_le_J : R0 ≤ J.subgroupOf G0 := by
    change Pbar.comap η ≤ J.subgroupOf G0
    rw [← hJbar_comap]
    exact Subgroup.comap_mono hP
  have hRm0_le_J : Rm0 ≤ J.subgroupOf G0 := by
    change Pmbar.comap η ≤ J.subgroupOf G0
    rw [← hJbar_comap]
    exact Subgroup.comap_mono hPm
  have hRJ : R ≤ J := by
    change R0.map G0.subtype ≤ J
    have h := Subgroup.map_mono (f := G0.subtype) hR0_le_J
    rwa [Subgroup.map_subgroupOf_eq_of_le hJG0] at h
  have hRmJ : Rm ≤ J := by
    change Rm0.map G0.subtype ≤ J
    have h := Subgroup.map_mono (f := G0.subtype) hRm0_le_J
    rwa [Subgroup.map_subgroupOf_eq_of_le hJG0] at h
  have hRetaG0 : (R.subgroupOf G0).map (etaG0 (Ω := Ω) f ψ G0 hG0 hker hcenter) =
      Pbar.map (MulAut.conj g0).toMonoidHom := by
    rw [etaG0_eq_conj_etaF4 (f := f) ψ G0 hG0 hker hcenter g0, ← Subgroup.map_map, hRη]
  have hRmetaG0 : (Rm.subgroupOf G0).map (etaG0 (Ω := Ω) f ψ G0 hG0 hker hcenter) =
      Pmbar.map (MulAut.conj g0).toMonoidHom := by
    rw [etaG0_eq_conj_etaF4 (f := f) ψ G0 hG0 hker hcenter g0, ← Subgroup.map_map, hRmη]
  have hgA : g0 * wD ∈ adjointGroup Tag.F4 Ω :=
    Subgroup.mul_mem _ hg0C (Zsub_le_adjointGroup χ hwD)
  have hstabplus : (rootSubgroup Tag.F4 Ω α).map
      (MulAut.conj (entrywiseFrobGL Tag.F4 Ω 2 f (g0 * wD))).toMonoidHom =
      (rootSubgroup Tag.F4 Ω α).map (MulAut.conj (g0 * wD)).toMonoidHom :=
    f4_frob_stable_of_step_stable f hf hFr hFr_eq w hg0C hg0 hstepplus
  have hstabminus : (rootSubgroup Tag.F4 Ω (-α)).map
      (MulAut.conj (entrywiseFrobGL Tag.F4 Ω 2 f (g0 * wD))).toMonoidHom =
      (rootSubgroup Tag.F4 Ω (-α)).map (MulAut.conj (g0 * wD)).toMonoidHom :=
    f4_frob_stable_of_step_stable f hf hFr hFr_eq w hg0C hg0 hstepminus
  have hPbar_curve : Pbar ≤ (rootSubgroup Tag.F4 Ω α).map (MulAut.conj wD).toMonoidHom :=
    conjugatedRootRange_le_conj_rootSubgroup (k := GaloisField 2 f) wD α ε
  have hPmbar_curve : Pmbar ≤ (rootSubgroup Tag.F4 Ω (-α)).map (MulAut.conj wD).toMonoidHom :=
    conjugatedRootRange_le_conj_rootSubgroup (k := GaloisField 2 f) wD (-α) εm
  have hRle : (R.subgroupOf G0).map (etaG0 (Ω := Ω) f ψ G0 hG0 hker hcenter) ≤
      (rootSubgroup Tag.F4 Ω α).map (MulAut.conj (g0 * wD)).toMonoidHom := by
    rw [hRetaG0]
    calc Pbar.map (MulAut.conj g0).toMonoidHom
        ≤ ((rootSubgroup Tag.F4 Ω α).map (MulAut.conj wD).toMonoidHom).map
            (MulAut.conj g0).toMonoidHom := Subgroup.map_mono hPbar_curve
      _ = (rootSubgroup Tag.F4 Ω α).map (MulAut.conj (g0 * wD)).toMonoidHom := by
          rw [show (MulAut.conj (g0 * wD)).toMonoidHom =
              ((MulAut.conj g0).toMonoidHom).comp ((MulAut.conj wD).toMonoidHom) from by
            ext x
            simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
            group,
            Subgroup.map_map]
  have hRmle : (Rm.subgroupOf G0).map (etaG0 (Ω := Ω) f ψ G0 hG0 hker hcenter) ≤
      (rootSubgroup Tag.F4 Ω (-α)).map (MulAut.conj (g0 * wD)).toMonoidHom := by
    rw [hRmetaG0]
    calc Pmbar.map (MulAut.conj g0).toMonoidHom
        ≤ ((rootSubgroup Tag.F4 Ω (-α)).map (MulAut.conj wD).toMonoidHom).map
            (MulAut.conj g0).toMonoidHom := Subgroup.map_mono hPmbar_curve
      _ = (rootSubgroup Tag.F4 Ω (-α)).map (MulAut.conj (g0 * wD)).toMonoidHom := by
          rw [show (MulAut.conj (g0 * wD)).toMonoidHom =
              ((MulAut.conj g0).toMonoidHom).comp ((MulAut.conj wD).toMonoidHom) from by
            ext x
            simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
            group,
            Subgroup.map_map]
  have hPbar_model : Pbar ≤ (langDatumF4 (K := GaloisField 2 f) (L :=
      Ω) Fr hFr w hg0C hg0).model := by
    refine le_trans hPbar_range ?_
    exact le_of_eq (etaF4_range_model (L := Ω) (K := GaloisField 2 f) ψ G0 hG0 hker hcenter
      Fr hFr w hg0C hg0)
  have hstep_p_of_mem : ∀ p ∈ Pbar,
      (langDatumF4 (K := GaloisField 2 f) (L := Ω) Fr hFr w hg0C hg0).step p = p := by
    intro p hp
    have h := ((LangDatum.mem_model (D := langDatumF4 (K := GaloisField 2 f) (L :=
        Ω) Fr hFr w hg0C hg0)).1 (hPbar_model hp)).2
    rw [show (langDatumF4 (K := GaloisField 2 f) (L := Ω) Fr hFr w hg0C hg0).step p =
        (langDatumF4 (K := GaloisField 2 f) (L := Ω) Fr hFr w hg0C hg0).n *
          (langDatumF4 (K := GaloisField 2 f) (L := Ω) Fr hFr w hg0C hg0).Φ p *
          (langDatumF4 (K := GaloisField 2 f) (L := Ω) Fr hFr w hg0C hg0).n⁻¹ from rfl]
    exact h
  have hRfix : ∀ x ∈ (R.subgroupOf G0).map (etaG0 (Ω := Ω) f ψ G0 hG0 hker hcenter),
      entrywiseFrobGL Tag.F4 Ω 2 f x = x := by
    intro x hx
    rw [hRetaG0] at hx
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.1 hx
    change entrywiseFrobGL Tag.F4 Ω 2 f (g0 * p * g0⁻¹) = g0 * p * g0⁻¹
    rw [f4_frob_conj_step_commute f hFr hFr_eq w hg0C hg0 p, hstep_p_of_mem p hp]
  have hPmbar_model : Pmbar ≤
      (langDatumF4 (K := GaloisField 2 f) (L := Ω) Fr hFr w hg0C hg0).model := by
    refine le_trans hPmbar_range ?_
    exact le_of_eq (etaF4_range_model (L := Ω) (K := GaloisField 2 f) ψ G0 hG0 hker hcenter
      Fr hFr w hg0C hg0)
  have hstepm_p_of_mem : ∀ p ∈ Pmbar,
      (langDatumF4 (K := GaloisField 2 f) (L := Ω) Fr hFr w hg0C hg0).step p = p := by
    intro p hp
    have h := ((LangDatum.mem_model (D := langDatumF4 (K := GaloisField 2 f) (L :=
        Ω) Fr hFr w hg0C hg0)).1 (hPmbar_model hp)).2
    rw [show (langDatumF4 (K := GaloisField 2 f) (L := Ω) Fr hFr w hg0C hg0).step p =
        (langDatumF4 (K := GaloisField 2 f) (L := Ω) Fr hFr w hg0C hg0).n *
          (langDatumF4 (K := GaloisField 2 f) (L := Ω) Fr hFr w hg0C hg0).Φ p *
          (langDatumF4 (K := GaloisField 2 f) (L := Ω) Fr hFr w hg0C hg0).n⁻¹ from rfl]
    exact h
  have hRmfix : ∀ x ∈ (Rm.subgroupOf G0).map (etaG0 (Ω := Ω) f ψ G0 hG0 hker hcenter),
      entrywiseFrobGL Tag.F4 Ω 2 f x = x := by
    intro x hx
    rw [hRmetaG0] at hx
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.1 hx
    change entrywiseFrobGL Tag.F4 Ω 2 f (g0 * p * g0⁻¹) = g0 * p * g0⁻¹
    rw [f4_frob_conj_step_commute f hFr hFr_eq w hg0C hg0 p, hstepm_p_of_mem p hp]
  have hRcard : Nat.card ((R.subgroupOf G0).map (etaG0 (Ω := Ω) f ψ G0 hG0 hker hcenter)) =
      Nat.card (GaloisField 2 f) := by
    rw [hRetaG0, Subgroup.card_map_of_injective (MulAut.conj g0).injective]
    exact conjugatedRootRange_card wD α ε
  have hRmcard : Nat.card ((Rm.subgroupOf G0).map (etaG0 (Ω := Ω) f ψ G0 hG0 hker hcenter)) =
      Nat.card (GaloisField 2 f) := by
    rw [hRmetaG0, Subgroup.card_map_of_injective (MulAut.conj g0).injective]
    exact conjugatedRootRange_card wD (-α) εm
  exact ⟨R, Rm, hRJ, hRmJ, hRη, hRmη,
    f4_ggRootPosG0_of_arbitrary_root n f p hf ψ G0 hG0 hker hcenter R Rm
      (le_trans hRJ hJG0) (le_trans hRmJ hJG0)
      (isRoot_of_mem_componentRoots hα) hgA hstabplus hstabminus
      hRle hRmle hRfix hRmfix hRcard hRmcard⟩

theorem f4_selected_pair_ambient
    (n f p : ℕ) (hf : 1 ≤ f) [Algebra (GaloisField 2 f) Ω]
    (ψ : adjointGroup Tag.F4 (GaloisField 2 f) →* X)
    (G0 : Subgroup X) (hG0 : ψ.range = G0)
    (hker : ψ.ker ≤ Subgroup.center (adjointGroup Tag.F4 (GaloisField 2 f)))
    (hcenter : Subgroup.center (adjointGroup Tag.F4 (GaloisField 2 f)) = ⊥)
    {Fr : Ω →+* Ω} (hFr : ∀ c, Fr c = c ^ Nat.card (GaloisField 2 f))
    (hFr_eq : Fr = iterateFrobenius Ω 2 f)
    (w : WeylGroup Tag.F4) {g0 : ModGL Tag.F4 Ω}
    (hg0C : g0 ∈ adjointGroup Tag.F4 Ω)
    (hg0 : ((frobF4 (K := GaloisField 2 f) (L := Ω) Fr hFr ⟨g0, hg0C⟩ : adjointGroup Tag.F4 Ω) :
      ModGL Tag.F4 Ω) = g0 * canonicalRep (coxeterSystem Tag.F4) Ω w)
    (J : Subgroup X) (hJG0 : J ≤ G0)
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin Tag.F4.rank → ℤ) →* M}
    {i : KernelComponent χ}
    (h : SelectedPairOutput (k := GaloisField 2 f)
      (langDatumF4 (K := GaloisField 2 f) (L := Ω) Fr hFr w hg0C hg0) χ
      ((J.subgroupOf G0).map (etaF4 ψ G0 hG0 hker hcenter g0)) i) :
    ∃ (α : Fin Tag.F4.rank → ℤ) (wD : ModGL Tag.F4 Ω) (ε εm : Ωˣ) (R Rm : Subgroup X),
      α ∈ componentRoots χ i ∧ wD ∈ Zsub χ ∧
      R ≤ J ∧ Rm ≤ J ∧
      (R.subgroupOf G0).map (etaF4 ψ G0 hG0 hker hcenter g0) =
        conjugatedRootRange (k := GaloisField 2 f) wD α ε ∧
      (Rm.subgroupOf G0).map (etaF4 ψ G0 hG0 hker hcenter g0) =
        conjugatedRootRange (k := GaloisField 2 f) wD (-α) εm ∧
      GGRootPosG0 .F4 n f p ψ R Rm := by
  obtain ⟨α, hα, wD, hwD, ε, εm, hP, hPm, -, -, hstepplus, hstepminus⟩ := h
  obtain ⟨R, Rm, hRJ, hRmJ, hRη, hRmη, hpos⟩ :=
    f4_selected_pair_lower_endpoint n f p hf ψ G0 hG0 hker hcenter hFr hFr_eq w hg0C hg0
      J hJG0 hα hwD ε εm hP hPm hstepplus hstepminus
  exact ⟨α, wD, ε, εm, R, Rm, hα, hwD, hRJ, hRmJ, hRη, hRmη, hpos⟩

end CFSG.StandardType.F4ExplicitPos.SelectedPairAmbient

end

end
