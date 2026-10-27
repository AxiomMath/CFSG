module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.RationalB2Part2
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.ActualPerfect
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.InnerSelectedPair
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.B2Inner

@[expose] public section

public noncomputable section

namespace CFSG.StandardType.F4ExplicitPos.B2SelectedPair

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType
  CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.SeitzReduction.F4Pilot

open CFSG.StandardType.F4ExplicitPos.RationalB2

open CFSG.StandardType.F4ExplicitPos.BaseChange

open CFSG.StandardType.F4ExplicitPos.InnerSelectedPair

open CFSG.StandardType.F4ExplicitPos.NativePinFinal

open CFSG.StandardType.F4ExplicitPos.SelectedPair

open scoped Matrix

theorem f4_b2_selected_pair_output_of_hinner
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharP Ω 2]
    [Algebra (ZMod 2) Ω] [Algebra.IsAlgebraic (ZMod 2) Ω]
    {k : Type} [Field k] [Finite k] [CharP k 2] [Algebra k Ω]
    (D : LangDatum Tag.F4 Ω) (f : ℕ) (hf : 1 ≤ f) (hq : D.q = 2 ^ f)
    (hk : Nat.card k = 2 ^ f)
    {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin Tag.F4.rank → ℤ) →* M}
    (ρ : Equiv.Perm (Fin Tag.F4.rank → ℤ)) (hρ : FrobRootMap D ρ)
    (i : KernelComponent χ)
    (hker : ∀ α ∈ kernelRoots χ, ρ α ∈ kernelRoots χ)
    (hinner : twistInner (componentRoots χ i) ρ)
    (v : WeylGroup Tag.F4)
    (hΨ : componentRoots χ i = (fun α => v • α) '' b2LeviRoots)
    {Ccent : Subgroup (ModGL Tag.F4 Ω)} {P : Subgroup (ModGL Tag.F4 Ω)}
    (hP : CFSG.Assembly.IsComponentOf P (D.Γ ⊓ Ccent))
    (hPleH : P ≤ rootSpan Tag.F4 Ω (componentRoots χ i))
    (hHcent : rootSpan Tag.F4 Ω (componentRoots χ i) ≤ Ccent)
    (hΓ : D.Γ = D.model)
    {J : Type*} [Group J] (ηJ : J →* ModGL Tag.F4 Ω)
    (hηinj : Function.Injective ηJ) (hηrange : ηJ.range = P)
    (h28 : IsEmpty (J ≃* alternatingGroup (Fin 6))) :
    SelectedPairOutput (k := k) D χ P i := by
  obtain ⟨σ, z, hσc, hzZ, hnorm, hgoal⟩ :=
    CFSG.StandardType.F4ExplicitPos.NativePinFinal.exists_untwist_one_step_native
      D f hf hq ρ hρ i hker hinner
  have hσ : ∀ c, σ c = c ^ Nat.card k := fun c => by rw [hσc c, hq, hk]
  have hS : ∀ γ ∈ b2LeviRoots, IsRoot Tag.F4 γ := fun γ hγ => (mem_b2LeviRoots.1 hγ).1
  let n : ModGL Tag.F4 Ω := canonicalRep (coxeterSystem Tag.F4) Ω v
  have hnRange : MonoidHom.range (conjIMB2 Ω n) =
      rootSpan Tag.F4 Ω (componentRoots χ i) := by
    rw [CFSG.StandardType.F4ExplicitPos.RationalB2.range_conjIMB2 Ω n,
      CFSG.RankThree.PartOne.KE.map_conj_rootSpan (L := Ω) v hS, ← hΨ]
  have hn : bcGL (τ := Tag.F4) σ.toRingHom n = n :=
    CFSG.StandardType.F4ExplicitPos.PinnedBaseChange.bcGL_canonicalRep (τ := Tag.F4) σ.toRingHom
      (coxeterSystem Tag.F4) v
  have hn_adj : n ∈ adjointGroup Tag.F4 Ω :=
    CFSG.LieType.Chevalley.canonicalRep_mem_adjointGroup (coxeterSystem Tag.F4) Ω v
  have hz_adj : z ∈ adjointGroup Tag.F4 Ω := Zsub_le_adjointGroup χ hzZ
  have hbc : bcGL (τ := Tag.F4) σ.toRingHom = frobGL σ := by
    unfold CFSG.StandardType.F4ExplicitPos.BaseChange.bcGL
    rw [CFSG.StandardType.F4ExplicitPos.BaseChange.bcEndHom_eq_entrywiseHom]
  have hzH : ∀ g, g ∈ MonoidHom.range (conjIMB2 Ω n) ↔
      z * g * z⁻¹ ∈ MonoidHom.range (conjIMB2 Ω n) := by
    intro g
    rw [hnRange]
    exact normalizesAll_apply hnorm i g
  have hzF : ∀ g ∈ MonoidHom.range (conjIMB2 Ω n),
      D.step (z * g * z⁻¹) = z * bcGL (τ := Tag.F4) σ.toRingHom g * z⁻¹ := by
    intro g hg
    rw [hnRange] at hg
    rw [hbc]
    exact hgoal g hg
  let κ : StatedSp 2 k →* ModGL Tag.F4 Ω :=
    ((MulAut.conj z).toMonoidHom.comp (conjIMB2 Ω n)).comp
      (statedSpMap (algebraMap k Ω) 2)
  have hκrange : κ.range = rootSpan Tag.F4 Ω (componentRoots χ i) ⊓ D.model := by
    change MonoidHom.range (((MulAut.conj z).toMonoidHom.comp (conjIMB2 Ω n)).comp
        (statedSpMap (algebraMap k Ω) 2)) = _
    rw [CFSG.StandardType.F4ExplicitPos.RationalB2.range_PhiB2_eq_inf_model Ω D σ.toRingHom hσ n z
      hn_adj hz_adj hn hzH hzF, hnRange]
  have hκinj : Function.Injective κ := by
    change Function.Injective (((MulAut.conj z).toMonoidHom.comp (conjIMB2 Ω n)).comp
      (statedSpMap (algebraMap k Ω) 2))
    exact CFSG.StandardType.F4ExplicitPos.RationalB2.PhiB2_injective Ω n z
  have hPleΓ : P ≤ D.Γ := hP.1.trans inf_le_left
  have hPleM : P ≤ D.model := hPleΓ.trans (Subgroup.commutator_le_self D.model)
  have hPleN : P ≤ κ.range := by
    rw [hκrange]; exact le_inf hPleH hPleM
  by_cases hf1 : f = 1
  ·
    have hk2 : Nat.card k = 2 := by rw [hk, hf1]; norm_num
    have hNleC : κ.range ≤ D.Γ ⊓ Ccent :=
      CFSG.StandardType.F4ExplicitPos.ActualPerfect.fixed_range_le_component_ambient
        (Γ := D.Γ) (M := D.model) (H := rootSpan Tag.F4 Ω (componentRoots χ i))
        (Ccent := Ccent) (N := κ.range) hΓ hHcent hκrange
    have hNleM : κ.range ≤ D.model := by rw [hκrange]; exact inf_le_right
    exact (CFSG.StandardType.F4ExplicitPos.B2SmallJ.false_of_component_le_fixed_sp4_two
      (X := ModGL Tag.F4 Ω) (J := J) (k := k) hk2 κ ηJ
      (model := D.model) (C := D.Γ ⊓ Ccent) (N := κ.range) (P := P)
      hκinj rfl hNleM hNleC hP hPleN hηinj hηrange h28).elim
  ·
    have hf2 : 2 ≤ f := by
      by_contra h
      have h_eq : f = 1 := by omega
      exact hf1 h_eq
    have h4 : 4 ≤ Nat.card k := by
      rw [hk]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
    have hNq : CFSG.IsQuasisimple ↥κ.range := by
      change CFSG.IsQuasisimple ↥(MonoidHom.range
        (((MulAut.conj z).toMonoidHom.comp (conjIMB2 Ω n)).comp
          (statedSpMap (algebraMap k Ω) 2)))
      exact CFSG.StandardType.F4ExplicitPos.RationalB2.isQuasisimple_range_PhiB2 Ω n z h4
    have hNleM : κ.range ≤ D.model := by rw [hκrange]; exact inf_le_right
    have hNleH : κ.range ≤ rootSpan Tag.F4 Ω (componentRoots χ i) := by
      rw [hκrange]; exact inf_le_left
    have hNΓ : κ.range ≤ D.Γ := by
      have : Group.IsPerfect ↥κ.range := hNq.1
      calc κ.range = ⁅κ.range, κ.range⁆ := Subgroup.commutator_eq_self.symm
        _ ≤ ⁅D.model, D.model⁆ := Subgroup.commutator_mono hNleM hNleM
        _ = D.Γ := rfl
    have hNleC : κ.range ≤ D.Γ ⊓ Ccent := le_inf hNΓ (hNleH.trans hHcent)
    have hPN : P = κ.range :=
      RationalC3Attach.eq_of_isComponentOf_of_fixed_quasisimple_of_le_actual
        (C := D.Γ ⊓ Ccent) (M := D.model) (Γ := D.Γ)
        (H := rootSpan Tag.F4 Ω (componentRoots χ i)) (N := κ.range) (K := P)
        hκrange (Subgroup.commutator_le_self D.model) hNleC hNq hP hPleH hPleΓ hP.2.2
    refine CFSG.StandardType.F4ExplicitPos.InnerSelectedPair.inner_selected_pair_output_exists
      (k := k) (Jbar := P) (H := rootSpan Tag.F4 Ω (componentRoots χ i))
      D hzZ rfl ?_ hσ ?_ ?_
    · intro g
      exact normalizesAll_apply hnorm i g
    · exact hgoal
    · exact hPN.trans hκrange

theorem f4_b2_selected_pair_output
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharP Ω 2]
    [Algebra (ZMod 2) Ω] [Algebra.IsAlgebraic (ZMod 2) Ω]
    {k : Type} [Field k] [Finite k] [CharP k 2] [Algebra k Ω]
    (D : LangDatum Tag.F4 Ω) (f : ℕ) (hf : 1 ≤ f) (hq : D.q = 2 ^ f)
    (hk : Nat.card k = 2 ^ f)
    {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin Tag.F4.rank → ℤ) →* M}
    (ρ : Equiv.Perm (Fin Tag.F4.rank → ℤ)) (hρ : FrobRootMap D ρ)
    (i : KernelComponent χ)
    (hker : ∀ α ∈ kernelRoots χ, ρ α ∈ kernelRoots χ)
    (hstable : (fun α => ρ α) '' componentRoots χ i = componentRoots χ i)
    (v : WeylGroup Tag.F4)
    (hΨ : componentRoots χ i = (fun α => v • α) '' b2LeviRoots)
    {Ccent : Subgroup (ModGL Tag.F4 Ω)} {P : Subgroup (ModGL Tag.F4 Ω)}
    (hP : CFSG.Assembly.IsComponentOf P (D.Γ ⊓ Ccent))
    (hPleH : P ≤ rootSpan Tag.F4 Ω (componentRoots χ i))
    (hHcent : rootSpan Tag.F4 Ω (componentRoots χ i) ≤ Ccent)
    (hΓ : D.Γ = D.model)
    {J : Type*} [Group J] (ηJ : J →* ModGL Tag.F4 Ω)
    (hηinj : Function.Injective ηJ) (hηrange : ηJ.range = P)
    (h28 : IsEmpty (J ≃* alternatingGroup (Fin 6))) :
    SelectedPairOutput (k := k) D χ P i :=
  f4_b2_selected_pair_output_of_hinner (k := k) D f hf hq hk ρ hρ i hker
    (CFSG.StandardType.F4ExplicitPos.B2Inner.b2_component_rho_twistInner
      (D := D) (ρ := ρ) hρ i hΨ hstable)
    v hΨ hP hPleH hHcent hΓ ηJ hηinj hηrange h28

end CFSG.StandardType.F4ExplicitPos.B2SelectedPair

end

end
