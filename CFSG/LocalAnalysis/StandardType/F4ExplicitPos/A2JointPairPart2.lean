module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.A2JointPairPart1

@[expose] public section

public noncomputable section

namespace CFSG.StandardType.F4ExplicitPos.A2JointPair
open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType
  CFSG.LieType.Chevalley CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.StandardType.F4ExplicitPos.RationalA2Finish
open CFSG.StandardType.F4ExplicitPos.RationalA2
open CFSG.StandardType.F4ExplicitPos.NativePinFinal
open CFSG.StandardType.F4ExplicitPos.SelectedPair
open CFSG.StandardType.F4ExplicitPos.UnitaryPair
open CFSG.RankThree.Classical2
open scoped Matrix MatrixGroups

theorem a2_unitary_selected_pair_output
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharP Ω 2]
    {k : Type} [Field k] [Algebra k Ω] [IsAlgClosure k Ω]
    {f : ℕ} (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (D : LangDatum Tag.F4 Ω) (hq : D.q = 2 ^ f)
    (hstep_inj : Function.Injective D.step)
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin Tag.F4.rank → ℤ) →* M}
    (i : KernelComponent χ)
    (Jbar : Subgroup (ModGL Tag.F4 Ω))
    (ρ : SL(3, Ω) →* ModGL Tag.F4 Ω) (r : Fin 3 → Fin 3 → Fin Tag.F4.rank → ℤ)
    (hframe : IsSLFrame ρ r) (hρinj : Function.Injective ρ)
    (hframe_eq : frameRoots r = componentRoots χ i)
    (ρperm : Equiv.Perm (Fin Tag.F4.rank → ℤ)) (hρperm : FrobRootMap D ρperm)
    (_hstable : (ρperm : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ)) ''
        componentRoots χ i = componentRoots χ i)
    (π : Equiv.Perm (Fin 3))
    (hunitary : ∀ a b : Fin 3, a ≠ b → ρperm (r a b) = r (π b) (π a))
    {Ccent : Subgroup (ModGL Tag.F4 Ω)}
    (hCcent : ρ.range ≤ Ccent)
    (hJbar : CFSG.Assembly.IsComponentOf Jbar (D.Γ ⊓ Ccent))
    (hJbar_le : Jbar ≤ ρ.range) :
    SelectedPairOutput (k := k) D χ Jbar i := by
  classical
  have hρrange : ρ.range = rootSpan Tag.F4 Ω (componentRoots χ i) := by
    rw [hframe.range, hframe_eq]
  obtain ⟨ρ₀, hρeq, hρ₀par⟩ := step_pinnedX_F4_perm (Ω := Ω) D ρperm hρperm
  let σ : Ω ≃+* Ω := iterateFrobeniusEquiv Ω 2 f
  have hσc : ∀ c : Ω, σ c = c ^ 2 ^ f := fun c => iterateFrobeniusEquiv_def Ω 2 f c
  have hσq : ∀ c : Ω, σ c = c ^ D.q := by intro c; rw [hσc, hq]
  have hρ₀unitary : ∀ a b : Fin 3, a ≠ b → ρ₀ (r a b) = r (π b) (π a) := by
    intro a b hab
    exact (hρeq (r a b) (hframe.isRoot a b hab)).symm.trans (hunitary a b hab)
  have hΨ : ∀ a b : Fin 3, a ≠ b → ∃ bu : Ωˣ, ∀ c : Ω,
      D.step (pinnedX Tag.F4 Ω (r a b) c) =
        pinnedX Tag.F4 Ω (r (π b) (π a)) ((bu : Ω) * σ c) := by
    intro a b hab
    obtain ⟨μ, hμ0, hμ⟩ := hρ₀par (r a b) (hframe.isRoot a b hab)
    refine ⟨Units.mk0 μ hμ0, fun c => ?_⟩
    rw [hμ c, hρ₀unitary a b hab]
    congr 2
    rw [hσq]
  obtain ⟨Φ', hΦ', bu, hshape⟩ :=
    inducedAut_unitary (τ := Tag.F4) (L := Ω) hframe hρinj σ.toRingHom σ.bijective D.step
      hstep_inj π hΨ
  have hΦ'' : ∀ (a b : Fin 3) (hab : a ≠ b) (t : Ω),
      ((Φ' (Matrix.SpecialLinearGroup.transvection hab t) : SL(3, Ω)) :
        Matrix (Fin 3) (Fin 3) Ω) =
        1 + Matrix.single (π b) (π a) ((bu a b : Ω) * t ^ 2 ^ f) := by
    intro a b hab t
    rw [hshape a b hab t, show σ.toRingHom t = t ^ 2 ^ f from hσc t]
  obtain ⟨H, hfullGL, hfix⟩ :=
    unitary_full_intertwining (ℓ := 2) (f := f) (k := k) (Ω := Ω) Nat.prime_two hf hk
      (n := 3) (by norm_num) σ.toRingHom hσc π Φ' bu hΦ''
  have hfull : ∀ X : SL(3, Ω), Φ' (H * X * H⁻¹) = H * stdUnitary σ.toRingHom X * H⁻¹ :=
    unitary_full_intertwining_stdUnitary σ H Φ' hfullGL
  obtain ⟨F, μ, hF, hFcard, -, -, hallPlus, hallMinus, hmemPlus, hmemMinus⟩ :=
    exists_unitary_opposite_pair (Ω := Ω) hf σ hσc
  have hNdef : (kappaSU ρ H F 2 f).range = ρ.range ⊓ D.model := by
    rw [kappaSU_range (ρ := ρ) (H := H) F (ℓ := 2) (f := f) Nat.prime_two hF hFcard hρinj
      D.step Φ' hΦ' hfix, LangDatum.model, ← inf_assoc,
      inf_eq_left.mpr hframe.range_le_adjointGroup]
  have hrootPlus : ∃ ε02 : Ωˣ, ∀ t : Ω,
      ρ (xPlus t) = pinnedX Tag.F4 Ω (r 0 2) ((ε02 : Ω) * t) := by
    obtain ⟨ε, hε⟩ := hframe.transv 0 2 (by decide)
    exact ⟨ε, fun t => by rw [xPlus_eq_transvection]; exact hε t⟩
  have hrootMinus : ∃ ε20 : Ωˣ, ∀ t : Ω,
      ρ (xMinus t) = pinnedX Tag.F4 Ω (r 2 0) ((ε20 : Ω) * t) := by
    obtain ⟨ε, hε⟩ := hframe.transv 2 0 (by decide)
    exact ⟨ε, fun t => by rw [xMinus_eq_transvection]; exact hε t⟩
  obtain ⟨ε02, hε02⟩ := hrootPlus
  obtain ⟨ε20, hε20⟩ := hrootMinus
  have hα : r 0 2 ∈ componentRoots χ i := by
    rw [← hframe_eq]
    exact ⟨0, 2, by decide, rfl⟩
  have hα20 : r 2 0 = -(r 0 2) := hframe.neg 0 2
  have hwD : ρ (H * P μ) ∈ Zsub χ :=
    (mem_Zsub_iff χ (ρ (H * P μ))).mpr
      (Subgroup.mem_sup_right
        (rootSpan_mono (fun γ hγ => mem_kernelRoots_of_mem_componentRoots (L := Ω) hγ)
          (by rw [← hρrange]; exact ⟨H * P μ, rfl⟩)))
  have hstab := frame_conj_rootSubgroup_step_stable_unitary (Ω := Ω) D ρ r H (P μ) σ Φ' hΦ' hfull
    0 2 (by decide) (xs := xPlus) ε02 hε02 hallPlus
  have hstabm := frame_conj_rootSubgroup_step_stable_unitary (Ω := Ω) D ρ r H (P μ) σ Φ' hΦ' hfull
    2 0 (by decide) (xs := xMinus) ε20 hε20 hallMinus
  have hJbar_eq : (kappaSU ρ H F 2 f).range = Jbar := by
    by_cases hf2 : 2 ≤ f
    · have hNq : CFSG.IsQuasisimple ↥(kappaSU ρ H F 2 f).range :=
        isQuasisimple_kappaSU_range (f := f) hf2 hFcard ρ H hρinj
      exact (component_eq_of_isComponentOf_of_fixed_quasisimple_of_perfect
        (C := D.Γ ⊓ Ccent) (Ccent := Ccent) (M := D.model) (Γ := D.Γ)
        (H := ρ.range) (N := (kappaSU ρ H F 2 f).range) (K := Jbar)
        rfl rfl hNdef hNq.1 hCcent hNq hJbar hJbar_le hJbar.2.2).symm
    · exfalso
      have hf1 : f = 1 := by omega
      have hFcard1 : Nat.card F = (2 ^ 1) ^ 2 := by
        rw [hf1] at hFcard
        exact hFcard
      have hsol : Group.IsSolvable ↥(kappaSU ρ H F 2 f).range := by
        rw [hf1]; exact isSolvable_kappaSU_range_one hFcard1 ρ H hρinj
      have hJleN : Jbar ≤ (kappaSU ρ H F 2 f).range := by
        rw [hNdef]
        exact le_inf hJbar_le
          (hJbar.1.trans (inf_le_left.trans (Subgroup.commutator_le_self D.model)))
      have hJsol : Group.IsSolvable ↥Jbar :=
        Group.isSolvable_of_isSolvable_injective
          (f := Subgroup.inclusion hJleN) (Subgroup.inclusion_injective hJleN)
      have hJq : CFSG.IsQuasisimple ↥Jbar :=
        (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native ↥Jbar).mp
          hJbar.2.2
      have : Nontrivial ↥Jbar := CFSG.LocalCores.isQuasisimple_nontrivial hJq
      have : Group.IsPerfect ↥Jbar := hJq.1
      exact Group.IsPerfect.not_isSolvable ↥Jbar hJsol
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; exact pow_ne_zero f (by norm_num))
  obtain ⟨ε02', ε20', hP, hPm⟩ :=
    kappaSU_pair_all_rootRange_le (Ω := Ω) (f := f) hk ρ H ⟨ε02, hε02⟩ ⟨ε20, hε20⟩ F μ
      hmemPlus hmemMinus
  refine selectedPairOutput_of_curves (k := k) D hα hwD ε02' ε20' ?_ ?_ ?_ ?_ ?_ ?_
  · rw [← hJbar_eq]; exact hP
  · rw [← hJbar_eq, ← hα20]; exact hPm
  · exact conjugatedRootRange_card (k := k) (ρ (H * P μ)) (r 0 2) ε02'
  · exact conjugatedRootRange_card (k := k) (ρ (H * P μ)) (-(r 0 2)) ε20'
  · exact hstab
  · simpa only [hα20] using hstabm

end CFSG.StandardType.F4ExplicitPos.A2JointPair

end

end
