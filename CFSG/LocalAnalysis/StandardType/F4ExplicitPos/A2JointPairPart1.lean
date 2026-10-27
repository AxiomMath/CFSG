module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.NativePinFinalPart2
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.RationalA2FinishPart2
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.SelectedPair

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

theorem frame_conj_rootSubgroup_step_stable
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharP Ω 2]
    (D : LangDatum Tag.F4 Ω)
    (ρ : SL(3, Ω) →* ModGL Tag.F4 Ω) (r : Fin 3 → Fin 3 → Fin Tag.F4.rank → ℤ)
    (hframe : IsSLFrame ρ r) (H : SL(3, Ω))
    (σ : Ω ≃+* Ω) (Φ' : SL(3, Ω) ≃* SL(3, Ω))
    (hΦ' : ∀ X, D.step (ρ X) = ρ (Φ' X))
    (hfull : ∀ X, Φ' (H * X * H⁻¹) = H * Matrix.SpecialLinearGroup.map σ X * H⁻¹)
    (a b : Fin 3) (hab : a ≠ b) :
    ((rootSubgroup Tag.F4 Ω (r a b)).map (MulAut.conj (ρ H)).toMonoidHom).map D.step =
      (rootSubgroup Tag.F4 Ω (r a b)).map (MulAut.conj (ρ H)).toMonoidHom := by
  obtain ⟨ε, hε⟩ := hframe.transv a b hab
  have hframeU : ∀ c : Ω, pinnedX Tag.F4 Ω (r a b) c =
      ρ (Matrix.SpecialLinearGroup.transvection hab ((ε⁻¹ : Ωˣ) * c)) := by
    intro c
    rw [hε, ← mul_assoc, Units.mul_inv, one_mul]
  have hφinv : ∀ c : Ω,
      (ε : Ω) * σ ((ε⁻¹ : Ωˣ) * ((ε : Ω) * σ.symm ((ε⁻¹ : Ωˣ) * c))) = c := by
    intro c
    rw [map_mul, map_mul, σ.apply_symm_apply]
    rw [show σ ((ε⁻¹ : Ωˣ) : Ω) = (σ ((ε : Ωˣ) : Ω))⁻¹ by
      rw [Units.val_inv_eq_inv_val, map_inv₀]]
    field_simp
    rw [Units.val_inv_eq_inv_val, mul_inv_cancel₀ (Units.ne_zero ε), one_mul]
  have hstep_formula : ∀ c : Ω,
      D.step ((MulAut.conj (ρ H)).toMonoidHom (pinnedX Tag.F4 Ω (r a b) c)) =
        (MulAut.conj (ρ H)).toMonoidHom
          (pinnedX Tag.F4 Ω (r a b) ((ε : Ω) * σ ((ε⁻¹ : Ωˣ) * c))) := by
    intro c
    calc D.step ((MulAut.conj (ρ H)).toMonoidHom (pinnedX Tag.F4 Ω (r a b) c))
        = D.step ((MulAut.conj (ρ H)).toMonoidHom
            (ρ (Matrix.SpecialLinearGroup.transvection hab ((ε⁻¹ : Ωˣ) * c)))) := by
              rw [hframeU c]
      _ = D.step (ρ (H * Matrix.SpecialLinearGroup.transvection hab ((ε⁻¹ : Ωˣ) * c) * H⁻¹)) := by
              simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]
      _ = ρ (Φ' (H * Matrix.SpecialLinearGroup.transvection hab ((ε⁻¹ : Ωˣ) * c) * H⁻¹)) := by
              rw [hΦ']
      _ = ρ (H * Matrix.SpecialLinearGroup.map σ
            (Matrix.SpecialLinearGroup.transvection hab ((ε⁻¹ : Ωˣ) * c)) * H⁻¹) := by
              rw [hfull]
      _ = ρ (H * Matrix.SpecialLinearGroup.transvection hab (σ ((ε⁻¹ : Ωˣ) * c)) * H⁻¹) := by
              simp only [Matrix.SpecialLinearGroup.map_transvection]
              rfl
      _ = ρ H * ρ (Matrix.SpecialLinearGroup.transvection hab (σ ((ε⁻¹ : Ωˣ) * c))) *
            (ρ H)⁻¹ := by simp only [map_mul, map_inv]
      _ = (MulAut.conj (ρ H)).toMonoidHom
            (pinnedX Tag.F4 Ω (r a b) ((ε : Ω) * σ ((ε⁻¹ : Ωˣ) * c))) := by
              rw [hε]
              simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  apply le_antisymm
  · rintro y ⟨x, ⟨z, hz, rfl⟩, rfl⟩
    obtain ⟨c, rfl⟩ := (mem_rootSubgroup).mp hz
    rw [hstep_formula c]
    exact Subgroup.mem_map.mpr ⟨pinnedX Tag.F4 Ω (r a b) ((ε : Ω) * σ ((ε⁻¹ : Ωˣ) * c)),
      mem_rootSubgroup.mpr ⟨_, rfl⟩, rfl⟩
  · rintro y ⟨z, hz, rfl⟩
    obtain ⟨c, rfl⟩ := (mem_rootSubgroup).mp hz
    refine ⟨(MulAut.conj (ρ H)).toMonoidHom
        (pinnedX Tag.F4 Ω (r a b) ((ε : Ω) * σ.symm ((ε⁻¹ : Ωˣ) * c))), ?_, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨pinnedX Tag.F4 Ω (r a b) ((ε : Ω) * σ.symm ((ε⁻¹ : Ωˣ) * c)),
        mem_rootSubgroup.mpr ⟨_, rfl⟩, rfl⟩
    · rw [hstep_formula ((ε : Ω) * σ.symm ((ε⁻¹ : Ωˣ) * c)), hφinv]

theorem a2_split_selected_pair_output
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
    (hsplit : ∀ a b : Fin 3, a ≠ b → ρperm (r a b) = r (π a) (π b))
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
  have hρ₀split : ∀ a b : Fin 3, a ≠ b → ρ₀ (r a b) = r (π a) (π b) := by
    intro a b hab
    exact (hρeq (r a b) (hframe.isRoot a b hab)).symm.trans (hsplit a b hab)
  have hΨ : ∀ a b : Fin 3, a ≠ b → ∃ bu : Ωˣ, ∀ c : Ω,
      D.step (pinnedX Tag.F4 Ω (r a b) c) =
        pinnedX Tag.F4 Ω (r (π a) (π b)) ((bu : Ω) * σ c) := by
    intro a b hab
    obtain ⟨μ, hμ0, hμ⟩ := hρ₀par (r a b) (hframe.isRoot a b hab)
    refine ⟨Units.mk0 μ hμ0, fun c => ?_⟩
    rw [hμ c, hρ₀split a b hab]
    congr 2
    rw [hσq]
  obtain ⟨Φ', hΦ', bu, hshape⟩ :=
    inducedAut_split (τ := Tag.F4) (L := Ω) hframe hρinj σ.toRingHom σ.bijective D.step
      hstep_inj π hΨ
  have hΦ'' : ∀ (a b : Fin 3) (hab : a ≠ b) (t : Ω),
      ((Φ' (Matrix.SpecialLinearGroup.transvection hab t) : SL(3, Ω)) :
        Matrix (Fin 3) (Fin 3) Ω) =
        1 + Matrix.single (π a) (π b) ((bu a b : Ω) * t ^ 2 ^ f) := by
    intro a b hab t
    rw [hshape a b hab t, show σ.toRingHom t = t ^ 2 ^ f from hσc t]
  obtain ⟨H, hfull, hfix⟩ :=
    split_full_intertwining (ℓ := 2) (f := f) (k := k) (Ω := Ω) Nat.prime_two hf hk
      (n := 3) (by norm_num) σ.toRingHom hσc π Φ' bu hΦ''
  have hNdef : (kappaSL (k := k) ρ H).range = ρ.range ⊓ D.model := by
    rw [kappaSL_range (ρ := ρ) (H := H) D.step Φ' hρinj hΦ' hfix, LangDatum.model, ← inf_assoc,
      inf_eq_left.mpr hframe.range_le_adjointGroup]
  have hNq : CFSG.IsQuasisimple ↥(kappaSL (k := k) ρ H).range :=
    isQuasisimple_kappaSL_range (k := k) ρ H hρinj
  have hJbar_eq : (kappaSL (k := k) ρ H).range = Jbar :=
    (component_eq_of_isComponentOf_of_fixed_quasisimple_of_perfect
      (C := D.Γ ⊓ Ccent) (Ccent := Ccent) (M := D.model) (Γ := D.Γ)
      (H := ρ.range) (N := (kappaSL (k := k) ρ H).range) (K := Jbar)
      rfl rfl hNdef hNq.1 hCcent hNq hJbar hJbar_le hJbar.2.2).symm
  obtain ⟨ε02, hε02⟩ := (kappaSL_pair (k := k) (ρ := ρ) (H := H) hframe.transv).1
  obtain ⟨ε20, hε20⟩ := (kappaSL_pair (k := k) (ρ := ρ) (H := H) hframe.transv).2
  have hα : r 0 2 ∈ componentRoots χ i := by
    rw [← hframe_eq]
    exact ⟨0, 2, by decide, rfl⟩
  have hα20 : r 2 0 = -(r 0 2) := hframe.neg 0 2
  have hP : conjugatedRootRange (k := k) (ρ H) (r 0 2) ε02 ≤ Jbar := by
    rw [← hJbar_eq]
    intro y hy
    obtain ⟨t, rfl⟩ :=
      (mem_conjugatedRootRange_iff (k := k) (ρ H) (r 0 2) ε02 y).mp hy
    exact MonoidHom.mem_range.mpr
      ⟨Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) t, hε02 t⟩
  have hPm : conjugatedRootRange (k := k) (ρ H) (-(r 0 2)) ε20 ≤ Jbar := by
    rw [← hJbar_eq]
    intro y hy
    obtain ⟨t, rfl⟩ :=
      (mem_conjugatedRootRange_iff (k := k) (ρ H) (-(r 0 2)) ε20 y).mp hy
    rw [← hα20]
    exact MonoidHom.mem_range.mpr
      ⟨Matrix.SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 0 by decide) t, hε20 t⟩
  have hwD : ρ H ∈ Zsub χ :=
    (mem_Zsub_iff χ (ρ H)).mpr
      (Subgroup.mem_sup_right
        (rootSpan_mono (fun γ hγ => mem_kernelRoots_of_mem_componentRoots (L := Ω) hγ)
          (by rw [← hρrange]; exact ⟨H, rfl⟩)))
  have hstab := frame_conj_rootSubgroup_step_stable (Ω := Ω) D ρ r hframe H σ Φ' hΦ' hfull 0 2
    (by decide)
  have hstabm := frame_conj_rootSubgroup_step_stable (Ω := Ω) D ρ r hframe H σ Φ' hΦ' hfull 2 0
    (by decide)
  refine selectedPairOutput_of_curves (k := k) D hα hwD ε02 ε20 hP hPm ?_ ?_ ?_ ?_
  · exact conjugatedRootRange_card (k := k) (ρ H) (r 0 2) ε02
  · exact conjugatedRootRange_card (k := k) (ρ H) (-(r 0 2)) ε20
  · exact hstab
  · simpa only [hα20] using hstabm

theorem toGL_stdUnitary {Ω : Type} [Field Ω] (σ : Ω →+* Ω) (X : SL(3, Ω)) :
    Matrix.SpecialLinearGroup.toGL (stdUnitary σ X) =
      invTransposeHom (Matrix.GeneralLinearGroup.map σ (Matrix.SpecialLinearGroup.toGL X)) := by
  apply Units.ext
  change ((stdUnitary σ X : SL(3, Ω)) : Matrix (Fin 3) (Fin 3) Ω) =
    ((invTransposeHom (Matrix.GeneralLinearGroup.map σ (Matrix.SpecialLinearGroup.toGL X)) :
      GL (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω)
  rw [coe_stdUnitary, coe_invTransposeHom]
  have hcoe : ((Matrix.GeneralLinearGroup.map σ (Matrix.SpecialLinearGroup.toGL X) :
      GL (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω) =
      (X : Matrix (Fin 3) (Fin 3) Ω).map σ := rfl
  have hval : (↑((Matrix.GeneralLinearGroup.map σ (Matrix.SpecialLinearGroup.toGL X))⁻¹) :
      Matrix (Fin 3) (Fin 3) Ω) =
      ((↑((Matrix.GeneralLinearGroup.map σ (Matrix.SpecialLinearGroup.toGL X)) :
        Matrix (Fin 3) (Fin 3) Ω))⁻¹) :=
    Matrix.GeneralLinearGroup.coe_inv _
  rw [hval, hcoe]

theorem unitary_full_intertwining_stdUnitary {Ω : Type} [Field Ω]
    (σ : Ω ≃+* Ω) (H : SL(3, Ω)) (Φ' : SL(3, Ω) ≃* SL(3, Ω))
    (hfull : ∀ X : SL(3, Ω),
      Matrix.SpecialLinearGroup.toGL (Φ' (H * X * H⁻¹)) =
        Matrix.SpecialLinearGroup.toGL H *
          invTransposeHom (Matrix.GeneralLinearGroup.map σ.toRingHom
            (Matrix.SpecialLinearGroup.toGL X)) *
          (Matrix.SpecialLinearGroup.toGL H)⁻¹) :
    ∀ X : SL(3, Ω), Φ' (H * X * H⁻¹) = H * stdUnitary σ.toRingHom X * H⁻¹ := by
  intro X
  apply Matrix.SpecialLinearGroup.toGL_injective
  rw [hfull X, map_mul, map_mul, map_inv, toGL_stdUnitary]

theorem frame_conj_rootSubgroup_step_stable_unitary
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharP Ω 2]
    (D : LangDatum Tag.F4 Ω)
    (ρ : SL(3, Ω) →* ModGL Tag.F4 Ω) (r : Fin 3 → Fin 3 → Fin Tag.F4.rank → ℤ)
    (H Pμ : SL(3, Ω))
    (σ : Ω ≃+* Ω) (Φ' : SL(3, Ω) ≃* SL(3, Ω))
    (hΦ' : ∀ X, D.step (ρ X) = ρ (Φ' X))
    (hfull : ∀ X, Φ' (H * X * H⁻¹) = H * stdUnitary σ.toRingHom X * H⁻¹)
    (a b : Fin 3) (_hab : a ≠ b) {xs : Ω → SL(3, Ω)} (ε : Ωˣ)
    (hframeFwd : ∀ t : Ω, ρ (xs t) = pinnedX Tag.F4 Ω (r a b) ((ε : Ω) * t))
    (hall : ∀ t : Ω,
      stdUnitary σ.toRingHom (Pμ * xs t * Pμ⁻¹) = Pμ * xs (σ t) * Pμ⁻¹) :
    ((rootSubgroup Tag.F4 Ω (r a b)).map (MulAut.conj (ρ (H * Pμ))).toMonoidHom).map D.step =
      (rootSubgroup Tag.F4 Ω (r a b)).map (MulAut.conj (ρ (H * Pμ))).toMonoidHom := by
  have hframeU : ∀ c : Ω, pinnedX Tag.F4 Ω (r a b) c = ρ (xs ((ε⁻¹ : Ωˣ) * c)) := by
    intro c
    rw [hframeFwd, ← mul_assoc, Units.mul_inv, one_mul]
  have hφinv : ∀ c : Ω,
      (ε : Ω) * σ ((ε⁻¹ : Ωˣ) * ((ε : Ω) * σ.symm ((ε⁻¹ : Ωˣ) * c))) = c := by
    intro c
    rw [map_mul, map_mul, σ.apply_symm_apply]
    rw [show σ ((ε⁻¹ : Ωˣ) : Ω) = (σ ((ε : Ωˣ) : Ω))⁻¹ by
      rw [Units.val_inv_eq_inv_val, map_inv₀]]
    field_simp
    rw [Units.val_inv_eq_inv_val, mul_inv_cancel₀ (Units.ne_zero ε), one_mul]
  have hconj : ∀ t : Ω, (MulAut.conj (ρ (H * Pμ))).toMonoidHom (ρ (xs t)) =
      ρ (H * (Pμ * xs t * Pμ⁻¹) * H⁻¹) := by
    intro t
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    simp only [map_mul, map_inv]
    group
  have hstep_formula : ∀ c : Ω,
      D.step ((MulAut.conj (ρ (H * Pμ))).toMonoidHom (pinnedX Tag.F4 Ω (r a b) c)) =
        (MulAut.conj (ρ (H * Pμ))).toMonoidHom
          (pinnedX Tag.F4 Ω (r a b) ((ε : Ω) * σ ((ε⁻¹ : Ωˣ) * c))) := by
    intro c
    rw [hframeU c, hconj ((ε⁻¹ : Ωˣ) * c), hΦ', hfull, hall, ← hconj (σ ((ε⁻¹ : Ωˣ) * c)),
      hframeFwd (σ ((ε⁻¹ : Ωˣ) * c))]
  apply le_antisymm
  · rintro y ⟨x, ⟨z, hz, rfl⟩, rfl⟩
    obtain ⟨c, rfl⟩ := (mem_rootSubgroup).mp hz
    rw [hstep_formula c]
    exact Subgroup.mem_map.mpr ⟨pinnedX Tag.F4 Ω (r a b) ((ε : Ω) * σ ((ε⁻¹ : Ωˣ) * c)),
      mem_rootSubgroup.mpr ⟨_, rfl⟩, rfl⟩
  · rintro y ⟨z, hz, rfl⟩
    obtain ⟨c, rfl⟩ := (mem_rootSubgroup).mp hz
    refine ⟨(MulAut.conj (ρ (H * Pμ))).toMonoidHom
        (pinnedX Tag.F4 Ω (r a b) ((ε : Ω) * σ.symm ((ε⁻¹ : Ωˣ) * c))), ?_, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨pinnedX Tag.F4 Ω (r a b) ((ε : Ω) * σ.symm ((ε⁻¹ : Ωˣ) * c)),
        mem_rootSubgroup.mpr ⟨_, rfl⟩, rfl⟩
    · rw [hstep_formula ((ε : Ω) * σ.symm ((ε⁻¹ : Ωˣ) * c)), hφinv]

end CFSG.StandardType.F4ExplicitPos.A2JointPair
end

end
