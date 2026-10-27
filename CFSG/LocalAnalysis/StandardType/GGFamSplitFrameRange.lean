module

public import CFSG.LocalAnalysis.StandardType.GGFamTypeAFrames
public import CFSG.LocalAnalysis.StandardType.GGFamInnerCover
public import CFSG.LocalAnalysis.StandardType.GGFamTameRange
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TypeASplit
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TypeASplitConj

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.LieType.Steinberg.Adjoint
  CFSG.ClassicalInvolution.WeakCT CFSG.Timmesfeld CFSG.Assembly.LowTwoRank
  CFSG.RankThree.Classical2
open scoped MatrixGroups commutatorElement

theorem fam_split_exists_hom
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀)
    {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} (hρ : ∀ γ ∈ kernelRoots χ, S.ρ γ ∈ kernelRoots χ)
    (i : KernelComponent χ) {ν : ℕ} (hν : 3 ≤ ν)
    {ψ : SL(ν, L) →* ModGL τ L} {σ : Fin ν → Fin ν → Fin τ.rank → ℤ} (hψ : IsSLFrame ψ σ)
    (hΨ : componentRoots χ i = frameRoots σ) (π : Equiv.Perm (Fin ν))
    (hπ : ∀ a b, a ≠ b → (S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
      (componentRoots χ i)] (σ a b) = σ (π a) (π b))
    {r e : ℕ} (hr : r.Prime) (hchar : CharP L r) (he : 0 < e) (hq : S.D.q = r ^ e) :
    ∃ σQ : L ≃+* L,
      (∀ c, σQ c = c ^ (r ^ (e * componentOrbitLength S.ρ (componentRoots χ i)))) ∧
      ∃ f : SL(ν, ↥(fixSubfield σQ)) →* ModGL τ L,
        rationalComponentM S.ρ S.Γ χ i ≤ f.range ∧
        f.ker ≤ Subgroup.center SL(ν, ↥(fixSubfield σQ)) ∧
        (Group.IsPerfect SL(ν, ↥(fixSubfield σQ)) →
          f.range ≤ rationalComponentM S.ρ S.Γ χ i) := by
  classical
  obtain ⟨hs0, hs, hmin⟩ := fam_componentOrbitLength_spec S hρ i
  set s := componentOrbitLength S.ρ (componentRoots χ i) with hsdef
  haveI : NeZero s := ⟨hs0.ne'⟩
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : CharP L r := hchar
  obtain ⟨σQ, hσQ⟩ := exists_ringEquiv_frob (L := L) r (e * s)
  have hσc : ∀ c, σQ c = c ^ (r ^ (e * s)) := fun c => by
    have h1 : σQ c = iterateFrobenius L r (e * s) c := by
      rw [← hσQ]
      rfl
    rw [h1, iterateFrobenius_def]
  set Fs : ModGL τ L →* ModGL τ L := iterHom S.D.step s with hFs
  set P := famOrbitFamily S hρ i hs hmin with hP
  have hP0 : P.S 0 = rootSpan τ L (componentRoots χ i) := by
    rw [hP, famOrbitFamily_S, ZMod.val_zero]
    simp only [Function.iterate_zero, id_eq, Set.image_id']
  obtain ⟨B, hstd⟩ := split_exists_pin S hν hψ π hπ hq hσc
  choose! ε hε using fun (a b : Fin ν) (hab : a ≠ b) => hψ.transv a b hab
  have hψS : ∀ X, ψ X ∈ rootSpan τ L (componentRoots χ i) := fun X => by
    rw [hΨ, ← hψ.range]
    exact ⟨X, rfl⟩
  have hy₁ : ψ B ∈ rootSpan τ L (kernelRoots χ) :=
    rootSpan_mono (fun γ hγ => hγ.1) (hψS B)
  obtain ⟨z, hz, hnorm⟩ := fam_exists_lang S hρ (s := s) hs0 (Subgroup.mem_sup_right hy₁)
  have hconj : ∀ X : SL(ν, L), Fs (z * ψ X * z⁻¹) =
      z * ψ (Matrix.SpecialLinearGroup.map σQ.toRingHom X) * z⁻¹ := by
    intro X
    rw [← hstd X, map_mul, map_mul, map_inv, hz, hFs]
    group
  have hzA : ∀ y ∈ P.A, z * y * z⁻¹ ∈ P.A := by
    have h : P.A ≤ P.A.comap (MulAut.conj z).toMonoidHom := by
      refine iSup_le fun k => ?_
      obtain ⟨j, hj⟩ := fam_iterate_image_component S hρ i k.val
      intro g hg
      have hg' : g ∈ rootSpan τ L (componentRoots χ j) := by rw [hj]; exact hg
      have h2 := (hnorm j g).1 hg'
      rw [hj] at h2
      exact P.S_le_A k h2
    exact fun y hy => h hy
  have hZconj : ∀ x : ModGL τ L, z * x * z⁻¹ ∈ P.Z → x ∈ P.Z := by
    intro x hx
    rw [CycFamily.mem_Z] at hx ⊢
    intro y hy
    have := hx _ (hzA y hy)
    have e1 : z * y * z⁻¹ * (z * x * z⁻¹) = z * (y * x) * z⁻¹ := by group
    have e2 : z * x * z⁻¹ * (z * y * z⁻¹) = z * (x * y) * z⁻¹ := by group
    rw [e1, e2] at this
    simpa using this
  have hker : ψ.ker ≠ ⊤ := by
    intro h
    have h01 : (⟨0, by omega⟩ : Fin ν) ≠ ⟨1, by omega⟩ := by simp
    have h1 : Matrix.SpecialLinearGroup.transvection h01 (1 : L) ∈ ψ.ker := by
      rw [h]
      exact Subgroup.mem_top _
    rw [MonoidHom.mem_ker, hε _ _ h01, mul_one, ← pinnedX_zero τ L (σ _ _)] at h1
    exact Units.ne_zero _ (pinnedX_injective τ L _ h1)
  have hcentral : ∀ X : SL(ν, L), ψ X ∈ P.Z → X ∈ Subgroup.center SL(ν, L) := by
    intro X hX
    refine mem_center_SL_of_commute hν ψ hker fun Y => ?_
    have hYA : ψ Y ∈ P.A := P.S_le_A 0 (by rw [hP0]; exact hψS Y)
    exact ((CycFamily.mem_Z P).1 hX (ψ Y) hYA).symm
  set K : Subfield L := fixSubfield σQ with hKdef
  let ι : SL(ν, ↥K) →* SL(ν, L) := Matrix.SpecialLinearGroup.map K.subtype
  have hιinj : Function.Injective ι := specialLinearGroup_map_injective K.subtype_injective
  have hσι : ∀ c : SL(ν, ↥K), Matrix.SpecialLinearGroup.map σQ.toRingHom (ι c) = ι c := by
    intro c
    ext i j
    simp only [ι, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    exact (mem_fixSubfield σQ).1 (c i j).2
  have hιrange : ∀ Y : SL(ν, L), Matrix.SpecialLinearGroup.map σQ.toRingHom Y = Y →
      ∃ c : SL(ν, ↥K), ι c = Y := by
    intro Y hY
    refine exists_map_eq_of_forall_mem_range K.subtype_injective Y fun i j => ?_
    have := congrArg (fun Z : SL(ν, L) => (Z : Matrix (Fin ν) (Fin ν) L) i j) hY
    simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom] at this
    exact ⟨⟨_, (mem_fixSubfield σQ).2 this⟩, rfl⟩
  let θ : SL(ν, ↥K) →* ModGL τ L := (MulAut.conj z).toMonoidHom.comp (ψ.comp ι)
  have hθ : ∀ c : SL(ν, ↥K), θ c = z * ψ (ι c) * z⁻¹ := fun c => rfl
  have hθS : ∀ c : SL(ν, ↥K), θ c ∈ rootSpan τ L (componentRoots χ i) := fun c => by
    rw [hθ]
    exact (hnorm i _).1 (hψS _)
  have hθfix : ∀ c : SL(ν, ↥K), Fs (θ c) = θ c := fun c => by
    rw [hθ, hconj, hσι]
  have hpre : ∀ g ∈ rootSpan τ L (componentRoots χ i),
      ∃ X : SL(ν, L), g = z * ψ X * z⁻¹ := by
    intro g hg
    have h1 : z⁻¹ * g * z ∈ rootSpan τ L (componentRoots χ i) := (hnorm i _).2 (by
      have e : z * (z⁻¹ * g * z) * z⁻¹ = g := by group
      rw [e]
      exact hg)
    rw [hΨ, ← hψ.range] at h1
    obtain ⟨X, hX⟩ := h1
    exact ⟨X, by rw [hX]; group⟩
  have hfixmod : ∀ X : SL(ν, L), Fs (z * ψ X * z⁻¹) * (z * ψ X * z⁻¹)⁻¹ ∈ P.Z →
      Matrix.SpecialLinearGroup.map σQ.toRingHom X * X⁻¹ ∈ Subgroup.center SL(ν, L) := by
    intro X hX
    have e : Fs (z * ψ X * z⁻¹) * (z * ψ X * z⁻¹)⁻¹ =
        z * ψ (Matrix.SpecialLinearGroup.map σQ.toRingHom X * X⁻¹) * z⁻¹ := by
      rw [hconj, map_mul, map_inv]
      group
    rw [e] at hX
    exact hcentral _ (hZconj _ hX)
  have hθY : ∀ g g' : ModGL τ L, g ∈ rootSpan τ L (componentRoots χ i) →
      g' ∈ rootSpan τ L (componentRoots χ i) → Fs g * g⁻¹ ∈ P.Z →
        Fs g' * g'⁻¹ ∈ P.Z → ⁅g, g'⁆ ∈ θ.range := by
    intro g g' hg hg' hgZ hg'Z
    obtain ⟨X, rfl⟩ := hpre g hg
    obtain ⟨X', rfl⟩ := hpre g' hg'
    have hc := hfixmod X hgZ
    have hc' := hfixmod X' hg'Z
    set c := Matrix.SpecialLinearGroup.map σQ.toRingHom X * X⁻¹ with hcdef
    set c' := Matrix.SpecialLinearGroup.map σQ.toRingHom X' * X'⁻¹ with hc'def
    have hX : Matrix.SpecialLinearGroup.map σQ.toRingHom X = c * X := by
      rw [hcdef, inv_mul_cancel_right]
    have hX' : Matrix.SpecialLinearGroup.map σQ.toRingHom X' = c' * X' := by
      rw [hc'def, inv_mul_cancel_right]
    have hcomm : ∀ (w : SL(ν, L)) (hw : w ∈ Subgroup.center SL(ν, L)) (y : SL(ν, L)),
        Commute w y := fun w hw y => (Subgroup.mem_center_iff.1 hw y).symm
    have hfixc : Matrix.SpecialLinearGroup.map σQ.toRingHom ⁅X, X'⁆ = ⁅X, X'⁆ := by
      rw [map_commutatorElement, hX, hX']
      exact CycFamily.commutatorElement_central_mul (hcomm c hc X) (hcomm c hc X')
        (hcomm c hc c') (hcomm c' hc' X) (hcomm c' hc' X')
    obtain ⟨c₀, hc₀⟩ := hιrange _ hfixc
    refine ⟨c₀, ?_⟩
    rw [hθ, hc₀]
    simp only [commutatorElement_def, map_mul, map_inv]
    group
  have hθZ : ∀ c : SL(ν, ↥K), θ c ∈ P.Z → c ∈ Subgroup.center SL(ν, ↥K) := by
    intro c hc
    rw [hθ] at hc
    have h := hcentral _ (hZconj _ hc)
    rw [Subgroup.mem_center_iff]
    intro c2
    apply hιinj
    rw [map_mul, map_mul]
    exact Subgroup.mem_center_iff.1 h (ι c2)
  obtain ⟨f, hf1, hfker, hf2⟩ :=
    fam_rationalComponent_eq_range_of_hom S hρ i hs hmin θ hθS hθfix hθY hθZ
  exact ⟨σQ, hσc, f, hf1, hfker, hf2⟩

end CFSG.StandardType.TableCRes
