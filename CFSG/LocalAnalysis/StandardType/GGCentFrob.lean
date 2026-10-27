module

public import CFSG.LocalAnalysis.StandardType.GGNTPlaneInput

public section

namespace CFSG.StandardType.NTPlane

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE
open scoped Matrix

private def s4rel {L : Type} [Field L] (χ : Multiplicative (Fin Tag.E6.rank → ℤ) →* Lˣ) :
    kernelRoots χ → kernelRoots χ → Prop :=
  fun α β => (α : Fin Tag.E6.rank → ℤ) ⬝ᵥ
    (Tag.E6.symmetrizedCartan *ᵥ (β : Fin Tag.E6.rank → ℤ)) ≠ 0

private theorem s4_rho_mem_kernel
    {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup .E6 L p₀) (a : Fin Tag.E6.rank → Lˣ)
    (hT : rootDiagUnit .E6 a ∈ S.D.torus)
    {α : Fin Tag.E6.rank → ℤ} (hα : α ∈ kernelRoots (rootCharHom a)) :
    S.ρ α ∈ kernelRoots (rootCharHom a) := by
  refine ⟨(S.frob.isRoot_iff α).2 hα.1, ?_⟩
  show rootChar a (S.ρ α) = 1
  rw [S.frob.rootChar_eq a hT α hα.1, show rootChar a α = 1 from hα.2, one_pow]

private theorem s4_map_rootSpan
    {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup .E6 L p₀) (Ψ : Set (Fin Tag.E6.rank → ℤ))
    (hΨ : ∀ α ∈ Ψ, IsRoot .E6 α) :
    (rootSpan .E6 L Ψ).map S.D.step = rootSpan .E6 L (S.ρ '' Ψ) := by
  calc (rootSpan .E6 L Ψ).map S.D.step
      = ⨆ α ∈ Ψ, (rootSubgroup .E6 L α).map S.D.step := by
        change (⨆ α ∈ Ψ, rootSubgroup .E6 L α).map S.D.step =
          ⨆ α ∈ Ψ, (rootSubgroup .E6 L α).map S.D.step
        rw [Subgroup.map_iSup]
        simp only [Subgroup.map_iSup]
    _ = ⨆ α ∈ Ψ, rootSubgroup .E6 L (S.ρ α) := by
        refine iSup_congr fun α => iSup_congr fun hα => ?_
        rw [S.frob.map_rootSubgroup α (hΨ α hα)]
    _ = ⨆ β ∈ S.ρ '' Ψ, rootSubgroup .E6 L β :=
        (iSup_image (f := ⇑S.ρ) (g := fun β => rootSubgroup .E6 L β) (t := Ψ)).symm
    _ = rootSpan .E6 L (S.ρ '' Ψ) := rfl

theorem ntpS4_frobPerm
    {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup .E6 L p₀)
    (a : Fin Tag.E6.rank → Lˣ) (hT : rootDiagUnit .E6 a ∈ S.D.torus) :
    ∃ ρb : Equiv.Perm (KernelComponent (rootCharHom a)),
      (∀ i, ⇑S.ρ '' componentRoots (rootCharHom a) i = componentRoots (rootCharHom a) (ρb i)) ∧
      (∀ i, (componentRootSpan L (rootCharHom a) i).map S.D.step =
        componentRootSpan L (rootCharHom a) (ρb i)) := by
  classical
  haveI : Finite (kernelRoots (rootCharHom a)) :=
    ((finite_setOf_isRoot .E6).subset fun γ hγ => hγ.1).to_subtype
  let f : kernelRoots (rootCharHom a) → kernelRoots (rootCharHom a) :=
    fun x => ⟨S.ρ x, s4_rho_mem_kernel S a hT x.2⟩
  have hf : Function.Injective f := fun x y h =>
    Subtype.ext (S.ρ.injective (Subtype.ext_iff.mp h))
  let e : kernelRoots (rootCharHom a) ≃ kernelRoots (rootCharHom a) :=
    Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf)
  have he_val : ∀ x : kernelRoots (rootCharHom a), (e x).1 = S.ρ x.1 := fun _ => rfl
  have hiff : ∀ x y : kernelRoots (rootCharHom a),
      (iform (e x).1 (e y).1 ≠ 0) ↔ (iform x.1 y.1 ≠ 0) := by
    intro x y
    rw [he_val x, he_val y, S.frob.iform_eq]
  have hdot : ∀ x y : kernelRoots (rootCharHom a),
      s4rel (rootCharHom a) (e x) (e y) ↔ s4rel (rootCharHom a) x y := by
    intro x y
    change (e x).1 ⬝ᵥ (Tag.E6.symmetrizedCartan *ᵥ (e y).1) ≠ 0 ↔
      x.1 ⬝ᵥ (Tag.E6.symmetrizedCartan *ᵥ y.1) ≠ 0
    simpa only [dotProduct_mulVec_eq_iform] using hiff x y
  have hmaps : ∀ {x y : kernelRoots (rootCharHom a)},
      kernelRootSetoid (rootCharHom a) x y →
      kernelRootSetoid (rootCharHom a) (e x) (e y) := by
    intro x y h
    have h' : Relation.EqvGen (s4rel (rootCharHom a)) x y := h
    clear h
    induction h' with
    | rel u v huv => exact Relation.EqvGen.rel _ _ ((hdot u v).mpr huv)
    | refl => exact Relation.EqvGen.refl _
    | symm u v _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans u v w _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2
  have hmaps_symm : ∀ {u v : kernelRoots (rootCharHom a)},
      Relation.EqvGen (s4rel (rootCharHom a)) u v →
      Relation.EqvGen (s4rel (rootCharHom a)) (e.symm u) (e.symm v) := by
    intro u v h
    induction h with
    | rel x y hxy =>
        exact Relation.EqvGen.rel _ _ ((hdot (e.symm x) (e.symm y)).mp
          (by rwa [e.apply_symm_apply, e.apply_symm_apply]))
    | refl => exact Relation.EqvGen.refl _
    | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans x y z _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2
  have hmaps' : ∀ {x y : kernelRoots (rootCharHom a)},
      kernelRootSetoid (rootCharHom a) (e x) (e y) →
      kernelRootSetoid (rootCharHom a) x y := by
    intro x y h
    have h' : Relation.EqvGen (s4rel (rootCharHom a)) (e.symm (e x)) (e.symm (e y)) :=
      hmaps_symm h
    rwa [e.symm_apply_apply, e.symm_apply_apply] at h'
  have heq : ∀ x y : kernelRoots (rootCharHom a),
      kernelRootSetoid (rootCharHom a) x y ↔
      kernelRootSetoid (rootCharHom a) (e x) (e y) :=
    fun x y => ⟨fun h => hmaps h, fun h => hmaps' h⟩
  let ρb : Equiv.Perm (KernelComponent (rootCharHom a)) := Quotient.congr e heq
  have hρbmk : ∀ x : kernelRoots (rootCharHom a),
      ρb (⟦x⟧ : KernelComponent (rootCharHom a)) = ⟦e x⟧ :=
    fun x => Quotient.congr_mk e heq x
  have hσ : ∀ i, ⇑S.ρ '' componentRoots (rootCharHom a) i =
      componentRoots (rootCharHom a) (ρb i) := by
    intro i
    refine Set.Subset.antisymm ?_ ?_
    · rintro β ⟨α, hα, rfl⟩
      simp only [componentRoots, Set.mem_setOf_eq] at hα ⊢
      obtain ⟨hαk, hαi⟩ := hα
      refine ⟨s4_rho_mem_kernel S a hT hαk, ?_⟩
      have hev : e ⟨α, hαk⟩ = ⟨S.ρ α, s4_rho_mem_kernel S a hT hαk⟩ := Subtype.ext rfl
      calc (⟦(⟨S.ρ α, s4_rho_mem_kernel S a hT hαk⟩ : kernelRoots (rootCharHom a))⟧ :
              KernelComponent (rootCharHom a))
          = ⟦e ⟨α, hαk⟩⟧ := by rw [hev]
        _ = ρb (⟦⟨α, hαk⟩⟧ : KernelComponent (rootCharHom a)) := (hρbmk ⟨α, hαk⟩).symm
        _ = ρb i := by rw [hαi]
    · rintro β hβ
      simp only [componentRoots, Set.mem_setOf_eq] at hβ
      obtain ⟨hβk, hβi⟩ := hβ
      let δ : kernelRoots (rootCharHom a) := e.symm ⟨β, hβk⟩
      have heδ : e δ = ⟨β, hβk⟩ := by
        show e (e.symm ⟨β, hβk⟩) = ⟨β, hβk⟩
        exact e.apply_symm_apply ⟨β, hβk⟩
      have hδi : (⟦δ⟧ : KernelComponent (rootCharHom a)) = i := by
        apply ρb.injective
        rw [hρbmk δ, heδ]
        exact hβi
      rw [Set.mem_image]
      refine ⟨δ.1, ?_, ?_⟩
      · exact ⟨δ.2, hδi⟩
      · have hval := congrArg Subtype.val heδ
        simpa [he_val δ] using hval
  refine ⟨ρb, hσ, ?_⟩
  intro i
  rw [componentRootSpan, componentRootSpan]
  rw [s4_map_rootSpan S
    {α | ∃ h : α ∈ kernelRoots (rootCharHom a),
      (⟦⟨α, h⟩⟧ : KernelComponent (rootCharHom a)) = i}
    (fun α hα => hα.1.1)]
  exact congrArg (rootSpan .E6 L)
    (show ⇑S.ρ '' {α | ∃ h : α ∈ kernelRoots (rootCharHom a),
        (⟦⟨α, h⟩⟧ : KernelComponent (rootCharHom a)) = i} =
      {α | ∃ h : α ∈ kernelRoots (rootCharHom a),
        (⟦⟨α, h⟩⟧ : KernelComponent (rootCharHom a)) = ρb i} from hσ i)

theorem ntpS4_commute
    {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup .E6 L p₀)
    (a : Fin Tag.E6.rank → Lˣ) (g : ModGL .E6 L) (hg : g ∈ S.D.model)
    (π ρb : Equiv.Perm (KernelComponent (rootCharHom a)))
    (hπ : ∀ i, (componentRootSpan L (rootCharHom a) i).map (MulAut.conj g).toMonoidHom =
      componentRootSpan L (rootCharHom a) (π i))
    (hρ : ∀ i, (componentRootSpan L (rootCharHom a) i).map S.D.step =
      componentRootSpan L (rootCharHom a) (ρb i))
    (hinj : ∀ i j, componentRootSpan L (rootCharHom a) i = componentRootSpan L (rootCharHom a) j →
      i = j) :
    π * ρb = ρb * π := by
  classical
  have hgstep : S.D.step g = g := by
    have h : S.D.n * S.D.Φ g * S.D.n⁻¹ = g := ((LangDatum.mem_model (D := S.D)).1 hg).2
    simpa [LangDatum.step, MulAut.conj_apply] using h
  have hconj : S.D.step.comp (MulAut.conj g).toMonoidHom =
      (MulAut.conj g).toMonoidHom.comp S.D.step := by
    refine MonoidHom.ext fun x => ?_
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply]
    rw [show (MulAut.conj g).toMonoidHom x = g * x * g⁻¹ from MulAut.conj_apply g x,
      show (MulAut.conj g).toMonoidHom (S.D.step x) = g * S.D.step x * g⁻¹ from
        MulAut.conj_apply g (S.D.step x)]
    rw [map_mul, map_mul, map_inv, hgstep]
  apply Equiv.ext
  intro i
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
  apply hinj
  calc componentRootSpan L (rootCharHom a) (π (ρb i))
      = (componentRootSpan L (rootCharHom a) (ρb i)).map (MulAut.conj g).toMonoidHom :=
        (hπ (ρb i)).symm
    _ = ((componentRootSpan L (rootCharHom a) i).map S.D.step).map
          (MulAut.conj g).toMonoidHom := by rw [hρ i]
    _ = (componentRootSpan L (rootCharHom a) i).map
          ((MulAut.conj g).toMonoidHom.comp S.D.step) := by rw [Subgroup.map_map]
    _ = (componentRootSpan L (rootCharHom a) i).map
          (S.D.step.comp (MulAut.conj g).toMonoidHom) := by rw [hconj]
    _ = ((componentRootSpan L (rootCharHom a) i).map
          (MulAut.conj g).toMonoidHom).map S.D.step := by rw [Subgroup.map_map]
    _ = (componentRootSpan L (rootCharHom a) (π i)).map S.D.step := by rw [hπ i]
    _ = componentRootSpan L (rootCharHom a) (ρb (π i)) := hρ (π i)

end CFSG.StandardType.NTPlane

end
