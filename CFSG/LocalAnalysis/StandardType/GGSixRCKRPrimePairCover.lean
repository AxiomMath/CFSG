module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeReturnedFrame
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.InnerCover
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcCtx
public import CFSG.LieType.Chevalley.GraphFixedOrbitCollection
public import CFSG.LieType.AlgebraicGroups.ToralTwistSemilinearDatum

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.StandardType.GGFinModel
open scoped commutatorElement

section Helpers

theorem rckCov_rationalComponent_eq_range_of_hom_T
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    (S : LangSetup τ L p) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a)) {s : ℕ} [NeZero s]
    (hs : (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' componentRoots (rootCharHom a) i =
      componentRoots (rootCharHom a) i)
    (hmin : ∀ k, 0 < k → k < s →
      (S.ρ : (Fin τ.rank → ℤ) → _)^[k] '' componentRoots (rootCharHom a) i ≠
        componentRoots (rootCharHom a) i)
    {C : Type*} [Group C] (θ : C →* ModGL τ L)
    (hθS0 : ∀ c, θ c ∈ (outerOrbitFamily S hT i hs hmin).S 0)
    (hθfix : ∀ c, iterHom S.D.step s (θ c) = θ c)
    (hθY : ∀ g g' : ModGL τ L, g ∈ rootSpan τ L (componentRoots (rootCharHom a) i) →
      g' ∈ rootSpan τ L (componentRoots (rootCharHom a) i) →
      iterHom S.D.step s g * g⁻¹ ∈ (outerOrbitFamily S hT i hs hmin).Z →
      iterHom S.D.step s g' * g'⁻¹ ∈ (outerOrbitFamily S hT i hs hmin).Z → ⁅g, g'⁆ ∈ θ.range)
    (hθZ : ∀ c, θ c ∈ (outerOrbitFamily S hT i hs hmin).Z → c ∈ Subgroup.center C) :
    ∃ f : C →* ModGL τ L, rationalComponent S.ρ S.Γ (rootCharHom a) i ≤ f.range ∧
      f.ker ≤ Subgroup.center C ∧
      (Group.IsPerfect C → f.range ≤ rationalComponent S.ρ S.Γ (rootCharHom a) i) ∧
      ∀ c, f c = (outerOrbitFamily S hT i hs hmin).norm
        (θ.codRestrict ((outerOrbitFamily S hT i hs hmin).S 0) hθS0 c) := by
  classical
  set P := outerOrbitFamily S hT i hs hmin with hP
  set Ψ := componentRoots (rootCharHom a) i with hΨ
  have hP0 : P.S 0 = rootSpan τ L Ψ := by
    rw [hP, outerOrbitFamily_S, ZMod.val_zero]
    simp only [Function.iterate_zero, id_eq, Set.image_id']
    rfl
  let θ₀ : C →* P.S 0 := θ.codRestrict (P.S 0) hθS0
  have hθ₀ : ∀ c, ((θ₀ c : P.S 0) : ModGL τ L) = θ c := fun c => rfl
  let f : C →* ModGL τ L := P.norm.comp θ₀
  have hfix : ∀ c, iterHom S.D.step s ((θ₀ c : P.S 0) : ModGL τ L) = θ₀ c := fun c => by
    rw [hθ₀]; exact hθfix c
  have hYW : ⁅P.Y, P.Y⁆ ≤ θ.range := by
    rw [Subgroup.commutator_le]
    intro u hu u' hu'
    obtain ⟨hu0, huZ⟩ := P.mem_Y.1 hu
    obtain ⟨hu0', huZ'⟩ := P.mem_Y.1 hu'
    rw [hP0] at hu0 hu0'
    exact hθY u u' hu0 hu0' huZ huZ'
  have hΓM : S.Γ ≤ S.D.model := commutator_le_self' _
  have hrsA : rationalSpan S.ρ S.Γ (rootCharHom a) i ≤ P.Afix := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.1 hx
    refine ⟨?_, (hΓM hx2).2⟩
    rw [hP, outerOrbitFamily_A]
    exact hx1
  refine ⟨f, ?_, ?_, ?_, ?_⟩
  · intro g hg
    have h1 := P.commutator_Afix_le (Subgroup.commutator_mono hrsA hrsA hg)
    obtain ⟨y, hyY, rfl⟩ := P.mem_normImage.1 h1
    obtain ⟨c, hc⟩ := hYW hyY
    refine ⟨c, ?_⟩
    change P.norm (θ₀ c) = P.norm y
    congr 1
    exact Subtype.ext hc
  · intro c hc
    have h1 : P.norm (θ₀ c) = 1 := hc
    exact hθZ c (P.mem_Z_of_norm_eq_one h1)
  · intro hperf
    rintro _ ⟨x, rfl⟩
    exact outer_norm_mem_rationalComponent S hT i hs hmin hperf θ₀ hfix x
  · intro c
    rfl

private theorem rckCov_norm_eq_self_of_subsingleton {G : Type*} [Group G] {F : G →* G} {s : ℕ}
    [NeZero s] [Subsingleton (ZMod s)] (P : CycFamily F s) (y : P.S 0) :
    P.norm y = (y : G) := by
  have hdiag : P.diag y = Pi.mulSingle (0 : ZMod s) (P.iter (0 : ZMod s) y) := by
    funext k
    rw [Subsingleton.elim k (0 : ZMod s)]
    simp [CycFamily.diag]
  show P.mu (P.diag y) = (y : G)
  rw [hdiag, CycFamily.mu_mulSingle]
  simp [CycFamily.coe_iter, ZMod.val_zero]

private theorem rckCov_rationalComponent_eq_rangeT
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    (S : LangSetup τ L p) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    {s : ℕ} [NeZero s]
    (hs : (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' componentRoots (rootCharHom a) i =
      componentRoots (rootCharHom a) i)
    (hmin : ∀ k, 0 < k → k < s →
      (S.ρ : (Fin τ.rank → ℤ) → _)^[k] '' componentRoots (rootCharHom a) i ≠
        componentRoots (rootCharHom a) i)
    (σ : L ≃+* L) (z : ModGL τ L)
    (hnorm : ∀ j : KernelComponent (rootCharHom a), ∀ g : ModGL τ L,
      g ∈ rootSpan τ L (componentRoots (rootCharHom a) j) ↔
        z * g * z⁻¹ ∈ rootSpan τ L (componentRoots (rootCharHom a) j))
    (hz : ∀ g ∈ rootSpan τ L (componentRoots (rootCharHom a) i),
      iterHom S.D.step s (z * g * z⁻¹) = z * frobGL σ g * z⁻¹)
    (Cg : Subgroup (ModGL τ (fixSubfield σ)))
    (hCg : Cg ≤ componentRootSpan (fixSubfield σ) (rootCharHom a) i)
    (hY : ∀ g g' : ModGL τ L, g ∈ rootSpan τ L (componentRoots (rootCharHom a) i) →
      g' ∈ rootSpan τ L (componentRoots (rootCharHom a) i) →
      frobGL σ g * g⁻¹ ∈ (outerOrbitFamily S hT i hs hmin).Z →
      frobGL σ g' * g'⁻¹ ∈ (outerOrbitFamily S hT i hs hmin).Z →
      ⁅g, g'⁆ ∈ Cg.map (baseChangeGL (fixSubfield σ).subtype)) :
    ∃ f : Cg →* ModGL τ L, rationalComponent S.ρ S.Γ (rootCharHom a) i ≤ f.range ∧
      f.ker ≤ Subgroup.center Cg ∧
      (⁅Cg, Cg⁆ = Cg → f.range ≤ rationalComponent S.ρ S.Γ (rootCharHom a) i) ∧
      (s = 1 → ∀ x : Cg, f x = z * baseChangeGL (fixSubfield σ).subtype
        (x : ModGL τ (fixSubfield σ)) * z⁻¹) := by
  classical
  set P := outerOrbitFamily S hT i hs hmin with hP
  set ι := baseChangeGL (τ := τ) (fixSubfield σ).subtype with hι
  set Ψ := componentRoots (rootCharHom a) i with hΨ
  have hP0 : P.S 0 = rootSpan τ L Ψ := by
    rw [hP, outerOrbitFamily_S, ZMod.val_zero]
    simp only [Function.iterate_zero, id_eq, Set.image_id']
    rfl
  have hιC : ∀ x ∈ Cg, ι x ∈ CQ σ i := by
    intro x hx
    rw [CQ_eq_map]
    exact ⟨x, hCg hx, rfl⟩
  have hιS : ∀ x ∈ Cg, ι x ∈ rootSpan τ L Ψ := fun x hx => CQ_le_rootSpan σ i (hιC x hx)
  have hιinj : Function.Injective ι := baseChangeGL_injective _
  have hzA : ∀ a ∈ P.A, z * a * z⁻¹ ∈ P.A := by
    have h : P.A ≤ P.A.comap (MulAut.conj z).toMonoidHom := by
      refine iSup_le fun k => ?_
      obtain ⟨j, hj⟩ := outer_iterate_image_component S hT i k.val
      intro g hg
      have hg' : g ∈ rootSpan τ L (componentRoots (rootCharHom a) j) := by rw [hj]; exact hg
      have h2 := (hnorm j g).1 hg'
      rw [hj] at h2
      exact P.S_le_A k h2
    exact fun a ha => h ha
  have hZconj : ∀ X : ModGL τ L, z * X * z⁻¹ ∈ P.Z → X ∈ P.Z := by
    intro X hX
    rw [CycFamily.mem_Z] at hX ⊢
    intro a ha
    have := hX _ (hzA a ha)
    have e : z * a * z⁻¹ * (z * X * z⁻¹) = z * (a * X) * z⁻¹ := by group
    have e' : z * X * z⁻¹ * (z * a * z⁻¹) = z * (X * a) * z⁻¹ := by group
    rw [e, e'] at this
    simpa using this
  have hYc : ∀ u ∈ rootSpan τ L Ψ, iterHom S.D.step s u * u⁻¹ ∈ P.Z →
      ∃ g ∈ rootSpan τ L Ψ, u = z * g * z⁻¹ ∧ frobGL σ g * g⁻¹ ∈ P.Z := by
    intro u hu0 huZ
    have e : z * (z⁻¹ * u * z) * z⁻¹ = u := by group
    have hg : z⁻¹ * u * z ∈ rootSpan τ L Ψ := (hnorm i (z⁻¹ * u * z)).2 (by rw [e]; exact hu0)
    refine ⟨z⁻¹ * u * z, hg, by group, hZconj _ ?_⟩
    have h1 := hz _ hg
    rw [e] at h1
    have e2 : z * (frobGL σ (z⁻¹ * u * z) * (z⁻¹ * u * z)⁻¹) * z⁻¹ =
        (z * frobGL σ (z⁻¹ * u * z) * z⁻¹) * u⁻¹ := by group
    rw [e2, ← h1]
    exact huZ
  let θ : Cg →* ModGL τ L := (MulAut.conj z).toMonoidHom.comp (ι.comp Cg.subtype)
  have hθ : ∀ x : Cg, θ x = z * ι x.1 * z⁻¹ := fun x => rfl
  have hθS0 : ∀ x : Cg, θ x ∈ P.S 0 := fun x => by
    rw [hθ, hP0]
    exact (hnorm i (ι x.1)).1 (hιS x.1 x.2)
  obtain ⟨f, hf1, hf2, hf3, hform⟩ :=
    rckCov_rationalComponent_eq_range_of_hom_T S hT i hs hmin θ hθS0
      (fun x => by rw [hθ, hz _ (hιS x.1 x.2), frobGL_eq_self_of_mem_CQ σ i (hιC x.1 x.2)])
      (fun u u' hu hu' huZ huZ' => by
        obtain ⟨g, hg, rfl, hgZ⟩ := hYc u hu huZ
        obtain ⟨g', hg', rfl, hgZ'⟩ := hYc u' hu' huZ'
        obtain ⟨c0, hc0, hc0e⟩ := hY g g' hg hg' hgZ hgZ'
        refine ⟨⟨c0, hc0⟩, ?_⟩
        show z * ι c0 * z⁻¹ = ⁅z * g * z⁻¹, z * g' * z⁻¹⁆
        rw [show ι c0 = ⁅g, g'⁆ from hc0e]
        simp only [commutatorElement_def]
        group)
      (fun c hc => by
        rw [hθ] at hc
        have h3 := hZconj _ hc
        rw [Subgroup.mem_center_iff]
        intro c'
        have h4 := P.mem_Z.1 h3 (ι c'.1) (P.S_le_A 0 (by rw [hP0]; exact hιS c'.1 c'.2))
        exact Subtype.ext (hιinj (by simpa using h4)))
  refine ⟨f, hf1, hf2, fun hperf => hf3 (Subgroup.isPerfect_iff.2 hperf), ?_⟩
  intro hs1 x
  haveI : Subsingleton (ZMod s) := ZMod.subsingleton_iff.2 hs1
  rw [hform x, rckCov_norm_eq_self_of_subsingleton P (θ.codRestrict (P.S 0) hθS0 x)]
  rfl

end Helpers

theorem rckInnerCoverExplicit
    {τ : Tag} {p₀ : ℕ} (S : LangSetup τ GGL p₀)
    {a : Fin τ.rank → GGLˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a))
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    ∃ σ : GGL ≃+* GGL, (∀ c, σ c = c ^ (S.D.q ^ componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i))) ∧ Finite ↥(fixSubfield σ) ∧
      Nat.card ↥(fixSubfield σ) = S.D.q ^ componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i) ∧
      ∃ f : ↥(componentRootSpan (fixSubfield σ) (rootCharHom a) i) →* ModGL τ GGL,
        rationalComponent S.ρ S.Γ (rootCharHom a) i ≤ f.range ∧
        f.ker ≤ Subgroup.center ↥(componentRootSpan (fixSubfield σ) (rootCharHom a) i) ∧
        (⁅componentRootSpan (fixSubfield σ) (rootCharHom a) i,
            componentRootSpan (fixSubfield σ) (rootCharHom a) i⁆ =
            componentRootSpan (fixSubfield σ) (rootCharHom a) i →
          f.range ≤ rationalComponent S.ρ S.Γ (rootCharHom a) i) ∧
        (componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1 →
          ∃ z ∈ adjointGroup τ GGL,
            (∀ g ∈ rootSpan τ GGL (componentRoots (rootCharHom a) i),
              S.D.step (z * g * z⁻¹) = z * frobGL σ g * z⁻¹) ∧
            (∀ x : ↥(componentRootSpan (fixSubfield σ) (rootCharHom a) i),
              f x = z * baseChangeGL (fixSubfield σ).subtype
                (x : ModGL τ ↥(fixSubfield σ)) * z⁻¹) ∧
            z ∈ torusGroup τ GGL ⊔ rootSpan τ GGL (kernelRoots (rootCharHom a)) ∧
            ∀ (j : KernelComponent (rootCharHom a)) (g : ModGL τ GGL),
              g ∈ rootSpan τ GGL (componentRoots (rootCharHom a) j) ↔
                z * g * z⁻¹ ∈ rootSpan τ GGL (componentRoots (rootCharHom a) j)) := by
  classical
  obtain ⟨hs0, hs, hmin⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) with hsdef
  haveI : NeZero s := ⟨hs0.ne'⟩
  obtain ⟨σ, z, hσ, hzZ, hnorm, hz⟩ :=
    CFSG.HardMathSupport.Dickson.Sec6.Up34Exc.exists_untwistT_Z S hT i hs0 hinner
  obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : CharP GGL r := hchar
  have hσ' : ∀ c, σ c = c ^ (r ^ (e * s)) := fun c => by rw [hσ, hq, ← pow_mul]
  obtain ⟨hfinK, hKcard⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.finite_card_fixSubfield
      (L := GGL) (r := r) (n := e * s) (Nat.mul_pos he hs0) σ hσ'
  have hsL : ∃ u : GGLˣ, u ^ 2 ≠ 1 := by
    obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset ({0, 1, -1} : Finset GGL)
    have hc0 : c ≠ 0 := fun h => hc (by simp [h])
    refine ⟨Units.mk0 c hc0, fun h => hc ?_⟩
    have h2 : c ^ 2 = 1 := by simpa using congrArg (fun x : GGLˣ => (x : GGL)) h
    have h3 : (c - 1) * (c + 1) = 0 := by linear_combination h2
    rcases mul_eq_zero.1 h3 with h | h
    · simp [sub_eq_zero.1 h]
    · simp [eq_neg_of_add_eq_zero_left h]
  obtain ⟨f, hf1, hker, hf2, hsform⟩ :=
    rckCov_rationalComponent_eq_rangeT S hT i hs hmin σ z hnorm hz
      (componentRootSpan (fixSubfield σ) (rootCharHom a) i) le_rfl
      (fun g g' hg hg' hgZ hgZ' => by
        have h := orbit_commutator_mem_CQT S hT i hs hmin σ hsL hg hg' hgZ hgZ'
        rwa [CQ_eq_map] at h)
  have hzA : z ∈ adjointGroup τ GGL :=
    (sup_le (CFSG.LieType.AlgebraicGroups.torusGroup_le_adjointGroup)
      (CFSG.LieType.Chevalley.rootSpan_le_adjointGroup GGL
        (kernelRoots (rootCharHom a)))) hzZ
  refine ⟨σ, hσ, hfinK, ?_, f, hf1, hker, hf2, ?_⟩
  · rw [hKcard, hq, ← pow_mul]
  · intro h1
    have hz' := hz
    rw [h1] at hz'
    exact ⟨z, hzA, hz', hsform h1, hzZ, hnorm⟩

end CFSG.StandardType.RCKRP

end
