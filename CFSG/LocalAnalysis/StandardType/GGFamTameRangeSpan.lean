module

public import CFSG.LocalAnalysis.StandardType.GGFamTameRange
public import CFSG.LocalAnalysis.StandardType.GGFamTameTransfer
public import CFSG.LocalAnalysis.StandardType.GGFamTameOrbit
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimple

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped commutatorElement

theorem famRangeSpan_CQ_le_rootSpan
    {τ : Tag} {L : Type} [Field L] {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} (σ : L ≃+* L) (i : KernelComponent χ) :
    CQ σ i ≤ rootSpan τ L (componentRoots χ i) := by
  unfold CQ
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨γ, hγ, c, hc, rfl⟩
  rw [unionRoots_singleton] at hγ
  exact pinnedX_mem_rootSpan hγ c

theorem famRangeSpan_frobGL_eq_self_of_mem_CQ
    {τ : Tag} {L : Type} [Field L] {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} (σ : L ≃+* L) (i : KernelComponent χ)
    {x : ModGL τ L} (hx : x ∈ CQ σ i) : frobGL σ x = x := by
  have : CQ σ i ≤ (frobGL σ).eqLocus (MonoidHom.id _) := by
    unfold CQ
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨γ, hγ, c, hc, rfl⟩
    show frobGL σ (pinnedX τ L γ c) = pinnedX τ L γ c
    rw [frobGL_pinnedX, hc]
  exact this hx

theorem famRangeSpan_unionRootSpan_singleton_eq
    {τ : Tag} {L : Type} [Field L] {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} (i : KernelComponent χ) :
    unionRootSpan L χ ({i} : Set (KernelComponent χ)) = rootSpan τ L (componentRoots χ i) := by
  unfold unionRootSpan
  rw [unionRoots_singleton]

theorem famRangeSpan_orbit_centralizer_hyp
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hρ : ∀ γ ∈ kernelRoots χ, S.ρ γ ∈ kernelRoots χ) (i : KernelComponent χ) {s : ℕ} [NeZero s]
    (hs : (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' componentRoots χ i = componentRoots χ i)
    (hmin : ∀ k, 0 < k → k < s →
      (S.ρ : (Fin τ.rank → ℤ) → _)^[k] '' componentRoots χ i ≠ componentRoots χ i) :
    ∀ w ∈ (famOrbitFamily S hρ i hs hmin).Z,
      ∀ x ∈ unionRootSpan L χ ({i} : Set (KernelComponent χ)), x * w = w * x := by
  intro w hw x hx
  rw [famRangeSpan_unionRootSpan_singleton_eq] at hx
  exact (famOrbitFamily S hρ i hs hmin).mem_Z.1 hw x
    ((famOrbitFamily S hρ i hs hmin).S_le_A 0 (by
      show x ∈ rootSpan τ L ((S.ρ : (Fin τ.rank → ℤ) → _)^[(0 : ZMod s).val] ''
        componentRoots χ i)
      rw [ZMod.val_zero]
      simpa using hx))

theorem famRangeSpan_orbit_commutator_mem_CQ
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hρ : ∀ γ ∈ kernelRoots χ, S.ρ γ ∈ kernelRoots χ) (i : KernelComponent χ) {s : ℕ} [NeZero s]
    (hs : (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' componentRoots χ i = componentRoots χ i)
    (hmin : ∀ k, 0 < k → k < s →
      (S.ρ : (Fin τ.rank → ℤ) → _)^[k] '' componentRoots χ i ≠ componentRoots χ i)
    (σ : L ≃+* L) (hsL : ∃ u : Lˣ, u ^ 2 ≠ 1)
    {g g' : ModGL τ L} (hg : g ∈ rootSpan τ L (componentRoots χ i))
    (hg' : g' ∈ rootSpan τ L (componentRoots χ i))
    (hgZ : frobGL σ g * g⁻¹ ∈ (famOrbitFamily S hρ i hs hmin).Z)
    (hgZ' : frobGL σ g' * g'⁻¹ ∈ (famOrbitFamily S hρ i hs hmin).Z) :
    ⁅g, g'⁆ ∈ CQ σ i :=
  commutator_mem_CQ (σ := σ) (i := i) hsL
    (famRangeSpan_orbit_centralizer_hyp S hρ i hs hmin)
    (by rw [famRangeSpan_unionRootSpan_singleton_eq]; exact hg)
    (by rw [famRangeSpan_unionRootSpan_singleton_eq]; exact hg')
    hgZ hgZ'

theorem famRangeSpan_rationalComponent_eq_rangeT_le
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hρ : ∀ γ ∈ kernelRoots χ, S.ρ γ ∈ kernelRoots χ) (i : KernelComponent χ)
    {s : ℕ} [NeZero s]
    (hs : (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' componentRoots χ i = componentRoots χ i)
    (hmin : ∀ k, 0 < k → k < s →
      (S.ρ : (Fin τ.rank → ℤ) → _)^[k] '' componentRoots χ i ≠ componentRoots χ i)
    (σ : L ≃+* L) (z : ModGL τ L)
    (hnorm : ∀ j : KernelComponent χ, ∀ g : ModGL τ L,
      g ∈ rootSpan τ L (componentRoots χ j) ↔
        z * g * z⁻¹ ∈ rootSpan τ L (componentRoots χ j))
    (hz : ∀ g ∈ rootSpan τ L (componentRoots χ i),
      iterHom S.D.step s (z * g * z⁻¹) = z * frobGL σ g * z⁻¹)
    (Cg : Subgroup (ModGL τ (fixSubfield σ)))
    (hCg : Cg ≤ componentRootSpan (fixSubfield σ) χ i)
    (hY : ∀ g g' : ModGL τ L, g ∈ rootSpan τ L (componentRoots χ i) →
      g' ∈ rootSpan τ L (componentRoots χ i) →
      frobGL σ g * g⁻¹ ∈ (famOrbitFamily S hρ i hs hmin).Z →
      frobGL σ g' * g'⁻¹ ∈ (famOrbitFamily S hρ i hs hmin).Z →
      ⁅g, g'⁆ ∈ Cg.map (baseChangeGL (fixSubfield σ).subtype)) :
    ∃ f : Cg →* ModGL τ L, rationalComponentM S.ρ S.Γ χ i ≤ f.range ∧
      f.ker ≤ Subgroup.center Cg ∧
      (⁅Cg, Cg⁆ = Cg → f.range ≤ rationalComponentM S.ρ S.Γ χ i) ∧
      f.range ≤ rootSpan τ L (rationalRootsM S.ρ χ i) ⊓ S.D.model := by
  classical
  set P := famOrbitFamily S hρ i hs hmin with hP
  set ι := baseChangeGL (τ := τ) (fixSubfield σ).subtype with hι
  set Ψ := componentRoots χ i with hΨ
  have hP0 : P.S 0 = rootSpan τ L Ψ := by
    rw [hP, famOrbitFamily_S, ZMod.val_zero]
    simp only [Function.iterate_zero, id_eq, Set.image_id']
    rfl
  have hιC : ∀ x ∈ Cg, ι x ∈ CQ σ i := by
    intro x hx
    rw [CQ_eq_map]
    exact ⟨x, hCg hx, rfl⟩
  have hιS : ∀ x ∈ Cg, ι x ∈ rootSpan τ L Ψ :=
    fun x hx => famRangeSpan_CQ_le_rootSpan σ i (hιC x hx)
  have hιinj : Function.Injective ι := baseChangeGL_injective _
  have hzA : ∀ a ∈ P.A, z * a * z⁻¹ ∈ P.A := by
    have h : P.A ≤ P.A.comap (MulAut.conj z).toMonoidHom := by
      refine iSup_le fun k => ?_
      obtain ⟨j, hj⟩ := fam_iterate_image_component S hρ i k.val
      intro g hg
      have hg' : g ∈ rootSpan τ L (componentRoots χ j) := by rw [hj]; exact hg
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
  obtain ⟨f, hf1, hf2, hf3, hf4⟩ :=
    fam_rationalComponent_eq_range_of_hom_le S hρ i hs hmin θ
    (fun x => (hnorm i _).1 (hιS x.1 x.2))
    (fun x => by rw [hθ, hz _ (hιS x.1 x.2),
      famRangeSpan_frobGL_eq_self_of_mem_CQ σ i (hιC x.1 x.2)])
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
  exact ⟨f, hf1, hf2, fun hperf => hf3 (Subgroup.isPerfect_iff.2 hperf), hf4⟩

theorem famRangeSpan_rationalComponent_eq_rangeT
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hρ : ∀ γ ∈ kernelRoots χ, S.ρ γ ∈ kernelRoots χ) (i : KernelComponent χ)
    {s : ℕ} [NeZero s]
    (hs : (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' componentRoots χ i = componentRoots χ i)
    (hmin : ∀ k, 0 < k → k < s →
      (S.ρ : (Fin τ.rank → ℤ) → _)^[k] '' componentRoots χ i ≠ componentRoots χ i)
    (σ : L ≃+* L) (z : ModGL τ L)
    (hnorm : ∀ j : KernelComponent χ, ∀ g : ModGL τ L,
      g ∈ rootSpan τ L (componentRoots χ j) ↔
        z * g * z⁻¹ ∈ rootSpan τ L (componentRoots χ j))
    (hz : ∀ g ∈ rootSpan τ L (componentRoots χ i),
      iterHom S.D.step s (z * g * z⁻¹) = z * frobGL σ g * z⁻¹)
    (Cg : Subgroup (ModGL τ (fixSubfield σ)))
    (hCg : Cg ≤ componentRootSpan (fixSubfield σ) χ i)
    (hY : ∀ g g' : ModGL τ L, g ∈ rootSpan τ L (componentRoots χ i) →
      g' ∈ rootSpan τ L (componentRoots χ i) →
      frobGL σ g * g⁻¹ ∈ (famOrbitFamily S hρ i hs hmin).Z →
      frobGL σ g' * g'⁻¹ ∈ (famOrbitFamily S hρ i hs hmin).Z →
      ⁅g, g'⁆ ∈ Cg.map (baseChangeGL (fixSubfield σ).subtype)) :
    ∃ f : Cg →* ModGL τ L, rationalComponentM S.ρ S.Γ χ i ≤ f.range ∧
      f.ker ≤ Subgroup.center Cg ∧
      (⁅Cg, Cg⁆ = Cg → f.range ≤ rationalComponentM S.ρ S.Γ χ i) := by
  obtain ⟨f, hf1, hf2, hf3, -⟩ :=
    famRangeSpan_rationalComponent_eq_rangeT_le S hρ i hs hmin σ z hnorm hz Cg hCg hY
  exact ⟨f, hf1, hf2, hf3⟩

theorem fam_rationalComponent_eq_range_componentRootSpan_le
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hρ : ∀ γ ∈ kernelRoots χ, S.ρ γ ∈ kernelRoots χ) (i : KernelComponent χ)
    {s : ℕ} [NeZero s]
    (hs : (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' componentRoots χ i = componentRoots χ i)
    (hmin : ∀ k, 0 < k → k < s →
      (S.ρ : (Fin τ.rank → ℤ) → _)^[k] '' componentRoots χ i ≠ componentRoots χ i)
    (σ : L ≃+* L) (z : ModGL τ L)
    (hnorm : ∀ j : KernelComponent χ, ∀ g : ModGL τ L,
      g ∈ rootSpan τ L (componentRoots χ j) ↔
        z * g * z⁻¹ ∈ rootSpan τ L (componentRoots χ j))
    (hz : ∀ g ∈ rootSpan τ L (componentRoots χ i),
      iterHom S.D.step s (z * g * z⁻¹) = z * frobGL σ g * z⁻¹)
    (hsL : ∃ u : Lˣ, u ^ 2 ≠ 1) :
    ∃ f : componentRootSpan (fixSubfield σ) χ i →* ModGL τ L,
      rationalComponentM S.ρ S.Γ χ i ≤ f.range ∧
      f.ker ≤ Subgroup.center (componentRootSpan (fixSubfield σ) χ i) ∧
      (⁅componentRootSpan (fixSubfield σ) χ i, componentRootSpan (fixSubfield σ) χ i⁆ =
          componentRootSpan (fixSubfield σ) χ i →
        f.range ≤ rationalComponentM S.ρ S.Γ χ i) ∧
      f.range ≤ rootSpan τ L (rationalRootsM S.ρ χ i) ⊓ S.D.model :=
  famRangeSpan_rationalComponent_eq_rangeT_le S hρ i hs hmin σ z hnorm hz _
    le_rfl fun _ _ hg hg' hgZ hgZ' => by
    have := famRangeSpan_orbit_commutator_mem_CQ S hρ i hs hmin σ hsL hg hg' hgZ hgZ'
    rwa [CQ_eq_map] at this

theorem fam_rationalComponent_eq_range_componentRootSpan
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hρ : ∀ γ ∈ kernelRoots χ, S.ρ γ ∈ kernelRoots χ) (i : KernelComponent χ)
    {s : ℕ} [NeZero s]
    (hs : (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' componentRoots χ i = componentRoots χ i)
    (hmin : ∀ k, 0 < k → k < s →
      (S.ρ : (Fin τ.rank → ℤ) → _)^[k] '' componentRoots χ i ≠ componentRoots χ i)
    (σ : L ≃+* L) (z : ModGL τ L)
    (hnorm : ∀ j : KernelComponent χ, ∀ g : ModGL τ L,
      g ∈ rootSpan τ L (componentRoots χ j) ↔
        z * g * z⁻¹ ∈ rootSpan τ L (componentRoots χ j))
    (hz : ∀ g ∈ rootSpan τ L (componentRoots χ i),
      iterHom S.D.step s (z * g * z⁻¹) = z * frobGL σ g * z⁻¹)
    (hsL : ∃ u : Lˣ, u ^ 2 ≠ 1) :
    ∃ f : componentRootSpan (fixSubfield σ) χ i →* ModGL τ L,
      rationalComponentM S.ρ S.Γ χ i ≤ f.range ∧
      f.ker ≤ Subgroup.center (componentRootSpan (fixSubfield σ) χ i) ∧
      (⁅componentRootSpan (fixSubfield σ) χ i, componentRootSpan (fixSubfield σ) χ i⁆ =
          componentRootSpan (fixSubfield σ) χ i →
        f.range ≤ rationalComponentM S.ρ S.Γ χ i) := by
  obtain ⟨f, hf1, hf2, hf3, -⟩ :=
    fam_rationalComponent_eq_range_componentRootSpan_le S hρ i hs hmin σ z hnorm hz hsL
  exact ⟨f, hf1, hf2, hf3⟩

theorem fam_twistInner_of_twistKind_eq_inner (hW : RootAutIsWeyl)
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hρ : ∀ γ ∈ kernelRoots χ, S.ρ γ ∈ kernelRoots χ) (i : KernelComponent χ)
    (h : twistKindM S.ρ χ i = .inner) :
    twistInner (componentRoots χ i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ (componentRoots χ i)]) := by
  classical
  by_contra hn
  have hΨ := isRootComponent_componentRoots (χ := χ) i
  obtain ⟨hs0, hs, -⟩ := fam_componentOrbitLength_spec S hρ i
  unfold twistKindM at h
  rw [ite_eq_right hn] at h
  split_ifs at h with h1 h2 h3
  refine hn (hW τ _ hΨ ?_ _ ?_ (fun γ _ δ _ => iform_rho_iterate S _ γ δ) ?_)
  · rintro (h4 | h4 | h4)
    · exact h3 h4
    · exact h2 h4
    · exact h1 (Or.inl h4)
  · refine ⟨fun x hx => ?_, ?_, hs.ge⟩
    · have h5 := Set.mem_image_of_mem ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots χ i)]) hx
      rwa [hs] at h5
    · exact (S.ρ.injective.iterate _).injOn
  · intro γ hγ
    have hγ' : -γ ∈ componentRoots χ i := hΨ.neg_mem γ hγ
    set σ := (S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
      (componentRoots χ i)] with hσ
    have e0 : iform (σ (-γ) + σ γ) (σ (-γ) + σ γ) = 0 := by
      simp only [iform_add_left, iform_add_right, hσ, iform_rho_iterate S]
      simp only [iform_neg_left_aux, iform_neg_right_aux]
      ring
    have hz : σ (-γ) + σ γ = 0 := by
      by_contra hne
      have := iform_self_pos hne
      omega
    exact eq_neg_of_add_eq_zero_left hz

end CFSG.StandardType.TableCRes
