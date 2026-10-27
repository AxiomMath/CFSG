module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TwoDefs
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6Narrow
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeLow2Z
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TwoCompLabCat
import CFSG.LocalAnalysis.StandardType.KGCoverLift
import CFSG.LocalAnalysis.StandardType.GGTCJDivLin
public import Certificates.Certificate707002

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem e6TwoLeaf_rawDatum_elim_const' {lab : LargeEvenLabel} {Q : Prop}
    (h : LargeEvenRawDatum lab (fun _ _ _ _ => Q)) : Q := by
  obtain ⟨t, l, n⟩ := lab
  cases t
  all_goals dsimp only [LargeEvenRawDatum, LargeEvenRecipeLinear, LargeEvenRecipeUnitary,
    LargeEvenRecipeSymplectic, LargeEvenRecipeOmegaPlus, LargeEvenRecipeOmegaMinus,
    LargeEvenRecipeChevalley, LargeEvenRecipeTwisted, LargeEvenRecipeSuzuki,
    LargeEvenRecipeG2Derived, LargeEvenRecipeTwF4Inherited] at h
  all_goals try split_ifs at h
  all_goals first
    | (obtain ⟨K, i1, i2, hK, b, c, hbc, hq⟩ := h
       exact hq)
    | (obtain ⟨K, i1, i2, hK, hq⟩ := h
       exact hq)

theorem e6TwoLeaf_datumOn_mono {F F' : LargeEvenLieTag → Prop}
    (hFF : ∀ t, F t → F' t) {X : Type} [Group X]
    {A : Subgroup (MulAut X)} {δ : MulAut X} {J : Subgroup X}
    (h : DatumOn F X A δ J) : DatumOn F' X A δ J :=
  ⟨h.1, h.2.1, h.2.2.1,
    largeEvenMarking_mono
      (fun lab R _ I F'' θ ⟨hF, hs3, hin⟩ => ⟨hFF lab.tag hF, hs3, hin⟩) h.2.2.2⟩

theorem e6TwoLeaf_chevE6 {R : Type} [Group R] {lab : LargeEvenLabel} {n : ℕ}
    (h : CFSG.Blueprint.ChevalleyExceptionalModel R (markTag lab) 2 n) (hl : lab.tag = .E6) :
    CFSG.Blueprint.ChevalleyExceptionalModel R .E6 2 n := by
  obtain ⟨t, r, m⟩ := lab
  simp only [LargeEvenLabel.tag] at hl
  subst hl
  simpa [markTag] using h

theorem e6TwoLeaf_chevTwE6 {R : Type} [Group R] {lab : LargeEvenLabel} {n : ℕ}
    (h : CFSG.Blueprint.ChevalleyExceptionalModel R (markTag lab) 2 n) (hl : lab.tag = .twE6) :
    CFSG.Blueprint.ChevalleyExceptionalModel R .twistedE6 2 n := by
  obtain ⟨t, r, m⟩ := lab
  simp only [LargeEvenLabel.tag] at hl
  subst hl
  simpa [markTag] using h

theorem e6TwoLeaf_index_E6
    {G : Type} [Group G] {p f : ℕ} (h : CFSG.Blueprint.ChevalleyExceptionalModel G .E6 p f) :
    ∃ d : TauCeti.ValidLieTypeIndex,
      d.1.characteristic = p ∧
      CFSG.LocalAnalysis.GLTheoremA.KD264Lie.fieldSize d.1 = p ^ f ∧
      (∃ q : TauCeti.PrimePower, d.1 = .E6 q) ∧
      Nonempty (G ≃* (TauCeti.CFSGIndex.lie d).Group) := by
  obtain ⟨hadm, hm⟩ := h
  have hp : p.Prime := hadm.1
  have hf : 1 ≤ f := hadm.2.1
  let q : TauCeti.PrimePower := ⟨p, f, hp, hf⟩
  have hq : q.card = p ^ f := TauCeti.PrimePower.card_def q
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hm
  have hv : (TauCeti.LieTypeIndex.E6 q).Valid := by simp
  obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 q hv K (by rw [hK, hq])
  exact ⟨⟨TauCeti.LieTypeIndex.E6 q, hv⟩, by simp [q],
    by show q.card = p ^ f; rw [hq], ⟨q, rfl⟩, ⟨e.trans b⟩⟩

theorem e6TwoLeaf_index_twE6
    {G : Type} [Group G] {p f : ℕ} (h : CFSG.Blueprint.ChevalleyExceptionalModel G .twistedE6 p f) :
    ∃ d : TauCeti.ValidLieTypeIndex,
      d.1.characteristic = p ∧
      CFSG.LocalAnalysis.GLTheoremA.KD264Lie.fieldSize d.1 = p ^ f ∧
      (∃ q : TauCeti.PrimePower, d.1 = .twistedE6 q) ∧
      Nonempty (G ≃* (TauCeti.CFSGIndex.lie d).Group) := by
  obtain ⟨hadm, hm⟩ := h
  have hp : p.Prime := hadm.1
  have hf : 1 ≤ f := hadm.2.1
  let q : TauCeti.PrimePower := ⟨p, f, hp, hf⟩
  have hq : q.card = p ^ f := TauCeti.PrimePower.card_def q
  obtain ⟨K, _, _, hK, σ, hσ, ⟨e⟩⟩ := hm
  have hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid := by simp
  obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.twistedE6 q hv K (by rw [hK, hq])
    σ (fun x => by rw [hq]; exact hσ x)
  exact ⟨⟨TauCeti.LieTypeIndex.twistedE6 q, hv⟩, by simp [q],
    by show q.card = p ^ f; rw [hq], ⟨q, rfl⟩, ⟨e.trans b⟩⟩

theorem e6TwoLeaf_compLabE6TwoAt_of_mulEquiv
    {untw : Prop} {S S' : Type} [Group S] [Group S'] (e : S ≃* S')
    (h : CompLabE6TwoAt untw S) : CompLabE6TwoAt untw S' := by
  intro b hbmem hbp hb1 K' hK' hK'uniq
  set α : MulAut S := MulAut.congr e.symm b with hα
  have hconj : MulAut.congr e α = b := by
    rw [hα]
    ext y
    simp [MulAut.congr_apply]
  have hαmem : α ∈ CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived S := by
    rw [← CFSG.ComponentClassification.OuterAutomorphisms.mem_innAutDerived_congr e, hconj]
    exact hbmem
  have hαp : α ^ 3 = 1 := by
    apply (MulAut.congr e).injective
    rw [map_pow, map_one, hconj]
    exact hbp
  have hα1 : α ≠ 1 := by
    intro h1
    apply hb1
    rw [← hconj, h1, map_one]
  set K : Subgroup S := K'.map (e.symm : S' →* S) with hK
  have hfix : (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup b).map (e.symm : S' →* S) =
      CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup α := by
    rw [← hconj, CFSG.HardMathSupport.Solomon.Coordinator.LieComp.fixSubgroup_congr e α,
      Subgroup.map_map]
    simp
  have hfix' : (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup α).map (e : S →* S') =
      CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup b := by
    rw [← hfix, Subgroup.map_map]
    simp
  have hKcomp : CFSG.Open.IsComponentOf K
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup α) := by
    rw [← hfix]
    exact CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map e.symm hK'
  have hKuniq : ∀ K'' : Subgroup S,
      CFSG.Open.IsComponentOf K'' (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup α) →
        K'' = K := by
    intro K'' hK''
    have hK''b : CFSG.Open.IsComponentOf (K''.map (e : S →* S'))
        (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup b) := by
      rw [← hfix']
      exact CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map e hK''
    have h1 := hK'uniq (K''.map (e : S →* S')) hK''b
    have h2 : (K''.map (e : S →* S')).map (e.symm : S' →* S) = K'' := by
      rw [Subgroup.map_map]; simp
    have h3 : (K''.map (e : S →* S')).map (e.symm : S' →* S) = K := by
      rw [h1, hK]
    exact h2.symm.trans h3
  obtain ⟨lab, hlab, hhas, hcomp⟩ := h α hαmem hαp hα1 K hKcomp hKuniq
  have hKmap : K.map (e : S →* S') = K' := by
    rw [hK, Subgroup.map_map]
    simp
  let ε : ↥K ≃* ↥K' :=
    (K.equivMapOfInjective (e : S →* S') e.injective).trans (MulEquiv.subgroupCongr hKmap)
  refine ⟨lab, hlab, ?_, ?_⟩
  · unfold GGHasLabel at hhas ⊢
    refine largeEvenRawDatum_mono (fun R' _ I F ⟨ψ⟩ => ?_) hhas
    exact ⟨(QuotientGroup.congr (Subgroup.center ↥K) (Subgroup.center ↥K') ε
      (Subgroup.map_center_eq ε)).symm.trans ψ⟩
  · refine ⟨fun huntw => ⟨(hcomp.1 huntw).1, fun hA => ?_⟩, hcomp.2⟩
    intro hbot
    exact (hcomp.1 huntw).2 hA (by
      apply Subgroup.map_injective (f := (ε : ↥K →* ↥K')) ε.injective
      rw [Subgroup.map_center_eq ε, hbot, Subgroup.map_bot])

section CenterAux

open scoped commutatorElement

theorem e6TwoLeaf_comap_center_eq_center_of_perfect {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Surjective f) (hker : f.ker ≤ Subgroup.center G)
    (hperf : commutator G = ⊤) :
    (Subgroup.center H).comap f = Subgroup.center G := by
  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_comap] at hx
    have hval : ∀ g : G, ⁅x, g⁆ ∈ Subgroup.center G := by
      intro g
      apply hker
      rw [MonoidHom.mem_ker, map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr
        (Subgroup.mem_center_iff.mp hx (f g)).symm
    have hmul : ∀ g h : G, ⁅x, g * h⁆ = ⁅x, g⁆ * ⁅x, h⁆ := by
      intro g h
      have hc : ⁅x, h⁆ ∈ Subgroup.center G := hval h
      have hac : x * h = ⁅x, h⁆ * h * x := by
        rw [commutatorElement_def]; group
      have hab : x * g = ⁅x, g⁆ * g * x := by
        rw [commutatorElement_def]; group
      have hk := Subgroup.mem_center_iff.1 hc
      generalize ⁅x, h⁆ = k at hac hk ⊢
      have e : ⁅x, g * h⁆ * ((g * h) * x) = x * (g * h) := by
        rw [commutatorElement_def]; group
      have e' : x * (g * h) = ⁅x, g⁆ * k * ((g * h) * x) := by
        calc x * (g * h) = (x * g) * h := by group
          _ = ⁅x, g⁆ * g * (x * h) := by rw [hab]; group
          _ = ⁅x, g⁆ * g * (k * h * x) := by rw [hac]
          _ = ⁅x, g⁆ * (g * k) * h * x := by group
          _ = ⁅x, g⁆ * (k * g) * h * x := by rw [hk g]
          _ = ⁅x, g⁆ * k * ((g * h) * x) := by group
      rw [e'] at e
      exact mul_right_cancel e
    let ψ : G →* G :=
      { toFun := fun g => ⁅x, g⁆
        map_one' := by simp [commutatorElement_def]
        map_mul' := hmul }
    have hψker : commutator G ≤ ψ.ker := by
      rw [_root_.commutator_def G]
      rw [Subgroup.commutator_le]
      intro a _ b _
      rw [MonoidHom.mem_ker]
      change ψ ⁅a, b⁆ = 1
      rw [map_commutatorElement ψ a b]
      exact commutatorElement_eq_one_iff_mul_comm.mpr
        (Subgroup.mem_center_iff.mp (hval a) (ψ b)).symm
    rw [hperf] at hψker
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : ⁅x, g⁆ = 1 := hψker (Subgroup.mem_top g)
    exact (commutatorElement_eq_one_iff_mul_comm.mp hg).symm
  · intro x hx
    rw [Subgroup.mem_comap]
    exact Subgroup.map_center_le_center (f := f) hf (Subgroup.mem_map_of_mem f hx)

end CenterAux

end CFSG.StandardType.TablePThreeKG

end
