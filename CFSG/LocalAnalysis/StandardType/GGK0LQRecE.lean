module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154NonCfgE7
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGReverseMarkingRaw
public import CFSG.ClassicalInvolution.Q3.Q3TWWMinus
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Lie
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPD4Rank4
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPD4Rank4All
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TriD4
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TwE6
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaPlusIota
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphUnitaryNormal
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2RowNeighbour
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SixRevCommBasic
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14LUUnitary
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14ModelUnitary
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14PartnerCoset
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14SpAMain
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindUnitaryGlobal
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphFix
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphLevi
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaBMain
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaBRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaBShape
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaCTClass
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaCTRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaRowStepOneMinus
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowOmegaClass
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowOmegaUnitaryRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowUnitaryCover
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotInvolutionTwoPartEvenInner
public import CFSG.RankThree.PartOne.KEXC.Basic
public import CFSG.RankThree.PartOne.TCX.Ree.Perm

public section

namespace CFSG.StandardType.GGK0LQ

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.PartOne.KE CFSG.Timmesfeld
  CFSG.ClassicalInvolution.WeakCT CFSG.LocalAnalysis.GLTheoremA.K155X
open scoped MatrixGroups Matrix

private theorem lk0xlqrece_hasLabel_of_lieModel_E7 {X : Type} [Group X] {N : ℕ}
    (h : LieModel X .E7 0 2 N) : GGHasLabel ⟨.E7, 0, N⟩ X := by
  have hc : ChevalleyExceptionalModel X .E7 2 N := h.chevalleyExceptionalModel (by decide)
  obtain ⟨-, h⟩ := hc
  exact recipeChevalley_of_untwistedChevalleyModel .E7 h

private theorem lk0xlqrece_hasLabel_of_lieModel_E6 {X : Type} [Group X] {N : ℕ}
    (h : LieModel X .E6 0 2 N) : GGHasLabel ⟨.E6, 0, N⟩ X := by
  have hc : ChevalleyExceptionalModel X .E6 2 N := h.chevalleyExceptionalModel (by decide)
  obtain ⟨-, h⟩ := hc
  exact recipeChevalley_of_untwistedChevalleyModel .E6 h

private theorem lk0xlqrece_innerModel_E6
    {τ : Tag} (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type}
    [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hf : 0 < f) (hK : Nat.card K = p ^ f)
    {ι : Type} [Fintype ι] (β : ι → Fin τ.rank → ℤ) (hroot : ∀ b, IsRoot τ (β b))
    (l : Fin 6 → ι)
    (hgram : ∀ i j : Fin 6, i ≠ j → ¬ edgeE 6 i j → ¬ edgeE 6 j i →
      iform (β (l i)) (β (l j)) = 0)
    (hframe : ∀ i j : Fin 6, edgeE 6 i j → ∃ θ : SL(3, K) →* ModGL τ K,
      θ.comp (blockSL K 3 2 0 (by omega)) = rootSL2 τ K (β (l i)) ∧
        θ.comp (blockSL K 3 2 1 (by omega)) = rootSL2 τ K (β (l j))) :
    commutator ↥(rootSpan τ K (rootsOfFam β (Set.range l))) = ⊤ ∧
      LieModel (↥(rootSpan τ K (rootsOfFam β (Set.range l))) ⧸
        Subgroup.center ↥(rootSpan τ K (rootsOfFam β (Set.range l)))) .E6 0 p f := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨U, ρ, hgen, hcomm, hρ, hψ⟩ := weakCT_data hτ β hroot l (edgeE 6) hgram hframe
  have hadm : CFSG.Open.StatedLieAdmissible .E6 0 p f := ⟨hp, hf, rfl⟩
  obtain ⟨-, -, -, hqs, -, hmodel⟩ := weakCT_e6_of_frame p f hadm hK U hgen hcomm hρ hψ
  exact ⟨hqs.1.commutator_eq_top, hmodel⟩

private theorem lk0xlqrece_rationalComponent_e6Model
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {ta : Fin τ.rank → Lˣ}
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hT : rootDiagUnit τ ta ∈ S.D.torus) (i : KernelComponent (rootCharHom ta))
    (hinner : twistInner (componentRoots (rootCharHom ta) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom ta) i)]))
    {ι : Type} [Fintype ι] (β : ι → Fin τ.rank → ℤ)
    (hroot : ∀ b, IsRoot τ (β b)) (l : Fin 6 → ι)
    (hroots : componentRoots (rootCharHom ta) i = rootsOfFam β (Set.range l))
    (hgram : ∀ i j : Fin 6, i ≠ j → ¬ edgeE 6 i j → ¬ edgeE 6 j i →
      iform (β (l i)) (β (l j)) = 0)
    (hframe : ∀ {F : Type} [Field F] (i j : Fin 6), edgeE 6 i j → ∃ θ : SL(3, F) →* ModGL τ F,
      θ.comp (blockSL F 3 2 0 (by omega)) = rootSL2 τ F (β (l i)) ∧
        θ.comp (blockSL F 3 2 1 (by omega)) = rootSL2 τ F (β (l j)))
    {r e : ℕ} (hr : r.Prime) (he : 0 < e) (hq : S.D.q = r ^ e) :
    LieModel
      (↥(rationalComponent S.ρ S.Γ (rootCharHom ta) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom ta) i))
      .E6 0 r (e * componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i)) := by
  classical
  obtain ⟨hs0, -, -⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i) with hsdef
  have hes : 0 < e * s := Nat.mul_pos he hs0
  obtain ⟨σ, hfin, hcard, f, hf1, hker, hf2⟩ := exists_inner_cover S hT i hinner
  haveI : Finite ↥(fixSubfield σ) := hfin
  have hcard' : Nat.card ↥(fixSubfield σ) = r ^ (e * s) := by rw [hcard, hq, ← pow_mul]
  have hcomp : componentRootSpan (fixSubfield σ) (rootCharHom ta) i =
      rootSpan τ (fixSubfield σ) (rootsOfFam β (Set.range l)) := by
    show rootSpan τ (fixSubfield σ) (componentRoots (rootCharHom ta) i) = _
    rw [hroots]
  obtain ⟨hperf, hmod⟩ := lk0xlqrece_innerModel_E6 hτ hr hes hcard' β hroot l hgram
    (hframe (F := ↥(fixSubfield σ)))
  rw [← hcomp] at hperf hmod
  have hCperf : Group.IsPerfect ↥(componentRootSpan (fixSubfield σ) (rootCharHom ta) i) :=
    Group.isPerfect_def.2 hperf
  have hRf : f.range = rationalComponent S.ρ S.Γ (rootCharHom ta) i :=
    le_antisymm (hf2 (Subgroup.isPerfect_iff.1 hCperf)) hf1
  let g : ↥(componentRootSpan (fixSubfield σ) (rootCharHom ta) i) →*
      ↥(rationalComponent S.ρ S.Γ (rootCharHom ta) i) :=
    f.codRestrict _ (fun c => hRf ▸ ⟨c, rfl⟩)
  have hgsurj : Function.Surjective g := by
    rintro ⟨x, hx⟩
    obtain ⟨c, hc⟩ : x ∈ f.range := hRf ▸ hx
    exact ⟨c, Subtype.ext hc⟩
  have hgker : g.ker ≤ Subgroup.center
      ↥(componentRootSpan (fixSubfield σ) (rootCharHom ta) i) := by
    intro c hc
    apply hker
    rw [MonoidHom.mem_ker] at hc ⊢
    exact congrArg Subtype.val hc
  obtain ⟨e1⟩ := nonempty_centralQuotient_mulEquiv hperf g hgsurj hgker
  exact LieModel.of_mulEquiv e1 hmod

theorem lq_rec_E7
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p₀ p : ℕ} (S : LangSetup Tag.E8 L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0)
    {a : Fin Tag.E8.rank → Lˣ} (hT : rootDiagUnit Tag.E8 a ∈ S.D.torus)
    (hTp : rootDiagUnit Tag.E8 a ^ p = 1) (i : KernelComponent (rootCharHom a))
    (h7 : compRank (componentRoots (rootCharHom a) i) = 7)
    (hn : (componentRoots (rootCharHom a) i).ncard = 126)
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E8.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]))
    {N : ℕ} (hN : S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 2 ^ N) :
    GGHasLabel ⟨.E7, 0, N⟩
      (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
  classical
  have h2 : ringChar L = 2 := ringChar.eq L 2
  have h6 : 6 ≤ compRank (componentRoots (rootCharHom a) i) := by omega
  have hn' : (componentRoots (rootCharHom a) i).ncard =
      eRootCount (compRank (componentRoots (rootCharHom a) i)) := by
    rw [hn, h7]
    rfl
  obtain ⟨v, n, l, -, -, hrk, hroots, hnon, hE⟩ :=
    l154_exists_tree_of_class_rank kacE8 facts_E8 e8_tree e8_adj e8_check e8_lt e8_card edgeE 6
      eRootCount e8_ecount e8_etrees (fun n => n = 6 ∨ n = 7 ∨ n = 8) e8_elen S hp hpL hTp i h6 hn'
  have hn7 : n = 7 := by rw [← hrk, h7]
  subst hn7
  obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
  have hr2 : r = 2 := (ringChar.eq L r).symm.trans h2
  have hroots' : componentRoots (rootCharHom a) i =
      rootsOfFam (fun x => v • kacE8.extRoot x) (Set.range l) := by
    rw [hroots, l154_smul_image_rootsOf_eq]
  have hmodel := l154_rationalComponent_e7Model S (Or.inr (Or.inr (Or.inr rfl))) hT i hinner
    (fun x => v • kacE8.extRoot x) (fun b => IsRoot.smul (kacE8.isRoot_extRoot b) v) l hroots'
    (fun c d hcd h1 h2 => by
      show iform (v • kacE8.extRoot (l c)) (v • kacE8.extRoot (l d)) = 0
      rw [iform_smul]
      exact hnon c d hcd h1 h2)
    (fun {F} _ c d hcd =>
      treeFrames kacE8 (fun {F} _ x y h => e8_frames x y h) v l (edgeE 7) hE (F := F) c d hcd)
    hr he hq
  subst hr2
  have hes : e * componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = N := by
    rw [hq, ← pow_mul] at hN
    exact Nat.pow_right_injective (by norm_num) hN
  rw [hes] at hmodel
  exact lk0xlqrece_hasLabel_of_lieModel_E7 hmodel

theorem lq_rec_E6
    {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8)
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0)
    {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (hTp : rootDiagUnit τ a ^ p = 1) (i : KernelComponent (rootCharHom a))
    (h6 : compRank (componentRoots (rootCharHom a) i) = 6)
    (hn : (componentRoots (rootCharHom a) i).ncard = 72)
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]))
    {N : ℕ} (hN : S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 2 ^ N) :
    GGHasLabel ⟨.E6, 0, N⟩
      (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
  classical
  obtain rfl | rfl := hτ
  ·
    have h2 : ringChar L = 2 := ringChar.eq L 2
    have hn' : (componentRoots (rootCharHom a) i).ncard =
        eRootCount (compRank (componentRoots (rootCharHom a) i)) := by
      rw [hn, h6]
      rfl
    have h6le : 6 ≤ compRank (componentRoots (rootCharHom a) i) := by omega
    obtain ⟨v, n, l, -, -, hrk, hroots, hnon, hE⟩ :=
      l154_exists_tree_of_class_rank kacE7 facts_E7 e7_tree e7_adj e7_check e7_lt e7_card edgeE 6
        eRootCount e7_ecount e7_etrees (fun n => n = 6 ∨ n = 7 ∨ n = 8) e7_elen S hp hpL hTp i h6le
        hn'
    have hn6 : n = 6 := by rw [← hrk, h6]
    subst hn6
    obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
    have hr2 : r = 2 := (ringChar.eq L r).symm.trans h2
    have hroots' : componentRoots (rootCharHom a) i =
        rootsOfFam (fun x => v • kacE7.extRoot x) (Set.range l) := by
      rw [hroots, l154_smul_image_rootsOf_eq]
    have hmodel := lk0xlqrece_rationalComponent_e6Model S (Or.inr (Or.inr (Or.inl rfl))) hT i
      hinner (fun x => v • kacE7.extRoot x) (fun b => IsRoot.smul (kacE7.isRoot_extRoot b) v) l
      hroots'
      (fun c d hcd h1 h2 => by
        show iform (v • kacE7.extRoot (l c)) (v • kacE7.extRoot (l d)) = 0
        rw [iform_smul]
        exact hnon c d hcd h1 h2)
      (fun {F} _ c d hcd =>
        treeFrames kacE7 (fun {F} _ x y h => e7_frames x y h) v l (edgeE 6) hE (F := F) c d hcd)
      hr he hq
    subst hr2
    have hes : e * componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = N := by
      rw [hq, ← pow_mul] at hN
      exact Nat.pow_right_injective (by norm_num) hN
    rw [hes] at hmodel
    exact lk0xlqrece_hasLabel_of_lieModel_E6 hmodel
  ·
    have h2 : ringChar L = 2 := ringChar.eq L 2
    have hn' : (componentRoots (rootCharHom a) i).ncard =
        eRootCount (compRank (componentRoots (rootCharHom a) i)) := by
      rw [hn, h6]
      rfl
    have h6le : 6 ≤ compRank (componentRoots (rootCharHom a) i) := by omega
    obtain ⟨v, n, l, -, -, hrk, hroots, hnon, hE⟩ :=
      l154_exists_tree_of_class_rank kacE8 facts_E8 e8_tree e8_adj e8_check e8_lt e8_card edgeE 6
        eRootCount e8_ecount e8_etrees (fun n => n = 6 ∨ n = 7 ∨ n = 8) e8_elen S hp hpL hTp i h6le
        hn'
    have hn6 : n = 6 := by rw [← hrk, h6]
    subst hn6
    obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
    have hr2 : r = 2 := (ringChar.eq L r).symm.trans h2
    have hroots' : componentRoots (rootCharHom a) i =
        rootsOfFam (fun x => v • kacE8.extRoot x) (Set.range l) := by
      rw [hroots, l154_smul_image_rootsOf_eq]
    have hmodel := lk0xlqrece_rationalComponent_e6Model S (Or.inr (Or.inr (Or.inr rfl))) hT i
      hinner (fun x => v • kacE8.extRoot x) (fun b => IsRoot.smul (kacE8.isRoot_extRoot b) v) l
      hroots'
      (fun c d hcd h1 h2 => by
        show iform (v • kacE8.extRoot (l c)) (v • kacE8.extRoot (l d)) = 0
        rw [iform_smul]
        exact hnon c d hcd h1 h2)
      (fun {F} _ c d hcd =>
        treeFrames kacE8 (fun {F} _ x y h => e8_frames x y h) v l (edgeE 6) hE (F := F) c d hcd)
      hr he hq
    subst hr2
    have hes : e * componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = N := by
      rw [hq, ← pow_mul] at hN
      exact Nat.pow_right_injective (by norm_num) hN
    rw [hes] at hmodel
    exact lk0xlqrece_hasLabel_of_lieModel_E6 hmodel

end CFSG.StandardType.GGK0LQ

end
