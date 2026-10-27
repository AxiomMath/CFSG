module

public import CFSG.LocalAnalysis.StandardType.GGFamTwoDExport
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxExc2
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPTwoDMain
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPTwoDRecog
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPTwoDChainO
public import CFSG.ClassicalInvolution.Q3.Q3TWWMinus
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Lie
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Certs
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPD4Rank4
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPD4Rank4All
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TriD4
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TwE6
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Graph.Transfer
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiag
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.PlanesSetup
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
public import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
public import CFSG.RankThree.Lattice.SteinbergBIE6EvenBruhat
public import CFSG.RankThree.Lattice.SteinbergBIE6OrderThreeTools
public import CFSG.RankThree.Lattice.SteinbergBIE6Qplus
public import CFSG.RankThree.PartOne.KE.E7FiveBlock
public import CFSG.RankThree.PartOne.KE.E8D4Family
public import CFSG.RankThree.PartOne.KEXC.Basic
public import CFSG.RankThree.PartOne.TCX.Ree.Perm
public import CFSG.RankThree.PartTwo.Sec8.Item87Proof84

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.RootAut CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.RankThree.Lattice
  CFSG.RankThree.PartOne.KE CFSG.LieType.Steinberg.Adjoint CFSG.ClassicalInvolution.WeakCT
  CFSG.Timmesfeld
open scoped MatrixGroups Matrix

private theorem famTwoDModel_frames_of_kac
    {τ : Tag} (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (K : KacData τ) (hK : K.Facts) {E : List (ℕ × ℕ)} {tp : ℕ → ℕ → List ℕ}
    (hT : IsTreePaths (τ.rank + 1) E tp)
    (hadj : ∀ x y : Option (Fin τ.rank), K.Adj x y ↔ (nodeIdx x, nodeIdx y) ∈ E)
    {cands : List (List ℕ)}
    (hcheck : ((List.range (τ.rank + 1)).sublists.all fun zl =>
      !(fun _ : List ℕ => true) zl ||
        zl.all fun x => cands.any (sameSet (compIdx (τ.rank + 1) tp zl x))) = true)
    (hlt : ∀ c ∈ cands, ∀ w ∈ c, w < τ.rank + 1)
    (hcard : ∀ c ∈ cands, (c.map (idxNode (r := τ.rank))).toFinset.card = c.length)
    {trees : List (List (Option (Fin τ.rank)))}
    (hcount : ∀ c ∈ cands, 4 ≤ c.length →
      kacCount τ K.θ (c.map (idxNode (r := τ.rank))).toFinset = 2 * c.length * (c.length - 1) →
        ∃ P ∈ trees, sameSet c (P.map nodeIdx) = true)
    (htrees : ∀ P ∈ trees, P.Nodup ∧ 4 ≤ P.length ∧
      (∀ c d : Fin P.length, c ≠ d → ¬ edgeD P.length c d → ¬ edgeD P.length d c →
        iform (K.extRoot (P.get c)) (K.extRoot (P.get d)) = 0) ∧
      ∀ c d : Fin P.length, edgeD P.length c d →
        (nodeIdx (P.get c), nodeIdx (P.get d)) ∈ E)
    (hframes : ∀ {F : Type} [Field F] (x y : Option (Fin τ.rank)),
      (nodeIdx x, nodeIdx y) ∈ E →
        ∃ (ρ : SL(3, F) →* ModGL τ F) (σ : Fin 3 → Fin 3 → Fin τ.rank → ℤ),
          CFSG.RankThree.PartOne.KF4.IsA2Frame ρ σ ∧ σ 0 1 = K.extRoot x ∧
            σ 1 2 = K.extRoot y)
    {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {N : ℕ} (hN : N.Prime) (hNL : (N : L) ≠ 0)
    {M : Type*} [CommGroup M]
    (b : Fin τ.rank → Lˣ) (j : KernelComponent (rootCharHom b))
    (χ : Multiplicative (Fin τ.rank → ℤ) →* M) (i : KernelComponent χ)
    (hsel : componentRoots (rootCharHom b) j = componentRoots χ i)
    (h5 : 5 ≤ compRank (componentRoots χ i))
    (hD : (componentRoots χ i).ncard =
      2 * compRank (componentRoots χ i) * (compRank (componentRoots χ i) - 1))
    (hbN : rootDiagUnit τ b ^ N = 1)
    {m : ℕ} (ε : simpleRoots (componentRoots χ i) ≃ Fin m)
    (hCart : ∀ β γ : simpleRoots (componentRoots χ i),
      corootPair (β : Fin τ.rank → ℤ) γ = CFSG.LieType.Universal.Spin.cartanD m (ε β) (ε γ)) :
    ∀ jj kk : Fin m, CFSG.LieType.Universal.Spin.cartanD m jj kk = -1 →
      ∃ θ : SL(3, L) →* ModGL τ L,
        θ.comp (blockSL L 3 2 0 (by omega)) = rootSL2 τ L (ε.symm jj : Fin τ.rank → ℤ) ∧
        θ.comp (blockSL L 3 2 1 (by omega)) = rootSL2 τ L (ε.symm kk : Fin τ.rank → ℤ) := by
  have hsb : simpleRoots (componentRoots (rootCharHom b) j) =
      simpleRoots (componentRoots χ i) := congrArg simpleRoots hsel
  let εb : simpleRoots (componentRoots (rootCharHom b) j) ≃ Fin m :=
  { toFun := fun β => ε ⟨β.1, by rw [← hsb]; exact β.2⟩
    invFun := fun k => ⟨(ε.symm k).1, by rw [hsb]; exact (ε.symm k).2⟩
    left_inv := by intro β; simp
    right_inv := by intro k; simp }
  have hval : ∀ k, Subtype.val (εb.symm k) = Subtype.val (ε.symm k) := fun k => rfl
  have h4b : 4 ≤ compRank (componentRoots (rootCharHom b) j) := by rw [hsel]; omega
  have hnb : (componentRoots (rootCharHom b) j).ncard =
      2 * compRank (componentRoots (rootCharHom b) j) *
        (compRank (componentRoots (rootCharHom b) j) - 1) := by
    rw [hsel]; exact hD
  have hCartb : ∀ β γ : simpleRoots (componentRoots (rootCharHom b) j),
      corootPair (β : Fin τ.rank → ℤ) γ =
        CFSG.LieType.Universal.Spin.cartanD m (εb β) (εb γ) := by
    intro β γ
    simpa [εb] using hCart ⟨β.1, by rw [← hsb]; exact β.2⟩ ⟨γ.1, by rw [← hsb]; exact γ.2⟩
  intro jj kk hjk
  obtain ⟨θ, hθ0, hθ1⟩ := CompsPTwoDMain.exists_dFrames hτ K hK hT hadj hcheck hlt hcard hcount
    htrees hframes S hN hNL hbN j h4b hnb εb hCartb L jj kk hjk
  refine ⟨θ, ?_, ?_⟩
  · rw [hθ0, hval jj]
  · rw [hθ1, hval kk]

private theorem famTwoDModel_frames_dispatch
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {N : ℕ} (hN : N.Prime) (hNL : (N : L) ≠ 0)
    {M : Type*} [CommGroup M]
    (b : Fin τ.rank → Lˣ) (j : KernelComponent (rootCharHom b))
    (χ : Multiplicative (Fin τ.rank → ℤ) →* M) (i : KernelComponent χ)
    (hsel : componentRoots (rootCharHom b) j = componentRoots χ i)
    (h5 : 5 ≤ compRank (componentRoots χ i))
    (hD : (componentRoots χ i).ncard =
      2 * compRank (componentRoots χ i) * (compRank (componentRoots χ i) - 1))
    (hbN : rootDiagUnit τ b ^ N = 1)
    {m : ℕ} (ε : simpleRoots (componentRoots χ i) ≃ Fin m)
    (hCart : ∀ β γ : simpleRoots (componentRoots χ i),
      corootPair (β : Fin τ.rank → ℤ) γ = CFSG.LieType.Universal.Spin.cartanD m (ε β) (ε γ)) :
    ∀ jj kk : Fin m, CFSG.LieType.Universal.Spin.cartanD m jj kk = -1 →
      ∃ θ : SL(3, L) →* ModGL τ L,
        θ.comp (blockSL L 3 2 0 (by omega)) = rootSL2 τ L (ε.symm jj : Fin τ.rank → ℤ) ∧
        θ.comp (blockSL L 3 2 1 (by omega)) = rootSL2 τ L (ε.symm kk : Fin τ.rank → ℤ) := by
  rcases hτ with hE6 | hE7 | hE8
  · subst τ
    exact famTwoDModel_frames_of_kac (Or.inr (Or.inl rfl)) kacE6 facts_E6 e6_tree e6_adj e6_check
      e6_lt e6_card e6_dcount e6_dtrees (fun {F} _ x y h => e6_frames x y h) S hN hNL b j χ i
      hsel h5 hD hbN ε hCart
  · subst τ
    exact famTwoDModel_frames_of_kac (Or.inr (Or.inr (Or.inl rfl))) kacE7 facts_E7 e7_tree e7_adj
      e7_check e7_lt e7_card e7_dcount e7_dtrees (fun {F} _ x y h => e7_frames x y h) S hN hNL b j
      χ i hsel h5 hD hbN ε hCart
  · subst τ
    exact famTwoDModel_frames_of_kac (Or.inr (Or.inr (Or.inr rfl))) kacE8 facts_E8 e8_tree e8_adj
      e8_check e8_lt e8_card e8_dcount e8_dtrees (fun {F} _ x y h => e8_frames x y h) S hN hNL b j
      χ i hsel h5 hD hbN ε hCart

private theorem famTwoDModel_lieModel_of_export
    {τ : Tag} (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {M : Type*} [CommGroup M]
    (χ : Multiplicative (Fin τ.rank → ℤ) →* M) (i : KernelComponent χ)
    {r e m : ℕ} [Fact r.Prime] [CharP L r] (hm5 : 5 ≤ m)
    (z : ModGL τ L) (ε : simpleRoots (componentRoots χ i) ≃ Fin m)
    (D : GenFixedRootDatum τ r L (SpanQuot (componentRoots χ i)))
    (hq : S.D.q = r ^ e) (he : 1 ≤ e) (hDe : D.e = e)
    (hRC : (rationalComponentM S.ρ S.Γ χ i).map (MulAut.conj z⁻¹).toMonoidHom = D.orbitGroup)
    (hDs : D.simpleRootsJ = ((simpleRoots (componentRoots χ i) :
      Finset (Fin τ.rank → ℤ)) : Set (Fin τ.rank → ℤ)))
    (hCart : ∀ β γ : simpleRoots (componentRoots χ i),
      corootPair (β : Fin τ.rank → ℤ) γ = CFSG.LieType.Universal.Spin.cartanD m (ε β) (ε γ))
    (hfix : ∀ k : Fin m, k.val + 2 < m →
      D.θ (toReal (ε.symm k : Fin τ.rank → ℤ)) = toReal (ε.symm k : Fin τ.rank → ℤ))
    (hswap : ∀ k l : Fin m, k.val + 2 = m → l.val + 1 = m →
      D.θ (toReal (ε.symm k : Fin τ.rank → ℤ)) = toReal (ε.symm l : Fin τ.rank → ℤ) ∧
      D.θ (toReal (ε.symm l : Fin τ.rank → ℤ)) = toReal (ε.symm k : Fin τ.rank → ℤ))
    (Q : ℕ → ℕ → Prop) (hrec : CompsPTwoDRecog.TwoDChainRecogAll L Q)
    (hQ : Q (ringChar L) S.D.q)
    (hframes : ∀ jj kk : Fin m, CFSG.LieType.Universal.Spin.cartanD m jj kk = -1 →
      ∃ θ : SL(3, L) →* ModGL τ L,
        θ.comp (blockSL L 3 2 0 (by omega)) = rootSL2 τ L (ε.symm jj : Fin τ.rank → ℤ) ∧
        θ.comp (blockSL L 3 2 1 (by omega)) = rootSL2 τ L (ε.symm kk : Fin τ.rank → ℤ)) :
    ∃ e : ℕ, ringChar L ^ e = S.D.q ∧
      LieModel (↥(rationalComponentM S.ρ S.Γ χ i) ⧸
        Subgroup.center ↥(rationalComponentM S.ρ S.Γ χ i))
        .POmegaMinus m (ringChar L) e := by
  classical
  have hrc : ringChar L = r := ringChar.eq L r
  have hQ' : Q r (r ^ e) := by
    have h := hQ
    rw [hrc, hq] at h
    exact h
  have hΨ : IsRootComponent (componentRoots χ i) := isRootComponent_componentRoots i
  have hsl : ∀ β ∈ componentRoots χ i, iform β β = 2 := fun β hβ => by
    rw [← dotProduct_mulVec_eq_iform]
    exact rootForm_self hτ (hΨ.isRoot β hβ)
  have hbroot : ∀ j : Fin m, IsRoot τ (ε.symm j : Fin τ.rank → ℤ) := fun j =>
    simpleRoots_isRoot (ε.symm j).2
  have hbinj : Function.Injective (fun j : Fin m => (ε.symm j : Fin τ.rank → ℤ)) :=
    fun j k h => ε.symm.injective (Subtype.ext h)
  have hG : ∀ j k : Fin m, iform (ε.symm j : Fin τ.rank → ℤ) (ε.symm k) =
      CFSG.LieType.Universal.Spin.cartanD m j k := by
    intro j k
    have h := hCart (ε.symm j) (ε.symm k)
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
    rw [← h]
    exact (CompsPTwoDBase.corootPair_eq_iform (hbroot j)
      (hsl _ (simpleRoots_subset (ε.symm j).2)) _).symm
  have hrange : Set.range (fun j : Fin m => (ε.symm j : Fin τ.rank → ℤ)) =
      ((simpleRoots (componentRoots χ i) : Finset (Fin τ.rank → ℤ)) :
        Set (Fin τ.rank → ℤ)) := by
    ext β
    constructor
    · rintro ⟨j, rfl⟩
      exact (ε.symm j).2
    · intro hβ
      exact ⟨ε ⟨β, hβ⟩, by simp⟩
  have hsw := hswap ⟨m - 2, by omega⟩ ⟨m - 1, by omega⟩ (by simp only [Fin.val_mk]; omega)
    (by simp only [Fin.val_mk]; omega)
  have hlie := CFSG.LocalAnalysis.GLTheoremA.KD264Lie.ExcUntw.lieModel_orbitGroup_of_datum_four
    hτ D (by omega) (by rw [hDe]; exact hrec r e m he hm5 hQ')
    (fun j : Fin m => (ε.symm j : Fin τ.rank → ℤ)) hbroot hbinj hG (hDs.trans hrange.symm) hfix
    hsw.1 hsw.2 hframes
  let eR : ↥(rationalComponentM S.ρ S.Γ χ i) ≃* ↥D.orbitGroup :=
    ((rationalComponentM S.ρ S.Γ χ i).equivMapOfInjective
      (MulAut.conj z⁻¹).toMonoidHom (MulAut.conj z⁻¹).injective).trans
      (MulEquiv.subgroupCongr hRC)
  have hqiso : ↥(rationalComponentM S.ρ S.Γ χ i) ⧸
      Subgroup.center ↥(rationalComponentM S.ρ S.Γ χ i) ≃*
      ↥D.orbitGroup ⧸ Subgroup.center ↥D.orbitGroup :=
    QuotientGroup.congr _ _ eR (Subgroup.map_center_eq eR)
  have hmodel : LieModel (↥(rationalComponentM S.ρ S.Γ χ i) ⧸
      Subgroup.center ↥(rationalComponentM S.ρ S.Γ χ i))
      .POmegaMinus m r D.e :=
    LieModel.of_mulEquiv hqiso.symm hlie
  refine ⟨e, ?_, ?_⟩
  · rw [hrc, hq]
  · rw [hrc]
    exact hDe ▸ hmodel

theorem fam_lieModel_rationalComponent_of_twoD_rank
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀) (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {M : Type*} [CommGroup M]
    (χ : Multiplicative (Fin τ.rank → ℤ) →* M) (i : KernelComponent χ)
    (hker : ∀ γ ∈ kernelRoots χ, S.ρ γ ∈ kernelRoots χ)
    (hρΨ : ∀ γ ∈ componentRoots χ i, S.ρ γ ∈ componentRoots χ i)
    (h5 : 5 ≤ compRank (componentRoots χ i))
    (hD : (componentRoots χ i).ncard =
      2 * compRank (componentRoots χ i) * (compRank (componentRoots χ i) - 1))
    (hout : ¬ twistInner (componentRoots χ i) (S.ρ : (Fin τ.rank → ℤ) → _))
    (b : Fin τ.rank → Lˣ) (j : KernelComponent (rootCharHom b))
    (hsel : componentRoots (rootCharHom b) j = componentRoots χ i)
    {N : ℕ} (hN : N.Prime) (hNL : (N : L) ≠ 0)
    (hbN : rootDiagUnit τ b ^ N = 1)
    (Q : ℕ → ℕ → Prop) (hrec : CompsPTwoDRecog.TwoDChainRecogAll L Q)
    (hQ : Q (ringChar L) S.D.q) :
    ∃ e : ℕ, ringChar L ^ e = S.D.q ∧
      LieModel (↥(rationalComponentM S.ρ S.Γ χ i) ⧸
        Subgroup.center ↥(rationalComponentM S.ρ S.Γ χ i))
        .POmegaMinus (compRank (componentRoots χ i)) (ringChar L) e := by
  classical
  obtain ⟨r, e, m, hr, hchar, hm5, z, ε, D, hq, he, hDe, hRC, hDs, hCart, hfix, hswap⟩ :=
    fam_exists_twoD_export S (Or.inr hτ) χ i hker hρΨ h5 hD hout b j hsel
  haveI := hr
  haveI := hchar
  obtain ⟨e', he', hmodel⟩ :=
    famTwoDModel_lieModel_of_export (Or.inr hτ) S χ i hm5 z ε D hq he hDe hRC hDs hCart hfix
      hswap Q hrec hQ
      (famTwoDModel_frames_dispatch hτ S hN hNL b j χ i hsel h5 hD hbN ε hCart)
  have hΨ : IsRootComponent (componentRoots χ i) := isRootComponent_componentRoots i
  have hcardΔ : (simpleRoots (componentRoots χ i)).card = m := by
    rw [← Fintype.card_coe, Fintype.card_congr ε, Fintype.card_fin]
  have hmrank : m = compRank (componentRoots χ i) := by
    rw [compRank_eq_card hΨ, hcardΔ]
  refine ⟨e', he', ?_⟩
  rw [← hmrank]
  exact hmodel

theorem fam_lieModel_rationalComponent_of_twoD
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀) (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {M : Type*} [CommGroup M]
    (χ : Multiplicative (Fin τ.rank → ℤ) →* M) (i : KernelComponent χ)
    (hker : ∀ γ ∈ kernelRoots χ, S.ρ γ ∈ kernelRoots χ)
    (hρΨ : ∀ γ ∈ componentRoots χ i, S.ρ γ ∈ componentRoots χ i)
    (h5 : 5 ≤ compRank (componentRoots χ i))
    (hD : (componentRoots χ i).ncard =
      2 * compRank (componentRoots χ i) * (compRank (componentRoots χ i) - 1))
    (hout : ¬ twistInner (componentRoots χ i) (S.ρ : (Fin τ.rank → ℤ) → _))
    (b : Fin τ.rank → Lˣ) (j : KernelComponent (rootCharHom b))
    (hsel : componentRoots (rootCharHom b) j = componentRoots χ i)
    {N : ℕ} (hN : N.Prime) (hNL : (N : L) ≠ 0)
    (hbN : rootDiagUnit τ b ^ N = 1)
    (Q : ℕ → ℕ → Prop) (hrec : CompsPTwoDRecog.TwoDChainRecogAll L Q)
    (hQ : Q (ringChar L) S.D.q) :
    ∃ m e : ℕ, ringChar L ^ e = S.D.q ∧
      LieModel (↥(rationalComponentM S.ρ S.Γ χ i) ⧸
        Subgroup.center ↥(rationalComponentM S.ρ S.Γ χ i))
        .POmegaMinus m (ringChar L) e := by
  obtain ⟨e, he, h⟩ :=
    fam_lieModel_rationalComponent_of_twoD_rank S hτ χ i hker hρΨ h5 hD hout b j hsel hN hNL hbN
      Q hrec hQ
  exact ⟨compRank (componentRoots χ i), e, he, h⟩

end CFSG.StandardType.TableCRes
