module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154NonCfgRank4C
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcTD4D4
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6RatLabelOuterD
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ExcTwD4Layer
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ExcD4Action
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExcD4
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExcE6
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24D4T2Outer
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.OuterE6
public import CFSG.RankThree.PartOne.KD4L.TriStd
public import CFSG.LieType.Chevalley.E7SupportedBruhat
public import CFSG.ClassicalInvolution.Q3.Q3TWWMinus
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Lie
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPD4Rank4
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPD4Rank4All
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TriD4
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TwE6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154NonCfgClass
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154NonCfgRank4
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

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KE6 CFSG.RankThree.PartOne.KD4T
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.RankThree.PartOne.KD4L CFSG.LocalAnalysis.GLTheoremA.K155X CFSG.StandardType.TablePThreeKG
open CFSG.RankThree.PartOne.KE (twistedFixedPoints mem_twistedFixedPoints frobenius_canonicalRep
  d4Nodes)

open CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsPD4Layers

private theorem lk0xlqd4tw_cartan_inv {π : Equiv.Perm (Fin Tag.E6.rank)} (hπ : IsD4LeafPerm π) :
    ∀ j m : Fin Tag.E6.rank, 1 ≤ j.val → j.val ≤ 4 → 1 ≤ m.val → m.val ≤ 4 →
      Tag.E6.cartan (π j) (π m) = Tag.E6.cartan j m := by
  rcases hπ with rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | decide +kernel
    | (intro j m h1 h2 h3 h4
       fin_cases j <;> fin_cases m <;>
         first | decide +kernel | (exfalso; revert h1 h2 h3 h4; decide +kernel))

private theorem lk0xlqd4tw_norm_simple
    {π : Equiv.Perm (Fin Tag.E6.rank)} (hπ : IsD4LeafPerm π)
    {j : Fin Tag.E6.rank} (hj : j ∈ d4Nodes Tag.E6) {x : Fin Tag.E6.rank → ℤ}
    (hx : ∀ k, k ∉ d4Nodes Tag.E6 → x k = 0) :
    permLattice π (simple Tag.E6 j • x) = simple Tag.E6 (π j) • permLattice π x := by
  have hcart := lk0xlqd4tw_cartan_inv hπ
  have hj' : 1 ≤ j.val ∧ j.val ≤ 4 := hj
  have hsum : ∑ k, Tag.E6.cartan (π j) k * permLattice π x k =
      ∑ k, Tag.E6.cartan j k * x k := by
    rw [← Equiv.sum_comp π (fun k => Tag.E6.cartan (π j) k * permLattice π x k)]
    refine Finset.sum_congr rfl fun m _ => ?_
    by_cases hm : m ∈ d4Nodes Tag.E6
    · have hm' : 1 ≤ m.val ∧ m.val ≤ 4 := hm
      simp only [permLattice, Function.comp_apply, Equiv.symm_apply_apply,
        hcart j m hj'.1 hj'.2 hm'.1 hm'.2]
    · simp only [permLattice, Function.comp_apply, Equiv.symm_apply_apply, hx m hm, mul_zero]
  have hlin : ∀ (y z : Fin Tag.E6.rank → ℤ) (c : ℤ),
      permLattice π (y - c • z) = permLattice π y - c • permLattice π z := fun y z c => rfl
  rw [simple_smul, simple_smul]
  unfold reflect
  rw [hlin, hsum, permLattice_single]

private theorem lk0xlqd4tw_simple_apply
    {j : Fin Tag.E6.rank} (hj : j ∈ d4Nodes Tag.E6)
    (x : Fin Tag.E6.rank → ℤ) {k : Fin Tag.E6.rank} (hk : k ∉ d4Nodes Tag.E6) :
    (simple Tag.E6 j • x) k = x k := by
  rw [simple_smul]
  unfold reflect
  have hkj : k ≠ j := fun h => hk (by rw [h]; exact hj)
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_of_ne hkj, mul_zero,
    sub_zero]

private theorem lk0xlqd4tw_norm
    {π : Equiv.Perm (Fin Tag.E6.rank)} (hπ : IsD4LeafPerm π)
    {u : WeylGroup Tag.E6} (hu : u ∈ parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6)) :
    ∃ u' ∈ parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6), ∀ x : Fin Tag.E6.rank → ℤ,
      ((∀ k, k ∉ d4Nodes Tag.E6 → x k = 0) ↔ (∀ k, k ∉ d4Nodes Tag.E6 → (u • x) k = 0)) ∧
      ((∀ k, k ∉ d4Nodes Tag.E6 → x k = 0) → permLattice π (u • x) = u' • permLattice π x) := by
  unfold parabolicWeylGroup at hu ⊢
  induction hu using Subgroup.closure_induction with
  | mem w hw =>
    obtain ⟨j, hj, rfl⟩ := hw
    refine ⟨simple Tag.E6 (π j), Subgroup.subset_closure ⟨π j, hπ.mem_d4Set hj, rfl⟩,
      fun x => ⟨⟨fun hx k hk => ?_, fun hx k hk => ?_⟩,
        fun hx => lk0xlqd4tw_norm_simple hπ hj hx⟩⟩
    · rw [lk0xlqd4tw_simple_apply hj x hk]
      exact hx k hk
    · rw [← lk0xlqd4tw_simple_apply hj x hk]
      exact hx k hk
  | one =>
    exact ⟨1, one_mem _, fun x => by simp⟩
  | mul a b _ _ ha hb =>
    obtain ⟨a', ha', haa⟩ := ha
    obtain ⟨b', hb', hbb⟩ := hb
    refine ⟨a' * b', mul_mem ha' hb', fun x => ⟨?_, fun hx => ?_⟩⟩
    · rw [mul_smul]
      exact (hbb x).1.trans (haa (b • x)).1
    · rw [mul_smul a b x, (haa (b • x)).2 ((hbb x).1.mp hx), (hbb x).2 hx, mul_smul a' b']
  | inv a _ ha =>
    obtain ⟨a', ha', haa⟩ := ha
    refine ⟨a'⁻¹, inv_mem ha', fun x => ⟨?_, fun hx => ?_⟩⟩
    · have h := (haa (a⁻¹ • x)).1
      rw [smul_inv_smul] at h
      exact h.symm
    · have hy : ∀ k, k ∉ d4Nodes Tag.E6 → (a⁻¹ • x) k = 0 := by
        have h := (haa (a⁻¹ • x)).1
        rw [smul_inv_smul] at h
        exact h.mpr hx
      have h := (haa (a⁻¹ • x)).2 hy
      rw [smul_inv_smul] at h
      exact (eq_inv_smul_iff.2 h.symm)

theorem lk0xlqd4tw_pi_sq
    {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup .E6 L p)
    {a : Fin Tag.E6.rank → Lˣ} (i : KernelComponent (rootCharHom a)) (v : WeylGroup .E6)
    (hΨ : componentRoots (rootCharHom a) i =
      (fun α => v • α) '' parabolicRoots .E6 (d4Nodes .E6))
    (hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i)
    (h2 : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[2]))
    {u : WeylGroup Tag.E6} (hu : u ∈ parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6))
    {πJ : Equiv.Perm (Fin Tag.E6.rank)} (hleaf : IsD4LeafPerm πJ)
    (hθ' : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      v⁻¹ • S.ρ (v • α) = u • permLattice πJ α) :
    πJ * πJ ≠ 1 := by
  intro h1
  apply h2
  obtain ⟨u', hu', hnorm⟩ := lk0xlqd4tw_norm hleaf hu
  refine ⟨v * (u * u') * v⁻¹, hΨ ▸ conj_mem_closure_rootReflection v (mul_mem hu hu'), ?_⟩
  intro γ hγ
  obtain ⟨α, hα, rfl⟩ :=
    (hΨ ▸ hγ : γ ∈ (fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6))
  have hρβ : ∀ β ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      S.ρ (v • β) = v • (u • permLattice πJ β) := fun β hβ => by
    rw [← hθ' β hβ, smul_inv_smul]
  have hβ : u • permLattice πJ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6) := by
    rw [← hθ' α hα]
    exact l154td4_theta_mem S i v hΨ hρ hα
  have hx : ∀ k, k ∉ d4Nodes Tag.E6 → permLattice πJ α k = 0 := fun k hk => by
    refine hα.2 _ fun hmem => hk ?_
    have h' := hleaf.mem_d4Set (show πJ.symm k ∈ d4Set Tag.E6 from hmem)
    rwa [Equiv.apply_symm_apply] at h'
  have hππ : permLattice πJ (permLattice πJ α) = α := by
    rw [← permLattice_mul, h1]
    funext k
    rfl
  rw [Function.iterate_succ_apply, Function.iterate_one, hρβ α hα, hρβ _ hβ,
    (hnorm (permLattice πJ α)).2 hx, hππ]
  simp only [mul_smul, inv_smul_smul]

private theorem lk0xlqd4tw_layer
    {L : Type} [Field L] [IsAlgClosed L] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ] (hf : 1 ≤ f)
    {a b c : Fin TwistTag.E6.tag.rank}
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) (ha : a.val = 1 ∨ a.val = 2 ∨ a.val = 4)
    (hb : b.val = 1 ∨ b.val = 2 ∨ b.val = 4) (hc : c.val = 1 ∨ c.val = 2 ∨ c.val = 4)
    {n : ModGL TwistTag.E6.tag L} (hn : n ∈ monomialSubgroup TwistTag.E6.tag L)
    {u : WeylGroup TwistTag.E6.tag} (hu : u ∈ parabolicWeylGroup TwistTag.E6.tag (d4Nodes _))
    (hact : ∀ α ∈ parabolicRoots TwistTag.E6.tag (d4Nodes _),
      weylQuotientHom TwistTag.E6.tag L ⟨n, hn⟩ • permLattice TwistTag.E6.perm α =
        u • permLattice (List.formPerm [a, b, c]) α) :
    LieModel (↥(rootSpan TwistTag.E6.tag L (parabolicRoots TwistTag.E6.tag (d4Nodes _)) ⊓
        twistedFixedPoints (n * diagramMap TwistTag.E6 L)
          (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) ⧸
      Subgroup.center ↥(rootSpan TwistTag.E6.tag L (parabolicRoots TwistTag.E6.tag (d4Nodes _)) ⊓
        twistedFixedPoints (n * diagramMap TwistTag.E6 L)
          (Units.map (entrywiseHom (iterateFrobenius L ℓ f))))) .trialityD4 0 ℓ f := by
  obtain ⟨hcyc, hπ, hπ'⟩ := leafCycle_E6 a b c ha hb hc hab hbc hac
  have hact' : ∀ j ∈ d4Set TwistTag.E6.tag, weylQuotientHom TwistTag.E6.tag L ⟨n, hn⟩ •
      permLattice TwistTag.E6.perm (Pi.single j 1 : Fin TwistTag.E6.tag.rank → ℤ) =
        u • (Pi.single (List.formPerm [a, b, c] j) 1 : Fin TwistTag.E6.tag.rank → ℤ) :=
    fun j hj => by
      have := hact _ (single_mem_parabolicRoots hj)
      rw [permLattice_single (List.formPerm [a, b, c])] at this
      exact this
  obtain ⟨n₁, h, hh, hgen, hlang⟩ := exists_conj_twistedFixed_twist hf hn (fun i hi => hπ i hi)
    (fun i hi => hπ' i hi) hu hact'
  have hd4 : d4Nodes TwistTag.E6.tag = d4Set TwistTag.E6.tag := rfl
  rw [hd4, ← subsystemGroup_eq_rootSpan]
  rcases hcyc with h1 | h2
  · have hstd : StdTwist n₁ (List.formPerm [a, b, c]) 1 :=
      ⟨Or.inl rfl, h1, fun i hi => hπ i hi, fun i hi => hπ' i hi, hgen⟩
    exact lieModel_model_layer_triality hf hstd hh hlang rfl
  · have hstd : StdTwist n₁ (List.formPerm [a, b, c]) 2 :=
      ⟨Or.inr rfl, h2, fun i hi => hπ i hi, fun i hi => hπ' i hi, hgen⟩
    exact lieModel_model_layer_triality hf hstd hh hlang rfl

theorem lq_triD4_twE6
    {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup .E6 L p)
    (hS : ∃ (t : TwistTag) (h : t.tag = .E6) (Fr : L →+* L), (∀ c, Fr c = c ^ S.D.q) ∧
      ∀ g, S.D.Φ g = diagramAt .E6 L t h * Units.map (entrywiseHom Fr) g *
        (diagramAt .E6 L t h)⁻¹)
    {a : Fin Tag.E6.rank → Lˣ} (i : KernelComponent (rootCharHom a)) (v : WeylGroup .E6)
    (hΨ : componentRoots (rootCharHom a) i =
      (fun α => v • α) '' parabolicRoots .E6 (d4Nodes .E6))
    (hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i)
    (hnin : ¬ twistInner (componentRoots (rootCharHom a) i) (S.ρ : (Fin Tag.E6.rank → ℤ) → _))
    (h2 : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[2])) :
    ∃ f : ℕ, ringChar L ^ f = S.D.q ∧
      LieModel (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) .trialityD4 0
        (ringChar L) f := by
  classical
  obtain ⟨w, hn, hρw⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24.d4t2out_rho_eq S hS
  obtain ⟨t, ht, Fr, hFr, hΦ⟩ := hS
  cases t with
  | D4 => exact absurd ht (by decide)
  | E6 =>
  have hΦ' : ∀ g, S.D.Φ g = e6Diagram L * Units.map (entrywiseHom Fr) g * (e6Diagram L)⁻¹ := hΦ
  obtain ⟨ℓ, f, hℓ, hchar, hf, hq⟩ := S.exists_char_pow
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hFr' : Fr = iterateFrobenius L ℓ f := by
    ext x
    rw [hFr, hq, iterateFrobenius_def]
  obtain ⟨u, hu, w₀, hw₀, πJ, hleaf, hlin, hθ'⟩ := l154r4_tw_action S hρw i v hΨ hρ
  have hπ1 := l154r4_tw_pi_ne_one S i v hΨ hnin hu hθ'
  have hπ2 := lk0xlqd4tw_pi_sq S i v hΨ hρ h2 hu hleaf hθ'
  obtain ⟨n', hn', hact, g, heq⟩ := l154r4_tw_layer_eq S hFr' hΦ' hn i v hΨ hw₀ hlin
  have h12 : e6Idx (τ := Tag.E6) 1 ≠ e6Idx 2 := e6Idx_ne (by decide)
  have h14 : e6Idx (τ := Tag.E6) 1 ≠ e6Idx 4 := e6Idx_ne (by decide)
  have h24 : e6Idx (τ := Tag.E6) 2 ≠ e6Idx 4 := e6Idx_ne (by decide)
  have hv1 : (e6Idx (τ := Tag.E6) 1).val = 1 ∨ (e6Idx (τ := Tag.E6) 1).val = 2 ∨
      (e6Idx (τ := Tag.E6) 1).val = 4 := Or.inl rfl
  have hv2 : (e6Idx (τ := Tag.E6) 2).val = 1 ∨ (e6Idx (τ := Tag.E6) 2).val = 2 ∨
      (e6Idx (τ := Tag.E6) 2).val = 4 := Or.inr (Or.inl rfl)
  have hv4 : (e6Idx (τ := Tag.E6) 4).val = 1 ∨ (e6Idx (τ := Tag.E6) 4).val = 2 ∨
      (e6Idx (τ := Tag.E6) 4).val = 4 := Or.inr (Or.inr rfl)
  set Q := rootSpan Tag.E6 L (parabolicRoots Tag.E6 (d4Nodes Tag.E6)) ⊓
    twistedFixedPoints (n' * e6Diagram L) (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))
    with hQ
  have hlayer : CFSG.IsQuasisimple ↥Q ∧
      LieModel (↥Q ⧸ Subgroup.center ↥Q) .trialityD4 0 ℓ f := by
    rcases hleaf.eq_cycle hπ1 hπ2 with hc | hc
    · rw [hc] at hact
      exact ⟨(twisted_triality_layer_E6 hf h12 h24 h14 hv1 hv2 hv4 hn' hu hact).2,
        lk0xlqd4tw_layer hf h12 h24 h14 hv1 hv2 hv4 hn' hu hact⟩
    · rw [hc] at hact
      exact ⟨(twisted_triality_layer_E6 hf h14 h24.symm h12 hv1 hv4 hv2 hn' hu hact).2,
        lk0xlqd4tw_layer hf h14 h24.symm h12 hv1 hv4 hv2 hn' hu hact⟩
  have e : Q ≃* Q.map (MulAut.conj g).toMonoidHom :=
    Q.equivMapOfInjective _ (MulAut.conj g).injective
  have hqs : CFSG.IsQuasisimple
      ↥(rootSpan Tag.E6 L (componentRoots (rootCharHom a) i) ⊓ S.D.model) := by
    rw [heq]
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e hlayer.1
  refine ⟨f, by rw [ringChar.eq L ℓ, hq], ?_⟩
  rw [rationalComponent_eq_of_layer S i hρ hqs, heq, ringChar.eq L ℓ]
  exact lieModel_triD4_map_conj (MulAut.conj g) hlayer.2

end CFSG.StandardType.GGK0LQ

end
