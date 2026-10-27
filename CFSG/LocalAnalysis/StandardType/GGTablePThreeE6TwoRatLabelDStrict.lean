module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TwoRatLabelDStrictBase
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6RatLabel
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6FrobDefs
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6RatLabelOuterD
public import CFSG.RankThree.PartOne.KD4T.Emb
public import CFSG.RankThree.PartOne.KD4T.Inj
public import CFSG.RankThree.PartOne.KE.D4TranspositionInterface
public import CFSG.RankThree.PartOne.KE6.E6LAct
public import CFSG.LieType.Chevalley.WeylRoots
public import CFSG.LieType.Chevalley.KernelComponentRoots
public import CFSG.LieType.Chevalley.StandardParabolic
public import CFSG.LieType.Chevalley.StandardParabolicCells
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ExcD4Action
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExcD4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154NonCfgRank4B
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcTD4D4
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTame

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section E6TwoRatLabelD

open CFSG.RankThree.PartOne.KD4T CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KE6
  CFSG.LocalAnalysis.GLTheoremA.K155X CFSG.RankThree.PartOne.KD4L
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.ExcUntw CFSG.LieType.Steinberg.Adjoint
  CFSG.RankThree.Lattice CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.Chevalley
  CFSG.RankThree.E6 CFSG.Timmesfeld.LevisSpin CFSG.ClassicalInvolution.WeakCT
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsPD4Tau
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsPD4Layers
  CFSG.Yardstones.Md0ec50421ce4

theorem e6TwoRatLabelD_formPerm_three_sq_ne_one
    {τ : Tag} {a b c : Fin τ.rank} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    List.formPerm [a, b, c] * List.formPerm [a, b, c] ≠ 1 := by
  intro h
  have h1 : (List.formPerm [a, b, c] * List.formPerm [a, b, c]) a = a := by rw [h]; rfl
  simp only [List.formPerm_cons_cons, List.formPerm_singleton, mul_one] at h1
  have h2 : ((Equiv.swap a b * Equiv.swap b c) * (Equiv.swap a b * Equiv.swap b c)) a = c := by
    simp only [Equiv.Perm.mul_apply]
    rw [Equiv.swap_apply_of_ne_of_ne hab hac, Equiv.swap_apply_left,
      Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hac.symm hbc.symm]
  rw [h2] at h1
  exact hac h1.symm

theorem e6TwoRatLabelD_strict_rationalComponent_of_d4_outer
    {τ : Tag} [E6Sub τ] {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    (hsearch : D4BaseSearch τ) (hL2 : CFSG.HardMathSupport.Timmesfeld.CrossChar.D4SwapLayer τ)
    (hR2 : e6TwoRatLabelD_StrictSwapLayer τ)
    (S : LangSetup τ L p) {Fr : L →+* L}
    (hFr : ∀ c, Fr c = c ^ S.D.q) (hΦ : S.D.Φ = Units.map (entrywiseHom Fr)) {w : WeylGroup τ}
    (hn : S.D.n = canonicalRep (coxeterSystem τ) L w) (hρw : ∀ γ, IsRoot τ γ → S.ρ γ = w • γ)
    {a : Fin τ.rank → Lˣ} (i : KernelComponent (rootCharHom a)) (v : WeylGroup τ)
    (hΨ : componentRoots (rootCharHom a) i = (fun α => v • α) '' parabolicRoots τ (d4Nodes τ))
    (hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i)
    (h1 : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)]))
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[2])) :
    ∃ f : ℕ, ringChar L ^ f = S.D.q ∧
      e6TwoRatLabelD_StrictModel (ringChar L) f
        ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  classical
  have hfin : (componentRoots (rootCharHom a) i).Finite :=
    (finite_setOf_isRoot _).subset fun γ hγ => hγ.1.1
  rw [componentOrbitLength_eq_one hfin hρ, Function.iterate_one] at h1
  obtain ⟨u, hu, π, hπ, hπ1, hact⟩ :=
    l154r4_d4_outer_action hsearch S hρw i v hΨ hρ h1
  have hππ : π * π = 1 :=
    e6TwoRatLabelD_leaf_sq hsearch S hρw i v hΨ hρ hinner u hu π hπ hact
  have h12 : e6Idx (τ := τ) 1 ≠ e6Idx 2 := e6Idx_ne (by decide)
  have h14 : e6Idx (τ := τ) 1 ≠ e6Idx 4 := e6Idx_ne (by decide)
  have h24 : e6Idx (τ := τ) 2 ≠ e6Idx 4 := e6Idx_ne (by decide)
  have hv1 : (e6Idx (τ := τ) 1).val ∈ ({1, 2, 4} : Set ℕ) := by
    rw [e6Idx_val']; exact Or.inl rfl
  have hv2 : (e6Idx (τ := τ) 2).val ∈ ({1, 2, 4} : Set ℕ) := by
    rw [e6Idx_val']; exact Or.inr (Or.inl rfl)
  have hv4 : (e6Idx (τ := τ) 4).val ∈ ({1, 2, 4} : Set ℕ) := by
    rw [e6Idx_val']; exact Or.inr (Or.inr rfl)
  have hlayer : CFSG.IsQuasisimple
        ↥(rootSpan τ L (componentRoots (rootCharHom a) i) ⊓ S.D.model) ∧
      ∃ f : ℕ, ringChar L ^ f = S.D.q ∧ e6TwoRatLabelD_StrictModel (ringChar L) f
        ↥(rootSpan τ L (componentRoots (rootCharHom a) i) ⊓ S.D.model) := by
    rw [hΨ]
    rcases hπ with rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl hπ1
    · exact ⟨(rootSpan_inf_model_quasisimple_d4_swap hL2 S hFr hΦ hn v hu h12 hv1 hv2 hact).2,
        e6TwoRatLabelD_strict_rootSpan_inf_model_d4_swap hR2 S hFr hΦ hn v hu h12 hv1 hv2 hact⟩
    · exact ⟨(rootSpan_inf_model_quasisimple_d4_swap hL2 S hFr hΦ hn v hu h14 hv1 hv4 hact).2,
        e6TwoRatLabelD_strict_rootSpan_inf_model_d4_swap hR2 S hFr hΦ hn v hu h14 hv1 hv4 hact⟩
    · exact ⟨(rootSpan_inf_model_quasisimple_d4_swap hL2 S hFr hΦ hn v hu h24 hv2 hv4 hact).2,
        e6TwoRatLabelD_strict_rootSpan_inf_model_d4_swap hR2 S hFr hΦ hn v hu h24 hv2 hv4 hact⟩
    · exfalso
      exact e6TwoRatLabelD_formPerm_three_sq_ne_one (e6Idx_ne (by decide))
        (e6Idx_ne (by decide)) (e6Idx_ne (by decide)) hππ
    · exfalso
      exact e6TwoRatLabelD_formPerm_three_sq_ne_one (e6Idx_ne (by decide))
        (e6Idx_ne (by decide)) (e6Idx_ne (by decide)) hππ
  rw [rationalComponent_eq_of_layer S i hρ hlayer.1]
  exact hlayer.2



theorem e6TwoRatLabelD_strict_swapLayer_E6 :
    e6TwoRatLabelD_StrictSwapLayer Tag.E6 := by
  intro L _ _ ℓ f _ _ hf i j hij hi hj n hn hC hact P hP
  have hi' : i.val = 1 ∨ i.val = 2 ∨ i.val = 4 := by simpa using hi
  have hj' : j.val = 1 ∨ j.val = 2 ∨ j.val = 4 := by simpa using hj
  obtain ⟨hcases, hπ, hπ'⟩ := leafSwap_E6 i j hi' hj' hij
  rcases hcases with h1 | h2 | h3
  · exact e6TwoRatLabelD_strict_swapLayer_generic hf (Equiv.swap 1 3)
      (e6TwoRatLabelD_strict_exists_fix_swap13 hf) (Equiv.swap i j) h1
      (fun x hx => hπ x hx) (fun x hx => hπ' x hx) n hn hact P hP
  · exact e6TwoRatLabelD_strict_swapLayer_generic hf (Equiv.swap 0 3)
      (e6TwoRatLabelD_strict_exists_fix_swap03 hf) (Equiv.swap i j) h2
      (fun x hx => hπ x hx) (fun x hx => hπ' x hx) n hn hact P hP
  · exact e6TwoRatLabelD_strict_swapLayer_generic hf (Equiv.swap 0 1)
      (e6TwoRatLabelD_strict_exists_fix_swap01 hf) (Equiv.swap i j) h3
      (fun x hx => hπ x hx) (fun x hx => hπ' x hx) n hn hact P hP

theorem e6TwoRatLabelD_strict_swapLayer_E7 :
    e6TwoRatLabelD_StrictSwapLayer Tag.E7 := by
  intro L _ _ ℓ f _ _ hf i j hij hi hj n hn hC hact P hP
  have hi' : i.val = 1 ∨ i.val = 2 ∨ i.val = 4 := by simpa using hi
  have hj' : j.val = 1 ∨ j.val = 2 ∨ j.val = 4 := by simpa using hj
  obtain ⟨hcases, hπ, hπ'⟩ := leafSwap_E7 i j hi' hj' hij
  rcases hcases with h1 | h2 | h3
  · exact e6TwoRatLabelD_strict_swapLayer_generic hf (Equiv.swap 1 3)
      (e6TwoRatLabelD_strict_exists_fix_swap13 hf) (Equiv.swap i j) h1
      (fun x hx => hπ x hx) (fun x hx => hπ' x hx) n hn hact P hP
  · exact e6TwoRatLabelD_strict_swapLayer_generic hf (Equiv.swap 0 3)
      (e6TwoRatLabelD_strict_exists_fix_swap03 hf) (Equiv.swap i j) h2
      (fun x hx => hπ x hx) (fun x hx => hπ' x hx) n hn hact P hP
  · exact e6TwoRatLabelD_strict_swapLayer_generic hf (Equiv.swap 0 1)
      (e6TwoRatLabelD_strict_exists_fix_swap01 hf) (Equiv.swap i j) h3
      (fun x hx => hπ x hx) (fun x hx => hπ' x hx) n hn hact P hP

theorem e6TwoRatLabelD_strict_swapLayer_E8 :
    e6TwoRatLabelD_StrictSwapLayer Tag.E8 := by
  intro L _ _ ℓ f _ _ hf i j hij hi hj n hn hC hact P hP
  have hi' : i.val = 1 ∨ i.val = 2 ∨ i.val = 4 := by simpa using hi
  have hj' : j.val = 1 ∨ j.val = 2 ∨ j.val = 4 := by simpa using hj
  obtain ⟨hcases, hπ, hπ'⟩ := leafSwap_E8 i j hi' hj' hij
  rcases hcases with h1 | h2 | h3
  · exact e6TwoRatLabelD_strict_swapLayer_generic hf (Equiv.swap 1 3)
      (e6TwoRatLabelD_strict_exists_fix_swap13 hf) (Equiv.swap i j) h1
      (fun x hx => hπ x hx) (fun x hx => hπ' x hx) n hn hact P hP
  · exact e6TwoRatLabelD_strict_swapLayer_generic hf (Equiv.swap 0 3)
      (e6TwoRatLabelD_strict_exists_fix_swap03 hf) (Equiv.swap i j) h2
      (fun x hx => hπ x hx) (fun x hx => hπ' x hx) n hn hact P hP
  · exact e6TwoRatLabelD_strict_swapLayer_generic hf (Equiv.swap 0 1)
      (e6TwoRatLabelD_strict_exists_fix_swap01 hf) (Equiv.swap i j) h3
      (fun x hx => hπ x hx) (fun x hx => hπ' x hx) n hn hact P hP


theorem e6TwoRatLabelD_strict_rationalComponent_of_d4_twE6
    {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup .E6 L p)
    (hS : ∃ (t : TwistTag) (h : t.tag = .E6) (Fr : L →+* L), (∀ c, Fr c = c ^ S.D.q) ∧
      ∀ g, S.D.Φ g = diagramAt .E6 L t h * Units.map (entrywiseHom Fr) g *
        (diagramAt .E6 L t h)⁻¹)
    {a : Fin Tag.E6.rank → Lˣ} (i : KernelComponent (rootCharHom a)) (v : WeylGroup .E6)
    (hΨ : componentRoots (rootCharHom a) i = (fun α => v • α) '' parabolicRoots .E6 (d4Nodes .E6))
    (hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i)
    (hnin : ¬ twistInner (componentRoots (rootCharHom a) i) (S.ρ : (Fin Tag.E6.rank → ℤ) → _))
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[2])) :
    ∃ f : ℕ, ringChar L ^ f = S.D.q ∧
      e6TwoRatLabelD_StrictModel (ringChar L) f ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  exact l154td4_d4_tw S hS i v hΨ hρ hnin hinner

theorem e6TwoRatLabelD_strict_of_rank_four
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ}
    (S : LangSetup τ L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0)
    {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus) (hTp : rootDiagUnit τ a ^ p = 1)
    (ha1 : rootDiagUnit τ a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hr : compRank (componentRoots (rootCharHom a) i) = 4)
    (hc : (componentRoots (rootCharHom a) i).ncard = 24)
    (hnin : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)]))
    (hsq : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[
        2 * componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)])) :
    ∃ f : ℕ, ringChar L ^ f = S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) ∧
      e6TwoRatLabelD_StrictModel (ringChar L) f
        ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  cases τ with
  | G2 =>
    have hle := compRank_le_rank (componentRoots (rootCharHom a) i)
    rw [hr] at hle
    exact absurd hle (by decide)
  | F4 =>
    obtain ⟨v, μ, -, hpinned⟩ := S.exists_pinnedT_of_prime hp hpL facts_F4 hTp
    obtain ⟨x, C, -, -, -, hr', hc'⟩ := hpinned i
    exact absurd (hc' ▸ hc) (kacCount_F4_four C (hr' ▸ hr))
  | D4 => exact absurd (rootDiagUnit_eq_one_of_ncard i (by rw [hc]; rfl)) ha1
  | E6 =>
    obtain ⟨v, hv, hρ⟩ := S.d4_pinnedT_of_prime hp hpL facts_E6 kacCount_E6_four (by decide)
      (by decide)
      (fun y hy => far_d4_E6 y fun z hz => by
        have h := hy z hz
        rwa [KacData.Adj, extRoot_eq_extRootOf] at h)
      ⟨none, by decide⟩ (lt_of_eq_of_lt kacCount_far_E6 (by decide)) hT hTp i hr hc
    have hfin : (componentRoots (rootCharHom a) i).Finite :=
      (finite_setOf_isRoot _).subset fun γ hγ => hγ.1.1
    have hs : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1 :=
      componentOrbitLength_eq_one hfin hρ
    have hinner := hsq
    rw [hs, mul_one] at hinner
    obtain ⟨w, hn⟩ := S.D.n_weyl
    obtain ⟨Fr, hFr, P, hP, hΦ⟩ := S.D.steinberg
    rcases hP with rfl | ⟨t, ht, rfl⟩
    · have hΦ' : S.D.Φ = Units.map (entrywiseHom Fr) := by
        ext1 g
        rw [hΦ, one_mul, inv_one, mul_one]
      obtain ⟨f, hf, hm⟩ := e6TwoRatLabelD_strict_rationalComponent_of_d4_outer d4Base_E6
        (d4SwapLayer_E6 e6FixDNAll_proved) e6TwoRatLabelD_strict_swapLayer_E6 S hFr hΦ' hn
        (fun γ hγ => S.rho_eq_smul_of_frob hFr hΦ' hn hγ) i v hv hρ hnin hinner
      exact ⟨f, by rw [hs, pow_one]; exact hf, hm⟩
    · have hnin' := hnin
      rw [hs, Function.iterate_one] at hnin'
      obtain ⟨f, hf, hm⟩ := e6TwoRatLabelD_strict_rationalComponent_of_d4_twE6 S
        ⟨t, ht, Fr, hFr, hΦ⟩ i v hv hρ hnin' hinner
      exact ⟨f, by rw [hs, pow_one]; exact hf, hm⟩
  | E7 =>
    obtain ⟨v, hv, hρ⟩ := S.d4_pinnedT_of_prime hp hpL facts_E7 kacCount_E7_four (by decide)
      (by decide)
      (fun y hy => far_d4_E7 y fun z hz => by
        have h := hy z hz
        rwa [KacData.Adj, extRoot_eq_extRootOf] at h)
      ⟨some 0, by decide⟩ (lt_of_eq_of_lt kacCount_far_E7 (by decide)) hT hTp i hr hc
    obtain ⟨Fr, hFr, hΦ⟩ := S.D.exists_frob_of_untwisted twistTag_tag_ne_E7
    obtain ⟨w, hn⟩ := S.D.n_weyl
    have hfin : (componentRoots (rootCharHom a) i).Finite :=
      (finite_setOf_isRoot _).subset fun γ hγ => hγ.1.1
    have hs : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1 :=
      componentOrbitLength_eq_one hfin hρ
    have hinner := hsq
    rw [hs, mul_one] at hinner
    obtain ⟨f, hf, hm⟩ := e6TwoRatLabelD_strict_rationalComponent_of_d4_outer d4Base_E7
      (d4SwapLayer_E7 e6FixDNAll_proved) e6TwoRatLabelD_strict_swapLayer_E7 S hFr hΦ hn
      (fun γ hγ => S.rho_eq_smul_of_frob hFr hΦ hn hγ) i v hv hρ hnin hinner
    exact ⟨f, by rw [hs, pow_one]; exact hf, hm⟩
  | E8 =>
    obtain ⟨v, hv, hρ⟩ := S.d4_pinnedT_of_prime hp hpL facts_E8 kacCount_E8_four (by decide)
      (by decide)
      (fun y hy => far_d4_E8 y fun z hz => by
        have h := hy z hz
        rwa [KacData.Adj, extRoot_eq_extRootOf] at h)
      ⟨some 0, by decide⟩ (lt_of_eq_of_lt kacCount_far_E8 (by decide)) hT hTp i hr hc
    obtain ⟨Fr, hFr, hΦ⟩ := S.D.exists_frob_of_untwisted twistTag_tag_ne_E8
    obtain ⟨w, hn⟩ := S.D.n_weyl
    have hfin : (componentRoots (rootCharHom a) i).Finite :=
      (finite_setOf_isRoot _).subset fun γ hγ => hγ.1.1
    have hs : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1 :=
      componentOrbitLength_eq_one hfin hρ
    have hinner := hsq
    rw [hs, mul_one] at hinner
    obtain ⟨f, hf, hm⟩ := e6TwoRatLabelD_strict_rationalComponent_of_d4_outer d4Base_E8
      (d4SwapLayer_E8 e6FixDNAll_proved) e6TwoRatLabelD_strict_swapLayer_E8 S hFr hΦ hn
      (fun γ hγ => S.rho_eq_smul_of_frob hFr hΦ hn hγ) i v hv hρ hnin hinner
    exact ⟨f, by rw [hs, pow_one]; exact hf, hm⟩

end E6TwoRatLabelD

end CFSG.StandardType.TablePThreeKG

end
