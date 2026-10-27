module

public import CFSG.LocalAnalysis.StandardType.GGQ2HeartJFrame
public import CFSG.LocalAnalysis.StandardType.GGQ2HeartJDict
public import CFSG.LocalAnalysis.StandardType.GGQTwoHeartDict
public import CFSG.LocalAnalysis.StandardType.GGLangDetectsTwoDispatch
public import CFSG.RankThree.PartOne.KLR.RootKernel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem ggQ2HeartJHoldsAux_rootChar_eq_one_iff {K : Type} [Field K] {ζ : Kˣ}
    (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1) (t : Fin Tag.E6.rank → ZMod 3)
    (β : Fin Tag.E6.rank → ℤ) :
    rootChar (TableBExc.E6Three.zetaVec (τ := Tag.E6) ζ hζ t) β = 1 ↔
      ∑ j, (β j : ZMod 3) * t j = 0 := by
  rw [show TableBExc.E6Three.zetaVec (τ := Tag.E6) ζ hζ t = fun i => ζ ^ (t i).val from
    funext (TableBExc.E6Three.zetaVec_apply ζ hζ t)]
  exact CFSG.RankThree.PartOne.KLR.rootChar_zetaPow_eq_one_iff_charVal
    (hζo ▸ IsPrimitiveRoot.orderOf ζ) t β

private theorem ggQ2HeartJHoldsAux_zetaVec_pow {K : Type} [Field K] {ζ : Kˣ} (hζ : ζ ^ 3 = 1)
    (t : Fin Tag.E6.rank → ZMod 3) (j : Fin Tag.E6.rank) :
    TableBExc.E6Three.zetaVec (τ := Tag.E6) ζ hζ t j ^ 3 = 1 := by
  rw [TableBExc.E6Three.zetaVec_apply, ← pow_mul, mul_comm, pow_mul, hζ, one_pow]

private theorem ggQ2HeartJHoldsAux_mem_span_iff {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) (b : ↥Bs) :
    M.model (Additive.ofMul b) ∈ Submodule.span (ZMod 3) {M.xV} ↔
      (b : G) ∈ Subgroup.zpowers x := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 h
    have h1 : M.model (Additive.ofMul b) = M.model (c.val • Additive.ofMul (⟨x, M.hx⟩ : ↥Bs)) := by
      rw [← hc, map_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod 3), ZMod.natCast_zmod_val]
      rfl
    have h2 := M.model.injective h1
    rw [← ofMul_pow] at h2
    have h3 : b = ⟨x, M.hx⟩ ^ c.val := Additive.ofMul.injective h2
    rw [h3, Subgroup.coe_pow]
    exact Subgroup.npow_mem_zpowers x c.val
  · intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h
    have h1 : b = ⟨x, M.hx⟩ ^ k := Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk.symm)
    rw [h1, ofMul_zpow, map_zsmul]
    exact zsmul_mem (Submodule.mem_span_singleton_self M.xV) k

theorem ggQ2HeartJCentralizes_holds :
    GGQ2HeartJCentralizes := by
  intro G _ _ p B Bs x L D J hS hp _ labL htag hmark M hW hB yB hyB hyx
  subst hp
  classical
  obtain ⟨Dd⟩ := ggQ2_heartDict htag M hW hB
  obtain ⟨K, _, _, S, ζ, hζ, κ, i, hζo, hρ, hq, hAlg, htor, hκ1, hκhyp, hnorm, hqi, hcent⟩ :=
    ggQ2HeartJ_frame hS htag hmark M hW hB yB hyB hyx
  let κA : M.V →+ (Fin Tag.E6.rank → ZMod 3) :=
    { toFun := fun v => Multiplicative.toAdd (κ (Additive.toMul (M.model.symm v)))
      map_zero' := by simp
      map_add' := fun v w => by simp }
  let κL : M.V →ₗ[ZMod 3] (Fin Tag.E6.rank → ZMod 3) := κA.toZModLinearMap 3
  have hκL' : ∀ v, κL v = Multiplicative.toAdd (κ (Additive.toMul (M.model.symm v))) :=
    fun v => rfl
  have hκL : ∀ b : ↥Bs, κL (M.model (Additive.ofMul b)) = Multiplicative.toAdd (κ b) := by
    intro b
    rw [hκL', AddEquiv.symm_apply_apply, toMul_ofMul]
  have hsurjV : ∀ v : M.V, ∃ b : ↥Bs, M.model (Additive.ofMul b) = v :=
    fun v => ⟨Additive.toMul (M.model.symm v), by simp⟩
  have hx0 : M.xV ≠ 0 := fun h0 => hB.2.2.1 (h0 ▸ M.coSpan.zero_mem)
  have hker : LinearMap.ker κL = Submodule.span (ZMod 3) {M.xV} := by
    ext v
    obtain ⟨b, rfl⟩ := hsurjV v
    rw [LinearMap.mem_ker, hκL, ggQ2HeartJHoldsAux_mem_span_iff, ← hκ1]
    exact ⟨fun h => by simpa using congrArg Multiplicative.ofAdd h,
      fun h => by rw [h, toAdd_one]⟩
  have hrange : ∀ t, t ∈ NoOffRest.hypE6 ↔ t ∈ LinearMap.range κL := by
    intro t
    rw [← hκhyp, MonoidHom.mem_range, LinearMap.mem_range]
    constructor
    · rintro ⟨b, hb⟩
      exact ⟨M.model (Additive.ofMul b), by rw [hκL, hb, toAdd_ofAdd]⟩
    · rintro ⟨v, rfl⟩
      exact ⟨Additive.toMul (M.model.symm v), by rw [hκL', ofAdd_toAdd]⟩
  have hW' : ∀ φ ∈ ggAutomizer L Bs, ∃ u : WeylGroup Tag.E6, ∀ v,
      κL (ggLin (p := 3) M.model φ v) = TableBExc.E6Three.adAct Tag.E6 3 u (κL v) := by
    intro φ hφ
    obtain ⟨u, hu⟩ := hnorm φ hφ
    refine ⟨u, fun v => ?_⟩
    obtain ⟨b, rfl⟩ := hsurjV v
    rw [ggLin_apply_ofMul, hκL, hκL, hu]
  obtain ⟨Φ, hΦroot, hΦsurj, hΦinj, hΦpair, hΦform⟩ :=
    ggQ2HeartJ_rootMap M Dd hx0 κL hker hrange hW'
  let χ := rootCharHom (TableBExc.E6Three.zetaVec (τ := Tag.E6) ζ hζ
    (Multiplicative.toAdd (κ yB)))
  have hkerR : ∀ γ, γ ∈ kernelRoots χ ↔
      IsRoot Tag.E6 γ ∧ ∑ j, (γ j : ZMod 3) * Multiplicative.toAdd (κ yB) j = 0 := by
    intro γ
    change γ ∈ kernelRoots (rootCharHom (TableBExc.E6Three.zetaVec (τ := Tag.E6) ζ hζ
      (Multiplicative.toAdd (κ yB)))) ↔ _
    rw [kernelRoots_rootCharHom, Set.mem_setOf_eq]
    exact and_congr_right fun _ => ggQ2HeartJHoldsAux_rootChar_eq_one_iff hζo hζ _ γ
  have hΦker : ∀ w : {a : M.Λ → ℤ // CFSG.ClassicalInvolution.RouteD.RRoot M.cartan a ∧
      M.rootForm a (M.model (Additive.ofMul yB)) = 0}, Φ w.1 ∈ kernelRoots χ := by
    intro w
    refine (hkerR _).2 ⟨hΦroot _ w.2.1, ?_⟩
    rw [← hκL, ← hΦform]
    exact w.2.2
  have hadj : ∀ w w', (M.phiGraph (M.model (Additive.ofMul yB))).Adj w w' →
      (⟦⟨Φ w.1, hΦker w⟩⟧ : KernelComponent χ) = ⟦⟨Φ w'.1, hΦker w'⟩⟧ := by
    intro w w' h
    simp only [GGQ2LDatum.phiGraph, SimpleGraph.fromRel_adj] at h
    apply mk_eq_of_iform_ne_zero
    change iform (Φ w.1) (Φ w'.1) ≠ 0
    rcases h.2 with h2 | h2
    · rwa [← hΦpair]
    · rw [hΦpair] at h2
      rwa [iform_comm]
  have hreach : ∀ w w', (M.phiGraph (M.model (Additive.ofMul yB))).Reachable w w' →
      (⟦⟨Φ w.1, hΦker w⟩⟧ : KernelComponent χ) = ⟦⟨Φ w'.1, hΦker w'⟩⟧ := by
    intro w w' ⟨p⟩
    induction p with
    | nil => rfl
    | cons h _ ih => exact (hadj _ _ h).trans ih
  have hΨ := isRootComponent_componentRoots (χ := χ) i
  have hT : rootDiagUnit Tag.E6 (TableBExc.E6Three.zetaVec (τ := Tag.E6) ζ hζ
      (Multiplicative.toAdd (κ yB))) ∈ S.D.torus :=
    (htor _).2 (ggQ2HeartJHoldsAux_zetaVec_pow hζ _)
  have h3 := QTwoHeartJ.three_le_compRank_of_quasisimple S (Or.inl rfl) hq (fun γ _ => hρ γ) hT
    (ggQ2HeartJHoldsAux_zetaVec_pow hζ _) i hqi
  have h6 := QTwoHeartJ.six_lt_ncard_of_three_le_compRank hΨ h3
  obtain ⟨γ₀, hγ₀k, hγ₀i⟩ := Set.nonempty_of_ncard_ne_zero
    (by omega : (componentRoots χ i).ncard ≠ 0)
  obtain ⟨a₀, ha₀, hΦa₀⟩ := hΦsurj γ₀ ((hkerR γ₀).1 hγ₀k).1
  have hw₀ : CFSG.ClassicalInvolution.RouteD.RRoot M.cartan a₀ ∧
      M.rootForm a₀ (M.model (Additive.ofMul yB)) = 0 := by
    refine ⟨ha₀, ?_⟩
    rw [hΦform, hκL, hΦa₀]
    exact ((hkerR γ₀).1 hγ₀k).2
  let w₀ : {a : M.Λ → ℤ // CFSG.ClassicalInvolution.RouteD.RRoot M.cartan a ∧
      M.rootForm a (M.model (Additive.ofMul yB)) = 0} := ⟨a₀, hw₀⟩
  have hw₀i : (⟦⟨Φ w₀.1, hΦker w₀⟩⟧ : KernelComponent χ) = i := by
    rw [← hγ₀i]
    exact congrArg _ (Subtype.ext hΦa₀)
  let c := (M.phiGraph (M.model (Additive.ofMul yB))).connectedComponentMk w₀
  have hsupp : ∀ w ∈ c.supp, Φ w.1 ∈ componentRoots χ i := by
    intro w hw
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hw
    exact ⟨hΦker w, (hreach _ _ (SimpleGraph.ConnectedComponent.exact hw)).trans hw₀i⟩
  have hstep : ∀ α β : kernelRoots χ, iform (α : Fin Tag.E6.rank → ℤ) β ≠ 0 →
      (∃ w, ∃ hw : w ∈ c.supp, Φ w.1 = α) → ∃ w, ∃ hw : w ∈ c.supp, Φ w.1 = β := by
    rintro α β hαβ ⟨w, hw, hwα⟩
    obtain ⟨b', hb', hΦb'⟩ := hΦsurj β.1 ((hkerR β.1).1 β.2).1
    have hwb : CFSG.ClassicalInvolution.RouteD.RRoot M.cartan b' ∧
        M.rootForm b' (M.model (Additive.ofMul yB)) = 0 := by
      refine ⟨hb', ?_⟩
      rw [hΦform, hκL, hΦb']
      exact ((hkerR β.1).1 β.2).2
    let w' : {a : M.Λ → ℤ // CFSG.ClassicalInvolution.RouteD.RRoot M.cartan a ∧
        M.rootForm a (M.model (Additive.ofMul yB)) = 0} := ⟨b', hwb⟩
    refine ⟨w', ?_, hΦb'⟩
    by_cases hww : w = w'
    · rw [← hww]
      exact hw
    · have hadj' : (M.phiGraph (M.model (Additive.ofMul yB))).Adj w w' := by
        simp only [GGQ2LDatum.phiGraph, SimpleGraph.fromRel_adj]
        refine ⟨hww, Or.inl ?_⟩
        rw [hΦpair]
        change iform (Φ w.1) (Φ b') ≠ 0
        rw [hwα, hΦb']
        exact hαβ
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hw ⊢
      rw [← hw]
      exact (SimpleGraph.ConnectedComponent.sound hadj'.reachable).symm
  have heqv : ∀ α β : kernelRoots χ, Relation.EqvGen (fun α β : kernelRoots χ =>
      (α : Fin Tag.E6.rank → ℤ) ⬝ᵥ (Tag.E6.symmetrizedCartan *ᵥ (β : Fin Tag.E6.rank → ℤ)) ≠ 0)
        α β →
      ((∃ w, ∃ hw : w ∈ c.supp, Φ w.1 = α) ↔ ∃ w, ∃ hw : w ∈ c.supp, Φ w.1 = β) := by
    intro α β h
    induction h with
    | rel α β h =>
        rw [dotProduct_mulVec_eq_iform] at h
        exact ⟨hstep α β h, hstep β α (by rwa [iform_comm])⟩
    | refl => exact Iff.rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2
  have hw₀c : w₀ ∈ c.supp := (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).2 rfl
  have hcard : Nat.card c.supp = (componentRoots χ i).ncard := by
    rw [← Nat.card_coe_set_eq]
    refine Nat.card_congr (Equiv.ofBijective
      (fun w : c.supp => (⟨Φ w.1.1, hsupp w.1 w.2⟩ : componentRoots χ i)) ⟨?_, ?_⟩)
    · intro w w' h
      have h1 : Φ w.1.1 = Φ w'.1.1 := congrArg Subtype.val h
      exact Subtype.ext (Subtype.ext (hΦinj _ _ w.1.2.1 w'.1.2.1 h1))
    · rintro ⟨γ, hγk, hγi⟩
      have h1 : Relation.EqvGen (fun α β : kernelRoots χ =>
          (α : Fin Tag.E6.rank → ℤ) ⬝ᵥ (Tag.E6.symmetrizedCartan *ᵥ (β : Fin Tag.E6.rank → ℤ)) ≠ 0)
          ⟨Φ w₀.1, hΦker w₀⟩ ⟨γ, hγk⟩ :=
        Quotient.exact (hw₀i.trans hγi.symm)
      obtain ⟨w, hw, hwγ⟩ := (heqv _ _ h1).1 ⟨w₀, hw₀c, rfl⟩
      exact ⟨⟨w, hw⟩, Subtype.ext hwγ⟩
  have : CharP (AlgebraicClosure K) 2 :=
    LangRat.charP_two_of_langSetup_q_eq_two_pow S (f := 1) (by rw [hq]; norm_num)
  have hpL : ((3 : ℕ) : AlgebraicClosure K) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff (AlgebraicClosure K) 2]
    norm_num
  have hρ' : ∀ γ, IsRoot Tag.E6 γ →
      S.ρ γ = (-1 : ℤ) • latPerm (1 : Equiv.Perm (Fin Tag.E6.rank)) γ := by
    intro γ _
    rw [hρ γ]
    exact (neg_one_smul ℤ (latPerm 1 γ)).symm
  refine ⟨c, by rw [hcard]; exact h6, fun b hb w => ?_⟩
  have hZ := LangRat.langRatCentralizerDetectsPTwo_holds Tag.E6 (AlgebraicClosure K) 5 3 S
    (Or.inr (Or.inl rfl)) Nat.prime_three (by decide) hpL hq 1 (fun _ _ => rfl) (-1)
    (Or.inr rfl) hρ' (by rw [hq]; norm_num) hAlg _ _ hT
    ((htor _).2 (ggQ2HeartJHoldsAux_zetaVec_pow hζ _)) (ggQ2HeartJHoldsAux_zetaVec_pow hζ _)
    (ggQ2HeartJHoldsAux_zetaVec_pow hζ _) i hqi (hcent b hb)
  have h1 := hZ (Φ w.1.1) ⟨0, Φ w.1.1, hsupp w.1 w.2, rfl⟩
  rw [ggQ2HeartJHoldsAux_rootChar_eq_one_iff hζo hζ] at h1
  rw [hΦform, hκL]
  exact h1

end CFSG.StandardType

end
