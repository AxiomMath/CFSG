module

public import CFSG.LocalAnalysis.StandardType.GGTBJE6ThreeCoord
public import CFSG.LocalAnalysis.StandardType.GGTBJE6ThreeWeyl
public import CFSG.LocalAnalysis.StandardType.GGTBJTwE6Class
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeRootGenFrame
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUDefs
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangTwE6Conj
public import CFSG.LieType.Chevalley.GraphFixedCenterTrivial

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Solomon.Coordinator


theorem ggTBJ_twE6Three_core {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (h3 : 3 ∣ 2 ^ n + 1) {σ : K ≃+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ n) {L' : Type} [Group L'] [Finite L']
    {ψ₀ : L' →* ↥(twistedE6RootGroup K σ)} (hψ₀ : Function.Surjective ψ₀)
    (hker : ψ₀.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    (hker3 : ∀ z ∈ ψ₀.ker, z ^ 3 = 1) {A : Subgroup (MulAut L')} (hA : IsElemAbelian 3 A)
    (hAH : ∀ a ∈ A, ∃ φ ∈ (RecipeExcLang.twConj K σ).range, ∀ l, φ (ψ₀ l) = ψ₀ (a l))
    (h5 : 3 ^ 5 ≤ Nat.card A) (hsc : GGTorusSelfCent 3 A) {y : MulAut L'} (hy : y ∈ A)
    (hy1 : y ≠ 1) {J : Subgroup L'} (hJ : CFSG.Open.IsComponentOf J (fixSubgroup y))
    (hJl : ∀ Q : Subgroup L', CFSG.Open.IsComponentOf Q (fixSubgroup y) → Q ≤ J)
    (hcount : 3 ^ 2 * Nat.card ↥(A ⊓ ⨅ j : J, MulAction.stabilizer (MulAut L') (j : L')) ≤
      Nat.card ↥A) :
    ∃ (n₁ n₂ : L') (h₁ : MulAut.conj n₁ ∈ Subgroup.normalizer (A : Set (MulAut L')))
      (h₂ : MulAut.conj n₂ ∈ Subgroup.normalizer (A : Set (MulAut L'))),
      n₁ ∈ J ∧ n₂ ∈ J ∧ GGTorusWeylElt 3 A n₁ ∧ GGTorusWeylElt 3 A n₂ ∧
      GGIsReflection 3 (ggConjAut A h₁) ∧ GGIsReflection 3 (ggConjAut A h₂) ∧
      ggConjAut A h₁ * ggConjAut A h₂ ≠ ggConjAut A h₂ * ggConjAut A h₁ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (MulAut L') :=
    Finite.of_injective (fun f : MulAut L' => (f.toEquiv : Equiv.Perm L'))
      fun f f' h => MulEquiv.ext fun x => congrArg (fun e : Equiv.Perm L' => e x) h
  have hn1 : 1 ≤ n := by omega
  obtain ⟨ζ, Fr, hζ, hζo, hFr⟩ : ∃ (ζ : (AlgebraicClosure K)ˣ)
      (Fr : AlgebraicClosure K →+* AlgebraicClosure K),
      ζ ^ 3 = 1 ∧ orderOf ζ = 3 ∧ ∀ c, Fr c = c ^ 2 ^ n := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : Fintype K := Fintype.ofFinite K
    haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2 * n)
      (by rw [Fintype.card_eq_nat_card, hK, ← pow_mul, mul_comm])
    haveI : CharP (AlgebraicClosure K) 2 :=
      charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
    haveI : IsAlgClosed (AlgebraicClosure K) := IsAlgClosure.isAlgClosed K
    obtain ⟨ζ, hζp⟩ := CFSG.LieType.SeitzGeneration.exists_primitiveRoot_units
      (L := AlgebraicClosure K) (ℓ := 2) Nat.prime_two Nat.prime_three (by norm_num)
    exact ⟨ζ, iterateFrobenius (AlgebraicClosure K) 2 n, hζp.pow_eq_one, hζp.eq_orderOf.symm,
      fun c => iterateFrobenius_def (R := AlgebraicClosure K) (p := 2) (n := n) (x := c)⟩
  obtain ⟨g, κ, t, T, hg, hglang, hκinj, hκrange, ht, hconj, hTodd, hTfix, hHyp, -⟩ :=
    TwE6ThreeRootGen.exists_frame_torus (L' := L') (ψ₀ := ψ₀) (A := A) (Fr := Fr)
      (ζ := ζ) hn1 hK σ hσ h3 hFr hζ hζo hψ₀ hker hperf hA hAH h5 hsc
  obtain ⟨E, F, -, hFv, hFg⟩ :=
    TwE6ThreeRootGen.exists_twE6Frame (K := K) (σ := σ) (n := n) (p := 3) (Fr := Fr)
      (v := CFSG.HardMathSupport.Lang.E6Descent.twE6W0) (g₀ := g) hFr hg hglang
  have hv : ExcIsLongest TwistTag.E6.tag F.v := by
    rw [hFv]
    exact TwE6ThreeRootGen.excIsLongest_twE6W0
  have htF : ∀ x, baseChangeGL (algebraMap K (AlgebraicClosure K)) (t x) =
      F.g0 * rootDiagUnit TwistTag.E6.tag (TableBExc.E6Three.zetaVec ζ hζ x) * F.g0⁻¹ := by
    intro x
    rw [hFg]
    exact ht x
  have htmul : ∀ x x' : Fin TwistTag.E6.tag.rank → ZMod 3, t (x + x') = t x * t x' := by
    have ht' : ∀ x : Fin TwistTag.E6.tag.rank → ZMod 3,
        baseChangeGL (algebraMap K (AlgebraicClosure K)) (t x) =
          g * rootDiagUnit TwistTag.E6.tag (TableBExc.E6Three.zetaVec ζ hζ x) * g⁻¹ := ht
    intro x x'
    refine baseChangeGL_injective (f := algebraMap K (AlgebraicClosure K)) ?_
    rw [map_mul, ht', ht', ht', ExcFrames.zetaVec_add (τ := TwistTag.E6.tag), rootDiagUnit_mul]
    group
  let V : Set (Fin Tag.E6.rank → ZMod 3) := {x | Multiplicative.ofAdd x ∈ κ.range}
  have hκV : ∀ x, Multiplicative.ofAdd x ∈ κ.range ↔ x ∈ V := fun _ => Iff.rfl
  have hV : V = Set.univ ∨ V = (NoOffRest.hypE6 : Set (Fin Tag.E6.rank → ZMod 3)) := by
    rcases hκrange with h | h
    · left
      ext x
      change Multiplicative.ofAdd x ∈ κ.range ↔ True
      rw [h]
      exact ⟨fun _ => trivial, fun _ => Subgroup.mem_top _⟩
    · right
      ext x
      exact h x
  have hAV : Nat.card ↥A = Nat.card V := by
    refine Nat.card_congr (Equiv.ofBijective (fun a => ⟨Multiplicative.toAdd (κ a),
      MonoidHom.mem_range.2 ⟨a, rfl⟩⟩) ⟨fun a b hab => hκinj ?_, fun x => ?_⟩)
    · exact Multiplicative.toAdd.injective (congrArg Subtype.val hab)
    · obtain ⟨a, ha⟩ := MonoidHom.mem_range.1 x.2
      exact ⟨a, Subtype.ext (by simp only [ha, toAdd_ofAdd])⟩
  have hact : ∀ (a : A) (l : L'), ggKGTwY F (ψ₀ ((a : MulAut L') l)) =
      rootDiagUnit TwistTag.E6.tag
          (TableBExc.E6Three.zetaVec ζ hζ (Multiplicative.toAdd (κ a) : Fin 6 → ZMod 3)) *
        ggKGTwY F (ψ₀ l) * (rootDiagUnit TwistTag.E6.tag
          (TableBExc.E6Three.zetaVec ζ hζ (Multiplicative.toAdd (κ a) : Fin 6 → ZMod 3)))⁻¹ := by
    intro a l
    rw [ggKGTwY_apply, ggKGTwY_apply, hconj a l, map_mul, map_mul, map_inv, htF]
    group
  have hYinj : Function.Injective (ggKGTwY F) := by
    intro x x' h
    rw [ggKGTwY_apply, ggKGTwY_apply] at h
    exact Subtype.ext (baseChangeGL_injective (f := algebraMap K (AlgebraicClosure K))
      (mul_left_cancel (mul_right_cancel h)))
  set t₀ : Fin Tag.E6.rank → ZMod 3 := Multiplicative.toAdd (κ ⟨y, hy⟩) with ht₀
  have hyact : ∀ l, ggKGTwY F (ψ₀ (y l)) =
      rootDiagUnit TwistTag.E6.tag (TableBExc.E6Three.zetaVec ζ hζ t₀) * ggKGTwY F (ψ₀ l) *
        (rootDiagUnit TwistTag.E6.tag (TableBExc.E6Three.zetaVec ζ hζ t₀))⁻¹ :=
    fun l => hact ⟨y, hy⟩ l
  have hd1 : rootDiagUnit TwistTag.E6.tag (TableBExc.E6Three.zetaVec ζ hζ t₀) ≠ 1 := by
    intro hd
    apply hy1
    refine TypeA.mulAut_eq_of_forall ψ₀ hker hperf fun l => hYinj ?_
    rw [hyact l, hd, one_mul, inv_one, mul_one]
    rfl
  obtain ⟨i, hW, hfixJ⟩ := ggTBJ_twE6_class (p := 3) hn hK hσ h3 F hv hζ ψ₀ hψ₀ hker t₀ hd1 y
    hyact hJ hJl
  have hcard : 3 ^ 2 * Nat.card {x : Fin Tag.E6.rank → ZMod 3 // x ∈ V ∧
      ∀ γ ∈ componentRoots (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ t₀)) i,
        ∑ j, (γ j : ZMod 3) * x j = 0} ≤ Nat.card V := by
    have hmem : ∀ x : {x : Fin Tag.E6.rank → ZMod 3 // x ∈ V ∧
        ∀ γ ∈ componentRoots (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ t₀)) i,
          ∑ j, (γ j : ZMod 3) * x j = 0},
        ∃ a : A, κ a = Multiplicative.ofAdd x.1 := fun x => MonoidHom.mem_range.1 x.2.1
    choose φ hφ using hmem
    let f : {x : Fin Tag.E6.rank → ZMod 3 // x ∈ V ∧
        ∀ γ ∈ componentRoots (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ t₀)) i,
          ∑ j, (γ j : ZMod 3) * x j = 0} →
        ↥(A ⊓ ⨅ j : J, MulAction.stabilizer (MulAut L') (j : L')) := fun x =>
      ⟨(φ x : MulAut L'), Subgroup.mem_inf.2 ⟨(φ x).2, Subgroup.mem_iInf.2 fun j => by
        rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]
        refine hfixJ (φ x : MulAut L') x.1 (fun l => ?_) (fun γ hγ => x.2.2 γ hγ) j j.2
        have h := hact (φ x) l
        rw [hφ x] at h
        exact h⟩⟩
    have hf : Function.Injective f := by
      intro x x' h
      have h1 : φ x = φ x' := Subtype.ext (by have h' := congrArg Subtype.val h; exact h')
      have h2 := hφ x
      rw [h1, hφ x'] at h2
      exact Subtype.ext (Multiplicative.ofAdd.injective h2.symm)
    calc 3 ^ 2 * Nat.card {x : Fin Tag.E6.rank → ZMod 3 // x ∈ V ∧
          ∀ γ ∈ componentRoots (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ t₀)) i,
            ∑ j, (γ j : ZMod 3) * x j = 0}
        ≤ 3 ^ 2 * Nat.card ↥(A ⊓ ⨅ j : J, MulAction.stabilizer (MulAut L') (j : L')) :=
          Nat.mul_le_mul_left _ (Nat.card_le_card_of_injective f hf)
      _ ≤ Nat.card ↥A := hcount
      _ = Nat.card V := hAV
  obtain ⟨γ₁, hγ₁, γ₂, hγ₂, w, hwV, hne⟩ := e6Three_exists_noncomm_pair hV i hcard
  let c : ↥A → Fin Tag.E6.rank → ZMod 3 := fun a => Multiplicative.toAdd (κ a)
  have hstep : ∀ γ ∈ componentRoots (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ t₀)) i,
      ∃ (m : L') (hN : MulAut.conj m ∈ Subgroup.normalizer (A : Set (MulAut L'))),
        m ∈ J ∧ GGTorusWeylElt 3 A m ∧ GGIsReflection 3 (ggConjAut A hN) ∧
        ∀ a : A, c (ggConjAut A hN a) = ExcSplitRootGen.excRefl (p := 3) γ (c a) := by
    intro γ hγ
    have hγr : IsRoot Tag.E6 γ := isRoot_of_mem_componentRoots hγ
    obtain ⟨r, hrJ, hr⟩ := TwE6ThreeRootGen.exists_mem_ggKGTwJ_conj hK hσ F hv hζ htF hγr
    obtain ⟨m, hmJ, hmr⟩ := hW γ hγ r hrJ
    have hsH : ∀ x, ExcSplitRootGen.excRefl (p := 3) γ x - x ∈ NoOffRest.hypE6 := fun x => by
      simpa only [ExcSplitRootGen.excRefl] using
        TableBExc.E6Three.adAct_sub_mem_hypE6 (rootReflection γ) x
    have hsV : ∀ x ∈ V, ExcSplitRootGen.excRefl (p := 3) γ x ∈ V := by
      intro x hx
      rcases hV with hV' | hV'
      · rw [hV']
        exact Set.mem_univ _
      · rw [hV'] at hx ⊢
        have h := NoOffRest.hypE6.add_mem (hsH x) (SetLike.mem_coe.1 hx)
        rw [sub_add_cancel] at h
        exact SetLike.mem_coe.2 h
    obtain ⟨hN, hWeyl, hcoord⟩ := e6Three_weylPoint hψ₀ hker hperf
      (center_graphFixedRootGroup_eq_bot (t := TwistTag.E6) (σ := σ.toRingHom) σ.surjective)
      hker3 hκinj hκV htmul hconj hTodd hTfix hHyp (s := ExcSplitRootGen.excRefl (p := 3) γ)
      (ExcSplitRootGen.excRefl_excRefl hγr) hsV hsH (m := m) (fun x => by rw [hmr]; exact hr x)
    exact ⟨m, hN, hmJ, hWeyl, e6Three_isReflection_of_coord hκinj hκV hV hγr hcoord,
      fun a => hcoord a⟩
  obtain ⟨m₁, hN₁, hm₁, hW₁, hR₁, hc₁⟩ := hstep γ₁ hγ₁
  obtain ⟨m₂, hN₂, hm₂, hW₂, hR₂, hc₂⟩ := hstep γ₂ hγ₂
  refine ⟨m₁, m₂, hN₁, hN₂, hm₁, hm₂, hW₁, hW₂, hR₁, hR₂, fun hcomm => hne ?_⟩
  obtain ⟨a, ha⟩ := MonoidHom.mem_range.1 ((hκV w).2 hwV)
  have hca : c a = w := by
    show Multiplicative.toAdd (κ a) = w
    rw [ha]
    rfl
  have h := congrArg (fun φ : MulAut ↥A => c (φ a)) hcomm
  simp only [MulAut.mul_apply, hc₁, hc₂, hca] at h
  exact h

end CFSG.StandardType

end
