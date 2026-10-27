module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TwoDefs
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6RatLabel
public import Certificates.Certificate707002
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6FrobAdd
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TwoRatLabelD
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TwoCentre
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6RatLabelA
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6RatLabelD
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6RatLabelOuterD
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6RatDistinct
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6RatTransfer
public import CFSG.LocalAnalysis.StandardType.GGLangSolvBridge
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6CompLabel
public import CFSG.LocalAnalysis.StandardType.GGJ4dRankOne
public import CFSG.LocalAnalysis.StandardType.GGLangSixRoot
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TypeAOne
import CFSG.Quasithin.H13.NQTermLinearThreeTools
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Basic
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Certs
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section LangComp

open CFSG.StandardType.LangRat

theorem e6TwoLangComp_prod_zpow_eq_zpow_sum {ι G : Type*} [CommGroup G] (s : Finset ι)
    (f : ι → ℤ) (x : G) : ∏ i ∈ s, x ^ f i = x ^ ∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add]

theorem e6TwoLangComp_rootChar_eq_pow_sum {τ : Tag} {K : Type} [Field K]
    (a : Fin τ.rank → Kˣ) (ω : Kˣ) (e : Fin τ.rank → ℕ)
    (ha : ∀ i, a i = ω ^ e i) (γ : Fin τ.rank → ℤ) :
    rootChar a γ = ω ^ (∑ i, (e i : ℤ) * γ i) := by
  simp only [rootChar]
  calc ∏ i, a i ^ γ i
      = ∏ i, (ω ^ (e i : ℤ)) ^ γ i := by
        apply Finset.prod_congr rfl
        intro i _
        rw [ha i, zpow_natCast]
    _ = ∏ i, ω ^ ((e i : ℤ) * γ i) := by
        apply Finset.prod_congr rfl
        intro i _
        rw [zpow_mul]
    _ = ω ^ (∑ i, (e i : ℤ) * γ i) := by
        simpa using e6TwoLangComp_prod_zpow_eq_zpow_sum Finset.univ
          (fun i => (e i : ℤ) * γ i) ω

theorem e6TwoLangComp_rootChar_single {τ : Tag} {K : Type} [Field K]
    (a : Fin τ.rank → Kˣ) (i : Fin τ.rank) : rootChar a (Pi.single i 1) = a i := by
  simpa using rootChar_nsmul_single a i 1

theorem e6TwoLangComp_natPow_eq_zpow_mul {G : Type*} [CommGroup G] (x : G) (m n : ℕ) :
    (x ^ m) ^ n = x ^ ((m : ℤ) * (n : ℤ)) := by
  calc (x ^ m) ^ n = (x ^ (m : ℤ)) ^ (n : ℤ) := by rw [zpow_natCast, zpow_natCast]
    _ = x ^ ((m : ℤ) * (n : ℤ)) := by rw [zpow_mul]

theorem e6TwoLangComp_zmod_eq_of_zpow_eq {G : Type*} [CommGroup G] {x : G}
    (hx : IsPrimitiveRoot x 3) {A B : ℤ} (h : x ^ A = x ^ B) : (A : ZMod 3) = (B : ZMod 3) := by
  have hdvd : (3 : ℤ) ∣ A - B := by
    apply (hx.zpow_eq_one_iff_dvd (A - B)).1
    rw [zpow_sub, h, mul_inv_cancel]
  have h0 : ((A - B : ℤ) : ZMod 3) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (A - B) 3).2 hdvd
  rw [Int.cast_sub, sub_eq_zero] at h0
  exact h0

theorem e6TwoLangComp_zmod_sum_val {n : ℕ} (v : Fin n → ZMod 3) (γ : Fin n → ℤ) :
    ((∑ k, ((v k).val : ℤ) * γ k : ℤ) : ZMod 3) =
      ∑ k, ((γ k : ℤ) : ZMod 3) * v k := by
  push_cast
  apply Finset.sum_congr rfl
  intro k _
  rw [ZMod.natCast_zmod_val]
  exact mul_comm _ _

theorem e6TwoLangComp_zmod_mul_val {n : ℕ} (v : Fin n → ZMod 3) (q : ℕ) (i : Fin n) :
    ((((v i).val : ℤ) * (q : ℤ) : ℤ) : ZMod 3) = ((q : ℕ) : ZMod 3) * v i := by
  push_cast
  rw [ZMod.natCast_zmod_val, mul_comm]

theorem e6TwoLangComp_exists_componentRoots_eq {τ : Tag} {M M' : Type*}
    [CommGroup M] [CommGroup M']
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {χ' : Multiplicative (Fin τ.rank → ℤ) →* M'}
    (h : kernelRoots χ = kernelRoots χ') (i' : KernelComponent χ') :
    ∃ i : KernelComponent χ, componentRoots χ i = componentRoots χ' i' := by
  induction i' using Quotient.inductionOn with
  | h a =>
    obtain ⟨α, hα'⟩ := a
    exact ⟨⟦⟨α, h.ge hα'⟩⟧,
      CFSG.LieType.Chevalley.OddToralOrdinary.componentRoots_eq_of_kernelRoots_eq h (h.ge hα') hα'⟩

theorem e6TwoLangComp_admissible
    {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup Tag.E6 L p₀) (hq : S.D.q = 2)
    {a : Fin Tag.E6.rank → Lˣ} (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus) (ω : L)
    (hω : IsPrimitiveRoot ω 3) (v : Fin Tag.E6.rank → ZMod 3)
    (hv : ∀ i, ((a i : Lˣ) : L) = ω ^ (v i).val) :
    E6Admissible (fun i => S.ρ (Pi.single i 1)) v 2 ∧
      kernelRoots (rootCharHom a) =
        {γ | IsRoot Tag.E6 γ ∧ ∑ k, ((γ k : ℤ) : ZMod 3) * v k = 0} := by
  classical
  have hq' : ((S.D.q : ℕ) : ZMod 3) = 2 := by rw [hq]; norm_num
  have hmain :
      E6Admissible (fun i => S.ρ (Pi.single i 1)) v ((S.D.q : ℕ) : ZMod 3) ∧
        kernelRoots (rootCharHom a) =
          {γ | IsRoot Tag.E6 γ ∧ ∑ k, ((γ k : ℤ) : ZMod 3) * v k = 0} := by
    set ω₀ : Lˣ := Units.mk0 ω (hω.ne_zero (by norm_num)) with hω₀def
    have hω₀ : IsPrimitiveRoot ω₀ 3 := by
      rw [hω₀def]
      exact IsPrimitiveRoot.coe_units_iff.1 (by simpa only [Units.val_mk0] using hω)
    have hae : ∀ i, a i = ω₀ ^ (v i).val := by
      intro i
      rw [hω₀def]
      exact Units.ext (by simpa only [Units.val_pow_eq_pow_val, Units.val_mk0] using hv i)
    have hrootChar : ∀ γ : Fin Tag.E6.rank → ℤ,
        rootChar a γ = ω₀ ^ (∑ k, ((v k).val : ℤ) * γ k) :=
      fun γ => e6TwoLangComp_rootChar_eq_pow_sum a ω₀ (fun k => (v k).val) hae γ
    refine ⟨?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · intro i
        exact (S.frob.isRoot_iff (Pi.single i 1)).2 (IsRoot.basis i)
      · intro i j
        exact S.frob.iform_eq (Pi.single i 1) (Pi.single j 1)
      · intro i
        have hroot := S.frob.rootChar_eq a hT (Pi.single i 1) (IsRoot.basis i)
        have hB : rootChar a (Pi.single i 1) ^ S.D.q =
            ω₀ ^ (((v i).val : ℤ) * (S.D.q : ℤ)) := by
          rw [e6TwoLangComp_rootChar_single a i, hae i, e6TwoLangComp_natPow_eq_zpow_mul]
        have hAB : ω₀ ^ (∑ k, ((v k).val : ℤ) * (S.ρ (Pi.single i 1)) k) =
            ω₀ ^ (((v i).val : ℤ) * (S.D.q : ℤ)) := by
          rw [← hrootChar (S.ρ (Pi.single i 1)), hroot, hB]
        have hz := e6TwoLangComp_zmod_eq_of_zpow_eq hω₀ hAB
        rw [e6TwoLangComp_zmod_sum_val v (S.ρ (Pi.single i 1)),
          e6TwoLangComp_zmod_mul_val v S.D.q i] at hz
        exact hz
    · ext γ
      rw [kernelRoots_rootCharHom]
      simp only [Set.mem_setOf_eq]
      refine and_congr_right fun _ => ?_
      rw [hrootChar γ, hω₀.zpow_eq_one_iff_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd,
        ← e6TwoLangComp_zmod_sum_val v γ]
  rwa [hq'] at hmain

theorem e6TwoLangComp_compRank_eq_one_of_ncard_eq_two
    {τ : Tag} {L : Type} [Field L]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* Lˣ} (i : KernelComponent χ)
    (h2 : (componentRoots χ i).ncard = 2) :
    compRank (componentRoots χ i) = 1 := by
  obtain ⟨β, hβ, hC⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.exists_pair_of_rank_one i h2
  rw [hC]
  set a : Fin τ.rank → ℚ := fun j => (β j : ℚ) with ha
  have ha0 : a ≠ 0 := by
    intro h
    apply hβ.ne_zero
    funext j
    have hj : (β j : ℚ) = 0 := by simpa [a] using congrFun h j
    exact_mod_cast hj
  have hβneg : (fun j => (((-β) j : ℤ) : ℚ)) = -a := by
    ext j
    simp [a, Pi.neg_apply]
  have himg : (fun γ : Fin τ.rank → ℤ => fun j => (γ j : ℚ)) '' ({β, -β} : Set _) =
      ({a, -a} : Set (Fin τ.rank → ℚ)) := by
    rw [Set.image_pair, hβneg, ← ha]
  have hspan : Submodule.span ℚ ({a, -a} : Set (Fin τ.rank → ℚ)) =
      Submodule.span ℚ ({a} : Set (Fin τ.rank → ℚ)) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      intro x hx
      rcases hx with rfl | hx
      · exact Submodule.subset_span (Set.mem_singleton a)
      · rw [Set.mem_singleton_iff] at hx
        rw [hx]
        exact Submodule.neg_mem _ (Submodule.subset_span (Set.mem_singleton a))
    · rw [Submodule.span_le]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact Submodule.subset_span (Set.mem_insert a _)
  simp only [compRank]
  rw [himg, hspan]
  exact finrank_span_singleton ha0

theorem e6TwoLangComp_solv_iff
    {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup Tag.E6 L p₀) (hq : S.D.q = 2)
    {a : Fin Tag.E6.rank → Lˣ} (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus)
    (hap : ∀ j, a j ^ 3 = 1) (h1 : rootDiagUnit Tag.E6 a ≠ 1)
    (i : KernelComponent (rootCharHom a)) :
    E6SolvTwo S.ρ (componentRoots (rootCharHom a) i) ↔
      LangSmallSolv 2 S.ρ (rootCharHom a) i := by
  classical
  constructor
  · intro h
    rcases h with ⟨hr1, horb1⟩ | ⟨hr2, hn6, horb1, hnotin⟩
    · left
      refine ⟨?_, ?_⟩
      · rw [horb1]; norm_num
      · exact j4d_rank_one_ncard (Or.inr (Or.inl rfl))
          (isRootComponent_componentRoots i) hr1
    · right
      refine ⟨?_, ?_, hn6⟩
      · rw [horb1]; norm_num
      · exact twistKind_A2_of_not_inner S.ρ (rootCharHom a) i hr2 hn6 (by
          rwa [horb1, Function.iterate_one])
  · intro h
    rcases h with ⟨hq3, hn2⟩ | ⟨hq2, hk, hn6⟩
    · left
      refine ⟨e6TwoLangComp_compRank_eq_one_of_ncard_eq_two i hn2, ?_⟩
      obtain ⟨hs0, -, -⟩ := outer_componentOrbitLength_spec S hT i
      have hle : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) ≤ 1 := by
        by_contra hc
        rw [not_le] at hc
        have h2 : 2 ^ 2 ≤ 2 ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) :=
          Nat.pow_le_pow_right (by norm_num) hc
        omega
      omega
    · right
      have hcr : compRank (componentRoots (rootCharHom a) i) = 2 :=
        compRank_eq_two_of_ncard_eq_six (isRootComponent_componentRoots i) hn6
      have horb1 : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1 := by
        apply Nat.pow_right_injective (by norm_num : 2 ≤ 2)
        simpa using hq2
      have hnotin : ¬ twistInner (componentRoots (rootCharHom a) i)
          ((S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))) := by
        intro hti
        unfold twistKind at hk
        have hti' : twistInner (componentRoots (rootCharHom a) i)
            ((S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[
              componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)]) := by
          rwa [horb1, Function.iterate_one]
        rw [if_pos hti'] at hk
        exact absurd hk (by decide)
      exact ⟨hcr, hn6, horb1, hnotin⟩

theorem e6TwoLangComp_lambda2_rank_one {lab : LargeEvenLabel}
    (h : LargeEvenInLambda2 lab) (hr : lab.rank = 1) : lab.tag = .A ∧ 2 ≤ lab.n := by
  rcases lab with ⟨tag, r, n⟩
  simp only at hr
  subst hr
  simp only [LargeEvenInLambda2] at h
  cases tag <;>
    first
      | exact ⟨rfl, h.2.2 rfl⟩
      | exact ⟨rfl, h.2.2 trivial⟩
      | exact absurd h.2.1 (by decide)
      | omega

theorem e6TwoLangComp_not_solv
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ} (S : LangSetup Tag.E6 L p₀)
    (hq : S.D.q = 2) {a : Fin Tag.E6.rank → Lˣ} (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus)
    (hap : ∀ j, a j ^ 3 = 1) (h1 : rootDiagUnit Tag.E6 a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (hQS : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    ¬ E6SolvTwo S.ρ (componentRoots (rootCharHom a) i) := by
  classical
  intro hsolv
  rcases hsolv with ⟨hr1, horb1⟩ | ⟨hr2, hn6, horb1, hnotin⟩
  · have hn2 : (componentRoots (rootCharHom a) i).ncard = 2 :=
      j4d_rank_one_ncard (Or.inr (Or.inl rfl)) (isRootComponent_componentRoots i) hr1
    have hA : 1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
        (componentRoots (rootCharHom a) i).ncard =
          compRank (componentRoots (rootCharHom a) i) *
            (compRank (componentRoots (rootCharHom a) i) + 1) := by
      rw [hr1, hn2]; norm_num
    obtain ⟨lab, hdeg, hrank, -, -, hRL⟩ :=
      rationalLabel_typeA S Nat.prime_three hT hap h1 i hA hQS
    have hn1 : lab.n = 1 := by
      apply Nat.pow_right_injective (by norm_num : 2 ≤ 2)
      dsimp only
      rw [hdeg, horb1, hq]
    have hn2le : 2 ≤ lab.n := by
      have hrank1 : lab.rank = 1 := by rw [hrank, hr1]
      exact (e6TwoLangComp_lambda2_rank_one hRL.1 hrank1).2
    omega
  · have hA : 1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
        (componentRoots (rootCharHom a) i).ncard =
          compRank (componentRoots (rootCharHom a) i) *
            (compRank (componentRoots (rootCharHom a) i) + 1) := by
      rw [hr2, hn6]; norm_num
    obtain ⟨lab, hdeg, hrank, -, hsu, hRL⟩ :=
      rationalLabel_typeA S Nat.prime_three hT hap h1 i hA hQS
    have hkind : twistKind S.ρ (rootCharHom a) i = .suN := by
      apply twistKind_A2_of_not_inner S.ρ (rootCharHom a) i hr2 hn6
      rwa [horb1, Function.iterate_one]
    have htag : lab.tag = .twA := hsu hkind
    have hn1 : lab.n = 1 := by
      apply Nat.pow_right_injective (by norm_num : 2 ≤ 2)
      dsimp only
      rw [hdeg, horb1, hq]
    have hn2le : 2 ≤ lab.n := by
      have hrl := hRL.1
      rcases lab with ⟨tag, r, n⟩
      simp only at htag hrank
      subst htag
      have hr : r = 2 := by rw [hrank, hr2]
      subst hr
      simp only [LargeEvenInLambda2] at hrl
      first
        | exact hrl.2.2 rfl
        | exact hrl.2.2 trivial
    omega

theorem e6TwoLangComp_others
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ} (S : LangSetup Tag.E6 L p₀)
    (hq : S.D.q = 2) {a : Fin Tag.E6.rank → Lˣ} (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus)
    (hap : ∀ j, a j ^ 3 = 1) (h1 : rootDiagUnit Tag.E6 a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (hQS : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))
    (huniq : ∀ i' : KernelComponent (rootCharHom a),
      CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i') →
        rationalComponent S.ρ S.Γ (rootCharHom a) i' =
          rationalComponent S.ρ S.Γ (rootCharHom a) i)
    {v : Fin Tag.E6.rank → ZMod 3}
    (hker : kernelRoots (rootCharHom a) = kernelRoots (e6Chi v))
    (Ψ' : Set (Fin Tag.E6.rank → ℤ)) (hΨ' : E6KerComponent v Ψ')
    (hno : ∀ k : ℕ, (S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[k] ''
      componentRoots (rootCharHom a) i ≠ Ψ') :
    E6SolvTwo S.ρ Ψ' := by
  classical
  obtain ⟨i', rfl⟩ := hΨ'
  obtain ⟨i'', hi''⟩ := e6TwoLangComp_exists_componentRoots_eq hker i'
  have hgoal : E6SolvTwo S.ρ (componentRoots (rootCharHom a) i'') := by
    refine (e6TwoLangComp_solv_iff S hq hT hap h1 i'').2 ?_
    by_contra hnot
    have hnot' : ¬ LangSmallSolv S.D.q S.ρ (rootCharHom a) i'' := by rwa [hq]
    have hQS'' : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i'') :=
      isQuasisimple_rationalComponent_of_not_langSmallSolv S (by decide) Nat.prime_three
        (by
          have h2 : ((2 : ℕ) : L) = 0 := CharP.cast_eq_zero L 2
          have h3 : ((3 : ℕ) : L) = 1 := by
            have hcast : ((3 : ℕ) : L) = ((2 : ℕ) : L) + 1 := by norm_num
            rw [hcast, h2, zero_add]
          rw [h3]; exact one_ne_zero)
        hT hap h1 i'' hnot'
    have heq : rationalComponent S.ρ S.Γ (rootCharHom a) i'' =
        rationalComponent S.ρ S.Γ (rootCharHom a) i := huniq i'' hQS''
    have hno' : ∀ k : ℕ, (S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[k] ''
        componentRoots (rootCharHom a) i ≠ componentRoots (rootCharHom a) i'' := by
      intro k
      rw [hi'']
      exact hno k
    exact (rationalComponent_ne_of_not_orbit S hT i i'' hno' hQS) heq.symm
  exact hi'' ▸ hgoal

end LangComp

end CFSG.StandardType.TablePThreeKG

end
