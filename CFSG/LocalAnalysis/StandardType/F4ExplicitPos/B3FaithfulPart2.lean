module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.B3Exact
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.B3FaithfulPart1

@[expose] public section

public section

namespace CFSG.StandardType.F4ExplicitPos.B3Faithful
open CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Chevalley CFSG.LieType.BorelTits
  CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.LieType.RootSystem
variable {τ : Tag} {K : Type} [Field K]

theorem rootVec_fixed_of_simple
    {h : Module.End K (RootModule τ K)}
    (hn : ∀ i, h * (weylElt τ K i 1 : Module.End K (RootModule τ K)) =
      (weylElt τ K i 1 : Module.End K (RootModule τ K)) * h)
    (hs : ∀ j, h (rootVec τ K (Pi.single j 1)) = rootVec τ K (Pi.single j 1))
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) : h (rootVec τ K α) = rootVec τ K α := by
  induction hα with
  | basis j => exact hs j
  | reflect i hv ih => exact rootVec_fixed_reflect (hn i) hv ih

theorem commute_weylElt
    {h : Module.End K (RootModule τ K)} {i : Fin τ.rank}
    (hx : h * xOp τ K i 1 = xOp τ K i 1 * h) (hy : h * yOp τ K i (-1) = yOp τ K i (-1) * h) :
    h * (weylElt τ K i 1 : Module.End K (RootModule τ K)) =
      (weylElt τ K i 1 : Module.End K (RootModule τ K)) * h := by
  have hw : (weylElt τ K i 1 : Module.End K (RootModule τ K)) =
      xOp τ K i 1 * yOp τ K i (-1) * xOp τ K i 1 := by
    rw [coe_weylElt, inv_one, Units.val_one]
  rw [hw]
  calc h * (xOp τ K i 1 * yOp τ K i (-1) * xOp τ K i 1)
      = (h * xOp τ K i 1) * yOp τ K i (-1) * xOp τ K i 1 := by simp only [mul_assoc]
    _ = xOp τ K i 1 * (h * yOp τ K i (-1)) * xOp τ K i 1 := by
      rw [hx]
      simp only [mul_assoc]
    _ = xOp τ K i 1 * yOp τ K i (-1) * (h * xOp τ K i 1) := by
      rw [hy]
      simp only [mul_assoc]
    _ = xOp τ K i 1 * yOp τ K i (-1) * xOp τ K i 1 * h := by
      rw [hx]
      simp only [mul_assoc]

theorem rootVec_fixed_of_foldr
    {h : Module.End K (RootModule τ K)}
    (hn : ∀ i, h * (weylElt τ K i 1 : Module.End K (RootModule τ K)) =
      (weylElt τ K i 1 : Module.End K (RootModule τ K)) * h)
    {v : Fin τ.rank → ℤ} (hv : IsRoot τ v) (u : List (Fin τ.rank))
    (hfix : h (rootVec τ K (u.foldr (reflect τ) v)) = rootVec τ K (u.foldr (reflect τ) v)) :
    h (rootVec τ K v) = rootVec τ K v := by
  induction u with
  | nil => exact hfix
  | cons i u ih =>
    apply ih
    have hβ : IsRoot τ (u.foldr (reflect τ) v) := by
      clear ih hfix
      induction u with
      | nil => exact hv
      | cons j u ih' => exact .reflect j ih'
    have := rootVec_fixed_reflect (hn i) (.reflect i hβ) hfix
    rwa [reflect_reflect] at this

theorem eq_one_of_fixes_simple
    {h : Module.End K (RootModule τ K)}
    (hx : ∀ i, h * xOp τ K i 1 = xOp τ K i 1 * h)
    (hy : ∀ i, h * yOp τ K i (-1) = yOp τ K i (-1) * h)
    (hs : ∀ j, h (rootVec τ K (Pi.single j 1)) = rootVec τ K (Pi.single j 1)) : h = 1 := by
  have hr : ∀ α, IsRoot τ α → h (rootVec τ K α) = rootVec τ K α :=
    fun α hα => rootVec_fixed_of_simple (fun i => commute_weylElt (hx i) (hy i)) hs hα
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, Module.End.one_apply]
  rcases b with i | ⟨α, hα⟩
  · change h (hVec τ K i) = hVec τ K i
    have key := congrArg (fun f : Module.End K (RootModule τ K) =>
      f (rootVec τ K (-Pi.single i 1))) (hx i)
    simp only [Module.End.mul_apply, hr _ (isRoot_neg_single τ i), xOp_rootVec_neg_single',
      one_smul, one_pow, map_add, hr _ (isRoot_single τ i)] at key
    exact add_left_cancel (add_right_cancel key)
  · rw [← rootVec_eq_single hα]
    exact hr α hα

theorem wordProd_smul {τ : Tag} (l : List (Fin τ.rank)) (v : Fin τ.rank → ℤ) :
    (coxeterSystem τ).wordProd l • v = l.foldr (reflect τ) v := by
  induction l with
  | nil => rw [CoxeterSystem.wordProd_nil, one_smul, List.foldr_nil]
  | cons i l ih => rw [CoxeterSystem.wordProd_cons, mul_smul, ih, simple_smul, List.foldr_cons]

theorem mem_shortModule_of_mem
    (hp : (ReeTag.F4.prime : K) = 0) {g : ModGL ReeTag.F4.tag K}
    (hg : g ∈ adjointGroup ReeTag.F4.tag K) {v : RootModule ReeTag.F4.tag K} (hv : v ∈
        ReeTag.F4.shortModule K) :
    (g : Module.End K (RootModule ReeTag.F4.tag K)) v ∈ ReeTag.F4.shortModule K := by
  induction hg using Subgroup.closure_induction'' generalizing v with
  | mem g hg =>
    obtain ⟨i, c, h | h⟩ := hg
    · rw [h]
      exact xOp_mem_shortModule K hp i c hv
    · rw [h]
      exact yOp_mem_shortModule K hp i c hv
  | inv_mem g hg =>
    obtain ⟨i, c, h | h⟩ := hg
    · rw [show g = xUnit ReeTag.F4.tag K i c from Units.ext h, coe_xUnit_inv]
      exact xOp_mem_shortModule K hp i (-c) hv
    · rw [show g = yUnit ReeTag.F4.tag K i c from Units.ext h, coe_yUnit_inv]
      exact yOp_mem_shortModule K hp i (-c) hv
  | one => simpa using hv
  | mul g g' _ _ ihg ihg' =>
    rw [Units.val_mul, Module.End.mul_apply]
    exact ihg (ihg' hv)

theorem rootVec_mem_shortModule {β : Fin ReeTag.F4.tag.rank → ℤ} (hβ : β ∈ ReeTag.F4.shortRoots) :
    rootVec ReeTag.F4.tag K β ∈ ReeTag.F4.shortModule K :=
  Submodule.subset_span (Or.inr ⟨β, hβ, rfl⟩)

theorem quadForm_neg (α : Fin ReeTag.F4.tag.rank →
    ℤ) : ReeTag.F4.quadForm (-α) = ReeTag.F4.quadForm α := by
  simp [quadForm, Matrix.mulVec_neg]

theorem neg_mem_shortRoots {β : Fin ReeTag.F4.tag.rank → ℤ} (hβ : β ∈ ReeTag.F4.shortRoots) :
    -β ∈ ReeTag.F4.shortRoots :=
  ⟨IsRoot.neg hβ.1, by rw [lengthParam, quadForm_neg]; exact hβ.2⟩

theorem isRoot_of_memDec
    {v : Fin ReeTag.F4.tag.rank → ℤ}
    (h : ReeTag.F4.tag.stringData.memDec ReeTag.F4.tag.rootCertificate v = true) : IsRoot
        ReeTag.F4.tag v :=
  (StringData.memDec_iff ReeTag.F4.tag.rootCertificate_check ReeTag.F4.tag.stringData_check).1 h

theorem not_isRoot_of_memDec
    {v : Fin ReeTag.F4.tag.rank → ℤ}
    (h : ReeTag.F4.tag.stringData.memDec ReeTag.F4.tag.rootCertificate v = false) : ¬IsRoot
        ReeTag.F4.tag v := fun hv => by
  rw [← StringData.memDec_iff ReeTag.F4.tag.rootCertificate_check ReeTag.F4.tag.stringData_check,
      h] at hv
  exact Bool.false_ne_true hv

theorem mem_shortRoots_of_memDec
    {v : Fin ReeTag.F4.tag.rank → ℤ}
    (h : ReeTag.F4.tag.stringData.memDec ReeTag.F4.tag.rootCertificate v = true) (hq :
        ReeTag.F4.quadForm v = 2) :
    v ∈ ReeTag.F4.shortRoots :=
  ⟨isRoot_of_memDec h, lengthParam_eq_one_iff.2 hq⟩

theorem mem_shortKernel {g : adjointGroup ReeTag.F4.tag K} :
    g ∈ ReeTag.F4.shortKernel K ↔ ∀ v ∈ ReeTag.F4.shortModule K, glRep _ g v = v :=
  Iff.rfl

theorem shortKernel_normal
    (hp : (ReeTag.F4.prime : K) = 0) : (ReeTag.F4.shortKernel K).Normal := by
  refine ⟨fun g hg x v hv => ?_⟩
  have hv' : glRep _ x⁻¹ v ∈ ReeTag.F4.shortModule K := mem_shortModule_of_mem hp (x⁻¹).2 hv
  rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hg _ hv',
    ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

theorem negOne_smul_single (i : Fin ReeTag.F4.tag.rank) :
    ReeTag.F4.negOne • (Pi.single i 1 : Fin ReeTag.F4.tag.rank → ℤ) = -Pi.single i 1 := by
  rw [show ReeTag.F4.negOne = (coxeterSystem ReeTag.F4.tag).wordProd ReeTag.F4.negOneWord from rfl,
    wordProd_smul]
  revert i
  decide +kernel

theorem negOne_smul (v : Fin ReeTag.F4.tag.rank → ℤ) : ReeTag.F4.negOne • v = -v := by
  have h : weylAction (isFiniteType_cartan ReeTag.F4.tag) ReeTag.F4.negOne = -LinearMap.id := by
    refine LinearMap.pi_ext fun i x => ?_
    rw [← mul_one x, ← smul_eq_mul, Pi.single_smul, map_smul, map_smul, ← smul_def,
      negOne_smul_single]
    simp
  rw [smul_def, h]
  rfl

theorem shortPair_spec : ∀ i : Fin ReeTag.F4.tag.rank,
    (ReeTag.F4.tag.stringData.memDec ReeTag.F4.tag.rootCertificate (ReeTag.F4.shortPair i).1 = true
        ∧
      ReeTag.F4.quadForm (ReeTag.F4.shortPair i).1 = 2) ∧
    ((ReeTag.F4.shortPair i).2 = 0 ∨
      (ReeTag.F4.tag.stringData.memDec ReeTag.F4.tag.rootCertificate (ReeTag.F4.shortPair i).2 =
          true ∧
        ReeTag.F4.quadForm (ReeTag.F4.shortPair i).2 = 2)) ∧
    (Pi.single i 1 : Fin ReeTag.F4.tag.rank →
        ℤ) = (ReeTag.F4.shortPair i).1 - (ReeTag.F4.shortPair i).2 := by
  decide +kernel

theorem eq_one_of_forall_shortRoots
    {w : WeylGroup ReeTag.F4.tag} (hw : ∀ β ∈ ReeTag.F4.shortRoots, w • β = β) :
    w = 1 := by
  refine ext_single fun i => ?_
  obtain ⟨⟨h1, h1'⟩, h2, he⟩ := shortPair_spec i
  rw [one_smul, he, smul_sub, hw _ (mem_shortRoots_of_memDec h1 h1')]
  rcases h2 with h2 | ⟨h2, h2'⟩
  · rw [h2, smul_zero]
  · rw [hw _ (mem_shortRoots_of_memDec h2 h2')]

theorem longWitness_spec : ∀ j : Fin ReeTag.F4.tag.rank,
    (ReeTag.F4.tag.stringData.memDec ReeTag.F4.tag.rootCertificate (Pi.single j 1) = true ∧
      ReeTag.F4.quadForm (Pi.single j 1) = 2) ∨
    (ReeTag.F4.witnessRoot j ≠ ReeTag.F4.witnessSingle j ∧
        ReeTag.F4.witnessRoot j ≠ -ReeTag.F4.witnessSingle j ∧
      ReeTag.F4.tag.stringData.memDec ReeTag.F4.tag.rootCertificate (ReeTag.F4.witnessRoot j +
          ReeTag.F4.witnessSingle j) =
        true ∧
      ReeTag.F4.quadForm (ReeTag.F4.witnessRoot j + ReeTag.F4.witnessSingle j) = 2 ∧
      ReeTag.F4.tag.stringData.memDec ReeTag.F4.tag.rootCertificate (ReeTag.F4.witnessRoot j -
          ReeTag.F4.witnessSingle j) =
        false) := by
  decide +kernel

theorem rootVec_single_fixed
    {h : Module.End K (RootModule ReeTag.F4.tag K)} (hh : PreservesWeights h)
    (hx : ∀ i, h * xOp ReeTag.F4.tag K i 1 = xOp ReeTag.F4.tag K i 1 * h)
    (hn : ∀ i, h * (weylElt ReeTag.F4.tag K i 1 : Module.End K (RootModule ReeTag.F4.tag K)) =
      (weylElt ReeTag.F4.tag K i 1 : Module.End K (RootModule ReeTag.F4.tag K)) * h)
    (hI : ∀ β ∈ ReeTag.F4.shortRoots,
        h (rootVec ReeTag.F4.tag K β) = rootVec ReeTag.F4.tag K β) (j : Fin ReeTag.F4.tag.rank) :
    h (rootVec ReeTag.F4.tag K (Pi.single j 1)) = rootVec ReeTag.F4.tag K (Pi.single j 1) := by
  rcases longWitness_spec j with ⟨h1, h2⟩ | ⟨h1, h2, h3, h4, h5⟩
  · exact hI _ (mem_shortRoots_of_memDec h1 h2)
  · have hα : IsRoot ReeTag.F4.tag (ReeTag.F4.witnessRoot j) := by
      unfold witnessRoot
      induction (ReeTag.F4.longWitness j).1 with
      | nil => exact .basis j
      | cons i u ih => exact .reflect i ih
    exact rootVec_fixed_of_foldr hn (.basis j) _ (rootVec_fixed_of_witness hh (hx _) hα h1 h2
      (isRoot_of_memDec h3) (not_isRoot_of_memDec h5) (hI _ (mem_shortRoots_of_memDec h3 h4)))

theorem shortKernel_le_B
    (S : RootSubgroups ReeTag.F4.tag K) [Finite K] (hp : (ReeTag.F4.prime : K) = 0) :
    ReeTag.F4.shortKernel K ≤ S.toRootGroupData.B := by
  intro g hg
  obtain ⟨m, b₁, hb₁, b₂, hb₂, rfl⟩ := RootGroupData.exists_mem_doubleCoset
    (D := S.toRootGroupData) S.simple_le_normalizer_Ui S.rankOne S.closure_B_union_n g
  have hQ : ((m : monomialGroup ReeTag.F4.tag K) : adjointGroup ReeTag.F4.tag K) * (b₂ * b₁) ∈
      ReeTag.F4.shortKernel K := by
    have := (shortKernel_normal hp).conj_mem _ hg b₁⁻¹
    convert this using 1
    group
  have hb : b₂ * b₁ ∈ S.toRootGroupData.B := mul_mem hb₂ hb₁
  have hw : (weylHom ReeTag.F4.tag K m)⁻¹ = 1 := eq_one_of_forall_shortRoots fun β hβ =>
    inv_smul_eq_of_fixes S m hb hβ.1 (hQ _ (rootVec_mem_shortModule hβ))
      (hQ _ (rootVec_mem_shortModule (neg_mem_shortRoots hβ)))
  have hmH : (m : adjointGroup ReeTag.F4.tag K) ∈ S.toRootGroupData.H :=
    (RootGroupData.mem_H_iff (D := S.toRootGroupData)).2 ⟨m, inv_eq_one.1 hw, rfl⟩
  exact mul_mem (mul_mem hb₁ (S.toRootGroupData.H_le_B hmH)) hb₂

theorem preservesWeights_of_mem_shortKernel
    (S : RootSubgroups ReeTag.F4.tag K) [Finite K]
    (hp : (ReeTag.F4.prime : K) = 0) {g : adjointGroup ReeTag.F4.tag K} (hg : g ∈
        ReeTag.F4.shortKernel K) :
    PreservesWeights (glRep _ g) := by
  obtain ⟨n, hn⟩ := weylHom_surjective (τ := ReeTag.F4.tag) (K := K) ReeTag.F4.negOne
  have hn' : ∀ v : Fin ReeTag.F4.tag.rank → ℤ, weylHom ReeTag.F4.tag K n • v = -v := fun v => by
    rw [hn]
    exact negOne_smul v
  have hc : (n : adjointGroup ReeTag.F4.tag K)⁻¹ * g * (n : adjointGroup ReeTag.F4.tag K) ∈
      ReeTag.F4.shortKernel K := by
    have := (shortKernel_normal hp).conj_mem _ hg (n : adjointGroup ReeTag.F4.tag K)⁻¹
    rwa [inv_inv] at this
  exact preservesWeights_of_isUpper n hn' (isUpper_of_mem_B S (shortKernel_le_B S hp hg))
    (isUpper_of_mem_B S (shortKernel_le_B S hp hc))

theorem commute_of_mem_shortKernel
    (S : RootSubgroups ReeTag.F4.tag K) [Finite K]
    (hp : (ReeTag.F4.prime : K) = 0) {g : adjointGroup ReeTag.F4.tag K} (hg : g ∈
        ReeTag.F4.shortKernel K)
    {α : Root ReeTag.F4.tag} {s : ℤ} (hs : 0 < s * height α.1) {x : adjointGroup ReeTag.F4.tag K}
    (hx : x ∈ S.X α) : g * x = x * g := by
  have hz : g * x * g⁻¹ * x⁻¹ ∈ ReeTag.F4.shortKernel K := by
    have := mul_mem hg ((shortKernel_normal hp).conj_mem _ (inv_mem hg) x)
    rwa [← mul_assoc, ← mul_assoc] at this
  exact commute_of_preservesWeights (preservesWeights_of_mem_shortKernel S hp hg)
    (preservesWeights_of_mem_shortKernel S hp (inv_mem hg))
    (preservesWeights_of_mem_shortKernel S hp hz) (raisesHeight_of_mem_X S hs hx)

theorem shortKernel_eq_bot_of_rootSubgroups
    (S : RootSubgroups ReeTag.F4.tag K) [Finite K]
    (hp : (ReeTag.F4.prime : K) = 0) : ReeTag.F4.shortKernel K = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun g hg => ?_
  have hx : ∀ i, glRep _ g * xOp ReeTag.F4.tag K i 1 = xOp ReeTag.F4.tag K i 1 * glRep _ g := fun i
      => by
    have := congrArg (glRep _) (commute_of_mem_shortKernel S hp hg (α := simpleRoot ReeTag.F4.tag i)
      (s := 1) (by simp [simpleRoot])
      ((S.mem_simple i (xElement i 1)).2 ⟨1, rfl⟩))
    rwa [map_mul, map_mul] at this
  have hy : ∀ i, glRep _ g * yOp ReeTag.F4.tag K i (-1) = yOp ReeTag.F4.tag K i (-1) * glRep _
      g := fun i => by
    have := congrArg (glRep _) (commute_of_mem_shortKernel S hp hg (α :=
        -simpleRoot ReeTag.F4.tag i)
      (s := -1) (by simp [simpleRoot])
      ((S.mem_neg_simple i (yElement i (-1))).2 ⟨-1, rfl⟩))
    rwa [map_mul, map_mul] at this
  have h1 : glRep _ g = 1 := eq_one_of_fixes_simple hx hy
    (rootVec_single_fixed (preservesWeights_of_mem_shortKernel S hp hg) hx
      (fun i => commute_weylElt (hx i) (hy i))
      (fun β hβ => hg _ (rootVec_mem_shortModule hβ)))
  exact glRep_injective _ (by rw [h1, map_one])

theorem shortFaithful_of_rootSubgroups
    (S : RootSubgroups ReeTag.F4.tag K) [Finite K]
    (hp : (ReeTag.F4.prime : K) = 0) : ReeTag.F4.ShortFaithful K := by
  intro g hg h
  have : (⟨g, hg⟩ : adjointGroup ReeTag.F4.tag K) ∈ ReeTag.F4.shortKernel K := h
  rw [shortKernel_eq_bot_of_rootSubgroups S hp, Subgroup.mem_bot] at this
  exact congrArg Subtype.val this

theorem f4_shortFaithful
    (K : Type) [Field K] [Finite K] [CharP K 2] :
    ReeTag.F4.ShortFaithful K :=
  shortFaithful_of_rootSubgroups (CFSG.StandardType.F4ExplicitPos.B3Exact.f4RootSubgroups K)
    (CFSG.StandardType.F4ExplicitPos.B3Exact.Narrow.F4_prime_cast_eq_zero K)

end CFSG.StandardType.F4ExplicitPos.B3Faithful

end

end
