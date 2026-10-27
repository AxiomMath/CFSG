module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore

namespace CFSG
end CFSG
open CFSG

/-!
# Strong embedding and the involution core

This file records the basic objects occurring in Theorem SE of
`docs/cfsg-vol4.tex`.  The classification models are kept in `SE.Models` so
the group-theoretic reduction layer does not depend on matrix recognition.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1

universe u

/-- A subgroup `M` of a finite group `X` is strongly embedded when it is
proper, contains an involution, and the intersection of `M` with any distinct
right conjugate contains no involution.  This is the standard criterion
`[IG; 17.11(ii)]`.  The explicit nonvacuity clause is essential for odd-order
groups. -/
@[expose] public def IsStronglyEmbedded {X : Type u} [Group X] [Finite X]
    (M : Subgroup X) : Prop :=
  M ≠ ⊤ ∧
    (∃ x : X, x ∈ M ∧ IsInvolution x) ∧
      ∀ {g : X}, g ∉ M →
        ∀ {x : X}, x ∈ M → x ∈ rightConjugate M g → ¬ IsInvolution x

/-- Conjugating an element of `M` by `g` gives an element of the right
conjugate `M^g`. -/
public theorem rightConjugateElem_mem_rightConjugate
    {X : Type u} [Group X] {M : Subgroup X} {x g : X}
    (hx : x ∈ M) :
    rightConjugateElem x g ∈ rightConjugate M g := by
  rw [rightConjugate, Subgroup.conjBy, Subgroup.mem_map]
  refine ⟨x, hx, ?_⟩
  simp [rightConjugateElem, mul_assoc]

/-- Conjugating an element of `M^(g⁻¹)` by `g` returns an element of
`M`. -/
public theorem rightConjugateElem_mem_of_mem_rightConjugate
    {X : Type u} [Group X] {M : Subgroup X} {g x : X}
    (hx : x ∈ rightConjugate M g⁻¹) :
    rightConjugateElem x g ∈ M := by
  rw [rightConjugate, Subgroup.conjBy, Subgroup.mem_map] at hx
  rcases hx with ⟨y, hy, hxy⟩
  have hyx : y = rightConjugateElem x g := by
    rw [← hxy]
    simp [rightConjugateElem, mul_assoc]
  exact hyx ▸ hy

private theorem isPGroup_zpowers_of_involution
    {X : Type u} [Group X] [Finite X] {x : X} (hx : IsInvolution x) :
    IsPGroup 2 (Subgroup.zpowers x) := by
  have horder : orderOf x = 2 :=
    (orderOf_eq_prime_iff).2 ⟨hx.sq_eq_one, hx.ne_one⟩
  apply IsPGroup.of_card (p := 2) (G := Subgroup.zpowers x) (n := 1)
  simp [Nat.card_zpowers, horder]

namespace IsInvolution

/-- An injective group homomorphism sends an involution to an involution. -/
public theorem map_of_injective
    {H X : Type*} [Group H] [Group X]
    {x : H} (hx : IsInvolution x) (f : H →* X)
    (hf : Function.Injective f) :
    IsInvolution (f x) := by
  unfold IsInvolution at hx ⊢
  exact ⟨fun h => hx.1 (hf (by simpa using h)),
    by simpa using congrArg f hx.2⟩

/-- An ambient involution lying in a subgroup is an involution of the
subgroup. -/
public theorem subtype
    {X : Type u} [Group X] {M : Subgroup X} {x : X}
    (hx : IsInvolution x) (hxM : x ∈ M) :
    IsInvolution (⟨x, hxM⟩ : M) := by
  unfold IsInvolution at hx ⊢
  constructor
  · intro h
    apply hx.1
    exact congrArg Subtype.val h
  · apply Subtype.ext
    exact hx.2

end IsInvolution

namespace IsStronglyEmbedded

/-- A strongly embedded subgroup is proper. -/
public theorem ne_top {X : Type u} [Group X] [Finite X]
    {M : Subgroup X} (hM : IsStronglyEmbedded M) : M ≠ ⊤ :=
  hM.1

/-- If an involution lies in both `M` and its right conjugate by `g`, then the
conjugator already lies in a strongly embedded subgroup `M`. -/
public theorem mem_of_involution_mem_rightConjugate
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) {g x : X}
    (hxM : x ∈ M) (hxg : x ∈ rightConjugate M g)
    (hx : IsInvolution x) : g ∈ M := by
  by_contra hgM
  exact hM.2.2 hgM hxM hxg hx

/-- The centralizer in `X` of an involution in a strongly embedded subgroup
lies in that subgroup. -/
public theorem centralizer_le {X : Type u} [Group X] [Finite X]
    {M : Subgroup X} (hM : IsStronglyEmbedded M) {x : X}
    (hxM : x ∈ M) (hx : IsInvolution x) :
    Subgroup.centralizer ({x} : Set X) ≤ M := by
  intro g hg
  have hcomm : g * x = x * g :=
    Subgroup.mem_centralizer_singleton_iff.mp hg
  have hfix : rightConjugateElem x g = x := by
    dsimp [rightConjugateElem]
    calc
      g⁻¹ * x * g = g⁻¹ * (x * g) := by rw [mul_assoc]
      _ = g⁻¹ * (g * x) := by rw [hcomm]
      _ = x := by simp
  apply hM.mem_of_involution_mem_rightConjugate hxM _ hx
  rw [← hfix]
  exact rightConjugateElem_mem_rightConjugate hxM

/-- A strongly embedded subgroup contains an involution. -/
public theorem exists_involution {X : Type u} [Group X] [Finite X]
    {M : Subgroup X} (hM : IsStronglyEmbedded M) :
    ∃ x : X, x ∈ M ∧ IsInvolution x :=
  hM.2.1

/-- Strong embedding restricts along an injective homomorphism when the
comap remains proper and contains an involution. -/
public theorem comap_of_injective
    {H X : Type*} [Group H] [Group X] [Finite H] [Finite X]
    {M : Subgroup X} (hM : IsStronglyEmbedded M)
    (f : H →* X) (hf : Function.Injective f)
    (hproper : M.comap f ≠ ⊤)
    (hinvolution : ∃ x : H, x ∈ M.comap f ∧ IsInvolution x) :
    IsStronglyEmbedded (M.comap f) := by
  refine ⟨hproper, hinvolution, ?_⟩
  intro g hg x hxM hxright hx
  apply hM.2.2 (g := f g) (x := f x) (by simpa using hg)
      (by simpa using hxM) ?_ (IsInvolution.map_of_injective hx f hf)
  rw [rightConjugate, Subgroup.conjBy, Subgroup.mem_map] at hxright ⊢
  rcases hxright with ⟨y, hyM, hyx⟩
  refine ⟨f y, ?_, ?_⟩
  · simpa using hyM
  · simpa using congrArg f hyx

/-- A strongly embedded subgroup has even cardinality. -/
public theorem card_even {X : Type u} [Group X] [Finite X]
    {M : Subgroup X} (hM : IsStronglyEmbedded M) :
    Even (Nat.card M) := by
  obtain ⟨x, hxM, hx⟩ := hM.exists_involution
  let xm : M := ⟨x, hxM⟩
  have hxm : IsInvolution xm := IsInvolution.subtype hx hxM
  have horder : orderOf xm = 2 :=
    orderOf_eq_prime hxm.sq_eq_one hxm.ne_one
  apply even_iff_two_dvd.mpr
  rw [← horder]
  exact orderOf_dvd_natCard xm

/-- A strongly embedded subgroup contains an ambient Sylow `2`-subgroup. -/
public theorem containsSylowTwo {X : Type u} [Group X] [Finite X]
    {M : Subgroup X} (hM : IsStronglyEmbedded M) :
    ∃ S : Sylow 2 X, (S : Subgroup X) ≤ M := by
  obtain ⟨x, hxM, hx⟩ := hM.exists_involution
  let xm : M := ⟨x, hxM⟩
  have hxm : IsInvolution xm :=
    IsInvolution.subtype hx hxM
  have hxp : IsPGroup 2 (Subgroup.zpowers xm) :=
    isPGroup_zpowers_of_involution hxm
  obtain ⟨P, hzpP⟩ := hxp.exists_le_sylow
  obtain ⟨S, hSM⟩ := P.exists_comap_subtype_eq
  refine ⟨S, ?_⟩
  by_contra hSleM
  let K : Subgroup S := M.comap (S : Subgroup X).subtype
  have hxS : x ∈ (S : Subgroup X) := by
    have hxmP : xm ∈ (P : Subgroup M) :=
      hzpP (Subgroup.mem_zpowers xm)
    rw [← hSM] at hxmP
    exact hxmP
  let xs : S := ⟨x, hxS⟩
  have hxsK : xs ∈ K := by
    change x ∈ M
    exact hxM
  have hKne : K ≠ ⊤ := by
    intro hK
    apply hSleM
    intro y hyS
    let ys : S := ⟨y, hyS⟩
    have hysK : ys ∈ K := by
      rw [hK]
      exact Subgroup.mem_top ys
    change y ∈ M at hysK
    exact hysK
  have hKlt : K < ⊤ := lt_top_iff_ne_top.mpr hKne
  haveI : Group.IsNilpotent S := S.2.isNilpotent
  have hKnormlt : K < Subgroup.normalizer K :=
    normalizerCondition_of_isNilpotent K hKlt
  obtain ⟨q, hqnorm, hqnotK⟩ := SetLike.exists_of_lt hKnormlt
  have hqnotM : (q : X) ∉ M := by
    intro hqM
    apply hqnotK
    change (q : X) ∈ M
    exact hqM
  have hconjK : q * xs * q⁻¹ ∈ K :=
    (Subgroup.mem_normalizer_iff.mp hqnorm xs).mp hxsK
  have hconjM : ((q : X) * x * (q : X)⁻¹) ∈ M := by
    change (q * xs * q⁻¹ : S) ∈ K at hconjK
    exact hconjK
  have hxright : x ∈ rightConjugate M (q : X) := by
    rw [rightConjugate, Subgroup.conjBy, Subgroup.mem_map]
    refine ⟨(q : X) * x * (q : X)⁻¹, hconjM, ?_⟩
    simp [mul_assoc]
  exact hqnotM (hM.mem_of_involution_mem_rightConjugate hxM hxright hx)

/-- In a simple ambient group, the normalizer of a nontrivial subgroup lying
in a proper strongly embedded subgroup is proper. -/
public theorem normalizer_ne_top_of_isSimpleGroup_of_ne_bot_of_le
    {X : Type u} [Group X] [Finite X]
    {M Y : Subgroup X} (hM : IsStronglyEmbedded M)
    (hX : IsSimpleGroup X) (hYne : Y ≠ ⊥) (hYM : Y ≤ M) :
    Subgroup.normalizer (Y : Set X) ≠ ⊤ := by
  intro hNtop
  have hYnormal : Y.Normal := by
    apply Subgroup.normalizer_eq_top_iff.mp
    exact hNtop
  rcases (haveI := hYnormal; IsSimpleGroup.eq_bot_or_eq_top_of_normal Y) with
    hYbot | hYtop
  · exact hYne hYbot
  · apply hM.1
    apply top_unique
    intro x _hx
    have hxY : x ∈ Y := by
      rw [hYtop]
      exact Subgroup.mem_top x
    exact hYM hxY

end IsStronglyEmbedded

/-- The set `I(X)` of involutions of `X`. -/
@[expose] public def involutionsSet (X : Type u) [Group X] : Set X :=
  {x : X | IsInvolution x}

/-- The subgroup generated by all involutions of `X`, denoted
`\langle I(X)\rangle` in Theorem SE. -/
@[expose] public def involutionCore (X : Type u) [Group X] : Subgroup X :=
  Subgroup.closure (involutionsSet X)

/-- Unfolding equation for the subgroup generated by the involutions. -/
public theorem involutionCore_eq_closure (X : Type u) [Group X] :
    involutionCore X = Subgroup.closure (involutionsSet X) :=
  rfl

/-- The odd core `O_{2'}(X)`. -/
@[expose] public def twoPrimeCore (X : Type u) [Group X] : Subgroup X :=
  pPrimeCore 2 X

/-- The odd core is normal. -/
public instance twoPrimeCore_normal {X : Type u} [Group X] :
    (twoPrimeCore X).Normal := by
  unfold twoPrimeCore
  infer_instance

end CFSG.BenderSuzuki
