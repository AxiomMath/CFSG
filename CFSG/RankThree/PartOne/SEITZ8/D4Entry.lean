module

public import CFSG.RankThree.PartOne.SEITZ8.D4Span

public section

namespace CFSG.RankThree.PartOne.SEITZ8

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4

variable {K : Type} [Field K]

@[expose] def RatMod (k : Subfield K) (y : RootModule d4 K) : Prop :=
  (∀ γ : Fin d4.rank → ℤ, coordAt γ y ∈ k) ∧ y (Sum.inl (nd 2)) ∈ k ∧
    y (Sum.inl (nd 0)) + y (Sum.inl (nd 1)) + y (Sum.inl (nd 3)) ∈ k

@[expose] def LongEntriesIn (k : Subfield K) (g : adjointGroup d4 K) : Prop :=
  ∀ σ ∈ longPos, ∀ τ ∈ longPos, coordAt (d4Root τ) (g • (rv σ : RootModule d4 K)) ∈ k

section Entry

variable [CharP K 2] {σ : K →+* K} {k : Subfield K}
  {R : Subgroup (adjointGroup d4 K)}

omit [CharP K 2] in
theorem jForm_mem_of_span {y : RootModule d4 K}
    (hy : ∀ r ∈ R, ∀ p ∈ longPos, jForm K (r • (rv p : RootModule d4 K)) y ∈ k)
    {x : RootModule d4 K} (hx : x ∈ Submodule.span k (longOrbit R)) : jForm K x y ∈ k := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨r, hr, p, hp, rfl⟩ := hx
    exact hy r hr p hp
  | zero => simp [k.zero_mem]
  | add x z _ _ hx hz =>
    rw [map_add, LinearMap.add_apply]
    exact k.add_mem hx hz
  | smul a x _ hx =>
    have : a • x = (a : K) • x := rfl
    rw [this, map_smul, LinearMap.smul_apply, smul_eq_mul]
    exact k.mul_mem a.2 hx

theorem ratMod_of_pairing (h : SpanHyp σ k R) {y : RootModule d4 K}
    (hy : ∀ r ∈ R, ∀ p ∈ longPos, jForm K (r • (rv p : RootModule d4 K)) y ∈ k) :
    RatMod k y := by
  refine ⟨fun γ => ?_, ?_, ?_⟩
  · by_cases hγ : IsRoot d4 γ
    · obtain ⟨q, hq, hqγ⟩ := exists_pos_of_isRoot (isRoot_neg_d4 hγ)
      have hmem := rv_mem_span h hq
      have := jForm_mem_of_span hy hmem
      have e : (rv q : RootModule d4 K) = rootVec d4 K (-γ) := by rw [rv, hqγ]
      rwa [e, jForm_rootVec_left] at this
    · have : coordAt γ y = 0 := by
        unfold coordAt
        simp [hγ]
      rw [this]
      exact k.zero_mem
  · have h1 := jForm_mem_of_span hy (t2_mem_span h)
    rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply,
      jForm_hVec_outer (i := nd 0) (by decide), jForm_hVec_outer (i := nd 1) (by decide),
      jForm_hVec_outer (i := nd 3) (by decide)] at h1
    have e : y (Sum.inl (nd 2)) + y (Sum.inl (nd 2)) + y (Sum.inl (nd 2)) = y (Sum.inl (nd 2)) := by
      have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
      linear_combination (y (Sum.inl (nd 2))) * h2
    rwa [e] at h1
  · have h1 := jForm_mem_of_span hy (h2_mem_span h)
    rwa [jForm_hVec_central] at h1

@[expose] def ratModSub (k : Subfield K) : Submodule k (RootModule d4 K) where
  carrier := {y | RatMod k y}
  add_mem' := fun {x y} hx hy =>
    ⟨fun γ => by rw [coordAt_add]; exact k.add_mem (hx.1 γ) (hy.1 γ),
      by rw [Finsupp.add_apply]; exact k.add_mem hx.2.1 hy.2.1,
      by
        have h1 := k.add_mem hx.2.2 hy.2.2
        simp only [Finsupp.add_apply]
        convert h1 using 1
        ring⟩
  zero_mem' := ⟨fun γ => by simp [coordAt, k.zero_mem], by simp [k.zero_mem], by simp [k.zero_mem]⟩
  smul_mem' := fun a x hx =>
    ⟨fun γ => by
        have : a • x = (a : K) • x := rfl
        rw [this, coordAt_smul]
        exact k.mul_mem a.2 (hx.1 γ),
      by
        have : a • x = (a : K) • x := rfl
        rw [this, Finsupp.smul_apply, smul_eq_mul]
        exact k.mul_mem a.2 hx.2.1,
      by
        have : a • x = (a : K) • x := rfl
        simp only [this, Finsupp.smul_apply, smul_eq_mul]
        have h1 := k.mul_mem a.2 hx.2.2
        convert h1 using 1
        ring⟩

theorem ratMod_of_long (h : SpanHyp σ k R) (g : adjointGroup d4 K)
    (hg : ∀ r ∈ R, ∀ r' ∈ R, LongEntriesIn k (r * g * r')) :
    ∀ x ∈ Submodule.span k (longOrbit R), RatMod k (g • x) := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨r', hr', b, hb, rfl⟩ := hx
    refine ratMod_of_pairing h fun r hr p hp => ?_
    rw [jForm_smul_left, ← mul_smul, ← mul_smul]
    obtain ⟨p', hp', hpp'⟩ := neg_long p hp
    have hneg : d4Root p = -d4Root p' := neg_eq_iff_eq_neg.1 hpp'.symm
    rw [rv, jForm_rootVec_left' hneg]
    exact hg r⁻¹ (R.inv_mem hr) r' hr' b hb p' hp'
  | zero =>
    rw [smul_zero]
    exact (ratModSub k).zero_mem
  | add x z _ _ hx hz =>
    rw [smul_add]
    exact (ratModSub k).add_mem hx hz
  | smul a x _ hx =>
    have : g • (a • x) = a • (g • x) := smul_smul_comm' g (a : K) x
    rw [this]
    exact (ratModSub k).smul_mem a hx

omit [CharP K 2] in
theorem weylElement_smul_rv (i : Fin d4.rank) {p p' : ℕ} (hp : p < 24)
    (h : reflect d4 i (d4Root p) = d4Root p') (hK : (2 : K) = 0) :
    (weylElement d4 K i : adjointGroup d4 K) • (rv p : RootModule d4 K) = rv p' := by
  have hα : IsRoot d4 (d4Root p) := isRoot_d4 hp
  have hw := weylElt_rootVec (R := K) i (1 : Kˣ) hα
  have hm1 : (-1 : K) = 1 := by
    have : (1 : K) + 1 = 0 := by rw [one_add_one_eq_two, hK]
    exact neg_eq_of_add_eq_zero_right this
  show (weylElt d4 K i 1 : Module.End K (RootModule d4 K)) (rootVec d4 K (d4Root p)) = _
  rw [hw, h, hm1]
  simp

omit [CharP K 2] in
theorem reflect_facts :
    reflect d4 (nd 2) (d4Root 22) = d4Root 19 ∧ reflect d4 (nd 2) (d4Root 2) = d4Root 8 ∧
    reflect d4 (nd 2) (d4Root 21) = d4Root 23 ∧
    reflect d4 (nd 3) (d4Root 19) = d4Root 12 ∧ reflect d4 (nd 1) (d4Root 12) = d4Root 5 ∧
    reflect d4 (nd 0) (d4Root 5) = d4Root 2 ∧
    reflect d4 (nd 3) (d4Root 8) = d4Root 16 ∧ reflect d4 (nd 1) (d4Root 16) = d4Root 20 ∧
    reflect d4 (nd 0) (d4Root 20) = d4Root 21 := by
  decide +kernel

omit [CharP K 2] in
theorem n1_smul_19 (hK : (2 : K) = 0) :
    (weylElement d4 K (nd 0) * weylElement d4 K (nd 1) * weylElement d4 K (nd 3) :
        adjointGroup d4 K) • (rv 19 : RootModule d4 K) = rv 2 := by
  obtain ⟨-, -, -, a1, a2, a3, -, -, -⟩ := reflect_facts
  rw [mul_smul, mul_smul, weylElement_smul_rv (nd 3) (by decide) a1 hK,
    weylElement_smul_rv (nd 1) (by decide) a2 hK, weylElement_smul_rv (nd 0) (by decide) a3 hK]

omit [CharP K 2] in
theorem n1_smul_8 (hK : (2 : K) = 0) :
    (weylElement d4 K (nd 0) * weylElement d4 K (nd 1) * weylElement d4 K (nd 3) :
        adjointGroup d4 K) • (rv 8 : RootModule d4 K) = rv 21 := by
  obtain ⟨-, -, -, -, -, -, b1, b2, b3⟩ := reflect_facts
  rw [mul_smul, mul_smul, weylElement_smul_rv (nd 3) (by decide) b1 hK,
    weylElement_smul_rv (nd 1) (by decide) b2 hK, weylElement_smul_rv (nd 0) (by decide) b3 hK]

theorem reach_long (h : SpanHyp σ k R) :
    ∀ p ∈ longPos, ∃ m ∈ R, m • (rv 22 : RootModule d4 K) = rv p := by
  have hK : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨c1, c2, c3, -, -, -, -, -, -⟩ := reflect_facts
  have s0 := weylElement_smul_rv (K := K) (nd 2) (p := 22) (by decide) c1 hK
  have s1 := weylElement_smul_rv (K := K) (nd 2) (p := 2) (by decide) c2 hK
  have s2 := weylElement_smul_rv (K := K) (nd 2) (p := 21) (by decide) c3 hK
  have s3 := n1_smul_19 (K := K) hK
  have s4 := n1_smul_8 (K := K) hK
  set a := weylElement d4 K (nd 2) with ha
  set b := weylElement d4 K (nd 0) * weylElement d4 K (nd 1) * weylElement d4 K (nd 3) with hb
  intro p hp
  simp only [longPos, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨b * a, R.mul_mem h.n1 h.n0, by rw [mul_smul, s0, s3]⟩
  · exact ⟨a * b * a, R.mul_mem (R.mul_mem h.n0 h.n1) h.n0, by rw [mul_smul, mul_smul, s0, s3, s1]⟩
  · exact ⟨a, h.n0, s0⟩
  · exact ⟨b * a * b * a, R.mul_mem (R.mul_mem (R.mul_mem h.n1 h.n0) h.n1) h.n0,
      by rw [mul_smul, mul_smul, mul_smul, s0, s3, s1, s4]⟩
  · exact ⟨1, R.one_mem, by rw [one_smul]⟩
  · exact ⟨a * b * a * b * a,
      R.mul_mem (R.mul_mem (R.mul_mem (R.mul_mem h.n0 h.n1) h.n0) h.n1) h.n0,
      by rw [mul_smul, mul_smul, mul_smul, mul_smul, s0, s3, s1, s4, s2]⟩

theorem longEntries_of_hcon (h : SpanHyp σ k R) (g : adjointGroup d4 K)
    (hcon : ∀ r ∈ R, ∀ r' ∈ R,
      coordAt (d4Root 23) ((r * g * r') • (rv 22 : RootModule d4 K)) ∈ k) :
    ∀ r ∈ R, ∀ r' ∈ R, LongEntriesIn k (r * g * r') := by
  intro r hr r' hr' σ hσ τ hτ
  obtain ⟨mσ, hmσ, hσ7⟩ := reach_long h σ hσ
  obtain ⟨τ', hτ', hττ'⟩ := neg_long τ hτ
  obtain ⟨mτ, hmτ, hτ7⟩ := reach_long h τ' hτ'
  have h1 := hcon (mτ⁻¹ * r) (R.mul_mem (R.inv_mem hmτ) hr) (r' * mσ) (R.mul_mem hr' hmσ)
  have hneg : d4Root τ' = -d4Root τ := hττ'
  have hw : (r * g * r') • (rv σ : RootModule d4 K) =
      (r * g * r' * mσ) • (rv 22 : RootModule d4 K) := by
    rw [mul_smul (r * g * r') mσ, hσ7]
  have s1 : coordAt (d4Root τ) ((r * g * r') • (rv σ : RootModule d4 K)) =
      jForm K (rv τ' : RootModule d4 K) ((r * g * r') • (rv σ : RootModule d4 K)) :=
    (jForm_rootVec_left' hneg _).symm
  have s2 : jForm K (rv τ' : RootModule d4 K) ((r * g * r') • (rv σ : RootModule d4 K)) =
      jForm K (rv 22 : RootModule d4 K) (mτ⁻¹ • ((r * g * r') • (rv σ : RootModule d4 K))) := by
    rw [← hτ7, jForm_smul_left]
  have s3 : ∀ z : RootModule d4 K, jForm K (rv 22 : RootModule d4 K) z =
      coordAt (d4Root 23) z := by
    intro z
    exact jForm_rootVec_left' (by rw [d4Root_23, neg_neg]) z
  have e : mτ⁻¹ * (r * g * r' * mσ) = mτ⁻¹ * r * g * (r' * mσ) := by group
  have h2 : coordAt (d4Root τ) ((r * g * r') • (rv σ : RootModule d4 K)) =
      coordAt (d4Root 23) ((mτ⁻¹ * r * g * (r' * mσ)) • (rv 22 : RootModule d4 K)) := by
    rw [s1, s2, s3, hw, ← mul_smul, e]
  rw [h2]
  exact h1

theorem ratMod_of_hcon (h : SpanHyp σ k R) (g : adjointGroup d4 K)
    (hcon : ∀ r ∈ R, ∀ r' ∈ R,
      coordAt (d4Root 23) ((r * g * r') • (rv 22 : RootModule d4 K)) ∈ k) :
    ∀ x ∈ Submodule.span k (longOrbit R), RatMod k (g • x) :=
  ratMod_of_long h g (longEntries_of_hcon h g hcon)

end Entry

end CFSG.RankThree.PartOne.SEITZ8
