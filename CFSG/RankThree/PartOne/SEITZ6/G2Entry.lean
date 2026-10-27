module

public import CFSG.RankThree.PartOne.SEITZ6.G2Span

public section

namespace CFSG.RankThree.PartOne.SEITZ6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.PartOne.SEITZ3

variable {K : Type} [Field K]

@[expose] def kVecs (k : Subfield K) : Submodule k (RootModule .G2 K) where
  carrier := {y | ∀ a, y a ∈ k}
  add_mem' := fun {x y} hx hy a => by
    rw [Finsupp.add_apply]
    exact k.add_mem (hx a) (hy a)
  zero_mem' := fun a => by
    rw [Finsupp.zero_apply]
    exact k.zero_mem
  smul_mem' := fun c x hx a => by
    rw [Finsupp.smul_apply]
    exact k.mul_mem c.2 (hx a)

@[expose] def EntriesIn (k : Subfield K) (g : adjointGroup .G2 K) : Prop :=
  ∀ b a : Label .G2, (g • (Finsupp.single b (1 : K) : RootModule .G2 K)) a ∈ k

@[expose] def LongEntriesIn (k : Subfield K) (g : adjointGroup .G2 K) : Prop :=
  ∀ σ ∈ longPos, ∀ τ ∈ longPos, coordAt (rt τ) (g • rootVec .G2 K (rt σ)) ∈ k

theorem neg_long : ∀ σ ∈ longPos, ∃ σ' ∈ longPos, rt σ' = -rt σ := by decide +kernel

theorem neg_rt10 : -rt 10 = rt 7 := by
  rw [rt10_eq_neg, neg_neg]

section Entry

variable [CharP K 2] (k : Subfield K) (hk : 4 ≤ Nat.card k)
  {R : Subgroup (adjointGroup .G2 K)} (hR : ∀ p < 12, ∀ c ∈ k, xp p c ∈ R)

omit [CharP K 2] in
theorem jForm_mem_of_span {y : RootModule .G2 K}
    (hy : ∀ r ∈ R, ∀ σ ∈ longPos, jForm K (r • rootVec .G2 K (rt σ)) y ∈ k)
    {x : RootModule .G2 K} (hx : x ∈ Submodule.span k (longOrbit R)) : jForm K x y ∈ k := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨r, hr, σ, hσ, rfl⟩ := hx
    exact hy r hr σ hσ
  | zero => simp [k.zero_mem]
  | add x z _ _ hx hz =>
    rw [map_add, LinearMap.add_apply]
    exact k.add_mem hx hz
  | smul a x _ hx =>
    have : a • x = (a : K) • x := rfl
    rw [this, map_smul, LinearMap.smul_apply, smul_eq_mul]
    exact k.mul_mem a.2 hx

include hk hR in
theorem mem_kVecs_of_pairing {y : RootModule .G2 K}
    (hy : ∀ r ∈ R, ∀ σ ∈ longPos, jForm K (r • rootVec .G2 K (rt σ)) y ∈ k) :
    y ∈ kVecs k := by
  intro a
  rcases a with i | ⟨γ, hγ⟩
  · obtain ⟨j, hij⟩ : ∃ j : Fin (Tag.rank .G2), j ≠ i := by
      fin_cases i
      · exact ⟨e1, by decide⟩
      · exact ⟨e0, by decide⟩
    have := jForm_mem_of_span k hy (hVec_mem_span k hk hR j)
    rwa [jForm_hVec_left j i hij] at this
  · have := jForm_mem_of_span k hy (rootVec_mem_span k hk hR (-γ) (isRoot_neg hγ))
    rwa [jForm_rootVec_left, coordAt_eq hγ] at this

theorem jForm_smul_left (r : adjointGroup .G2 K) (x y : RootModule .G2 K) :
    jForm K (r • x) y = jForm K x (r⁻¹ • y) := by
  have := jForm_invariant r x (r⁻¹ • y)
  rwa [smul_inv_smul] at this

include hk hR in
theorem entriesIn_of_long (g : adjointGroup .G2 K)
    (h : ∀ r ∈ R, ∀ r' ∈ R, LongEntriesIn k (r * g * r')) : EntriesIn k g := by
  have key : ∀ x ∈ Submodule.span k (longOrbit R), g • x ∈ kVecs k := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨r', hr', b, hb, rfl⟩ := hx
      refine mem_kVecs_of_pairing k hk hR fun r hr σ hσ => ?_
      rw [jForm_smul_left, ← mul_smul, ← mul_smul]
      obtain ⟨σ', hσ', hσσ'⟩ := neg_long σ hσ
      have hneg : rt σ = -rt σ' := neg_eq_iff_eq_neg.1 hσσ'.symm
      rw [jForm_rootVec_left' hneg]
      exact h r⁻¹ (R.inv_mem hr) r' hr' b hb σ' hσ'
    | zero => simp
    | add x z _ _ hx hz =>
      rw [smul_add]
      exact Submodule.add_mem _ hx hz
    | smul a x _ hx =>
      have : g • (a • x) = a • (g • x) := smul_smul_comm g (a : K) x
      rw [this]
      exact Submodule.smul_mem _ a hx
  intro b a
  exact key _ (single_mem_span k hk hR b) a

omit [CharP K 2] in
include hR in
theorem weylElement_mem :
    weylElement .G2 K e0 ∈ R ∧ weylElement .G2 K e1 ∈ R := by
  refine ⟨?_, ?_⟩
  · rw [weylElement_e0_eq]
    exact R.mul_mem (R.mul_mem (hR 0 (by norm_num) 1 k.one_mem)
      (hR 2 (by norm_num) (-1) (k.neg_mem k.one_mem))) (hR 0 (by norm_num) 1 k.one_mem)
  · rw [weylElement_e1_eq]
    exact R.mul_mem (R.mul_mem (hR 1 (by norm_num) 1 k.one_mem)
      (hR 5 (by norm_num) (-1) (k.neg_mem k.one_mem))) (hR 1 (by norm_num) 1 k.one_mem)

include hR in
theorem reach_long : ∀ σ ∈ longPos, ∃ m ∈ R, m • rootVec .G2 K (rt 7) = rootVec .G2 K (rt σ) := by
  obtain ⟨hw0, hw1⟩ := weylElement_mem k hR
  have s73 := weylElement_smul_rootVec (K := K) e0 (t := 7) (by norm_num) reflect_7
  have s30 := weylElement_smul_rootVec (K := K) e1 (t := 3) (by norm_num) reflect_3
  have s02 := weylElement_smul_rootVec (K := K) e0 (t := 0) (by norm_num) reflect_0
  have s26 := weylElement_smul_rootVec (K := K) e1 (t := 2) (by norm_num) reflect_2
  have s610 := weylElement_smul_rootVec (K := K) e0 (t := 6) (by norm_num) reflect_6
  intro σ hσ
  simp only [longPos, Finset.mem_insert, Finset.mem_singleton] at hσ
  rcases hσ with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨weylElement .G2 K e1 * weylElement .G2 K e0, R.mul_mem hw1 hw0, by
      rw [mul_smul, s73, s30]⟩
  · exact ⟨weylElement .G2 K e0 * weylElement .G2 K e1 * weylElement .G2 K e0,
      R.mul_mem (R.mul_mem hw0 hw1) hw0, by rw [mul_smul, mul_smul, s73, s30, s02]⟩
  · exact ⟨weylElement .G2 K e0, hw0, s73⟩
  · exact ⟨weylElement .G2 K e1 * weylElement .G2 K e0 * weylElement .G2 K e1 *
        weylElement .G2 K e0, R.mul_mem (R.mul_mem (R.mul_mem hw1 hw0) hw1) hw0, by
      rw [mul_smul, mul_smul, mul_smul, s73, s30, s02, s26]⟩
  · exact ⟨1, R.one_mem, by rw [one_smul]⟩
  · exact ⟨weylElement .G2 K e0 * weylElement .G2 K e1 * weylElement .G2 K e0 *
        weylElement .G2 K e1 * weylElement .G2 K e0,
      R.mul_mem (R.mul_mem (R.mul_mem (R.mul_mem hw0 hw1) hw0) hw1) hw0, by
      rw [mul_smul, mul_smul, mul_smul, mul_smul, s73, s30, s02, s26, s610]⟩

include hk hR in
theorem exists_bad_entry (g : adjointGroup .G2 K) (hg : ¬ EntriesIn k g) :
    ∃ r ∈ R, ∃ r' ∈ R, coordAt (rt 10) ((r * g * r') • rootVec .G2 K (rt 7)) ∉ k := by
  by_contra hcon
  push Not at hcon
  refine hg (entriesIn_of_long k hk hR g fun r hr r' hr' σ hσ τ hτ => ?_)
  obtain ⟨mσ, hmσ, hσ7⟩ := reach_long k hR σ hσ
  obtain ⟨τ', hτ', hττ'⟩ := neg_long τ hτ
  obtain ⟨mτ, hmτ, hτ7⟩ := reach_long k hR τ' hτ'
  have h1 := hcon (mτ⁻¹ * r) (R.mul_mem (R.inv_mem hmτ) hr) (r' * mσ) (R.mul_mem hr' hmσ)
  have hw : (r * g * r') • rootVec .G2 K (rt σ) =
      (r * g * r' * mσ) • rootVec .G2 K (rt 7) := by
    rw [mul_smul (r * g * r') mσ, hσ7]
  have s1 : coordAt (rt τ) ((r * g * r') • rootVec .G2 K (rt σ)) =
      jForm K (rootVec .G2 K (rt τ')) ((r * g * r') • rootVec .G2 K (rt σ)) := by
    exact (jForm_rootVec_left' hττ' _).symm
  have s2 : jForm K (rootVec .G2 K (rt τ')) ((r * g * r') • rootVec .G2 K (rt σ)) =
      jForm K (rootVec .G2 K (rt 7)) (mτ⁻¹ • ((r * g * r') • rootVec .G2 K (rt σ))) := by
    rw [← hτ7, jForm_smul_left]
  have s3 : ∀ z : RootModule .G2 K, jForm K (rootVec .G2 K (rt 7)) z = coordAt (rt 10) z := by
    intro z
    exact jForm_rootVec_left' neg_rt10.symm z
  have e : mτ⁻¹ * (r * g * r' * mσ) = mτ⁻¹ * r * g * (r' * mσ) := by group
  have h2 : coordAt (rt τ) ((r * g * r') • rootVec .G2 K (rt σ)) =
      coordAt (rt 10) ((mτ⁻¹ * r * g * (r' * mσ)) • rootVec .G2 K (rt 7)) := by
    rw [s1, s2, s3, hw, ← mul_smul, e]
  rw [h2]
  exact h1

end Entry

end CFSG.RankThree.PartOne.SEITZ6
