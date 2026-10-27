module

public import CFSG.RankThree.PartOne.SEITZ6.G2Entry
public import CFSG.RankThree.PartOne.SEITZ2.G2F2Span

public section

namespace CFSG.RankThree.PartOne.SEITZ2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.PartOne.SEITZ3 CFSG.RankThree.PartOne.SEITZ6

variable {K : Type} [Field K] [CharP K 2] (k : Subfield K)
  {R : Subgroup (adjointGroup .G2 K)} (hR : ∀ p < 12, ∀ c ∈ k, xp p c ∈ R)

include hR in
theorem mem_kVecs_of_pairing_f2 {y : RootModule .G2 K}
    (hy : ∀ r ∈ R, ∀ σ ∈ longPos, jForm K (r • rootVec .G2 K (rt σ)) y ∈ k) :
    y ∈ kVecs k := by
  have hR1 : ∀ p < 12, xp p (1 : K) ∈ R := fun p hp => hR p hp 1 k.one_mem
  intro a
  rcases a with i | ⟨γ, hγ⟩
  · obtain ⟨j, hij⟩ : ∃ j : Fin (Tag.rank .G2), j ≠ i := by
      fin_cases i
      · exact ⟨e1, by decide⟩
      · exact ⟨e0, by decide⟩
    have := jForm_mem_of_span k hy (show hVec .G2 K j ∈ Submodule.span k (longOrbit R) from
      single_mem_span_f2 k hR1 (Sum.inl j))
    rwa [jForm_hVec_left j i hij] at this
  · have := jForm_mem_of_span k hy (show rootVec .G2 K (-γ) ∈ Submodule.span k (longOrbit R) by
      rw [rootVec_eq_single K (isRoot_neg hγ)]
      exact single_mem_span_f2 k hR1 _)
    rwa [jForm_rootVec_left, coordAt_eq hγ] at this

include hR in
theorem entriesIn_of_long_f2 (g : adjointGroup .G2 K)
    (h : ∀ r ∈ R, ∀ r' ∈ R, LongEntriesIn k (r * g * r')) : EntriesIn k g := by
  have hR1 : ∀ p < 12, xp p (1 : K) ∈ R := fun p hp => hR p hp 1 k.one_mem
  have key : ∀ x ∈ Submodule.span k (longOrbit R), g • x ∈ kVecs k := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨r', hr', b, hb, rfl⟩ := hx
      refine mem_kVecs_of_pairing_f2 k hR fun r hr σ hσ => ?_
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
  exact key _ (single_mem_span_f2 k hR1 b) a

include hR in
theorem exists_bad_entry_f2 (g : adjointGroup .G2 K) (hg : ¬ EntriesIn k g) :
    ∃ r ∈ R, ∃ r' ∈ R, coordAt (rt 10) ((r * g * r') • rootVec .G2 K (rt 7)) ∉ k := by
  by_contra hcon
  push Not at hcon
  refine hg (entriesIn_of_long_f2 k hR g fun r hr r' hr' σ hσ τ hτ => ?_)
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

end CFSG.RankThree.PartOne.SEITZ2
