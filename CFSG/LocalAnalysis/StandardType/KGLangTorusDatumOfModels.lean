module

public import CFSG.LocalAnalysis.StandardType.KGLangTorusDatum
public import CFSG.LocalAnalysis.StandardType.GGLFourFourThreeMarking

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.RankThree.PerfectCover

theorem kgLangTorusDatumCont_of_models {p : ℕ} (hp : p.Prime) {R : Type} [Group R]
    {I F : Set (MulAut R)}
    (hcyc : ∃ J S : Subgroup (MulAut R), (J : Set (MulAut R)) = I ∧ J ≤ S ∧
      (J.subgroupOf S).Normal ∧ (∃ g ∈ S, ∀ s ∈ S, ∃ k : ℤ, g ^ k * s ∈ J) ∧
      ∀ α ∈ Subgroup.closure (I ∪ F), (∃ k : ℕ, α ^ p ^ k = 1) → α ∈ S)
    (hM : ∀ [Finite (HopfCover R)] (θ : HopfCover R ⧸ Subgroup.center (HopfCover R) ≃* R),
      commutator (HopfCover R) = ⊤ →
      ∀ A : Subgroup (MulAut (HopfCover R)), IsElemAbelian p A →
        (∀ α ∈ A, ∃ u ∈ I, ∃ f ∈ Subgroup.closure F, kgInducedAut θ α = u * f) →
        (∃ α ∈ A, α ≠ 1 ∧ kgInducedAut θ α ∈ I) →
        ∀ α₀ ∈ A, kgInducedAut θ α₀ ∉ I →
          ∃ M : Subgroup (HopfCover R), (∀ a ∈ M, ∀ c ∈ M, a * c = c * a) ∧
            (∀ t, α₀ t ∈ M ↔ t ∈ M) ∧
            (∀ α ∈ A, kgInducedAut θ α ∈ I → ∀ t ∈ M, α t = t) ∧
            (∀ c ∈ M, ((List.range p).map fun i => (α₀ ^ i) c).prod = 1 →
              ∃ s ∈ M, c = s⁻¹ * α₀ s) ∧
            ∃ e ∈ M, e ≠ 1 ∧ e ^ p = 1 ∧ α₀ e = e) :
    KGLangTorusDatumCont p R I F := by
  intro hfin θ hcomm A hA hAI hA0 α₀ hα₀ hα₀I
  haveI := hfin
  obtain ⟨J, S, hJI, hJS, hN, hcycS, hpS⟩ := hcyc
  have hα₀J : kgInducedAut θ α₀ ∉ J := by
    intro h
    exact hα₀I (hJI ▸ h)
  have hAS : ∀ α ∈ A, kgInducedAut θ α ∈ S := by
    intro α hα
    obtain ⟨u, huI, f, hfF, huf⟩ := hAI α hα
    apply hpS (kgInducedAut θ α)
    · rw [huf]
      exact Subgroup.mul_mem _
        (Subgroup.subset_closure (Set.mem_union_left F huI))
        (Subgroup.closure_mono (fun _ hx => Set.mem_union_right I hx) hfF)
    · exact ⟨1, by rw [pow_one, ← map_pow, hA.2 α hα, map_one]⟩
  refine ⟨?_, hM θ hcomm A hA hAI hA0 α₀ hα₀ hα₀I⟩
  intro α hα
  obtain ⟨k, hk⟩ := kgLangLT1_decomp hp θ hJS hN hcycS hA hAS hα₀ hα₀J α hα
  exact ⟨k, hJI ▸ hk⟩

theorem kgLangFieldConj_root {p : ℕ} {R : Type} [Group R] {I F : Set (MulAut R)}
    (hconj : GGRawFieldConj p R I F) (hs : IsSimpleGroup R) (hna : ∃ a b : R, a * b ≠ b * a)
    {u f : MulAut R} (hu : u ∈ I) (hf : f ∈ Subgroup.closure F) (hxI : u * f ∉ I)
    (hxp : (u * f) ^ p = 1) :
    ∃ u' ∈ I, ∃ f' ∈ F, orderOf f' = p ∧ u * f = u' * f' * u'⁻¹ := by
  obtain ⟨f', hf'F, u', hu'I, hord, heq⟩ := hconj hs hna u hu f hf hxI hxp
  exact ⟨u', hu'I, f', hf'F, hord, heq⟩

end CFSG.StandardType
