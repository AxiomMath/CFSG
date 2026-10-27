module

public import CFSG.LocalAnalysis.StandardType.GGTBJOmBlockGTwo
public import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs

public section

namespace CFSG.StandardType

theorem exists_two_representative_mem_ggRankOneIn
    {G : Type} [Group G] [Finite G] {Bs X : Subgroup G} {r : MulAut Bs}
    (hr : r ∈ ggAutomizer X Bs) (hr2 : r ^ 2 = 1) :
    ∃ n : G, n ∈ ggRankOneIn X Bs r ∧ n ∈ Subgroup.normalizer (Bs : Set G) ∧
      (∃ k : ℕ, n ^ (2 ^ k) = 1) ∧
      ∀ b : Bs, ((r b : Bs) : G) = n * b * n⁻¹ := by
  obtain ⟨g, hgX, hgN, hact⟩ := mem_ggAutomizer_iff.mp hr
  have hrself : ∀ b : Bs, r (r b) = b := by
    intro b
    have h := congrArg (fun t : MulAut Bs => t b) hr2
    simpa only [pow_two, MulAut.mul_apply, MulAut.one_apply] using h
  have hgC : g ∈ Subgroup.centralizer (ggHyperplane Bs r : Set G) := by
    apply Subgroup.mem_centralizer_iff.mpr
    rintro _ ⟨b, hb, rfl⟩
    have hfix : r b = b := hb
    have h : g * (b : G) * g⁻¹ = (b : G) := by
      rw [← hact b, hfix]
    exact ((mul_inv_eq_iff_eq_mul).mp h).symm
  obtain ⟨m, hm, k, hk⟩ := OrthTorus.exists_odd_pow_pow_two_eq_one g
  have hnS : g ^ m ∈ ggRankOneIn X Bs r := by
    change g ^ m ∈ Subgroup.closure
      {n : G | n ∈ X ⊓ Subgroup.centralizer (ggHyperplane Bs r : Set G) ∧
        ∃ k : ℕ, n ^ (2 ^ k) = 1}
    exact Subgroup.subset_closure
      ⟨⟨X.pow_mem hgX m, (Subgroup.centralizer _).pow_mem hgC m⟩, k, hk⟩
  refine ⟨g ^ m, hnS,
    (Subgroup.normalizer _).pow_mem hgN m, ⟨k, hk⟩, fun b => ?_⟩
  exact (OrthTorus.pow_odd_conj_eq Bs.subtype
    (fun b => (hact b).symm) hrself hm b).symm

end CFSG.StandardType
