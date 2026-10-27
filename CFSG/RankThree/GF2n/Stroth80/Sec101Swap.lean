module

public import CFSG.RankThree.GF2n.Stroth80.Conj
public import CFSG.RankThree.GF2n.Tim79Swap
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.GF2n.Stroth80.Basic

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

private theorem Ctx.conj_Z_B_of_swap_Q (hc : Ctx M Q Z B) {g n : G}
    (hg : B = conjSubgroup g Z) (h1 : conjSubgroup n Q = conjSubgroup g Q)
    (h2 : conjSubgroup n (conjSubgroup g Q) = Q) :
    conjSubgroup n Z = B ∧ conjSubgroup n B = Z := by
  have hgn : g⁻¹ * n ∈ M := by
    rw [← hc.hyp.normalizer_Z.2, ← conjSubgroup_eq_self_iff, conjSubgroup_mul, h1,
      ← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
  have hng : n * g ∈ M := by
    rw [← hc.hyp.normalizer_Z.2, ← conjSubgroup_eq_self_iff, conjSubgroup_mul, h2]
  have hZM : ∀ m ∈ M, conjSubgroup m Z = Z := fun m hm => by
    rw [conjSubgroup_eq_self_iff, hc.hyp.normalizer_Z.1]
    exact hm
  refine ⟨?_, ?_⟩
  · have h : conjSubgroup n Z = conjSubgroup g (conjSubgroup (g⁻¹ * n) Z) := by
      rw [← conjSubgroup_mul]
      congr 1
      group
    rw [h, hZM _ hgn, hg]
  · have h : conjSubgroup n B = conjSubgroup (n * g) Z := by
      rw [hg, ← conjSubgroup_mul]
    rw [h, hZM _ hng]

theorem Ctx.exists_swap_mem (hc : Ctx M Q Z B) :
    ∃ n ∈ Q ⊔ QB B, conjSubgroup n Q = QB B ∧ conjSubgroup n (QB B) = Q ∧
      conjSubgroup n Z = B ∧ conjSubgroup n B = Z := by
  obtain ⟨g, hg⟩ := hc.conj
  have hgV : conjSubgroup g Z ≠ Z := by
    rw [← hg]
    exact hc.ne
  have hgQ : conjSubgroup g Z ≤ Q := by
    rw [← hg]
    exact hc.le
  obtain ⟨n, hn, h1, h2⟩ := hc.hyp.toHyp79.exists_swap hgV hgQ
  have hQB : QB B = conjSubgroup g Q := (Ctx.QB_eq hc hg).2
  have hn' : n ∈ Q ⊔ QB B := by
    rwa [hQB]
  have h1' : conjSubgroup n Q = QB B := h1.trans hQB.symm
  have h2' : conjSubgroup n (QB B) = Q := by
    rw [hQB]
    exact h2
  obtain ⟨hZ, hB⟩ := hc.conj_Z_B_of_swap_Q hg h1 h2
  exact ⟨n, hn', h1', h2', hZ, hB⟩

end CFSG.RankThree.GF2n.Stroth80
