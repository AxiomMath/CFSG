module

public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.C2Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace S152V

variable {G : Type} [Group G]

theorem inv_mul_mem_normalizer_of_conjByElt_eq {a b : G} {L : Subgroup G}
    (h : conjByElt a L = conjByElt b L) : b⁻¹ * a ∈ Subgroup.normalizer (L : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  have h1 := SetLike.ext_iff.1 h (a * g * a⁻¹)
  rw [mem_conjByElt, mem_conjByElt] at h1
  have e1 : a⁻¹ * (a * g * a⁻¹) * a = g := by group
  have e2 : b⁻¹ * (a * g * a⁻¹) * b = b⁻¹ * a * g * (b⁻¹ * a)⁻¹ := by group
  rw [e1, e2] at h1
  exact h1

theorem conjByElt_one_eq (L : Subgroup G) : conjByElt (1 : G) L = L := by
  ext x
  rw [mem_conjByElt]
  simp

theorem exists_two_cosets {I S L : Subgroup G} (hSI : S ≤ I)
    (horb : conjSubgroupsBy I L = conjSubgroupsBy S L)
    (h2 : (∀ t ∈ S, t ∈ Subgroup.normalizer (L : Set G)) ∨
      ∃ t ∈ S, conjSubgroupsBy S L = {L, conjByElt t L}) :
    ∃ t ∈ I, ∀ a ∈ I, a ∈ Subgroup.normalizer (L : Set G) ∨
      t⁻¹ * a ∈ Subgroup.normalizer (L : Set G) := by
  rcases h2 with h | ⟨t, ht, hO⟩
  · refine ⟨1, one_mem _, fun a ha => Or.inl ?_⟩
    have hmem : conjByElt a L ∈ conjSubgroupsBy I L := ⟨a, ha, rfl⟩
    rw [horb] at hmem
    obtain ⟨s, hs, hseq⟩ := hmem
    have h1 := inv_mul_mem_normalizer_of_conjByElt_eq (a := a) (b := s) hseq
    have h3 : a = s * (s⁻¹ * a) := by group
    rw [h3]
    exact Subgroup.mul_mem _ (h s hs) h1
  · refine ⟨t, hSI ht, fun a ha => ?_⟩
    have hmem : conjByElt a L ∈ conjSubgroupsBy I L := ⟨a, ha, rfl⟩
    rw [horb, hO] at hmem
    rcases hmem with h1 | h1
    · left
      have := inv_mul_mem_normalizer_of_conjByElt_eq (a := a) (b := 1) (h1.trans (conjByElt_one_eq L).symm)
      simpa using this
    · exact Or.inr (inv_mul_mem_normalizer_of_conjByElt_eq h1)

theorem mul_self_mem_of_two_cosets {I N : Subgroup G} {t : G} (ht : t ∈ I)
    (h : ∀ a ∈ I, a ∈ N ∨ t⁻¹ * a ∈ N) {x : G} (hx : x ∈ I) : x * x ∈ N := by
  rcases h x hx with h1 | h1
  · exact N.mul_mem h1 h1
  · rcases h (x * t) (I.mul_mem hx ht) with h2 | h2
    · have e : x * x = (x * t) * (t⁻¹ * x) := by group
      rw [e]
      exact N.mul_mem h2 h1
    · have ht' : t ∈ N := by
        have e : t = (t⁻¹ * x)⁻¹ * (t⁻¹ * (x * t)) := by group
        rw [e]
        exact N.mul_mem (N.inv_mem h1) h2
      have hx' : x ∈ N := by
        have e : x = t * (t⁻¹ * x) := by group
        rw [e]
        exact N.mul_mem ht' h1
      exact N.mul_mem hx' hx'

theorem mem_of_mul_self_mem_of_odd {N : Subgroup G} {x : G} (hsq : x * x ∈ N) (hodd : Odd (orderOf x)) :
    x ∈ N := by
  obtain ⟨m, hm⟩ := hodd
  have h1 : x ^ (2 * m + 1) = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hm] at this
  have h2 : x = (x * x) ^ (m + 1) := by
    calc x = x ^ (2 * m + 1) * x := by rw [h1, one_mul]
      _ = x ^ (2 * (m + 1)) := by rw [← pow_succ]; congr 1
      _ = (x * x) ^ (m + 1) := by rw [pow_mul, pow_two]
  rw [h2]
  exact N.pow_mem hsq _

theorem oTwoUpper_le_of_two_cosets {I N K : Subgroup G} (hKI : K ≤ I) (hK : K = oTwoUpper K) {t : G}
    (ht : t ∈ I) (h : ∀ a ∈ I, a ∈ N ∨ t⁻¹ * a ∈ N) : K ≤ N := by
  refine hK.le.trans ((Subgroup.closure_le N).mpr fun x hx => ?_)
  exact mem_of_mul_self_mem_of_odd (mul_self_mem_of_two_cosets ht h (hKI hx.1)) hx.2

end S152V

end CFSG.Quasithin
