module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear
public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowTools

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

theorem commute_notMem_of_conj {S : Type} [Group S] {a b a' : S} (k : S)
    (hc : a * b = b * a) (hn : b ∉ Subgroup.zpowers a)
    (ha' : k * a * k⁻¹ = a' ∨ k * a * k⁻¹ = a'⁻¹) :
    (k * b * k⁻¹) * a' = a' * (k * b * k⁻¹) ∧ k * b * k⁻¹ ∉ Subgroup.zpowers a' := by
  have hmem : ∀ t : S, k * t * k⁻¹ ∈ Subgroup.zpowers (k * a * k⁻¹) → t ∈ Subgroup.zpowers a := by
    intro t ht
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp ht
    refine Subgroup.mem_zpowers_iff.mpr ⟨i, ?_⟩
    have h1 : (k * a * k⁻¹) ^ i = k * a ^ i * k⁻¹ := by simp [conj_zpow]
    rw [h1] at hi
    have := congrArg (fun u => k⁻¹ * u * k) hi
    simpa [mul_assoc] using this
  have hcomm : (k * b * k⁻¹) * (k * a * k⁻¹) = (k * a * k⁻¹) * (k * b * k⁻¹) := by
    calc k * b * k⁻¹ * (k * a * k⁻¹) = k * (b * a) * k⁻¹ := by group
      _ = k * (a * b) * k⁻¹ := by rw [hc]
      _ = k * a * k⁻¹ * (k * b * k⁻¹) := by group
  have hz : Subgroup.zpowers a' = Subgroup.zpowers (k * a * k⁻¹) := by
    rcases ha' with h | h
    · rw [h]
    · rw [h, Subgroup.zpowers_inv]
  have hcomm' : (k * b * k⁻¹) * a' = a' * (k * b * k⁻¹) := by
    rcases ha' with h | h
    · rw [← h]
      exact hcomm
    · have : a' = (k * a * k⁻¹)⁻¹ := by rw [h, inv_inv]
      rw [this]
      exact Commute.inv_right (show Commute (k * b * k⁻¹) (k * a * k⁻¹) from hcomm)
  exact ⟨hcomm', by rw [hz]; exact fun hm => hn (hmem b hm)⟩

theorem listRow_of_invariant {S ι : Type} [Group S] [Finite S] (inv : S → ι)
    (hinv : ∀ k x : S, inv (k * x * k⁻¹) = inv x)
    (hsep : ∀ x y : S, orderOf x = 3 → orderOf y = 3 → inv x = inv y →
      ∃ k : S, k * x * k⁻¹ = y ∨ k * x * k⁻¹ = y⁻¹)
    (hpair : ∀ z : S, orderOf z = 3 → ∃ a b : S, orderOf a = 3 ∧ b ^ 3 = 1 ∧ inv a = inv z ∧
      inv b = inv z ∧ a * b = b * a ∧ b ∉ Subgroup.zpowers a) : ListRow S := by
  refine listRow_of_forall_not_weaklyClosed fun z hz => ?_
  obtain ⟨a, b, ha, hb3, hia, hib, hc, hn⟩ := hpair z hz
  obtain ⟨k, hk⟩ := hsep a z ha hz hia
  obtain ⟨hc', hn'⟩ := commute_notMem_of_conj k hc hn hk
  have hb1 : b ≠ 1 := fun h => hn (h ▸ one_mem _)
  have hbo : orderOf b = 3 := orderOf_eq_prime hb3 hb1
  have hb'o : orderOf (k * b * k⁻¹) = 3 := by
    have := orderOf_injective (MulAut.conj k).toMonoidHom (MulAut.conj k).injective b
    rw [hbo] at this
    simpa using this
  have hib' : inv (k * b * k⁻¹) = inv z := by rw [hinv, hib]
  obtain ⟨g, hg⟩ := hsep z (k * b * k⁻¹) hz hb'o hib'.symm
  rcases hg with hg | hg
  · exact not_weaklyClosed_of_commute_conj (g := g) (by rw [hg]; exact hc') (by rw [hg]; exact hn')
  · refine not_weaklyClosed_of_commute_conj (g := g) ?_ ?_
    · rw [hg]
      exact Commute.inv_left (show Commute (k * b * k⁻¹) z from hc')
    · rw [hg]
      intro hm
      exact hn' (by simpa using inv_mem hm)

end CFSG.RankThree.PartTwo.Sec4.RonanK432
