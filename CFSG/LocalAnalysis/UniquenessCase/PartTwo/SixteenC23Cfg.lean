module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen5
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23Loc
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23Perm
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem c23_uniqueMax_of_thm145 (D : Data G) (h145 : Thm145 D) {K₁ K₂ X : Subgroup G} {z : G}
    (hH : Hyp141 D K₁ K₂ X) (hzT : ∀ t ∈ D.T, t * z = z * t) (hzX : ∀ x ∈ X, x * z = z * x)
    (hzN : ∀ n ∈ (K₁ ⊔ K₂) ⊓ normalizer (X : Set G), n * z = z * n)
    (h7 : 7 ∣ Nat.card ↥(centralizer ({z} : Set G) ⊓ D.M)) :
    UniqueMax D.M (D.M ⊓ centralizer ({z} : Set G)) := by
  have hle : ∀ {Y : Subgroup G}, (∀ y ∈ Y, y * z = z * y) → Y ≤ centralizer ({z} : Set G) := by
    intro Y hY y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hY y hy
  have hL : K₁ ⊔ K₂ ≤ D.M :=
    sup_le (uc22p22a_le_of_isSubnormal hH.mem₁.1) (uc22p22a_le_of_isSubnormal hH.mem₂.1)
  refine Set.eq_singleton_iff_unique_mem.2 ⟨⟨D.maxLocal, inf_le_left⟩, fun N hN => ?_⟩
  obtain ⟨hNmax, hCN⟩ := hN
  have hTC : D.T ≤ D.M ⊓ centralizer ({z} : Set G) := le_inf D.sylowM.le (hle hzT)
  have hXM : X ≤ D.M := hH.sylow.le.trans hL
  have hXC : X ≤ D.M ⊓ centralizer ({z} : Set G) := le_inf hXM (hle hzX)
  have hNM : N ≤ D.M := by
    refine h145 K₁ K₂ X hH N (hXC.trans hCN) ?_ ?_ ?_ ?_
    · exact TwelveEleven.fstar_eq_pCoreOf_of_charTwo (D.standing.charTwo _ hNmax.1)
    · exact c23_odd_relIndex_of_le D (hTC.trans hCN)
    · intro n hn
      obtain ⟨hnL, hnX⟩ := Subgroup.mem_inf.1 hn
      refine ⟨n, Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨?_, hnL⟩, hnX⟩, fun x _ => rfl⟩
      exact hCN ⟨hL hnL, Subgroup.mem_centralizer_singleton_iff.2 (hzN n hn)⟩
    · exact h7.trans (Subgroup.card_dvd_of_le fun g hg =>
        ⟨hCN ⟨hg.2, hg.1⟩, hg.2⟩)
  exact (hNmax.2 D.M D.maxLocal.1 hNM).symm

theorem c23_uniqueMax_of_conj (D : Data G) {z m : G} (hm : m ∈ D.M)
    (h : UniqueMax D.M (D.M ⊓ centralizer ({m * z * m⁻¹} : Set G))) :
    UniqueMax D.M (D.M ⊓ centralizer ({z} : Set G)) := by
  by_contra hz
  obtain ⟨N, hN, hle, hne⟩ := c23_exists_calM_ne_conj D.maxLocal hm hz
  have hmem : N ∈ calMOf (D.M ⊓ centralizer ({m * z * m⁻¹} : Set G)) := ⟨hN, hle⟩
  rw [h] at hmem
  exact hne hmem

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
