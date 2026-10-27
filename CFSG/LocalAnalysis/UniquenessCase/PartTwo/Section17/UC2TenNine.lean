module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThirtyTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ComponentCalV1

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem v0_eq_bot_of_uc2_10_9_of_normal {D : Data G}
    (h109 : Inputs1719.UC2_10_9 D) {V₀ V : Subgroup G} (hV : Hyp125 D V₀ V)
    {L : Subgroup G} (hL : L ∈ calC D.M) (hLN : D.M ≤ normalizer (L : Set G))
    (hUL : UniqueMax D.M (L ⊔ D.T))
    {s p : ℕ} {B : Subgroup G} (hs : Odd s) (hp : p.Prime) (hdvd : p ∣ 2 ^ s - 1)
    (hBL : B ≤ L) (hBT : B ≤ normalizer (D.T : Set G)) (hcard : Nat.card B = p)
    (hBU : UC6.InU D.M B) : V₀ = ⊥ := by
  by_contra hV₀
  have hLU : L ≤ centralizer (D.U : Set G) :=
    commutator_U_eq_bot_of_uniqueMax hV hV₀ hL hLN hUL
  have hZU : D.Z ≤ D.U := UC22.uc22main1_Z_le_U D
  have hcent : B ≤ centralizer (D.Z : Set G) :=
    hBL.trans (hLU.trans (Subgroup.centralizer_le hZU))
  exact hV₀ (v0_eq_bot_of_uc2_10_9 h109 hV hs hp hdvd
    (le_inf (hBL.trans hL.1.le) hBT) hcard hBU hcent)

theorem uniqueMax_of_inverted_uc2_10_9 {D : Data G} (h109 : Inputs1719.UC2_10_9 D)
    {s p : ℕ} {B K : Subgroup G} (hs : Odd s) (hp : p.Prime) (hdvd : p ∣ 2 ^ s - 1)
    (hB : B ≤ D.M ⊓ normalizer (D.T : Set G)) (hcard : Nat.card B = p) (hBU : UC6.InU D.M B)
    (hBK : B ≤ K) (hKM : K ≤ D.M) (hinv : UC22.F05.InvertedIn K B) :
    UniqueMax D.M (K ⊔ D.T) := by
  obtain ⟨-, h2, -, -⟩ := h109 s p B hs hp hdvd hB hcard hBU
  apply Set.Subset.antisymm
  · intro N hN
    rw [Set.mem_singleton_iff]
    by_contra hNM
    have hN' : N ∈ calMOf (B ⊔ D.T) := ⟨hN.1, (sup_le_sup_right hBK _).trans hN.2⟩
    apply h2 N hN' hNM
    obtain ⟨g, hgK, hg⟩ := hinv
    exact ⟨g, ⟨hKM hgK, (le_sup_left.trans hN.2) hgK⟩, hg⟩
  · rintro N rfl
    exact ⟨D.maxLocal, sup_le hKM D.sylowM.le⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
