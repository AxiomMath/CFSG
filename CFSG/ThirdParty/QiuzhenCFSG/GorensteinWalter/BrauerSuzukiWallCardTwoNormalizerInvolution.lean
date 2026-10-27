module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BrauerSuzukiWallCardTwoStrongEmbedding
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Involutions in the `A₄` normalizer

In the `|K| = 2` branch, `H` is a normal Klein four subgroup of
`N_G(H) ≃ A₄`, hence the unique Sylow `2`-subgroup.  Every involution of
the normalizer therefore lies in `H`.
-/

namespace CFSG.GorensteinWalter

universe u

/-- Every involution in `N_G(H)` lies in `H` when `|K| = 2`. -/
public theorem
    BrauerSuzukiWallHypotheses.involution_mem_H_of_mem_normalizer_of_card_K_eq_two
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G)
    (hk : Nat.card h.K = 2) {x : G}
    (hxN : x ∈ Subgroup.normalizer (h.H : Set G))
    (hxI : IsInvolution x) :
    x ∈ h.H := by
  classical
  let N : Subgroup G := Subgroup.normalizer (h.H : Set G)
  have hHleN : h.H ≤ N := Subgroup.le_normalizer
  let HN : Subgroup N := h.H.subgroupOf N
  have hHNcard : Nat.card HN = 4 := by
    calc
      Nat.card HN = Nat.card h.H :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHleN).toEquiv
      _ = 4 := (h.isKleinFour_H_of_card_K_eq_two hk).card_four
  have hNcard : Nat.card N = 12 := by
    obtain ⟨e⟩ :=
      h.normalizer_mulEquiv_alternatingGroup_four_of_card_K_eq_two hk
    calc
      Nat.card N = Nat.card (alternatingGroup (Fin 4)) :=
        Nat.card_congr e.toEquiv
      _ = 12 := alternatingGroup.card_of_card_eq_four (by simp)
  have hHNindex : HN.index = 3 := by
    have hmul := HN.card_mul_index
    rw [hHNcard, hNcard] at hmul
    omega
  have hHNp : IsPGroup 2 HN := by
    apply IsPGroup.of_card (n := 2)
    simpa using hHNcard
  let P : Sylow 2 N := hHNp.toSylow (by rw [hHNindex]; norm_num)
  have hHNnormal : HN.Normal := by
    apply (Subgroup.normal_subgroupOf_iff hHleN).2
    intro y n hyH hnN
    exact (Subgroup.mem_normalizer_iff.mp hnN y).mp hyH
  have hPnormal : (P : Subgroup N).Normal := by
    simpa [P, IsPGroup.toSylow_coe] using hHNnormal
  let : Unique (Sylow 2 N) := Sylow.unique_of_normal P hPnormal
  let xN : N := ⟨x, hxN⟩
  have hxNI : IsInvolution xN :=
    BenderSuzuki.IsInvolution.subtype hxI hxN
  have hxOrder : orderOf xN = 2 :=
    orderOf_eq_prime hxNI.2 hxNI.1
  let Z : Subgroup N := Subgroup.zpowers xN
  have hZp : IsPGroup 2 Z := by
    apply IsPGroup.of_card (n := 1)
    simp [Z, Nat.card_zpowers, hxOrder]
  obtain ⟨Q, hZQ⟩ := hZp.exists_le_sylow
  have hQP : Q = P := Subsingleton.elim Q P
  have hxP : xN ∈ (P : Subgroup N) := by
    rw [← hQP]
    exact hZQ (Subgroup.mem_zpowers xN)
  have hxHN : xN ∈ HN := by
    simpa [P, IsPGroup.toSylow_coe] using hxP
  exact hxHN

end CFSG.GorensteinWalter
