module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BrauerSuzukiWallCardTwoOutsideInvolutions
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The core of the normalizer in the order-two branch

In the proper `|K| = 2` branch, the normalizer `N=N_G(H)` is core-free.  An
outside involution `u` confines the normal core to the order-three subgroup
`N ∩ N^u`.  If the core were nontrivial, this intersection would be normal
in the ambient group, contradicting its being self-normalizing inside
`N ≃ A₄`.
-/

open scoped Pointwise
open BenderSuzuki.PFchapter1section1

namespace CFSG.GorensteinWalter

universe u

/-- In the proper `|K| = 2` branch, `N_G(H)` has trivial normal core. -/
public theorem
    BrauerSuzukiWallHypotheses.normalCore_normalizer_eq_bot_of_card_K_eq_two
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G)
    (hk : Nat.card h.K = 2)
    (hNne : Subgroup.normalizer (h.H : Set G) ≠ ⊤) :
    (Subgroup.normalizer (h.H : Set G)).normalCore = ⊥ := by
  classical
  let N : Subgroup G := Subgroup.normalizer (h.H : Set G)
  let C : Subgroup G := N.normalCore
  have hOutCard : Nat.card {v : G // IsInvolution v ∧ v ∉ N} = 12 := by
    simpa [N] using
      h.outside_involutions_card_eq_twelve_of_card_K_eq_two hk hNne
  have hOutNonempty : Nonempty {v : G // IsInvolution v ∧ v ∉ N} :=
    Finite.card_pos_iff.mp (by rw [hOutCard]; norm_num)
  let u : {v : G // IsInvolution v ∧ v ∉ N} := hOutNonempty.some
  have huI : IsInvolution (u : G) := u.property.1
  have huN : (u : G) ∉ N := u.property.2
  let T : Subgroup G := N ⊓ rightConjugate N (u : G)
  obtain ⟨hTcard0, _huNorm, _huInv⟩ :=
    h.normalizer_inf_rightConjugate_card_eq_three_and_inverted_of_card_K_eq_two
      hk huI (by simpa [N] using huN)
  have hTcard : Nat.card T = 3 := by
    simpa [T, N] using hTcard0
  have hCleT : C ≤ T := by
    intro x hxC
    refine ⟨Subgroup.normalCore_le N hxC, ?_⟩
    change x ∈ N.map (MulAut.conj (u : G)⁻¹).toMonoidHom
    rw [Subgroup.mem_map]
    refine ⟨(u : G) * x * (u : G)⁻¹, hxC (u : G), ?_⟩
    simp [mul_assoc]
  have hCdiv : Nat.card C ∣ 3 := by
    rw [← hTcard]
    exact Subgroup.card_dvd_of_le hCleT
  rcases (Nat.dvd_prime Nat.prime_three).mp hCdiv with hCone | hCthree
  · exact (Subgroup.eq_bot_iff_card C).2 hCone
  · exfalso
    have hCT : C = T :=
      Subgroup.eq_of_le_of_card_ge hCleT (by rw [hCthree, hTcard])
    have hTnormal : T.Normal := by
      rw [← hCT]
      exact Subgroup.normalCore_normal N
    have hTleN : T ≤ N := inf_le_left
    let TN : Subgroup N := T.subgroupOf N
    have hTNcard : Nat.card TN = 3 := by
      calc
        Nat.card TN = Nat.card T :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTleN).toEquiv
        _ = 3 := hTcard
    have hNiso : Nonempty (N ≃* alternatingGroup (Fin 4)) :=
      h.normalizer_mulEquiv_alternatingGroup_four_of_card_K_eq_two hk
    have hTNnorm : Subgroup.normalizer (TN : Set N) = TN :=
      normalizer_eq_self_of_card_eq_three_of_mulEquiv_alternatingGroup_four
        TN hTNcard hNiso
    have hTnormTop : Subgroup.normalizer (T : Set G) = ⊤ :=
      Subgroup.normalizer_eq_top_iff.mpr hTnormal
    have hNleT : N ≤ T := by
      intro x hxN
      let xN : N := ⟨x, hxN⟩
      have hxNorm : x ∈ Subgroup.normalizer (T : Set G) := by
        rw [hTnormTop]
        trivial
      have hxSub : xN ∈ (Subgroup.normalizer (T : Set G)).subgroupOf N :=
        hxNorm
      rw [Subgroup.subgroupOf_normalizer_eq hTleN, hTNnorm] at hxSub
      exact hxSub
    have hTN : T = N := le_antisymm hTleN hNleT
    have hNcard : Nat.card N = 12 := by
      calc
        Nat.card N = Nat.card (alternatingGroup (Fin 4)) :=
          Nat.card_congr hNiso.some.toEquiv
        _ = 12 := alternatingGroup.card_of_card_eq_four (by simp)
    rw [hTN, hNcard] at hTcard
    omega

end CFSG.GorensteinWalter
