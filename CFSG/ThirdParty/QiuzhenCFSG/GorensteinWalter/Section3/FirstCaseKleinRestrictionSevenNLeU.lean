module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixIndex
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinIntersectionOdd
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OddSubgroupLeOddFactor
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

/-! In restriction (7), the odd intersection with `VU` lies in `U`.

The index-six intersection is odd by restriction (6).  Since `V` is a
Klein four group, `VU` is a commuting `2`-by-odd product, so the generic
odd-subgroup transfer puts the intersection in its odd factor.
-/

public theorem firstCase_klein_restrictionSeven_N_le_U
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hklein : IsKleinFour (pCore 2 c.Hhat))
    {y : G} (hy : IsInvolution y) (hyH : y ∉ c.Hhat)
    (hindex :
      let D := c.Hhat ⊓ conjugateSubgroup c.Hhat y
      let N := D ⊓ (twoCoreOf c.Hhat ⊔ c.U)
      (N.subgroupOf D).index = 6) :
    let D := c.Hhat ⊓ conjugateSubgroup c.Hhat y
    let N := D ⊓ (twoCoreOf c.Hhat ⊔ c.U)
    N ≤ c.U := by
  classical
  intro D N
  let V : Subgroup G := twoCoreOf c.Hhat
  let B : Subgroup G := V ⊔ c.U
  have hNleB : N ≤ B := inf_le_right
  have hNodd : Odd (Nat.card N) := by
    have hcop := firstCase_klein_intersection_odd_of_index_six
      hmin c hfirst hklein hy hyH hindex
    exact Nat.coprime_two_left.mp (by simpa [D, N, B, V] using hcop)
  have hBleHhat : B ≤ c.Hhat := by
    have h26 := theorem_2_6 hmin c
    dsimp [B, V]
    apply sup_le
    · exact Subgroup.map_subtype_le (pCore 2 c.Hhat)
    · rw [h26.1]
      exact Subgroup.map_subtype_le (pPrimeCore 2 c.Hhat)
  have hVnormH : IsNormalIn V c.Hhat := by
    dsimp [V, twoCoreOf]
    refine ⟨Subgroup.map_subtype_le (pCore 2 c.Hhat), ?_⟩
    intro h hh v hv
    rcases Subgroup.mem_map.mp hv with ⟨v0, hv0, rfl⟩
    exact Subgroup.mem_map.mpr ⟨
      (⟨h, hh⟩ : c.Hhat) * v0 * (⟨h, hh⟩ : c.Hhat)⁻¹,
      (pCore_normal (p := 2) (G := c.Hhat)).conj_mem v0 hv0
        (⟨h, hh⟩ : c.Hhat), by simp⟩
  have hUnormH : IsNormalIn c.U c.Hhat := by
    have h26 := theorem_2_6 hmin c
    rw [h26.1]
    refine ⟨Subgroup.map_subtype_le (pPrimeCore 2 c.Hhat), ?_⟩
    intro h hh u hu
    rcases Subgroup.mem_map.mp hu with ⟨u0, hu0, rfl⟩
    exact Subgroup.mem_map.mpr ⟨
      (⟨h, hh⟩ : c.Hhat) * u0 * (⟨h, hh⟩ : c.Hhat)⁻¹,
      (pPrimeCore_normal (p := 2) (G := c.Hhat)).conj_mem u0 hu0
        (⟨h, hh⟩ : c.Hhat), by simp⟩
  have hVnormB : IsNormalIn V B :=
    ⟨le_sup_left, by
      intro b hb v hv
      exact hVnormH.2 b (hBleHhat hb) v hv⟩
  have hUnormB : IsNormalIn c.U B :=
    ⟨le_sup_right, by
      intro b hb u hu
      exact hUnormH.2 b (hBleHhat hb) u hu⟩
  have hVU : ∀ w : G, w ∈ V → ∀ u : G, u ∈ c.U → w * u = u * w := by
    intro w hw u hu
    have h26 := theorem_2_6 hmin c
    have hVc : V ≤ Subgroup.centralizer (c.U : Set G) := by
      simpa [V, h26.1] using twoCoreOf_centralizes_oddCoreOf c.Hhat
    exact (Subgroup.mem_centralizer_iff.mp (hVc hw) u hu).symm
  have hVp : IsPGroup 2 V := by
    have hcard : Nat.card V = 2 ^ 2 := by
      simpa [V] using (firstCase_klein_V_klein c hklein).card_four
    exact IsPGroup.of_card hcard
  have hdisj : Disjoint V c.U := by
    have hVne : Nat.card V ≠ 0 := Nat.card_pos.ne'
    have hUodd : Nat.Coprime 2 (Nat.card c.U) := by
      have h26 := theorem_2_6 hmin c
      rw [h26.1]
      change Nat.Coprime 2 (Nat.card (oddCoreOf c.Hhat))
      rw [show Nat.card (oddCoreOf c.Hhat) = Nat.card (pPrimeCore 2 c.Hhat) by
        simpa [oddCoreOf] using
          (Subgroup.card_map_of_injective (K := pPrimeCore 2 c.Hhat)
            c.Hhat.subtype_injective)]
      exact pPrimeCore_coprime_card (p := 2) (G := c.Hhat)
    rcases hVp.exists_card_eq with ⟨n, hn⟩
    have hcop : Nat.Coprime (Nat.card V) (Nat.card c.U) := by
      rw [hn]
      exact hUodd.pow_left n
    exact Subgroup.disjoint_of_coprime_natCard hcop
  have hNleU := odd_order_subgroup_le_of_le_sup_of_twoPGroup V c.U N
    hVnormB hUnormB hVU hNleB hVp hNodd hdisj
  simpa [B, V] using hNleU

end CFSG.GorensteinWalter
