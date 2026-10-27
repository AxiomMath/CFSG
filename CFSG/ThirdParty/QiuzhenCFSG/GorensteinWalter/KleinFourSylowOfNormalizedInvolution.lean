module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourSupInvolutionSylow
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-! # A Klein four Sylow subgroup from an outside normalizing involution -/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- Suppose all ambient Sylow `2`-subgroups have order eight.  If an outside
involution normalizes both `D` and a Klein four `V ≤ D`, then `V` has odd
index in `D`, and hence is a Sylow `2`-subgroup of `D`. -/
public theorem kleinFour_subgroupOf_has_odd_index_of_normalized_outside_involution
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) (hScard : Nat.card (S : Subgroup G) = 8)
    (D V : Subgroup G) (hVleD : V ≤ D) (hVK : IsKleinFour V)
    {y : G} (hy : IsInvolution y) (hyD : y ∉ D)
    (hyND : y ∈ Subgroup.normalizer (D : Set G))
    (hyNV : y ∈ Subgroup.normalizer (V : Set G)) :
    ¬ 2 ∣ (V.subgroupOf D).index := by
  classical
  let Z : Subgroup G := Subgroup.zpowers y
  let R : Subgroup G := D ⊔ Z
  let P : Subgroup G := V ⊔ Z
  let PR : Subgroup R := P.subgroupOf R
  obtain ⟨Q, hPReqQ, hRcard, hPRcard⟩ :=
    exists_sylow_sup_zpowers_of_normalized_kleinFour
      S hScard D V hVleD hVK hy hyD hyND hyNV
  change PR = (Q : Subgroup R) at hPReqQ
  change Nat.card R = Nat.card D * 2 at hRcard
  change Nat.card PR = 8 at hPRcard
  have hPRindexOdd : ¬ 2 ∣ PR.index := by
    rw [hPReqQ]
    exact Q.not_dvd_index
  let VD : Subgroup D := V.subgroupOf D
  have hVDcard : Nat.card VD = 4 := by
    calc
      Nat.card VD = Nat.card V :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVleD).toEquiv
      _ = 4 := hVK.card_four
  have hPRmul := Subgroup.card_mul_index PR
  have hVDmul := Subgroup.card_mul_index VD
  have hindexEq : PR.index = VD.index := by
    rw [hPRcard, hRcard] at hPRmul
    rw [hVDcard] at hVDmul
    omega
  simpa [VD, hindexEq] using hPRindexOdd

end CFSG.GorensteinWalter
