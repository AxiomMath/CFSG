module

public import CFSG.RankThree.PartTwo.Sec4.StatementsGraphField
import CFSG.RankThree.PartTwo.Sec4.StepsBender
import CFSG.RankThree.PartTwo.Sec4.Steps444

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

theorem rank3II_4_48_3 :
    ∀ (G : Type) [Group G] [Finite G] (A M H : Subgroup G) (s : G), Ctx4443 G A M H s →
      starQuot G s ∈
        Subgroup.centralizer (CFSG.pCore 3 (G ⧸ CFSG.pPrimeCore 3 G) : Set (G ⧸ CFSG.pPrimeCore 3 G)) :=
  fun G _ _ A M H s h => by
  have hs2 : IsPGroup 2 (Subgroup.zpowers s) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (H ⊓ M)).to_le
      (Subgroup.zpowers_le.mpr h.concl4442.1)
  have hQ : ¬ 3 ∣ Nat.card (Subgroup.zpowers s) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hs2
    rw [hk]
    intro h3
    exact absurd (Nat.prime_three.dvd_of_dvd_pow h3) (by norm_num)
  have hAQ : A ≤ Subgroup.normalizer (Subgroup.zpowers s : Set G) := by
    intro a ha
    have hsa : a * s = s * a := Subgroup.mem_centralizer_iff.mp h.concl4442.2.1 a ha
    have hconj : a * s * a⁻¹ = s := by rw [hsa, mul_inv_cancel_right]
    have key : ∀ k : ℤ, a * s ^ k * a⁻¹ = s ^ k := fun k => by rw [← conj_zpow, hconj]
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k, (key k).symm⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, mul_left_cancel (mul_right_cancel ((key k).trans hk))⟩
  exact map_le_centralizer_pCore_of_bender h.ctx444.isE27.1
    (fun _ hx hx3 => rank3II_4_45 G A M h.ctx444 _ hx hx3) hQ hAQ
    (Subgroup.mem_map_of_mem _ (Subgroup.mem_zpowers s))

end CFSG.RankThree.PartTwo.Sec4
