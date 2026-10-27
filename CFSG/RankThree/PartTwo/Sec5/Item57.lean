module

public import CFSG.RankThree.PartTwo.Sec5.Item56

public section

namespace CFSG.RankThree.PartTwo.Sec5

open CFSG

universe u

variable {G : Type u} [Group G] [Finite G]

theorem rank3II_5_7 {A S U : Subgroup G} (h : SectionFiveHyp A S)
    (hU : IsNormalFourGroup A S U)
    (hSB : ⁅S, A ⊓ Subgroup.centralizer (U : Set G)⁆ = ⊥) :
    S ⊓ Subgroup.centralizer (A : Set G) = ⊥ ∧ omegaOneSub S = U := by
  have hB9 := card_inf_centralizer_fourGroup h hU
  have h55 := rank3II_5_5 h (inf_le_left : A ⊓ Subgroup.centralizer (U : Set G) ≤ A) hB9
  have hSC : S ≤ Subgroup.centralizer
      ((A ⊓ Subgroup.centralizer (U : Set G) : Subgroup G) : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hSB
  rw [inf_eq_left.mpr hSC] at h55
  have hUZ := le_centralizer_fourGroup h hU
  have hΩ : omegaOneSub S = U := by
    apply le_antisymm
    · rw [omegaOneSub_eq_closure, Subgroup.closure_le]
      rintro x ⟨hxS, hx2⟩
      by_contra hxU
      obtain ⟨hE, hEcard⟩ := isElemAbelian_sup_zpowers (p := 2) hU.elemAbelian hxU hx2
        (fun u hu => (Subgroup.mem_centralizer_iff.mp (hUZ hu) x hxS).symm)
      have h3 := le_pRank_of_elemAbelian Nat.prime_two (X := S)
        (sup_le hU.le (Subgroup.zpowers_le.mpr hxS)) hE (k := 3)
        (by simp [hEcard, hU.card_eq])
      omega
    · rw [omegaOneSub_eq_closure]
      intro x hx
      exact Subgroup.subset_closure ⟨hU.le hx, hU.elemAbelian.2 x hx⟩
  refine ⟨?_, hΩ⟩
  rcases Subgroup.bot_or_exists_ne_one (S ⊓ Subgroup.centralizer (A : Set G)) with
    hb | ⟨y, hy, hy1⟩
  · exact hb
  exfalso
  obtain ⟨k, hk⟩ := (h.isPGroup.to_le
    (inf_le_left : S ⊓ Subgroup.centralizer (A : Set G) ≤ S)).exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero, Subgroup.card_eq_one] at hk
    rw [hk] at hy
    exact hy1 (Subgroup.mem_bot.mp hy)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(S ⊓ Subgroup.centralizer (A : Set G))) 2 (by rw [hk]; exact dvd_pow_self 2 hk0)
  have hz2 : (z : G) ^ 2 = 1 := by
    have hz' := pow_orderOf_eq_one z
    rw [hz] at hz'
    rw [← Subgroup.coe_pow, hz', Subgroup.coe_one]
  have hz1 : (z : G) ≠ 1 := by
    intro h'
    have hz1' : z = 1 := Subtype.ext h'
    rw [hz1', orderOf_one] at hz
    norm_num at hz
  have hzU : (z : G) ∈ U := by
    rw [← hΩ, omegaOneSub_eq_closure]
    exact Subgroup.subset_closure ⟨(Subgroup.mem_inf.mp z.2).1, hz2⟩
  have hmem : (z : G) ∈ U ⊓ Subgroup.centralizer (A : Set G) :=
    Subgroup.mem_inf.mpr ⟨hzU, (Subgroup.mem_inf.mp z.2).2⟩
  rw [inf_centralizer_fourGroup_eq_bot h hU] at hmem
  exact hz1 (Subgroup.mem_bot.mp hmem)

end CFSG.RankThree.PartTwo.Sec5
