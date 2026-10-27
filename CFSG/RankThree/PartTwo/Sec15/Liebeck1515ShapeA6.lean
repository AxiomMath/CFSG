module

public import CFSG.RankThree.PartTwo.Sec14.Item14ListStatements
import CFSG.RankThree.PartTwo.Sec14.Item14Res9ProofPair
import CFSG.RankThree.PartTwo.KFacts.KS12Moves
import CFSG.RankThree.PartTwo.Sec15.LiebeckA6Normalizer

public section

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck1515

private theorem exists_hom_ker_eq {Γ : Type*} [Group Γ] [Finite Γ] {U V : Subgroup Γ}
    (hP : Sec14.Res9Pair.IsPair U V) : ∃ π : Γ →* alternatingGroup (Fin 6), π.ker = V := by
  have := hP.normal_left
  have := hP.normal_right
  obtain ⟨-, ⟨e⟩⟩ := hP.cover_left
  let φ : ↥U →* Γ ⧸ V := (QuotientGroup.mk' V).comp U.subtype
  have hker : φ.ker = Subgroup.center ↥U := by
    ext u
    rw [MonoidHom.mem_ker]
    change QuotientGroup.mk' V (u : Γ) = 1 ↔ u ∈ Subgroup.center ↥U
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    have h1 : (u : Γ) ∈ V ↔ (u : Γ) ∈ U ⊓ V := ⟨fun h => ⟨u.2, h⟩, fun h => h.2⟩
    rw [h1, hP.inf_eq]
    constructor
    · intro h
      obtain ⟨_, h'⟩ := Sec14.Item148PtRes.mem_centerIn_iff.mp h
      exact h'
    · intro h
      exact Sec14.Item148PtRes.mem_centerIn_iff.mpr ⟨u.2, h⟩
  have hsurj : Function.Surjective φ := by
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective V x
    obtain ⟨y, hy, v, hv, rfl⟩ := Sec14.Item148PtRes.exists_mul_eq hP.sup_eq g
    refine ⟨⟨y, hy⟩, ?_⟩
    change QuotientGroup.mk' V y = QuotientGroup.mk' V (y * v)
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    simpa using hv
  let χ : Γ ⧸ V ≃* alternatingGroup (Fin 6) :=
    ((QuotientGroup.quotientKerEquivOfSurjective φ hsurj).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hker)).trans e
  refine ⟨χ.toMonoidHom.comp (QuotientGroup.mk' V), ?_⟩
  ext x
  rw [MonoidHom.mem_ker]
  change χ (QuotientGroup.mk' V x) = 1 ↔ x ∈ V
  rw [χ.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

private theorem le_of_isPerfect_le_normalizer_of_not_le {Γ : Type*} [Group Γ] [Finite Γ]
    {U V F W : Subgroup Γ} (hP : Sec14.Res9Pair.IsPair U V) (hF : Group.IsPerfect ↥F)
    (hW : IsPGroup 2 W) (hWV : ¬ W ≤ V) (hFW : F ≤ Subgroup.normalizer (W : Set Γ)) :
    F ≤ V := by
  obtain ⟨π, hπ⟩ := exists_hom_ker_eq hP
  have hWbar : W.map π ≠ ⊥ := by
    intro h
    apply hWV
    rw [← hπ]
    exact (Subgroup.map_eq_bot_iff W).1 h
  have hFbar : F.map π = ⊥ := by
    haveI := hF
    exact Sec15.LiebeckA6.eq_bot_of_isPerfect_le_normalizer_A6 (Group.IsPerfect.map π)
      (hW.map π) hWbar
      ((Subgroup.map_mono hFW).trans (Subgroup.le_normalizer_map π))
  rw [← hπ]
  exact (Subgroup.map_eq_bot_iff F).1 hFbar

theorem card_le_of_isPerfect_le_normalizer {Q : Type*} [Group Q] [Finite Q]
    (hQ : Sec4.IsTripleCover Q (alternatingGroup (Fin 6)) ∨ Sec14.IsCentralProductA6Covers Q)
    {F V : Subgroup Q} (hF : Group.IsPerfect ↥F) (hV : IsPGroup 2 V) (hV1 : V ≠ ⊥)
    (hFV : F ≤ Subgroup.normalizer (V : Set Q)) : Nat.card F ≤ 1080 := by
  rcases hQ with hT | hC
  · have hA6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
      rw [nat_card_alternatingGroup]
      simp [Nat.factorial]
    have hQc := KFacts.card_of_isTripleCover hT
    exact (Subgroup.card_le_card_group F).trans (by omega)
  · obtain ⟨U, C, hP⟩ := Sec14.Res9Pair.exists_isPair hC
    have hnot : ¬ (V ≤ U ∧ V ≤ C) := by
      rintro ⟨hVU, hVC⟩
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have h3 : IsPGroup 3 ↥(U ⊓ C) :=
        IsPGroup.of_card (p := 3) (n := 1) (by rw [hP.card_inf]; norm_num)
      exact hV1 ((IsPGroup.disjoint_of_ne 2 3 (by norm_num) V (U ⊓ C) hV h3).eq_bot_of_le
        (le_inf hVU hVC))
    by_cases hVC : V ≤ C
    · have hVU : ¬ V ≤ U := fun h => hnot ⟨h, hVC⟩
      have hFU : F ≤ U := le_of_isPerfect_le_normalizer_of_not_le hP.symm hF hV hVU hFV
      exact (Subgroup.card_le_of_le hFU).trans
        (Sec14.Item148PtRes.card_eq_of_isTripleCover hP.cover_left).le
    · have hFC : F ≤ C := le_of_isPerfect_le_normalizer_of_not_le hP hF hV hVC hFV
      exact (Subgroup.card_le_of_le hFC).trans
        (Sec14.Item148PtRes.card_eq_of_isTripleCover hP.cover_right).le

end CFSG.RankThree.PartTwo.Sec15.Liebeck1515
