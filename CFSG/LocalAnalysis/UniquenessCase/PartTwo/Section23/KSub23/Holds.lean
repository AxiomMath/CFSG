module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KSub23.Large
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KSub23.J1
import CFSG.Adapters.StatedPSLTwo
import CFSG.Adapters.StatedSLPerfect
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNotLarge23.Parts

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo Subgroup

theorem kSub23Simple_holds :
    KSub23Simple := by
  intro S _ _ hshape Y hY
  rcases hshape with ⟨a, hL2 | hSz⟩ | hrest
  · exact KS23.eq_bot_or_isSimpleGroup_of_isL2 hL2 Y hY
  · exact KS23.eq_bot_or_isSimpleGroup_of_isSz hSz Y hY
  · rcases hrest with ⟨q, hq, hq2, hL2Odd⟩ | hJ1
    · exact KS23.eq_bot_or_isSimpleGroup_of_isL2Odd hq hq2 hL2Odd Y hY
    · exact KS23.eq_bot_or_isSimpleGroup_of_isJ1 hJ1 Y hY

namespace KS23

private theorem isPerfect_of_isL2 {W : Type} [Group W] {m : ℕ}
    (hm : 3 ≤ m) (hW : IsL2 W m) : Group.IsPerfect W := by
  obtain ⟨_, K, hfield, hfin, hKcard, ⟨e⟩⟩ :=
    CFSG.Blueprint.LieModel.statedClassicalModel hW (by decide)
  letI := hfield
  letI := hfin
  have hK4 : 4 ≤ Nat.card K := by
    rw [hKcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
  haveI : Group.IsPerfect ↥(CFSG.Open.StatedSL 2 K) :=
    CFSG.Open.StatedAPI.isPerfect_statedSL_two_of_four_le_card hK4
  haveI : Group.IsPerfect (CFSG.Open.StatedProj (CFSG.Open.StatedSL 2 K)) :=
    Group.IsPerfect.ofSurjective
      (f := QuotientGroup.mk'
        ((CFSG.Open.StatedScalars (Fin 2) K).subgroupOf (CFSG.Open.StatedSL 2 K)))
      (QuotientGroup.mk'_surjective _)
  exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective

private theorem three_dvd_two_pow_mul_four_pow_sub_one (m : ℕ) :
    3 ∣ 2 ^ m * (4 ^ m - 1) := by
  have h3 : 3 ∣ 4 ^ m - 1 := by
    simpa using Nat.sub_one_dvd_pow_sub_one 4 m
  exact Nat.dvd_mul_left_of_dvd h3 (2 ^ m)

private theorem not_eq_sixty_of_three_le {m : ℕ} (hm : 3 ≤ m) :
    2 ^ m * (4 ^ m - 1) ≠ 60 := by
  intro h
  have h2m : 8 ≤ 2 ^ m := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have h4m : 63 ≤ 4 ^ m - 1 := by
    have h43 : 4 ^ 3 ≤ 4 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    norm_num at h43 ⊢
    omega
  have hprod : 8 * 63 ≤ 2 ^ m * (4 ^ m - 1) :=
    mul_le_mul h2m h4m (by norm_num) (by positivity)
  rw [h] at hprod
  omega

private theorem not_dvd_j1_of_three_le {m : ℕ} (hm : 3 ≤ m) :
    ¬ 2 ^ m * (4 ^ m - 1) ∣ 175560 := by
  intro hdvd
  have h2mdvd : 2 ^ m ∣ 175560 :=
    (dvd_mul_of_dvd_left (dvd_refl (2 ^ m)) (4 ^ m - 1)).trans hdvd
  have hcop : Nat.Coprime (2 ^ m) 21945 :=
    Nat.Coprime.pow_left m (Nat.coprime_two_left.mpr (by decide))
  have h175560 : 175560 = 2 ^ 3 * 21945 := by norm_num
  have h2m3 : 2 ^ m ∣ 2 ^ 3 := by
    apply hcop.dvd_of_dvd_mul_right
    rwa [h175560] at h2mdvd
  have hmle : m ≤ 3 :=
    (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp h2m3
  have hm3 : m = 3 := by omega
  rw [hm3] at hdvd
  norm_num at hdvd

theorem kSub23_one :
    ∀ (W S : Type) [Group W] [Finite W] [Group S] [Finite S] (m : ℕ),
      3 ≤ m → IsL2 W m → B23Shape S →
      ∀ Y : Subgroup S, (∃ f : W →* ↥Y, Function.Surjective f) →
        (∃ T : Sylow 2 S, ∀ t : T, (t : S) ∈ Subgroup.normalizer (Y : Set S)) →
        Y = ⊥ ∨ Y = ⊤ := by
  intro W S _ _ _ _ m hm hW hshape Y ⟨f, hf⟩ ⟨T, hT⟩
  have hperfW : Group.IsPerfect W := isPerfect_of_isL2 hm hW
  have hsimpleW : IsSimpleGroup W := CFSG.Blueprint.LieModel.isSimpleGroup_psl_two hW
  have hperfY : Group.IsPerfect ↥Y := by
    haveI := hperfW
    exact Group.IsPerfect.ofSurjective hf
  have hY : ⁅Y, Y⁆ = Y := Subgroup.isPerfect_iff.mp hperfY
  by_cases hne : Y = ⊥
  · exact Or.inl hne
  · right
    have hker : f.ker = ⊥ := by
      rcases hsimpleW.eq_bot_or_eq_top_of_normal f.ker with h | h
      · exact h
      · exfalso
        apply hne
        rw [eq_bot_iff]
        intro y hy
        obtain ⟨w, hw⟩ := hf ⟨y, hy⟩
        have hwker : w ∈ f.ker := by rw [h]; exact Subgroup.mem_top w
        have hfw : f w = 1 := MonoidHom.mem_ker.mp hwker
        have : (⟨y, hy⟩ : ↥Y) = 1 := by rw [← hw, hfw]
        simpa using congrArg Subtype.val this
    have hinj : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp hker
    have hcardY : Nat.card ↥Y = Nat.card W :=
      Nat.card_congr (Equiv.ofBijective f ⟨hinj, hf⟩).symm
    have hcardW : Nat.card W = 2 ^ m * ((2 ^ m) ^ 2 - 1) := (KNL23.card_isL2 hW).2
    have hpow : (2 ^ m) ^ 2 = 4 ^ m := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    have hW4 : Nat.card W = 2 ^ m * (4 ^ m - 1) := by
      rw [hcardW, hpow]
    rcases hshape with ⟨a, hL2 | hSz⟩ | hrest
    · exact eq_top_of_sylow_le_normalizer_of_isL2 hL2 Y hY hne T hT
    · exfalso
      have h3Y : 3 ∣ Nat.card ↥Y := by
        rw [hcardY, hW4]
        exact three_dvd_two_pow_mul_four_pow_sub_one m
      exact not_three_dvd_card_of_isSz hSz (h3Y.trans Y.card_subgroup_dvd_card)
    · rcases hrest with ⟨q, hq, hq2, hL2Odd⟩ | hJ1
      · rcases eq_top_or_isAlt_of_isL2Odd hq hq2 hL2Odd Y hY hne with htop | hAlt
        · exact htop
        · exfalso
          obtain ⟨eY⟩ := hAlt
          have hYcard : Nat.card ↥Y = 60 := by
            rw [Nat.card_congr eY.toEquiv, nat_card_alternatingGroup]
            norm_num
          exact not_eq_sixty_of_three_le hm (by rw [← hW4, ← hcardY, hYcard])
      · exfalso
        have hdvd : Nat.card ↥Y ∣ 175560 := by
          rw [← KNL23.card_isJ1 hJ1]
          exact Y.card_subgroup_dvd_card
        rw [hcardY, hW4] at hdvd
        exact not_dvd_j1_of_three_le hm hdvd

theorem kSub23_three :
    ∀ (S : Type) [Group S] [Finite S], B23Shape S →
      ∀ Y : Subgroup S, ⁅Y, Y⁆ = Y →
        ∀ R : Subgroup ↥Y, R.Normal → Group.IsSolvable ↥R → R = ⊥ := by
  intro S _ _ hshape Y hY R hRnorm hRsolv
  haveI : R.Normal := hRnorm
  rcases kSub23Simple_holds S hshape Y hY with hYbot | hYsimple
  · subst Y
    exact Subgroup.eq_bot_of_subsingleton R
  · rcases hYsimple.eq_bot_or_eq_top_of_normal R with hRbot | hRtop
    · exact hRbot
    · exfalso
      haveI : Nontrivial ↥Y := hYsimple.toNontrivial
      haveI : Group.IsPerfect ↥Y := Subgroup.isPerfect_iff.mpr hY
      haveI hsolvTop : Group.IsSolvable ↥(⊤ : Subgroup ↥Y) := hRtop ▸ hRsolv
      let e := (Subgroup.topEquiv : ↥(⊤ : Subgroup ↥Y) ≃* ↥Y)
      have hsolvY : Group.IsSolvable ↥Y :=
        Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
      exact (Group.IsPerfect.not_isSolvable ↥Y) hsolvY

end KS23

theorem kSub23_holds : KSub23 :=
  ⟨KS23.kSub23_one, KS23.kSub23_two, KS23.kSub23_three⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
