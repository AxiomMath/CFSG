module

public import CFSG.LocalAnalysis.StandardType.GGExcCompSLMarking
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeSplit
import CFSG.LocalAnalysis.StandardType.GGExcCompSLLen
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6Labels

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly

private theorem rawDatum_elim_const' {lab : LargeEvenLabel} {Q : Prop}
    (h : LargeEvenRawDatum lab (fun _ _ _ _ => Q)) : Q := by
  obtain ⟨t, l, n⟩ := lab
  cases t
  all_goals dsimp only [LargeEvenRawDatum, LargeEvenRecipeLinear, LargeEvenRecipeUnitary,
    LargeEvenRecipeSymplectic, LargeEvenRecipeOmegaPlus, LargeEvenRecipeOmegaMinus,
    LargeEvenRecipeChevalley, LargeEvenRecipeTwisted, LargeEvenRecipeSuzuki,
    LargeEvenRecipeG2Derived, LargeEvenRecipeTwF4Inherited] at h
  all_goals try split_ifs at h
  all_goals first
    | (obtain ⟨K, i1, i2, hK, b, c, hbc, hq⟩ := h
       exact hq)
    | (obtain ⟨K, i1, i2, hK, hq⟩ := h
       exact hq)

private theorem eq_of_ggLabelIso_of_dFourTag {labJ lab : LargeEvenLabel}
    (h : GGLabelIso labJ lab) (hJ : labJ.tag = .D ∧ labJ.rank = 4) : labJ = lab := by
  obtain ⟨t, l, n⟩ := labJ
  obtain ⟨t', l', n'⟩ := lab
  rcases h with h | h | h | h | h | h | h | h
  · exact h
  · rcases h with ⟨h1, -⟩
    rcases h1 with h2 | h2 <;> simp_all
  · rcases h with ⟨h1, -⟩
    have hl : l = 3 := congrArg LargeEvenLabel.rank h1
    have hl4 : l = 4 := hJ.2
    omega
  · rcases h with ⟨h1, -⟩
    have ht : t = .A := congrArg LargeEvenLabel.tag h1
    simp_all
  · rcases h with ⟨h1, -⟩
    have ht : t = .twD := congrArg LargeEvenLabel.tag h1
    simp_all
  · rcases h with ⟨h1, -⟩
    have ht : t = .twA := congrArg LargeEvenLabel.tag h1
    simp_all
  · rcases h with ⟨h1, -⟩
    have ht : t = .twD := congrArg LargeEvenLabel.tag h1
    simp_all
  · rcases h with ⟨-, h1⟩
    have ht : t = .A := congrArg LargeEvenLabel.tag h1
    simp_all

private theorem even_iff_three_dvd_two_pow_sub_one (n : ℕ) : 3 ∣ 2 ^ n - 1 ↔ Even n := by
  induction n using Nat.strong_induction_on with
  | h k ih =>
    rcases k with _ | _ | m
    · norm_num
    · norm_num
    · have h4 : (2 : ℕ) ^ (m + 2) = 4 * 2 ^ m := by
        rw [pow_add, pow_two]
        ring
      have hle : 1 ≤ 2 ^ m := by simpa using Nat.one_le_pow' m 1
      have hsub : 4 * 2 ^ m - 1 = 4 * (2 ^ m - 1) + 3 := by omega
      have hrec : (3 ∣ 2 ^ (m + 2) - 1) ↔ (3 ∣ 2 ^ m - 1) := by
        rw [h4, hsub, Nat.dvd_add_self_right]
        constructor
        · intro hd
          exact (Nat.prime_three.dvd_mul.mp hd).resolve_left (by norm_num)
        · intro hd
          exact dvd_mul_of_dvd_right hd 4
      rw [hrec, ih m (by omega)]
      constructor
      · rintro ⟨k, hk⟩
        exact ⟨k + 1, by omega⟩
      · rintro ⟨k, hk⟩
        exact ⟨k - 1, by omega⟩

theorem kg5e_E6
    {X : Type} [Group X] [Finite X] (hX : commutator X = ⊤)
    {A : Subgroup (MulAut X)} {δ : MulAut X} {J : Subgroup X}
    (hD : DatumOn (fun t => t = .E6) X A δ J)
    (hq : LargeEvenMarking X (fun lab _ _ _ _ _ => 2 ≤ lab.n)) :
    ¬ LargeEvenMarking J (fun lab _ _ _ _ _ => lab.tag = .D ∧ lab.rank = 4 ∧ Odd lab.n) := by
  have hδmem : δ ∈ A := hD.1.1.2.1
  have hδ3 : δ ^ 3 = 1 := hD.1.1.1.2 δ hδmem
  have hδne1 : δ ≠ 1 := hD.1.1.2.2.1
  have hcomp : IsComponentOf J (ggAutFixedSubgroup δ) := hD.1.1.2.2.2.1
  let P : LargeEvenLabel → Prop := fun lab => LargeEvenSplit 3 lab ∧ lab.tag = .E6
  have hdat : GGTorsionDatum P 3 δ J := by
    refine ⟨Nat.prime_three, by norm_num, hδ3, hδne1, hcomp, ?_⟩
    refine largeEvenMarking_mono
      (P := fun lab _ _ I _ θ => lab.tag = .E6 ∧ (LargeEvenSplit 3 lab ∧ GGInducedInn A θ I)) ?_
      hD.2.2.2
    intro lab R _ I F θ h
    exact ⟨⟨h.2.1, h.1⟩, h.2.2 δ hδmem⟩
  have hPtag : ∀ lab, P lab → lab.tag = .E6 ∨ lab.tag = .twE6 ∨ lab.tag = .E7 ∨ lab.tag = .E8 :=
    fun lab h => Or.inl h.2
  have hSL := ggTorsion_exc_simplyLaced (P := P)
    CFSG.StandardType.LangRat.langRatCompFieldLenSL_holds hPtag hdat
  obtain ⟨-, labSL, hlabSL, hrawSL⟩ := hSL
  have hP_SL : P labSL :=
    rawDatum_elim_const'
      (largeEvenRawDatum_mono (fun R _ I F h => h.2.2.elim fun _ hh => hh.1) hrawSL)
  have hfdSL : GGCompFieldDataSL (2 ^ labSL.n) J :=
    rawDatum_elim_const'
      (largeEvenRawDatum_mono (fun R _ I F h => h.2.2.elim fun _ hh => hh.2) hrawSL)
  have hHasSL : GGHasLabel labSL (X ⧸ Subgroup.center X) :=
    largeEvenRawDatum_mono (fun R _ I F h => ⟨h.2.2.choose⟩) hrawSL
  obtain ⟨-, labq, hlabq, hrawq⟩ := hq
  have hq2 : 2 ≤ labq.n :=
    rawDatum_elim_const'
      (largeEvenRawDatum_mono (fun R _ I F h => h.2.2.elim fun _ hh => hh) hrawq)
  have hHasq : GGHasLabel labq (X ⧸ Subgroup.center X) :=
    largeEvenRawDatum_mono (fun R _ I F h => ⟨h.2.2.choose⟩) hrawq
  have hrigid : GGLabelRigidInput := ggLabelRigidInput_holds
  have hEqSL : labSL = labq :=
    eq_of_ggLabelIso_of_e6Tag (hrigid labSL labq _ hlabSL hlabq hHasSL hHasq) (Or.inl hP_SL.2)
  have htagSL : labSL.tag = .E6 := hP_SL.2
  have hn2 : 2 ≤ labSL.n := by rw [hEqSL]; exact hq2
  have hdiv : 3 ∣ 2 ^ labSL.n - 1 := by
    rcases hP_SL.1 with ⟨-, hd⟩ | ⟨hunt, -⟩ | ⟨hD', -⟩ | ⟨hn1, -⟩
    · exact hd
    · exact (hunt (by simp [LargeEvenUntwisted, htagSL])).elim
    · rcases hD' with h | h <;> (rw [htagSL] at h; exact absurd h (by simp))
    · omega
  have hevenSL : Even labSL.n := (even_iff_three_dvd_two_pow_sub_one labSL.n).mp hdiv
  intro hJ
  obtain ⟨-, labD, hlabD, hrawD⟩ := hJ
  have hHasD : GGHasLabel labD (J ⧸ Subgroup.center J) :=
    largeEvenRawDatum_mono (fun R _ I F h => ⟨h.2.2.choose⟩) hrawD
  have hJprop : labD.tag = .D ∧ labD.rank = 4 ∧ Odd labD.n :=
    rawDatum_elim_const'
      (largeEvenRawDatum_mono (fun R _ I F h => h.2.2.elim fun _ hh => hh) hrawD)
  obtain ⟨m, -, hfdAt⟩ := hfdSL
  obtain ⟨lab', hlab', -, hdeg', -, hHas', -⟩ := hfdAt
  have hEqD : labD = lab' :=
    eq_of_ggLabelIso_of_dFourTag (hrigid labD lab' _ hlabD hlab' hHasD hHas') ⟨hJprop.1, hJprop.2.1⟩
  have ht' : lab'.tag = .D := by rw [← hEqD]; exact hJprop.1
  have hmarkDeg' : markDeg lab' = lab'.n := by
    obtain ⟨t, l, n⟩ := lab'
    cases ht'
    rfl
  have hdegD : 2 ^ labD.n = (2 ^ labSL.n) ^ m := by
    rw [hmarkDeg', ← hEqD] at hdeg'
    exact hdeg'
  have hpow : 2 ^ labD.n = 2 ^ (labSL.n * m) := by
    rw [hdegD, pow_mul]
  have hnat : labD.n = labSL.n * m :=
    Nat.pow_right_injective (a := 2) (by norm_num) hpow
  have hevenD : Even labD.n := by
    rw [hnat]
    exact Even.mul_right hevenSL m
  exact (Nat.not_even_iff_odd.mpr hJprop.2.2) hevenD


end CFSG.StandardType.TablePThreeKG

end
