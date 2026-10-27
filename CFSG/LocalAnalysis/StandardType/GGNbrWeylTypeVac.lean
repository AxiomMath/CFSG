module

public import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitFamilies
import CFSG.FeitThompson.OddOrderTheorem
import CFSG.LocalAnalysis.StandardType.GGNbrLangWeylRestVac
import CFSG.LocalAnalysis.StandardType.GGCorFourTwoRestSmall
import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRanks
import CFSG.LocalAnalysis.StandardType.GGTwF4SUThreeRank
import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBVac
import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrSmallRank
import CFSG.LocalAnalysis.StandardType.GGNbrTableBExcInduced
import CFSG.LocalAnalysis.StandardType.GGTableBTypeATorus
import Certificates.Certificate8032

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

private theorem ggWTVac_two_dvd_natCard_of_isSimpleGroup {R : Type} [Group R]
    (hs : IsSimpleGroup R) (hna : ∃ a b : R, a * b ≠ b * a) : 2 ∣ Nat.card R := by
  rcases finite_or_infinite R with hR | hR
  · obtain ⟨a, b, hab⟩ := hna
    by_contra h2
    have hodd : Odd (Nat.card R) := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h2)
    exact hab ((IsSimpleGroup.comm_iff_isSolvable).2 (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd) a b)
  · rw [Nat.card_eq_zero_of_infinite]
    exact dvd_zero 2

private theorem ggWTVac_ggTorusWeylTypeW_of_card_lt {p r : ℕ} {R : Type} [Group R]
    {I : Set (MulAut R)}
    (hX : ∀ X : Subgroup (MulAut R), (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X →
      Nat.card X < p ^ 3) : GGTorusWeylTypeW p r R I := by
  classical
  intro L' _ _ ψ A hA
  obtain ⟨hψ, hker, hperf, hAe, hAI, -, h3, -⟩ := hA
  exfalso
  have hXA : IsElemAbelian p (TypeA.inducedSub ψ A) := TypeA.isElemAbelian_inducedSub hψ hAe
  have hXI : ((TypeA.inducedSub ψ A : Subgroup (MulAut R)) : Set (MulAut R)) ⊆ I := by
    rintro x ⟨a, ha, hxa⟩
    obtain ⟨φa, hφaI, hφa⟩ := hAI a ha
    exact TypeA.induced_unique ψ hψ hφa hxa ▸ hφaI
  have hcardX : Nat.card (TypeA.inducedSub ψ A) = Nat.card A :=
    TypeA.card_inducedSub hψ hker hperf (fun a ha => by
      obtain ⟨φa, -, hφa⟩ := hAI a ha
      exact ⟨φa, hφa⟩)
  have hlt := hX _ hXI hXA
  rw [hcardX] at hlt
  omega

private theorem ggWTVac_largeEvenLabelAll_weylTypeNonSplit_of_card_lt {p : ℕ}
    {lab : LargeEvenLabel}
    (h : LargeEvenLabelAll lab fun R _ I _ => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      ∀ X : Subgroup (MulAut R), (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X →
        Nat.card X < p ^ 3) :
    LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ =>
      ∃ r, GGTorusLift p r R ∧ GGTorusWeylTypeW p r R I) :=
  h.mono fun _ _ _ _ hX hs hna =>
    ⟨0, TypeA.ggTorusLift_zero (ggWTVac_two_dvd_natCard_of_isSimpleGroup hs hna),
      ggWTVac_ggTorusWeylTypeW_of_card_lt (hX hs hna)⟩

private theorem ggWTVac_not_dvd_sub_of_nonSplit {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGNbrNonSplitLabel p lab)
    (hu : LargeEvenUntwisted lab.tag) : ¬ p ∣ 2 ^ lab.n - 1 := fun hd => by
  rcases Nat.lt_or_ge lab.n 2 with h2 | h2
  · have hn : lab.n = 1 := by have := hlab.1; omega
    rw [hn] at hd
    exact hp.ne_one (Nat.dvd_one.mp (by simpa using hd))
  · exact h.2.2.1 ⟨hu, h2, hd⟩

private theorem ggWTVac_largeEvenSplit_of_halfSplit_twF4 {p : ℕ} {lab : LargeEvenLabel}
    (ht : lab.tag = .twF4) (h : LargeEvenHalfSplit p lab True) : LargeEvenSplit p lab := by
  rcases h with h | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · exact h
  all_goals simp [ht] at h

theorem ggNbrTableBWeylTypeNonSplitOn_vac :
       GGNbrTableBWeylTypeNonSplitOn GGNbrNonSplitVacLabel := by
  intro p hp hp2 lab hlab hV hns
  apply ggWTVac_largeEvenLabelAll_weylTypeNonSplit_of_card_lt
  have hsmall : GGNbrInnerSmallLabel p lab → LargeEvenLabelAll lab fun R _ I _ =>
      IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) → ∀ X : Subgroup (MulAut R),
        (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X → Nat.card X < p ^ 3 :=
    largeEvenLabelAll_card_lt_innerSmall hp hp2 hlab
  have hnine : GGTableBNbrInnerNineSmallLabel p lab → LargeEvenLabelAll lab fun R _ I _ =>
      IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) → ∀ X : Subgroup (MulAut R),
        (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X → Nat.card X < p ^ 3 :=
    fun h => hsmall (Or.inr (Or.inr (Or.inr (Or.inl h))))
  have hguard : ∀ {P : LargeEvenRawCont}, LargeEvenLabelAll lab P →
      LargeEvenLabelAll lab fun R _ I F => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
        P R I F := fun h => h.mono fun _ _ _ _ hP _ _ => hP
  rcases hV with ht | ht | ht | ht | ht | ht | ⟨ht | ht, hr⟩ | ⟨ht, hr, hd⟩ | ⟨ht, hr⟩ |
    ⟨ht, hr⟩ | ⟨ht, hr⟩
  · exact hnine (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ht)))))
  ·
    have hs := ggWTVac_largeEvenSplit_of_halfSplit_twF4 ht hns.1
    by_cases hp3 : p = 3
    · subst hp3
      exact hguard (TableBExcSmallRanks.largeEvenLabelAll_card_lt_twF4_of
        (fun a ha K _ _ _ hK _ E hE => TwF4SUThree.ggTwF4ThreeRankInput_holds a ha K hK E hE)
        hp hlab ht hs)
    · exact hguard
        (TableBExcSmallRanks.largeEvenLabelAll_card_lt_twF4_of_ne_three hp3 hp hlab ht hs)
  · exact hnine (Or.inr (Or.inr (Or.inl ht)))
  · exact hnine (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ht, Or.inr hns.2.1⟩)))))))
  · exact hnine (Or.inr (Or.inr (Or.inr (Or.inl ht))))
  · exact hnine (Or.inr (Or.inl ht))
  · exact hnine (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨ht, hr⟩))))))))
  · exact hguard (largeEvenLabelAll_card_lt_linearTwo hp hp2 hlab (Or.inr ⟨ht, hr⟩))
  ·
    exact hguard (largeEvenLabelAll_card_lt_corFourTwoSmall hp hlab
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ht, hr, hd⟩)))))
      (Or.inr (Or.inr (Or.inl ⟨Or.inl ht, hd⟩))))
  ·
    rcases Nat.lt_or_ge lab.rank 2 with hr1 | hr1
    · exact hguard (largeEvenLabelAll_card_lt_linearTwo hp hp2 hlab
        (Or.inl ⟨ht, by have := hlab.2; simp only [ht] at this; omega⟩))
    · refine hsmall (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl ⟨Or.inl ⟨ht, hr1⟩, fun j hj hj3 => ?_⟩)))))
      have hj1 : j = 1 := by simp only [ht, reduceCtorEq, if_false] at hj3; omega
      subst hj1
      simpa using ggWTVac_not_dvd_sub_of_nonSplit hp hlab hns (by simp [ht, LargeEvenUntwisted])
  ·
    refine hsmall (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inr ⟨ht, hr⟩, fun j hj hj3 => ?_⟩)))))
    have hj1 : j = 1 := by simp only [ht, if_true] at hj3; omega
    subst hj1
    simpa using ggWTVac_not_dvd_sub_of_nonSplit hp hlab hns (by simp [ht, LargeEvenUntwisted])
  · exact hguard (largeEvenLabelAll_card_lt_symplecticTwo hp hp2 hlab ht hr)

end CFSG.StandardType

end
