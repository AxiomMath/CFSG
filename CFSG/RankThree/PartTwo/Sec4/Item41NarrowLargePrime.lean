module

public import CFSG.RankThree.PartTwo.Sec4.Item41Narrow
public import CFSG.RankThree.OddKernel.CentralFailureExceptional
public import CFSG.RankThree.PartOne.TCB.Final
public import CFSG.RankThree.PartOne.KP.BExclusion
public import CFSG.RankThree.PartOne.KP.Fi22Section
public import CFSG.RankThree.PartOne.KP.MSectionMonster
public import CFSG.RankThree.PartOne.KS.FischerSections
public import CFSG.RankThree.PartOne.MultRes.Trim
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item41Narrow

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.ComponentClassification.TBLit (GriessMultipliersAllModels)

theorem exists_section_of_quotient {W V T : Type} [Group W] [Group V] [Group T] (π : W →* V)
    (hπ : Function.Surjective π) (K : Subgroup V) (ψ : K →* T) (hψ : Function.Surjective ψ) :
    ∃ (H' : Subgroup W) (N' : Subgroup H') (_ : N'.Normal), Nonempty (H' ⧸ N' ≃* T) := by
  let H' : Subgroup W := K.comap π
  let ρ : H' →* K := (π.comp H'.subtype).codRestrict K fun x => x.2
  have hρ : Function.Surjective ρ := by
    rintro ⟨v, hv⟩
    obtain ⟨w, rfl⟩ := hπ v
    exact ⟨⟨w, hv⟩, rfl⟩
  exact ⟨H', (ψ.comp ρ).ker, inferInstance,
    ⟨QuotientGroup.quotientKerEquivOfSurjective _ (hψ.comp hρ)⟩⟩

theorem exists_isComponent {Y : Type*} [Group Y] (hE : layer Y = ⊤) {A : Subgroup Y}
    (hA : A ≠ ⊥) : ∃ K : Subgroup Y, IsComponent K := by
  by_contra h
  push Not at h
  have hbot : layer Y = ⊥ := sSup_eq_bot.mpr fun K hK => absurd hK (h K)
  exact hA (eq_bot_iff.mpr ((le_top : A ≤ ⊤).trans (hE.symm.trans hbot).le))

theorem four_le_evenRank_of_sporadic
    {W V : Type} [Group W] [Finite W] [Group V] [Finite V] (π : W →* V)
    (hπ : Function.Surjective π) {K : Subgroup V} (hK : IsQuasisimple K) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hpZ : p ∣ Nat.card (Subgroup.center K)) {s : TauCeti.SporadicName}
    (e : K ⧸ Subgroup.center K ≃* Blueprint.NativeSporadic.Carrier s) :
    4 ≤ CFSG.Assembly.evenRank W := by
  have : Group.IsPerfect K := hK.1
  obtain ⟨hpair, hnot⟩ := PartOne.Mult.sporadic_residual_of_center e hp hp3 hpZ
  by_cases hexc : PartOne.Mult.SectionExcluded s
  · obtain ⟨H', N', _, ⟨f⟩⟩ := exists_section_of_quotient π hπ K
      (QuotientGroup.mk' (Subgroup.center K)) (QuotientGroup.mk'_surjective _)
    have h2224 := PartOne.sectionsForceEvenRankFour_fi23_fi24prime
      PartOne.sectionsForceEvenRankFour_Fi22 PartOne.hasSection_fi23_fi22
      PartOne.hasSection_fi24prime_fi23
    rcases hexc with rfl | rfl | rfl | rfl | rfl
    · exact PartOne.sectionsForceEvenRankFour_Fi22 W H' N' ⟨f.trans e⟩
    · exact h2224.1 W H' N' ⟨f.trans e⟩
    · exact h2224.2 W H' N' ⟨f.trans e⟩
    · exact PartOne.sectionsForceEvenRankFour_B W H' N' ⟨f.trans e⟩
    · have : IsSimpleGroup (K ⧸ Subgroup.center K) := hK.2.1
      exact PartOne.simplePresentationM_sections_of_B_section PartOne.sectionsForceEvenRankFour_B
        PartOne.simplePresentationMHasBSection_holds W H' N' (K ⧸ Subgroup.center K) hK.2.2 ⟨f⟩
        ⟨e⟩
  · exact (hnot (PartOne.MultRes.sporadicResidualKernelsTrim_holds.trivial_of_pair hexc
      hpair)).elim

theorem item4_1LargePrime_of_griess
    (hGA : GriessMultipliersAllModels) : Item4_1LargePrime := by
  intro G _ _ hG H N _ _ hq p hp hp3 _
  by_contra hlt
  have hfail : 2 < localRank p (H ⧸ N) := by omega
  have hK : CFSG.SectionRank.IsKGroupCat G :=
    PartOne.TCB.tcKGroupBridge G fun A B _ _ hs _ => hG.kGroup A (B.subgroupOf A) hs
  have he : CFSG.twoLocalOddRank G ≤ 3 := Census.SectionFourHyp.twoLocalOddRank_le hG
  have hr : ∀ r : ℕ, r.Prime → 3 < r → localRank r G ≤ 2 := fun r hr hr3 => by
    have := hG.localRank_lt r hr hr3
    omega
  have hS : layer (H ⧸ N) = ⊤ := CFSG.RankThree.Coprime.layer_eq_top_of_isQuasisimple hq
  classical
  have hex : ∃ n, ∃ U : Subgroup H, U.map (QuotientGroup.mk' N) = ⊤ ∧ Nat.card U = n :=
    ⟨_, ⊤, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N), rfl⟩
  obtain ⟨X, hXS, hXn⟩ := Nat.find_spec hex
  have hXmin : ∀ U : Subgroup H, U.map (QuotientGroup.mk' N) = ⊤ → Nat.card X ≤ Nat.card U :=
    fun U hU => by
      rw [hXn]
      exact Nat.find_min' hex ⟨U, hU, rfl⟩
  obtain ⟨_, _, _, f, -, -, -, hA, -, -, -, hEY, -, hcomp⟩ :=
    OddKernel.original_central_failure_components hK he hr H N hS hp hp3 (Or.inl hfail) X hXS
      hXmin
  obtain ⟨_, _, _, -, -, -, -, -, -, -, -, halt, -⟩ :=
    OddKernel.original_central_failure_excludes_Ree_Suzuki_and_twelve_sporadic_components hK he
      hr H N hS hp hp3 (Or.inl hfail) X hXS hXmin
  obtain ⟨K, hKc⟩ := exists_isComponent hEY hA
  obtain ⟨hZ, hZp, -⟩ := hcomp K hKc
  have hpZ : p ∣ Nat.card (Subgroup.center K) := by
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨k, hk⟩ := hZp.exists_card_eq
    rcases k with _ | k
    · rw [pow_zero] at hk
      exact absurd (Subgroup.card_eq_one.mp hk) hZ
    · rw [hk]
      exact dvd_pow_self p k.succ_ne_zero
  have heX : CFSG.Assembly.evenRank X ≤ 3 :=
    (evenRank_subgroup_le X).trans ((evenRank_subgroup_le H).trans hG.evenRank_le)
  rcases (halt K hKc).1 with ⟨τ, hτ, ℓ, d, -, -, hM, -⟩ |
      (⟨s, -, ⟨e⟩, -⟩ | ⟨s, -, ⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩) | hMs
  · exact PartOne.Mult.exceptionalCenterSmallPrimes_of_griess hGA K hKc.1
      (Or.inl ⟨τ, ℓ, d, hτ, hM⟩) p hp hp3 hpZ
  · have := four_le_evenRank_of_sporadic (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
      hKc.1 hp hp3 hpZ e
    omega
  · have := four_le_evenRank_of_sporadic (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
      hKc.1 hp hp3 hpZ e
    omega
  · have := four_le_evenRank_of_sporadic (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
      hKc.1 hp hp3 hpZ e
    omega
  · obtain ⟨e⟩ := hMs
    have := four_le_evenRank_of_sporadic (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
      hKc.1 hp hp3 hpZ e
    omega

end CFSG.RankThree.PartTwo.Sec4.Item41Narrow
