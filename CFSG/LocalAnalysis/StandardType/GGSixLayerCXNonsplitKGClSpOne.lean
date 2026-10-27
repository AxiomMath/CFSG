module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGClSpNbr
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.RootSp2

public section

namespace CFSG.StandardType

namespace ClNonsplit

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LieType.Universal Matrix

theorem linearRecipeLabel_of_markTag_PSL {lab : LargeEvenLabel} (hT : markTag lab = .PSL)
    (hc : markChar lab = 2) : GGLinearRecipeLabel lab := by
  obtain ⟨t, l, n⟩ := lab
  cases t <;> simp only [markTag, markChar] at hT hc
  all_goals first
    | exact Or.inl rfl
    | exact absurd hc (by decide)
    | (simp at hT; done)
    | (by_cases h3 : l = 3
       · exact Or.inr (Or.inl ⟨rfl, h3⟩)
       · simp [h3] at hT)
    | (by_cases h2 : l = 2
       · exact Or.inr (Or.inr ⟨rfl, h2⟩)
       · by_cases h3 : l = 3 <;> simp [h2, h3] at hT)

section Main

theorem not_ggNbrClauseFiveMarking_sl_two {G : Type} [Group G] {f : ℕ} {F' : Type} [Field F']
    [Finite F'] (hF' : Nat.card F' = 2 ^ f) (hf2 : 2 ≤ f)
    (ψ' : SpecialLinearGroup (Fin (1 + 1)) F' →* G)
    (hker : ψ'.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (1 + 1)) F')) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hq1 : ¬ p ∣ 2 ^ f - 1) (hq2 : ¬ p ∣ 2 ^ f + 1) {x : G}
    (hinn : ∃ k ∈ ψ'.range, ∀ l ∈ ψ'.range, x⁻¹ * l * x = k⁻¹ * l * k) :
    ¬ GGNbrClauseFiveMarking p x ψ'.range := by
  have : CharP F' 2 := CFSG.SeitzReduction.LinearPilot.charP_two_of_card_eq_two_pow hF'
  have hp3 : p ≠ 3 := LinNonsplit.ne_three_of_not_dvd hq1 hq2
  have hf : 1 ≤ f := by omega
  have h4 : 4 ≤ Nat.card F' := by
    rw [hF']
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
  have hgood : 3 ≤ 1 + 1 ∨ ∃ s : Finset F', s.card = 4 := by
    right
    have := Fintype.ofFinite F'
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F')) (n := 4)
      (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact h4)
    exact ⟨s, hs⟩
  have hperf : commutator (SpecialLinearGroup (Fin (1 + 1)) F') = ⊤ :=
    Group.isPerfect_def.mp (CFSG.RankThree.PartOne.KCUnitary.isQuasisimple_SL (by omega) hgood).1
  have hadm : StatedLieAdmissible .PSL (1 + 1) 2 f := by
    refine ⟨Nat.prime_two, hf, by omega, fun h => ?_, fun h => ?_⟩
    · simp only [Prod.mk.injEq] at h
      have : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
      omega
    · simp only [Prod.mk.injEq] at h
      exact two_pow_ne_three f h.2
  have hL := LinNonsplit.lieModel_range_sl hF' hadm hperf ψ' hker
  have hdet : ∀ lab : LargeEvenLabel, markChar lab = 2 →
      MarkedModel lab (↥ψ'.range ⧸ Subgroup.center ↥ψ'.range) →
        markTag lab = .PSL ∧ markRank lab = 1 + 1 ∧ markDeg lab = f := by
    intro lab hc hX
    have hX' : LieModel (↥ψ'.range ⧸ Subgroup.center ↥ψ'.range) (markTag lab) (markRank lab) 2
        (markDeg lab) := by
      have h := hX
      unfold MarkedModel at h
      rwa [hc] at h
    exact CFSG.SeitzReduction.RankOne.sl2EvenTypeDet _ f _ _ _ hL
      (CFSG.SeitzReduction.F4Pilot.statedLieAdmissible_of_lieModel hX') hX'
  refine not_ggNbrClauseFiveMarking_of_inner hp hp3 hinn (fun lab _ hc hX hHS => ?_)
    (fun lab hlab hc hX => ?_)
  · obtain ⟨hT, -, hD⟩ := hdet lab hc hX
    obtain ⟨hf1, -⟩ := LinNonsplit.eq_seven_of_halfSplit_markPSL hp3 hT hc hD hHS hq1 hq2
    omega
  · obtain ⟨hT, -, -⟩ := hdet lab hc hX
    exact ggRawInnFieldOn_linear p hp hp2 lab hlab (linearRecipeLabel_of_markTag_PSL hT hc)

theorem ggNonsplitNbrSpOneInput_holds : GGNonsplitNbrSpOneInput := by
  intro G _ _ K' f F' _ _ hF' hf2 ⟨e⟩ p hp hp2 hq1 hq2 x hinn
  set ψ' : SpecialLinearGroup (Fin (1 + 1)) F' →* G :=
    K'.subtype.comp (e.symm.toMonoidHom.comp
      (CFSG.ClassicalInvolution.Models.SymplecticPairs.longBlockEquivOne F').toMonoidHom)
    with hψ'
  have hinj : Function.Injective ψ' :=
    (Subgroup.subtype_injective K').comp (e.symm.injective.comp
      (CFSG.ClassicalInvolution.Models.SymplecticPairs.longBlockEquivOne F').injective)
  have hrange : ψ'.range = K' := by
    ext k
    constructor
    · rintro ⟨g, rfl⟩
      exact (e.symm _).2
    · intro hk
      refine ⟨(CFSG.ClassicalInvolution.Models.SymplecticPairs.longBlockEquivOne F').symm
        (e ⟨k, hk⟩), ?_⟩
      simp [hψ']
  have hker : ψ'.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (1 + 1)) F') := by
    rw [(MonoidHom.ker_eq_bot_iff ψ').mpr hinj]
    exact bot_le
  have h := not_ggNbrClauseFiveMarking_sl_two hF' hf2 ψ' hker hp hp2 hq1 hq2 (hrange ▸ hinn)
  rwa [hrange] at h

end Main

end ClNonsplit

section Tag

theorem ggNonsplitTag_PSp_of_altSix (hA6 : ClNonsplit.GGNonsplitNbrAltSixInput) :
    GGNonsplitTag .PSp :=
  ggNonsplitTag_PSp ClNonsplit.ggNonsplitNbrSpOneInput_holds hA6

end Tag

end CFSG.StandardType
