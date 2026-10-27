module

public import CFSG.RankThree.PartOne.Mult.PPart
public import CFSG.RankThree.PartOne.S11c.Sec68
public import CFSG.Adapters.TauCetiExceptional.EvenAll
public import CFSG.RankThree.Chevalley.SmallReeCentralExtension
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.TitsCover

public section

namespace CFSG.RankThree.PartOne.Mult

open CFSG CFSG.Blueprint CFSG.Blueprint.Multiplier CFSG.Assembly.LowTwoRank Subgroup TauCeti
  CFSG.RankThree.PartOne

theorem exists_index_of_chevalley (hB : CFSG.TauCetiBridge.Even.ChevalleyBridgesAll) {X : Type}
    [Group X] {t : StatedLieTag} {p f : ℕ} (hp : p.Prime) (ht : t ∈ chevalleyExceptionalTags)
    (h : ChevalleyExceptionalModel X t p f) :
    ∃ d : ValidLieTypeIndex, CFSG.Models.NamesTag d.1 t p f ∧ Nonempty (X ≃* d.Group) := by
  obtain ⟨hadm, hm⟩ := h
  have hf : 1 ≤ f := hadm.2.1
  let q : PrimePower := ⟨p, f, hp, hf⟩
  have hq : q.card = p ^ f := PrimePower.card_def q
  cases t <;> simp only [chevalleyExceptionalTags, Finset.mem_insert,
    Finset.mem_singleton, reduceCtorEq, or_false, false_or] at ht
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hm
    have hv : (LieTypeIndex.G2 q).Valid := by
      refine (LieTypeIndex.valid_iff _).2 ⟨?_, ?_⟩
      · simpa [LieTypeIndex.inStandardRange_iff, hq] using hadm.2.2.2
      · simp [LieTypeIndex.isDuplicateRepresentative_iff]
    obtain ⟨b⟩ := hB.g2 q hv K (by rw [hK, hq])
    exact ⟨⟨_, hv⟩, ⟨rfl, rfl⟩, ⟨e.trans b⟩⟩
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hm
    have hv : (LieTypeIndex.F4 q).Valid := by simp
    obtain ⟨b⟩ := hB.f4 q hv K (by rw [hK, hq])
    exact ⟨⟨_, hv⟩, ⟨rfl, rfl⟩, ⟨e.trans b⟩⟩
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hm
    have hv : (LieTypeIndex.E6 q).Valid := by simp
    obtain ⟨b⟩ := hB.e6 q hv K (by rw [hK, hq])
    exact ⟨⟨_, hv⟩, ⟨rfl, rfl⟩, ⟨e.trans b⟩⟩
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hm
    have hv : (LieTypeIndex.E7 q).Valid := by simp
    obtain ⟨b⟩ := hB.e7 q hv K (by rw [hK, hq])
    exact ⟨⟨_, hv⟩, ⟨rfl, rfl⟩, ⟨e.trans b⟩⟩
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hm
    have hv : (LieTypeIndex.E8 q).Valid := by simp
    obtain ⟨b⟩ := hB.e8 q hv K (by rw [hK, hq])
    exact ⟨⟨_, hv⟩, ⟨rfl, rfl⟩, ⟨e.trans b⟩⟩
  · obtain ⟨K, _, _, hK, σ, hσ, ⟨e⟩⟩ := hm
    have hv : (LieTypeIndex.twistedE6 q).Valid := by simp
    obtain ⟨b⟩ := hB.twistedE6 q hv K (by rw [hK, hq]) σ (fun x => by rw [hq]; exact hσ x)
    exact ⟨⟨_, hv⟩, ⟨rfl, rfl⟩, ⟨e.trans b⟩⟩
  · obtain ⟨K, _, _, hK, σ, hσ, ⟨e⟩⟩ := hm
    have hv : (LieTypeIndex.trialityD4 q).Valid := by simp
    obtain ⟨b⟩ := hB.trialityD4 q hv K (by rw [hK, hq]) σ (fun x => by rw [hq]; exact hσ x)
    exact ⟨⟨_, hv⟩, ⟨rfl, rfl⟩, ⟨e.trans b⟩⟩

theorem card_center_dvd_of_lieModel
    (hGA : CFSG.Open.GriessAllModelsStatement)
    {K : Type} [Group K] [Finite K] (hK : CFSG.IsQuasisimple K) {t : StatedLieTag}
    {n ℓ f : ℕ} (hm : Models.LieModel (K ⧸ Subgroup.center K) t n ℓ f) :
    Nat.card (Subgroup.center K) ∣ ((genericOrders t n ℓ f).1 * (genericOrders t n ℓ f).2) *
      ((exceptionalOrders t n ℓ f).1 * (exceptionalOrders t n ℓ f).2) := by
  have : Group.IsPerfect K := hK.1
  obtain ⟨-, ⟨e⟩⟩ := hGA _ t n ℓ f hm
  have h1 := ComponentClassification.FooteLit.card_center_dvd_card_hopfMultiplier (Q := K)
    (MulEquiv.refl (K ⧸ Subgroup.center K))
  rw [Nat.card_congr (RankThree.PerfectCover.hopfMultiplierEquivGriess _).symm.toEquiv,
    Nat.card_congr e.toEquiv, card_generic_exceptional] at h1
  exact h1

open CFSG.SectionRank in
theorem exceptionalCenterSmallPrimes_of_griess
    (hGA : CFSG.Open.GriessAllModelsStatement) :
    ExceptionalCenterSmallPrimes := by
  intro K _ _ hK hrep p hp hp3 hpZ
  have : Fact p.Prime := ⟨hp⟩
  have : Group.IsPerfect K := hK.1
  rcases hrep with ⟨t, ℓ, d, ht, hM⟩ | ⟨t, ℓ, d, ht, hM⟩ | ⟨ℓ, d, hM⟩
  · obtain ⟨dd, hdd, he⟩ := exists_index_of_chevalley
      CFSG.TauCetiBridge.Even.chevalleyBridgesAll hM.1.1 ht hM
    have hm : Models.LieModel (K ⧸ Subgroup.center K) t 0 ℓ d :=
      ⟨hM.1, Or.inr ⟨rfl, dd, hdd, he⟩⟩
    have hdvd := card_center_dvd_of_lieModel hGA hK hm
    rcases prime_dvd_table hp hp3 (hpZ.trans hdvd) with ⟨rfl, -, -⟩ | ⟨rfl, -, -⟩ <;>
      simp [chevalleyExceptionalTags] at ht
  all_goals
    obtain ⟨N, hNn, π, hperf, -, hsurj, hker, hpg, hne⟩ := exists_central_p_extension (K := K) hpZ
    have : Group.IsPerfect (K ⧸ N) := hperf
    have hcop := coprime_six_card_of_isPGroup hp hp3 hpg
    have hodd := odd_card_of_isPGroup hp hp3 hpg
    have key : ∀ {T : Type} [Group T] (e : K ⧸ center K ≃* T),
        (∀ π' : K ⧸ N →* T, Function.Surjective π' → π'.ker ≤ center (K ⧸ N) →
          Odd (Nat.card π'.ker) → π'.ker = ⊥) → False := by
      intro T _ e htriv
      have hker' : (e.toMonoidHom.comp π).ker = π.ker := by
        ext x
        simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
          MulEquiv.map_eq_one_iff]
      have h := htriv (e.toMonoidHom.comp π) (e.surjective.comp hsurj) (by rw [hker']; exact hker)
        (by rw [hker']; exact hodd)
      exact hne (by rw [← hker']; exact h)
  · have ht' : t ∈ reeTitsTags := ht
    simp only [reeTitsTags, Finset.mem_insert, Finset.mem_singleton] at ht'
    rcases ht' with rfl | rfl | rfl
    · exact hne (CFSG.RankThree.Chevalley.small_Ree_model_central_kernel_trivial _ ℓ d hM π hsurj
        hker hcop)
    · obtain ⟨F, _, _, _, a, ha, hF, ⟨e⟩⟩ := exists_mulEquiv_reeFixed_of_model hM
      exact key e fun π' h1 h2 h3 =>
        LargeRee.large_ree_perfect_odd_cover_trivial_of_suzuki LargeRee.suzukiBlockInputs ha hF
          π' h1 h2 h3
    · obtain ⟨F, _, _, _, hF, ⟨e⟩⟩ := exists_mulEquiv_titsGroup_of_model hM
      exact key e fun π' h1 h2 h3 => Tits_perfect_odd_cover_trivial hF π' h1 h2 h3
  · obtain ⟨a, ha, ⟨e⟩⟩ :=
      CFSG.LieType.Simplicity.exists_mulEquiv_suzukiMatrixGroup_of_suzukiModel hM
    exact key e fun π' h1 h2 h3 => suzuki_perfect_odd_cover_trivial a (by omega) π' h1 h2 h3

end CFSG.RankThree.PartOne.Mult
