module

public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.LocalAnalysis.UniquenessCase.UC22DataExt
public import CFSG.LocalAnalysis.StronglyEmbedded.Normalizer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

@[expose] def SigmaThree (D : Data G) : Prop :=
  CFSG.Open.evenRank G = 3 → D.sig ⊆ CFSG.Open.rankThreeSigmaA G

theorem evenRank_eq_three (D : Data G) (hx : DataExt D) (hsig : D.sig = {3})
    (hm3 : CFSG.Open.pRank 3 D.M = 3) : CFSG.Open.evenRank G = 3 := by
  refine le_antisymm ?_ ?_
  · by_contra h
    push Not at h
    have hmem : 3 ∈ D.sig := by rw [hsig]; exact Set.mem_singleton 3
    have h4 : 4 ≤ CFSG.Open.pRank 3 D.M := hx.four_le h 3 hmem
    omega
  · have h := CFSG.RankThreeCoreUniqueness.Helpers.local_pRank_le_evenRank 3 Nat.prime_three
      (by norm_num) D.M D.maxLocal.1
    omega

private theorem s16c1_rankThreeLocalRank_lt_three (hrank : CFSG.Open.evenRank G = 3)
    (h3 : 3 ∈ CFSG.Open.rankThreeSigmaA G) {q : ℕ} (hq : q.Prime) (hq3 : 3 < q) :
    CFSG.Open.rankThreeLocalRank q G < 3 := by
  classical
  by_contra hlt
  push Not at hlt
  have hupper := CFSG.RankThreeCoreUniqueness.Helpers.rankThreeLocalRank_le_evenRank
    (G := G) q hq (by omega)
  have hupper3 := CFSG.RankThreeCoreUniqueness.Helpers.rankThreeLocalRank_le_evenRank
    (G := G) 3 Nat.prime_three (by norm_num)
  have hq_eq : CFSG.Open.rankThreeLocalRank q G = 3 := by omega
  obtain ⟨H, -, hHrank⟩ :=
    CFSG.RankThreeCoreUniqueness.Helpers.rankThreeLocalRank_attained (G := G) q (by omega)
  have hqdvd : q ∣ Nat.card G :=
    CFSG.RankThreeCoreUniqueness.Helpers.prime_dvd_card_of_pRank_pos q H (by omega)
  have hS3 : ({p : ℕ | p.Prime ∧ 3 < p ∧ p ∣ Nat.card G ∧
      CFSG.Open.rankThreeLocalRank p G = 3}).Nonempty :=
    ⟨q, hq, hq3, hqdvd, hq_eq⟩
  dsimp only [CFSG.Open.rankThreeSigmaA] at h3
  split_ifs at h3
  · exact absurd h3.2.2.2 (by omega)
  · exact absurd h3.2.1 (by norm_num)
  · exact absurd h3.2.1 (by norm_num)

theorem pRank_le_two_of_twoLocal (D : Data G) (hx : DataExt D) (hσ3 : SigmaThree D)
    (hsig : D.sig = {3}) (hm3 : CFSG.Open.pRank 3 D.M = 3) {q : ℕ} (hq : q.Prime) (hq3 : 3 < q)
    {H : Subgroup G} (hH : CFSG.Open.IsTwoLocal H) : CFSG.Open.pRank q H ≤ 2 := by
  have he : CFSG.Open.evenRank G = 3 := evenRank_eq_three D hx hsig hm3
  have hsig3 : 3 ∈ D.sig := by rw [hsig]; exact Set.mem_singleton 3
  have h3mem : 3 ∈ CFSG.Open.rankThreeSigmaA G := hσ3 he hsig3
  have hlt : CFSG.Open.rankThreeLocalRank q G < 3 :=
    s16c1_rankThreeLocalRank_lt_three he h3mem hq hq3
  have hle : CFSG.Open.pRank q H ≤ CFSG.Open.rankThreeLocalRank q G :=
    CFSG.RankThreeCoreUniqueness.Helpers.local_pRank_le_localRank q hq.one_lt H hH
  omega

theorem isStronglyPEmbedded_three (D : Data G) (hSg : UC6S846.SigmaStd D)
    (h1219 : D.sig = D.sig1) (hsig : D.sig = {3}) : IsStronglyPEmbedded 3 D.M :=
  hSg.sig1_sp 3 (by rw [← h1219, hsig]; exact Set.mem_singleton 3)

theorem pRank_three_centralizer (D : Data G) (h61 : UC6.R6_1 D) (hsig : 3 ∈ D.sig)
    (hse : IsStronglyPEmbedded 3 D.M) {z : G} (hz : z ≠ 1) (hz2 : ∃ n : ℕ, z ^ (2 ^ n) = 1)
    (hnot : ¬ centralizer ({z} : Set G) ≤ D.M)
    (h3 : 1 ≤ CFSG.Open.pRank 3 (D.M ⊓ centralizer ({z} : Set G))) :
    CFSG.Open.pRank 3 (centralizer ({z} : Set G)) = 1 := by
  classical
  let C : Subgroup G := centralizer ({z} : Set G)
  change CFSG.Open.pRank 3 C = 1
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E0, hE0le, hE0ea, hE0card⟩ :=
    CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) (D.M ⊓ C)
  have hE0ne : E0 ≠ ⊥ := by
    intro hbot
    have hpow : 3 ≤ Nat.card E0 := by
      have hpow' := pow_le_pow_right₀ (show (1 : ℕ) ≤ 3 by norm_num) h3
      rw [pow_one, ← hE0card] at hpow'
      exact hpow'
    rw [hbot, Subgroup.card_bot] at hpow
    omega
  have hE0C : E0 ≤ C := hE0le.trans inf_le_right
  have hE0M : E0 ≤ D.M := hE0le.trans inf_le_left
  obtain ⟨P₁, hP₁le⟩ := (hE0ea.subgroupOf C).isPGroup.exists_le_sylow
  let P₁' : Subgroup G := (P₁ : Subgroup C).map C.subtype
  have hE0_le_P₁' : E0 ≤ P₁' := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hE0C]
    exact Subgroup.map_mono hP₁le
  have hP₁'group : IsPGroup 3 P₁' := P₁.isPGroup'.map C.subtype
  have hP₁'C : P₁' ≤ C := Subgroup.map_subtype_le (P₁ : Subgroup C)
  have hP₁'M : P₁' ≤ D.M := by
    refine hse.le_of_isPGroup_inf hP₁'group ?_
    intro hbot
    have hle : E0 ≤ (⊥ : Subgroup G) := hbot ▸ le_inf hE0_le_P₁' hE0M
    exact hE0ne (le_bot_iff.mp hle)
  have hP₁'cyc : IsCyclic P₁' := by
    by_contra hcyc
    exact hnot (centralizer_le_of_noncyclic D h61 hsig hP₁'M hP₁'group hcyc hz hz2 hP₁'C)
  have hlower : 1 ≤ CFSG.Open.pRank 3 C :=
    h3.trans (CFSG.SectionRank.pRank_mono (by norm_num : 1 < 3) inf_le_right)
  refine le_antisymm ?_ hlower
  apply CFSG.SectionRank.pRank_le (by norm_num : 1 < 3)
  intro A hAC hAea
  obtain ⟨P₂, hP₂le⟩ := (hAea.subgroupOf C).isPGroup.exists_le_sylow
  haveI : IsCyclic (P₁ : Subgroup C) := by
    haveI : IsCyclic ((P₁ : Subgroup C).map C.subtype) := hP₁'cyc
    exact isCyclic_of_surjective
      (Subgroup.equivMapOfInjective (P₁ : Subgroup C) C.subtype C.subtype_injective).symm
      (Subgroup.equivMapOfInjective (P₁ : Subgroup C) C.subtype
        C.subtype_injective).symm.surjective
  have hP₂cyc : IsCyclic (P₂ : Subgroup C) :=
    isCyclic_of_surjective (Sylow.equiv P₁ P₂) (Sylow.equiv P₁ P₂).surjective
  have hAcyc_sub : IsCyclic (A.subgroupOf C) := by
    haveI : IsCyclic (P₂ : Subgroup C) := hP₂cyc
    exact Subgroup.isCyclic_of_le hP₂le
  have hAcyc : IsCyclic A := by
    haveI : IsCyclic (A.subgroupOf C) := hAcyc_sub
    exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hAC)
      (Subgroup.subgroupOfEquivOfLe hAC).surjective
  haveI : IsCyclic A := hAcyc
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := A)
  have hg3 : g ^ 3 = 1 := Subtype.ext (hAea.2 g g.2)
  have hcard : Nat.card A = orderOf g := (orderOf_eq_card_of_forall_mem_zpowers hg).symm
  have hle : orderOf g ≤ 3 := by
    refine Nat.le_of_dvd (by norm_num) ?_
    exact orderOf_dvd_iff_pow_eq_one.mpr hg3
  have hA3 : Nat.card A ≤ 3 := by omega
  simpa using hA3

theorem exists_pGroup_map_eq {p : ℕ} [Fact p.Prime] {M M' : Type*} [Group M] [Group M'] [Finite M]
    (f : M →* M') (E : Subgroup M') (hE : IsPGroup p E) (hEf : E ≤ f.range) :
    ∃ P : Subgroup M, IsPGroup p P ∧ P.map f = E := by
  classical
  let W : Subgroup M := E.comap f
  let ψ : W →* E := (f.comp W.subtype).codRestrict E fun w => w.2
  have hψ : Function.Surjective ψ := by
    rintro ⟨q, hq⟩
    obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp (hEf hq)
    exact ⟨⟨a, show f a ∈ E by rw [ha]; exact hq⟩, Subtype.ext ha⟩
  obtain ⟨T, -⟩ := (IsPGroup.of_bot : IsPGroup p (⊥ : Subgroup W)).exists_le_sylow
  have htop : ((T.mapSurjective hψ : Sylow p E) : Subgroup E) = ⊤ :=
    ((T.mapSurjective hψ).is_maximal' (hE.to_subgroup ⊤) le_top).symm
  rw [Sylow.coe_mapSurjective] at htop
  refine ⟨(T : Subgroup W).map W.subtype, T.isPGroup'.map W.subtype, le_antisymm ?_ ?_⟩
  · rintro _ ⟨_, ⟨w, -, rfl⟩, rfl⟩
    exact w.2
  · intro q hq
    obtain ⟨w, hw, hwq⟩ : (⟨q, hq⟩ : E) ∈ (T : Subgroup W).map ψ := by
      rw [htop]
      exact Subgroup.mem_top _
    exact ⟨w, ⟨w, hw, rfl⟩, congrArg Subtype.val hwq⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
