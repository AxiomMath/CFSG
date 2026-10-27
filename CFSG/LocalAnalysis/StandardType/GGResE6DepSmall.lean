module

public import CFSG.LocalAnalysis.StandardType.GGResE6DepLabels
public import CFSG.LocalAnalysis.StandardType.GGCSRHolds
public import CFSG.LocalAnalysis.StandardType.GGTorusTBGroupCard
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeADvd
public import CFSG.LocalAnalysis.StandardType.GGResE6DepRank
public import CFSG.LocalAnalysis.StandardType.GGNbrLangRestRank
public import CFSG.LocalAnalysis.StandardType.GGL45FixA2Rank

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem GGResHyp.not_rankOneOrTwo_of_gamma_ge_five
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K X : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hX : X = L ∨ X = K)
    (h5 : ∀ (hN : Bs ≤ Subgroup.normalizer (X : Set G)),
      3 ^ 5 ≤ Nat.card ↥(ggGamma X hN).range)
    (hMark : GGInnerDiagOnLabel (fun _ lab => GGLinearTwoLabel lab ∨ GGLabelA2 lab) 3 Bs X) :
    False := by
  obtain ⟨hperf, lab, hΛ, hraw⟩ := hMark
  obtain ⟨R, _, I, F, -, -, θ, htag, -, -⟩ := largeEvenRawDatum_exists hraw
  have hAll : LargeEvenLabelAll lab (fun R _ _ _ => IsSimpleGroup R →
      (∃ a b : R, a * b ≠ b * a) → ∀ A : Subgroup (MulAut R),
        IsElemAbelian 3 A → Nat.card A ≤ 3 ^ 3) := by
    rcases htag with hTwo | hA2
    · exact (largeEvenLabelAll_autRankLeTwo_linearTwo Nat.prime_three (by norm_num) hTwo).mono
        (fun R _ I F h hs hna A hA => (h hs hna A hA).trans (by norm_num))
    · intro Q hQ
      obtain ⟨t, l, f⟩ := lab
      obtain ⟨hl, _, htag⟩ := hA2
      change l = 2 at hl
      dsimp only at htag
      subst l
      rcases htag with ⟨ht, _⟩ | ⟨ht, _⟩
      · subst ht
        obtain ⟨E, _, _, hE, hQ⟩ := hQ
        exact ⟨E, inferInstance, inferInstance, hE, hQ, fun _ _ => gffa2_rank_linear hE⟩
      · subst ht
        obtain ⟨E, _, _, hE, hQ⟩ := hQ
        have hf : 2 ≤ f := by
          change 1 ≤ f ∧ 2 ≤ 2 ∧ (2 = 2 → 2 ≤ f) at hΛ
          exact hΛ.2.2 rfl
        exact ⟨E, inferInstance, inferInstance, hE, hQ, fun _ _ => gffa2_rank_unitary hf hE⟩
  obtain ⟨R, _, I, F, ⟨hs, hna, θ, -, hN, hind⟩, hBound⟩ :=
    largeEvenRawDatum_exists (hAll _ hraw)
  have hBs : IsElemAbelian 3 Bs := hH.1.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs :=
    hH.1.2.1.2.2.2
  have hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut X θ ⟨b, hN hb⟩ ∈ I :=
    fun b hb => ggLAut_mem_of_induces X θ hN hind hb
  have h3 := hH.pow_three_le_card_range hX hN
  have hTB := ggTorusTBGroup_of_marking (r := 3) Nat.prime_three hBs hSC hperf θ hN hBsI h3 h3
  let A := (ggGamma X hN).range
  let ψ := ggQuotHom θ
  have hAb : IsElemAbelian 3 (TypeA.inducedSub ψ A) :=
    TypeA.isElemAbelian_inducedSub (ggQuotHom_surjective θ) hTB.2.2.2.1
  have hcard := TypeA.card_inducedSub (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom]) hperf
    (fun a ha => by obtain ⟨φ, _, hφ⟩ := hTB.2.2.2.2.1 a ha; exact ⟨φ, hφ⟩)
  have hle := hBound hs hna (TypeA.inducedSub ψ A) hAb
  rw [hcard] at hle
  have h5' := h5 hN
  change Nat.card (ggGamma X hN).range ≤ 3 ^ 3 at hle
  norm_num at hle h5'
  omega

theorem GGResHyp.not_innerDiagOnLabel_of_card_lt
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K X : Subgroup G}
    {S : ℕ → LargeEvenLabel → Prop}
    (hH : GGResHyp p B Bs x L D J y K) (hX : X = L ∨ X = K)
    (hRank : ∀ lab, LargeEvenInLambda2 lab → S p lab →
      LargeEvenLabelAll lab fun R _ I _ => ∀ E : Subgroup (MulAut R),
        (E : Set (MulAut R)) ⊆ I → IsElemAbelian p E → Nat.card E < p ^ 3)
    (hMark : GGInnerDiagOnLabel S p Bs X) : False := by
  obtain ⟨hperf, lab, hΛ, hraw⟩ := hMark
  have hS : S p lab := by
    obtain ⟨_, _, _, _, -, -, -, hS, -⟩ := largeEvenRawDatum_exists hraw
    exact hS
  obtain ⟨R, _, I, _, ⟨-, -, θ, -, hN, hind⟩, hBound⟩ :=
    largeEvenRawDatum_exists (hRank lab hΛ hS _ hraw)
  have hBs : IsElemAbelian p Bs := hH.1.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs :=
    hH.1.2.1.2.2.2
  have hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut X θ ⟨b, hN hb⟩ ∈ I :=
    fun b hb => ggLAut_mem_of_induces X θ hN hind hb
  have h3 := hH.pow_three_le_card_range hX hN
  have hTB := ggTorusTBGroup_of_marking (r := 3) Fact.out hBs hSC hperf θ hN hBsI h3 h3
  exact ggTorusTBGroup_false_of_card_lt hBound hTB

theorem GGResHyp.not_smallLie
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K X : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hX : X = L ∨ X = K)
    (hMark : GGInnerDiagOnLabel (fun _ lab => lab.tag = .G2 ∨ lab.tag = .triD4 ∨ lab.tag = .twB2 ∨
      lab.tag = .twF4 ∨ lab.tag = .B2der ∨ lab.tag = .G2der ∨ lab.tag = .twF4der) 3 Bs X) :
    False := by
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine hH.not_innerDiagOnLabel_of_card_lt hX ?_ hMark
  intro lab hΛ htag
  exact (ggSmallThreeRank_of_labels lab hΛ htag).mono
    fun _ _ _ _ h E hEI hE => (h E hEI hE).trans_lt (by norm_num)

end CFSG.StandardType
