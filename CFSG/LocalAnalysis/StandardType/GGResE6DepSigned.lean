module

public import CFSG.LocalAnalysis.StandardType.GGResE6DepLabels
public import CFSG.LocalAnalysis.StandardType.GGTwAutHolds
public import CFSG.LocalAnalysis.StandardType.GGResE6DepRank
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerMoreCl
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerMoreU
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011LabUniq2

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem GGResHyp.not_lowNonsplitClassical_of_gamma_ge_five
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K X : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hX : X = L ∨ X = K)
    (h5 : ∀ (hN : Bs ≤ Subgroup.normalizer (X : Set G)),
      3 ^ 5 ≤ Nat.card ↥(ggGamma X hN).range)
    (hMark : GGInnerDiagOnLabel (fun _ lab => lab.rank ≤ 4 ∧
      ((lab.tag = .A ∧ 3 ∣ 2 ^ lab.n + 1) ∨
        (lab.tag = .twA ∧ 3 ∣ 2 ^ lab.n - 1))) 3 Bs X) :
    False := by
  obtain ⟨hperf, lab, hΛ, hraw⟩ := hMark
  obtain ⟨R, _, I, F, -, -, θ, ⟨hrank, hsign⟩, -, -⟩ := largeEvenRawDatum_exists hraw
  have hAll : LargeEvenLabelAll lab (fun R _ I _ => IsSimpleGroup R →
      (∃ a b : R, a * b ≠ b * a) → GGTorusRankLE 3 lab.rank R I) := by
    intro Q hQ
    obtain ⟨t, l, f⟩ := lab
    rcases hsign with ⟨ht, hdiv⟩ | ⟨ht, hdiv⟩
    · subst ht
      obtain ⟨E, _, _, hE, hQ⟩ := hQ
      have : CharP E 2 := charP_two_of_card hE
      have hn : ¬ 3 ∣ Nat.card E - 1 := by
        rw [hE]
        have hq : 1 ≤ 2 ^ f := Nat.one_le_pow _ _ (by norm_num)
        omega
      refine ⟨E, inferInstance, inferInstance, hE, hQ, ?_⟩
      intro hs hna
      let := hs
      exact ggTorusRankLE_of_elemAbelian (TableBUE.center_eq_bot_of_simple hna)
        (NbrInnerMore.ggOutdiagPrime_linear Nat.prime_three hn (by omega))
        (fun A hA => CFSG.LocalAnalysis.GLTheoremA.card_le_pow_statedProj
          Nat.prime_three (by norm_num)
          (CFSG.LocalAnalysis.GLTheoremA.natCast_ne_zero_of_card_two_pow hE
            Nat.prime_three (by norm_num))
          (by omega) (LargeEvenSLGroup (Fin (l + 1)) E) A hA)
    · subst ht
      obtain ⟨E, _, _, hE, hQ⟩ := hQ
      change 3 ∣ 2 ^ f - 1 at hdiv
      have hn : ¬ 3 ∣ 2 ^ f + 1 := by
        have hq : 1 ≤ 2 ^ f := Nat.one_le_pow _ _ (by norm_num)
        omega
      have hd : 3 ≤ l + 1 := by
        change 1 ≤ f ∧ 2 ≤ l ∧ (l = 2 → 2 ≤ f) at hΛ
        omega
      have hdq : ¬ (l + 1 = 3 ∧ 2 ^ f = 2) := by
        rintro ⟨-, h⟩
        rw [h] at hn
        exact hn (by norm_num)
      have hE' : Nat.card E = 2 ^ (f * 2) := by rw [hE, pow_mul]
      refine ⟨E, inferInstance, inferInstance, hE, hQ, ?_⟩
      intro hs hna
      let := hs
      exact ggTorusRankLE_of_elemAbelian (TableBUE.center_eq_bot_of_simple hna)
        (NbrInnerMore.ggOutdiagPrime_unitary_of_not_dvd hE hΛ.1 hd hdq Nat.prime_three hn)
        (fun A hA => CFSG.LocalAnalysis.GLTheoremA.card_le_pow_statedProj
          Nat.prime_three (by norm_num)
          (CFSG.LocalAnalysis.GLTheoremA.natCast_ne_zero_of_card_two_pow hE'
            Nat.prime_three (by norm_num))
          (by omega) (LargeEvenSUGroup (Fin (l + 1)) E (2 ^ f)) A hA)
  obtain ⟨R, _, I, F, ⟨hs, hna, θ, -, hN', hind⟩, hBound⟩ :=
    largeEvenRawDatum_exists (hAll _ hraw)
  have hBs : IsElemAbelian 3 Bs := hH.1.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs :=
    hH.1.2.1.2.2.2
  have hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut X θ ⟨b, hN' hb⟩ ∈ I :=
    fun b hb => ggLAut_mem_of_induces X θ hN' hind hb
  have h3 := hH.pow_three_le_card_range hX hN'
  have hTB := ggTorusTBGroup_of_marking (r := 3) Nat.prime_three hBs hSC hperf θ hN' hBsI h3 h3
  have hle := hBound hs hna X (ggQuotHom θ) (ggQuotHom_surjective θ)
    (by rw [ker_ggQuotHom]) hperf (ggGamma X hN').range hTB.2.2.2.1 hTB.2.2.2.2.1
  have hle4 : Nat.card (ggGamma X hN').range ≤ 3 ^ 4 :=
    hle.trans (Nat.pow_le_pow_right (by norm_num) hrank)
  have h5' := h5 hN'
  norm_num at hle4 h5'
  omega

theorem GGResE6DepShape.not_lowNonsplitClassical
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K X : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hS : GGResE6DepShape p Bs L J K)
    (hX : X = L ∨ X = K) :
    ¬ GGInnerDiagOnLabel (fun p lab => lab.rank ≤ 4 ∧
      ((lab.tag = .A ∧ p ∣ 2 ^ lab.n + 1) ∨
        (lab.tag = .twA ∧ p ∣ 2 ^ lab.n - 1))) p Bs X := by
  have hp3 : p = 3 := hS.1
  subst hp3
  have h5 := hS.five_le_card_range hX
  exact hH.not_lowNonsplitClassical_of_gamma_ge_five hX h5

theorem GGResHyp.not_nonsplitClassical_of_card_automizer_E6_upto_seven
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K X : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hX : X = L ∨ X = K)
    (hcardBs : Nat.card Bs ≤ 3 ^ 7)
    (hcard : Nat.card ↥(ggAutomizer X Bs) = 51840)
    (hMark : GGInnerDiagOnLabel (fun _ lab => 5 ≤ lab.rank ∧
      ((lab.tag = .A ∧ 3 ∣ 2 ^ lab.n + 1) ∨ (lab.tag = .twA ∧ 3 ∣ 2 ^ lab.n - 1)))
      3 Bs X) : False := by
  obtain ⟨hperf, lab, hΛ, hraw⟩ := hMark
  obtain ⟨R, _, I, F, -, -, θ, ⟨hrank, hsign⟩, -, -⟩ := largeEvenRawDatum_exists hraw
  let r := (lab.rank + 1) / 2
  let ε := (lab.rank + 1) % 2
  have hr : 3 ≤ r := by dsimp [r]; omega
  have hε : ε ≤ 1 := by dsimp [ε]; omega
  have hdim : 2 * r - 1 + ε = lab.rank := by
    dsimp [r, ε]
    omega
  let P : LargeEvenRawCont := fun R _ I _ =>
    GGTorusAutCardSC 3 R I r (2 ^ r * r.factorial) ∧ GGCenterPrime 3 R
  have hAll : LargeEvenLabelAll lab P := by
    have hRank : LargeEvenLabelAll lab (fun R _ I _ =>
        GGTorusAutCardSC 3 R I r (2 ^ r * r.factorial)) := by
      rcases hsign with ⟨ht, hdiv⟩ | ⟨ht, hdiv⟩
      · have heq : lab = ⟨.A, 2 * r - 1 + ε, lab.n⟩ := by
          cases lab; simp_all
        rw [heq]
        exact ggTwSL_label hr hdiv ε hε
      · have heq : lab = ⟨.twA, 2 * r - 1 + ε, lab.n⟩ := by
          cases lab; simp_all
        rw [heq]
        exact ggTwSU_label hΛ.1 hr hdiv ε hε
    have hCenter : LargeEvenLabelAll lab (fun R _ _ _ => GGCenterPrime 3 R) := by
      intro Q hQ
      obtain ⟨t, l, f⟩ := lab
      rcases hsign with ⟨ht, hdiv⟩ | ⟨ht, hdiv⟩
      · subst ht
        obtain ⟨E, _, _, hE, hQ⟩ := hQ
        have : CharP E 2 := charP_two_of_card hE
        exact ⟨E, inferInstance, inferInstance, hE, hQ,
          (ggTwSL_facts_rec (d := l + 1) hr (by dsimp [r]; omega)
            (by rw [hE]; exact hdiv)).2.2⟩
      · subst ht
        obtain ⟨E, _, _, hE, hQ⟩ := hQ
        have : CharP E 2 := charP_two_of_card (m := f * 2) (by rw [hE, pow_mul])
        exact ⟨E, inferInstance, inferInstance, hE, hQ,
          (ggTwSU_facts_rec (d := l + 1) hE hΛ.1 hr (by dsimp [r]; omega) hdiv).2.2⟩
    exact largeEvenLabelAll_and hRank hCenter
  obtain ⟨R, _, I, F, ⟨-, -, θ, -, hN, hind⟩, hRank, hCenter⟩ :=
    largeEvenRawDatum_exists (hAll _ hraw)
  have hBs : IsElemAbelian 3 Bs := hH.1.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs :=
    hH.1.2.1.2.2.2
  have hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut X θ ⟨b, hN hb⟩ ∈ I :=
    fun b hb => ggLAut_mem_of_induces X θ hN hind hb
  have horder : Nat.card (ggAutomizer X Bs) = 51840 := hcard
  have h7 := seven_le_card_range_ggGamma_of_autCardSC hBs hSC hH.2.2.2.1 hperf θ hN hBsI
    hRank hCenter (hH.pow_three_le_card_range hX hN) horder
  have hz : ∃ z : G, z ∈ Bs ∧ z ≠ 1 ∧ z ∈ Subgroup.centralizer (X : Set G) := by
    rcases hX with hX | hX
    · rw [hX]
      exact ⟨x, hH.1.tableB_facts.2.2.1, hH.1.data_L.2.1, hH.1.data_L.1⟩
    · rw [hX]
      exact ⟨y, hH.1.2.1.1 hH.2.2.2.2.1.1.2.1, hH.data_K.2.1, hH.data_K.1⟩
  obtain ⟨z, hzBs, hz1, hzC⟩ := hz
  have hmul := card_range_ggGamma_mul_prime_le Nat.prime_three hBs hN hzBs hz1 hzC
  norm_num at hmul h7 hcardBs
  omega

theorem GGResHyp.not_nonsplitClassical_of_card_automizer_E6
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K X : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hX : X = L ∨ X = K)
    (hcardBs : Nat.card Bs = 3 ^ 6)
    (hcard : Nat.card ↥(ggAutomizer X Bs) = 51840)
    (hMark : GGInnerDiagOnLabel (fun _ lab => 5 ≤ lab.rank ∧
      ((lab.tag = .A ∧ 3 ∣ 2 ^ lab.n + 1) ∨ (lab.tag = .twA ∧ 3 ∣ 2 ^ lab.n - 1)))
      3 Bs X) : False := by
  exact GGResHyp.not_nonsplitClassical_of_card_automizer_E6_upto_seven
    hH hX (by rw [hcardBs]; norm_num) hcard hMark

theorem GGResE6DepShape.not_nonsplitClassical
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K X : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hS : GGResE6DepShape p Bs L J K)
    (hX : X = L ∨ X = K) :
    ¬ GGInnerDiagOnLabel (fun p lab => 5 ≤ lab.rank ∧
      ((lab.tag = .A ∧ p ∣ 2 ^ lab.n + 1) ∨ (lab.tag = .twA ∧ p ∣ 2 ^ lab.n - 1))) p Bs X := by
  have hp3 : p = 3 := hS.1
  subst hp3
  have hcard : Nat.card (ggAutomizer X Bs) = 51840 := by
    rcases hX with hX | hX
    · rw [hX]; exact (ggResE6DepShape_card_automizer hS).1
    · rw [hX]; exact (ggResE6DepShape_card_automizer hS).2
  exact hH.not_nonsplitClassical_of_card_automizer_E6 hX hS.2.1 hcard

end CFSG.StandardType
