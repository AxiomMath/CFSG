module

public import CFSG.LocalAnalysis.StandardType.GGResE6DepLabels
public import CFSG.LocalAnalysis.StandardType.GGResILineAutBound
public import CFSG.LocalAnalysis.StandardType.GGPumpTwExcKnownHolds
public import CFSG.LocalAnalysis.StandardType.GGKGAF4Aut
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSplitLLine
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTorus
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylExcPlusLift
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeNbrKnownLemmas
public import CFSG.LocalAnalysis.StandardType.GGNbrU63Setup
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNSEnnolaExcPlusAux2

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem four_le_card_of_automizer_five_dvd {L' : Type} [Group L'] [Finite L']
    {A : Subgroup (MulAut L')} (hA : IsElemAbelian 3 A)
    (hbad : 5 ∣ Nat.card (ggAutomizer (MulAut.conj : L' →* MulAut L').range A)) :
    3 ^ 4 ≤ Nat.card A := by
  have hgt : 27 < Nat.card A := by
    by_contra h
    exact not_five_dvd_card_ggAutomizer_of_card_le hA (by omega) hbad
  obtain ⟨k, hk⟩ := @IsPGroup.exists_card_eq 3 A _ ⟨Nat.prime_three⟩ _ hA.isPGroup
  have hk4 : 4 ≤ k := by
    have hgt' : 3 ^ 3 < 3 ^ k := by norm_num at hgt ⊢; omega
    have h := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).mp hgt'
    omega
  rw [hk]
  exact Nat.pow_le_pow_right (by norm_num) hk4

theorem four_le_card_of_automizer_dvd {L' : Type} [Group L'] [Finite L']
    {A : Subgroup (MulAut L')} (hA : IsElemAbelian 3 A)
    (hbad : 51840 ∣ Nat.card (ggAutomizer (MulAut.conj : L' →* MulAut L').range A)) :
    3 ^ 4 ≤ Nat.card A :=
  four_le_card_of_automizer_five_dvd hA
    ((show 5 ∣ 51840 from by norm_num).trans hbad)

theorem not_five_dvd_automizer_of_order_1152
    {G : Type} [Group G] [Finite G] {Bs X : Subgroup G}
    (hBs : IsElemAbelian 3 Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hNT : GGNoTransvection 3 Bs) (hperf : commutator X = ⊤)
    {R : Type} [Group R] (θ : X ⧸ Subgroup.center X ≃* R) {I : Set (MulAut R)}
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut X θ ⟨b, hN hb⟩ ∈ I)
    (hZ : Nat.card ↥(Bs ⊓ X ⊓ Subgroup.centralizer (X : Set G)) ≤ 3)
    (hOrder : ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
      ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
      ∀ A : Subgroup (MulAut L'), IsElemAbelian 3 A →
        (∀ a ∈ A, ∃ φ ∈ I, ∀ l, φ (ψ l) = ψ (a l)) →
        3 ^ 4 ≤ Nat.card A → GGTorusSelfCent 3 A →
        Nat.card (ggAutomizer (MulAut.conj : L' →* MulAut L').range A) = 1152)
    (h3 : 3 ^ 3 ≤ Nat.card (ggGamma X hN).range)
    (hfive : 5 ∣ Nat.card (ggAutomizer X Bs)) : False := by
  have hTB := ggTorusTBGroup_of_marking (r := 3) Nat.prime_three hBs hSC hperf θ hN hBsI h3 h3
  have hdvd := card_ggAutomizer_dvd_gamma Nat.prime_three hBs hNT hN hZ
  have h5gamma := hfive.trans hdvd
  have h4 := four_le_card_of_automizer_five_dvd hTB.2.2.2.1 h5gamma
  have hInnerOrder := hOrder X (ggQuotHom θ) (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom])
    hperf (ggGamma X hN).range hTB.2.2.2.1 hTB.2.2.2.2.1 h4 hTB.2.2.2.2.2.2.2
  rw [hInnerOrder] at h5gamma
  norm_num at h5gamma

theorem not_automizer_card_of_order_1152
    {G : Type} [Group G] [Finite G] {Bs X : Subgroup G}
    (hBs : IsElemAbelian 3 Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hNT : GGNoTransvection 3 Bs) (hperf : commutator X = ⊤)
    {R : Type} [Group R] (θ : X ⧸ Subgroup.center X ≃* R) {I : Set (MulAut R)}
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut X θ ⟨b, hN hb⟩ ∈ I)
    (hZ : Nat.card ↥(Bs ⊓ X ⊓ Subgroup.centralizer (X : Set G)) ≤ 3)
    (hOrder : ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
      ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
      ∀ A : Subgroup (MulAut L'), IsElemAbelian 3 A →
        (∀ a ∈ A, ∃ φ ∈ I, ∀ l, φ (ψ l) = ψ (a l)) →
        3 ^ 4 ≤ Nat.card A → GGTorusSelfCent 3 A →
        Nat.card (ggAutomizer (MulAut.conj : L' →* MulAut L').range A) = 1152)
    (h3 : 3 ^ 3 ≤ Nat.card (ggGamma X hN).range)
    (hcard : Nat.card (ggAutomizer X Bs) = 51840) : False :=
  not_five_dvd_automizer_of_order_1152 hBs hSC hNT hperf θ hN hBsI hZ hOrder h3
    (by rw [hcard]; norm_num)

theorem GGResHyp.not_torusLift_six_of_card_bstar
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K X : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hX : X = L ∨ X = K)
    (hperf : commutator X = ⊤)
    {R : Type} [Group R] (θ : X ⧸ Subgroup.center X ≃* R)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hcardBs : Nat.card Bs = 3 ^ 6)
    (hLift : GGTorusLift 3 6 R) : False := by
  have h6 : 3 ^ 6 ≤ Nat.card (ggGamma X hN).range := by
    rcases hX with hX | hX
    · subst X
      exact (card_range_ggGamma_bstar_ge hH.1 hperf θ hN hLift).1
    · subst X
      exact pow_le_card_range_ggGamma_bstar_of_torusLift hH.1 hH.2.2.2.2.1 hperf θ hN hLift
  have hz : ∃ z : G, z ∈ Bs ∧ z ≠ 1 ∧ z ∈ Subgroup.centralizer (X : Set G) := by
    rcases hX with hX | hX
    · rw [hX]
      exact ⟨x, hH.1.tableB_facts.2.2.1, hH.1.data_L.2.1, hH.1.data_L.1⟩
    · rw [hX]
      exact ⟨y, hH.1.2.1.1 hH.2.2.2.2.1.1.2.1, hH.data_K.2.1, hH.data_K.1⟩
  obtain ⟨z, hzBs, hz1, hzC⟩ := hz
  have hmul := card_range_ggGamma_mul_prime_le Nat.prime_three hH.1.2.1.2.1 hN hzBs hz1 hzC
  rw [hcardBs] at hmul
  norm_num at hmul h6
  omega

theorem GGResE6DepShape.not_torusLift_six
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K X : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hS : GGResE6DepShape p Bs L J K)
    (hX : X = L ∨ X = K) (hperf : commutator X = ⊤)
    {R : Type} [Group R] (θ : X ⧸ Subgroup.center X ≃* R)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)) (hLift : GGTorusLift p 6 R) : False := by
  have hp3 : p = 3 := hS.1
  subst hp3
  exact hH.not_torusLift_six_of_card_bstar hX hperf θ hN hS.2.1 hLift

theorem GGResHyp.not_torusLift_seven_of_card_bs_le
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K X : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hX : X = L ∨ X = K)
    (hperf : commutator X = ⊤)
    {R : Type} [Group R] (θ : X ⧸ Subgroup.center X ≃* R)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hcardBs : Nat.card Bs ≤ 3 ^ 7)
    (hLift : GGTorusLift 3 7 R) : False := by
  have h7 : 3 ^ 7 ≤ Nat.card (ggGamma X hN).range := by
    rcases hX with hX | hX
    · subst X
      exact (card_range_ggGamma_bstar_ge hH.1 hperf θ hN hLift).1
    · subst X
      exact pow_le_card_range_ggGamma_bstar_of_torusLift hH.1 hH.2.2.2.2.1 hperf θ hN hLift
  have hz : ∃ z : G, z ∈ Bs ∧ z ≠ 1 ∧ z ∈ Subgroup.centralizer (X : Set G) := by
    rcases hX with hX | hX
    · rw [hX]
      exact ⟨x, hH.1.tableB_facts.2.2.1, hH.1.data_L.2.1, hH.1.data_L.1⟩
    · rw [hX]
      exact ⟨y, hH.1.2.1.1 hH.2.2.2.2.1.1.2.1, hH.data_K.2.1, hH.data_K.1⟩
  obtain ⟨z, hzBs, hz1, hzC⟩ := hz
  have hzord : orderOf z = 3 := orderOf_eq_prime (hH.1.2.1.2.1.2 z hzBs) hz1
  have hzp : Subgroup.zpowers z ≤ Bs ⊓ Subgroup.centralizer (X : Set G) :=
    Subgroup.zpowers_le.mpr ⟨hzBs, hzC⟩
  have hcard : 3 ≤ Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) := by
    rw [← hzord, ← Nat.card_zpowers]
    exact Subgroup.card_le_of_le hzp
  have hmul : Nat.card (ggGamma X hN).range * 3 ≤ Nat.card Bs :=
    (Nat.mul_le_mul_left _ hcard).trans_eq
      (NbrU63.card_range_ggGamma_mul_card_inf hN)
  norm_num at hmul h7 hcardBs
  omega

section Exceptional


theorem GGResHyp.not_E8_of_card_bstar_le_seven
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K X : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hX : X = L ∨ X = K)
    (hcardBs : Nat.card Bs ≤ 3 ^ 7)
    (hMark : GGInnerDiagOnLabel (fun _ lab => lab.tag = .E8) 3 Bs X) :
    False := by
  obtain ⟨hperf, lab, hΛ, hraw⟩ := hMark
  obtain ⟨R, _, I, F, -, -, θ, htag, -, -⟩ := largeEvenRawDatum_exists hraw
  have hAll : LargeEvenLabelAll lab (fun R _ _ _ => GGTorusLift 3 7 R) := by
    intro Q hQ
    obtain ⟨t, l, f⟩ := lab
    change t = .E8 at htag
    subst htag
    obtain ⟨E, _, _, hE, hQ⟩ := hQ
    have : CharP E 2 := charP_two_of_card hE
    have hLift : GGTorusLift 3 7 (TableBExc.RecipeGroup .E8 E) := by
      rcases three_dvd_two_pow_pred_or_succ f with h | h
      · exact ggTorusLift_mono Nat.prime_three
          (TableBExc.ggTorusLift_E8 Nat.prime_three (by norm_num) (by rw [hE]; exact h))
          (by norm_num)
      · exact ggTorusLift_E8Plus Nat.prime_three (by norm_num) (by rw [hE]; exact h)
    exact ⟨E, inferInstance, inferInstance, hE, hQ, hLift⟩
  obtain ⟨R, _, I, F, ⟨-, -, θ, -, hN, -⟩, hLift⟩ := largeEvenRawDatum_exists (hAll _ hraw)
  exact hH.not_torusLift_seven_of_card_bs_le hX hperf θ hN hcardBs hLift

theorem GGResHyp.not_E7_split_of_card_bstar_le_seven
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K X : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hX : X = L ∨ X = K)
    (hcardBs : Nat.card Bs ≤ 3 ^ 7)
    (hMark : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .E7 ∧ 3 ∣ 2 ^ lab.n - 1) 3 Bs X) :
    False := by
  obtain ⟨hperf, lab, hΛ, hraw⟩ := hMark
  obtain ⟨R, _, I, F, -, -, θ, ⟨htag, hsplit⟩, -, -⟩ := largeEvenRawDatum_exists hraw
  have hAll : LargeEvenLabelAll lab (fun R _ _ _ => GGTorusLift 3 7 R) := by
    intro Q hQ
    obtain ⟨t, l, f⟩ := lab
    change t = .E7 at htag
    subst htag
    obtain ⟨E, _, _, hE, hQ⟩ := hQ
    have : CharP E 2 := charP_two_of_card hE
    have hLift : GGTorusLift 3 7 (TableBExc.RecipeGroup .E7 E) :=
      TableBExc.ggTorusLift_E7 Nat.prime_three (by norm_num) (by rw [hE]; exact hsplit)
    exact ⟨E, inferInstance, inferInstance, hE, hQ, hLift⟩
  obtain ⟨R, _, I, F, ⟨-, -, θ, -, hN, -⟩, hLift⟩ := largeEvenRawDatum_exists (hAll _ hraw)
  exact hH.not_torusLift_seven_of_card_bs_le hX hperf θ hN hcardBs hLift

theorem GGResHyp.e7plus_marking_of_e7e8_of_card_bstar_le_seven
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K X : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hX : X = L ∨ X = K)
    (hcardBs : Nat.card Bs ≤ 3 ^ 7)
    (hMark : GGInnerDiagOnLabel (fun _ lab => lab.tag = .E7 ∨ lab.tag = .E8) 3 Bs X) :
    GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .E7 ∧ 3 ∣ 2 ^ lab.n + 1) 3 Bs X := by
  obtain ⟨hperf, lab, hΛ, hraw⟩ := hMark
  obtain ⟨R, _, I, F, -, -, θ, htag, -, -⟩ := largeEvenRawDatum_exists hraw
  have hMarkEq : GGInnerDiagOnLabel (fun _ lab' => lab' = lab) 3 Bs X := by
    refine ⟨hperf, lab, hΛ, ?_⟩
    exact largeEvenRawDatum_mono (fun R _ I F h =>
      ⟨h.1, h.2.1, h.2.2.choose, rfl, h.2.2.choose_spec.2⟩) hraw
  have marked (S : LargeEvenLabel → Prop) (hS : S lab) :
      GGInnerDiagOnLabel (fun _ lab' => S lab') 3 Bs X :=
    GGInnerDiagOnLabel.mono_label (S := fun _ lab' => lab' = lab)
      (T := fun _ lab' => S lab') (fun _ heq => heq ▸ hS) hMarkEq
  rcases lab with ⟨tag, r, n⟩
  rcases htag with rfl | rfl
  · rcases three_dvd_two_pow_pred_or_succ n with hminus | hplus
    · exact False.elim (GGResHyp.not_E7_split_of_card_bstar_le_seven hH hX hcardBs
        (marked (fun lab => lab.tag = .E7 ∧ 3 ∣ 2 ^ lab.n - 1) ⟨rfl, hminus⟩))
    · exact marked (fun lab => lab.tag = .E7 ∧ 3 ∣ 2 ^ lab.n + 1) ⟨rfl, hplus⟩
  · exact False.elim (GGResHyp.not_E8_of_card_bstar_le_seven hH hX hcardBs
      (marked (fun lab => lab.tag = .E8) rfl))



theorem GGResHyp.not_E7plus_of_card_bstar_le_seven
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K X : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hX : X = L ∨ X = K)
    (hcardBs : Nat.card Bs ≤ 3 ^ 7)
    (hMark : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .E7 ∧ 3 ∣ 2 ^ lab.n + 1) 3 Bs X) :
    False := by
  obtain ⟨hperf, lab, hΛ, hraw⟩ := hMark
  obtain ⟨_, _, _, _, -, -, _, ⟨htag, hplus⟩, -, -⟩ :=
    largeEvenRawDatum_exists hraw
  have hAllLift : LargeEvenLabelAll lab
      (fun R _ _ _ => GGTorusLift 3 6 R) := by
    intro Q hQ
    obtain ⟨t, l, f⟩ := lab
    change t = .E7 at htag
    subst htag
    obtain ⟨E, _, _, hE, hQ⟩ := hQ
    have : CharP E 2 := charP_two_of_card hE
    have hpq : 3 ∣ Nat.card E + 1 := by
      rw [hE]
      simpa using hplus
    exact ⟨E, inferInstance, inferInstance, hE, hQ,
      ggTorusLift_E7Plus Nat.prime_three (by norm_num) hpq⟩
  have hAllModel : LargeEvenLabelAll lab
      (fun R _ I _ => GGExcPlusWeylModelSCr .E7 3 6 R I) := by
    have h := ggNEE_largeEvenLabelAll_model_excPlus (p := 3) Nat.prime_three
      (by norm_num) (lab := lab) (Or.inl htag) hplus
    rw [show ggNEE_tagOf lab.tag = .E7 by simp [ggNEE_tagOf, htag],
      show ggNbrExcPlusRank lab.tag = 6 by simp [ggNbrExcPlusRank, htag]] at h
    exact h
  have hAll : LargeEvenLabelAll lab
      (fun R _ I _ => GGTorusLift 3 6 R ∧ GGExcPlusWeylModelSCr .E7 3 6 R I) :=
    LargeEvenLabelAll.and hAllLift hAllModel
  obtain ⟨R, _, I, F, ⟨⟨-, -, θ, hP⟩, hLift, hModelR⟩⟩ :=
    largeEvenRawDatum_exists (hAll _ hraw)
  obtain ⟨⟨-, -⟩, hN, hind⟩ := hP
  have hBs : IsElemAbelian 3 Bs := hH.1.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs :=
    hH.1.2.1.2.2.2
  have hr : 3 ^ 6 ≤ Nat.card (ggGamma X hN).range := by
    rcases hX with hX | hX
    · subst X
      exact (card_range_ggGamma_bstar_ge hH.1 hperf θ hN hLift).1
    · subst X
      exact pow_le_card_range_ggGamma_bstar_of_torusLift hH.1 hH.2.2.2.2.1
        hperf θ hN hLift
  have h3 : 3 ^ 3 ≤ Nat.card (ggGamma X hN).range :=
    le_trans (by norm_num) hr
  have hTB : GGTorusTBGroup 3 6 R I X (ggQuotHom θ) (ggGamma X hN).range :=
    ggTorusTBGroup_of_marking Nat.prime_three hBs hSC hperf θ hN
      (fun b hb => ggLAut_mem_of_induces X θ hN hind hb) hr h3
  obtain ⟨Φ, -⟩ := hModelR X (ggQuotHom θ) (ggGamma X hN).range hTB
  have hA7 : Nat.card (ggGamma X hN).range = 3 ^ 7 := by
    rw [Nat.card_congr Φ.toEquiv, Nat.card_congr Multiplicative.toAdd,
      Nat.card_fun, Nat.card_zmod, Nat.card_fin]
    rfl
  have hz : ∃ z : G, z ∈ Bs ∧ z ≠ 1 ∧
      z ∈ Subgroup.centralizer (X : Set G) := by
    rcases hX with hX | hX
    · rw [hX]
      exact ⟨x, hH.1.tableB_facts.2.2.1, hH.1.data_L.2.1, hH.1.data_L.1⟩
    · rw [hX]
      exact ⟨y, hH.1.2.1.1 hH.2.2.2.2.1.1.2.1, hH.data_K.2.1, hH.data_K.1⟩
  obtain ⟨z, hzBs, hz1, hzC⟩ := hz
  have hzord : orderOf z = 3 := orderOf_eq_prime (hBs.2 z hzBs) hz1
  have hzp : Subgroup.zpowers z ≤ Bs ⊓ Subgroup.centralizer (X : Set G) :=
    Subgroup.zpowers_le.mpr ⟨hzBs, hzC⟩
  have hcard : 3 ≤ Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) := by
    rw [← hzord, ← Nat.card_zpowers]
    exact Subgroup.card_le_of_le hzp
  have hmul : Nat.card (ggGamma X hN).range * 3 ≤ Nat.card Bs :=
    (Nat.mul_le_mul_left _ hcard).trans_eq
      (NbrU63.card_range_ggGamma_mul_card_inf hN)
  rw [hA7] at hmul
  norm_num at hmul hcardBs
  omega

theorem GGResHyp.not_E7_E8_of_card_bstar_le_seven
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K X : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hX : X = L ∨ X = K)
    (hcardBs : Nat.card Bs ≤ 3 ^ 7)
    (hMark : GGInnerDiagOnLabel (fun _ lab => lab.tag = .E7 ∨ lab.tag = .E8) 3 Bs X) :
    False :=
  hH.not_E7plus_of_card_bstar_le_seven hX hcardBs
    (hH.e7plus_marking_of_e7e8_of_card_bstar_le_seven hX hcardBs hMark)


theorem GGResHyp.not_E7_E8_of_card_bstar
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K X : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hX : X = L ∨ X = K)
    (hcardBs : Nat.card Bs = 3 ^ 6)
    (hMark : GGInnerDiagOnLabel (fun _ lab => lab.tag = .E7 ∨ lab.tag = .E8) 3 Bs X) :
    False := by
  obtain ⟨hperf, lab, hΛ, hraw⟩ := hMark
  obtain ⟨R, _, I, F, -, -, θ, ht, -, -⟩ := largeEvenRawDatum_exists hraw
  have hAll : LargeEvenLabelAll lab (fun R _ _ _ => GGTorusLift 3 6 R) := by
    intro Q hQ
    obtain ⟨t, l, f⟩ := lab
    rcases ht with ht | ht
    · subst ht
      obtain ⟨E, _, _, hE, hQ⟩ := hQ
      have : CharP E 2 := charP_two_of_card hE
      have hLift : GGTorusLift 3 6 (TableBExc.RecipeGroup .E7 E) := by
        rcases three_dvd_two_pow_pred_or_succ f with h | h
        · exact ggTorusLift_mono Nat.prime_three
            (TableBExc.ggTorusLift_E7 Nat.prime_three (by norm_num) (by rw [hE]; exact h)) (by norm_num)
        · exact ggTorusLift_E7Plus Nat.prime_three (by norm_num) (by rw [hE]; exact h)
      exact ⟨E, inferInstance, inferInstance, hE, hQ, hLift⟩
    · subst ht
      obtain ⟨E, _, _, hE, hQ⟩ := hQ
      have : CharP E 2 := charP_two_of_card hE
      have hLift : GGTorusLift 3 6 (TableBExc.RecipeGroup .E8 E) := by
        rcases three_dvd_two_pow_pred_or_succ f with h | h
        · exact ggTorusLift_mono Nat.prime_three
            (TableBExc.ggTorusLift_E8 Nat.prime_three (by norm_num) (by rw [hE]; exact h)) (by norm_num)
        · exact ggTorusLift_mono Nat.prime_three
            (ggTorusLift_E8Plus Nat.prime_three (by norm_num) (by rw [hE]; exact h)) (by norm_num)
      exact ⟨E, inferInstance, inferInstance, hE, hQ, hLift⟩
  obtain ⟨R, _, I, F, ⟨-, -, θ, -, hN, -⟩, hLift⟩ := largeEvenRawDatum_exists (hAll _ hraw)
  exact hH.not_torusLift_six_of_card_bstar hX hperf θ hN hcardBs hLift

theorem GGResE6DepShape.not_E7_E8
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K X : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hS : GGResE6DepShape p Bs L J K)
    (hX : X = L ∨ X = K) :
    ¬ GGInnerDiagOnLabel (fun _ lab => lab.tag = .E7 ∨ lab.tag = .E8) p Bs X := by
  have hp3 : p = 3 := hS.1
  subst hp3
  exact hH.not_E7_E8_of_card_bstar hX hS.2.1

theorem GGResHyp.not_five_dvd_automizer_of_F4
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K X : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hX : X = L ∨ X = K)
    (hfive : 5 ∣ Nat.card ↥(ggAutomizer X Bs))
    (hMark : GGInnerDiagOnLabel (fun _ lab => lab.tag = .F4) 3 Bs X) : False := by
  obtain ⟨hperf, lab, hΛ, hraw⟩ := hMark
  obtain ⟨R, _, I, F, -, -, θ, ht, -, -⟩ := largeEvenRawDatum_exists hraw
  have hEq : lab = ⟨.F4, 0, lab.n⟩ := by
    have hr : lab.rank = 0 := by simpa only [LargeEvenInLambda2, ht] using hΛ.2
    cases lab
    simp_all
  have hCenter : LargeEvenLabelAll lab (fun R _ _ _ => GGCenterPrime 3 R) := by
    intro Q hQ
    rw [hEq] at hQ ⊢
    obtain ⟨E, _, _, hE, hQ⟩ := hQ
    have : CharP E 2 := charP_two_of_card hE
    exact ⟨E, inferInstance, inferInstance, hE, hQ,
      ExcSplitL.ggCenterPrime_recipe_F4 Nat.prime_three (by norm_num)⟩
  have hOrder : LargeEvenLabelAll lab (fun R _ _ _ => KGA.GGF4AutOrderAt 3 R) := by
    rw [hEq]
    change LargeEvenLabelAll ⟨.F4, 4, lab.n⟩ (fun R _ _ _ => KGA.GGF4AutOrderAt 3 R)
    exact KGA.ggF4_autOrder_label Nat.prime_three (by norm_num)
  have hBasic : LargeEvenLabelAll lab (fun R _ I _ => IsSimpleGroup R ∧
      (∃ a b : R, a * b ≠ b * a) ∧ GGHasLabel ⟨.F4, 4, lab.n⟩ R ∧
        ∀ φ ∈ I, ∃ r : R, φ = MulAut.conj r) := by
    rw [hEq]
    change LargeEvenLabelAll ⟨.F4, 4, lab.n⟩ _
    exact KGA.ggF4_basics_label
  obtain ⟨R, _, I, F, ⟨-, -, θ, -, hN, hind⟩, ⟨hCenter, hOrder⟩,
      hSimple, hNonab, _, hI⟩ := largeEvenRawDatum_exists
    ((largeEvenLabelAll_and (largeEvenLabelAll_and hCenter hOrder) hBasic) _ hraw)
  have hZ : Subgroup.center R = ⊥ :=
    @center_eq_bot_of_isSimpleGroup_of_nonabelian R _ hSimple hNonab
  have hBs : IsElemAbelian 3 Bs := hH.1.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs :=
    hH.1.2.1.2.2.2
  have hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut X θ ⟨b, hN hb⟩ ∈ I :=
    fun b hb => ggLAut_mem_of_induces X θ hN hind hb
  have hcp := hCenter X (ggQuotHom θ) (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom]) hperf
  have hZB : Nat.card ↥(Bs ⊓ X ⊓ Subgroup.centralizer (X : Set G)) ≤ 3 := by
    rw [inf_center_eq_bot_of_isElemAbelian_of_not_dvd Nat.prime_three hBs hcp, Subgroup.card_bot]
    norm_num
  exact not_five_dvd_automizer_of_order_1152 hBs hSC hH.2.2.2.1 hperf θ hN hBsI hZB
    (fun L' _ _ ψ hψ hker hperf A hA hAI h4 _ =>
      KGA.ggF4_transport hZ hI hOrder ψ hψ hker hperf A hA hAI h4)
    (hH.pow_three_le_card_range hX hN) hfive

theorem GGResHyp.not_F4_of_card_automizer_E6
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K X : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hX : X = L ∨ X = K)
    (hcard : Nat.card ↥(ggAutomizer X Bs) = 51840)
    (hMark : GGInnerDiagOnLabel (fun _ lab => lab.tag = .F4) 3 Bs X) : False := by
  exact hH.not_five_dvd_automizer_of_F4 hX (by rw [hcard]; norm_num) hMark

theorem GGResE6DepShape.not_F4
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K X : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hS : GGResE6DepShape p Bs L J K)
    (hX : X = L ∨ X = K) :
    ¬ GGInnerDiagOnLabel (fun _ lab => lab.tag = .F4) p Bs X := by
  have hp3 : p = 3 := hS.1
  subst hp3
  have hcard : Nat.card (ggAutomizer X Bs) = 51840 := by
    rcases hX with hX | hX
    · rw [hX]; exact (ggResE6DepShape_card_automizer hS).1
    · rw [hX]; exact (ggResE6DepShape_card_automizer hS).2
  exact hH.not_F4_of_card_automizer_E6 hX hcard

theorem GGResHyp.not_oppositeE6_of_card_automizer_E6
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K X : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hX : X = L ∨ X = K)
    (hcard : Nat.card ↥(ggAutomizer X Bs) = 51840)
    (hMark : GGInnerDiagOnLabel (fun _ lab =>
      (lab.tag = .E6 ∧ 3 ∣ 2 ^ lab.n + 1) ∨
        (lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n - 1)) 3 Bs X) : False := by
  obtain ⟨hperf, lab, hΛ, hraw⟩ := hMark
  obtain ⟨R, _, I, F, -, -, θ, hsign, -, -⟩ := largeEvenRawDatum_exists hraw
  have hrow : (lab = ⟨.E6, 0, lab.n⟩ ∧ 3 ∣ 2 ^ lab.n + 1) ∨
      (lab = ⟨.twE6, 0, lab.n⟩ ∧ 3 ∣ 2 ^ lab.n - 1) := by
    rcases hsign with ⟨ht, hd⟩ | ⟨ht, hd⟩
    · have hr : lab.rank = 0 := by simpa only [LargeEvenInLambda2, ht] using hΛ.2
      left
      refine ⟨?_, hd⟩
      cases lab
      simp_all
    · have hr : lab.rank = 0 := by simpa only [LargeEvenInLambda2, ht] using hΛ.2
      right
      refine ⟨?_, hd⟩
      cases lab
      simp_all
  obtain ⟨R, _, I, F, ⟨-, -, θ, -, hN, hind⟩, hCenter, _, hOrder⟩ :=
    largeEvenRawDatum_exists (ggPumpTwExcKnown_holds lab.n hΛ.1 lab hrow _ hraw)
  have hBs : IsElemAbelian 3 Bs := hH.1.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs :=
    hH.1.2.1.2.2.2
  have hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut X θ ⟨b, hN hb⟩ ∈ I :=
    fun b hb => ggLAut_mem_of_induces X θ hN hind hb
  have hcp := hCenter X (ggQuotHom θ) (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom]) hperf
  have hZ : Nat.card ↥(Bs ⊓ X ⊓ Subgroup.centralizer (X : Set G)) ≤ 3 := by
    rw [inf_center_eq_bot_of_isElemAbelian_of_not_dvd Nat.prime_three hBs hcp, Subgroup.card_bot]
    norm_num
  have hActual : Nat.card (ggAutomizer X Bs) = 51840 := hcard
  exact not_automizer_card_of_order_1152 hBs hSC hH.2.2.2.1 hperf θ hN hBsI hZ hOrder
    (hH.pow_three_le_card_range hX hN) hActual

theorem GGResE6DepShape.not_oppositeE6
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K X : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hS : GGResE6DepShape p Bs L J K)
    (hX : X = L ∨ X = K) :
    ¬ GGInnerDiagOnLabel (fun p lab => (lab.tag = .E6 ∧ p ∣ 2 ^ lab.n + 1) ∨
      (lab.tag = .twE6 ∧ p ∣ 2 ^ lab.n - 1)) p Bs X := by
  have hp3 : p = 3 := hS.1
  subst hp3
  have hcard : Nat.card (ggAutomizer X Bs) = 51840 := by
    rcases hX with hX | hX
    · rw [hX]; exact (ggResE6DepShape_card_automizer hS).1
    · rw [hX]; exact (ggResE6DepShape_card_automizer hS).2
  exact hH.not_oppositeE6_of_card_automizer_E6 hX hcard



theorem GGResHyp.not_F4_of_e6_exactTwo_either_all_fields
    {G : Type} [Group G] [Finite G]
    {B Bs L D J K X : Subgroup G} {x y : G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hD : GGResLeviDatumExact2 3 Bs L J K ggSelAny ggTypLE6 ∨
      GGResLeviDatumExact2 3 Bs K J L ggSelAny ggTypLE6)
    (hMJ : GGInnerDiagOnLabel
      (fun _ lab => lab = (⟨.twA, 4, 1⟩ : LargeEvenLabel)) 3 Bs J)
    (hX : X = L ∨ X = K)
    (hF4 : GGInnerDiagOnLabel (fun _ lab => lab.tag = .F4) 3 Bs X) : False := by
  have h120 := hH.twA_four_two_J_automizer_card_of_e6_exactTwo hD hMJ
  have hAJ : ggAutomizer J Bs ≤ ggAutomizer L Bs ⊓ ggAutomizer K Bs := by
    rcases hD with hDL | hDK
    · exact hDL.aj_le
    · simpa only [inf_comm] using hDK.aj_le
  have hJX : ggAutomizer J Bs ≤ ggAutomizer X Bs := by
    rcases hX with rfl | rfl
    · exact hAJ.trans inf_le_left
    · exact hAJ.trans inf_le_right
  have h5 : 5 ∣ Nat.card ↥(ggAutomizer X Bs) :=
    (show 5 ∣ 120 from by norm_num).trans
      (by rw [← h120]; exact Subgroup.card_dvd_of_le hJX)
  exact hH.not_five_dvd_automizer_of_F4 hX h5 hF4

end Exceptional

end CFSG.StandardType
