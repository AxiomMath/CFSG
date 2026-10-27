module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBProperRoot
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermLabelDefs
import CFSG.LocalAnalysis.StandardType.GGSecFiveBProperRootRed
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpBstar
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1OfPrim
import CFSG.LocalAnalysis.StandardType.GGSpJoinNbrModel
import CFSG.LocalAnalysis.StandardType.GGTBJTwoNodeUnitarySix
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag

private theorem largeEvenInLambda2_twA {p r f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hr : 3 ≤ r) (hpq : p ∣ 2 ^ f + 1) : LargeEvenInLambda2 ⟨.twA, r, f⟩ := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with hf0 | hfpos
    · rw [hf0] at hpq
      exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (by simpa using hpq)) hp2
    · exact hfpos
  simp only [LargeEvenInLambda2]
  exact ⟨hf, by omega, fun h => by omega⟩

private theorem exists_model_input_of_cover {G : Type} [Group G] [Finite G] {p n d : ℕ}
    {Bs L : Subgroup G} (hd : 4 ≤ d) (hpq : p ∣ 2 ^ n + 1)
    (hcover : ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (φ : ↥(unitarySU 2 n F d) →* L),
      Nat.card F = (2 ^ n) ^ 2 ∧ UnitTB.Model φ ∧
        ∀ a ∈ (ggGamma L hN).range, ∃ t : Fin d → F, LineU.ActsDiagU φ a t) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (f e : ℕ)
      (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (φ : ↥(unitarySU 2 f F e) →* L),
      4 ≤ e ∧ p ∣ 2 ^ f + 1 ∧ Nat.card F = (2 ^ f) ^ 2 ∧ UnitTB.Model φ ∧
        ∀ a ∈ (ggGamma L hN).range, ∃ t : Fin e → F, LineU.ActsDiagU φ a t := by
  obtain ⟨F, hField, hFinite, hCharP, hN, φ, hcard, hM, hdiag⟩ := hcover
  exact ⟨F, hField, hFinite, hCharP, n, d, hN, φ, hd, hpq, hcard, hM, hdiag⟩

private theorem exists_model_input_of_label_rank_three
    {G : Type} [Group G] [Finite G]
    {p f : ℕ} {Bs L : Subgroup G} (hp : p.Prime) (hpq : p ∣ 2 ^ f + 1)
    (hRig : GGLabelRigidInput) (hBs : IsElemAbelian p Bs) (hInn : GGInnerDiagOn Bs L)
    (hz : f = 1 → Line63.H5.twoCenter L = ⊥)
    (hLab : GGHasLabel ⟨.twA, 3, f⟩ (L ⧸ Subgroup.center L))
    (hΛ : LargeEvenInLambda2 ⟨.twA, 3, f⟩) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (hN : Bs ≤ Subgroup.normalizer (L : Set G))
      (φ : ↥(unitarySU 2 f F (3 + 1)) →* L),
      Nat.card F = (2 ^ f) ^ 2 ∧ UnitTB.Model φ ∧
        ∀ a ∈ (ggGamma L hN).range, ∃ t : Fin (3 + 1) → F, LineU.ActsDiagU φ a t := by
  rcases eq_or_ne f 1 with rfl | hf1
  · have hp3 : p = 3 := by
      have h3 : p ∣ 3 := by simpa using hpq
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3
    exact exists_diagonal_cover_of_unitary_four_two_of_twoCenter_eq_bot hRig (hp3 ▸ hBs) hInn
      (hz rfl) hLab hΛ
  · have hf2 : 2 ≤ f := by
      have h1 : 1 ≤ f := hΛ.1
      omega
    have : Fact p.Prime := ⟨hp⟩
    exact exists_diagonal_cover_of_unitary_four hRig hBs hInn hf2 hpq hLab hΛ

private theorem exists_model_input_of_label_of_rank_five
    {G : Type} [Group G] [Finite G]
    {p f : ℕ} {B Bs L D J : Subgroup G} {x : G} (hp : p.Prime) (hp2 : p ≠ 2)
    (hRig : GGLabelRigidInput) (hcfg : GGConfig p B Bs x L D J)
    (hIDA : GGInnerDiagAll p B Bs x L D J) (hBs : IsElemAbelian p Bs)
    (hInn : GGInnerDiagOn Bs L) (hz : f = 1 → Line63.H5.twoCenter L = ⊥)
    (hLab : GGHasLabel ⟨.twA, 5, f⟩ (L ⧸ Subgroup.center L))
    (hΛ : LargeEvenInLambda2 ⟨.twA, 5, f⟩) (hpq : p ∣ 2 ^ f + 1) (hpd : p ∣ 5 + 1) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (hN : Bs ≤ Subgroup.normalizer (L : Set G))
      (φ : ↥(unitarySU 2 f F (5 + 1)) →* L),
      Nat.card F = (2 ^ f) ^ 2 ∧ UnitTB.Model φ ∧
        ∀ a ∈ (ggGamma L hN).range, ∃ t : Fin (5 + 1) → F, LineU.ActsDiagU φ a t := by
  have hp3 : p = 3 := by
    have h6 : p ∣ 6 := by simpa using hpd
    have h23 : p ∣ 2 * 3 := by simpa using h6
    rcases hp.dvd_mul.mp h23 with h2 | h3
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2) hp2
    · exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3
  have : Fact p.Prime := ⟨hp⟩
  have hBs3 : IsElemAbelian 3 Bs := hp3 ▸ hBs
  have hcard : ∀ hN : Bs ≤ Subgroup.normalizer (L : Set G),
      3 ^ 4 ≤ Nat.card (ggGamma L hN).range :=
    fun hN => four_le_card_ggGamma_of_unitary_six_L_of_cfg hRig (hp3 ▸ hcfg) hInn (hp3 ▸ hpq)
      hLab hΛ hN
  rcases eq_or_ne f 1 with rfl | hf1
  · exact exists_diagonal_cover_of_unitary_six_two_of_twoCenter_eq_bot hRig hBs3 hInn (hz rfl)
      hLab hΛ hcard
  · have hcardp : ∀ hN : Bs ≤ Subgroup.normalizer (L : Set G),
        p ^ 4 ≤ Nat.card (ggGamma L hN).range := by
      intro hN
      rw [hp3]
      exact hcard hN
    exact exists_diagonal_cover_of_large_unitary_side_of_cfg_of_rank hRig hcfg hIDA (Or.inl rfl)
      (by norm_num) (Or.inr ⟨hf1, hcardp⟩) hpq hpd hLab hΛ


theorem exists_unitary_model_of_twA_label {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {r f : ℕ} (hr : 3 ≤ r) (hpq : p ∣ 2 ^ f + 1)
    (hLab : GGHasLabel ⟨.twA, r, f⟩ (L ⧸ Subgroup.center L))
    (hz : f = 1 → Line63.H5.twoCenter L = ⊥) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (φ : ↥(unitarySU 2 f F (r + 1)) →* L),
      Nat.card F = (2 ^ f) ^ 2 ∧ UnitTB.Model φ ∧
        ∀ a ∈ (ggGamma L hN).range, ∃ t : Fin (r + 1) → F, LineU.ActsDiagU φ a t := by
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hR
  have hcfg : GGConfig p B Bs x L D J := hR.1.1
  have hIDA : GGInnerDiagAll p B Bs x L D J := hR.1.2.2.1
  have hInn : GGInnerDiagOn Bs L := hIDA.1
  have hBs : IsElemAbelian p Bs := hcfg.2.1.2.1
  have hRig : GGLabelRigidInput := ggLabelRigidInput_holds
  have hΛ : LargeEvenInLambda2 ⟨.twA, r, f⟩ := largeEvenInLambda2_twA hp hp2 hr hpq
  have : Fact p.Prime := ⟨hp⟩
  rcases eq_or_ne r 3 with rfl | hr3
  · exact exists_model_input_of_label_rank_three hp hpq hRig hBs hInn hz hLab hΛ
  · have hr4 : 4 ≤ r := by omega
    by_cases hpd : p ∣ r + 1
    · rcases eq_or_ne r 5 with rfl | hr5
      · exact exists_model_input_of_label_of_rank_five hp hp2 hRig hcfg hIDA hBs hInn hz hLab
          hΛ hpq hpd
      · exact exists_diagonal_cover_of_large_unitary_side_of_cfg hRig hcfg hIDA (Or.inl rfl) hr4
          hr5 hpq hpd hLab hΛ
    · have hr5f : r ≠ 5 ∨ f ≠ 1 := by
        by_cases h5 : r = 5
        · right
          intro hf1
          have h3 : p ∣ 3 := by simpa [hf1] using hpq
          have h6 : p ∣ 6 := dvd_trans h3 (by norm_num)
          exact hpd (by simpa [h5] using h6)
        · exact Or.inl h5
      exact exists_diagonal_cover_of_large_unitary_coprime_of_inner hRig hBs hInn hr4 hr5f hpq
        hpd hLab hΛ

theorem exists_unitary_model_of_uniLabel {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {n f : ℕ} (hn : 4 ≤ n) (hf : 2 ≤ f)
    (hL : GGInnerDiagOnLabel (fun p lab => GGSecFiveBPermUniLabel n p lab ∧ lab.n = f) p Bs L) :
    p ∣ 2 ^ f + 1 ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (φ : ↥(unitarySU 2 f F n) →* L),
      Nat.card F = (2 ^ f) ^ 2 ∧ UnitTB.Model φ ∧
        ∀ a ∈ (ggGamma L hN).range, ∃ t : Fin n → F, LineU.ActsDiagU φ a t := by
  obtain ⟨r, rfl⟩ : ∃ r, n = r + 1 := ⟨n - 1, by omega⟩
  have hmark : LargeEvenMarking ↥L
      (fun lab _ _ _ _ _ => GGSecFiveBPermUniLabel (r + 1) p lab ∧ lab.n = f) :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ hP => hP.1) hL
  obtain ⟨lab, hlab, hhas, R, hGR, I, F, θ, hP⟩ := largeEvenMarking_exists_hasLabel hmark
  obtain ⟨hUni, hm⟩ := hP
  obtain ⟨tag, rank, m⟩ := lab
  have hUni' : tag = .twA ∧ rank = (r + 1) - 1 ∧ p ∣ 2 ^ m + 1 := hUni
  obtain ⟨htag, hrank, hpq⟩ := hUni'
  have hm' : m = f := hm
  subst tag
  have hrankr : rank = r := by omega
  subst rank
  subst m
  have hr3 : 3 ≤ r := by omega
  exact ⟨hpq, exists_unitary_model_of_twA_label hR hr3 hpq hhas (fun h1 => absurd h1 (by omega))⟩

theorem ggSecFiveBPermUnitaryModelInput_of_label (h : GGSecFiveBPermUnitaryLabelInput) :
    GGSecFiveBPermUnitaryModelInput := by
  intro G _ _ p B Bs x L D J 𝒦 hR hne n eta hJoin hAut
  obtain ⟨r, f, hr, hpq, hLab⟩ := h G p B Bs x L D J 𝒦 hR hne n eta hJoin hAut
  have hcfg : GGConfig p B Bs x L D J := hR.1.1
  have hIDA : GGInnerDiagAll p B Bs x L D J := hR.1.2.2.1
  have hInn : GGInnerDiagOn Bs L := hIDA.1
  have hlt : B < Bs := lt_of_le_of_ne hcfg.2.1.1 hne
  have hz : Line63.H5.twoCenter L = ⊥ :=
    hcfg.twoCenter_eq_bot_of_B_lt_Bs hlt hInn.le_normalizer
  exact exists_model_input_of_cover (n := f) (d := r + 1) (by omega) hpq
    (exists_unitary_model_of_twA_label hR hr hpq hLab fun _ => hz)

theorem ggSecFiveBProperRootInput_of_label (h : GGSecFiveBPermUnitaryLabelInput) :
    GGSecFiveBProperRootInput :=
  ggSecFiveBProperRootInput_of_model (ggSecFiveBPermUnitaryModelInput_of_label h)

end CFSG.StandardType

end
