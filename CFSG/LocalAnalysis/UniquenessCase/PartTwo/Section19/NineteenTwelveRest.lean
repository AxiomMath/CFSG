module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenTwelve
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenTenTwoComponents
public import CFSG.GroupTheory.ElemAbelianProjection
public import CFSG.Mathlib.Arithmetic.TwoPowModThree
public import CFSG.SignalizerFunctorTheorem.McBride.Models.PSL2Even.Arithmetic
public import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofRead

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
open CFSG.ComponentClassification.CatLeafProof CFSG.Blueprint
open CFSG.Blueprint (LieModel)
open CFSG.SignalizerFunctorTheorem.McBride.PSL2Even
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]


theorem nineteen_twelve_at (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L A : Subgroup G}
    {t : G} {B : Subgroup G} {r : ℕ} (h : Ctx19_10 D V₀ V p L A t B r)
    (hr3 : 3 ∈ piSet A → r = 3)
    (h42 : S17.R17_42At D V₀ V) (h8107 : F08.R8107 D)
    (hj4 : S17.jM D p = 4 →
      ∃ K₁ K₂ : Subgroup G, K₁ ∈ calC D.M ∧ K₂ ∈ calC D.M ∧ K₁ ≠ K₂ ∧
        IOf D p L = K₁ ⊔ K₂ ∧ IsL2 (Bar2 K₁) (S17.nOf L) ∧
        (IsL2 (Bar2 K₂) (S17.nOf L) ∨ IsU3 (Bar2 K₂) (S17.nOf L)) ∧
        IsPowTwo (S17.nOf L) ∧ 2 < S17.nOf L) :
    R19_12At D V₀ V p L A t B r h := by
  intro E hEA hEel hEcard
  have hEM : E ≤ D.M :=
    hEA.trans (h.hA.trans (IOf_le_M D p h.hyp.hL.1.1.le))
  have three_dvd_of_even : ∀ {m : ℕ}, Even m → 3 ∣ 2 ^ m - 1 := by
    intro m hm
    have hmod : 2 ^ m % 3 = 1 := CFSG.two_pow_mod_three_of_even hm
    refine ⟨2 ^ m / 3, ?_⟩
    have h := Nat.div_add_mod (2 ^ m) 3
    omega
  by_cases h3 : 3 ∈ piSet A
  ·
    have hr : r = 3 := hr3 h3
    subst hr
    have h3dvdA : 3 ∣ Nat.card A := h3.2
    have hAcard : Nat.card A = (2 ^ S17.nOf L - 1) * (2 ^ S17.nOf L - 1) :=
      card_eq_of_isZModSq h.hAcard
    have h3dvd : 3 ∣ 2 ^ S17.nOf L - 1 := by
      have h : 3 ∣ (2 ^ S17.nOf L - 1) ^ 2 := by
        rw [pow_two, ← hAcard]
        exact h3dvdA
      exact Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    have keyL2 : ∀ (L₁ L₂ : Subgroup G) (m : ℕ), L₁ ∈ calC D.M → L₂ ∈ calC D.M →
        L₁ ≠ L₂ → IsL2 (Bar2 L₁) m → IsL2 (Bar2 L₂) m →
        L₂ ≤ normalizer (L₁ : Set G) → E ≤ L₁ ⊔ L₂ →
        E ∈ CFSG.LocalAnalysis.RankThreeUC.uniqueSet D.M := by
      intro L₁ L₂ m h1 h2 hne hL₁ hL₂ hnorm hsup
      have hp1 : CFSG.Open.pRank 3 L₁ = 1 := pRank_three_eq_one_of_isL2 hL₁
      have hp2 : CFSG.Open.pRank 3 L₂ = 1 := pRank_three_eq_one_of_isL2 hL₂
      obtain ⟨F, hFle, hFcard⟩ := CFSG.GroupTheory.exists_card_prime_le_inf_of_le_sup
        (q := 3) Nat.prime_three (by norm_num) hnorm (le_of_eq hp2) hsup hEel hEcard
      obtain ⟨A₂, hA₂le, -, hA₂card⟩ :=
        CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) L₂
      have hA₂card' : Nat.card A₂ = 3 := by rw [hA₂card, hp2, pow_one]
      have hFuniq := (h8107 L₁ h1 L₂ h2 hne hp1 hp2
        (Or.inl (thin8_of_isL2 hL₁)) (Or.inl (thin8_of_isL2 hL₂))
        F A₂ (hFle.trans inf_le_right) hFcard hA₂le hA₂card').1
      exact CFSG.LocalAnalysis.RankThreeUC.mem_uniqueSet_of_le hFuniq (hFle.trans inf_le_left) hEM
    by_cases hj : S17.jM D p = 4
    ·
      obtain ⟨K₁, K₂, hK₁, hK₂, hne, hIOfeq, hL₂K₁, hL₂K₂, hpow, hn2⟩ := hj4 hj
      have hnorm : K₂ ≤ normalizer (K₁ : Set G) :=
        uc22p22u_calC_normalizes hK₁ hK₂ hne
      have hp1 : CFSG.Open.pRank 3 K₁ = 1 := pRank_three_eq_one_of_isL2 hL₂K₁
      have hp2 : CFSG.Open.pRank 3 K₂ = 1 := by
        rcases hL₂K₂ with hL₂ | hU₃
        · exact pRank_three_eq_one_of_isL2 hL₂
        · exact pRank_three_eq_one_of_isU3FourPow hU₃ hpow (by omega)
      have hthin₂ : F08.Thin8 K₂ ∨ ∃ m : ℕ, IsU3 (Bar2 K₂) m := by
        rcases hL₂K₂ with hL₂ | hU₃
        · exact Or.inl (thin8_of_isL2 hL₂)
        · exact Or.inr ⟨S17.nOf L, hU₃⟩
      have hsup : E ≤ K₁ ⊔ K₂ := by
        rw [← hIOfeq]
        exact hEA.trans h.hA
      obtain ⟨F, hFle, hFcard⟩ := CFSG.GroupTheory.exists_card_prime_le_inf_of_le_sup
        (q := 3) Nat.prime_three (by norm_num) hnorm (le_of_eq hp2) hsup hEel hEcard
      obtain ⟨A₂, hA₂le, -, hA₂card⟩ :=
        CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) K₂
      have hA₂card' : Nat.card A₂ = 3 := by rw [hA₂card, hp2, pow_one]
      have hFuniq := (h8107 K₁ hK₁ K₂ hK₂ hne hp1 hp2
        (Or.inl (thin8_of_isL2 hL₂K₁)) hthin₂
        F A₂ (hFle.trans inf_le_right) hFcard hA₂le hA₂card').1
      exact CFSG.LocalAnalysis.RankThreeUC.mem_uniqueSet_of_le hFuniq (hFle.trans inf_le_left) hEM
    ·
      have hI : IOf D p L = conjClosure D.M L := by simp [IOf, hj]
      have h1910 := h.h1910
      simp only [Setting1910] at h1910
      obtain ⟨-, h1 | h2 | h3alt⟩ := h1910
      ·
        exact absurd h3dvd (not_three_dvd_pow_sub_one h1.2.1)
      ·
        obtain ⟨x, hxM, hIOfeq⟩ := (bar2_IOf_shape_of_alt2 D h h42 h2).1
        have hL2 : IsL2 (Bar2 L) (S17.nOf L) := by
          rcases h2.2.2.2 with hL₂ | hSz
          · exact hL₂.1
          · have hodd : Odd (S17.nOf L) := by
              rw [S17.nOf_eq_of_isSz hSz.1]
              have hadm := hSz.1.admissible
              simp only [StatedLieAdmissible] at hadm
              exact hadm.2.2.2.2.1
            exact absurd h3dvd (not_three_dvd_pow_sub_one hodd)
        let L₂ : Subgroup G := CFSG.Quasithin.conjSubgroup L x
        have hXeq : conjClosure D.M L = L ⊔ L₂ := h2.1.symm.trans hIOfeq
        have hcal : L₂ ∈ calC D.M :=
          (conjSubgroup_mem_calC_and_ne h.hyp.hL.1 hxM hXeq h2.2.1).1
        have hne : L ≠ L₂ :=
          (conjSubgroup_mem_calC_and_ne h.hyp.hL.1 hxM hXeq h2.2.1).2.symm
        have hL₂L2 : IsL2 (Bar2 L₂) (S17.nOf L) := by
          change IsL2 (Bar2 (L.map (MulAut.conj x⁻¹).toMonoidHom)) (S17.nOf L)
          obtain ⟨e⟩ := uc22p20d_bar2_conj x⁻¹ L
          exact LieModel.of_mulEquiv e hL2
        have hnorm : L₂ ≤ normalizer (L : Set G) :=
          uc22p22u_calC_normalizes h.hyp.hL.1 hcal hne
        have hsup : E ≤ L ⊔ L₂ := by
          rw [← hXeq, ← hI]
          exact hEA.trans h.hA
        exact keyL2 L L₂ (S17.nOf L) h.hyp.hL.1 hcal hne hL2 hL₂L2 hnorm hsup
      ·
        have hXne : conjClosure D.M L ≠ L := by
          intro hXL
          have hq : CFSG.Open.IsQuasisimple (Bar2 (IOf D p L)) := by
            rw [hI, hXL]
            exact h.hyp.hL.1.2.2
          rcases h3alt.1 with ⟨A', B', gA, gB, ⟨f⟩, hA', hB'⟩ |
            ⟨A', B', gA, gB, ⟨f⟩, hA', hB'⟩
          · have : IsSimpleGroup A' :=
              LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hA'
            have : IsSimpleGroup B' :=
              LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hB'
            exact (CFSG.RankThree.PartTwo.Sec15.Proof1515.isEmpty_mulEquiv_prod_of_isQuasisimple
              (CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hq)).false f
          · have : IsSimpleGroup A' :=
              LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hA'
            have : IsSimpleGroup B' :=
              LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hB'
            exact (CFSG.RankThree.PartTwo.Sec15.Proof1515.isEmpty_mulEquiv_prod_of_isQuasisimple
              (CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hq)).false f
        obtain ⟨m, x, hxM, hXsup, -, hshape, -⟩ :=
          p42_alt2_of_ne h42 h.hyp.hp h.hyp.hL.1 hXne
        rcases hshape with hL₂ | hSz
        · have hL2 : IsL2 (Bar2 L) m := hL₂.1
          let L₂ : Subgroup G := CFSG.Quasithin.conjSubgroup L x
          have hcal : L₂ ∈ calC D.M :=
            (conjSubgroup_mem_calC_and_ne h.hyp.hL.1 hxM hXsup hXne).1
          have hne : L ≠ L₂ :=
            (conjSubgroup_mem_calC_and_ne h.hyp.hL.1 hxM hXsup hXne).2.symm
          have hL₂L2 : IsL2 (Bar2 L₂) m := by
            change IsL2 (Bar2 (L.map (MulAut.conj x⁻¹).toMonoidHom)) m
            obtain ⟨e⟩ := uc22p20d_bar2_conj x⁻¹ L
            exact LieModel.of_mulEquiv e hL2
          have hnorm : L₂ ≤ normalizer (L : Set G) :=
            uc22p22u_calC_normalizes h.hyp.hL.1 hcal hne
          have hsup : E ≤ L ⊔ L₂ := by
            rw [← hXsup, ← hI]
            exact hEA.trans h.hA
          exact keyL2 L L₂ m h.hyp.hL.1 hcal hne hL2 hL₂L2 hnorm hsup
        ·
          have hoddm : Odd m := by
            have hadm := hSz.1.admissible
            simp only [StatedLieAdmissible] at hadm
            exact hadm.2.2.2.2.1
          have hoddn : Odd (S17.nOf L) := by
            rw [S17.nOf_eq_of_isSz hSz.1]
            exact hoddm
          have hn2 : 2 < S17.nOf L := h3alt.2.1
          obtain ⟨k, hk⟩ := h3alt.2.2.1
          have hk0 : k ≠ 0 := by
            rintro rfl
            rw [hk] at hn2
            norm_num at hn2
          exact absurd hoddn (by
            rw [hk]
            exact Nat.not_odd_iff_even.mpr ((Nat.even_pow' hk0).mpr even_two))
  ·
    have h1910 := h.h1910
    simp only [Setting1910] at h1910
    have hodd : Odd (S17.nOf L) := by
      obtain ⟨-, h1 | h2 | h3alt⟩ := h1910
      · exact h1.2.1
      · by_contra hoddn
        have heven : Even (S17.nOf L) := Nat.not_odd_iff_even.mp hoddn
        have h3dvd : 3 ∣ 2 ^ S17.nOf L - 1 := three_dvd_of_even heven
        exfalso
        exact h3 ⟨Nat.prime_three, by
          rw [card_eq_of_isZModSq h.hAcard]
          exact dvd_mul_of_dvd_left h3dvd (2 ^ S17.nOf L - 1)⟩
      · have hn2 : 2 < S17.nOf L := h3alt.2.1
        obtain ⟨k, hk⟩ := h3alt.2.2.1
        have hk0 : k ≠ 0 := by
          rintro rfl
          rw [hk] at hn2
          norm_num at hn2
        have heven : Even (S17.nOf L) := by
          rw [hk]
          exact (Nat.even_pow' hk0).mpr even_two
        have h3dvd : 3 ∣ 2 ^ S17.nOf L - 1 := three_dvd_of_even heven
        exfalso
        exact h3 ⟨Nat.prime_three, by
          rw [card_eq_of_isZModSq h.hAcard]
          exact dvd_mul_of_dvd_left h3dvd (2 ^ S17.nOf L - 1)⟩
    have hjne : S17.jM D p ≠ 4 := by
      intro hj
      obtain ⟨K₁, K₂, -, -, -, -, -, -, hpow, hn2⟩ := hj4 hj
      obtain ⟨k, hk⟩ := hpow
      have hk0 : k ≠ 0 := by
        rintro rfl
        rw [hk] at hn2
        norm_num at hn2
      have heven : Even (S17.nOf L) := by
        rw [hk]
        exact (Nat.even_pow' hk0).mpr even_two
      have h3dvd : 3 ∣ 2 ^ S17.nOf L - 1 := three_dvd_of_even heven
      exact h3 ⟨Nat.prime_three, by
        rw [card_eq_of_isZModSq h.hAcard]
        exact dvd_mul_of_dvd_left h3dvd (2 ^ S17.nOf L - 1)⟩
    have hI : IOf D p L = conjClosure D.M L := by simp [IOf, hjne]
    have hrprime : r.Prime := h.hr.1
    have hrne3 : r ≠ 3 := by
      intro hr
      exact h3 (by simpa [hr] using h.hr)
    have hnpos : 0 < S17.nOf L := by
      obtain ⟨k, hk⟩ := hodd
      omega
    have hAodd : Odd (Nat.card A) := by
      rw [card_eq_of_isZModSq h.hAcard]
      exact (CFSG.Timmesfeld.Orders.odd_two_pow_sub_one hnpos).mul
        (CFSG.Timmesfeld.Orders.odd_two_pow_sub_one hnpos)
    have hrne2 : r ≠ 2 := by
      intro h2
      have h2dvd : 2 ∣ Nat.card A := by simpa [h2] using h.hr.2
      exact (Nat.not_even_iff_odd.mpr hAodd) (even_iff_two_dvd.mpr h2dvd)
    have hr5 : 5 < r := by
      by_contra hnot
      have hrle : r ≤ 5 := Nat.le_of_not_lt hnot
      have hle : 2 ≤ r := hrprime.two_le
      interval_cases r
      · exact hrne2 rfl
      · exact hrne3 rfl
      · norm_num at hrprime
      · exact h.hr5 rfl
    rcases h1910 with ⟨-, h1 | h2 | h3alt⟩
    · exact nineteen_twelve_sp4 D h h42 hI h1.1 hr5 E hEA hEel hEcard
    · exact nineteen_twelve_of_X_ne D h h42 hI h2.2.1 hr5 E hEA hEel hEcard
    · have hn2 : 2 < S17.nOf L := h3alt.2.1
      obtain ⟨k, hk⟩ := h3alt.2.2.1
      have hk0 : k ≠ 0 := by
        rintro rfl
        rw [hk] at hn2
        norm_num at hn2
      have heven : Even (S17.nOf L) := by
        rw [hk]
        exact (Nat.even_pow' hk0).mpr even_two
      exact absurd hodd (Nat.not_odd_iff_even.mpr heven)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
