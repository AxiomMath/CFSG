module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThirtySixAN3B
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThirtySixAFull
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThirtyFiveProof
public import CFSG.LocalAnalysis.SteinbergCCSQTKTwoCoreQuotient

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC6S846

variable {G : Type} [Group G] [Finite G]

theorem exists_elemAbelian_card_nine_of_mem_conjSet {D : Data G} {L K : Subgroup G} {n : ℕ}
    (hL : L ∈ calC D.M) (hK : K ∈ conjSetOf D.M L) (hshape : IsSU3 (Bar2 L) n)
    (hn : n = 3) :
    ∃ E : Subgroup G, E ≤ K ∧ IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  classical
  have hKC : K ∈ calC D.M := uc22p2214_calC_of_mem_conjSetOf hL hK
  have hshapeK : IsSU3 (Bar2 K) n := isSU3_bar2_of_mem_conjSet hK hshape
  have hodd : Odd n := by rw [hn]; decide
  have h2 : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 K)) :=
    two_le_pRank_three_of_isSU3 hshapeK hodd
  obtain ⟨E0, hE0K, hE0el, a, ha2, hE0card⟩ :=
    exists_elemAbelian_sq_lift_of_isSU3 (L := K) (q := 3) Nat.prime_three (by norm_num) h2
  have hE0p : IsPGroup 3 E0 := hE0el.isPGroup
  have hE0rank : 2 ≤ CFSG.Open.pRank 3 E0 := by
    have h := CFSG.SectionRank.le_pRank (p := 3) (by norm_num) (H := E0) (E := E0)
      le_rfl hE0el hE0card
    omega
  have h3dvd : 3 ∣ Nat.card E0 := by
    rw [hE0card]
    exact dvd_pow_self 3 (by omega)
  obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' (G := ↥E0) 3 h3dvd
  let X : Subgroup G := Subgroup.zpowers (x : G)
  have hXE0 : X ≤ E0 := Subgroup.zpowers_le.mpr x.2
  have hXcard : Nat.card X = 3 := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hxord]
  obtain ⟨E, hXE, hEE0, hEel, hEcard⟩ :=
    CFSG.GroupTheory.exists_isElemAbelian_card_sq_of_le_of_card_prime hE0p hE0rank hXE0 hXcard
  exact ⟨E, hEE0.trans hE0K, hEel, by simpa using hEcard⟩

theorem four_le_pRank_three_of_three_conj {D : Data G} {L : Subgroup G} {n : ℕ}
    (hL : L ∈ calC D.M) (hshape : IsSU3 (Bar2 L) n) (hn : n = 3)
    (hZcard : Nat.card (Subgroup.center (Bar2 L)) = 3)
    {K₁ K₂ K₃ : Subgroup G}
    (hK₁ : K₁ ∈ conjSetOf D.M L) (hK₂ : K₂ ∈ conjSetOf D.M L)
    (hK₃ : K₃ ∈ conjSetOf D.M L)
    (hne₁₂ : K₁ ≠ K₂) (hne₁₃ : K₁ ≠ K₃) (hne₂₃ : K₂ ≠ K₃) :
    4 ≤ CFSG.Open.pRank 3 D.M := by
  classical
  subst hn
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨E₁, hE₁K₁, hE₁el, hE₁card⟩ :=
    exists_elemAbelian_card_nine_of_mem_conjSet hL hK₁ hshape rfl
  obtain ⟨E₂, hE₂K₂, hE₂el, hE₂card⟩ :=
    exists_elemAbelian_card_nine_of_mem_conjSet hL hK₂ hshape rfl
  obtain ⟨E₃, hE₃K₃, hE₃el, hE₃card⟩ :=
    exists_elemAbelian_card_nine_of_mem_conjSet hL hK₃ hshape rfl
  have hK₁C : K₁ ∈ calC D.M := uc22p2214_calC_of_mem_conjSetOf hL hK₁
  have hK₂C : K₂ ∈ calC D.M := uc22p2214_calC_of_mem_conjSetOf hL hK₂
  have hK₃C : K₃ ∈ calC D.M := uc22p2214_calC_of_mem_conjSetOf hL hK₃
  have hK₁M : K₁ ≤ D.M := hK₁C.1.le
  have hK₂M : K₂ ≤ D.M := hK₂C.1.le
  have hK₃M : K₃ ≤ D.M := hK₃C.1.le
  let π : ↥D.M →* Bar2 D.M := QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)
  let Eb₁ : Subgroup (Bar2 D.M) := (E₁.subgroupOf D.M).map π
  let Eb₂ : Subgroup (Bar2 D.M) := (E₂.subgroupOf D.M).map π
  let Eb₃ : Subgroup (Bar2 D.M) := (E₃.subgroupOf D.M).map π
  let C₁ : Subgroup (Bar2 D.M) := barImage D.M K₁
  let C₂ : Subgroup (Bar2 D.M) := barImage D.M K₂
  let C₃ : Subgroup (Bar2 D.M) := barImage D.M K₃
  have hE₁M : E₁ ≤ D.M := hE₁K₁.trans hK₁M
  have hE₂M : E₂ ≤ D.M := hE₂K₂.trans hK₂M
  have hE₃M : E₃ ≤ D.M := hE₃K₃.trans hK₃M
  have hEb₁le : Eb₁ ≤ C₁ := Subgroup.map_mono (Subgroup.subgroupOf_mono D.M hE₁K₁)
  have hEb₂le : Eb₂ ≤ C₂ := Subgroup.map_mono (Subgroup.subgroupOf_mono D.M hE₂K₂)
  have hEb₃le : Eb₃ ≤ C₃ := Subgroup.map_mono (Subgroup.subgroupOf_mono D.M hE₃K₃)
  have hker : π.ker = CFSG.pCore 2 ↥D.M := QuotientGroup.ker_mk' _
  have hnotdvdKer : ¬ 3 ∣ Nat.card π.ker := by
    rw [hker]
    exact CFSG.LocalAnalysis.SQTKTwoCoreQuotient.not_dvd_card_pCore_two
      Nat.prime_three (by norm_num)
  have hcardEb₁ : Nat.card Eb₁ = 9 := by
    show Nat.card ((E₁.subgroupOf D.M).map π) = 9
    have hsub : Nat.card (E₁.subgroupOf D.M) = 9 :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE₁M).toEquiv).trans hE₁card
    have hdisj : Disjoint (E₁.subgroupOf D.M) π.ker := by
      refine Subgroup.disjoint_of_coprime_natCard ?_
      rw [hsub]
      exact (Nat.prime_three.coprime_iff_not_dvd.mpr hnotdvdKer).pow_left 2
    rw [CFSG.LocalAnalysis.UniquenessCase.UC6S846.card_map_of_disjoint_ker π _ hdisj, hsub]
  have hcardEb₂ : Nat.card Eb₂ = 9 := by
    show Nat.card ((E₂.subgroupOf D.M).map π) = 9
    have hsub : Nat.card (E₂.subgroupOf D.M) = 9 :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE₂M).toEquiv).trans hE₂card
    have hdisj : Disjoint (E₂.subgroupOf D.M) π.ker := by
      refine Subgroup.disjoint_of_coprime_natCard ?_
      rw [hsub]
      exact (Nat.prime_three.coprime_iff_not_dvd.mpr hnotdvdKer).pow_left 2
    rw [CFSG.LocalAnalysis.UniquenessCase.UC6S846.card_map_of_disjoint_ker π _ hdisj, hsub]
  have hcardEb₃ : Nat.card Eb₃ = 9 := by
    show Nat.card ((E₃.subgroupOf D.M).map π) = 9
    have hsub : Nat.card (E₃.subgroupOf D.M) = 9 :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE₃M).toEquiv).trans hE₃card
    have hdisj : Disjoint (E₃.subgroupOf D.M) π.ker := by
      refine Subgroup.disjoint_of_coprime_natCard ?_
      rw [hsub]
      exact (Nat.prime_three.coprime_iff_not_dvd.mpr hnotdvdKer).pow_left 2
    rw [CFSG.LocalAnalysis.UniquenessCase.UC6S846.card_map_of_disjoint_ker π _ hdisj, hsub]
  have hEb₁el : IsElemAbelian 3 Eb₁ := CFSG.SectionRank.isElemAbelian_map (hE₁el.subgroupOf D.M) π
  have hEb₂el : IsElemAbelian 3 Eb₂ := CFSG.SectionRank.isElemAbelian_map (hE₂el.subgroupOf D.M) π
  have hEb₃el : IsElemAbelian 3 Eb₃ := CFSG.SectionRank.isElemAbelian_map (hE₃el.subgroupOf D.M) π
  have hc₁₂ : ∀ a : Bar2 D.M, a ∈ Eb₁ → ∀ b : Bar2 D.M, b ∈ Eb₂ → a * b = b * a := by
    intro a ha b hb
    exact uc22p22l_barImage_commute hK₁C hK₂C hne₁₂ a (hEb₁le ha) b (hEb₂le hb)
  have hc₁₃ : ∀ a : Bar2 D.M, a ∈ Eb₁ → ∀ b : Bar2 D.M, b ∈ Eb₃ → a * b = b * a := by
    intro a ha b hb
    exact uc22p22l_barImage_commute hK₁C hK₃C hne₁₃ a (hEb₁le ha) b (hEb₃le hb)
  have hc₂₃ : ∀ a : Bar2 D.M, a ∈ Eb₂ → ∀ b : Bar2 D.M, b ∈ Eb₃ → a * b = b * a := by
    intro a ha b hb
    exact uc22p22l_barImage_commute hK₂C hK₃C hne₂₃ a (hEb₂le ha) b (hEb₃le hb)
  have hcC₁₂ : ∀ a : Bar2 D.M, a ∈ C₁ → ∀ b : Bar2 D.M, b ∈ C₂ → a * b = b * a :=
    fun a ha b hb => uc22p22l_barImage_commute hK₁C hK₂C hne₁₂ a ha b hb
  have hcC₁₃ : ∀ a : Bar2 D.M, a ∈ C₁ → ∀ b : Bar2 D.M, b ∈ C₃ → a * b = b * a :=
    fun a ha b hb => uc22p22l_barImage_commute hK₁C hK₃C hne₁₃ a ha b hb
  have hcC₂₃ : ∀ a : Bar2 D.M, a ∈ C₂ → ∀ b : Bar2 D.M, b ∈ C₃ → a * b = b * a :=
    fun a ha b hb => uc22p22l_barImage_commute hK₂C hK₃C hne₂₃ a ha b hb
  have hC₂C₁ : C₂ ≤ Subgroup.centralizer (C₁ : Set (Bar2 D.M)) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact hcC₁₂ b hb a ha
  have hC₃C₁ : C₃ ≤ Subgroup.centralizer (C₁ : Set (Bar2 D.M)) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact hcC₁₃ b hb a ha
  have hC₁cent : C₁ ≤ Subgroup.centralizer ((C₂ ⊔ C₃ : Subgroup (Bar2 D.M)) : Set _) :=
    Subgroup.le_centralizer_iff.mp (sup_le hC₂C₁ hC₃C₁)
  have hcenterC₁ : Nat.card (Subgroup.center C₁) = 3 := by
    obtain ⟨e⟩ := s13_bar_equiv hK₁C
    rw [← Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    obtain ⟨g, -, hgK⟩ := hK₁
    rw [hgK, CFSG.LocalAnalysis.UniquenessCase.UC6S846.card_center_bar2_map
      (MulAut.conj g) L, hZcard]
  have hcenterC₂ : Nat.card (Subgroup.center C₂) = 3 := by
    obtain ⟨e⟩ := s13_bar_equiv hK₂C
    rw [← Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    obtain ⟨g, -, hgK⟩ := hK₂
    rw [hgK, CFSG.LocalAnalysis.UniquenessCase.UC6S846.card_center_bar2_map
      (MulAut.conj g) L, hZcard]
  have hcenterC₃ : Nat.card (Subgroup.center C₃) = 3 := by
    obtain ⟨e⟩ := s13_bar_equiv hK₃C
    rw [← Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    obtain ⟨g, -, hgK⟩ := hK₃
    rw [hgK, CFSG.LocalAnalysis.UniquenessCase.UC6S846.card_center_bar2_map
      (MulAut.conj g) L, hZcard]
  let Z₁ : Subgroup (Bar2 D.M) := (Subgroup.center C₁).map C₁.subtype
  have hcardZ₁ : Nat.card Z₁ = 3 := by
    show Nat.card ((Subgroup.center C₁).map C₁.subtype) = 3
    rw [Subgroup.card_map_of_injective C₁.subtype_injective, hcenterC₁]
  have hinter₁ : Nat.card ↥(Eb₁ ⊓ (Eb₂ ⊔ Eb₃)) ≤ 3 := by
    have hle : Eb₁ ⊓ (Eb₂ ⊔ Eb₃) ≤ Z₁ := by
      intro x hx
      refine Subgroup.mem_map.mpr ⟨⟨x, hEb₁le hx.1⟩, ?_, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      have hxSup : x ∈ (C₂ ⊔ C₃ : Subgroup (Bar2 D.M)) :=
        (sup_le (le_trans hEb₂le le_sup_left) (le_trans hEb₃le le_sup_right) :
          Eb₂ ⊔ Eb₃ ≤ C₂ ⊔ C₃) hx.2
      exact (Subgroup.mem_centralizer_iff.mp (hC₁cent y.2) x hxSup).symm
    have h1 : Nat.card ↥(Eb₁ ⊓ (Eb₂ ⊔ Eb₃)) ≤ Nat.card Z₁ :=
      Subgroup.card_le_of_le hle
    omega
  have hC₁C₂ : C₁ ≤ Subgroup.centralizer (C₂ : Set (Bar2 D.M)) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (hcC₁₂ a ha b hb).symm
  have hC₃C₂ : C₃ ≤ Subgroup.centralizer (C₂ : Set (Bar2 D.M)) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact hcC₂₃ b hb a ha
  have hC₂cent : C₂ ≤ Subgroup.centralizer ((C₁ ⊔ C₃ : Subgroup (Bar2 D.M)) : Set _) :=
    Subgroup.le_centralizer_iff.mp (sup_le hC₁C₂ hC₃C₂)
  let Z₂ : Subgroup (Bar2 D.M) := (Subgroup.center C₂).map C₂.subtype
  have hcardZ₂ : Nat.card Z₂ = 3 := by
    show Nat.card ((Subgroup.center C₂).map C₂.subtype) = 3
    rw [Subgroup.card_map_of_injective C₂.subtype_injective, hcenterC₂]
  have hinter₂ : Nat.card ↥(Eb₂ ⊓ (Eb₁ ⊔ Eb₃)) ≤ 3 := by
    have hle : Eb₂ ⊓ (Eb₁ ⊔ Eb₃) ≤ Z₂ := by
      intro x hx
      refine Subgroup.mem_map.mpr ⟨⟨x, hEb₂le hx.1⟩, ?_, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      have hxSup : x ∈ (C₁ ⊔ C₃ : Subgroup (Bar2 D.M)) :=
        (sup_le (le_trans hEb₁le le_sup_left) (le_trans hEb₃le le_sup_right) :
          Eb₁ ⊔ Eb₃ ≤ C₁ ⊔ C₃) hx.2
      exact (Subgroup.mem_centralizer_iff.mp (hC₂cent y.2) x hxSup).symm
    have h1 : Nat.card ↥(Eb₂ ⊓ (Eb₁ ⊔ Eb₃)) ≤ Nat.card Z₂ :=
      Subgroup.card_le_of_le hle
    omega
  have h4bar : 4 ≤ CFSG.Open.pRank 3 (Eb₁ ⊔ Eb₂ ⊔ Eb₃) :=
    pRank_four_of_three_commuting_squares Nat.prime_three hEb₁el hEb₂el hEb₃el
      (by simpa using hcardEb₁) (by simpa using hcardEb₂) (by simpa using hcardEb₃)
      hc₁₂ hc₁₃ hc₂₃ hinter₂ hinter₁
  have h4top : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 D.M)) :=
    h4bar.trans (CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) le_top)
  have hnotdvd : ¬ 3 ∣ Nat.card (CFSG.pCore 2 ↥D.M) :=
    CFSG.LocalAnalysis.SQTKTwoCoreQuotient.not_dvd_card_pCore_two Nat.prime_three (by norm_num)
  have hquot := CFSG.SectionRank.pRank_quotient_eq (p := 3) (G := ↥D.M)
    (N := CFSG.pCore 2 ↥D.M) hnotdvd
  have htop : CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 D.M)) =
      CFSG.Open.pRank 3 D.M := by
    rw [show CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 D.M)) =
        CFSG.Open.pRank 3 (⊤ : Subgroup ↥D.M) from hquot]
    exact (CFSG.SectionRank.pRank_eq_pRank_top_subgroup D.M).symm
  rwa [htop] at h4top

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
