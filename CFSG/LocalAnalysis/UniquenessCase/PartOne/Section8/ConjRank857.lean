module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.ConjSetCard
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.List857
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.ThreeConjugateRank
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214c
public import CFSG.GroupTheory.CommutingProductFixedSubgroup
public import CFSG.RankThree.GroupTheory.SteinbergBYAschCoreConjugacy

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22

theorem four_le_pRank_three_of_three_commuting_of_center {H : Type*} [Group H] [Finite H]
    {A₀ A₁ A₂ : Subgroup H}
    (hcomm₀₁ : ∀ x ∈ A₀, ∀ y ∈ A₁, x * y = y * x)
    (hcomm₀₂ : ∀ x ∈ A₀, ∀ y ∈ A₂, x * y = y * x)
    (hcomm₁₂ : ∀ x ∈ A₁, ∀ y ∈ A₂, x * y = y * x)
    (hc₀ : Nat.card (Subgroup.center ↥A₀) ≤ 3)
    (hc₁ : Nat.card (Subgroup.center ↥A₁) ≤ 3)
    (hc₂ : Nat.card (Subgroup.center ↥A₂) ≤ 3)
    (hr₀ : 2 ≤ CFSG.Open.pRank 3 A₀)
    (hr₁ : 2 ≤ CFSG.Open.pRank 3 A₁)
    (hr₂ : 2 ≤ CFSG.Open.pRank 3 A₂) :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup H) := by
  classical
  have hcent₀₁ : A₀ ⊓ A₁ ≤ (Subgroup.center ↥A₀).map A₀.subtype := by
    rintro x ⟨hx₀, hx₁⟩
    refine ⟨⟨x, hx₀⟩, ?_, rfl⟩
    refine Subgroup.mem_center_iff.mpr ?_
    intro a
    exact Subtype.ext (hcomm₀₁ a a.2 x hx₁)
  have hcard₀₁ : Nat.card ↥(A₀ ⊓ A₁) ≤ 3 := by
    have hle := Subgroup.card_le_of_le hcent₀₁
    rw [Subgroup.card_map_of_injective A₀.subtype_injective] at hle
    exact hle.trans hc₀
  have hcommW₂ : ∀ x ∈ A₀ ⊔ A₁, ∀ y ∈ A₂, x * y = y * x := by
    intro x hx y hy
    obtain ⟨a, ha, b, hb, rfl⟩ :=
      CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hcomm₀₁ (g := x) hx
    calc (a * b) * y = a * (b * y) := by rw [mul_assoc]
      _ = a * (y * b) := by rw [hcomm₁₂ b hb y hy]
      _ = (a * y) * b := by rw [← mul_assoc]
      _ = (y * a) * b := by rw [hcomm₀₂ a ha y hy]
      _ = y * (a * b) := by rw [mul_assoc]
  have hcent₂ : A₂ ⊓ (A₀ ⊔ A₁) ≤ (Subgroup.center ↥A₂).map A₂.subtype := by
    rintro x ⟨hx₂, hxW⟩
    refine ⟨⟨x, hx₂⟩, ?_, rfl⟩
    refine Subgroup.mem_center_iff.mpr ?_
    intro a
    exact Subtype.ext (hcommW₂ x hxW a a.2).symm
  have hcard₂ : Nat.card ↥(A₂ ⊓ (A₀ ⊔ A₁)) ≤ 3 := by
    have hle := Subgroup.card_le_of_le hcent₂
    rw [Subgroup.card_map_of_injective A₂.subtype_injective] at hle
    exact hle.trans hc₂
  exact four_le_pRank_three_of_three_commuting hcomm₀₁ hcomm₀₂ hcomm₁₂ hcard₀₁ hcard₂
    hr₀ hr₁ hr₂

theorem four_le_pRank_three_of_two_commuting_of_not_three_dvd_center {H : Type*}
    [Group H] [Finite H] {A B : Subgroup H}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hZA : ¬ 3 ∣ Nat.card (Subgroup.center ↥A))
    (hrA : 2 ≤ CFSG.Open.pRank 3 A) (hrB : 2 ≤ CFSG.Open.pRank 3 B) :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup H) := by
  classical
  obtain ⟨E, hEA, hEel, hEcard⟩ :=
    CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) A
  obtain ⟨F, hFB, hFel, hFcard⟩ :=
    CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) B
  have hdisj : ∀ x ∈ E, x ∈ F → x = 1 := by
    intro x hxE hxF
    by_contra hx1
    have hx3 : x ^ 3 = 1 := hEel.2 x hxE
    have hxod : orderOf x = 3 := by
      have hdvd : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one hx3
      rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hx1
      · exact h
    have hxZ : x ∈ (Subgroup.center ↥A).map A.subtype := by
      exact Subgroup.mem_map.mpr ⟨⟨x, hEA hxE⟩,
        Subgroup.mem_center_iff.mpr (fun a => Subtype.ext (hcomm a a.2 x (hFB hxF))), rfl⟩
    have hzle : Subgroup.zpowers x ≤ (Subgroup.center ↥A).map A.subtype :=
      Subgroup.zpowers_le.mpr hxZ
    have hdvd : 3 ∣ Nat.card ↥((Subgroup.center ↥A).map A.subtype) := by
      have h0 : Nat.card ↥(Subgroup.zpowers x) ∣
          Nat.card ↥((Subgroup.center ↥A).map A.subtype) :=
        Subgroup.card_dvd_of_le hzle
      rwa [Nat.card_zpowers, hxod] at h0
    rw [Subgroup.card_map_of_injective A.subtype_injective] at hdvd
    exact hZA hdvd
  have hbot : E ⊓ F = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    exact hdisj x hx.1 hx.2
  have hcommEF : ∀ a ∈ E, ∀ b ∈ F, a * b = b * a :=
    fun a ha b hb => hcomm a (hEA ha) b (hFB hb)
  have hEFel : CFSG.Open.IsElemAbelian 3 (E ⊔ F) :=
    hEel.sup_of_commute hFel hcommEF
  have hsupcard : Nat.card ↥(E ⊔ F) = Nat.card E * Nat.card F := by
    have hprod := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute E F hcommEF).1
    rw [hbot, Subgroup.card_bot, mul_one] at hprod
    exact hprod
  have hbig : 81 ≤ Nat.card ↥(E ⊔ F) := by
    rw [hsupcard, hEcard, hFcard, ← pow_add]
    calc 81 = 3 ^ 4 := by norm_num
      _ ≤ 3 ^ (CFSG.Open.pRank 3 A + CFSG.Open.pRank 3 B) :=
        Nat.pow_le_pow_right (by norm_num : 0 < 3) (by omega)
  have hWelcard : Nat.card ↥(E ⊔ F) = 3 ^ CFSG.Open.pRank 3 (E ⊔ F) :=
    CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian Nat.prime_three hEFel
  have h4 : 4 ≤ CFSG.Open.pRank 3 (E ⊔ F) := by
    apply (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp
    calc 3 ^ 4 = 81 := by norm_num
      _ ≤ Nat.card ↥(E ⊔ F) := hbig
      _ = 3 ^ CFSG.Open.pRank 3 (E ⊔ F) := hWelcard
  exact h4.trans (CFSG.SectionRank.pRank_mono (by norm_num : 1 < 3) le_top)

theorem pRank_three_conj_of_mem_conjSetOf {G : Type} [Group G] [Finite G]
    {M L K : Subgroup G} (hK : K ∈ conjSetOf M L) :
    CFSG.Open.pRank 3 K = CFSG.Open.pRank 3 L := by
  obtain ⟨g, -, rfl⟩ := hK
  exact CFSG.RankThree.GroupTheory.SteinbergBY.assembly_pRank_map_mulEquiv
    (by norm_num : 1 < 3) (MulAut.conj g) L

theorem card_center_bar2_conj_of_mem_conjSetOf {G : Type} [Group G] [Finite G]
    {M L K : Subgroup G} (hK : K ∈ conjSetOf M L) :
    Nat.card (Subgroup.center (Bar2 K)) = Nat.card (Subgroup.center (Bar2 L)) := by
  obtain ⟨g, -, rfl⟩ := hK
  obtain ⟨e⟩ := uc22p20d_bar2_conj g L
  exact (Nat.card_congr (Subgroup.centerCongr e).toEquiv).symm

theorem not_three_dvd_center_barImage_of_mem_conjSetOf {G : Type} [Group G] [Finite G]
    {M L K : Subgroup G} (hL : L ∈ calC M) (hK : K ∈ conjSetOf M L)
    (hcenter : ¬ 3 ∣ Nat.card (Subgroup.center (Bar2 L))) :
    ¬ 3 ∣ Nat.card (Subgroup.center ↥(barImage M K)) := by
  have hKC : K ∈ calC M := uc22p2214_calC_of_mem_conjSetOf hL hK
  have hZK : ¬ 3 ∣ Nat.card (Subgroup.center (Bar2 K)) := by
    rw [card_center_bar2_conj_of_mem_conjSetOf hK]
    exact hcenter
  obtain ⟨e, -⟩ := uc22p22l_barImage_equiv hKC
  rwa [← Nat.card_congr (Subgroup.centerCongr e).toEquiv]

theorem four_le_pRank_three_of_two_conj_of_not_three_dvd_center {G : Type} [Group G]
    [Finite G] {M L L1 L2 : Subgroup G}
    (hL : L ∈ calC M)
    (h1 : L1 ∈ conjSetOf M L) (h2 : L2 ∈ conjSetOf M L) (h12 : L1 ≠ L2)
    (hr : CFSG.Open.pRank 3 L = 2)
    (hcenter : ¬ 3 ∣ Nat.card (Subgroup.center (Bar2 L))) :
    4 ≤ CFSG.Open.pRank 3 M := by
  have hL1 : L1 ∈ calC M := uc22p2214_calC_of_mem_conjSetOf hL h1
  have hL2 : L2 ∈ calC M := uc22p2214_calC_of_mem_conjSetOf hL h2
  have hZ1 : ¬ 3 ∣ Nat.card (Subgroup.center ↥(barImage M L1)) :=
    not_three_dvd_center_barImage_of_mem_conjSetOf hL h1 hcenter
  have hrank1 : 2 ≤ CFSG.Open.pRank 3 (barImage M L1) := by
    obtain ⟨e, -⟩ := uc22p22l_barImage_equiv hL1
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 3) (barImage M L1)]
    rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e]
    rw [pRank_bar2_eq_of_odd (Y := L1) Nat.prime_three (by norm_num)]
    rw [pRank_three_conj_of_mem_conjSetOf h1, hr]
  have hrank2 : 2 ≤ CFSG.Open.pRank 3 (barImage M L2) := by
    obtain ⟨e, -⟩ := uc22p22l_barImage_equiv hL2
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 3) (barImage M L2)]
    rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e]
    rw [pRank_bar2_eq_of_odd (Y := L2) Nat.prime_three (by norm_num)]
    rw [pRank_three_conj_of_mem_conjSetOf h2, hr]
  have hcomm : ∀ x ∈ barImage M L1, ∀ y ∈ barImage M L2, x * y = y * x :=
    uc22p22l_barImage_commute (L := M) hL1 hL2 h12
  have hmain : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 M)) :=
    four_le_pRank_three_of_two_commuting_of_not_three_dvd_center hcomm hZ1 hrank1 hrank2
  rwa [pRank_bar2_eq_of_odd (Y := M) Nat.prime_three (by norm_num)] at hmain

theorem four_le_pRank_three_of_three_conj_of_center {G : Type} [Group G] [Finite G]
    {M L L1 L2 L3 : Subgroup G}
    (hL : L ∈ calC M)
    (h1 : L1 ∈ conjSetOf M L) (h2 : L2 ∈ conjSetOf M L) (h3 : L3 ∈ conjSetOf M L)
    (h12 : L1 ≠ L2) (h13 : L1 ≠ L3) (h23 : L2 ≠ L3)
    (hr : CFSG.Open.pRank 3 L = 2)
    (hcenter : Nat.card (Subgroup.center (Bar2 L)) ≤ 3) :
    4 ≤ CFSG.Open.pRank 3 M := by
  have hL1 : L1 ∈ calC M := uc22p2214_calC_of_mem_conjSetOf hL h1
  have hL2 : L2 ∈ calC M := uc22p2214_calC_of_mem_conjSetOf hL h2
  have hL3 : L3 ∈ calC M := uc22p2214_calC_of_mem_conjSetOf hL h3
  have hcenter_eq : ∀ {K : Subgroup G}, K ∈ conjSetOf M L →
      Nat.card (Subgroup.center (Bar2 K)) = Nat.card (Subgroup.center (Bar2 L)) :=
    fun hK => card_center_bar2_conj_of_mem_conjSetOf hK
  have hZ1 : Nat.card (Subgroup.center ↥(barImage M L1)) ≤ 3 := by
    obtain ⟨e, -⟩ := uc22p22l_barImage_equiv hL1
    rw [← Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    rw [hcenter_eq h1]
    exact hcenter
  have hZ2 : Nat.card (Subgroup.center ↥(barImage M L2)) ≤ 3 := by
    obtain ⟨e, -⟩ := uc22p22l_barImage_equiv hL2
    rw [← Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    rw [hcenter_eq h2]
    exact hcenter
  have hZ3 : Nat.card (Subgroup.center ↥(barImage M L3)) ≤ 3 := by
    obtain ⟨e, -⟩ := uc22p22l_barImage_equiv hL3
    rw [← Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    rw [hcenter_eq h3]
    exact hcenter
  have hrank1 : 2 ≤ CFSG.Open.pRank 3 (barImage M L1) := by
    obtain ⟨e, -⟩ := uc22p22l_barImage_equiv hL1
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 3) (barImage M L1)]
    rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e]
    rw [pRank_bar2_eq_of_odd (Y := L1) Nat.prime_three (by norm_num)]
    rw [pRank_three_conj_of_mem_conjSetOf h1, hr]
  have hrank2 : 2 ≤ CFSG.Open.pRank 3 (barImage M L2) := by
    obtain ⟨e, -⟩ := uc22p22l_barImage_equiv hL2
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 3) (barImage M L2)]
    rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e]
    rw [pRank_bar2_eq_of_odd (Y := L2) Nat.prime_three (by norm_num)]
    rw [pRank_three_conj_of_mem_conjSetOf h2, hr]
  have hrank3 : 2 ≤ CFSG.Open.pRank 3 (barImage M L3) := by
    obtain ⟨e, -⟩ := uc22p22l_barImage_equiv hL3
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 3) (barImage M L3)]
    rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e]
    rw [pRank_bar2_eq_of_odd (Y := L3) Nat.prime_three (by norm_num)]
    rw [pRank_three_conj_of_mem_conjSetOf h3, hr]
  have hcomm12 : ∀ x ∈ barImage M L1, ∀ y ∈ barImage M L2, x * y = y * x :=
    uc22p22l_barImage_commute (L := M) hL1 hL2 h12
  have hcomm13 : ∀ x ∈ barImage M L1, ∀ y ∈ barImage M L3, x * y = y * x :=
    uc22p22l_barImage_commute (L := M) hL1 hL3 h13
  have hcomm23 : ∀ x ∈ barImage M L2, ∀ y ∈ barImage M L3, x * y = y * x :=
    uc22p22l_barImage_commute (L := M) hL2 hL3 h23
  have hmain : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 M)) :=
    four_le_pRank_three_of_three_commuting_of_center hcomm12 hcomm13 hcomm23
      hZ1 hZ2 hZ3 hrank1 hrank2 hrank3
  rwa [pRank_bar2_eq_of_odd (Y := M) Nat.prime_three (by norm_num)] at hmain

theorem four_le_pRank_three_of_three_conj_list857_of_center {G : Type} [Group G] [Finite G]
    {M L L1 L2 L3 : Subgroup G}
    (hL : L ∈ calC M)
    (h1 : L1 ∈ conjSetOf M L) (h2 : L2 ∈ conjSetOf M L) (h3 : L3 ∈ conjSetOf M L)
    (h12 : L1 ≠ L2) (h13 : L1 ≠ L3) (h23 : L2 ≠ L3)
    (hr : CFSG.Open.pRank 3 L = 2)
    (hlist : List857 (Bar2 L))
    (hcenter : Nat.card (Subgroup.center (Bar2 L)) ≤ 3) :
    4 ≤ CFSG.Open.pRank 3 M :=
  four_le_pRank_three_of_three_conj_of_center hL h1 h2 h3 h12 h13 h23 hr hcenter

theorem center_card_le_three_of_threeCover {X : Type} [Group X]
    {S : ∀ (Y : Type) [Group Y], Prop}
    (h : CFSG.LocalAnalysis.UniquenessCase.UCK.ThreeCover S X) :
    Nat.card (Subgroup.center X) ≤ 3 := by
  have := h.2.1
  omega

theorem four_le_pRank_three_of_three_conj_list857_of_cover {G : Type} [Group G] [Finite G]
    {M L L1 L2 L3 : Subgroup G}
    (hL : L ∈ calC M)
    (h1 : L1 ∈ conjSetOf M L) (h2 : L2 ∈ conjSetOf M L) (h3 : L3 ∈ conjSetOf M L)
    (h12 : L1 ≠ L2) (h13 : L1 ≠ L3) (h23 : L2 ≠ L3)
    (hcover : F08.IsA6Z3 (Bar2 L) ∨ F08.IsA7Z3 (Bar2 L) ∨ F08.IsM22Z3 (Bar2 L)) :
    4 ≤ CFSG.Open.pRank 3 M :=
  four_le_pRank_three_of_three_conj hL h1 h2 h3 h12 h13 h23 hcover

theorem ncard_conjSetOf_le_two_of_cover {G : Type} [Group G] [Finite G]
    {M L : Subgroup G} (hL : L ∈ calC M)
    (hcover : F08.IsA6Z3 (Bar2 L) ∨ F08.IsA7Z3 (Bar2 L) ∨ F08.IsM22Z3 (Bar2 L))
    (hm3 : CFSG.Open.pRank 3 M ≤ 3) :
    (conjSetOf M L).ncard ≤ 2 :=
  ncard_conjSetOf_le_two_of_three_conj_rank
    (fun L₁ h1 L₂ h2 L₃ h3 h12 h13 h23 =>
      four_le_pRank_three_of_three_conj_list857_of_cover hL h1 h2 h3 h12 h13 h23 hcover)
    hm3

theorem ncard_conjSetOf_le_two_of_list857_of_center {G : Type} [Group G] [Finite G]
    {M L : Subgroup G}
    (hL : L ∈ calC M) (hr : CFSG.Open.pRank 3 L = 2) (hlist : List857 (Bar2 L))
    (hcenter : Nat.card (Subgroup.center (Bar2 L)) ≤ 3)
    (hm3 : CFSG.Open.pRank 3 M ≤ 3) :
    (conjSetOf M L).ncard ≤ 2 :=
  ncard_conjSetOf_le_two_of_three_conj_rank
    (fun L₁ h1 L₂ h2 L₃ h3 h12 h13 h23 =>
      four_le_pRank_three_of_three_conj_list857_of_center hL h1 h2 h3 h12 h13 h23 hr hlist
        hcenter)
    hm3

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
