module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8U37
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8KCaseTwoA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8KCaseTwoB
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartOne.CTP.StrongPGlue
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC22.F09 (Hbar9 img9 L9 Lbar9 IsSL2Cover Hyp91)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G] [Finite G]

theorem c8k_inner_on_shat (D : Data G) {Y H C : Subgroup G} (hY : Y = H ⊓ D.M) (hCY : C ≤ Y)
    (hCn : (C.subgroupOf Y).Normal) (hC3 : ¬ 3 ∣ Nat.card C) (hP : C8P0 Y C) {e : ℕ}
    (he : 1 ≤ e) (hS : IsSL2Cover ↥(img9 H (Opp 3 Y)) 7 e) {n : ↥H} (hn : (n : G) ∈ D.M) :
    ∃ s ∈ img9 H (Opp 3 Y), ∀ x ∈ img9 H (Opp 3 Y),
      (n : Hbar9 H) * x * (n : Hbar9 H)⁻¹ = s * x * s⁻¹ := by
  have hYH : Y ≤ H := hY ▸ inf_le_left
  have hnY : (n : G) ∈ Y := hY ▸ ⟨n.2, hn⟩
  obtain ⟨x, hx, c, hc, hxc⟩ := c8k_mem_opp_mul hCY hP (n : G) hnY
  have hxY : x ∈ Y := c8k_opp_le Y hx
  have hcY : c ∈ Y := hCY hc
  let xH : ↥H := ⟨x, hYH hxY⟩
  let cH : ↥H := ⟨c, hYH hcY⟩
  have hn' : n = xH * cH := Subtype.ext hxc
  have hxE : (xH : Hbar9 H) ∈ img9 H (Opp 3 Y) :=
    Subgroup.mem_map.mpr ⟨xH, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  refine ⟨(xH : Hbar9 H), hxE, fun y hy => ?_⟩
  have hcy := c8k_c_centralizes hYH hCY hCn hC3 he hS (c := cH) hc y hy
  rw [hn', QuotientGroup.mk_mul]
  calc (xH : Hbar9 H) * (cH : Hbar9 H) * y * ((xH : Hbar9 H) * (cH : Hbar9 H))⁻¹
      = (xH : Hbar9 H) * ((cH : Hbar9 H) * y) * (cH : Hbar9 H)⁻¹ * (xH : Hbar9 H)⁻¹ := by group
    _ = (xH : Hbar9 H) * y * (xH : Hbar9 H)⁻¹ := by rw [hcy]; group

theorem c8k_alt_two_false (D : Data G) (hse : IsStronglyPEmbedded 3 D.M) (hu37 : U37Outer)
    {Y H C : Subgroup G} {d : G} (hY : Y = H ⊓ D.M) (h91 : Hyp91 D Y H (zpowers d))
    (hCY : C ≤ Y) (hCn : (C.subgroupOf Y).Normal) (hC3 : ¬ 3 ∣ Nat.card C)
    (hP : C8P0 Y C) (hd3 : orderOf d = 3) {e : ℕ} (he : 1 ≤ e)
    (hL : LieModel (Lbar9 Y H) .PSU 3 7 e)
    (hS : IsSL2Cover ↥(Opp 3 (img9 H (H ⊓ D.M) ⊓ img9 H (L9 Y H))) 7 e) : False := by
  have hYH : Y ≤ H := hY ▸ inf_le_left
  rw [c8k_shat_eq D hY] at hS
  have he1 : e = 1 := c8k_cover_e_eq_one hYH hCY hC3 hP he hS
  subst he1
  have hdO : d ∈ Opp 3 Y := h91.2.2.1 (Subgroup.mem_zpowers d)
  have hdY : d ∈ Y := c8k_opp_le Y hdO
  let dH : ↥H := ⟨d, hYH hdY⟩
  have hdH3 : orderOf dH = 3 := by rw [← hd3]; exact Subgroup.orderOf_mk d _
  have hdE : (dH : Hbar9 H) ∈ img9 H (Opp 3 Y) :=
    Subgroup.mem_map.mpr ⟨dH, Subgroup.mem_subgroupOf.mpr hdO, rfl⟩
  have hdo : orderOf (dH : Hbar9 H) = 3 := c8k_dorder_pprime hdH3
  have hEX : img9 H (Opp 3 Y) ≤ img9 H (L9 Y H) := Subgroup.map_mono fun x hx =>
    Subgroup.mem_subgroupOf.mpr (c8k_opp_le_l9 hYH (Subgroup.mem_subgroupOf.mp hx))
  obtain ⟨g, -, -, hgD, hnot⟩ := hu37 (Hbar9 H) (img9 H (L9 Y H)) hL (img9 H (Opp 3 Y))
    hEX hS
    (zpowers (dH : Hbar9 H)) ((Subgroup.zpowers_le).mpr hdE) (by rw [Nat.card_zpowers, hdo])
  obtain ⟨n, hnN, k, hk⟩ := c8k_frattini_lift hdH3 hgD
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hU1 : zpowers d ≠ ⊥ := by
    intro h
    have : d = 1 := by simpa using (Subgroup.zpowers_eq_bot.mp h)
    rw [this, orderOf_one] at hd3
    omega
  have hU3 : IsPGroup 3 (zpowers d) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hd3]; norm_num)
  have hnM : (n : G) ∈ D.M :=
    hse.normalizer_le hU1 hU3
      ((Subgroup.zpowers_le).mpr (hY ▸ hdY |> fun h => (Subgroup.mem_inf.mp h).2)) hnN
  obtain ⟨s, hsE, hs⟩ := c8k_inner_on_shat D hY hCY hCn hC3 hP (e := 1) he hS hnM
  apply hnot
  refine ⟨(dH : Hbar9 H) ^ (-k) * s,
    Subgroup.mul_mem _ (Subgroup.zpow_mem _ hdE _) hsE, fun x hx => ?_⟩
  have hg : g = (dH : Hbar9 H) ^ (-k) * (n : Hbar9 H) := by
    rw [hk]
    group
  have hx' := hs x hx
  rw [hg]
  calc (dH : Hbar9 H) ^ (-k) * (n : Hbar9 H) * x * ((dH : Hbar9 H) ^ (-k) * (n : Hbar9 H))⁻¹
      = (dH : Hbar9 H) ^ (-k) * ((n : Hbar9 H) * x * (n : Hbar9 H)⁻¹) *
          ((dH : Hbar9 H) ^ (-k))⁻¹ := by group
    _ = (dH : Hbar9 H) ^ (-k) * (s * x * s⁻¹) * ((dH : Hbar9 H) ^ (-k))⁻¹ := by rw [hx']
    _ = ((dH : Hbar9 H) ^ (-k) * s) * x * ((dH : Hbar9 H) ^ (-k) * s)⁻¹ := by group

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
