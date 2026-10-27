module

public import CFSG.Quasithin.H13.AS91Sec7FourD
public import CFSG.Quasithin.H13.AS91Sec3Eleven

public section

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open MulAction CFSG.Quasithin.Asc94
open scoped Pointwise
open CFSG.ASVolI.ChH (IsTrio IsSextet M24g S24)

namespace Loc49

variable {G : Type} [Group G] [Finite G] {z : G} (c : Loc49 G z)

theorem comp_trans_comp {x u y v w : G ⧸ c.G1} (h₁ : comp c.Delta x u y v)
    (h₂ : comp c.Delta x v y w) : comp c.Delta x u y w := by
  obtain ⟨hu, hv, hr₁⟩ := h₁
  obtain ⟨hv', hw, hr₂⟩ := h₂
  exact ⟨hu, hw, hr₁.trans hr₂⟩

theorem dSet_two_of_dSet_one {x u y v w : G ⧸ c.G1} (hv : comp c.Delta x u y v)
    (h : dSet c.Delta c.Rh 1 x v y w) : dSet c.Delta c.Rh 2 x u y w := by
  rcases h with h | ⟨hxw, d, hd, hR⟩
  · exact Or.inl (c.comp_trans_comp hv h)
  · exact Or.inr ⟨hxw, d, c.comp_trans_comp hv hd, c.rh_two_iff.2 (Or.inl hR)⟩

theorem not_adj_of_not_rh_two {x u y : G ⧸ c.G1} (h2 : ¬ c.Rh 2 x u y)
    (hxu : c.Delta.Adj x u) (huy : c.Delta.Adj u y) : ¬ c.Delta.Adj x y := fun hxy =>
  h2 (c.rh_two_iff.2 (Or.inl (c.rh_one_iff.2 (Or.inl ⟨hxu, huy, hxy⟩))))

theorem not_rh_one_of_not_rh_two (hI : Sec7Inputs) (hJ : HypJ4 G z) {x u y v : G ⧸ c.G1}
    (h2 : ¬ c.Rh 2 x u y) (hxu : c.Delta.Adj x u) (huy : c.Delta.Adj u y) (hxy : x ≠ y) :
    ¬ c.Rh 1 x v y := by
  have hnxy : ¬ c.Delta.Adj x y := c.not_adj_of_not_rh_two h2 hxu huy
  intro h1
  rcases c.rh_one_iff.1 h1 with ⟨-, -, hxy'⟩ | ⟨-, -, -, m, n, -, hxm, -, hyn, σ, hmσ, hnσ⟩
  · exact hnxy hxy'
  · have hxσ : c.OnP x σ := c.inc_pt_plane hxm hmσ
    have hyσ : c.OnP y σ := c.inc_pt_plane hyn hnσ
    have hd : Dist2 c.Delta x y := ⟨hxy, hnxy, u, hxu, huy⟩
    have huσ : c.OnP u σ := c.stmt5_7_at hI.s57 hJ hxσ hyσ hd hxu huy.symm
    obtain ⟨L, hLu, hLx⟩ := c.exists_onL_of_adj hxu.symm
    obtain ⟨M, hMu, hMy⟩ := c.exists_onL_of_adj huy
    have hLσ : c.LnP L σ := c.lnP_of_adj hI.gamma2 hJ huσ hxσ hxu.symm hLu hLx
    have hMσ : c.LnP M σ := c.lnP_of_adj hI.gamma2 hJ huσ hyσ huy hMu hMy
    exact h2 (c.rh_two_iff.2 (Or.inl (c.rh_one_iff.2
      (Or.inr ⟨hxu, huy, hxy, L, M, hLu, hLx, hMu, hMy, ⟨σ, hLσ, hMσ⟩⟩))))

end Loc49

namespace ResM24

variable {G : Type} [Group G] [Finite G] {z : G} {c : Loc49 G z} (ρ : ResM24 c)

section Symm


include ρ in
theorem rh_two_symm {x u y : G ⧸ c.G1} (h : c.Rh 2 x u y) : c.Rh 2 y u x := by
  rcases c.rh_two_iff.1 h with h | ⟨hxu, huy, hxy, m, n, hum, hxm, hun, hyn, hδ⟩
  · rcases c.rh_one_iff.1 h with ⟨hxu, huy, hxy⟩ | ⟨hxu, huy, hxy, m, n, hum, hxm, hun, hyn, hco⟩
    · exact c.rh_two_iff.2 (Or.inl (c.rh_one_iff.2 (Or.inl ⟨huy.symm, hxu.symm, hxy.symm⟩)))
    · exact c.rh_two_iff.2 (Or.inl (c.rh_one_iff.2 (Or.inr ⟨huy.symm, hxu.symm, hxy.symm, n, m,
        hun, hyn, hum, hxm, Loc49.CoL.symm c hco⟩)))
  · exact c.rh_two_iff.2 (Or.inr ⟨huy.symm, hxu.symm, hxy.symm, n, m, hun, hyn, hum, hxm,
      ρ.deltaAt_symm 3 hum hun hδ⟩)

end Symm

section Four


include ρ in
theorem mem_delta_four_of_not_rh_two {x u y : G ⧸ c.G1} (h2 : ¬ c.Rh 2 x u y)
    (hxu : c.Delta.Adj x u) (huy : c.Delta.Adj u y) (hxy : x ≠ y) {L M : G ⧸ c.G2}
    (hLu : c.OnL u L) (hLx : c.OnL x L) (hMu : c.OnL u M) (hMy : c.OnL y M) :
    M ∈ c.deltaAt 4 u L := by
  obtain ⟨i, hi, -⟩ := ρ.deltaAt_existsUnique hLu hMu
  have hnc : ¬ c.CoL L M := fun h => h2 (c.rh_two_iff.2 (Or.inl (c.rh_one_iff.2
    (Or.inr ⟨hxu, huy, hxy, L, M, hLu, hLx, hMu, hMy, h⟩))))
  have hn3 : M ∉ c.deltaAt 3 u L := fun h => h2 (c.rh_two_iff.2
    (Or.inr ⟨hxu, huy, hxy, L, M, hLu, hLx, hMu, hMy, h⟩))
  have hcop := ρ.coL_iff_deltaAt hLu hMu
  fin_cases i
  · exact absurd (hcop.2 (Or.inl hi)) hnc
  · exact absurd (hcop.2 (Or.inr (Or.inl hi))) hnc
  · exact absurd (hcop.2 (Or.inr (Or.inr hi))) hnc
  · exact absurd hi hn3
  · exact hi

end Four

section Trio


include ρ in
theorem exists_line_of_isTrio_at {g : G} {x : G ⧸ c.G1} (hg : g • c.x0 = x)
    {t : Finset (Finset (Fin 24))} (ht : IsTrio t) :
    ∃ n, c.OnL x n ∧ ρ.trio (g⁻¹ • n) = t := by
  obtain ⟨σ, hσ, hσt⟩ := ρ.exists_smul_l₀ ht
  obtain ⟨m, hm, hmt⟩ := ρ.exists_trio_eq hσ
  refine ⟨g • m, ?_, by rw [inv_smul_smul, hmt, hσt]⟩
  rw [← hg]
  exact (cInc_smul c.G1 c.G2 g c.x0 m).2 hm

end Trio

section Thirteen


include ρ in
theorem exists_delta_two_two {u : G ⧸ c.G1} {L M : G ⧸ c.G2} (hLu : c.OnL u L)
    (hMu : c.OnL u M) (h4 : M ∈ c.deltaAt 4 u L) :
    ∃ l, c.OnL u l ∧ l ∈ c.deltaAt 2 u L ∧ l ∈ c.deltaAt 2 u M := by
  obtain ⟨g, hg, -⟩ := c.exists_frame hLu
  have hd4 : M24G.Delta (ρ.trio (g⁻¹ • L)) (ρ.trio (g⁻¹ • M)) 4 :=
    (ρ.mem_deltaAt_iff 4 hg hLu hMu).1 h4
  obtain ⟨k, hk, hLk, hMk⟩ := M24G.exists_delta_two_delta_two (ρ.isTrio_trio_at hg hLu)
    (ρ.isTrio_trio_at hg hMu) hd4
  obtain ⟨l, hul, hlk⟩ := ρ.exists_line_of_isTrio_at hg hk
  refine ⟨l, hul, (ρ.mem_deltaAt_iff 2 hg hLu hul).2 ?_, (ρ.mem_deltaAt_iff 2 hg hMu hul).2 ?_⟩
  · rw [hlk]
    exact hLk
  · rw [hlk]
    exact hMk

end Thirteen

section Spread


include ρ in
theorem exists_pt_off_line (hI : Sec7Inputs) (hJ : HypJ4 G z) {x : G ⧸ c.G1} {π : G ⧸ c.G3}
    {l m : G ⧸ c.G2} (hxπ : c.OnP x π) (hlπ : c.LnP l π) (hxl : ¬ c.OnL x l)
    (hadj : ∀ w, c.OnL w l → c.Delta.Adj x w) (hxm : c.OnL x m) (hmπ : c.LnP m π) :
    ∃ v, c.OnL v l ∧ ¬ c.OnL v m ∧ ∀ a, c.OnL a m → c.Delta.Adj v a := by
  obtain ⟨g, hg, -⟩ := c.exists_frame hxm
  have hU : IsSextet (ρ.sext (g⁻¹ • π)) := ρ.isSextet_sext_at hg hxπ
  obtain ⟨D, hD, hDiff⟩ := ρ.stmt7_3_two hI hJ hg hxπ hlπ hxl hadj
  have ht : ρ.trio (g⁻¹ • m) ∈ M24G.triosOf (ρ.sext (g⁻¹ • π)) :=
    ρ.trio_mem_triosOf hg hxπ hxm hmπ
  obtain ⟨k, hkD, hkdis⟩ : ∃ k ∈ D, Disjoint k (ρ.trio (g⁻¹ • m)) := by
    by_contra hcon
    have hall : ∀ k ∈ D, ¬ Disjoint k (ρ.trio (g⁻¹ • m)) := fun k hk hdis => hcon ⟨k, hk, hdis⟩
    have hsub : D ⊆ (ρ.trio (g⁻¹ • m)).biUnion fun o => D.filter (o ∈ ·) := by
      intro k hk
      obtain ⟨o, hok, hot⟩ := Finset.not_disjoint_iff.1 (hall k hk)
      exact Finset.mem_biUnion.2 ⟨o, hot, Finset.mem_filter.2 ⟨hk, hok⟩⟩
    have hle : D.card ≤ ∑ o ∈ ρ.trio (g⁻¹ • m), (D.filter (o ∈ ·)).card :=
      (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    have hone : ∀ o ∈ ρ.trio (g⁻¹ • m), (D.filter (o ∈ ·)).card = 1 := fun o ho =>
      M24G.stmt2_1_2_triosOf hU D hD o ((M24G.mem_triosOf.1 ht).2 ho)
    have h3 : (ρ.trio (g⁻¹ • m)).card = 3 := (ρ.isTrio_trio_at hg hxm).1
    have h5 : D.card = 5 := (M24G.mem_spreadsOf.1 hD).1
    rw [Finset.sum_congr rfl hone, Finset.sum_const, smul_eq_mul, mul_one, h3, h5] at hle
    omega
  have hkT : k ∈ M24G.triosOf (ρ.sext (g⁻¹ • π)) := by
    obtain ⟨h1, h2, -⟩ := (M24G.mem_spreadsOf.1 hD).2 k hkD
    exact M24G.mem_triosOf.2 ⟨h1, h2⟩
  obtain ⟨n, hxn, hnπ, hnk⟩ := ρ.exists_line_of_mem_triosOf hg hxπ hkT
  obtain ⟨v, hvl, hvn⟩ := (hDiff n hxn).2 (by rw [hnk]; exact hkD)
  have hvx : v ≠ x := fun e => hxl (by rw [← e]; exact hvl)
  have hdis : Disjoint (ρ.trio (g⁻¹ • m)) (ρ.trio (g⁻¹ • n)) := by
    rw [hnk]
    exact hkdis.symm
  have hδ2 : m ∈ c.deltaAt 2 x n :=
    (ρ.mem_deltaAt_two_iff_at hg hxn hxm).2 ⟨hdis, ⟨π, hnπ, hmπ⟩⟩
  exact ⟨v, hvl, ρ.not_onL_of_disjoint hI hJ hvx hvn hxn hxm hg hdis,
    fun a ha => c.stmt7_1_two hI.s54 hJ hxn hvn hvx hδ2 ha⟩

end Spread

section Eleven


include ρ in
theorem exists_line_coplanar_or_delta_three (hI : Sec7Inputs) (hJ : HypJ4 G z) {v : G ⧸ c.G1}
    {π : G ⧸ c.G3} {m M : G ⧸ c.G2} (hvπ : c.OnP v π) (hmπ : c.LnP m π) (hvm : ¬ c.OnL v m)
    (hadj : ∀ a, c.OnL a m → c.Delta.Adj v a) (hvM : c.OnL v M) :
    ∃ w k, c.OnL w m ∧ c.OnL v k ∧ c.OnL w k ∧ (c.CoL M k ∨ k ∈ c.deltaAt 3 v M) := by
  obtain ⟨g, hg, -⟩ := c.exists_frame hvM
  obtain ⟨D, hD, hDiff⟩ := ρ.stmt7_3_two hI hJ hg hvπ hmπ hvm hadj
  have hU : IsSextet (ρ.sext (g⁻¹ • π)) := ρ.isSextet_sext_at hg hvπ
  have hDo : M24G.IsDiscOrOval (ρ.sext (g⁻¹ • π)) D := Or.inr (M24G.mem_spreadsOf.1 hD)
  obtain ⟨d, hdD, hd⟩ :=
    M24G.exists_coplanar_or_delta_three hU hDo (ρ.isTrio_trio_at hg hvM)
  have hdT : d ∈ M24G.triosOf (ρ.sext (g⁻¹ • π)) := by
    obtain ⟨h1, h2, -⟩ := (M24G.mem_spreadsOf.1 hD).2 d hdD
    exact M24G.mem_triosOf.2 ⟨h1, h2⟩
  obtain ⟨k, hvk, -, hkd⟩ := ρ.exists_line_of_mem_triosOf hg hvπ hdT
  obtain ⟨w, hwm, hwk⟩ := (hDiff k hvk).2 (by rw [hkd]; exact hdD)
  refine ⟨w, k, hwm, hvk, hwk, ?_⟩
  rcases hd with hd | hd
  · exact Or.inl ((ρ.coplanar_iff_at hg hvM hvk).2 (by rw [hkd]; exact hd))
  · exact Or.inr ((ρ.mem_deltaAt_three_iff_at hg hvM hvk).2 (by rw [hkd]; exact hd))

end Eleven

section CaseA


include ρ in
theorem stmt7_7_of_rh_two (hI : Sec7Inputs) (hJ : HypJ4 G z) {x u y v : G ⧸ c.G1}
    (h2 : ¬ c.Rh 2 x u y) (hxu : c.Delta.Adj x u) (huy : c.Delta.Adj u y) (hxy : x ≠ y)
    (hv : comp c.Delta x u y v) (hv2 : c.Rh 2 x v y) :
    ∃ π, c.OnP x π ∧ ∀ m, c.OnL x m → c.LnP m π →
      ∃ w, c.OnL w m ∧ dSet c.Delta c.Rh 2 x u y w := by
  have hv1 : ¬ c.Rh 1 x v y := c.not_rh_one_of_not_rh_two hI hJ h2 hxu huy hxy
  obtain ⟨hxv, hvy, -, -⟩ := c.rh21_path hv2 hv1
  obtain ⟨L, hvL, hxL⟩ := c.exists_onL_of_adj hxv.symm
  obtain ⟨M, hvM, hyM⟩ := c.exists_onL_of_adj hvy
  have hM3 : M ∈ c.deltaAt 3 v L := c.rh21_mem_delta3 hI hJ hv2 hv1 hvL hxL hvM hyM
  obtain ⟨π, ⟨hvπ, hLπ, hMπ⟩, -⟩ := ρ.existsUnique_plane_meetsP hJ hvL hvM hM3
  refine ⟨π, c.inc_pt_plane hxL hLπ, fun m hxm hmπ => ?_⟩
  obtain ⟨w, hwm, hw⟩ := ρ.stmt7_4_two hI hJ hv2 hv1 hvL hxL hvM hyM hvπ hLπ hMπ hxm hmπ
  exact ⟨w, hwm, c.dSet_two_of_dSet_one hv hw⟩

end CaseA

section CaseB


include ρ in
theorem stmt7_7_of_not_rh_two (hI : Sec7Inputs) (hJ : HypJ4 G z) {x u y : G ⧸ c.G1}
    (h2 : ¬ c.Rh 2 x u y) (hxu : c.Delta.Adj x u) (huy : c.Delta.Adj u y) (hxy : x ≠ y)
    (hB : ∀ v, comp c.Delta x u y v → ¬ c.Rh 2 x v y) :
    ∃ π, c.OnP x π ∧ ∀ m, c.OnL x m → c.LnP m π →
      ∃ w, c.OnL w m ∧ dSet c.Delta c.Rh 2 x u y w := by
  have hnxy : ¬ c.Delta.Adj x y := c.not_adj_of_not_rh_two h2 hxu huy
  obtain ⟨L, huL, hxL⟩ := c.exists_onL_of_adj hxu.symm
  obtain ⟨M, huM, hyM⟩ := c.exists_onL_of_adj huy
  obtain ⟨l, hul, hlL, hlM⟩ := ρ.exists_delta_two_two huL huM
    (ρ.mem_delta_four_of_not_rh_two h2 hxu huy hxy huL hxL huM hyM)
  obtain ⟨π, hLπ, hlπ⟩ := (ρ.coL_iff_deltaAt huL hul).2 (Or.inr (Or.inr hlL))
  have hxπ : c.OnP x π := c.inc_pt_plane hxL hLπ
  have hxadj : ∀ w, c.OnL w l → c.Delta.Adj x w := fun w hw =>
    c.stmt7_1_two hI.s54 hJ huL hxL hxu.ne hlL hw
  have hyadj : ∀ w, c.OnL w l → c.Delta.Adj y w := fun w hw =>
    c.stmt7_1_two hI.s54 hJ huM hyM huy.ne.symm hlM hw
  have hxl : ¬ c.OnL x l := by
    intro h
    have hlL' : l = L := c.eq_of_onL hI.lineU hJ hxu.ne.symm hul h huL hxL
    rw [hlL'] at hlL
    obtain ⟨i, -, hi⟩ := ρ.deltaAt_existsUnique huL huL
    have h0 : L ∈ c.deltaAt 0 u L := (ρ.mem_deltaAt_zero_iff huL huL).2 rfl
    exact absurd ((hi 0 h0).trans (hi 2 hlL).symm) (by decide)
  refine ⟨π, hxπ, fun m hxm hmπ => ?_⟩
  obtain ⟨v, hvl, hvm, hadj⟩ := ρ.exists_pt_off_line hI hJ hxπ hlπ hxl hxadj hxm hmπ
  have hvπ : c.OnP v π := c.inc_pt_plane hvl hlπ
  have hcomp : comp c.Delta x u y v := by
    by_cases hvu : v = u
    · rw [hvu]
      exact c.comp_refl_of hxu huy.symm
    · exact c.comp_of_adj_pt hxu huy.symm (hxadj v hvl) (hyadj v hvl)
        (c.adj_of_onL (Ne.symm hvu) hul hvl)
  obtain ⟨N, hvN, hyN⟩ := c.exists_onL_of_adj (hyadj v hvl).symm
  obtain ⟨w, k, hwm, hvk, hwk, hk⟩ :=
    ρ.exists_line_coplanar_or_delta_three hI hJ hvπ hmπ hvm hadj hvN
  have hvw : c.Delta.Adj v w := hadj w hwm
  have hyv : c.Delta.Adj y v := hyadj v hvl
  have hyw : y ≠ w := fun e => hnxy (c.adj_of_onL hxy hxm (by rw [e]; exact hwm))
  have hR : c.Rh 2 y v w := by
    rcases hk with hk | hk
    · exact c.rh_two_iff.2 (Or.inl (c.rh_one_iff.2
        (Or.inr ⟨hyv, hvw, hyw, N, k, hvN, hyN, hvk, hwk, hk⟩)))
    · exact c.rh_two_iff.2 (Or.inr ⟨hyv, hvw, hyw, N, k, hvN, hyN, hvk, hwk, hk⟩)
  have hwx : w ≠ x := fun e => hB v hcomp (ρ.rh_two_symm (by rw [e] at hR; exact hR))
  exact ⟨w, hwm, Or.inr ⟨c.adj_of_onL hwx.symm hxm hwm, v, hcomp, hR⟩⟩

end CaseB

section Main


include ρ in
theorem stmt7_7 (hI : Sec7Inputs) (hJ : HypJ4 G z) {x u y : G ⧸ c.G1} (h3 : c.Rh 3 x u y)
    (h2 : ¬ c.Rh 2 x u y) :
    ∃ π, c.OnP x π ∧ ∀ m, c.OnL x m → c.LnP m π →
      ∃ w, c.OnL w m ∧ dSet c.Delta c.Rh 2 x u y w := by
  obtain ⟨hxu, huy, hxy⟩ := c.rh_three_iff.1 h3
  by_cases hA : ∃ v, comp c.Delta x u y v ∧ c.Rh 2 x v y
  · obtain ⟨v, hv, hv2⟩ := hA
    exact ρ.stmt7_7_of_rh_two hI hJ h2 hxu huy hxy hv hv2
  · exact ρ.stmt7_7_of_not_rh_two hI hJ h2 hxu huy hxy fun v hv h => hA ⟨v, hv, h⟩

end Main

end ResM24

end CFSG.Quasithin.H13.AS91
