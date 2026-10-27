module

public import CFSG.Quasithin.H13.AS91Sec7Five
public import CFSG.Quasithin.H13.AS91Sec7FourC
public import CFSG.Quasithin.H13.AS91Sec3Eleven

public section

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open MulAction CFSG.Quasithin.Asc94
open scoped Pointwise
open CFSG.ASVolI.ChH (IsTrio IsSextet M24g S24)

namespace Loc49

variable {G : Type} [Group G] [Finite G] {z : G} (c : Loc49 G z)

private theorem exists_mem_inter_line {A B : Set (G ⧸ c.G1)} {m : G ⧸ c.G2}
    (hA3 : 3 ≤ A.ncard) (hB3 : 3 ≤ B.ncard) (hA : ∀ a ∈ A, c.OnL a m)
    (hB : ∀ a ∈ B, c.OnL a m) : ∃ a, a ∈ A ∧ a ∈ B := by
  have hsub : A ∪ B ⊆ {a | c.OnL a m} := by
    rintro a (ha | ha)
    · exact hA a ha
    · exact hB a ha
  have h5 := Set.ncard_le_ncard hsub
  rw [c.ncard_onL m] at h5
  have hinter := Set.ncard_union_add_ncard_inter A B
  have hne0 : (A ∩ B).ncard ≠ 0 := by omega
  obtain ⟨a, ha⟩ := Set.nonempty_of_ncard_ne_zero hne0
  exact ⟨a, ha.1, ha.2⟩

private theorem comp_of_perp {x u v w : G ⧸ c.G1} (hxu : c.Delta.Adj x u)
    (hvu : c.Delta.Adj v u) (hxw : c.Delta.Adj x w) (hvw : c.Delta.Adj v w)
    (h : Perp c.Delta u w) : comp c.Delta x u v w := by
  rcases h with rfl | h
  · exact ⟨⟨hxu, hvu⟩, ⟨hxu, hvu⟩, SimpleGraph.Reachable.refl _⟩
  · exact ⟨⟨hxu, hvu⟩, ⟨hxw, hvw⟩, SimpleGraph.Adj.reachable h⟩

end Loc49

namespace ResM24

variable {G : Type} [Group G] [Finite G] {z : G} {c : Loc49 G z} (ρ : ResM24 c)

section LineOfTrio


private theorem exists_line_of_isTrio {g : G} {a : G ⧸ c.G1} (hg : g • c.x0 = a)
    {t : Finset (Finset (Fin 24))} (ht : IsTrio t) :
    ∃ n, c.OnL a n ∧ ρ.trio (g⁻¹ • n) = t := by
  obtain ⟨σ, hσ, hσt⟩ := ρ.exists_smul_l₀ ht
  obtain ⟨m, hm, hmt⟩ := ρ.exists_trio_eq hσ
  refine ⟨g • m, ?_, ?_⟩
  · rw [← hg]
    exact (cInc_smul c.G1 c.G2 g c.x0 m).2 hm
  · rw [inv_smul_smul, hmt, hσt]

end LineOfTrio

section ThreeAdj


include ρ in
private theorem three_adj (hI : Sec7Inputs) (hJ : HypJ4 G z) {x w : G ⧸ c.G1}
    {d k : G ⧸ c.G2} (hxd : c.OnL x d) (hwd : c.OnL w d) (hwx : w ≠ x) (hxk : c.OnL x k)
    (hco : c.CoL k d) : k = d ∨ 3 ≤ {a | c.OnL a k ∧ c.Delta.Adj w a}.ncard := by
  rcases (ρ.coL_iff_deltaAt hxd hxk).1 (Loc49.CoL.symm c hco) with h0 | h1 | h2
  · exact Or.inl ((ρ.mem_deltaAt_zero_iff hxd hxk).1 h0)
  · exact Or.inr (c.stmt7_1_one hI.s54 hJ hxd hwd hwx h1).ge
  · refine Or.inr ?_
    have hsub : {a | c.OnL a k} ⊆ {a | c.OnL a k ∧ c.Delta.Adj w a} :=
      fun a (ha : c.OnL a k) => ⟨ha, c.stmt7_1_two hI.s54 hJ hxd hwd hwx h2 ha⟩
    have h5 := Set.ncard_le_ncard hsub
    rw [c.ncard_onL k] at h5
    omega

end ThreeAdj

section ObsOne


private theorem obs_one (hI : Sec7Inputs) (hJ : HypJ4 G z) {x u v : G ⧸ c.G1}
    (hv : Dist2 c.Delta x v) (hxu : c.Delta.Adj x u) (huv : c.Delta.Adj u v) {g : G}
    (hg : g • c.x0 = x) {L M : G ⧸ c.G2} (hxL : c.OnL x L) (huL : c.OnL u L) (hvM : c.OnL v M)
    (hco : c.CoL L M) :
    ∃ U, c.OnP x U ∧ c.OnP u U ∧ ∃ D : Finset (Finset (Finset (Fin 24))),
      M24G.IsDiscOrOval (ρ.sext (g⁻¹ • U)) D ∧ ∀ t ∈ D, ∃ n, c.OnL x n ∧ c.LnP n U ∧
        ρ.trio (g⁻¹ • n) = t ∧ ∃ w, c.OnL w n ∧ Perp c.Delta u w ∧ c.Delta.Adj x w ∧
          c.Delta.Adj v w := by
  classical
  obtain ⟨σ, hLσ, hMσ⟩ := hco
  have hxσ : c.OnP x σ := c.inc_pt_plane hxL hLσ
  have huσ : c.OnP u σ := c.inc_pt_plane huL hLσ
  have hvσ : c.OnP v σ := c.inc_pt_plane hvM hMσ
  have hU : IsSextet (ρ.sext (g⁻¹ • σ)) := ρ.isSextet_sext_at hg hxσ
  obtain ⟨d, hd⟩ : (M24G.triosOf (ρ.sext (g⁻¹ • σ))).Nonempty :=
    Finset.card_pos.1 (by rw [M24G.card_triosOf hU]; norm_num)
  obtain ⟨hdT, hdU⟩ := M24G.mem_triosOf.1 hd
  refine ⟨σ, hxσ, huσ,
    (M24G.triosOf (ρ.sext (g⁻¹ • σ))).filter fun k => k ≠ d ∧ ¬ Disjoint k d, ?_, ?_⟩
  · unfold M24G.IsDiscOrOval
    refine Or.inl ⟨d, hdT, hdU, fun k => ?_⟩
    rw [Finset.mem_filter, M24G.mem_triosOf, and_assoc]
  · intro t ht
    obtain ⟨htT, -⟩ := Finset.mem_filter.1 ht
    obtain ⟨n, hxn, hnσ, hnt⟩ := ρ.exists_line_of_mem_triosOf hg hxσ htT
    refine ⟨n, hxn, hnσ, hnt, ?_⟩
    rcases ρ.three_adj hI hJ hxL huL hxu.ne.symm hxn ⟨σ, hnσ, hLσ⟩ with hnL | hB
    · exact ⟨u, by rw [hnL]; exact huL, Or.inl rfl, hxu, huv.symm⟩
    · have hA := c.stmt7_5_three hI hJ hv hxσ hvσ hxn hnσ
      obtain ⟨w, hwA, hwB⟩ := c.exists_mem_inter_line hA hB (fun a ha => ha.1) (fun a ha => ha.1)
      exact ⟨w, hwA.1, Or.inr hwB.2, hwA.2.1, hwA.2.2⟩

end ObsOne

section ObsTwo


private theorem obs_two (hI : Sec7Inputs) (hJ : HypJ4 G z) {x u v : G ⧸ c.G1}
    (hv : Dist2 c.Delta x v) (hxu : c.Delta.Adj x u) (huv : c.Delta.Adj u v) {g : G}
    (hg : g • c.x0 = x) {L M : G ⧸ c.G2} (hxL : c.OnL x L) (huL : c.OnL u L) (huM : c.OnL u M)
    (hvM : c.OnL v M) (hco : ¬ c.CoL L M) (h3 : M ∈ c.deltaAt 3 u L) :
    ∃ U, c.OnP x U ∧ c.OnP u U ∧ ∃ D : Finset (Finset (Finset (Fin 24))),
      M24G.IsDiscOrOval (ρ.sext (g⁻¹ • U)) D ∧ ∀ t ∈ D, ∃ n, c.OnL x n ∧ c.LnP n U ∧
        ρ.trio (g⁻¹ • n) = t ∧ ∃ w, c.OnL w n ∧ Perp c.Delta u w ∧ c.Delta.Adj x w ∧
          c.Delta.Adj v w := by
  classical
  have h2 : c.Rh 2 x u v :=
    c.rh_two_iff.2 (Or.inr ⟨hxu, huv, hv.1, L, M, huL, hxL, huM, hvM, h3⟩)
  have h1 : ¬ c.Rh 1 x u v := by
    intro h
    rcases c.rh_one_iff.1 h with h0 | ⟨-, -, -, m, n, hum, hxm, hun, hvn, hmn⟩
    · obtain ⟨-, -, hxv⟩ := h0
      exact hv.2.1 hxv
    · have hm : m = L := c.eq_of_onL hI.lineU hJ hxu.ne.symm hum hxm huL hxL
      have hn : n = M := c.eq_of_onL hI.lineU hJ huv.ne hun hvn huM hvM
      rw [hm, hn] at hmn
      exact hco hmn
  obtain ⟨π, ⟨hπu, hLπ, hMπ⟩, -⟩ := ρ.existsUnique_plane_meetsP hJ huL huM h3
  have hxπ : c.OnP x π := c.inc_pt_plane hxL hLπ
  obtain ⟨d, hd, hdiff⟩ := ρ.stmt7_4_one hI hJ h2 h1 huL hxL huM hvM hπu hLπ hMπ hg
  obtain ⟨hdT, hdU⟩ := M24G.mem_triosOf.1 hd
  refine ⟨π, hxπ, hπu,
    (M24G.triosOf (ρ.sext (g⁻¹ • π))).filter fun k => k ≠ d ∧ ¬ Disjoint k d, ?_, ?_⟩
  · unfold M24G.IsDiscOrOval
    refine Or.inl ⟨d, hdT, hdU, fun k => ?_⟩
    rw [Finset.mem_filter, M24G.mem_triosOf, and_assoc]
  · intro t ht
    obtain ⟨htT, htd⟩ := Finset.mem_filter.1 ht
    obtain ⟨n, hxn, hnπ, hnt⟩ := ρ.exists_line_of_mem_triosOf hg hxπ htT
    refine ⟨n, hxn, hnπ, hnt, ?_⟩
    obtain ⟨w, hxw, hvw, hwπ, hwn⟩ := (hdiff n hxn hnπ).2 (by rw [hnt]; exact htd)
    refine ⟨w, hwn, ?_, hxw, hvw⟩
    rcases eq_or_ne u w with huw | huw
    · exact Or.inl huw
    · exact Or.inr (c.rh21_clique hI hJ h2 h1 ⟨hxu, huv.symm, hπu⟩ ⟨hxw, hvw, hwπ⟩ huw)

end ObsTwo

section ObsThree


private theorem obs_three (hI : Sec7Inputs) (hJ : HypJ4 G z) {x u v : G ⧸ c.G1}
    (hxu : c.Delta.Adj x u) (huv : c.Delta.Adj u v) {g : G}
    (hg : g • c.x0 = x) {L M : G ⧸ c.G2} (hxL : c.OnL x L) (huL : c.OnL u L) (huM : c.OnL u M)
    (hvM : c.OnL v M) (hco : ¬ c.CoL L M) (h3 : M ∉ c.deltaAt 3 u L) :
    ∃ U, c.OnP x U ∧ c.OnP u U ∧ ∃ D : Finset (Finset (Finset (Fin 24))),
      M24G.IsDiscOrOval (ρ.sext (g⁻¹ • U)) D ∧ ∀ t ∈ D, ∃ n, c.OnL x n ∧ c.LnP n U ∧
        ρ.trio (g⁻¹ • n) = t ∧ ∃ w, c.OnL w n ∧ Perp c.Delta u w ∧ c.Delta.Adj x w ∧
          c.Delta.Adj v w := by
  have h4 : M ∈ c.deltaAt 4 u L := by
    obtain ⟨i, hi, -⟩ := ρ.deltaAt_existsUnique huL huM
    fin_cases i
    · exact absurd ((ρ.coL_iff_deltaAt huL huM).2 (Or.inl hi)) hco
    · exact absurd ((ρ.coL_iff_deltaAt huL huM).2 (Or.inr (Or.inl hi))) hco
    · exact absurd ((ρ.coL_iff_deltaAt huL huM).2 (Or.inr (Or.inr hi))) hco
    · exact absurd hi h3
    · exact hi
  obtain ⟨gu, hgu, -⟩ := c.exists_frame huL
  obtain ⟨k, hk, hlk, hmk⟩ := M24G.exists_delta_two_delta_two (ρ.isTrio_trio_at hgu huL)
    (ρ.isTrio_trio_at hgu huM) ((ρ.mem_deltaAt_iff 4 hgu huL huM).1 h4)
  obtain ⟨l, hul, hlk'⟩ := ρ.exists_line_of_isTrio hgu hk
  have hlL : l ∈ c.deltaAt 2 u L := (ρ.mem_deltaAt_iff 2 hgu huL hul).2 (by rw [hlk']; exact hlk)
  have hlM : l ∈ c.deltaAt 2 u M := (ρ.mem_deltaAt_iff 2 hgu huM hul).2 (by rw [hlk']; exact hmk)
  have hlx : ∀ a, c.OnL a l → c.Delta.Adj x a := fun a ha =>
    c.stmt7_1_two hI.s54 hJ huL hxL hxu.ne hlL ha
  have hlv : ∀ a, c.OnL a l → c.Delta.Adj v a := fun a ha =>
    c.stmt7_1_two hI.s54 hJ huM hvM huv.ne.symm hlM ha
  obtain ⟨σ, hLσ, hlσ⟩ := (ρ.coL_iff_deltaAt huL hul).2 (Or.inr (Or.inr hlL))
  have hxσ : c.OnP x σ := c.inc_pt_plane hxL hLσ
  have huσ : c.OnP u σ := c.inc_pt_plane huL hLσ
  obtain ⟨D, hD, hDiff⟩ := ρ.stmt7_3_two hI hJ hg hxσ hlσ (fun hxl => (hlx x hxl).ne rfl) hlx
  refine ⟨σ, hxσ, huσ, D, Or.inr (M24G.mem_spreadsOf.1 hD), fun t ht => ?_⟩
  obtain ⟨hIT, hTU, -⟩ := (M24G.mem_spreadsOf.1 hD).2 t ht
  obtain ⟨n, hxn, hnσ, hnt⟩ :=
    ρ.exists_line_of_mem_triosOf hg hxσ (M24G.mem_triosOf.2 ⟨hIT, hTU⟩)
  obtain ⟨w, hwl, hwn⟩ := (hDiff n hxn).2 (by rw [hnt]; exact ht)
  refine ⟨n, hxn, hnσ, hnt, w, hwn, ?_, hlx w hwl, hlv w hwl⟩
  rcases eq_or_ne u w with huw | huw
  · exact Or.inl huw
  · exact Or.inr (c.adj_of_onL huw hul hwl)

end ObsThree

section Obs


theorem stmt7_6_obs (hI : Sec7Inputs) (hJ : HypJ4 G z) {x u v : G ⧸ c.G1}
    (hv : Dist2 c.Delta x v) (hxu : c.Delta.Adj x u) (huv : c.Delta.Adj u v) {g : G}
    (hg : g • c.x0 = x) :
    ∃ U, c.OnP x U ∧ c.OnP u U ∧ ∃ D : Finset (Finset (Finset (Fin 24))),
      M24G.IsDiscOrOval (ρ.sext (g⁻¹ • U)) D ∧ ∀ t ∈ D, ∃ n, c.OnL x n ∧ c.LnP n U ∧
        ρ.trio (g⁻¹ • n) = t ∧ ∃ w, c.OnL w n ∧ Perp c.Delta u w ∧ c.Delta.Adj x w ∧
          c.Delta.Adj v w := by
  obtain ⟨L, hxL, huL⟩ := c.exists_onL_of_adj hxu
  obtain ⟨M, huM, hvM⟩ := c.exists_onL_of_adj huv
  by_cases hco : c.CoL L M
  · exact ρ.obs_one hI hJ hv hxu huv hg hxL huL hvM hco
  · by_cases h3 : M ∈ c.deltaAt 3 u L
    · exact ρ.obs_two hI hJ hv hxu huv hg hxL huL huM hvM hco h3
    · exact ρ.obs_three hI hJ hxu huv hg hxL huL huM hvM hco h3

end Obs

section Main


include ρ in
private theorem stmt7_6_aux (hI : Sec7Inputs) (hJ : HypJ4 G z) {x u v : G ⧸ c.G1}
    (hv : Dist2 c.Delta x v) (hxu : c.Delta.Adj x u) (huv : c.Delta.Adj u v) {π : G ⧸ c.G3}
    (hx : c.OnP x π) :
    ∃ k d w, c.OnL x k ∧ c.LnP k π ∧ c.OnL x d ∧ c.OnL w d ∧ Perp c.Delta u w ∧
      c.Delta.Adj x w ∧ c.Delta.Adj v w ∧ c.CoL k d := by
  obtain ⟨g, hg, -⟩ := c.exists_frameP hx
  obtain ⟨U, hxU, -, D, hD, hDw⟩ := ρ.stmt7_6_obs hI hJ hv hxu huv hg
  have hUs : IsSextet (ρ.sext (g⁻¹ • U)) := ρ.isSextet_sext_at hg hxU
  have hπs : IsSextet (ρ.sext (g⁻¹ • π)) := ρ.isSextet_sext_at hg hx
  obtain ⟨dt, hdt, kt, hkt, hkπ, hcop⟩ := M24G.exists_trioIn_coplanar hUs hD hπs
  obtain ⟨d, hxd, -, hdt', w, hwd, hperp, hxw, hvw⟩ := hDw dt hdt
  obtain ⟨k, hxk, hkπ', hkt'⟩ :=
    ρ.exists_line_of_mem_triosOf hg hx (M24G.mem_triosOf.2 ⟨hkt, hkπ⟩)
  refine ⟨k, d, w, hxk, hkπ', hxd, hwd, hperp, hxw, hvw, ?_⟩
  exact (ρ.coplanar_iff_at hg hxk hxd).2 (by rw [hkt', hdt']; exact M24G.coplanar_symm_of hcop)

include ρ in
theorem stmt7_6_one (hI : Sec7Inputs) (hJ : HypJ4 G z) {x : G ⧸ c.G1} {π : G ⧸ c.G3}
    (hx : c.OnP x π) {S : Set (G ⧸ c.G1)} (hS : ∀ s ∈ S, c.Delta.Adj x s ∧ c.OnP s π)
    (hSl : ∀ l, c.OnL x l → c.LnP l π → ∃ s ∈ S, c.OnL s l) {u v : G ⧸ c.G1}
    (hv : Dist2 c.Delta x v) (hxu : c.Delta.Adj x u) (huv : c.Delta.Adj u v) :
    ∃ s ∈ S, ∃ b, comp c.Delta x u v b ∧ induced c.Delta c.Rh 1 s b := by
  obtain ⟨k, d, w, hxk, hkπ, hxd, hwd, hperp, hxw, hvw, hco⟩ :=
    ρ.stmt7_6_aux hI hJ hv hxu huv hx
  obtain ⟨s, hsS, hsk⟩ := hSl k hxk hkπ
  refine ⟨s, hsS, w, c.comp_of_perp hxu huv.symm hxw hvw hperp, ?_⟩
  have hxs : c.Delta.Adj x s := (hS s hsS).1
  by_cases hsw : s = w
  · exact Or.inl (Or.inl hsw)
  by_cases hsw' : c.Delta.Adj s w
  · exact Or.inl (Or.inr hsw')
  · exact Or.inr ⟨x, c.rh_one_iff.2 (Or.inr ⟨hxs.symm, hxw, hsw, k, d, hxk, hsk, hxd, hwd, hco⟩)⟩

include ρ in
theorem stmt7_6_two (hI : Sec7Inputs) (hJ : HypJ4 G z) {x y : G ⧸ c.G1} (hy : Dist2 c.Delta x y)
    (hyπ : ∃ π, c.OnP x π ∧ c.OnP y π) {u v : G ⧸ c.G1} (hv : Dist2 c.Delta x v)
    (hxu : c.Delta.Adj x u) (huv : c.Delta.Adj u v) :
    ∃ a b, c.Delta.Adj x a ∧ c.Delta.Adj y a ∧ comp c.Delta x u v b ∧ Perp c.Delta a b := by
  obtain ⟨π, hxπ, hyπ⟩ := hyπ
  obtain ⟨k, d, w, hxk, hkπ, hxd, hwd, hperp, hxw, hvw, hco⟩ :=
    ρ.stmt7_6_aux hI hJ hv hxu huv hxπ
  have hcomp := c.comp_of_perp hxu huv.symm hxw hvw hperp
  have hA := c.stmt7_5_three hI hJ hy hxπ hyπ hxk hkπ
  rcases ρ.three_adj hI hJ hxd hwd hxw.ne.symm hxk hco with hkd | hB
  ·
    obtain ⟨a, ha⟩ := Set.nonempty_of_ncard_ne_zero (by omega :
      {a | c.OnL a k ∧ c.Delta.Adj x a ∧ c.Delta.Adj y a}.ncard ≠ 0)
    refine ⟨a, w, ha.2.1, ha.2.2, hcomp, ?_⟩
    rcases eq_or_ne a w with haw | haw
    · exact Or.inl haw
    · exact Or.inr (c.adj_of_onL haw ha.1 (by rw [hkd]; exact hwd))
  ·
    obtain ⟨a, haA, haB⟩ := c.exists_mem_inter_line hA hB (fun a ha => ha.1) (fun a ha => ha.1)
    exact ⟨a, w, haA.2.1, haA.2.2, hcomp, Or.inr haB.2.symm⟩

end Main

end ResM24

end CFSG.Quasithin.H13.AS91
