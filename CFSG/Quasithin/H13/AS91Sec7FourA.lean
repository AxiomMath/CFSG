module

public import CFSG.Quasithin.H13.AS91Sec7Geom
public import CFSG.Quasithin.H13.AS91Sec7Plane
public import CFSG.Quasithin.H13.AS91Sec3Thirteen

public section

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open MulAction CFSG.Quasithin.Asc94
open scoped Pointwise
open CFSG.ASVolI.ChH (IsTrio IsSextet M24g S24)

namespace Loc49

variable {G : Type} [Group G] [Finite G] {z : G} (c : Loc49 G z)

theorem exists_onL_of_adj {a b : G ⧸ c.G1} (h : c.Delta.Adj a b) :
    ∃ m : G ⧸ c.G2, c.OnL a m ∧ c.OnL b m :=
  (colGraph_adj.1 h).2

theorem rh21_path {x u y : G ⧸ c.G1} (h2 : c.Rh 2 x u y) (h1 : ¬ c.Rh 1 x u y) :
    c.Delta.Adj x u ∧ c.Delta.Adj u y ∧ x ≠ y ∧
      ∃ m n, c.OnL u m ∧ c.OnL x m ∧ c.OnL u n ∧ c.OnL y n ∧ n ∈ c.deltaAt 3 u m := by
  rcases c.rh_two_iff.1 h2 with h | h
  · exact absurd h h1
  · exact h

theorem rh21_not_adj {x u y} (h1 : ¬ c.Rh 1 x u y) (hxu : c.Delta.Adj x u)
    (huy : c.Delta.Adj u y) : ¬ c.Delta.Adj x y := fun hxy =>
  h1 (c.rh_one_iff.2 (Or.inl ⟨hxu, huy, hxy⟩))

theorem rh21_dist2 {x u y} (h2 : c.Rh 2 x u y) (h1 : ¬ c.Rh 1 x u y) : Dist2 c.Delta x y := by
  obtain ⟨hxu, huy, hxy, -⟩ := c.rh21_path h2 h1
  exact ⟨hxy, c.rh21_not_adj h1 hxu huy, u, hxu, huy⟩

theorem rh21_not_coL {x u y} (h2 : c.Rh 2 x u y) (h1 : ¬ c.Rh 1 x u y) {L M : G ⧸ c.G2}
    (hLu : c.OnL u L) (hLx : c.OnL x L) (hMu : c.OnL u M) (hMy : c.OnL y M) : ¬ c.CoL L M := by
  obtain ⟨hxu, huy, hxy, -⟩ := c.rh21_path h2 h1
  exact fun hLM => h1 (c.rh_one_iff.2 (Or.inr ⟨hxu, huy, hxy, L, M, hLu, hLx, hMu, hMy, hLM⟩))

theorem rh21_mem_delta3 (hI : Sec7Inputs) (hJ : HypJ4 G z) {x u y} (h2 : c.Rh 2 x u y)
    (h1 : ¬ c.Rh 1 x u y) {L M : G ⧸ c.G2} (hLu : c.OnL u L) (hLx : c.OnL x L)
    (hMu : c.OnL u M) (hMy : c.OnL y M) : M ∈ c.deltaAt 3 u L := by
  obtain ⟨hxu, huy, -, m, n, hum, hxm, hun, hyn, hδ⟩ := c.rh21_path h2 h1
  have hm : m = L := c.eq_of_onL hI.lineU hJ hxu.ne.symm hum hxm hLu hLx
  have hn : n = M := c.eq_of_onL hI.lineU hJ huy.ne hun hyn hMu hMy
  subst hm hn
  exact hδ

theorem rh21_not_onP (hI : Sec7Inputs) (hJ : HypJ4 G z) {x u y} (h2 : c.Rh 2 x u y)
    (h1 : ¬ c.Rh 1 x u y) {σ : G ⧸ c.G3} (hx : c.OnP x σ) : ¬ c.OnP y σ := by
  intro hy
  obtain ⟨hxu, huy, hxy, m, n, hum, hxm, hun, hyn, -⟩ := c.rh21_path h2 h1
  have hu : c.OnP u σ := c.stmt5_7_at hI.s57 hJ hx hy (c.rh21_dist2 h2 h1) hxu huy.symm
  have hm : c.LnP m σ := c.lnP_of_adj hI.gamma2 hJ hu hx hxu.symm hum hxm
  have hn : c.LnP n σ := c.lnP_of_adj hI.gamma2 hJ hu hy huy hun hyn
  exact h1 (c.rh_one_iff.2 (Or.inr ⟨hxu, huy, hxy, m, n, hum, hxm, hun, hyn, ⟨σ, hm, hn⟩⟩))

theorem rh21_eq_of_onL (hI : Sec7Inputs) (hJ : HypJ4 G z) {x u y} (h2 : c.Rh 2 x u y)
    (h1 : ¬ c.Rh 1 x u y) {n : G ⧸ c.G2} (hn : c.OnL x n) {a b : G ⧸ c.G1} (ha : c.OnL a n)
    (hb : c.OnL b n) (hay : c.Delta.Adj y a) (hby : c.Delta.Adj y b) : a = b := by
  by_contra hab
  have hab' : c.Delta.Adj a b := c.adj_of_onL hab ha hb
  obtain ⟨σ, haσ, hbσ, hyσ⟩ := hI.s55 G z hJ c a b y hab' hby.symm hay.symm
  have hnσ : c.LnP n σ := c.lnP_of_adj hI.gamma2 hJ haσ hbσ hab' ha hb
  exact c.rh21_not_onP hI hJ h2 h1 (c.inc_pt_plane hn hnσ) hyσ

theorem rh21_clique (hI : Sec7Inputs) (hJ : HypJ4 G z) {x u y} (h2 : c.Rh 2 x u y)
    (h1 : ¬ c.Rh 1 x u y) {π : G ⧸ c.G3} {a b : G ⧸ c.G1}
    (ha : c.Delta.Adj x a ∧ c.Delta.Adj y a ∧ c.OnP a π)
    (hb : c.Delta.Adj x b ∧ c.Delta.Adj y b ∧ c.OnP b π) (hab : a ≠ b) : c.Delta.Adj a b := by
  by_contra hnab
  have hd : Dist2 c.Delta a b := ⟨hab, hnab, x, ha.1.symm, hb.1⟩
  have hxπ : c.OnP x π := c.stmt5_7_at hI.s57 hJ ha.2.2 hb.2.2 hd ha.1.symm hb.1.symm
  have hyπ : c.OnP y π := c.stmt5_7_at hI.s57 hJ ha.2.2 hb.2.2 hd ha.2.1.symm hb.2.1.symm
  exact c.rh21_not_onP hI hJ h2 h1 hxπ hyπ

end Loc49

namespace ResM24

variable {G : Type} [Group G] [Finite G] {z : G} {c : Loc49 G z} (ρ : ResM24 c)

section Kappa


theorem kappa_one_of_octad {U l : Finset (Finset (Fin 24))} (hU : IsSextet U) (hl : IsTrio l)
    (hnot : ¬ M24G.TrioIn l U) {o : Finset (Fin 24)} (hol : o ∈ l) (hoU : o ∈ M24G.octsOf U) :
    M24G.Kappa U l 1 := by
  obtain ⟨i, hi, -⟩ := M24G.kappa_existsUnique hU hl
  fin_cases i
  · exact absurd (show M24G.TrioIn l U from hi) hnot
  · exact hi
  · obtain ⟨hdis, -⟩ := hi
    exact absurd hoU (Finset.disjoint_left.1 hdis hol)
  · obtain ⟨hdis, -⟩ := hi
    exact absurd hoU (Finset.disjoint_left.1 hdis hol)

end Kappa

section ClaimA


include ρ in
theorem claimA (hI : Sec7Inputs) (hJ : HypJ4 G z) {x u y v : G ⧸ c.G1} (h2 : c.Rh 2 x u y)
    (h1 : ¬ c.Rh 1 x u y) (hxv : c.Delta.Adj x v) (huv : c.Delta.Adj u v)
    (hyv : c.Delta.Adj y v) {L M N : G ⧸ c.G2} (hLu : c.OnL u L) (hLx : c.OnL x L)
    (hMu : c.OnL u M) (hMy : c.OnL y M) (hNu : c.OnL u N) (hNv : c.OnL v N)
    (hNL : N ∈ c.deltaAt 1 u L ∨ N ∈ c.deltaAt 2 u L) (hNM : N ∈ c.deltaAt 1 u M) :
    c.Rh 2 x v y ∧ ¬ c.Rh 1 x v y := by
  clear hLu hLx hNL
  obtain ⟨hxu, huy, hxy, -⟩ := c.rh21_path h2 h1
  have hnxy : ¬ c.Delta.Adj x y := c.rh21_not_adj h1 hxu huy
  obtain ⟨L', hxL', hvL'⟩ := c.exists_onL_of_adj hxv
  obtain ⟨M', hyM', hvM'⟩ := c.exists_onL_of_adj hyv
  obtain ⟨σ, hxσ, hvσ, huσ⟩ := hI.s55 G z hJ c x v u hxv huv.symm hxu
  have hL'σ : c.LnP L' σ := c.lnP_of_adj hI.gamma2 hJ hxσ hvσ hxv hxL' hvL'
  have hNσ : c.LnP N σ := c.lnP_of_adj hI.gamma2 hJ huσ hvσ huv hNu hNv
  have hMN : M ∈ c.deltaAt 1 u N := ρ.deltaAt_symm 1 hMu hNu hNM
  have hM'N : M' ∈ c.deltaAt 1 v N :=
    (hI.s56 G z hJ c u v y huv hyv.symm huy).2.2 N M M' 1 hNu hNv hMu hMy hvM' hyM' hMN
  obtain ⟨g, hgv, -⟩ := c.exists_frame hNv
  have hU : IsSextet (ρ.sext (g⁻¹ • σ)) := ρ.isSextet_sext_at hgv hvσ
  have hNT : M24G.TrioIn (ρ.trio (g⁻¹ • N)) (ρ.sext (g⁻¹ • σ)) :=
    (M24G.mem_triosOf.1 (ρ.trio_mem_triosOf hgv hvσ hNv hNσ)).2
  have hL'T : M24G.TrioIn (ρ.trio (g⁻¹ • L')) (ρ.sext (g⁻¹ • σ)) :=
    (ρ.lnP_iff_trioIn_at hgv hvσ hvL').1 hL'σ
  have hL't : IsTrio (ρ.trio (g⁻¹ • L')) := ρ.isTrio_trio_at hgv hvL'
  have hM't : IsTrio (ρ.trio (g⁻¹ • M')) := ρ.isTrio_trio_at hgv hvM'
  obtain ⟨o, hoM', hoN⟩ :=
    Finset.not_disjoint_iff.1 ((ρ.mem_deltaAt_one_iff_at hgv hNv hvM').1 hM'N).2
  have hnot : ¬ M24G.TrioIn (ρ.trio (g⁻¹ • M')) (ρ.sext (g⁻¹ • σ)) := fun hT =>
    c.rh21_not_onP hI hJ h2 h1 hxσ
      (c.inc_pt_plane hyM' ((ρ.lnP_iff_trioIn_at hgv hvσ hvM').2 hT))
  have hκ : M24G.Kappa (ρ.sext (g⁻¹ • σ)) (ρ.trio (g⁻¹ • M')) 1 :=
    kappa_one_of_octad hU hM't hnot hoM' (hNT hoN)
  have hnd4 : M' ∉ c.deltaAt 4 v L' := fun h =>
    M24G.not_delta_four_of_kappa_one hU hM't hκ hL't hL'T
      ((ρ.mem_deltaAt_iff 4 hgv hvL' hvM').1 h)
  have hncop : ¬ c.CoL L' M' := by
    intro hτ
    obtain ⟨τ, hL'τ, hM'τ⟩ := hτ
    exact c.rh21_not_onP hI hJ h2 h1 (c.inc_pt_plane hxL' hL'τ) (c.inc_pt_plane hyM' hM'τ)
  have hnc : ¬ (M' ∈ c.deltaAt 0 v L' ∨ M' ∈ c.deltaAt 1 v L' ∨ M' ∈ c.deltaAt 2 v L') :=
    fun h => hncop ((ρ.coL_iff_deltaAt hvL' hvM').2 h)
  have hδ3 : M' ∈ c.deltaAt 3 v L' := by
    obtain ⟨i, hi, -⟩ := ρ.deltaAt_existsUnique hvL' hvM'
    fin_cases i
    · exact absurd (Or.inl hi) hnc
    · exact absurd (Or.inr (Or.inl hi)) hnc
    · exact absurd (Or.inr (Or.inr hi)) hnc
    · exact hi
    · exact absurd hi hnd4
  refine ⟨c.rh_two_iff.2 (Or.inr ⟨hxv, hyv.symm, hxy, L', M', hvL', hxL', hvM', hyM', hδ3⟩),
    ?_⟩
  intro h
  rcases c.rh_one_iff.1 h with h0 | ⟨-, -, -, m, n, hvm, hxm, hvn, hyn, hmn⟩
  · obtain ⟨-, -, hxy'⟩ := h0
    exact hnxy hxy'
  · have hm : m = L' := c.eq_of_onL hI.lineU hJ hxv.ne.symm hvm hxm hvL' hxL'
    have hn : n = M' := c.eq_of_onL hI.lineU hJ hyv.ne.symm hvn hyn hvM' hyM'
    rw [hm, hn] at hmn
    exact hncop hmn

end ClaimA

end ResM24

end CFSG.Quasithin.H13.AS91
