module

public import CFSG.Quasithin.H13.AS91Sec7Geom

public section

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open MulAction CFSG.Quasithin.Asc94
open scoped Pointwise
open CFSG.ASVolI.ChH (IsTrio IsSextet M24g S24)

section Translate

variable {G : Type*} [Group G]

theorem cInc_inv_smul_iff' (A B : Subgroup G) (g : G) (a : G ⧸ A) (b : G ⧸ B) :
    CInc A B (g⁻¹ • a) b ↔ CInc A B a (g • b) := by
  have h := cInc_smul A B g (g⁻¹ • a) b
  rw [smul_inv_smul] at h
  exact h.symm

end Translate

namespace Loc49

variable {G : Type} [Group G] [Finite G] {z : G} (c : Loc49 G z)

theorem adj_smul_iff' (g : G) (u v : G ⧸ c.G1) :
    c.Delta.Adj (g • u) (g • v) ↔ c.Delta.Adj u v :=
  CFSG.Quasithin.GraphAction.adj_smul g u v

theorem stmt7_5_two (hI : Sec7Inputs) (hJ : HypJ4 G z) {x y u : G ⧸ c.G1}
    {π : G ⧸ c.G3} (hxy : Dist2 c.Delta x y) (hx : c.OnP x π) (hy : c.OnP y π)
    (hu : c.Delta.Adj x u) (huy : c.Delta.Adj y u) : c.OnP u π :=
  c.stmt5_7_at hI.s57 hJ hx hy hxy hu huy

theorem stmt7_5_three (hI : Sec7Inputs) (hJ : HypJ4 G z) {x y : G ⧸ c.G1}
    {π : G ⧸ c.G3} {m : G ⧸ c.G2} (hxy : Dist2 c.Delta x y) (hx : c.OnP x π) (hy : c.OnP y π)
    (hm : c.OnL x m) (hmπ : c.LnP m π) :
    3 ≤ {a | c.OnL a m ∧ c.Delta.Adj x a ∧ c.Delta.Adj y a}.ncard := by
  obtain ⟨g, hgx, hgπ⟩ := c.exists_frameP hx
  have hy' : g⁻¹ • y ∈ c.ptsP :=
    (cInc_inv_smul_iff' c.G1 c.G3 g y c.pi0).2 (by rw [hgπ]; exact hy)
  have hm' : g⁻¹ • m ∈ c.lnsP :=
    (cInc_inv_smul_iff' c.G2 c.G3 g m c.pi0).2 (by rw [hgπ]; exact hmπ)
  have hx0 : c.OnL c.x0 (g⁻¹ • m) := c.onL_x0_inv_smul hgx hm
  have hnot : ¬ CInc c.G1 c.G2 (g⁻¹ • y) (g⁻¹ • m) := by
    intro h
    apply hxy.2.1
    have h' : CInc c.G1 c.G2 y m := by
      have h2 := (cInc_smul c.G1 c.G2 g (g⁻¹ • y) (g⁻¹ • m)).2 h
      rwa [smul_inv_smul, smul_inv_smul] at h2
    exact c.adj_of_onL hxy.1 hm h'
  have hnx0 : ¬ c.Delta.Adj (g⁻¹ • y) c.x0 := by
    intro h0
    apply hxy.2.1
    have h1 := (c.adj_smul_iff' g _ _).2 h0
    rw [smul_inv_smul, hgx] at h1
    exact h1.symm
  rcases hI.s533 G z hJ c (g⁻¹ • y) hy' (g⁻¹ • m) hm' hnot with hall | hcount
  · exact absurd (hall c.x0 hx0) hnx0
  ·
    have hsub : (g • ·) '' {b | CInc c.G1 c.G2 b (g⁻¹ • m) ∧ c.Delta.Adj (g⁻¹ • y) b} ⊆
        {a | c.OnL a m ∧ c.Delta.Adj x a ∧ c.Delta.Adj y a} := by
      rintro _ ⟨b, ⟨hb, hyb⟩, rfl⟩
      have hbx : c.x0 ≠ b := by
        rintro rfl
        exact hnx0 hyb
      have hxb : c.Delta.Adj c.x0 b := c.adj_of_onL hbx hx0 hb
      refine ⟨?_, ?_, ?_⟩
      · have h2 := (cInc_smul c.G1 c.G2 g b (g⁻¹ • m)).2 hb
        rwa [smul_inv_smul] at h2
      · have h2 := (c.adj_smul_iff' g c.x0 b).2 hxb
        rwa [hgx] at h2
      · have h2 := (c.adj_smul_iff' g (g⁻¹ • y) b).2 hyb
        rwa [smul_inv_smul] at h2
    have h3 := Set.ncard_le_ncard hsub
    rw [Set.ncard_image_of_injective _ (MulAction.injective g), hcount] at h3
    exact h3

end Loc49

namespace ResM24

variable {G : Type} [Group G] [Finite G] {z : G} {c : Loc49 G z} (ρ : ResM24 c)

section Conn

include ρ in
theorem stmt7_5_comp (hI : Sec7Inputs) (hJ : HypJ4 G z) {x y u w : G ⧸ c.G1}
    {π : G ⧸ c.G3} (hxy : Dist2 c.Delta x y) (hx : c.OnP x π) (hy : c.OnP y π)
    (hu : c.Delta.Adj x u ∧ c.Delta.Adj y u) (hw : c.Delta.Adj x w ∧ c.Delta.Adj y w) :
    comp c.Delta x u y w := by
  unfold comp
  refine ⟨hu, hw, ?_⟩
  have hind : ∀ {a b : G ⧸ c.G1} (ha : c.Delta.Adj x a ∧ c.Delta.Adj y a)
      (hb : c.Delta.Adj x b ∧ c.Delta.Adj y b), c.Delta.Adj a b →
      (c.Delta.induce {p | c.Delta.Adj x p ∧ c.Delta.Adj y p}).Adj ⟨a, ha⟩ ⟨b, hb⟩ :=
    fun _ _ h => h
  have huπ : c.OnP u π := c.stmt7_5_two hI hJ hxy hx hy hu.1 hu.2
  have hwπ : c.OnP w π := c.stmt7_5_two hI hJ hxy hx hy hw.1 hw.2
  obtain ⟨mu, hxmu, humu⟩ := (colGraph_adj.1 hu.1).2
  obtain ⟨mw, hxmw, hwmw⟩ := (colGraph_adj.1 hw.1).2
  have hmuπ : c.LnP mu π := c.lnP_of_adj hI.gamma2 hJ hx huπ hu.1 hxmu humu
  have hmwπ : c.LnP mw π := c.lnP_of_adj hI.gamma2 hJ hx hwπ hw.1 hxmw hwmw
  have hne : u ≠ x := hu.1.ne.symm
  by_cases hmm : mu = mw
  · have hwmu : c.OnL w mu := by
      rw [hmm]
      exact hwmw
    by_cases huw : u = w
    · subst huw
      exact SimpleGraph.Reachable.refl _
    · exact (hind hu hw (c.adj_of_onL huw humu hwmu)).reachable
  ·
    have hco : c.CoL mu mw := ⟨π, hmuπ, hmwπ⟩
    have h12 : mw ∈ c.deltaAt 1 x mu ∨ mw ∈ c.deltaAt 2 x mu := by
      rcases (ρ.coL_iff_deltaAt hxmu hxmw).1 hco with h0 | h12
      · exact absurd ((ρ.mem_deltaAt_zero_iff hxmu hxmw).1 h0).symm hmm
      · exact h12
    have hS : 3 ≤ {p | c.OnL p mw ∧ c.Delta.Adj u p}.ncard := by
      rcases h12 with h1 | h2
      · exact (c.stmt7_1_one hI.s54 hJ hxmu humu hne h1).ge
      · have hall : {p | c.OnL p mw} ⊆ {p | c.OnL p mw ∧ c.Delta.Adj u p} :=
          fun p (hp : c.OnL p mw) => ⟨hp, c.stmt7_1_two hI.s54 hJ hxmu humu hne h2 hp⟩
        have h5 := Set.ncard_le_ncard hall
        rw [c.ncard_onL mw] at h5
        omega
    have hT := c.stmt7_5_three hI hJ hxy hx hy hxmw hmwπ
    have hsub : {p | c.OnL p mw ∧ c.Delta.Adj u p} ∪
        {p | c.OnL p mw ∧ c.Delta.Adj x p ∧ c.Delta.Adj y p} ⊆ {p | c.OnL p mw} := by
      rintro p (hp | hp) <;> exact hp.1
    have h5 := Set.ncard_le_ncard hsub
    rw [c.ncard_onL mw] at h5
    have hinter := Set.ncard_union_add_ncard_inter {p | c.OnL p mw ∧ c.Delta.Adj u p}
      {p | c.OnL p mw ∧ c.Delta.Adj x p ∧ c.Delta.Adj y p}
    have hne0 : ({p | c.OnL p mw ∧ c.Delta.Adj u p} ∩
        {p | c.OnL p mw ∧ c.Delta.Adj x p ∧ c.Delta.Adj y p}).ncard ≠ 0 := by
      omega
    obtain ⟨b', hb1, hb2⟩ := Set.nonempty_of_ncard_ne_zero hne0
    have hb'D : c.Delta.Adj x b' ∧ c.Delta.Adj y b' := hb2.2
    have h1 := (hind hu hb'D hb1.2).reachable
    by_cases hbw : b' = w
    · subst hbw
      exact h1
    · have h2 : c.Delta.Adj b' w := c.adj_of_onL hbw hb2.1 hwmw
      exact h1.trans (hind hb'D hw h2).reachable

end Conn

end ResM24

end CFSG.Quasithin.H13.AS91
