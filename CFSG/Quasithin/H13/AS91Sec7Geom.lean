module

public import CFSG.Quasithin.H13.AS91Sec7Inputs
public import CFSG.Quasithin.H13.AS91Sec7Chain
public import CFSG.Quasithin.H13.AS91Sec7Inc

public section

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open MulAction CFSG.Quasithin.Asc94
open scoped Pointwise
open CFSG.ASVolI.ChH (IsTrio IsSextet M24g S24)

section Translate

variable {G : Type*} [Group G]

private theorem cInc_inv_smul_iff (A B : Subgroup G) {g : G} {a : G ⧸ A} {b b' : G ⧸ B}
    (hb : g • b' = b) : CInc A B (g⁻¹ • a) b' ↔ CInc A B a b := by
  subst hb
  rw [← cInc_smul A B g⁻¹ a (g • b'), inv_smul_smul]

end Translate

namespace Loc49

variable {G : Type} [Group G] [Finite G] {z : G} (c : Loc49 G z)

private theorem adj_smul_iff (g : G) (u v : G ⧸ c.G1) :
    c.Delta.Adj (g • u) (g • v) ↔ c.Delta.Adj u v :=
  CFSG.Quasithin.GraphAction.adj_smul g u v

private theorem dist2_smul_iff (g : G) (u v : G ⧸ c.G1) :
    Dist2 c.Delta (g • u) (g • v) ↔ Dist2 c.Delta u v := by
  unfold Dist2
  rw [(MulAction.injective g).ne_iff, c.adj_smul_iff]
  refine and_congr Iff.rfl (and_congr Iff.rfl ⟨?_, ?_⟩)
  · rintro ⟨w, h1, h2⟩
    refine ⟨g⁻¹ • w, ?_, ?_⟩
    · rw [← c.adj_smul_iff g, smul_inv_smul]
      exact h1
    · rw [← c.adj_smul_iff g, smul_inv_smul]
      exact h2
  · rintro ⟨w, h1, h2⟩
    exact ⟨g • w, (c.adj_smul_iff g _ _).2 h1, (c.adj_smul_iff g _ _).2 h2⟩

theorem exists_frameP {a : G ⧸ c.G1} {σ : G ⧸ c.G3} (h : c.OnP a σ) :
    ∃ g : G, g • c.x0 = a ∧ g • c.pi0 = σ := by
  obtain ⟨g, hg1, hg2⟩ := h
  refine ⟨g, ?_, ?_⟩
  · rw [← hg1]
    simp [Loc49.x0, basePt, MulAction.Quotient.smul_mk]
  · rw [← hg2]
    simp [Loc49.pi0, basePt, MulAction.Quotient.smul_mk]

theorem mem_deltaAt_iff_frame {i : Fin 5} {a : G ⧸ c.G1} {m n : G ⧸ c.G2} {g : G}
    (hg : g • c.x0 = a) (hl : g • c.l0 = m) : n ∈ c.deltaAt i a m ↔ g⁻¹ • n ∈ c.delta i := by
  constructor
  · rintro ⟨g', hg', hl', hn⟩
    have hmem : g⁻¹ * g' ∈ c.G1 ⊓ c.G2 := by
      refine ⟨?_, ?_⟩
      · have h1 : g⁻¹ * g' ∈ stabilizer G c.x0 := MulAction.mem_stabilizer_iff.2 (by
          rw [mul_smul, hg', ← hg, inv_smul_smul])
        rwa [c.stab_x0] at h1
      · have h2 : g⁻¹ * g' ∈ stabilizer G c.l0 := MulAction.mem_stabilizer_iff.2 (by
          rw [mul_smul, hl', ← hl, inv_smul_smul])
        rwa [show stabilizer G c.l0 = c.G2 from stabilizer_mk_one c.G2] at h2
    have e : g⁻¹ • n = (g⁻¹ * g') • (g'⁻¹ • n) := by
      rw [← mul_smul]
      group
    rw [e, c.smul_mem_delta hmem]
    exact hn
  · intro h
    exact ⟨g, hg, hl, h⟩

theorem onL_of_mem_deltaAt {i : Fin 5} {a : G ⧸ c.G1} {m n : G ⧸ c.G2}
    (h : n ∈ c.deltaAt i a m) : c.OnL a n := by
  obtain ⟨g, hg, -, hn⟩ := h
  have h1 : CInc c.G1 c.G2 c.x0 (g⁻¹ • n) := hn.1.symm'
  have h2 := (cInc_smul c.G1 c.G2 g c.x0 (g⁻¹ • n)).2 h1
  rwa [hg, smul_inv_smul] at h2

theorem adj_of_onL {a b : G ⧸ c.G1} {m : G ⧸ c.G2} (hab : a ≠ b) (ha : c.OnL a m)
    (hb : c.OnL b m) : c.Delta.Adj a b :=
  ⟨hab, m, ha, hb⟩

theorem ncard_onL (m : G ⧸ c.G2) : {a | c.OnL a m}.ncard = 5 :=
  c.ncard_objOf_line m

theorem eq_of_onL (hLU : Stmt5_LineU) (hJ : HypJ4 G z) {a b : G ⧸ c.G1} {m n : G ⧸ c.G2}
    (hab : a ≠ b) (ham : c.OnL a m) (hbm : c.OnL b m) (han : c.OnL a n) (hbn : c.OnL b n) :
    m = n := by
  obtain ⟨g, hga, hgm⟩ := c.exists_frame ham
  have hb'L : g⁻¹ • b ∈ c.ptsL := (cInc_inv_smul_iff c.G1 c.G2 hgm).2 hbm
  have hb'x : g⁻¹ • b ≠ c.x0 := by
    intro h
    apply hab
    rw [← hga, ← h, smul_inv_smul]
  have hxn : CInc c.G1 c.G2 c.x0 (g⁻¹ • n) := c.onL_x0_inv_smul hga han
  have hbn' : CInc c.G1 c.G2 (g⁻¹ • b) (g⁻¹ • n) := (cInc_smul c.G1 c.G2 g⁻¹ b n).2 hbn
  obtain ⟨h, hh⟩ := c.exists_G1_smul_l0 hxn
  have hb''L : (h : G)⁻¹ • g⁻¹ • b ∈ c.ptsL := by
    rw [← hh] at hbn'
    exact (cInc_inv_smul_iff c.G1 c.G2 (a := g⁻¹ • b) rfl).2 hbn'
  have hb''x : (h : G)⁻¹ • g⁻¹ • b ≠ c.x0 := by
    intro h'
    apply hb'x
    rw [inv_smul_eq_iff, c.smul_x0_of_mem h.2] at h'
    exact h'
  obtain ⟨e, he, hee⟩ := c.E_transitive hb''L hb'L hb''x hb'x
  have hstab : (e * (h : G)⁻¹) ∈ c.G1 ⊓ stabilizer G (g⁻¹ • b) := by
    refine Subgroup.mem_inf.2 ⟨mul_mem (c.E_le_G1 he) (inv_mem h.2),
      MulAction.mem_stabilizer_iff.2 ?_⟩
    rw [mul_smul, hee]
  have hG2 : e * (h : G)⁻¹ ∈ c.G2 := hLU G z hJ c _ hb'L hb'x hstab
  have hhG2 : (h : G) ∈ c.G2 := by
    have : (h : G)⁻¹ ∈ c.G2 := by
      have := mul_mem (inv_mem (c.E_le_G2 he)) hG2
      simpa using this
    simpa using inv_mem this
  have hl : (h : G) • c.l0 = c.l0 := by
    have : (h : G) ∈ stabilizer G c.l0 := by
      rw [show stabilizer G c.l0 = c.G2 from stabilizer_mk_one c.G2]
      exact hhG2
    exact MulAction.mem_stabilizer_iff.1 this
  have hn : g⁻¹ • n = c.l0 := by rw [← hh, hl]
  rw [← hgm, ← hn, smul_inv_smul]

theorem lnP_of_adj (hG2 : Stmt5_Gamma2) (hJ : HypJ4 G z) {a b : G ⧸ c.G1} {σ : G ⧸ c.G3}
    {m : G ⧸ c.G2} (ha : c.OnP a σ) (hb : c.OnP b σ) (hab : c.Delta.Adj a b) (ham : c.OnL a m)
    (hbm : c.OnL b m) : c.LnP m σ := by
  obtain ⟨g, -, hgσ⟩ := c.exists_frameP ha
  have ha' : g⁻¹ • a ∈ c.ptsP := (cInc_inv_smul_iff c.G1 c.G3 hgσ).2 ha
  have hb' : g⁻¹ • b ∈ c.ptsP := (cInc_inv_smul_iff c.G1 c.G3 hgσ).2 hb
  have hab' : c.Delta.Adj (g⁻¹ • a) (g⁻¹ • b) := (c.adj_smul_iff g⁻¹ a b).2 hab
  have ham' : CInc c.G1 c.G2 (g⁻¹ • a) (g⁻¹ • m) := (cInc_smul c.G1 c.G2 g⁻¹ a m).2 ham
  have hbm' : CInc c.G1 c.G2 (g⁻¹ • b) (g⁻¹ • m) := (cInc_smul c.G1 c.G2 g⁻¹ b m).2 hbm
  have hm' : g⁻¹ • m ∈ c.lnsP := hG2 G z hJ c _ _ ha' hb' hab' _ ham' hbm'
  have h := (cInc_smul c.G2 c.G3 g (g⁻¹ • m) c.pi0).2 hm'
  rwa [smul_inv_smul, hgσ] at h

theorem stmt7_1_one (h54 : Stmt5_4) (hJ : HypJ4 G z) {x y : G ⧸ c.G1} {l m : G ⧸ c.G2}
    (hl : c.OnL x l) (hy : c.OnL y l) (hyx : y ≠ x) (hδ : m ∈ c.deltaAt 1 x l) :
    {a | c.OnL a m ∧ c.Delta.Adj y a}.ncard = 3 := by
  obtain ⟨g, hgx, hgl⟩ := c.exists_frame hl
  have hk : g⁻¹ • m ∈ c.delta 1 := (c.mem_deltaAt_iff_frame hgx hgl).1 hδ
  have hy' : g⁻¹ • y ∈ c.ptsL := (cInc_inv_smul_iff c.G1 c.G2 hgl).2 hy
  have hy'x : g⁻¹ • y ≠ c.x0 := by
    intro h
    apply hyx
    rw [← hgx, ← h, smul_inv_smul]
  obtain ⟨-, -, -, -, ⟨-, h3⟩, -⟩ := h54 G z hJ c (g⁻¹ • y) hy' hy'x
  have key := h3 (g⁻¹ • m) hk
  have hset : {a | c.OnL a m ∧ c.Delta.Adj y a} =
      (g • ·) '' {a | a ∈ objOf c.G1 c.G2 (g⁻¹ • m) ∧ c.Delta.Adj (g⁻¹ • y) a} := by
    ext a
    constructor
    · rintro ⟨ha, hya⟩
      exact ⟨g⁻¹ • a, ⟨(cInc_smul c.G1 c.G2 g⁻¹ a m).2 ha, (c.adj_smul_iff g⁻¹ y a).2 hya⟩,
        smul_inv_smul g a⟩
    · rintro ⟨a', ⟨ha', hya'⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · have h := (cInc_smul c.G1 c.G2 g a' (g⁻¹ • m)).2 ha'
        rwa [smul_inv_smul] at h
      · have h := (c.adj_smul_iff g (g⁻¹ • y) a').2 hya'
        rwa [smul_inv_smul] at h
  rw [hset, Set.ncard_image_of_injective _ (MulAction.injective g)]
  exact key

theorem stmt7_1_two (h54 : Stmt5_4) (hJ : HypJ4 G z) {x y : G ⧸ c.G1} {l m : G ⧸ c.G2}
    (hl : c.OnL x l) (hy : c.OnL y l) (hyx : y ≠ x) (hδ : m ∈ c.deltaAt 2 x l)
    {a : G ⧸ c.G1} (ha : c.OnL a m) : c.Delta.Adj y a := by
  obtain ⟨g, hgx, hgl⟩ := c.exists_frame hl
  have hk : g⁻¹ • m ∈ c.delta 2 := (c.mem_deltaAt_iff_frame hgx hgl).1 hδ
  have hy' : g⁻¹ • y ∈ c.ptsL := (cInc_inv_smul_iff c.G1 c.G2 hgl).2 hy
  have hy'x : g⁻¹ • y ≠ c.x0 := by
    intro h
    apply hyx
    rw [← hgx, ← h, smul_inv_smul]
  obtain ⟨-, -, -, -, -, ⟨-, h4⟩, -⟩ := h54 G z hJ c (g⁻¹ • y) hy' hy'x
  have ha' : g⁻¹ • a ∈ objOf c.G1 c.G2 (g⁻¹ • m) := (cInc_smul c.G1 c.G2 g⁻¹ a m).2 ha
  exact (c.adj_smul_iff g⁻¹ y a).1 (h4 (g⁻¹ • m) hk (g⁻¹ • a) ha')

theorem stmt5_7_at (h57 : Stmt5_7) (hJ : HypJ4 G z) {x y u : G ⧸ c.G1} {σ : G ⧸ c.G3}
    (hx : c.OnP x σ) (hy : c.OnP y σ) (hxy : Dist2 c.Delta x y) (hu : c.Delta.Adj x u)
    (huy : c.Delta.Adj y u) : c.OnP u σ := by
  obtain ⟨g, hgx, hgσ⟩ := c.exists_frameP hx
  have hy' : g⁻¹ • y ∈ c.ptsP := (cInc_inv_smul_iff c.G1 c.G3 hgσ).2 hy
  have hgx' : g⁻¹ • x = c.x0 := by rw [← hgx, inv_smul_smul]
  have hd : Dist2 c.Delta c.x0 (g⁻¹ • y) := by
    rw [← hgx']
    exact (c.dist2_smul_iff g⁻¹ x y).2 hxy
  have hu' : c.Delta.Adj c.x0 (g⁻¹ • u) := by
    rw [← hgx']
    exact (c.adj_smul_iff g⁻¹ x u).2 hu
  have huy' : c.Delta.Adj (g⁻¹ • y) (g⁻¹ • u) := (c.adj_smul_iff g⁻¹ y u).2 huy
  have h := h57 G z hJ c (g⁻¹ • y) hd ⟨c.pi0, c.x0_mem_ptsP, hy'⟩ hy' (g⁻¹ • u) hu' huy'
  exact (cInc_inv_smul_iff c.G1 c.G3 hgσ).1 h

theorem plane_unique (h532 : Stmt5_3_2) (hJ : HypJ4 G z) {x u : G ⧸ c.G1} {σ σ' : G ⧸ c.G3}
    (hx : c.OnP x σ) (hu : c.OnP u σ) (hux : u ≠ x) (hadj : ¬ c.Delta.Adj x u)
    (hx' : c.OnP x σ') (hu' : c.OnP u σ') : σ' = σ := by
  obtain ⟨g, hgx, hgσ⟩ := c.exists_frameP hx
  have hgx' : g⁻¹ • x = c.x0 := by rw [← hgx, inv_smul_smul]
  have hfar : g⁻¹ • u ∈ c.farP := by
    refine ⟨(cInc_inv_smul_iff c.G1 c.G3 hgσ).2 hu, ?_, ?_⟩
    · intro h
      apply hux
      rw [← hgx, ← h, smul_inv_smul]
    · intro h
      apply hadj
      rw [← hgx'] at h
      exact (c.adj_smul_iff g⁻¹ x u).1 h
  have h1 : CInc c.G1 c.G3 c.x0 (g⁻¹ • σ') := by
    have h := (cInc_smul c.G1 c.G3 g⁻¹ x σ').2 hx'
    rwa [hgx'] at h
  have h2 : CInc c.G1 c.G3 (g⁻¹ • u) (g⁻¹ • σ') := (cInc_smul c.G1 c.G3 g⁻¹ u σ').2 hu'
  have h := h532 G z hJ c (g⁻¹ • u) hfar (g⁻¹ • σ') h1 h2
  rw [← hgσ, ← h, smul_inv_smul]

theorem eq_of_not_coL (h55 : Stmt5_5) (hG2 : Stmt5_Gamma2) (hJ : HypJ4 G z)
    {u y a : G ⧸ c.G1} {k l : G ⧸ c.G2} (hk : c.OnL u k) (hl : c.OnL u l) (hkl : ¬ c.CoL k l)
    (hy : c.OnL y l) (hyu : y ≠ u) (ha : c.OnL a k) (hay : c.Delta.Adj y a) : a = u := by
  by_contra hau
  have hua : c.Delta.Adj u a := c.adj_of_onL (Ne.symm hau) hk ha
  have huy : c.Delta.Adj u y := c.adj_of_onL (Ne.symm hyu) hl hy
  obtain ⟨σ, hσu, hσa, hσy⟩ := h55 G z hJ c u a y hua hay.symm huy
  exact hkl ⟨σ, c.lnP_of_adj hG2 hJ hσu hσa hua hk ha, c.lnP_of_adj hG2 hJ hσu hσy huy hl hy⟩

end Loc49

namespace ResM24

variable {G : Type} [Group G] [Finite G] {z : G} {c : Loc49 G z} (ρ : ResM24 c)

include ρ in
theorem deltaAt_existsUnique {a : G ⧸ c.G1} {m n : G ⧸ c.G2} (hm : c.OnL a m)
    (hn : c.OnL a n) : ∃! i : Fin 5, n ∈ c.deltaAt i a m := by
  obtain ⟨g, hg, -⟩ := c.exists_frame hm
  obtain ⟨i, hi, hu⟩ := M24G.delta_existsUnique (ρ.isTrio_trio (c.onL_x0_inv_smul hg hm))
    (ρ.isTrio_trio (c.onL_x0_inv_smul hg hn))
  exact ⟨i, (ρ.mem_deltaAt_iff i hg hm hn).2 hi,
    fun j hj => hu j ((ρ.mem_deltaAt_iff j hg hm hn).1 hj)⟩

include ρ in
theorem mem_deltaAt_zero_iff {a : G ⧸ c.G1} {m n : G ⧸ c.G2} (hm : c.OnL a m)
    (hn : c.OnL a n) : n ∈ c.deltaAt 0 a m ↔ n = m := by
  obtain ⟨g, hg, -⟩ := c.exists_frame hm
  rw [ρ.mem_deltaAt_iff 0 hg hm hn]
  show ρ.trio (g⁻¹ • n) = ρ.trio (g⁻¹ • m) ↔ n = m
  constructor
  · intro h
    exact smul_left_cancel g⁻¹ (ρ.trio_injOn (c.onL_x0_inv_smul hg hn)
      (c.onL_x0_inv_smul hg hm) h)
  · rintro rfl
    rfl

section Cop

include ρ in
theorem coL_iff_deltaAt {a : G ⧸ c.G1} {m n : G ⧸ c.G2} (hm : c.OnL a m) (hn : c.OnL a n) :
    c.CoL m n ↔ n ∈ c.deltaAt 0 a m ∨ n ∈ c.deltaAt 1 a m ∨ n ∈ c.deltaAt 2 a m := by
  obtain ⟨g, hg, -⟩ := c.exists_frame hm
  have h1 : c.CoL m n ↔ M24G.Coplanar (ρ.trio (g⁻¹ • m)) (ρ.trio (g⁻¹ • n)) :=
    ρ.coplanar_iff_at hg hm hn
  rw [h1, M24G.coplanar_iff_delta (ρ.isTrio_trio (c.onL_x0_inv_smul hg hm))
    (ρ.isTrio_trio (c.onL_x0_inv_smul hg hn)), ρ.mem_deltaAt_iff 0 hg hm hn,
    ρ.mem_deltaAt_iff 1 hg hm hn, ρ.mem_deltaAt_iff 2 hg hm hn]

end Cop

end ResM24

end CFSG.Quasithin.H13.AS91
