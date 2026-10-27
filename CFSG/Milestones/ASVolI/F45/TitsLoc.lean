module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsGeoPtLocThm
public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsGeoLnLoc
public import CFSG.Quasithin.Recognition.F4Index

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.TitsGeo CFSG.Quasithin.F7
  CFSG.Quasithin.RankTwoAmalgam.Completion

section Data

variable {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y]

structure burnsideF45_TitsData (c : α.Completion Y) : Prop where
  faithful : c.IsFaithful
  poly : IsGenPolygon c.graph 8
  pt : ∃ b₀, PtLoc c.G0 c.graph c.xv b₀ c.lv
  aff : ∃ lab, AffLab c.G0 c.graph c.xv lab
  ln : ∃ b₇ b₁ b₂, LnLoc c.G0 c.graph c.lv b₇ b₁ b₂
  cardx : Nat.card (stv c c.xv) = 10240
  cardl : Nat.card (stv c c.lv) = 6144

@[expose] def burnsideF45_nbrKer (c : α.Completion Y) (u : c.Γ) : Subgroup c.G0 where
  carrier := {g | g • u = u ∧ ∀ w, c.graph.Adj u w → g • w = w}
  one_mem' := ⟨one_smul _ _, fun _ _ => one_smul _ _⟩
  mul_mem' := fun {a b} ha hb =>
    ⟨by rw [mul_smul, hb.1, ha.1], fun w hw => by rw [mul_smul, hb.2 w hw, ha.2 w hw]⟩
  inv_mem' := fun {a} ha =>
    ⟨by rw [inv_smul_eq_iff, ha.1], fun w hw => by rw [inv_smul_eq_iff, ha.2 w hw]⟩

theorem burnsideF45_nbrKer_le (c : α.Completion Y) (u : c.Γ) :
    burnsideF45_nbrKer c u ≤ stv c u := fun _ hg => MulAction.mem_stabilizer_iff.mpr hg.1

theorem burnsideF45_nbrKer_normal (c : α.Completion Y) (u : c.Γ) :
    ((burnsideF45_nbrKer c u).subgroupOf (stv c u)).Normal := by
  refine ⟨fun g hg h => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hg ⊢
  have hh : (h : c.G0) • u = u := MulAction.mem_stabilizer_iff.mp h.2
  have hh' : (h : c.G0)⁻¹ • u = u := by rw [inv_smul_eq_iff, hh]
  refine ⟨?_, fun w hw => ?_⟩
  · simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_smul, hh', hg.1, hh]
  · have hw' : c.graph.Adj u ((h : c.G0)⁻¹ • w) := by
      have := (GraphAction.adj_smul ((h : c.G0)⁻¹) u w).mpr hw
      rwa [hh'] at this
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_smul, hg.2 _ hw', smul_inv_smul]

theorem burnsideF45_nbrKer_le_pCoreOf (c : α.Completion Y) (u : c.Γ)
    (h : IsPGroup 2 (burnsideF45_nbrKer c u)) :
    burnsideF45_nbrKer c u ≤ pCoreOf 2 (stv c u) :=
  CFSG.LieType.BorelTits.le_pCoreOf 2 (burnsideF45_nbrKer_le c u) (burnsideF45_nbrKer_normal c u) h

theorem burnsideF45_relIndex_stv (c : α.Completion Y) (H : Subgroup c.G0) (w : c.Γ) :
    (stv c w).relIndex H = (MulAction.orbit H w).ncard := by
  have h : (stv c w).subgroupOf H = MulAction.stabilizer H w := by
    ext g
    rw [Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
    exact Iff.rfl
  rw [Subgroup.relIndex, h, MulAction.index_stabilizer]

@[expose] def burnsideF45_edge {V : Type*} {Γ : SimpleGraph V} {u w : V} (h : Γ.Adj u w) :
    GPath Γ 1 :=
  (GPath.triv u).snoc w h

theorem burnsideF45_edge_zero {V : Type*} {Γ : SimpleGraph V} {u w : V} (h : Γ.Adj u w) :
    burnsideF45_edge h 0 = u := rfl

theorem burnsideF45_edge_one {V : Type*} {Γ : SimpleGraph V} {u w : V} (h : Γ.Adj u w) :
    burnsideF45_edge h 1 = w := GPath.snoc_last _ _ _

theorem burnsideF45_edge_mem {V : Type*} {Γ : SimpleGraph V} {u w : V} (h : Γ.Adj u w) :
    burnsideF45_edge h ∈ GPath.nbPaths Γ u 1 :=
  ⟨rfl, fun i hi => absurd hi (by omega)⟩

theorem burnsideF45_aff_two_fix : ∀ a b i j : ZMod 5, i ≠ j →
    a * i + b = i → a * j + b = j → a = 1 ∧ b = 0 := by
  decide

theorem burnsideF45_adj_first {V : Type*} {Γ : SimpleGraph V} {a : V} {n : ℕ}
    (hn : 1 ≤ n) {q : GPath Γ n} (hq : q ∈ GPath.nbPaths Γ a n) : Γ.Adj a (q 1) := by
  have := q.adj 0 (by omega)
  rwa [hq.1] at this

theorem burnsideF45_card_pathOrbit (c : α.Completion Y) {a : c.Γ} {n : ℕ} {q : GPath c.graph n}
    (hq : q 0 = a) :
    Nat.card ↥{r : GPath c.graph n | ∃ g ∈ stv c a, g • q = r} =
      (q.stabPath : Subgroup c.G0).relIndex (stv c a) := by
  let p0 : PathSet c.graph a := ⟨n, q, hq⟩
  have hstab : MulAction.stabilizer (stv c a) p0 =
      (q.stabPath : Subgroup c.G0).subgroupOf (stv c a) := by
    ext g
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, GPath.mem_stabPath_iff]
    constructor
    · intro h i hi
      have := congrArg (fun x : PathSet c.graph a => x.2.1 i) h
      simpa [PathSet.smul_def] using this
    · intro h
      refine PathSet.ext rfl fun i => ?_
      show ((g : c.G0) • q) i = q i
      rw [GPath.smul_apply]
      by_cases hi : i ≤ n
      · exact h i hi
      · rw [q.tail i (by omega)]
        exact h n le_rfl
  rw [Subgroup.relIndex, ← hstab, MulAction.index_stabilizer]
  let ι : ↥{r : GPath c.graph n | ∃ g ∈ stv c a, g • q = r} → PathSet c.graph a := fun r =>
    ⟨n, r.1, by
      obtain ⟨g, hg, hgr⟩ := r.2
      rw [← hgr, GPath.smul_apply, hq]
      exact MulAction.mem_stabilizer_iff.mp hg⟩
  have hι : Function.Injective ι := fun r r' h => by
    have h1 : r.1 = r'.1 := by
      have := Sigma.mk.inj h
      exact eq_of_heq (by simpa using this.2)
    exact Subtype.ext h1
  have horb : MulAction.orbit (stv c a) p0 = Set.range ι := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨⟨(g : c.G0) • q, g, g.2, rfl⟩, rfl⟩
    · rintro ⟨⟨r, g, hg, rfl⟩, rfl⟩
      exact ⟨⟨g, hg⟩, rfl⟩
  rw [horb, ← Nat.card_coe_set_eq, Nat.card_range_of_injective hι]

theorem burnsideF45_pathOrbit_smul (c : α.Completion Y) {a : c.Γ} {n : ℕ} (q : GPath c.graph n)
    {g : c.G0} (hg : g ∈ stv c a) :
    {r : GPath c.graph n | ∃ h ∈ stv c a, h • (g • q) = r} =
      {r : GPath c.graph n | ∃ h ∈ stv c a, h • q = r} := by
  ext r
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h * g, mul_mem hh hg, GPath.mul_smul' _ _ _⟩
  · rintro ⟨h, hh, rfl⟩
    refine ⟨h * g⁻¹, mul_mem hh (inv_mem hg), ?_⟩
    rw [← GPath.mul_smul', inv_mul_cancel_right]

theorem burnsideF45_eq_one_of_card_two {G V : Type*} [Group G] [MulAction G V] {K : Subgroup G}
    (hK : Nat.card K = 2) {t g : G} (ht : t ∈ K) (hg : g ∈ K) {w : V} (htw : t • w ≠ w)
    (hgw : g • w = w) : g = 1 := by
  rw [Nat.card_eq_two_iff' (1 : K)] at hK
  obtain ⟨y, -, huniq⟩ := hK
  by_contra hg1
  have e1 : (⟨g, hg⟩ : K) = y := huniq _ (fun h => hg1 (congrArg Subtype.val h))
  have e2 : (⟨t, ht⟩ : K) = y := huniq _ (fun h => htw (by
    have : t = 1 := congrArg Subtype.val h
    rw [this, one_smul]))
  have : g = t := congrArg Subtype.val (e1.trans e2.symm)
  exact htw (this ▸ hgw)

@[expose] def burnsideF45_dih (e b : ZMod 5) : DihedralGroup 5 :=
  if e = 1 then DihedralGroup.r b else DihedralGroup.sr (-b)

theorem burnsideF45_dih_mul : ∀ e₁ e₂ b₁ b₂ : ZMod 5, (e₁ = 1 ∨ e₁ = -1) → (e₂ = 1 ∨ e₂ = -1) →
    burnsideF45_dih e₁ b₁ * burnsideF45_dih e₂ b₂ = burnsideF45_dih (e₁ * e₂) (e₁ * b₂ + b₁) := by
  decide

theorem burnsideF45_dih_inj : ∀ e₁ e₂ b₁ b₂ : ZMod 5, (e₁ = 1 ∨ e₁ = -1) → (e₂ = 1 ∨ e₂ = -1) →
    burnsideF45_dih e₁ b₁ = burnsideF45_dih e₂ b₂ → e₁ = e₂ ∧ b₁ = b₂ := by
  decide

theorem burnsideF45_aff_iter : ∀ e b : ZMod 5, (fun i => e * i + b)^[10] 0 = 0 →
    (fun i => e * i + b)^[10] 1 = 1 → e = 1 ∨ e = -1 := by
  decide

end Data

namespace burnsideF45_TitsData

variable {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y] [Finite Y] {c : α.Completion Y}
  (T : burnsideF45_TitsData c)

include T

theorem card_nbrs_xv : Nat.card (CosetGeom.nbrs c.xv) = 5 := by
  obtain ⟨lab, A⟩ := T.aff
  have e : Nat.card (ZMod 5) = Nat.card (CosetGeom.nbrs c.xv) :=
    Nat.card_congr (Equiv.ofBijective (fun i : ZMod 5 => (⟨lab i, A.adj i⟩ : CosetGeom.nbrs c.xv))
      ⟨fun i j hij => A.inj (congrArg Subtype.val hij), fun ⟨u, hu⟩ => by
        obtain ⟨i, hi⟩ := A.surj u hu
        exact ⟨i, Subtype.ext hi⟩⟩)
  rw [← e]
  simp [Nat.card_eq_fintype_card, ZMod.card]

theorem card_nbrs_lv : Nat.card (CosetGeom.nbrs c.lv) = 3 := by
  obtain ⟨b₇, b₁, b₂, L⟩ := T.ln
  rw [Nat.card_coe_set_eq]
  exact L.card

theorem qOne_eq : α.qOne = 4 := by
  have h := card_nbrs T.faithful c.xv
  rw [T.card_nbrs_xv] at h
  have h' : α.qv false = α.qOne := rfl
  change 5 = α.qv false + 1 at h
  omega

theorem qTwo_eq : α.qTwo = 2 := by
  have h := card_nbrs T.faithful c.lv
  rw [T.card_nbrs_lv] at h
  have h' : α.qv true = α.qTwo := rfl
  change 3 = α.qv true + 1 at h
  omega

theorem hval : ∀ v a b : c.Γ, ∃ w, c.graph.Adj v w ∧ w ≠ a ∧ w ≠ b :=
  exists_nbr_ne T.faithful (by rw [T.qOne_eq]; norm_num) (by rw [T.qTwo_eq])

theorem transX : c.PathTrans c.xv 8 := by
  obtain ⟨b₀, P⟩ := T.pt
  exact fun q q' hq hq' => P.pathTrans T.poly hq hq'

theorem transL : c.PathTrans c.lv 7 := by
  obtain ⟨b₇, b₁, b₂, L⟩ := T.ln
  exact fun q q' hq hq' => L.pathTrans7 T.poly hq hq'

theorem orbit_lv : MulAction.orbit (stv c c.xv) c.lv = CosetGeom.nbrs c.xv := by
  obtain ⟨b₀, P⟩ := T.pt
  ext u
  constructor
  · rintro ⟨g, rfl⟩
    have h1 : (g : c.G0) • c.xv = c.xv := MulAction.mem_stabilizer_iff.mp g.2
    have := (GraphAction.adj_smul (g : c.G0) c.xv c.lv).mpr P.adj
    rw [h1] at this
    exact this
  · intro hu
    obtain ⟨k, hk1, -, hk3⟩ := P.trans u hu
    exact ⟨⟨k, MulAction.mem_stabilizer_iff.mpr hk1⟩, hk3⟩

theorem card_borel : Nat.card ↥(stv c c.xv ⊓ stv c c.lv) = 2048 := by
  have h1 := Subgroup.relIndex_mul_card (stv c c.lv) (stv c c.xv)
  rw [burnsideF45_relIndex_stv, T.orbit_lv, ← Nat.card_coe_set_eq, T.card_nbrs_xv, T.cardx,
    inf_comm] at h1
  omega

theorem isPGroup_borel : IsPGroup 2 ↥(stv c c.xv ⊓ stv c c.lv) :=
  IsPGroup.of_card (n := 11) (by rw [T.card_borel]; norm_num)

theorem nbrKer_le_borel_x : burnsideF45_nbrKer c c.xv ≤ stv c c.xv ⊓ stv c c.lv := fun _ hg =>
  ⟨MulAction.mem_stabilizer_iff.mpr hg.1,
    MulAction.mem_stabilizer_iff.mpr (hg.2 _ CosetGeom.adj_γ₀_γ₁)⟩

theorem nbrKer_le_borel_l : burnsideF45_nbrKer c c.lv ≤ stv c c.xv ⊓ stv c c.lv := fun _ hg =>
  ⟨MulAction.mem_stabilizer_iff.mpr (hg.2 _ CosetGeom.adj_γ₀_γ₁.symm),
    MulAction.mem_stabilizer_iff.mpr hg.1⟩

theorem nbrKer_x_le : burnsideF45_nbrKer c c.xv ≤ pCoreOf 2 (stv c c.xv) :=
  burnsideF45_nbrKer_le_pCoreOf c c.xv (T.isPGroup_borel.to_le T.nbrKer_le_borel_x)

theorem nbrKer_l_le : burnsideF45_nbrKer c c.lv ≤ pCoreOf 2 (stv c c.lv) :=
  burnsideF45_nbrKer_le_pCoreOf c c.lv (T.isPGroup_borel.to_le T.nbrKer_le_borel_l)

theorem six_x_trans {w₁ w₂ : c.Γ} (h₁ : c.graph.Adj c.xv w₁) (h₁' : w₁ ≠ c.lv)
    (h₂ : c.graph.Adj c.xv w₂) (h₂' : w₂ ≠ c.lv) :
    ∃ g ∈ stv c c.xv ⊓ stv c c.lv, g • w₁ = w₂ := by
  have hlx : c.graph.Adj c.lv c.xv := CosetGeom.adj_γ₀_γ₁.symm
  have e1 : burnsideF45_edge hlx 1 = c.xv := burnsideF45_edge_one hlx
  obtain ⟨g, hgl, hgq, hgw⟩ := GPath.exists_fix_path_smul_eq (m := 6) T.hval T.transL
    (i := 1) (by norm_num) (burnsideF45_edge_mem hlx) (y := w₁) (y' := w₂)
    (by rw [e1]; exact h₁) (by rw [e1]; exact h₂) (fun _ => h₁') (fun _ => h₂')
  have hgx : g • c.xv = c.xv := by
    have := congrArg (fun r : GPath c.graph 1 => r 1) hgq
    simpa [e1] using this
  exact ⟨g, ⟨MulAction.mem_stabilizer_iff.mpr hgx, MulAction.mem_stabilizer_iff.mpr hgl⟩, hgw⟩

theorem six_l_trans {w₁ w₂ : c.Γ} (h₁ : c.graph.Adj c.lv w₁) (h₁' : w₁ ≠ c.xv)
    (h₂ : c.graph.Adj c.lv w₂) (h₂' : w₂ ≠ c.xv) :
    ∃ g ∈ stv c c.lv ⊓ stv c c.xv, g • w₁ = w₂ := by
  have hxl : c.graph.Adj c.xv c.lv := CosetGeom.adj_γ₀_γ₁
  have e1 : burnsideF45_edge hxl 1 = c.lv := burnsideF45_edge_one hxl
  obtain ⟨g, hgx, hgq, hgw⟩ := GPath.exists_fix_path_smul_eq (m := 7) T.hval T.transX
    (i := 1) (by norm_num) (burnsideF45_edge_mem hxl) (y := w₁) (y' := w₂)
    (by rw [e1]; exact h₁) (by rw [e1]; exact h₂) (fun _ => h₁') (fun _ => h₂')
  have hgl : g • c.lv = c.lv := by
    have := congrArg (fun r : GPath c.graph 1 => r 1) hgq
    simpa [e1] using this
  exact ⟨g, ⟨MulAction.mem_stabilizer_iff.mpr hgl, MulAction.mem_stabilizer_iff.mpr hgx⟩, hgw⟩

theorem six_x_free {g : c.G0} (hg : g ∈ stv c c.xv ⊓ stv c c.lv) {w : c.Γ}
    (hw : c.graph.Adj c.xv w) (hwl : w ≠ c.lv) (hgw : g • w = w) :
    g ∈ pCoreOf 2 (stv c c.xv) := by
  obtain ⟨lab, A⟩ := T.aff
  have hgx : g • c.xv = c.xv := MulAction.mem_stabilizer_iff.mp hg.1
  have hgl : g • c.lv = c.lv := MulAction.mem_stabilizer_iff.mp hg.2
  obtain ⟨a, b, -, hab⟩ := A.aff g hgx
  obtain ⟨i, hi⟩ := A.surj c.lv CosetGeom.adj_γ₀_γ₁
  obtain ⟨j, hj⟩ := A.surj w hw
  have hij : i ≠ j := fun h => hwl (by rw [← hj, ← h, hi])
  have e1 : a * i + b = i := A.inj (by rw [← hab, hi, hgl])
  have e2 : a * j + b = j := A.inj (by rw [← hab, hj, hgw])
  obtain ⟨ha, hb⟩ := burnsideF45_aff_two_fix a b i j hij e1 e2
  refine T.nbrKer_x_le ⟨hgx, fun u hu => ?_⟩
  obtain ⟨k, rfl⟩ := A.surj u hu
  rw [hab, ha, hb, one_mul, add_zero]

theorem six_l_free {g : c.G0} (hg : g ∈ stv c c.lv ⊓ stv c c.xv) {w : c.Γ}
    (hw : c.graph.Adj c.lv w) (hwx : w ≠ c.xv) (hgw : g • w = w) :
    g ∈ pCoreOf 2 (stv c c.lv) := by
  obtain ⟨b₇, b₁, b₂, L⟩ := T.ln
  have hgl : g • c.lv = c.lv := MulAction.mem_stabilizer_iff.mp hg.1
  have hgx : g • c.xv = c.xv := MulAction.mem_stabilizer_iff.mp hg.2
  have hlx : c.graph.Adj c.lv c.xv := CosetGeom.adj_γ₀_γ₁.symm
  obtain ⟨R, hR, hRx, hRw, hT⟩ := L.exists_third hlx hw (Ne.symm hwx)
  have hgR : g • R = R := by
    have hadj : c.graph.Adj c.lv (g • R) := by
      have := (GraphAction.adj_smul g c.lv R).mpr hR
      rwa [hgl] at this
    rcases hT _ hadj with h | h | h
    · exact absurd (smul_left_cancel g (h.trans hgx.symm)) hRx
    · exact absurd (smul_left_cancel g (h.trans hgw.symm)) hRw
    · exact h
  refine T.nbrKer_l_le ⟨hgl, fun u hu => ?_⟩
  rcases hT u hu with rfl | rfl | rfl
  · exact hgx
  · exact hgw
  · exact hgR

theorem line_moves {v : c.Γ} (hv : c.graph.dist c.lv v = 8) {u : c.Γ} (hu : c.graph.Adj c.lv u) :
    ∃ k ∈ stv c c.lv ⊓ stv c v, k • u = u ∧ ∃ w, c.graph.Adj c.lv w ∧ k • w ≠ w := by
  obtain ⟨b₇, b₁, b₂, L⟩ := T.ln
  have key : ∀ b : c.Γ, (∀ u, c.graph.Adj c.lv u → ∃ k : c.G0, k • c.lv = c.lv ∧ k • b = b ∧
      k • u = u ∧ ∃ w, c.graph.Adj c.lv w ∧ k • w ≠ w) →
      (∃ h : c.G0, h • c.lv = c.lv ∧ h • b = v) →
      ∃ k ∈ stv c c.lv ⊓ stv c v, k • u = u ∧ ∃ w, c.graph.Adj c.lv w ∧ k • w ≠ w := by
    rintro b hmv ⟨h, hhl, hhb⟩
    have hh' : h⁻¹ • c.lv = c.lv := by rw [inv_smul_eq_iff, hhl]
    have hu' : c.graph.Adj c.lv (h⁻¹ • u) := by
      have := (GraphAction.adj_smul h⁻¹ c.lv u).mpr hu
      rwa [hh'] at this
    obtain ⟨k, hkl, hkb, hku, w, hw, hkw⟩ := hmv _ hu'
    refine ⟨h * k * h⁻¹, Subgroup.mem_inf.mpr ⟨MulAction.mem_stabilizer_iff.mpr ?_,
      MulAction.mem_stabilizer_iff.mpr ?_⟩, ?_, h • w, ?_, ?_⟩
    · rw [mul_smul, mul_smul, hh', hkl, hhl]
    · rw [mul_smul, mul_smul, ← hhb, inv_smul_smul, hkb]
    · rw [mul_smul, mul_smul, hku, smul_inv_smul]
    · have := (GraphAction.adj_smul h c.lv w).mpr hw
      rwa [hhl] at this
    · rw [mul_smul, mul_smul, inv_smul_smul]
      exact fun hcon => hkw (smul_left_cancel h hcon)
  rcases L.orb8 v hv with hb | hb
  · exact key b₁ L.moves1 hb
  · exact key b₂ L.moves2 hb

theorem line_two_trans {v : c.Γ} (hv : c.graph.dist c.lv v = 8) {a b a' b' : c.Γ}
    (ha : c.graph.Adj c.lv a) (hb : c.graph.Adj c.lv b) (hab : a ≠ b)
    (ha' : c.graph.Adj c.lv a') (hb' : c.graph.Adj c.lv b') (hab' : a' ≠ b') :
    ∃ g ∈ stv c c.lv ⊓ stv c v, g • a = a' ∧ g • b = b' := by
  obtain ⟨b₇, b₁, b₂, L⟩ := T.ln
  have hswap : ∀ {P Q R : c.Γ}, c.graph.Adj c.lv P → c.graph.Adj c.lv Q → c.graph.Adj c.lv R →
      P ≠ Q → P ≠ R → Q ≠ R →
      ∃ t ∈ stv c c.lv ⊓ stv c v, t • P = P ∧ t • Q = R ∧ t • R = Q := by
    intro P Q R hP hQ hR hPQ hPR hQR
    obtain ⟨t, ht, htP, w, hw, htw⟩ := T.line_moves hv hP
    obtain ⟨R', -, -, -, hT⟩ := L.exists_third hP hQ hPQ
    have hRR' : R = R' := by
      rcases hT R hR with h | h | h
      · exact absurd h.symm hPR
      · exact absurd h.symm hQR
      · exact h
    subst hRR'
    have htl : t • c.lv = c.lv := MulAction.mem_stabilizer_iff.mp ht.1
    exact ⟨t, ht, htP, swap_of_moves hPQ hPR hQR hT hP hQ hR htl htP ⟨w, hw, htw⟩⟩
  have step1 : ∃ g₁ ∈ stv c c.lv ⊓ stv c v, g₁ • a = a' := by
    by_cases haa : a = a'
    · exact ⟨1, one_mem _, by rw [one_smul, haa]⟩
    obtain ⟨R, hR, hRa, hRa', -⟩ := L.exists_third ha ha' haa
    obtain ⟨t, ht, -, hta, -⟩ := hswap hR ha ha' hRa hRa' haa
    exact ⟨t, ht, hta⟩
  obtain ⟨g₁, hg₁, hg₁a⟩ := step1
  have hg₁l : g₁ • c.lv = c.lv := MulAction.mem_stabilizer_iff.mp hg₁.1
  have hb₁ : c.graph.Adj c.lv (g₁ • b) := by
    have := (GraphAction.adj_smul g₁ c.lv b).mpr hb
    rwa [hg₁l] at this
  have hb₁a' : g₁ • b ≠ a' := by
    rw [← hg₁a]
    exact fun h => hab (smul_left_cancel g₁ h).symm
  by_cases hbb : g₁ • b = b'
  · exact ⟨g₁, hg₁, hg₁a, hbb⟩
  obtain ⟨t, ht, hta', htb, -⟩ := hswap ha' hb₁ hb' (Ne.symm hb₁a') hab' hbb
  refine ⟨t * g₁, mul_mem ht hg₁, ?_, ?_⟩
  · rw [mul_smul, hg₁a, hta']
  · rw [mul_smul, htb]

theorem line_two_trans_paths {v : c.Γ} (hv : c.graph.dist c.lv v = 8)
    {q₁ q₂ r₁ r₂ : GPath c.graph 8} (hq₁ : q₁ ∈ GPath.nbPaths c.graph c.lv 8) (hq₁v : q₁ 8 = v)
    (hq₂ : q₂ ∈ GPath.nbPaths c.graph c.lv 8) (hq₂v : q₂ 8 = v) (hq : q₁ ≠ q₂)
    (hr₁ : r₁ ∈ GPath.nbPaths c.graph c.lv 8) (hr₁v : r₁ 8 = v)
    (hr₂ : r₂ ∈ GPath.nbPaths c.graph c.lv 8) (hr₂v : r₂ 8 = v) (hr : r₁ ≠ r₂) :
    ∃ g ∈ stv c c.lv ⊓ stv c v, g • q₁ = r₁ ∧ g • q₂ = r₂ := by
  have hq1 : q₁ 1 ≠ q₂ 1 := fun h => hq (eq_of_first_last T.poly hq₁ hq₂ h (hq₁v.trans hq₂v.symm))
  have hr1 : r₁ 1 ≠ r₂ 1 := fun h => hr (eq_of_first_last T.poly hr₁ hr₂ h (hr₁v.trans hr₂v.symm))
  obtain ⟨g, hg, hg1, hg2⟩ := T.line_two_trans hv (burnsideF45_adj_first (by norm_num) hq₁)
    (burnsideF45_adj_first (by norm_num) hq₂) hq1 (burnsideF45_adj_first (by norm_num) hr₁)
    (burnsideF45_adj_first (by norm_num) hr₂) hr1
  have hgl : g • c.lv = c.lv := MulAction.mem_stabilizer_iff.mp hg.1
  have hgv : g • v = v := MulAction.mem_stabilizer_iff.mp hg.2
  refine ⟨g, hg, ?_, ?_⟩
  · refine eq_of_first_last T.poly (smul_mem_nbPaths hq₁ hgl) hr₁ (by rw [GPath.smul_apply, hg1]) ?_
    rw [GPath.smul_apply, hq₁v, hgv, hr₁v]
  · refine eq_of_first_last T.poly (smul_mem_nbPaths hq₂ hgl) hr₂ (by rw [GPath.smul_apply, hg2]) ?_
    rw [GPath.smul_apply, hq₂v, hgv, hr₂v]

theorem line_trans_paths {v : c.Γ} (hv : c.graph.dist c.lv v = 8)
    {q r : GPath c.graph 8} (hq : q ∈ GPath.nbPaths c.graph c.lv 8) (hqv : q 8 = v)
    (hr : r ∈ GPath.nbPaths c.graph c.lv 8) (hrv : r 8 = v) :
    ∃ g ∈ stv c c.lv ⊓ stv c v, g • q = r := by
  obtain ⟨b, hb, hbq, -⟩ := T.hval c.lv (q 1) (q 1)
  obtain ⟨b', hb', hbr, -⟩ := T.hval c.lv (r 1) (r 1)
  obtain ⟨g, hg, hg1, -⟩ := T.line_two_trans hv (burnsideF45_adj_first (by norm_num) hq) hb
    (Ne.symm hbq) (burnsideF45_adj_first (by norm_num) hr) hb' (Ne.symm hbr)
  have hgl : g • c.lv = c.lv := MulAction.mem_stabilizer_iff.mp hg.1
  have hgv : g • v = v := MulAction.mem_stabilizer_iff.mp hg.2
  refine ⟨g, hg, eq_of_first_last T.poly (smul_mem_nbPaths hq hgl) hr
    (by rw [GPath.smul_apply, hg1]) ?_⟩
  rw [GPath.smul_apply, hqv, hgv, hrv]

theorem card_nbPaths_lv : Nat.card ↥(GPath.nbPaths c.graph c.lv 8) = 6144 := by
  have hv : CosetGeom.vtype c.lv = true := rfl
  rw [card_nbPaths T.faithful, hv, show (8 : ℕ) = 2 * 3 + 2 from rfl,
    RankTwoAmalgam.pathNum_even]
  simp only [RankTwoAmalgam.qv, Bool.not_true, ↓reduceIte, Bool.false_eq_true, T.qOne_eq,
    T.qTwo_eq] <;> norm_num

theorem card_nbPaths_xv : Nat.card ↥(GPath.nbPaths c.graph c.xv 8) = 5120 := by
  have hv : CosetGeom.vtype c.xv = false := rfl
  rw [card_nbPaths T.faithful, hv, show (8 : ℕ) = 2 * 3 + 2 from rfl,
    RankTwoAmalgam.pathNum_even]
  simp only [RankTwoAmalgam.qv, Bool.not_false, ↓reduceIte, Bool.false_eq_true, T.qOne_eq,
    T.qTwo_eq] <;> norm_num

theorem line_card_orbit_le {q : GPath c.graph 8} (hq : q ∈ GPath.nbPaths c.graph c.lv 8) :
    Nat.card ↥{r : GPath c.graph 8 | ∃ g ∈ stv c c.lv, g • q = r} ≤ 3072 := by
  obtain ⟨b₇, b₁, b₂, L⟩ := T.ln
  rw [burnsideF45_card_pathOrbit c hq.1]
  obtain ⟨t, ht, w, -, htw⟩ := L.nontriv T.poly hq
  have hle : (q.stabPath : Subgroup c.G0) ≤ stv c c.lv := GPath.stabPath_le_stabilizer q hq.1
  have h1 := Subgroup.relIndex_mul_card (q.stabPath : Subgroup c.G0) (stv c c.lv)
  rw [inf_of_le_left hle, T.cardl] at h1
  have hne : (q.stabPath : Subgroup c.G0) ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.mem_bot] at ht
    exact htw (by rw [ht, one_smul])
  have h2 := (Subgroup.one_lt_card_iff_ne_bot _).mpr hne
  nlinarith

theorem line_orbits : ∃ q₁ ∈ GPath.nbPaths c.graph c.lv 8, ∃ q₂ ∈ GPath.nbPaths c.graph c.lv 8,
    GPath.nbPaths c.graph c.lv 8 =
      {r | ∃ g ∈ stv c c.lv, g • q₁ = r} ∪ {r | ∃ g ∈ stv c c.lv, g • q₂ = r} ∧
    Disjoint {r | ∃ g ∈ stv c c.lv, g • q₁ = r} {r | ∃ g ∈ stv c c.lv, g • q₂ = r} ∧
    Nat.card ↥{r | ∃ g ∈ stv c c.lv, g • q₁ = r} =
      Nat.card ↥{r | ∃ g ∈ stv c c.lv, g • q₂ = r} := by
  obtain ⟨b₇, b₁, b₂, L⟩ := T.ln
  haveI := finite_gpath (c := c) 8
  set O : GPath c.graph 8 → Set (GPath c.graph 8) :=
    fun q => {r | ∃ g ∈ stv c c.lv, g • q = r} with hO
  have hsub : ∀ q ∈ GPath.nbPaths c.graph c.lv 8, O q ⊆ GPath.nbPaths c.graph c.lv 8 := by
    rintro q hq _ ⟨g, hg, rfl⟩
    exact smul_mem_nbPaths hq (MulAction.mem_stabilizer_iff.mp hg)
  have hsame : ∀ q ∈ GPath.nbPaths c.graph c.lv 8, ∀ r ∈ GPath.nbPaths c.graph c.lv 8,
      (∃ h ∈ stv c c.lv, h • q 8 = r 8) → r ∈ O q := by
    rintro q hq r hr ⟨h, hh, hhqr⟩
    have hhl : h • c.lv = c.lv := MulAction.mem_stabilizer_iff.mp hh
    have hd : c.graph.dist c.lv (r 8) = 8 := end_dist T.poly le_rfl hr
    obtain ⟨g, hg, hgr⟩ := T.line_trans_paths hd (smul_mem_nbPaths hq hhl)
      (by rw [GPath.smul_apply, hhqr]) hr rfl
    exact ⟨g * h, mul_mem hg.1 hh, by rw [GPath.mul_smul', hgr]⟩
  have hcls : ∀ r ∈ GPath.nbPaths c.graph c.lv 8,
      (∃ h ∈ stv c c.lv, h • b₁ = r 8) ∨ (∃ h ∈ stv c c.lv, h • b₂ = r 8) := by
    intro r hr
    rcases L.orb8 _ (end_dist T.poly le_rfl hr) with ⟨h, hhl, hh⟩ | ⟨h, hhl, hh⟩
    · exact Or.inl ⟨h, MulAction.mem_stabilizer_iff.mpr hhl, hh⟩
    · exact Or.inr ⟨h, MulAction.mem_stabilizer_iff.mpr hhl, hh⟩
  have hjoin : ∀ {b : c.Γ} {q r : GPath c.graph 8}, q ∈ GPath.nbPaths c.graph c.lv 8 →
      r ∈ GPath.nbPaths c.graph c.lv 8 → (∃ h ∈ stv c c.lv, h • b = q 8) →
      (∃ h ∈ stv c c.lv, h • b = r 8) → r ∈ O q := by
    rintro b q r hq hr ⟨h, hh, hhq⟩ ⟨h', hh', hhr⟩
    refine hsame q hq r hr ⟨h' * h⁻¹, mul_mem hh' (inv_mem hh), ?_⟩
    rw [mul_smul, ← hhq, inv_smul_smul, hhr]
  obtain ⟨q₁, hq₁⟩ := GPath.exists_nbPaths T.hval c.lv 8
  obtain ⟨q₂, hq₂, hq₂O⟩ : ∃ q₂ ∈ GPath.nbPaths c.graph c.lv 8, q₂ ∉ O q₁ := by
    by_contra hcon
    push Not at hcon
    have := Nat.card_mono (Set.toFinite _) (show GPath.nbPaths c.graph c.lv 8 ⊆ O q₁ from hcon)
    have h1 : Nat.card ↥(O q₁) ≤ 3072 := T.line_card_orbit_le hq₁
    rw [T.card_nbPaths_lv] at this
    omega
  have hcover : GPath.nbPaths c.graph c.lv 8 = O q₁ ∪ O q₂ := by
    refine Set.Subset.antisymm (fun r hr => ?_) (Set.union_subset (hsub q₁ hq₁) (hsub q₂ hq₂))
    rcases hcls q₁ hq₁ with h1 | h1 <;> rcases hcls q₂ hq₂ with h2 | h2 <;>
      rcases hcls r hr with h3 | h3
    · exact absurd (hjoin hq₁ hq₂ h1 h2) hq₂O
    · exact absurd (hjoin hq₁ hq₂ h1 h2) hq₂O
    · exact Or.inl (hjoin hq₁ hr h1 h3)
    · exact Or.inr (hjoin hq₂ hr h2 h3)
    · exact Or.inr (hjoin hq₂ hr h2 h3)
    · exact Or.inl (hjoin hq₁ hr h1 h3)
    · exact absurd (hjoin hq₁ hq₂ h1 h2) hq₂O
    · exact absurd (hjoin hq₁ hq₂ h1 h2) hq₂O
  have hc := T.card_nbPaths_lv
  have hA : Nat.card ↥(O q₁) ≤ 3072 := T.line_card_orbit_le hq₁
  have hB : Nat.card ↥(O q₂) ≤ 3072 := T.line_card_orbit_le hq₂
  rw [hcover] at hc
  have hu := Set.ncard_union_add_ncard_inter (O q₁) (O q₂) (Set.toFinite _) (Set.toFinite _)
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq,
    ← Nat.card_coe_set_eq] at hu
  have hinter : Nat.card ↥(O q₁ ∩ O q₂) = 0 := by omega
  refine ⟨q₁, hq₁, q₂, hq₂, hcover, ?_, ?_⟩
  swap
  · show Nat.card ↥(O q₁) = Nat.card ↥(O q₂)
    omega
  rw [Set.disjoint_iff_inter_eq_empty]
  rw [Nat.card_coe_set_eq, Set.ncard_eq_zero (Set.toFinite _)] at hinter
  exact hinter

theorem line_card_stabPath {q : GPath c.graph 8} (hq : q ∈ GPath.nbPaths c.graph c.lv 8) :
    Nat.card (q.stabPath : Subgroup c.G0) = 2 := by
  obtain ⟨q₁, hq₁, q₂, hq₂, hcov, hdisj, heq⟩ := T.line_orbits
  haveI := finite_gpath (c := c) 8
  have hc := T.card_nbPaths_lv
  rw [hcov, Nat.card_coe_set_eq, Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _),
    ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq] at hc
  have h3072 : Nat.card ↥{r : GPath c.graph 8 | ∃ g ∈ stv c c.lv, g • q = r} = 3072 := by
    have hmem : q ∈ {r : GPath c.graph 8 | ∃ g ∈ stv c c.lv, g • q₁ = r} ∪
        {r : GPath c.graph 8 | ∃ g ∈ stv c c.lv, g • q₂ = r} := hcov ▸ hq
    rcases hmem with ⟨g, hg, rfl⟩ | ⟨g, hg, rfl⟩
    · rw [burnsideF45_pathOrbit_smul c q₁ hg]
      omega
    · rw [burnsideF45_pathOrbit_smul c q₂ hg]
      omega
  rw [burnsideF45_card_pathOrbit c hq.1] at h3072
  have h1 := Subgroup.relIndex_mul_card (q.stabPath : Subgroup c.G0) (stv c c.lv)
  rw [inf_of_le_left (GPath.stabPath_le_stabilizer q hq.1), T.cardl, h3072] at h1
  omega

theorem line_compl {v : c.Γ} (hv : c.graph.dist c.lv v = 8)
    (hQ : ∀ w, c.graph.Adj c.lv w → ∀ q ∈ pCoreOf 2 (stv c c.lv), q • w = w) :
    IsComplementIn (stv c c.lv ⊓ stv c v) (pCoreOf 2 (stv c c.lv)) (stv c c.lv) := by
  obtain ⟨b₇, b₁, b₂, L⟩ := T.ln
  have hlx : c.graph.Adj c.lv c.xv := CosetGeom.adj_γ₀_γ₁.symm
  refine ⟨CFSG.LieType.BorelTits.pCoreOf_le 2 _, inf_le_left, ?_, fun g hg => ?_⟩
  · refine eq_bot_iff.mpr fun g hg => ?_
    obtain ⟨hgQ, hgl, hgv⟩ := hg
    obtain ⟨q, hq, hq1, hq8⟩ := exists_base_path T.poly hlx hv
    have hgq : g ∈ (q.stabPath : Subgroup c.G0) :=
      mem_stabPath_of_fix T.poly hq (MulAction.mem_stabilizer_iff.mp hgl)
        (by rw [hq1]; exact hQ _ hlx g hgQ) (by rw [hq8]; exact MulAction.mem_stabilizer_iff.mp hgv)
    obtain ⟨t, ht, w, hw, htw⟩ := L.nontriv T.poly hq
    rw [Subgroup.mem_bot]
    exact burnsideF45_eq_one_of_card_two (T.line_card_stabPath hq) ht hgq htw (hQ w hw g hgQ)
  · have hgl : g • c.lv = c.lv := MulAction.mem_stabilizer_iff.mp hg
    have hmap : ∀ t, c.graph.Adj c.lv t → c.graph.Adj c.lv (g • t) := fun t ht => by
      have := (GraphAction.adj_smul g c.lv t).mpr ht
      rwa [hgl] at this
    obtain ⟨b, hb, hbx, -⟩ := T.hval c.lv c.xv c.xv
    have hgbx : g • c.xv ≠ g • b := fun h => hbx (smul_left_cancel g h).symm
    obtain ⟨k, hk, hkx, hkb⟩ := T.line_two_trans hv hlx hb (Ne.symm hbx) (hmap _ hlx) (hmap _ hb)
      hgbx
    have hkl : k • c.lv = c.lv := MulAction.mem_stabilizer_iff.mp hk.1
    have hkmap : ∀ t, c.graph.Adj c.lv t → c.graph.Adj c.lv (k • t) := fun t ht => by
      have := (GraphAction.adj_smul k c.lv t).mpr ht
      rwa [hkl] at this
    obtain ⟨R, hR, hRx, hRb, hT⟩ := L.exists_third hlx hb (Ne.symm hbx)
    obtain ⟨R', -, -, -, hT'⟩ := L.exists_third (hmap _ hlx) (hmap _ hb) hgbx
    have hkR : k • R = R' := by
      rcases hT' _ (hkmap _ hR) with h | h | h
      · exact absurd (smul_left_cancel k (h.trans hkx.symm)) hRx
      · exact absurd (smul_left_cancel k (h.trans hkb.symm)) hRb
      · exact h
    have hgR : g • R = R' := by
      rcases hT' _ (hmap _ hR) with h | h | h
      · exact absurd (smul_left_cancel g h) hRx
      · exact absurd (smul_left_cancel g h) hRb
      · exact h
    have hagree : ∀ u, c.graph.Adj c.lv u → k • u = g • u := by
      intro u hu
      rcases hT u hu with rfl | rfl | rfl
      · exact hkx
      · exact hkb
      · rw [hkR, hgR]
    refine ⟨g * k⁻¹, T.nbrKer_l_le ⟨?_, fun u hu => ?_⟩, k, hk, by group⟩
    · rw [mul_smul, inv_smul_eq_iff.mpr hkl.symm, hgl]
    · have hu' : c.graph.Adj c.lv (k⁻¹ • u) := by
        have := (GraphAction.adj_smul k⁻¹ c.lv u).mpr hu
        rwa [inv_smul_eq_iff.mpr hkl.symm] at this
      rw [mul_smul, ← hagree _ hu', smul_inv_smul]

theorem point_card_stabPath {q : GPath c.graph 8} (hq : q ∈ GPath.nbPaths c.graph c.xv 8) :
    Nat.card (q.stabPath : Subgroup c.G0) = 2 := by
  have h := relIndex_stabPath T.faithful T.transX hq
  rw [← card_nbPaths T.faithful, T.card_nbPaths_xv] at h
  have h1 := Subgroup.relIndex_mul_card (q.stabPath : Subgroup c.G0) (stv c c.xv)
  rw [inf_of_le_left (GPath.stabPath_le_stabilizer q hq.1), T.cardx, h] at h1
  omega

theorem point_orbit {v : c.Γ} (hv : c.graph.dist c.xv v = 8) :
    MulAction.orbit ↥(stv c c.xv ⊓ stv c v) c.lv = CosetGeom.nbrs c.xv := by
  ext u
  constructor
  · rintro ⟨g, rfl⟩
    have h1 : (g : c.G0) • c.xv = c.xv := MulAction.mem_stabilizer_iff.mp g.2.1
    have := (GraphAction.adj_smul (g : c.G0) c.xv c.lv).mpr CosetGeom.adj_γ₀_γ₁
    rw [h1] at this
    exact this
  · intro hu
    have hxl : c.graph.Adj c.xv c.lv := CosetGeom.adj_γ₀_γ₁
    obtain ⟨q, hq, hq1, hq8⟩ := exists_base_path T.poly hxl hv
    obtain ⟨r, hr, hr1, hr8⟩ := exists_base_path T.poly hu hv
    obtain ⟨g, hgx, hgq⟩ := T.transX q r hq hr
    have e8 := congrArg (fun t : GPath c.graph 8 => t 8) hgq
    have e1 := congrArg (fun t : GPath c.graph 8 => t 1) hgq
    simp only [GPath.smul_apply] at e8 e1
    rw [hq8, hr8] at e8
    rw [hq1, hr1] at e1
    exact ⟨⟨g, MulAction.mem_stabilizer_iff.mpr hgx, MulAction.mem_stabilizer_iff.mpr e8⟩, e1⟩

theorem point_card {v : c.Γ} (hv : c.graph.dist c.xv v = 8) :
    Nat.card ↥(stv c c.xv ⊓ stv c v) = 10 := by
  have hxl : c.graph.Adj c.xv c.lv := CosetGeom.adj_γ₀_γ₁
  obtain ⟨q, hq, hq1, hq8⟩ := exists_base_path T.poly hxl hv
  have h1 := Subgroup.relIndex_mul_card (stv c c.lv) (stv c c.xv ⊓ stv c v)
  have hst : stv c c.lv ⊓ (stv c c.xv ⊓ stv c v) = (q.stabPath : Subgroup c.G0) := by
    ext g
    constructor
    · rintro ⟨hgl, hgx, hgv⟩
      exact mem_stabPath_of_fix T.poly hq (MulAction.mem_stabilizer_iff.mp hgx)
        (by rw [hq1]; exact MulAction.mem_stabilizer_iff.mp hgl)
        (by rw [hq8]; exact MulAction.mem_stabilizer_iff.mp hgv)
    · intro hg
      refine ⟨MulAction.mem_stabilizer_iff.mpr ?_, MulAction.mem_stabilizer_iff.mpr ?_,
        MulAction.mem_stabilizer_iff.mpr ?_⟩
      · rw [← hq1]; exact hg 1 (by norm_num)
      · rw [← hq.1]; exact hg 0 (by norm_num)
      · rw [← hq8]; exact hg 8 le_rfl
  rw [hst, T.point_card_stabPath hq, burnsideF45_relIndex_stv, T.point_orbit hv,
    ← Nat.card_coe_set_eq, T.card_nbrs_xv] at h1
  omega

theorem point_faithful {v : c.Γ} (hv : c.graph.dist c.xv v = 8) {g : c.G0}
    (hg : g ∈ stv c c.xv ⊓ stv c v) (hfix : ∀ w, c.graph.Adj c.xv w → g • w = w) : g = 1 := by
  obtain ⟨b₀, P⟩ := T.pt
  have hxl : c.graph.Adj c.xv c.lv := CosetGeom.adj_γ₀_γ₁
  obtain ⟨q, hq, hq1, hq8⟩ := exists_base_path T.poly hxl hv
  have hgq : g ∈ (q.stabPath : Subgroup c.G0) :=
    mem_stabPath_of_fix T.poly hq (MulAction.mem_stabilizer_iff.mp hg.1)
      (by rw [hq1]; exact hfix _ hxl)
      (by rw [hq8]; exact MulAction.mem_stabilizer_iff.mp hg.2)
  obtain ⟨t, ht, w, hw, htw⟩ := P.nontriv T.poly hq
  exact burnsideF45_eq_one_of_card_two (T.point_card_stabPath hq) ht hgq htw (hfix w hw)

theorem point_dihedral {v : c.Γ} (hv : c.graph.dist c.xv v = 8) :
    Nonempty (↥(stv c c.xv ⊓ stv c v) ≃* DihedralGroup 5) := by
  obtain ⟨lab, A⟩ := T.aff
  have hcard : Nat.card ↥(stv c c.xv ⊓ stv c v) = 10 := T.point_card hv
  let σ : c.G0 → ZMod 5 → ZMod 5 := fun g i => Function.invFun lab (g • lab i)
  have hadj : ∀ g ∈ stv c c.xv, ∀ i, c.graph.Adj c.xv (g • lab i) := fun g hg i => by
    have := (GraphAction.adj_smul g c.xv (lab i)).mpr (A.adj i)
    rwa [MulAction.mem_stabilizer_iff.mp hg] at this
  have hσlab : ∀ g ∈ stv c c.xv, ∀ i, lab (σ g i) = g • lab i := fun g hg i =>
    Function.invFun_eq (A.surj _ (hadj g hg i))
  have hσaff : ∀ g ∈ stv c c.xv, ∀ i, σ g i = (σ g 1 - σ g 0) * i + σ g 0 := by
    intro g hg i
    obtain ⟨e, b, -, hab⟩ := A.aff g (MulAction.mem_stabilizer_iff.mp hg)
    have h : ∀ j, σ g j = e * j + b := fun j => A.inj (by rw [hσlab g hg j, hab])
    rw [h i, h 1, h 0]
    ring
  have hσmul : ∀ g ∈ stv c c.xv, ∀ h ∈ stv c c.xv, ∀ i, σ (g * h) i = σ g (σ h i) := by
    intro g hg h hh i
    apply A.inj
    rw [hσlab _ (mul_mem hg hh), hσlab g hg, hσlab h hh, mul_smul]
  have hσpow : ∀ g ∈ stv c c.xv, ∀ (n : ℕ) i, σ (g ^ n) i = (σ g)^[n] i := by
    intro g hg n
    induction n with
    | zero =>
      intro i
      apply A.inj
      rw [pow_zero, hσlab _ (one_mem _), one_smul, Function.iterate_zero_apply]
    | succ n ih =>
      intro i
      rw [pow_succ', hσmul g hg _ (pow_mem hg n), ih, Function.iterate_succ_apply']
  let ε : c.G0 → ZMod 5 := fun g => σ g 1 - σ g 0
  let β : c.G0 → ZMod 5 := fun g => σ g 0
  have hsign : ∀ g : ↥(stv c c.xv ⊓ stv c v), ε g = 1 ∨ ε g = -1 := by
    intro g
    have hgx : (g : c.G0) ∈ stv c c.xv := g.2.1
    have h10 : (g : c.G0) ^ 10 = 1 := by
      have := pow_card_eq_one' (G := ↥(stv c c.xv ⊓ stv c v)) (x := g)
      rw [hcard] at this
      exact congrArg Subtype.val this
    have hfun : σ g = fun i => ε g * i + β g := funext (hσaff g hgx)
    have hit : ∀ i, (fun i => ε g * i + β g)^[10] i = i := by
      intro i
      rw [← hfun, ← hσpow g hgx 10 i, h10]
      apply A.inj
      rw [hσlab _ (one_mem _), one_smul]
    exact burnsideF45_aff_iter (ε g) (β g) (hit 0) (hit 1)
  let f : ↥(stv c c.xv ⊓ stv c v) → DihedralGroup 5 := fun g => burnsideF45_dih (ε g) (β g)
  have hf : ∀ g h : ↥(stv c c.xv ⊓ stv c v), f (g * h) = f g * f h := by
    intro g h
    have hgx : (g : c.G0) ∈ stv c c.xv := g.2.1
    have hhx : (h : c.G0) ∈ stv c c.xv := h.2.1
    have e1 : ε (g * h : ↥(stv c c.xv ⊓ stv c v)) = ε g * ε h := by
      show σ (g * h) 1 - σ (g * h) 0 = (σ g 1 - σ g 0) * (σ h 1 - σ h 0)
      rw [hσmul _ hgx _ hhx, hσmul _ hgx _ hhx, hσaff g hgx (σ h 1), hσaff g hgx (σ h 0)]
      ring
    have e2 : β (g * h : ↥(stv c c.xv ⊓ stv c v)) = ε g * β h + β g := by
      show σ (g * h) 0 = (σ g 1 - σ g 0) * σ h 0 + σ g 0
      rw [hσmul _ hgx _ hhx, hσaff g hgx (σ h 0)]
    show burnsideF45_dih (ε (g * h : ↥(stv c c.xv ⊓ stv c v)))
        (β (g * h : ↥(stv c c.xv ⊓ stv c v))) =
      burnsideF45_dih (ε g) (β g) * burnsideF45_dih (ε h) (β h)
    rw [e1, e2, burnsideF45_dih_mul _ _ _ _ (hsign g) (hsign h)]
  let ρ : ↥(stv c c.xv ⊓ stv c v) →* DihedralGroup 5 := MonoidHom.mk' f hf
  have hinj : Function.Injective ρ := by
    intro g h hgh
    have hgx : (g : c.G0) ∈ stv c c.xv := g.2.1
    have hhx : (h : c.G0) ∈ stv c c.xv := h.2.1
    obtain ⟨he, hb⟩ := burnsideF45_dih_inj _ _ _ _ (hsign g) (hsign h) hgh
    have hσ : ∀ i, σ g i = σ h i := by
      intro i
      rw [hσaff g hgx, hσaff h hhx]
      exact congrArg₂ (fun a b => a * i + b) he hb
    have hk : ((h : c.G0)⁻¹ * g) = 1 := by
      refine T.point_faithful hv (mul_mem (inv_mem h.2) g.2) fun w hw => ?_
      obtain ⟨i, rfl⟩ := A.surj w hw
      rw [mul_smul, ← hσlab g hgx, hσ i, hσlab h hhx, inv_smul_smul]
    exact Subtype.ext (inv_mul_eq_one.mp hk).symm
  have hbij : Function.Bijective ρ :=
    hinj.bijective_of_nat_card_le (by rw [DihedralGroup.nat_card, hcard])
  exact ⟨MulEquiv.ofBijective ρ hbij⟩

theorem nine_line (hQ : ∀ w, c.graph.Adj c.lv w → ∀ q ∈ pCoreOf 2 (stv c c.lv), q • w = w)
    {u v : c.Γ} (huv : c.graph.dist u v = 8) (hu : CosetGeom.vtype u = true) :
    IsComplementIn (stv c u ⊓ stv c v) (pCoreOf 2 (stv c u)) (stv c u) := by
  obtain ⟨g, hg⟩ := exists_smul_eq_baseVert c u
  have hgl : g • c.lv = u := by
    rw [← hg, hu]
    rfl
  have hvl : c.graph.dist c.lv (g⁻¹ • v) = 8 := by
    have h1 : c.graph.dist (g • c.lv) (g • (g⁻¹ • v)) = c.graph.dist c.lv (g⁻¹ • v) :=
      CosetGeom.dist_smul g _ _
    rw [hgl, smul_inv_smul] at h1
    rw [← h1]
    exact huv
  have h3 := (IsComplementIn.conjSub_iff g).mpr (T.line_compl hvl hQ)
  rw [conjSub_inf, ← pCoreOf_conjSub, ← stv_smul, ← stv_smul, smul_inv_smul, hgl] at h3
  exact h3

theorem nine_point {u v : c.Γ} (huv : c.graph.dist u v = 8) (hu : CosetGeom.vtype u = false) :
    Nonempty (↥(stv c u ⊓ stv c v) ≃* DihedralGroup 5) := by
  obtain ⟨g, hg⟩ := exists_smul_eq_baseVert c u
  have hgx : g • c.xv = u := by
    rw [← hg, hu]
    rfl
  have hvx : c.graph.dist c.xv (g⁻¹ • v) = 8 := by
    have h1 : c.graph.dist (g • c.xv) (g • (g⁻¹ • v)) = c.graph.dist c.xv (g⁻¹ • v) :=
      CosetGeom.dist_smul g _ _
    rw [hgx, smul_inv_smul] at h1
    rw [← h1]
    exact huv
  obtain ⟨φ⟩ := T.point_dihedral hvx
  have heqH : stv c u ⊓ stv c v = conjSub g (stv c c.xv ⊓ stv c (g⁻¹ • v)) := by
    rw [conjSub_inf, ← stv_smul, ← stv_smul, smul_inv_smul, hgx]
  rw [heqH]
  exact ⟨(MulEquiv.subgroupMap (MulAut.conj g) _).symm.trans φ⟩

end burnsideF45_TitsData

end CFSG.ASVolI
