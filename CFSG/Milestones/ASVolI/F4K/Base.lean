module

import all CFSG.Milestones.ASVolI.F4
public import CFSG.Quasithin.Recognition.F4Fifteen
public import CFSG.Milestones.ASVolI.F4

public section

namespace CFSG.ASVolI

open CFSG.Open

section Polygon

open CFSG.Quasithin

universe u

variable {V : Type u} {Γ : SimpleGraph V}

theorem burnsideF4k_polygon_two_nbrs {M : ℕ} (hM3 : 3 ≤ M) {S : Set V}
    (φ : SimpleGraph.cycleGraph M ≃g Γ.induce S) {x a b w : V}
    (hx : x ∈ S) (ha : a ∈ S) (hb : b ∈ S) (hw : w ∈ S)
    (hxa : Γ.Adj x a) (hxb : Γ.Adj x b) (hxw : Γ.Adj x w) (hab : a ≠ b) : w = a ∨ w = b := by
  obtain ⟨n, rfl⟩ : ∃ n, M = n + 2 := ⟨M - 2, by omega⟩
  obtain ⟨i, hi⟩ := φ.surjective ⟨x, hx⟩
  obtain ⟨ia, hia⟩ := φ.surjective ⟨a, ha⟩
  obtain ⟨ib, hib⟩ := φ.surjective ⟨b, hb⟩
  obtain ⟨iw, hiw⟩ := φ.surjective ⟨w, hw⟩
  have key : ∀ {j : Fin (n + 2)} {y : V} (hy : y ∈ S), φ j = ⟨y, hy⟩ → Γ.Adj x y →
      j = i - 1 ∨ j = i + 1 := by
    intro j y hy hj hxy
    have h1 : (Γ.induce S).Adj (φ i) (φ j) := by
      rw [hi, hj]
      exact hxy
    have h2 : (SimpleGraph.cycleGraph (n + 2)).Adj i j := by
      rw [← φ.map_rel_iff]
      exact h1
    have h3 : j ∈ (SimpleGraph.cycleGraph (n + 2)).neighborSet i := h2
    rw [SimpleGraph.cycleGraph_neighborSet] at h3
    simpa using h3
  have ka := key ha hia hxa
  have kb := key hb hib hxb
  have kw := key hw hiw hxw
  have hne : ia ≠ ib := by
    intro h
    apply hab
    have := congrArg Subtype.val (hia.symm.trans (h ▸ hib))
    exact this
  have hres : iw = ia ∨ iw = ib := by
    rcases ka with ka | ka <;> rcases kb with kb | kb <;> rcases kw with kw | kw <;>
      first | exact absurd (ka.trans kb.symm) hne | simp_all
  rcases hres with h | h
  · left
    have := congrArg Subtype.val (hiw.symm.trans (h ▸ hia))
    exact this
  · right
    have := congrArg Subtype.val (hiw.symm.trans (h ▸ hib))
    exact this

theorem burnsideF4k_polygon_start {M : ℕ} (hM : 0 < M) (hM3 : 3 ≤ M) {S : Set V}
    (φ : SimpleGraph.cycleGraph M ≃g Γ.induce S) {x l : V} (hx : x ∈ S) (hl : l ∈ S)
    (hxl : Γ.Adj x l) : ∃ i₀ : ℕ,
    (GPath.polyWalk hM φ i₀ 0 = x ∧ GPath.polyWalk hM φ i₀ 1 = l) ∨
    (GPath.polyWalk hM φ i₀ 0 = l ∧ GPath.polyWalk hM φ i₀ 1 = x) := by
  obtain ⟨i, hi⟩ := φ.surjective ⟨x, hx⟩
  obtain ⟨j, hj⟩ := φ.surjective ⟨l, hl⟩
  have h1 : (Γ.induce S).Adj (φ i) (φ j) := by
    rw [hi, hj]
    exact hxl
  have h2 : (SimpleGraph.cycleGraph M).Adj i j := by
    rw [← φ.map_rel_iff]
    exact h1
  have hiv := i.2
  have hjv := j.2
  have hstep : ∀ k : Fin M, GPath.polyWalk hM φ k.val 1 =
      (φ ⟨(k.val + 1) % M, Nat.mod_lt _ hM⟩ : ↥S) := by
    intro k
    unfold GPath.polyWalk
    rfl
  rw [cycleGraph_adj_iff hM3] at h2
  rcases h2 with h | h | ⟨h3, h4⟩ | ⟨h3, h4⟩
  · refine ⟨i.val, Or.inl ⟨?_, ?_⟩⟩
    · rw [GPath.polyWalk_zero, hi]
    · rw [hstep]
      have : (⟨(i.val + 1) % M, Nat.mod_lt _ hM⟩ : Fin M) = j :=
        Fin.ext (by
          show (i.val + 1) % M = j.val
          rw [Nat.mod_eq_of_lt (by omega)]; omega)
      rw [this, hj]
  · refine ⟨j.val, Or.inr ⟨?_, ?_⟩⟩
    · rw [GPath.polyWalk_zero, hj]
    · rw [hstep]
      have : (⟨(j.val + 1) % M, Nat.mod_lt _ hM⟩ : Fin M) = i :=
        Fin.ext (by
          show (j.val + 1) % M = i.val
          rw [Nat.mod_eq_of_lt (by omega)]; omega)
      rw [this, hi]
  · refine ⟨j.val, Or.inr ⟨?_, ?_⟩⟩
    · rw [GPath.polyWalk_zero, hj]
    · rw [hstep]
      have : (⟨(j.val + 1) % M, Nat.mod_lt _ hM⟩ : Fin M) = i :=
        Fin.ext (by
          show (j.val + 1) % M = i.val
          have : j.val + 1 = M := by omega
          rw [this, Nat.mod_self]; omega)
      rw [this, hi]
  · refine ⟨i.val, Or.inl ⟨?_, ?_⟩⟩
    · rw [GPath.polyWalk_zero, hi]
    · rw [hstep]
      have : (⟨(i.val + 1) % M, Nat.mod_lt _ hM⟩ : Fin M) = j :=
        Fin.ext (by
          show (i.val + 1) % M = j.val
          have : i.val + 1 = M := by omega
          rw [this, Nat.mod_self]; omega)
      rw [this, hj]

theorem burnsideF4k_polygon_fix {M : ℕ} (hM : 0 < M) (hM3 : 3 ≤ M) {S : Set V}
    (φ : SimpleGraph.cycleGraph M ≃g Γ.induce S) {H : Type*} [Group H] [MulAction H V]
    [GraphAction H Γ] (g : H) (hgS : ∀ v ∈ S, g • v ∈ S) (i₀ : ℕ)
    (h0 : g • GPath.polyWalk hM φ i₀ 0 = GPath.polyWalk hM φ i₀ 0)
    (h1 : g • GPath.polyWalk hM φ i₀ 1 = GPath.polyWalk hM φ i₀ 1) :
    ∀ v ∈ S, g • v = v := by
  have hadj := GPath.polyWalk_adj hM φ i₀ hM3
  have hnb := GPath.polyWalk_nb hM φ i₀ hM3
  have hmem := GPath.polyWalk_mem hM φ i₀
  have claim : ∀ k : ℕ, g • GPath.polyWalk hM φ i₀ k = GPath.polyWalk hM φ i₀ k ∧
      g • GPath.polyWalk hM φ i₀ (k + 1) = GPath.polyWalk hM φ i₀ (k + 1) := by
    intro k
    induction k with
    | zero => exact ⟨h0, h1⟩
    | succ k ih =>
      obtain ⟨hk0, hk1⟩ := ih
      refine ⟨hk1, ?_⟩
      set z := GPath.polyWalk hM φ i₀ with hz
      have hadj' : Γ.Adj (z (k + 1)) (g • z (k + 1 + 1)) := by
        have := (GraphAction.adj_smul g (z (k + 1)) (z (k + 1 + 1))).mpr (hadj (k + 1))
        rwa [hk1] at this
      have hw := burnsideF4k_polygon_two_nbrs hM3 φ (hmem (k + 1)) (hmem k) (hmem (k + 2))
        (hgS _ (hmem (k + 1 + 1))) (hadj k).symm (hadj (k + 1)) hadj' (hnb k)
      rcases hw with h | h
      · exfalso
        apply hnb k
        have h' : g • z (k + 2) = g • z k := by rw [hk0]; exact h
        exact ((MulAction.injective g h').symm)
      · exact h
  intro v hv
  obtain ⟨k, -, hk⟩ := GPath.polyWalk_surj hM φ i₀ v hv
  rw [← hk]
  exact (claim k).1

theorem burnsideF4k_polygon_fix_adj {M : ℕ} (hM3 : 3 ≤ M) {S : Set V}
    (φ : SimpleGraph.cycleGraph M ≃g Γ.induce S) {H : Type*} [Group H] [MulAction H V]
    [GraphAction H Γ] (g : H) (hgS : ∀ v ∈ S, g • v ∈ S) {x l : V} (hx : x ∈ S) (hl : l ∈ S)
    (hxl : Γ.Adj x l) (hgx : g • x = x) (hgl : g • l = l) : ∀ v ∈ S, g • v = v := by
  have hM : 0 < M := by omega
  obtain ⟨i₀, h | h⟩ := burnsideF4k_polygon_start hM hM3 φ hx hl hxl
  · exact burnsideF4k_polygon_fix hM hM3 φ g hgS i₀ (by rw [h.1]; exact hgx)
      (by rw [h.2]; exact hgl)
  · exact burnsideF4k_polygon_fix hM hM3 φ g hgS i₀ (by rw [h.1]; exact hgl)
      (by rw [h.2]; exact hgx)

theorem burnsideF4k_polygon_ncard {M : ℕ} {S : Set V}
    (φ : SimpleGraph.cycleGraph M ≃g Γ.induce S) : S.ncard = M := by
  rw [← Nat.card_coe_set_eq]
  have := Nat.card_congr φ.toEquiv
  rw [← this]
  simp

end Polygon

section Completion

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
  CFSG.ASVolI.ChF
open scoped Pointwise

variable {α : RankTwoAmalgam.{0}} {Z : Type} [Group Z] (c : α.Completion Z)

theorem burnsideF4k_setStab_mem {S : Set c.Γ} {g : c.G0} (hg : g ∈ setStab c S) {v : c.Γ}
    (hv : v ∈ S) : g • v ∈ S := by
  have h : g • S = S := MulAction.mem_stabilizer_iff.mp hg
  have : g • v ∈ g • S := Set.smul_mem_smul_set hv
  rwa [h] at this

theorem burnsideF4k_mem_pointwiseStab {S : Set c.Γ} {g : c.G0} :
    g ∈ pointwiseStab c S ↔ ∀ v ∈ S, g • v = v := by
  unfold pointwiseStab
  simp only [Subgroup.mem_iInf]
  exact forall₂_congr fun v _ => MulAction.mem_stabilizer_iff

theorem burnsideF4k_pointwiseStab_le_setStab (S : Set c.Γ) : pointwiseStab c S ≤ setStab c S := by
  intro g hg
  have h := (burnsideF4k_mem_pointwiseStab c).mp hg
  show g ∈ MulAction.stabilizer c.G0 S
  rw [MulAction.mem_stabilizer_iff]
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    show g • w ∈ S
    rw [h w hw]
    exact hw
  · intro hv
    exact ⟨v, hv, h v hv⟩

def burnsideF4k_WeakRefl (s : c.G0) (S : Set c.Γ) (u : c.Γ) : Prop :=
  s ∈ setStab c S ∧ s • u = u ∧ Set.ncard {w : c.Γ | w ∈ S ∧ s • w = w} = 2

theorem burnsideF4k_weakRefl_of_isReflectionOn {s : c.G0} {S : Set c.Γ} {u : c.Γ}
    (h : IsReflectionOn c s S u) : burnsideF4k_WeakRefl c s S u := ⟨h.2.1, h.2.2.1, h.2.2.2⟩

theorem burnsideF4k_reflection_moves {m : ℕ} (hm : 2 ≤ m) {S : Set c.Γ} (hS : c.IsApartment m S)
    {s : c.G0} {u l : c.Γ} (hs : burnsideF4k_WeakRefl c s S u) (hu : u ∈ S) (hl : l ∈ S)
    (hul : c.graph.Adj u l) (hsu : s • u = u) : s • l ≠ l := by
  intro hsl
  obtain ⟨φ⟩ := hS
  have hall := burnsideF4k_polygon_fix_adj (by omega : 3 ≤ 2 * m) φ s
    (fun v hv => burnsideF4k_setStab_mem c hs.1 hv) hu hl hul hsu hsl
  have hset : {w : c.Γ | w ∈ S ∧ s • w = w} = S := by
    ext w
    exact ⟨fun h => h.1, fun h => ⟨h, hall w h⟩⟩
  have h2 := hs.2.2
  rw [hset, burnsideF4k_polygon_ncard φ] at h2
  omega

theorem burnsideF4k_F416_two_weak {m : ℕ} (hm : 2 ≤ m) {S : Set c.Γ} (hS : c.IsApartment m S)
    (hx : c.xv ∈ S) (hl : c.lv ∈ S) {sx sl : c.G0} (hrx : burnsideF4k_WeakRefl c sx S c.xv)
    (hrl : burnsideF4k_WeakRefl c sl S c.lv)
    (htrans : ∀ u ∈ S, ∀ v ∈ S, CosetGeom.vtype u = CosetGeom.vtype v →
      ∃ w ∈ Subgroup.closure {sx, sl}, w • u = v) :
    setStab c S = (setStab c S ⊓ pointwiseStab c S) ⊔ Subgroup.closure {sx, sl} := by
  have hWle : Subgroup.closure {sx, sl} ≤ setStab c S := by
    rw [Subgroup.closure_le]
    intro s hs'
    rcases hs' with rfl | rfl
    · exact hrx.1
    · exact hrl.1
  have hxl : c.graph.Adj c.xv c.lv := CosetGeom.adj_γ₀_γ₁
  have hsxx : sx • c.xv = c.xv := hrx.2.1
  have hmove := burnsideF4k_reflection_moves c hm hS hrx hx hl hxl hsxx
  obtain ⟨φ⟩ := hS
  apply le_antisymm
  · intro n hn
    set u := n • c.xv with hu
    have huS : u ∈ S := burnsideF4k_setStab_mem c hn hx
    have htype : CosetGeom.vtype c.xv = CosetGeom.vtype u := by
      rw [hu, CosetGeom.vtype_smul]
    obtain ⟨w₁, hw₁, hw₁x⟩ := htrans c.xv hx u huS htype
    have hw₁S : w₁ ∈ setStab c S := hWle hw₁
    set n' := w₁⁻¹ * n with hn'
    have hn'S : n' ∈ setStab c S := (setStab c S).mul_mem ((setStab c S).inv_mem hw₁S) hn
    have hn'x : n' • c.xv = c.xv := by
      rw [hn', mul_smul, ← hu, ← hw₁x, inv_smul_smul]
    have hn'l : n' • c.lv ∈ S := burnsideF4k_setStab_mem c hn'S hl
    have hadj : c.graph.Adj c.xv (n' • c.lv) := by
      have := (GraphAction.adj_smul n' c.xv c.lv).mpr hxl
      rwa [hn'x] at this
    set c₀ := sx • c.lv with hc₀
    have hc₀S : c₀ ∈ S := burnsideF4k_setStab_mem c hrx.1 hl
    have hc₀adj : c.graph.Adj c.xv c₀ := by
      have := (GraphAction.adj_smul sx c.xv c.lv).mpr hxl
      rwa [hsxx] at this
    have hcases := burnsideF4k_polygon_two_nbrs (by omega : 3 ≤ 2 * m) φ hx hl hc₀S hn'l hxl
      hc₀adj hadj (Ne.symm hmove)
    have hmem : n ∈ (setStab c S ⊓ pointwiseStab c S) ⊔ Subgroup.closure {sx, sl} := by
      have hn_eq : n = w₁ * n' := by rw [hn']; group
      have hw₁mem : w₁ ∈ (setStab c S ⊓ pointwiseStab c S) ⊔ Subgroup.closure {sx, sl} :=
        Subgroup.mem_sup_right hw₁
      have hsxmem : sx ∈ Subgroup.closure {sx, sl} := Subgroup.subset_closure (by simp)
      rcases hcases with h | h
      · have hn'K : n' ∈ pointwiseStab c S :=
          (burnsideF4k_mem_pointwiseStab c).mpr
            (burnsideF4k_polygon_fix_adj (by omega : 3 ≤ 2 * m) φ n'
              (fun v hv => burnsideF4k_setStab_mem c hn'S hv) hx hl hxl hn'x h)
        rw [hn_eq]
        exact Subgroup.mul_mem _ hw₁mem (Subgroup.mem_sup_left ⟨hn'S, hn'K⟩)
      · have hk : sx⁻¹ * n' ∈ pointwiseStab c S := by
          refine (burnsideF4k_mem_pointwiseStab c).mpr ?_
          have hkS : sx⁻¹ * n' ∈ setStab c S :=
            (setStab c S).mul_mem ((setStab c S).inv_mem hrx.1) hn'S
          refine burnsideF4k_polygon_fix_adj (by omega : 3 ≤ 2 * m) φ (sx⁻¹ * n')
            (fun v hv => burnsideF4k_setStab_mem c hkS hv) hx hl hxl ?_ ?_
          · rw [mul_smul, hn'x]
            exact inv_smul_eq_iff.mpr hsxx.symm
          · rw [mul_smul, h, hc₀]
            exact inv_smul_smul sx _
        have hkS : sx⁻¹ * n' ∈ setStab c S :=
          (setStab c S).mul_mem ((setStab c S).inv_mem hrx.1) hn'S
        have hn'eq : n' = sx * (sx⁻¹ * n') := by group
        rw [hn_eq, hn'eq]
        exact Subgroup.mul_mem _ hw₁mem
          (Subgroup.mul_mem _ (Subgroup.mem_sup_right hsxmem)
            (Subgroup.mem_sup_left ⟨hkS, hk⟩))
    exact hmem
  · exact sup_le inf_le_left hWle

theorem burnsideF4k_F416_two {m : ℕ} (hm : 2 ≤ m) {S : Set c.Γ} (hS : c.IsApartment m S)
    (hx : c.xv ∈ S) (hl : c.lv ∈ S) {sx sl : c.G0} (hW : IsF415W c m S sx sl) :
    setStab c S = (setStab c S ⊓ pointwiseStab c S) ⊔ Subgroup.closure {sx, sl} := by
  obtain ⟨-, -, hrx, hrl, -, htrans⟩ := hW
  exact burnsideF4k_F416_two_weak c hm hS hx hl (burnsideF4k_weakRefl_of_isReflectionOn c hrx)
    (burnsideF4k_weakRefl_of_isReflectionOn c hrl) htrans

end Completion

section Parabolics

open CFSG.ASVolI.ChF

theorem burnsideF4k_parabolics (hcompat : NativeChartCompatibilityGoal) {κ : GLKind} {p f : ℕ}
    {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E} (hyp : HypF_4_4 κ p f Gp M₁ M₂) :
    IsLieParabolics p Gp (Gp ⊓ (M₁ ⊓ M₂)) (Gp ⊓ M₁) (Gp ⊓ M₂) := by
  obtain ⟨h1, h2, h3⟩ := hyp.toHypF_4_4g.chart_matches
  have hlp := (hcompat κ p f E Gp hyp.toHypF_4_4g.chart).1
  rw [← h1, ← h2, ← h3] at hlp
  exact hlp

end Parabolics

section ConjIso

@[expose] def burnsideF4k_conjIso {G G' : Type*} [Group G] [Group G'] {A : Subgroup G}
    {A' : Subgroup G'} (θ : ↥A ≃* ↥A') (g : G) (g' : G') {B : Subgroup G} {B' : Subgroup G'}
    (hB : ∀ x, x ∈ B ↔ g⁻¹ * x * g ∈ A) (hB' : ∀ y, y ∈ B' ↔ g'⁻¹ * y * g' ∈ A') :
    ↥B ≃* ↥B' where
  toFun x := ⟨g' * ((θ ⟨g⁻¹ * (x : G) * g, (hB _).mp x.2⟩ : ↥A') : G') * g'⁻¹, by
    rw [hB']
    have : g'⁻¹ * (g' * ((θ ⟨g⁻¹ * (x : G) * g, (hB _).mp x.2⟩ : ↥A') : G') * g'⁻¹) * g' =
        ((θ ⟨g⁻¹ * (x : G) * g, (hB _).mp x.2⟩ : ↥A') : G') := by group
    rw [this]
    exact (θ _).2⟩
  invFun y := ⟨g * ((θ.symm ⟨g'⁻¹ * (y : G') * g', (hB' _).mp y.2⟩ : ↥A) : G) * g⁻¹, by
    rw [hB]
    have : g⁻¹ * (g * ((θ.symm ⟨g'⁻¹ * (y : G') * g', (hB' _).mp y.2⟩ : ↥A) : G) * g⁻¹) * g =
        ((θ.symm ⟨g'⁻¹ * (y : G') * g', (hB' _).mp y.2⟩ : ↥A) : G) := by group
    rw [this]
    exact (θ.symm _).2⟩
  left_inv x := by
    apply Subtype.ext
    show g * ((θ.symm ⟨g'⁻¹ * (g' * ((θ ⟨g⁻¹ * (x : G) * g, (hB _).mp x.2⟩ : ↥A') : G') * g'⁻¹) *
      g', _⟩ : ↥A) : G) * g⁻¹ = x
    have h1 : (⟨g'⁻¹ * (g' * ((θ ⟨g⁻¹ * (x : G) * g, (hB _).mp x.2⟩ : ↥A') : G') * g'⁻¹) * g',
        by
          have e : g'⁻¹ * (g' * ((θ ⟨g⁻¹ * (x : G) * g, (hB _).mp x.2⟩ : ↥A') : G') * g'⁻¹) * g' =
            ((θ ⟨g⁻¹ * (x : G) * g, (hB _).mp x.2⟩ : ↥A') : G') := by group
          rw [e]
          exact (θ _).2⟩ : ↥A') =
        θ ⟨g⁻¹ * (x : G) * g, (hB _).mp x.2⟩ := Subtype.ext (by group)
    simp only [h1, MulEquiv.symm_apply_apply]
    group
  right_inv y := by
    apply Subtype.ext
    show g' * ((θ ⟨g⁻¹ * (g * ((θ.symm ⟨g'⁻¹ * (y : G') * g', (hB' _).mp y.2⟩ : ↥A) : G) * g⁻¹) *
      g, _⟩ : ↥A') : G') * g'⁻¹ = y
    have h1 : (⟨g⁻¹ * (g * ((θ.symm ⟨g'⁻¹ * (y : G') * g', (hB' _).mp y.2⟩ : ↥A) : G) * g⁻¹) * g,
        by
          have e : g⁻¹ * (g * ((θ.symm ⟨g'⁻¹ * (y : G') * g', (hB' _).mp y.2⟩ : ↥A) : G) * g⁻¹) * g =
            ((θ.symm ⟨g'⁻¹ * (y : G') * g', (hB' _).mp y.2⟩ : ↥A) : G) := by group
          rw [e]
          exact (θ.symm _).2⟩ : ↥A) =
        θ.symm ⟨g'⁻¹ * (y : G') * g', (hB' _).mp y.2⟩ := Subtype.ext (by group)
    simp only [h1, MulEquiv.apply_symm_apply]
    group
  map_mul' x y := by
    apply Subtype.ext
    show g' * ((θ ⟨g⁻¹ * ((x : G) * (y : G)) * g, _⟩ : ↥A') : G') * g'⁻¹ =
      g' * ((θ ⟨g⁻¹ * (x : G) * g, _⟩ : ↥A') : G') * g'⁻¹ *
        (g' * ((θ ⟨g⁻¹ * (y : G) * g, _⟩ : ↥A') : G') * g'⁻¹)
    have h1 : (⟨g⁻¹ * ((x : G) * (y : G)) * g, by
        have e : g⁻¹ * ((x : G) * (y : G)) * g = (g⁻¹ * (x : G) * g) * (g⁻¹ * (y : G) * g) := by
          group
        rw [e]
        exact A.mul_mem ((hB _).mp x.2) ((hB _).mp y.2)⟩ : ↥A) =
        (⟨g⁻¹ * (x : G) * g, (hB _).mp x.2⟩ : ↥A) * ⟨g⁻¹ * (y : G) * g, (hB _).mp y.2⟩ :=
      Subtype.ext (by simp only [Subgroup.coe_mul]; group)
    simp only [h1, map_mul, Subgroup.coe_mul]
    group

end ConjIso

section F421

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
  CFSG.ASVolI.ChF

variable {α : RankTwoAmalgam.{0}}

theorem burnsideF4k_f1_smul_lv_iff {Z : Type} [Group Z] {c : α.Completion Z} (hc : c.IsFaithful)
    (a : α.G1) : f1 (c := c) a • c.lv = c.lv ↔ a ∈ α.α1.range := by
  constructor
  · intro h
    have h1 := CosetGeom.mem_stab_of_smul_eq h
    rw [CosetGeom.stab_γ₁ (G₀ := c.φ1.range ⊔ c.φ2.range) le_sup_right] at h1
    have h2 : c.φ1 a ∈ c.φ1.range ⊓ c.φ2.range := ⟨⟨a, rfl⟩, h1⟩
    rw [c.inter] at h2
    obtain ⟨g, hg⟩ := h2
    refine ⟨g, hc.1 ?_⟩
    rw [c.comm1]
    exact hg
  · rintro ⟨g, rfl⟩
    apply CosetGeom.smul_eq_of_mem_stab
    rw [CosetGeom.stab_γ₁ (G₀ := c.φ1.range ⊔ c.φ2.range) le_sup_right]
    show c.φ1 (α.α1 g) ∈ c.φ2.range
    rw [c.comm1]
    have : c.φ12 g ∈ c.φ1.range ⊓ c.φ2.range := by
      rw [c.inter]
      exact ⟨g, rfl⟩
    exact this.2

end F421

section F416Core

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
  CFSG.ASVolI.ChF

theorem burnsideF4k_fix_tail {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y] {c : α.Completion Y}
    {m : ℕ} (F : c.Facts46 m) {p : GPath c.graph m} (hp : p.IsGeodesic) {g : c.G0}
    (h1 : g • p 1 = p 1) (hm' : g • p m = p m) : ∀ i, 1 ≤ i → i ≤ m → g • p i = p i := by
  have hm := F.hm
  have hnb : p.NoBack := GPath.noBack_of_dist_eq (connected_graph c) p hp
  let t : GPath c.graph (m - 1) := p.drop 1 (by omega)
  have ht0 : t ∈ GPath.nbPaths c.graph (p 1) (m - 1) :=
    ⟨by show p (1 + min 0 (m - 1)) = p 1; simp, hnb.drop 1 (by omega)⟩
  have htm : t (m - 1) = p m := by
    rw [GPath.drop_apply _ _ _ le_rfl]; congr 1; omega
  have hgt : g • t ∈ GPath.nbPaths c.graph (p 1) (m - 1) :=
    ⟨by show g • t 0 = p 1; rw [ht0.1, h1], GPath.smul_noBack ht0.2⟩
  have hgeo : (g • t).IsGeodesic := by
    show c.graph.dist ((g • t) 0) ((g • t) (m - 1)) = m - 1
    rw [hgt.1]
    exact (F.uniq (m - 1) (by omega) (p 1) (g • t) hgt).1
  have heq := (F.uniq (m - 1) (by omega) (p 1) t ht0).2 (g • t) hgt.1
    (by show g • t (m - 1) = t (m - 1); rw [htm, hm']) hgeo
  intro i hi1 hi2
  have := congrArg (fun r : GPath c.graph (m - 1) => r (i - 1)) heq
  simp only [GPath.smul_apply] at this
  have e : t (i - 1) = p i := by
    rw [GPath.drop_apply _ _ _ (by omega)]; congr 1; omega
  rwa [e] at this

end F416Core

section F416Core2

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
  CFSG.ASVolI.ChF

theorem burnsideF4k_F416_core {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y] {c : α.Completion Y}
    {m : ℕ} (F : c.Facts46 m) {S : Set c.Γ} (hS : c.IsApartment m S)
    (hx : c.xv ∈ S) (hl : c.lv ∈ S) {Qx Sg : Subgroup c.G0}
    (hcompl : ∀ b ∈ S, c.graph.dist c.xv b = m →
      IsComplementIn (stv c c.xv ⊓ stv c b) Qx (stv c c.xv))
    (htrans : ∀ b b' : c.Γ, c.graph.dist c.xv b = m → c.graph.dist c.xv b' = m →
      ∃ g : c.G0, g • c.xv = c.xv ∧ g • b = b')
    (hQS : Qx ≤ Sg) (hSg : Sg ≤ stv c c.xv ⊓ stv c c.lv)
    (hQfix : ∀ w, c.graph.Adj c.xv w → ∀ q ∈ Qx, q • w = w)
    (hSgtrans : ∀ w₁ w₂, c.graph.Adj c.xv w₁ → c.graph.Adj c.xv w₂ → w₁ ≠ c.lv → w₂ ≠ c.lv →
      ∃ s ∈ Sg, s • w₁ = w₂)
    (hSgstab : ∀ w, c.graph.Adj c.xv w → w ≠ c.lv → ∀ s ∈ Sg, s • w = w → s ∈ Qx) :
    IsComplementIn (setStab c S ⊓ pointwiseStab c S) Sg (stv c c.xv ⊓ stv c c.lv) := by
  classical
  have hm := F.hm
  have hΓ := connected_graph c
  have hU := F.uniqueGeod
  have hc' : ∀ a b : c.Γ, c.graph.Adj a b → CosetGeom.vtype a ≠ CosetGeom.vtype b :=
    fun a b h => CosetGeom.vtype_ne_of_adj h
  obtain ⟨⟨b, hbS, hbd⟩, -⟩ := GPath.exists_opposite_of_polygon hΓ hc' hU hm hS hx
  obtain ⟨p, q, hp, hq, hp0, hq0, hpm, hqm, hpq, hSeq⟩ :=
    GPath.exists_arcs_of_polygon hΓ hm hS hx hbS hbd
  have h0 : p 0 = q 0 := hp0.trans hq0.symm
  have hmm : p m = q m := hpm.trans hqm.symm
  have hSv : S = p.verts ∪ q.verts := by
    rw [hSeq]
    exact GPath.range_cycSeq (by omega) h0 hmm
  have hxl : c.graph.Adj c.xv c.lv := CosetGeom.adj_γ₀_γ₁
  have hlr : c.lv = p 1 ∨ c.lv = q 1 :=
    GPath.cycSeq_adj_start hΓ hc' hU hm hp hq h0 hmm hpq (w := c.lv)
      (by rw [← hSeq]; exact hl) (by rw [hp0]; exact hxl)
  have key : ∀ p q : GPath c.graph m, p.IsGeodesic → q.IsGeodesic → p 0 = c.xv → q 0 = c.xv →
      p m = b → q m = b → p ≠ q → S = p.verts ∪ q.verts → c.lv = p 1 →
      IsComplementIn (setStab c S ⊓ pointwiseStab c S) Sg (stv c c.xv ⊓ stv c c.lv) := by
    intro p q hp hq hp0 hq0 hpm hqm hpq hSv hlp
    have h0 : p 0 = q 0 := hp0.trans hq0.symm
    have hmm : p m = q m := hpm.trans hqm.symm
    obtain ⟨h1ne, -⟩ := GPath.geod_first_last_ne hΓ hU (by omega) hp hq h0 hmm hpq
    set c₀ : c.Γ := q 1 with hc₀
    have hc₀adj : c.graph.Adj c.xv c₀ := by
      have := q.adj 0 (by omega)
      rwa [hq0] at this
    have hc₀ne : c₀ ≠ c.lv := by
      intro h
      apply h1ne
      rw [← hlp]
      exact h.symm
    have hc₀S : c₀ ∈ S := by
      rw [hSv]
      exact Or.inr (GPath.mem_verts (by omega))
    have kfix : ∀ g : c.G0, g • c.xv = c.xv → g • c.lv = c.lv → g • c₀ = c₀ → g • b = b →
        g ∈ pointwiseStab c S := by
      intro g hgx hgl hgc hgb
      rw [burnsideF4k_mem_pointwiseStab]
      intro v hv
      rw [hSv] at hv
      rcases hv with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
      · rcases Nat.eq_zero_or_pos i with rfl | hipos
        · rw [hp0]; exact hgx
        · exact burnsideF4k_fix_tail F hp (by rw [← hlp]; exact hgl) (by rw [hpm]; exact hgb) i
            hipos hi
      · rcases Nat.eq_zero_or_pos i with rfl | hipos
        · rw [hq0]; exact hgx
        · exact burnsideF4k_fix_tail F hq hgc (by rw [hqm]; exact hgb) i hipos hi
    have hQcompl := hcompl b hbS hbd
    obtain ⟨hQle, hHle, hQH, hQdec⟩ := hQcompl
    have hQtrans : ∀ b' : c.Γ, c.graph.dist c.xv b' = m → ∃ q₀ ∈ Qx, q₀ • b = b' := by
      intro b' hb'd
      obtain ⟨g₀, hg₀x, hg₀b⟩ := htrans b b' hbd hb'd
      obtain ⟨q₀, hq₀, k₀, hk₀, hqk⟩ := hQdec g₀ (MulAction.mem_stabilizer_iff.mpr hg₀x)
      refine ⟨q₀, hq₀, ?_⟩
      have hk₀b : k₀ • b = b := MulAction.mem_stabilizer_iff.mp (Subgroup.mem_inf.mp hk₀).2
      rw [← hg₀b, ← hqk, mul_smul, hk₀b]
    refine ⟨hSg, ?_, ?_, ?_⟩
    · intro k hk
      have hk' := (burnsideF4k_mem_pointwiseStab c).mp (Subgroup.mem_inf.mp hk).2
      exact Subgroup.mem_inf.mpr
        ⟨MulAction.mem_stabilizer_iff.mpr (hk' _ hx), MulAction.mem_stabilizer_iff.mpr (hk' _ hl)⟩
    ·
      rw [eq_bot_iff]
      intro s hs
      obtain ⟨hsS, hsK⟩ := Subgroup.mem_inf.mp hs
      have hsK' := (burnsideF4k_mem_pointwiseStab c).mp (Subgroup.mem_inf.mp hsK).2
      have hsQ : s ∈ Qx := hSgstab c₀ hc₀adj hc₀ne s hsS (hsK' _ hc₀S)
      have hsH : s ∈ stv c c.xv ⊓ stv c b :=
        Subgroup.mem_inf.mpr ⟨MulAction.mem_stabilizer_iff.mpr (hsK' _ hx),
          MulAction.mem_stabilizer_iff.mpr (hsK' _ hbS)⟩
      have : s ∈ Qx ⊓ (stv c c.xv ⊓ stv c b) := ⟨hsQ, hsH⟩
      rw [hQH] at this
      exact this
    · intro g hg
      have hgx : g • c.xv = c.xv := MulAction.mem_stabilizer_iff.mp (Subgroup.mem_inf.mp hg).1
      have hgl : g • c.lv = c.lv := MulAction.mem_stabilizer_iff.mp (Subgroup.mem_inf.mp hg).2
      have hgc₀adj : c.graph.Adj c.xv (g • c₀) := by
        have := (GraphAction.adj_smul g c.xv c₀).mpr hc₀adj
        rwa [hgx] at this
      have hgc₀ne : g • c₀ ≠ c.lv := by
        intro h
        apply hc₀ne
        rw [← hgl] at h
        exact MulAction.injective g h
      obtain ⟨s₁, hs₁, hs₁c⟩ := hSgtrans c₀ (g • c₀) hc₀adj hgc₀adj hc₀ne hgc₀ne
      have hs₁x : s₁ • c.xv = c.xv :=
        MulAction.mem_stabilizer_iff.mp (Subgroup.mem_inf.mp (hSg hs₁)).1
      have hxx : (s₁⁻¹ * g) • c.xv = c.xv := by
        rw [mul_smul, hgx]
        exact inv_smul_eq_iff.mpr hs₁x.symm
      have hb'd : c.graph.dist c.xv ((s₁⁻¹ * g) • b) = m := by
        have h : c.graph.dist ((s₁⁻¹ * g) • c.xv) ((s₁⁻¹ * g) • b) = c.graph.dist c.xv b :=
          CosetGeom.dist_smul (s₁⁻¹ * g) c.xv b
        rw [hxx] at h
        rw [h]
        exact hbd
      obtain ⟨q₀, hq₀, hq₀b⟩ := hQtrans _ hb'd
      have hq₀S : q₀ ∈ Sg := hQS hq₀
      have hq₀c : q₀ • c₀ = c₀ := hQfix c₀ hc₀adj q₀ hq₀
      have hsS : s₁ * q₀ ∈ Sg := Sg.mul_mem hs₁ hq₀S
      obtain ⟨hsx, hsl⟩ := Subgroup.mem_inf.mp (hSg hsS)
      have hsx' : (s₁ * q₀) • c.xv = c.xv := MulAction.mem_stabilizer_iff.mp hsx
      have hsl' : (s₁ * q₀) • c.lv = c.lv := MulAction.mem_stabilizer_iff.mp hsl
      have hsc : (s₁ * q₀) • c₀ = g • c₀ := by rw [mul_smul, hq₀c, hs₁c]
      have hsb : (s₁ * q₀) • b = g • b := by
        rw [mul_smul, hq₀b, ← mul_smul, mul_inv_cancel_left]
      have hkK : (s₁ * q₀)⁻¹ * g ∈ pointwiseStab c S := by
        apply kfix
        · rw [mul_smul, hgx]
          exact inv_smul_eq_iff.mpr hsx'.symm
        · rw [mul_smul, hgl]
          exact inv_smul_eq_iff.mpr hsl'.symm
        · rw [mul_smul, ← hsc]
          exact inv_smul_smul _ _
        · rw [mul_smul, ← hsb]
          exact inv_smul_smul _ _
      refine ⟨s₁ * q₀, hsS, (s₁ * q₀)⁻¹ * g, ?_, mul_inv_cancel_left _ _⟩
      exact Subgroup.mem_inf.mpr ⟨burnsideF4k_pointwiseStab_le_setStab c S hkK, hkK⟩
  rcases hlr with h | h
  · exact key p q hp hq hp0 hq0 hpm hqm hpq hSv h
  · refine key q p hq hp hq0 hp0 hqm hpm hpq.symm ?_ h
    rw [hSv, Set.union_comm]

end F416Core2

section QGroups

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
  CFSG.Quasithin.F7 CFSG.ASVolI.ChF

theorem burnsideF4k_le_normalizer_pCoreOf {E : Type} [Group E] (p : ℕ) {Gp : Subgroup E}
    (hN : Gp.Normal) (M : Subgroup E) : M ≤ Subgroup.normalizer (pCoreOf p (Gp ⊓ M) : Set E) := by
  have hchar : (CFSG.pCore p ↥(Gp ⊓ M)).Characteristic :=
    CFSG.LieType.BorelTits.pCore_characteristic p
  have h1 := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
    (H := Gp ⊓ M) (CFSG.pCore p ↥(Gp ⊓ M))
  have h2 : M ≤ Subgroup.normalizer ((Gp ⊓ M : Subgroup E) : Set E) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hx1, hx2⟩
      exact ⟨hN.conj_mem x hx1 a, M.mul_mem (M.mul_mem ha hx2) (M.inv_mem ha)⟩
    · rintro ⟨hx1, hx2⟩
      refine ⟨?_, ?_⟩
      · have := hN.conj_mem _ hx1 a⁻¹
        simpa [mul_assoc] using this
      · have := M.mul_mem (M.mul_mem (M.inv_mem ha) hx2) ha
        simpa [mul_assoc] using this
  exact fun a ha => h1 (h2 ha)

theorem burnsideF4k_Qbar_normal {E : Type} [Group E] (p : ℕ) {Gp : Subgroup E}
    (hN : Gp.Normal) (M : Subgroup E) : ((pCoreOf p (Gp ⊓ M)).subgroupOf M).Normal := by
  have hle : pCoreOf p (Gp ⊓ M) ≤ M :=
    (CFSG.LieType.BorelTits.pCoreOf_le p (Gp ⊓ M)).trans inf_le_right
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr
    (burnsideF4k_le_normalizer_pCoreOf p hN M)

theorem burnsideF4k_pCoreOf_le_sylow {E : Type} [Group E] [Finite E] {p : ℕ} (hp : p.Prime)
    {H P S : Subgroup E} (hS : IsSylowOf p S H) (hSP : S ≤ P) (hPH : P ≤ H) :
    pCoreOf p P ≤ S := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hSH, hSp, hSidx⟩ := hS
  have h1 : IsPGroup p (S.subgroupOf P) := hSp.comap_subtype
  have hdvd : S.relIndex P ∣ S.relIndex H :=
    ⟨P.relIndex H, (Subgroup.relIndex_mul_relIndex S P H hSP hPH).symm⟩
  have h2 : ¬ p ∣ (S.subgroupOf P).index := fun h => hSidx (h.trans hdvd)
  let T : Sylow p ↥P := h1.toSylow h2
  have hcore : CFSG.pCore p ↥P ≤ (T : Subgroup ↥P) := by
    haveI : (CFSG.pCore p ↥P).Normal := CFSG.LieType.BorelTits.pCore_normal p
    exact (CFSG.LieType.BorelTits.pCore_isPGroup p).le_sylow_of_normal T
  have h3 : (T : Subgroup ↥P) = S.subgroupOf P := rfl
  rw [h3] at hcore
  have := Subgroup.map_mono (f := P.subtype) hcore
  rwa [Subgroup.map_subgroupOf_eq_of_le hSP] at this

theorem burnsideF4k_pCoreOf_le {E : Type} [Group E] [Finite E] {p : ℕ} (hp : p.Prime)
    {Gp M₁ M₂ : Subgroup E}
    (hP : IsLieParabolics p Gp (Gp ⊓ (M₁ ⊓ M₂)) (Gp ⊓ M₁) (Gp ⊓ M₂)) :
    pCoreOf p (Gp ⊓ M₁) ≤ M₂ ∧ pCoreOf p (Gp ⊓ M₂) ≤ M₁ := by
  obtain ⟨S, hS, hB⟩ := hP.1
  have hSB : S ≤ Gp ⊓ (M₁ ⊓ M₂) := by
    rw [hB]; exact le_inf hS.1 Subgroup.le_normalizer
  refine ⟨?_, ?_⟩
  · have hSP : S ≤ Gp ⊓ M₁ := hSB.trans (inf_le_inf_left _ inf_le_left)
    exact (burnsideF4k_pCoreOf_le_sylow hp hS hSP inf_le_left).trans
      (hSB.trans (inf_le_right.trans inf_le_right))
  · have hSP : S ≤ Gp ⊓ M₂ := hSB.trans (inf_le_inf_left _ inf_le_right)
    exact (burnsideF4k_pCoreOf_le_sylow hp hS hSP inf_le_left).trans
      (hSB.trans (inf_le_right.trans inf_le_left))

theorem burnsideF4k_Q_le_S {E : Type} [Group E] [Finite E] {p : ℕ} (hp : p.Prime)
    {Gp M₁ M₂ : Subgroup E} (hN : Gp.Normal)
    (hP : IsLieParabolics p Gp (Gp ⊓ (M₁ ⊓ M₂)) (Gp ⊓ M₁) (Gp ⊓ M₂)) :
    pCoreOf p (Gp ⊓ M₁) ≤ pCoreOf p (Gp ⊓ (M₁ ⊓ M₂)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h2 := (burnsideF4k_pCoreOf_le hp hP).1
  have h1 : pCoreOf p (Gp ⊓ M₁) ≤ Gp ⊓ M₁ := CFSG.LieType.BorelTits.pCoreOf_le p _
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer p ?_ ?_
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup p _)
  · exact le_inf (h1.trans inf_le_left) (le_inf (h1.trans inf_le_right) h2)
  · intro a ha
    exact burnsideF4k_le_normalizer_pCoreOf p hN M₁
      (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp ha).2).1

end QGroups

section QCompletion

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
  CFSG.Quasithin.F7 CFSG.ASVolI.ChF

variable {E : Type} [Group E] {M₁ M₂ : Subgroup E} {Y : Type} [Group Y]

theorem burnsideF4k_conjSub_f1 {α : RankTwoAmalgam.{0}} (c : α.Completion Y) {Q : Subgroup α.G1}
    (hQ : Q.Normal) (a : α.G1) :
    conjSub (f1 (c := c) a) (Q.map (f1 (c := c))) = Q.map (f1 (c := c)) := by
  rw [LieSetting.conjSub_map, LieSetting.conjSub_normal hQ]

theorem burnsideF4k_conjSub_f2 {α : RankTwoAmalgam.{0}} (c : α.Completion Y) {Q : Subgroup α.G2}
    (hQ : Q.Normal) (a : α.G2) :
    conjSub (f2 (c := c) a) (Q.map (f2 (c := c))) = Q.map (f2 (c := c)) := by
  rw [LieSetting.conjSub_map, LieSetting.conjSub_normal hQ]

theorem burnsideF4k_QNormalized (p : ℕ) {Gp : Subgroup E} (hN : Gp.Normal) (c : Cpl M₁ M₂ Y) :
    QNormalized (Qx p Gp c) (Ql p Gp c) := by
  intro b h hh
  cases b
  · have hh' : h ∈ stv c c.xv := MulAction.mem_stabilizer_iff.mpr hh
    obtain ⟨a0, rfl⟩ := stv_xv_le_range_f1 c hh'
    exact burnsideF4k_conjSub_f1 c (burnsideF4k_Qbar_normal p hN M₁) a0
  · have hh' : h ∈ stv c c.lv := MulAction.mem_stabilizer_iff.mpr hh
    obtain ⟨a0, rfl⟩ := stv_lv_le_range_f2 c hh'
    exact burnsideF4k_conjSub_f2 c (burnsideF4k_Qbar_normal p hN M₂) a0

theorem burnsideF4k_Qu_xv (p : ℕ) {Gp : Subgroup E} (hN : Gp.Normal) (c : Cpl M₁ M₂ Y) :
    Qu p Gp c c.xv = Qx p Gp c :=
  Qvert_baseVert (burnsideF4k_QNormalized p hN c) false

end QCompletion

section F416Hyps

open CFSG.Quasithin CFSG.ASVolI.ChF

def burnsideF4k_Reg : Prop :=
  ∀ (κ : GLKind) (p f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E),
    HypF_4_4 κ p f Gp M₁ M₂ →
    (∀ a b : E, a ∈ M₁ → b ∈ M₁ → a ∉ M₂ → b ∉ M₂ →
      ∃ s ∈ pCoreOf p (Gp ⊓ (M₁ ⊓ M₂)), b⁻¹ * s * a ∈ M₂) ∧
    (∀ a : E, a ∈ M₁ → a ∉ M₂ → ∀ s ∈ pCoreOf p (Gp ⊓ (M₁ ⊓ M₂)), a⁻¹ * s * a ∈ M₂ →
      s ∈ pCoreOf p (Gp ⊓ M₁))

end F416Hyps

section F416Pieces

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
  CFSG.ASVolI.ChF

variable {E : Type} [Group E] {M₁ M₂ : Subgroup E} {Y : Type} [Group Y]

@[expose] def burnsideF4k_val1 (M₁ M₂ : Subgroup E) (a : (RankTwoAmalgam.ofSubgroups M₁ M₂).G1) : E :=
  Subtype.val (show ↥M₁ from a)

theorem burnsideF4k_val1_mem (a : (RankTwoAmalgam.ofSubgroups M₁ M₂).G1) :
    burnsideF4k_val1 M₁ M₂ a ∈ M₁ := (show ↥M₁ from a).2

@[expose] def burnsideF4k_val12 (M₁ M₂ : Subgroup E) (d : (RankTwoAmalgam.ofSubgroups M₁ M₂).G12) :
    E := Subtype.val (show ↥(M₁ ⊓ M₂) from d)

theorem burnsideF4k_mem_range_iff (a : (RankTwoAmalgam.ofSubgroups M₁ M₂).G1) :
    a ∈ (RankTwoAmalgam.ofSubgroups M₁ M₂).α1.range ↔ burnsideF4k_val1 M₁ M₂ a ∈ M₂ := by
  rw [MonoidHom.mem_range]
  constructor
  · rintro ⟨d, hd⟩
    have h1 : burnsideF4k_val1 M₁ M₂ ((RankTwoAmalgam.ofSubgroups M₁ M₂).α1 d) =
        burnsideF4k_val1 M₁ M₂ a := congrArg (burnsideF4k_val1 M₁ M₂) hd
    rw [← h1]
    exact d.2.2
  · intro h
    exact ⟨⟨burnsideF4k_val1 M₁ M₂ a, ⟨burnsideF4k_val1_mem a, h⟩⟩, rfl⟩

theorem burnsideF4k_nbr_form (β : Cpl M₁ M₂ Y) {w : β.Γ} (hw : β.graph.Adj β.xv w) :
    ∃ a : (RankTwoAmalgam.ofSubgroups M₁ M₂).G1, w = f1 (c := β) a • β.lv := by
  have hxl : β.graph.Adj β.xv β.lv := CosetGeom.adj_γ₀_γ₁
  obtain ⟨g, hgx, hgl⟩ := CosetGeom.exists_stab_smul_eq hxl hw
  have hg : g ∈ (f1 (c := β)).range := by
    rw [← stv_xv_eq_range]
    exact MulAction.mem_stabilizer_iff.mpr hgx
  obtain ⟨a, rfl⟩ := hg
  exact ⟨a, hgl.symm⟩

theorem burnsideF4k_f1_fix_lv_iff (β : Cpl M₁ M₂ Y) (hβ : β.IsFaithful)
    (a : (RankTwoAmalgam.ofSubgroups M₁ M₂).G1) :
    f1 (c := β) a • β.lv = β.lv ↔ burnsideF4k_val1 M₁ M₂ a ∈ M₂ :=
  (burnsideF4k_f1_smul_lv_iff hβ a).trans (burnsideF4k_mem_range_iff a)

theorem burnsideF4k_mem_Qx {p : ℕ} {Gp : Subgroup E} (β : Cpl M₁ M₂ Y) {x : β.G0} :
    x ∈ Qx p Gp β ↔ ∃ a : (RankTwoAmalgam.ofSubgroups M₁ M₂).G1,
      burnsideF4k_val1 M₁ M₂ a ∈ pCoreOf p (Gp ⊓ M₁) ∧ f1 (c := β) a = x := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩

theorem burnsideF4k_mem_Sp {p : ℕ} {Gp : Subgroup E} (β : Cpl M₁ M₂ Y) {x : β.G0} :
    x ∈ Sp p Gp β ↔ ∃ d : (RankTwoAmalgam.ofSubgroups M₁ M₂).G12,
      burnsideF4k_val12 M₁ M₂ d ∈ pCoreOf p (Gp ⊓ (M₁ ⊓ M₂)) ∧
        f1 (c := β) ((RankTwoAmalgam.ofSubgroups M₁ M₂).α1 d) = x := by
  constructor
  · rintro ⟨_, ⟨d, hd, rfl⟩, rfl⟩
    exact ⟨d, hd, rfl⟩
  · rintro ⟨d, hd, rfl⟩
    exact ⟨_, ⟨d, hd, rfl⟩, rfl⟩

theorem burnsideF4k_Qb1_normal (p : ℕ) {Gp : Subgroup E} (hN : Gp.Normal) (M₁ M₂ : Subgroup E) :
    (((pCoreOf p (Gp ⊓ M₁)).subgroupOf M₁ : Subgroup (RankTwoAmalgam.ofSubgroups M₁ M₂).G1)).Normal :=
  burnsideF4k_Qbar_normal p hN M₁

theorem burnsideF4k_Sb_normal (p : ℕ) {Gp : Subgroup E} (hN : Gp.Normal) (M₁ M₂ : Subgroup E) :
    (((pCoreOf p (Gp ⊓ (M₁ ⊓ M₂))).subgroupOf (M₁ ⊓ M₂) :
      Subgroup (RankTwoAmalgam.ofSubgroups M₁ M₂).G12)).Normal :=
  burnsideF4k_Qbar_normal p hN (M₁ ⊓ M₂)

theorem burnsideF4k_Sp_le (p : ℕ) {Gp : Subgroup E} (β : Cpl M₁ M₂ Y) (hβ : β.IsFaithful) :
    Sp p Gp β ≤ stv β β.xv ⊓ stv β β.lv := by
  intro x hx
  obtain ⟨d, -, rfl⟩ := (burnsideF4k_mem_Sp β).mp hx
  refine Subgroup.mem_inf.mpr ⟨MulAction.mem_stabilizer_iff.mpr (f1_smul_xv _),
    MulAction.mem_stabilizer_iff.mpr ?_⟩
  exact (burnsideF4k_f1_smul_lv_iff hβ _).mpr ⟨d, rfl⟩

theorem burnsideF4k_Qx_le_Sp {p : ℕ} {Gp : Subgroup E} (β : Cpl M₁ M₂ Y)
    (hQM2 : pCoreOf p (Gp ⊓ M₁) ≤ M₂)
    (hQS : pCoreOf p (Gp ⊓ M₁) ≤ pCoreOf p (Gp ⊓ (M₁ ⊓ M₂))) : Qx p Gp β ≤ Sp p Gp β := by
  intro x hx
  obtain ⟨a, ha, rfl⟩ := (burnsideF4k_mem_Qx β).mp hx
  exact (burnsideF4k_mem_Sp β).mpr ⟨⟨burnsideF4k_val1 M₁ M₂ a,
    ⟨burnsideF4k_val1_mem a, hQM2 ha⟩⟩, hQS ha, rfl⟩

end F416Pieces

section F416Pieces2

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
  CFSG.ASVolI.ChF

variable {E : Type} [Group E] {M₁ M₂ : Subgroup E} {Y : Type} [Group Y]

theorem burnsideF4k_Qx_fix {p : ℕ} {Gp : Subgroup E} (hN : Gp.Normal) (β : Cpl M₁ M₂ Y)
    (hβ : β.IsFaithful) (hQM2 : pCoreOf p (Gp ⊓ M₁) ≤ M₂) {w : β.Γ}
    (hw : β.graph.Adj β.xv w) {q : β.G0} (hq : q ∈ Qx p Gp β) : q • w = w := by
  obtain ⟨a, rfl⟩ := burnsideF4k_nbr_form β hw
  obtain ⟨q₀, hq₀, rfl⟩ := (burnsideF4k_mem_Qx β).mp hq
  have hq₀' : q₀ ∈ ((pCoreOf p (Gp ⊓ M₁)).subgroupOf M₁ :
      Subgroup (RankTwoAmalgam.ofSubgroups M₁ M₂).G1) := hq₀
  have hconj : a⁻¹ * q₀ * a ∈ ((pCoreOf p (Gp ⊓ M₁)).subgroupOf M₁ :
      Subgroup (RankTwoAmalgam.ofSubgroups M₁ M₂).G1) := by
    exact (burnsideF4k_Qb1_normal p hN M₁ M₂).conj_mem' q₀ hq₀' a
  have hfix : f1 (c := β) (a⁻¹ * q₀ * a) • β.lv = β.lv :=
    (burnsideF4k_f1_fix_lv_iff β hβ _).mpr (hQM2 hconj)
  rw [← mul_smul]
  have e : f1 (c := β) q₀ * f1 (c := β) a = f1 (c := β) a * f1 (c := β) (a⁻¹ * q₀ * a) := by
    simp only [map_mul, map_inv]
    group
  rw [e, mul_smul, hfix]

theorem burnsideF4k_Sp_trans {p : ℕ} {Gp : Subgroup E} (β : Cpl M₁ M₂ Y) (hβ : β.IsFaithful)
    (hregA : ∀ a b : E, a ∈ M₁ → b ∈ M₁ → a ∉ M₂ → b ∉ M₂ →
      ∃ s ∈ pCoreOf p (Gp ⊓ (M₁ ⊓ M₂)), b⁻¹ * s * a ∈ M₂)
    {w₁ w₂ : β.Γ} (hw₁ : β.graph.Adj β.xv w₁) (hw₂ : β.graph.Adj β.xv w₂) (hw₁l : w₁ ≠ β.lv)
    (hw₂l : w₂ ≠ β.lv) : ∃ s ∈ Sp p Gp β, s • w₁ = w₂ := by
  obtain ⟨a₁, rfl⟩ := burnsideF4k_nbr_form β hw₁
  obtain ⟨a₂, rfl⟩ := burnsideF4k_nbr_form β hw₂
  have ha₁ : burnsideF4k_val1 M₁ M₂ a₁ ∉ M₂ := fun h =>
    hw₁l ((burnsideF4k_f1_fix_lv_iff β hβ a₁).mpr h)
  have ha₂ : burnsideF4k_val1 M₁ M₂ a₂ ∉ M₂ := fun h =>
    hw₂l ((burnsideF4k_f1_fix_lv_iff β hβ a₂).mpr h)
  obtain ⟨s, hs, hsM⟩ := hregA _ _ (burnsideF4k_val1_mem a₁) (burnsideF4k_val1_mem a₂) ha₁ ha₂
  have hsB : s ∈ Gp ⊓ (M₁ ⊓ M₂) := CFSG.LieType.BorelTits.pCoreOf_le p _ hs
  let d : (RankTwoAmalgam.ofSubgroups M₁ M₂).G12 := ⟨s, (Subgroup.mem_inf.mp hsB).2⟩
  refine ⟨f1 (c := β) ((RankTwoAmalgam.ofSubgroups M₁ M₂).α1 d),
    (burnsideF4k_mem_Sp β).mpr ⟨d, hs, rfl⟩, ?_⟩
  rw [← mul_smul]
  have ht : (a₂⁻¹ * (RankTwoAmalgam.ofSubgroups M₁ M₂).α1 d * a₁ :
      (RankTwoAmalgam.ofSubgroups M₁ M₂).G1) ∈ (RankTwoAmalgam.ofSubgroups M₁ M₂).α1.range :=
    (burnsideF4k_mem_range_iff _).mpr hsM
  have e : f1 (c := β) ((RankTwoAmalgam.ofSubgroups M₁ M₂).α1 d) * f1 (c := β) a₁ =
      f1 (c := β) a₂ * f1 (c := β) (a₂⁻¹ * (RankTwoAmalgam.ofSubgroups M₁ M₂).α1 d * a₁) := by
    simp only [map_mul, map_inv]
    group
  rw [e, mul_smul, (burnsideF4k_f1_smul_lv_iff hβ _).mpr ht]

theorem burnsideF4k_Sp_stab {p : ℕ} {Gp : Subgroup E} (β : Cpl M₁ M₂ Y) (hβ : β.IsFaithful)
    (hregB : ∀ a : E, a ∈ M₁ → a ∉ M₂ → ∀ s ∈ pCoreOf p (Gp ⊓ (M₁ ⊓ M₂)), a⁻¹ * s * a ∈ M₂ →
      s ∈ pCoreOf p (Gp ⊓ M₁))
    {w : β.Γ} (hw : β.graph.Adj β.xv w) (hwl : w ≠ β.lv) {s' : β.G0} (hs' : s' ∈ Sp p Gp β)
    (hfix : s' • w = w) : s' ∈ Qx p Gp β := by
  obtain ⟨a, rfl⟩ := burnsideF4k_nbr_form β hw
  have ha : burnsideF4k_val1 M₁ M₂ a ∉ M₂ := fun h =>
    hwl ((burnsideF4k_f1_fix_lv_iff β hβ a).mpr h)
  obtain ⟨d, hd, rfl⟩ := (burnsideF4k_mem_Sp β).mp hs'
  have hfix' : f1 (c := β) (a⁻¹ * (RankTwoAmalgam.ofSubgroups M₁ M₂).α1 d * a) • β.lv = β.lv := by
    have e : f1 (c := β) (a⁻¹ * (RankTwoAmalgam.ofSubgroups M₁ M₂).α1 d * a) =
        (f1 (c := β) a)⁻¹ * f1 (c := β) ((RankTwoAmalgam.ofSubgroups M₁ M₂).α1 d) *
          f1 (c := β) a := by
      simp only [map_mul, map_inv]
    rw [e, mul_smul, mul_smul, hfix]
    exact inv_smul_smul _ _
  have hmem2 := (burnsideF4k_f1_fix_lv_iff β hβ _).mp hfix'
  have hreg' := hregB _ (burnsideF4k_val1_mem a) ha (burnsideF4k_val12 M₁ M₂ d) hd hmem2
  exact (burnsideF4k_mem_Qx β).mpr ⟨(RankTwoAmalgam.ofSubgroups M₁ M₂).α1 d, hreg', rfl⟩

end F416Pieces2

section F416Pieces3

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
  CFSG.ASVolI.ChF

variable {E : Type} [Group E] {M₁ M₂ : Subgroup E} {Y : Type} [Group Y]

theorem burnsideF4k_Sp_normal {p : ℕ} {Gp : Subgroup E} (hN : Gp.Normal) (β : Cpl M₁ M₂ Y)
    (hβ : β.IsFaithful) : ((Sp p Gp β).subgroupOf (stv β β.xv ⊓ stv β β.lv)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have hn' : (n : β.G0) ∈ Sp p Gp β := hn
  obtain ⟨d, hd, hdn⟩ := (burnsideF4k_mem_Sp β).mp hn'
  obtain ⟨hgx, hgl⟩ := Subgroup.mem_inf.mp g.2
  have hga : (g : β.G0) ∈ (f1 (c := β)).range := by
    rw [← stv_xv_eq_range]
    exact hgx
  obtain ⟨a, ha⟩ := hga
  have hae : a ∈ (RankTwoAmalgam.ofSubgroups M₁ M₂).α1.range :=
    (burnsideF4k_f1_smul_lv_iff hβ a).mp (by rw [ha]; exact MulAction.mem_stabilizer_iff.mp hgl)
  obtain ⟨e, he⟩ := hae
  show (g : β.G0) * (n : β.G0) * (g : β.G0)⁻¹ ∈ Sp p Gp β
  rw [← hdn, ← ha, ← he]
  have hd' : d ∈ ((pCoreOf p (Gp ⊓ (M₁ ⊓ M₂))).subgroupOf (M₁ ⊓ M₂) :
      Subgroup (RankTwoAmalgam.ofSubgroups M₁ M₂).G12) := hd
  refine (burnsideF4k_mem_Sp β).mpr ⟨e * d * e⁻¹,
    (burnsideF4k_Sb_normal p hN M₁ M₂).conj_mem d hd' e, ?_⟩
  simp only [map_mul, map_inv]

end F416Pieces3

section F416Final

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
  CFSG.ASVolI.ChF

theorem burnsideF4k_lie_ne (hF : F_4_6) (hcompat : NativeChartCompatibilityGoal)
    {κ : GLKind} {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 κ p f Gp M₁ M₂) (hext : IsLieExtAmalgam M₁ M₂) {Y : Type} [Group Y]
    (β : Cpl M₁ M₂ Y) (hβ : β.IsFaithful) : κ ≠ GLKind.G2d ∧ κ ≠ GLKind.Tits := by
  have hthick := burnsideF4a_thick_of_hyp hcompat hyp.toHypF_4_4g
  have hval := burnsideF4a_hval hβ hthick.1 hthick.2
  have h6 := hF κ p f E Gp M₁ M₂ hyp Y β hβ (incl M₁ M₂) rfl
  have key : ¬ (κ = GLKind.G2d ∨ κ = GLKind.Tits) := by
    intro hκ
    have h1 := h6.1 β.lv
    have ht : β.PathTrans β.lv (κ.m + 1) := h1.1 hext
    obtain ⟨-, ⟨q₁, hq₁, q₂, hq₂, -, hD, -⟩, -⟩ :=
      (h1.2 ⟨hyp.canonical hκ, hκ⟩).2 CosetGeom.vtype_γ₁
    obtain ⟨g, hg1, hg2⟩ := GPath.trans_le hval ht 1 κ.m rfl q₂ q₁ hq₂ hq₁
    exact Set.disjoint_left.mp hD ⟨1, one_mem _, GPath.one_smul' q₁⟩
      ⟨g, MulAction.mem_stabilizer_iff.mpr hg1, hg2⟩
  exact ⟨fun h => key (Or.inl h), fun h => key (Or.inr h)⟩

theorem burnsideF4k_F416 (hF : F_4_6) (hcompat : NativeChartCompatibilityGoal)
    (hreg : burnsideF4k_Reg) : F_4_16 := by
  intro κ p f E _ Gp M₁ M₂ hyp hext Y _ β hβ hs S hS hx hl
  haveI := hyp.finite
  have hp := burnsideF4a_prime_of_isGenLie hyp.model
  haveI : Fact p.Prime := ⟨hp⟩
  have hN : Gp.Normal := hyp.normal
  have hP := burnsideF4k_parabolics hcompat hyp
  have hF46 := burnsideF4a_facts46_of_compat hF hcompat hyp β hβ
  obtain ⟨hκ1, hκ2⟩ := burnsideF4k_lie_ne hF hcompat hyp hext β hβ
  have h6 := hF κ p f E Gp M₁ M₂ hyp Y β hβ (incl M₁ M₂) rfl
  have h58 := h6.2.2.2.2
  obtain ⟨hregA, hregB⟩ := hreg κ p f E Gp M₁ M₂ hyp
  have hm : 2 ≤ κ.m := hF46.hm
  have hQM2 := (burnsideF4k_pCoreOf_le hp hP).1
  have hQS := burnsideF4k_Q_le_S hp hN hP
  have hΓ := connected_graph β
  have hSg := burnsideF4k_Sp_le p (Gp := Gp) β hβ
  have hQSp := burnsideF4k_Qx_le_Sp β hQM2 hQS
  refine ⟨⟨hSg, burnsideF4k_Sp_normal hN β hβ, ?_⟩,
    fun sx sl hW => burnsideF4k_F416_two β hm hS hx hl hW⟩
  refine burnsideF4k_F416_core hF46 hS hx hl ?_ ?_ hQSp hSg ?_ ?_ ?_
  ·
    intro b hbS hbd
    obtain ⟨p₀, q₀, hp₀, hq₀, hp0, hq0, hpm, hqm, hpq, -⟩ :=
      GPath.exists_arcs_of_polygon hΓ hm hS hx hbS hbd
    have hp₀nb : p₀ ∈ GPath.nbPaths β.graph β.xv κ.m :=
      ⟨hp0, GPath.noBack_of_dist_eq hΓ p₀ hp₀⟩
    rcases (h58 β.xv p₀ hp₀nb).2.2.2 with h | h | h | h
    · exfalso
      exact hpq (h q₀ hq0 (hqm.trans hpm.symm) hq₀).symm
    · have hcmp := h.1
      rw [burnsideF4k_Qu_xv p hN β, hpm] at hcmp
      exact hcmp
    · exact absurd h.1.2 hκ2
    · exact absurd h.1.2 hκ1
  ·
    intro b b' hbd hb'd
    obtain ⟨P, hP0, hPb, hPnb⟩ := GPath.exists_geodesic' hΓ β.xv b hbd
    obtain ⟨P', hP0', hPb', hPnb'⟩ := GPath.exists_geodesic' hΓ β.xv b' hb'd
    obtain ⟨g, hg1, hg2⟩ := hF46.trans_pt β.xv rfl P P' ⟨hP0, hPnb⟩ ⟨hP0', hPnb'⟩
    refine ⟨g, hg1, ?_⟩
    have := congrArg (fun r : GPath β.graph κ.m => r κ.m) hg2
    simp only [GPath.smul_apply] at this
    rw [hPb, hPb'] at this
    exact this
  · exact fun w hw q hq => burnsideF4k_Qx_fix hN β hβ hQM2 hw hq
  · exact fun w₁ w₂ hw₁ hw₂ hw₁l hw₂l => burnsideF4k_Sp_trans β hβ hregA hw₁ hw₂ hw₁l hw₂l
  · exact fun w hw hwl s hs hfix => burnsideF4k_Sp_stab β hβ hregB hw hwl hs hfix

end F416Final

section F415One

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
  CFSG.ASVolI.ChF

theorem burnsideF4k_three {X : Type*} {s : Set X} (hs : s.ncard = 3) {a b c d : X} (ha : a ∈ s)
    (hb : b ∈ s) (hc : c ∈ s) (hd : d ∈ s) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    d = a ∨ d = b ∨ d = c := by
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Set.ncard_eq_three.mp hs
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb hc hd
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    rcases hc with rfl | rfl | rfl <;> rcases hd with rfl | rfl | rfl <;> simp_all

theorem burnsideF4k_geods_smul {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y] {c : α.Completion Y}
    {m : ℕ} {a b : c.Γ} {g : c.G0} (hg : g ∈ stv c a ⊓ stv c b) {r : GPath c.graph m}
    (hr : r ∈ c.geods m a b) : g • r ∈ c.geods m a b := by
  have h := smul_mem_geods g hr
  have ha : g • a = a := MulAction.mem_stabilizer_iff.mp (Subgroup.mem_inf.mp hg).1
  have hb : g • b = b := MulAction.mem_stabilizer_iff.mp (Subgroup.mem_inf.mp hg).2
  rwa [ha, hb] at h

theorem burnsideF4k_Z3_pairs {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y] {c : α.Completion Y}
    {m : ℕ} {a b : c.Γ} (hH : Nat.card ↥(stv c a ⊓ stv c b) = 3)
    (hcard : Nat.card ↥(c.geods m a b) = 3)
    (htrans : ∀ q₁ ∈ c.geods m a b, ∀ q₂ ∈ c.geods m a b, ∃ g ∈ stv c a ⊓ stv c b, g • q₁ = q₂)
    {p₁ q₁ p₂ q₂ : GPath c.graph m} (hp₁ : p₁ ∈ c.geods m a b) (hq₁ : q₁ ∈ c.geods m a b)
    (hp₂ : p₂ ∈ c.geods m a b) (hq₂ : q₂ ∈ c.geods m a b) (h₁ : p₁ ≠ q₁) (h₂ : p₂ ≠ q₂) :
    ∃ g ∈ stv c a ⊓ stv c b, (g • p₁ = p₂ ∧ g • q₁ = q₂) ∨ (g • p₁ = q₂ ∧ g • q₁ = p₂) := by
  classical
  haveI : Finite ↥(stv c a ⊓ stv c b) := Nat.finite_of_card_ne_zero (by omega)
  have hncard : (c.geods m a b).ncard = 3 := by rw [← Nat.card_coe_set_eq]; exact hcard
  have hreg : ∀ r ∈ c.geods m a b, ∀ h ∈ stv c a ⊓ stv c b, h • r = r → h = 1 := by
    intro r hr h hh hhr
    let f : ↥(stv c a ⊓ stv c b) → ↥(c.geods m a b) := fun k =>
      ⟨(k : c.G0) • r, burnsideF4k_geods_smul k.2 hr⟩
    have hsurj : Function.Surjective f := by
      rintro ⟨r', hr'⟩
      obtain ⟨g, hg, hgr⟩ := htrans r hr r' hr'
      exact ⟨⟨g, hg⟩, Subtype.ext hgr⟩
    have hbij := Function.Surjective.bijective_of_nat_card_le hsurj (by rw [hH, hcard])
    have h1 : f ⟨h, hh⟩ = f 1 := by
      apply Subtype.ext
      show h • r = (1 : c.G0) • r
      rw [GPath.one_smul']
      exact hhr
    have := hbij.1 h1
    exact congrArg Subtype.val this
  have hinj : ∀ (g : c.G0) (r r' : GPath c.graph m), g • r = g • r' → r = r' := by
    intro g r r' h
    have := congrArg (fun s : GPath c.graph m => g⁻¹ • s) h
    simpa only [GPath.inv_smul_smul'] using this
  have hfree : ∀ r ∈ c.geods m a b, ∀ g ∈ stv c a ⊓ stv c b, ∀ g' ∈ stv c a ⊓ stv c b,
      g • r = g' • r → g = g' := by
    intro r hr g hg g' hg' h
    have h1 : (g'⁻¹ * g) • r = r := by
      rw [GPath.mul_smul', h, ← GPath.mul_smul', inv_mul_cancel, GPath.one_smul']
    exact (inv_mul_eq_one.mp (hreg r hr (g'⁻¹ * g) (mul_mem (inv_mem hg') hg) h1)).symm
  obtain ⟨g, hg, hgp⟩ := htrans p₁ hp₁ p₂ hp₂
  by_cases hq : g • q₁ = q₂
  · exact ⟨g, hg, Or.inl ⟨hgp, hq⟩⟩
  · obtain ⟨g', hg', hgp'⟩ := htrans p₁ hp₁ q₂ hq₂
    refine ⟨g', hg', Or.inr ⟨hgp', ?_⟩⟩
    by_contra hq'
    have hgq : g • q₁ ∈ c.geods m a b := burnsideF4k_geods_smul hg hq₁
    have hgq' : g' • q₁ ∈ c.geods m a b := burnsideF4k_geods_smul hg' hq₁
    have e1 : g • q₁ ≠ p₂ := fun h => h₁ (hinj g _ _ (hgp.trans h.symm))
    have e2 : g' • q₁ ≠ q₂ := fun h => h₁ (hinj g' _ _ (hgp'.trans h.symm))
    rcases burnsideF4k_three hncard hp₂ hq₂ hgq' hgq h₂ (fun h => hq' h.symm) (fun h => e2 h.symm)
      with h | h | h
    · exact e1 h
    · exact hq h
    · have hgg : g = g' := hfree q₁ hq₁ g hg g' hg' h
      subst hgg
      exact h₂ (hgp.symm.trans hgp')

theorem burnsideF4k_F415_one (hF : F_4_6) (hcompat : NativeChartCompatibilityGoal)
    {κ : GLKind} {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 κ p f Gp M₁ M₂) {Y : Type} [Group Y] (β : Cpl M₁ M₂ Y) (hβ : β.IsFaithful)
    (hnT : ¬ (Gp = ⊤ ∧ κ = .Tits)) {A A' : Set β.Γ} (hA : β.IsApartment κ.m A)
    (hA' : β.IsApartment κ.m A') : ∃ g : β.G0, (fun w => g • w) '' A = A' := by
  have F := burnsideF4a_facts46_of_compat hF hcompat hyp β hβ
  have hm := F.hm
  have h6 := hF κ p f E Gp M₁ M₂ hyp Y β hβ (incl M₁ M₂) rfl
  have h58 := h6.2.2.2.2
  have hconn := connected_graph β
  have hbip : ∀ x y : β.Γ, β.graph.Adj x y → CosetGeom.vtype x ≠ CosetGeom.vtype y :=
    fun _ _ h => CosetGeom.vtype_ne_of_adj h
  have P1 : ∀ {B : Set β.Γ}, β.IsApartment κ.m B → ∀ a ∈ B,
      (∃ b ∈ B, β.graph.dist a b = κ.m) ∧ ∃ w ∈ B, β.graph.Adj a w :=
    fun {B} hB a ha => GPath.exists_opposite_of_polygon (c := CosetGeom.vtype) hconn hbip
      F.uniqueGeod hm hB ha
  have hpt : ∀ {B : Set β.Γ}, β.IsApartment κ.m B → ∃ a ∈ B, CosetGeom.vtype a = false := by
    intro B hB
    obtain ⟨φ⟩ := hB
    have hB0 : (φ ⟨0, by omega⟩ : ↥B).1 ∈ B := (φ ⟨0, by omega⟩).2
    by_cases h : CosetGeom.vtype (φ ⟨0, by omega⟩ : ↥B).1 = false
    · exact ⟨_, hB0, h⟩
    · obtain ⟨w, hwB, hadj⟩ := (P1 ⟨φ⟩ _ hB0).2
      refine ⟨w, hwB, ?_⟩
      have := hbip _ _ hadj
      revert h this
      cases CosetGeom.vtype (φ ⟨0, by omega⟩ : ↥B).1 <;> cases CosetGeom.vtype w <;> simp
  obtain ⟨a, haA, hapt⟩ := hpt hA
  obtain ⟨a', ha'A', ha'pt⟩ := hpt hA'
  obtain ⟨b, hbA, hab⟩ := (P1 hA a haA).1
  obtain ⟨b', hb'A', hab'⟩ := (P1 hA' a' ha'A').1
  obtain ⟨g₁, hg₁⟩ := exists_smul_of_vtype_eq a a' (hapt.trans ha'pt.symm)
  have hd1 : β.graph.dist a' (g₁ • b) = κ.m := by
    rw [← hg₁, GPath.dist_smul hconn g₁ a b]
    exact hab
  obtain ⟨P, hP, hPb⟩ := Facts46.exists_geod_path (c := β) (m := κ.m) hd1
  obtain ⟨P', hP', hP'b⟩ := Facts46.exists_geod_path (c := β) (m := κ.m) hab'
  obtain ⟨h, hh1, hh2⟩ := F.trans_pt a' ha'pt P P' hP hP'
  have hhb : h • (g₁ • b) = b' := by
    rw [← hPb, ← hP'b]
    exact congrArg (fun r : GPath β.graph κ.m => r κ.m) hh2
  have hg₂a : (h * g₁) • a = a' := by rw [mul_smul, hg₁, hh1]
  have hg₂b : (h * g₁) • b = b' := by rw [mul_smul, hhb]
  obtain ⟨p₁, q₁, hp₁, hq₁, hpq₁, hAeq⟩ := (F.lemma_F414_1 hab A).mp ⟨hA, haA, hbA⟩
  obtain ⟨p₂, q₂, hp₂, hq₂, hpq₂, hA'eq⟩ := (F.lemma_F414_1 hab' A').mp ⟨hA', ha'A', hb'A'⟩
  have hgp : (h * g₁) • p₁ ∈ β.geods κ.m a' b' := by
    have := smul_mem_geods (h * g₁) hp₁
    rwa [hg₂a, hg₂b] at this
  have hgq : (h * g₁) • q₁ ∈ β.geods κ.m a' b' := by
    have := smul_mem_geods (h * g₁) hq₁
    rwa [hg₂a, hg₂b] at this
  have hgpq : (h * g₁) • p₁ ≠ (h * g₁) • q₁ := fun heq => hpq₁ (by
    have := congrArg (fun r : GPath β.graph κ.m => (h * g₁)⁻¹ • r) heq
    simpa [← GPath.mul_smul', inv_mul_cancel, GPath.one_smul'] using this)
  have hcase := (h58 a' P' hP').2
  rw [hP'b] at hcase
  have key : ∃ g₃ ∈ stv β a' ⊓ stv β b',
      (g₃ • ((h * g₁) • p₁) = p₂ ∧ g₃ • ((h * g₁) • q₁) = q₂) ∨
      (g₃ • ((h * g₁) • p₁) = q₂ ∧ g₃ • ((h * g₁) • q₁) = p₂) := by
    rcases hcase.2.2 with huniq | ⟨-, htrans2, -⟩ | hT | ⟨-, -, hZ, htr, hcard, -⟩
    · exact absurd ((huniq p₂ hp₂.1 hp₂.2.1 hp₂.2.2).trans (huniq q₂ hq₂.1 hq₂.2.1 hq₂.2.2).symm) hpq₂
    · obtain ⟨g₃, hg₃, e1, e2⟩ := htrans2 _ hgp _ hgq hgpq _ hp₂ _ hq₂ hpq₂
      exact ⟨g₃, hg₃, Or.inl ⟨e1, e2⟩⟩
    · exact absurd hT.1 hnT
    · obtain ⟨e⟩ := hZ
      have hH : Nat.card ↥(stv β a' ⊓ stv β b') = 3 := by
        rw [Nat.card_congr e.toEquiv]
        simp [Nat.card_eq_fintype_card]
      exact burnsideF4k_Z3_pairs hH hcard htr hgp hgq hp₂ hq₂ hgpq hpq₂
  obtain ⟨g₃, -, hcases⟩ := key
  refine ⟨g₃ * (h * g₁), ?_⟩
  rw [hAeq, hA'eq, GPath.range_cycSeq (by omega) (hp₁.1.trans hq₁.1.symm) (hp₁.2.1.trans hq₁.2.1.symm),
    GPath.range_cycSeq (by omega) (hp₂.1.trans hq₂.1.symm) (hp₂.2.1.trans hq₂.2.1.symm),
    Set.image_union, GPath.image_smul_verts, GPath.image_smul_verts]
  rcases hcases with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · have hmp : (g₃ * (h * g₁)) • p₁ = p₂ := by rw [GPath.mul_smul']; exact e1
    have hmq : (g₃ * (h * g₁)) • q₁ = q₂ := by rw [GPath.mul_smul']; exact e2
    rw [hmp, hmq]
  · have hmp : (g₃ * (h * g₁)) • p₁ = q₂ := by rw [GPath.mul_smul']; exact e1
    have hmq : (g₃ * (h * g₁)) • q₁ = p₂ := by rw [GPath.mul_smul']; exact e2
    rw [hmp, hmq, Set.union_comm]

end F415One

section RegGroupTheory

open CFSG.ASVolI.ChF

theorem burnsideF4k_pElt_mem_pCoreOf {E : Type} [Group E] [Finite E] {p : ℕ} (hp : p.Prime)
    {H S B : Subgroup E} (hS : IsSylowOf p S H) (hB : B = H ⊓ Subgroup.normalizer (S : Set E))
    {x : E} (hx : x ∈ B) {k : ℕ} (hk : orderOf x = p ^ k) : x ∈ pCoreOf p B := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hSH, hSp, hSidx⟩ := hS
  have hSB : S ≤ B := by rw [hB]; exact le_inf hSH Subgroup.le_normalizer
  have hBN : B ≤ Subgroup.normalizer (S : Set E) := by rw [hB]; exact inf_le_right
  have hBH : B ≤ H := by rw [hB]; exact inf_le_left
  have hxS : x ∈ S := by
    have h1 : IsPGroup p (S.subgroupOf B) := hSp.comap_subtype
    have hdvd : S.relIndex B ∣ S.relIndex H :=
      ⟨B.relIndex H, (Subgroup.relIndex_mul_relIndex S B H hSB hBH).symm⟩
    have h2 : ¬ p ∣ (S.subgroupOf B).index := fun h => hSidx (h.trans hdvd)
    let T : Sylow p ↥B := h1.toSylow h2
    have hnorm : (S.subgroupOf B).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hSB).mpr hBN
    have hTn : (T : Subgroup ↥B).Normal := hnorm
    let y : ↥B := ⟨x, hx⟩
    have hy : IsPGroup p (Subgroup.zpowers y) :=
      IsPGroup.of_card (by rw [Nat.card_zpowers, Subgroup.orderOf_mk]; exact hk)
    obtain ⟨Q, hQ⟩ := hy.exists_le_sylow
    haveI : Unique (Sylow p ↥B) := Sylow.unique_of_normal T hTn
    have hQT : Q = T := Subsingleton.elim _ _
    have hyT : y ∈ (T : Subgroup ↥B) := hQT ▸ hQ (Subgroup.mem_zpowers y)
    exact hyT
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer p hSB hBN hSp hxS

theorem burnsideF4k_oPPrime_le {E : Type} [Group E] (p : ℕ) (H : Subgroup E) : oPPrime p H ≤ H :=
  (Subgroup.closure_le H).mpr fun _ hx => hx.1

theorem burnsideF4k_pCoreOf_subgroupOf {E : Type} [Group E] (p : ℕ) {Gp X : Subgroup E}
    (hX : X ≤ Gp) : (pCoreOf p (X.subgroupOf Gp)).map Gp.subtype = pCoreOf p X := by
  let e : ↥(X.subgroupOf Gp) ≃* ↥X := Subgroup.subgroupOfEquivOfLe hX
  have h1 := CFSG.pCore_map_iso p e
  unfold pCoreOf
  rw [Subgroup.map_map, ← h1, Subgroup.map_map]
  congr 1

end RegGroupTheory

section RegSix

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
  CFSG.ASVolI.ChF

variable {E : Type} [Group E] {N₁ N₂ : Subgroup E} {Y : Type} [Group Y]

@[expose] noncomputable def burnsideF4k_Phi (c : Cpl N₁ N₂ Y) :
    (RankTwoAmalgam.ofSubgroups N₁ N₂).G12 →* c.G0 :=
  (f1 (c := c)).comp (RankTwoAmalgam.ofSubgroups N₁ N₂).α1

theorem burnsideF4k_Phi_injective (c : Cpl N₁ N₂ Y) (hc : c.IsFaithful) :
    Function.Injective (burnsideF4k_Phi c) := by
  intro x y h
  have h1 := f1_injective c hc h
  have h2 : burnsideF4k_val12 N₁ N₂ x = burnsideF4k_val12 N₁ N₂ y :=
    congrArg (burnsideF4k_val1 N₁ N₂) h1
  exact Subtype.ext h2

theorem burnsideF4k_stv_inf_le_range_Phi (c : Cpl N₁ N₂ Y) (hc : c.IsFaithful) :
    stv c c.xv ⊓ stv c c.lv ≤ (burnsideF4k_Phi c).range := by
  intro x hx
  obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
  have hr : x ∈ (f1 (c := c)).range := by rw [← stv_xv_eq_range]; exact hx1
  obtain ⟨a₁, rfl⟩ := hr
  have hmem := (burnsideF4k_f1_smul_lv_iff hc a₁).mp (MulAction.mem_stabilizer_iff.mp hx2)
  obtain ⟨d, rfl⟩ := hmem
  exact ⟨d, rfl⟩

theorem burnsideF4k_Phi_mem (c : Cpl N₁ N₂ Y) (hc : c.IsFaithful)
    (d : (RankTwoAmalgam.ofSubgroups N₁ N₂).G12) :
    burnsideF4k_Phi c d ∈ stv c c.xv ⊓ stv c c.lv := by
  refine Subgroup.mem_inf.mpr ⟨MulAction.mem_stabilizer_iff.mpr (f1_smul_xv _),
    MulAction.mem_stabilizer_iff.mpr ?_⟩
  exact (burnsideF4k_f1_smul_lv_iff hc _).mpr ⟨d, rfl⟩

theorem burnsideF4k_oPPrime_borel [Finite E] {p : ℕ} (hp : p.Prime)
    (hP : IsLieParabolics p ⊤ (⊤ ⊓ (N₁ ⊓ N₂)) (⊤ ⊓ N₁) (⊤ ⊓ N₂)) (c : Cpl N₁ N₂ Y)
    (hc : c.IsFaithful) (d : (RankTwoAmalgam.ofSubgroups N₁ N₂).G12)
    (hg : burnsideF4k_Phi c d ∈ oPPrime p (stv c c.xv ⊓ stv c c.lv)) :
    burnsideF4k_val12 N₁ N₂ d ∈ pCoreOf p (⊤ ⊓ (N₁ ⊓ N₂)) := by
  obtain ⟨S, hS, hB⟩ := hP.1
  let Ψ : (RankTwoAmalgam.ofSubgroups N₁ N₂).G12 →* E := (N₁ ⊓ N₂).subtype
  have hΨ : Function.Injective Ψ := (N₁ ⊓ N₂).subtype_injective
  have hΦ := burnsideF4k_Phi_injective c hc
  let R : Subgroup (RankTwoAmalgam.ofSubgroups N₁ N₂).G12 := (pCoreOf p (⊤ ⊓ (N₁ ⊓ N₂))).comap Ψ
  have hsub : oPPrime p (stv c c.xv ⊓ stv c c.lv) ≤ R.map (burnsideF4k_Phi c) := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨hx, k, hk⟩
    obtain ⟨d', rfl⟩ := burnsideF4k_stv_inf_le_range_Phi c hc hx
    refine ⟨d', ?_, rfl⟩
    have hk' : orderOf d' = p ^ k := by rw [← orderOf_injective _ hΦ d']; exact hk
    have hmemB : Ψ d' ∈ ⊤ ⊓ (N₁ ⊓ N₂) := ⟨Subgroup.mem_top _, d'.2⟩
    have hordΨ : orderOf (Ψ d') = p ^ k := by rw [orderOf_injective _ hΨ d']; exact hk'
    exact burnsideF4k_pElt_mem_pCoreOf hp hS hB hmemB hordΨ
  obtain ⟨d', hd', hdd⟩ := hsub hg
  have := hΦ hdd
  subst this
  exact hd'

theorem burnsideF4k_pCoreOf_borel_mem_oPPrime [Finite E] {p : ℕ} (hp : p.Prime) (c : Cpl N₁ N₂ Y)
    (hc : c.IsFaithful) (d : (RankTwoAmalgam.ofSubgroups N₁ N₂).G12)
    (hd : burnsideF4k_val12 N₁ N₂ d ∈ pCoreOf p (⊤ ⊓ (N₁ ⊓ N₂))) :
    burnsideF4k_Phi c d ∈ oPPrime p (stv c c.xv ⊓ stv c c.lv) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup p (⊤ ⊓ (N₁ ⊓ N₂))) ⟨_, hd⟩
  refine Subgroup.subset_closure ⟨burnsideF4k_Phi_mem c hc d, k, ?_⟩
  rw [orderOf_injective _ (burnsideF4k_Phi_injective c hc) d]
  have h1 : orderOf (burnsideF4k_val12 N₁ N₂ d) = orderOf d :=
    orderOf_injective (N₁ ⊓ N₂).subtype (N₁ ⊓ N₂).subtype_injective d
  rw [← h1, ← Subgroup.orderOf_mk _ hd]
  exact hk

end RegSix

section RegSix2

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
  CFSG.ASVolI.ChF

variable {E : Type} [Group E] {N₁ N₂ : Subgroup E} {Y : Type} [Group Y]

theorem burnsideF4k_adj_f1_lv (c : Cpl N₁ N₂ Y) (X : (RankTwoAmalgam.ofSubgroups N₁ N₂).G1) :
    c.graph.Adj c.xv (f1 (c := c) X • c.lv) := by
  have h := (GraphAction.adj_smul (f1 (c := c) X) c.xv c.lv).mpr CosetGeom.adj_γ₀_γ₁
  rwa [f1_smul_xv] at h

theorem burnsideF4k_reg_of_six [Finite E] {p : ℕ} (hp : p.Prime)
    (hP : IsLieParabolics p ⊤ (⊤ ⊓ (N₁ ⊓ N₂)) (⊤ ⊓ N₁) (⊤ ⊓ N₂)) (c : Cpl N₁ N₂ Y)
    (hc : c.IsFaithful)
    (hiii : ∀ w₁ ∈ CosetGeom.nbrs c.xv \ {c.lv}, ∀ w₂ ∈ CosetGeom.nbrs c.xv \ {c.lv},
      ∃ g ∈ oPPrime p (stv c c.xv ⊓ stv c c.lv), g • w₁ = w₂)
    (hiv : ∀ g ∈ oPPrime p (stv c c.xv ⊓ stv c c.lv), ∀ w ∈ CosetGeom.nbrs c.xv \ {c.lv},
      g • w = w → g ∈ Qu p ⊤ c c.xv) :
    (∀ a b : E, a ∈ N₁ → b ∈ N₁ → a ∉ N₂ → b ∉ N₂ →
      ∃ s ∈ pCoreOf p (⊤ ⊓ (N₁ ⊓ N₂)), b⁻¹ * s * a ∈ N₂) ∧
    (∀ a : E, a ∈ N₁ → a ∉ N₂ → ∀ s ∈ pCoreOf p (⊤ ⊓ (N₁ ⊓ N₂)), a⁻¹ * s * a ∈ N₂ →
      s ∈ pCoreOf p (⊤ ⊓ N₁)) := by
  have hne : ∀ X : (RankTwoAmalgam.ofSubgroups N₁ N₂).G1, burnsideF4k_val1 N₁ N₂ X ∉ N₂ →
      f1 (c := c) X • c.lv ∈ CosetGeom.nbrs c.xv \ {c.lv} := fun X hX =>
    ⟨burnsideF4k_adj_f1_lv c X, fun h => hX
      ((burnsideF4k_f1_fix_lv_iff c hc X).mp (Set.mem_singleton_iff.mp h))⟩
  refine ⟨?_, ?_⟩
  · intro a b ha hb haN hbN
    let A : (RankTwoAmalgam.ofSubgroups N₁ N₂).G1 := (⟨a, ha⟩ : ↥N₁)
    let B : (RankTwoAmalgam.ofSubgroups N₁ N₂).G1 := (⟨b, hb⟩ : ↥N₁)
    obtain ⟨g, hg, hgw⟩ := hiii _ (hne A haN) _ (hne B hbN)
    obtain ⟨hgx, hgl⟩ := Subgroup.mem_inf.mp (burnsideF4k_oPPrime_le p _ hg)
    obtain ⟨d, rfl⟩ := burnsideF4k_stv_inf_le_range_Phi c hc (Subgroup.mem_inf.mpr ⟨hgx, hgl⟩)
    refine ⟨burnsideF4k_val12 N₁ N₂ d, burnsideF4k_oPPrime_borel hp hP c hc d hg, ?_⟩
    have e : f1 (c := c) ((RankTwoAmalgam.ofSubgroups N₁ N₂).α1 d) * f1 (c := c) A =
        f1 (c := c) B * f1 (c := c) (B⁻¹ * (RankTwoAmalgam.ofSubgroups N₁ N₂).α1 d * A) := by
      simp only [map_mul, map_inv]
      group
    have h1 : f1 (c := c) B • (f1 (c := c) (B⁻¹ * (RankTwoAmalgam.ofSubgroups N₁ N₂).α1 d * A) •
        c.lv) = f1 (c := c) B • c.lv := by
      rw [← mul_smul, ← e, mul_smul]
      exact hgw
    have h2 := MulAction.injective (f1 (c := c) B) h1
    exact (burnsideF4k_f1_fix_lv_iff c hc _).mp h2
  · intro a ha haN s hs has
    let A : (RankTwoAmalgam.ofSubgroups N₁ N₂).G1 := (⟨a, ha⟩ : ↥N₁)
    have hsB : s ∈ ⊤ ⊓ (N₁ ⊓ N₂) := CFSG.LieType.BorelTits.pCoreOf_le p _ hs
    let d : (RankTwoAmalgam.ofSubgroups N₁ N₂).G12 := (⟨s, (Subgroup.mem_inf.mp hsB).2⟩ : ↥(N₁ ⊓ N₂))
    have hg : burnsideF4k_Phi c d ∈ oPPrime p (stv c c.xv ⊓ stv c c.lv) :=
      burnsideF4k_pCoreOf_borel_mem_oPPrime hp c hc d hs
    have hfix' : f1 (c := c) (A⁻¹ * (RankTwoAmalgam.ofSubgroups N₁ N₂).α1 d * A) • c.lv = c.lv :=
      (burnsideF4k_f1_fix_lv_iff c hc _).mpr has
    have hfix : burnsideF4k_Phi c d • (f1 (c := c) A • c.lv) = f1 (c := c) A • c.lv := by
      have e : f1 (c := c) ((RankTwoAmalgam.ofSubgroups N₁ N₂).α1 d) * f1 (c := c) A =
          f1 (c := c) A * f1 (c := c) (A⁻¹ * (RankTwoAmalgam.ofSubgroups N₁ N₂).α1 d * A) := by
        simp only [map_mul, map_inv]
        group
      show f1 (c := c) ((RankTwoAmalgam.ofSubgroups N₁ N₂).α1 d) • (f1 (c := c) A • c.lv) = _
      rw [← mul_smul, e, mul_smul, hfix']
    have hQ := hiv _ hg _ (hne A haN) hfix
    rw [burnsideF4k_Qu_xv p Subgroup.normal_top c] at hQ
    obtain ⟨a', ha', hfa'⟩ := (burnsideF4k_mem_Qx c).mp hQ
    have h3 : a' = (RankTwoAmalgam.ofSubgroups N₁ N₂).α1 d := f1_injective c hc hfa'
    subst h3
    exact ha'

end RegSix2

section RestrictHyp

open CFSG.ASVolI.ChF CFSG.Blueprint CFSG.Blueprint.Chevalley

theorem burnsideF4k_isGenLie_congr {H H' : Type} [Group H] [Group H'] (e : H ≃* H') {κ : GLKind}
    {p f : ℕ} (h : IsGenLie H κ p f) : IsGenLie H' κ p f := by
  cases κ
  · obtain ⟨h1, h2, K, fK, finK, hc, ⟨e'⟩⟩ := h
    exact And.intro h1 (And.intro h2 (Exists.intro K (Exists.intro fK (Exists.intro finK
      (And.intro hc ⟨e.symm.trans e'⟩)))))
  · obtain ⟨h1, h2, K, fK, finK, hc, ⟨e'⟩⟩ := h
    exact And.intro h1 (And.intro h2 (Exists.intro K (Exists.intro fK (Exists.intro finK
      (And.intro hc ⟨e.symm.trans e'⟩)))))
  · obtain ⟨h1, h2, K, fK, finK, hc, ⟨e'⟩⟩ := h
    exact And.intro h1 (And.intro h2 (Exists.intro K (Exists.intro fK (Exists.intro finK
      (And.intro hc ⟨e.symm.trans e'⟩)))))
  · obtain ⟨h1, h2, K, fK, finK, hc, σ, hσ, ⟨e'⟩⟩ := h
    exact And.intro h1 (And.intro h2 (Exists.intro K (Exists.intro fK (Exists.intro finK
      (And.intro hc (Exists.intro σ (And.intro hσ ⟨e.symm.trans e'⟩)))))))
  · obtain ⟨h1, h2, h3 | h3⟩ := h
    · obtain ⟨h4, K, fK, finK, hc, ⟨e'⟩⟩ := h3
      exact And.intro h1 (And.intro h2 (Or.inl (And.intro h4 (Exists.intro K (Exists.intro fK
        (Exists.intro finK (And.intro hc ⟨e.symm.trans e'⟩)))))))
    · obtain ⟨h4, h5, a, ha, K, fK, finK, hc, ⟨e'⟩⟩ := h3
      exact And.intro h1 (And.intro h2 (Or.inr (And.intro h4 (And.intro h5 (Exists.intro a
        (And.intro ha (Exists.intro K (Exists.intro fK (Exists.intro finK
          (And.intro hc ⟨e.symm.trans e'⟩))))))))))
  · obtain ⟨h1, h2, K, fK, finK, hc, ⟨e'⟩⟩ := h
    exact And.intro h1 (And.intro h2 (Exists.intro K (Exists.intro fK (Exists.intro finK
      (And.intro hc ⟨e.symm.trans e'⟩)))))
  · obtain ⟨h1, h2, K, fK, finK, hc, ⟨e'⟩⟩ := h
    exact And.intro h1 (And.intro h2 (Exists.intro K (Exists.intro fK (Exists.intro finK
      (And.intro hc ⟨e.symm.trans e'⟩)))))
  · obtain ⟨h1, h2, K, fK, finK, hc, ⟨e'⟩⟩ := h
    exact And.intro h1 (And.intro h2 (Exists.intro K (Exists.intro fK (Exists.intro finK
      (And.intro hc ⟨e.symm.trans e'⟩)))))
  · obtain ⟨h1, h2, h3, a, ha, K, fK, finK, hc, ⟨e'⟩⟩ := h
    exact And.intro h1 (And.intro h2 (And.intro h3 (Exists.intro a (And.intro ha
      (Exists.intro K (Exists.intro fK (Exists.intro finK (And.intro hc ⟨e.symm.trans e'⟩))))))))

end RestrictHyp

section RestrictChart

open CFSG.ASVolI.ChF

theorem burnsideF4k_map_trans {A B C : Type} [Group A] [Group B] [Group C] (f : A ≃* B) (e : B ≃* C)
    (X : Subgroup A) : X.map (f.trans e).toMonoidHom = (X.map f.toMonoidHom).map e.toMonoidHom := by
  rw [Subgroup.map_map]
  rfl

@[expose] def burnsideF4k_markingMap {kind : ClassicalRoots.Kind} {p exponent : ℕ} {H H' : Type}
    [Group H] [Group H'] (m : ClassicalRoots.Marking kind p exponent H) (e : H ≃* H') :
    ClassicalRoots.Marking kind p exponent H' :=
  { m with identification := m.identification.trans e }

theorem burnsideF4k_markingMap_borel {kind : ClassicalRoots.Kind} {p exponent : ℕ} {H H' : Type}
    [Group H] [Group H'] (m : ClassicalRoots.Marking kind p exponent H) (e : H ≃* H') :
    (burnsideF4k_markingMap m e).borel = m.borel.map e.toMonoidHom := by
  unfold ClassicalRoots.Marking.borel ClassicalRoots.Marking.transport
  rw [Subgroup.map_map]
  rfl

theorem burnsideF4k_markingMap_parabolic {kind : ClassicalRoots.Kind} {p exponent : ℕ} {H H' : Type}
    [Group H] [Group H'] (m : ClassicalRoots.Marking kind p exponent H) (e : H ≃* H') (b : Bool) :
    (burnsideF4k_markingMap m e).parabolic b = (m.parabolic b).map e.toMonoidHom := by
  unfold ClassicalRoots.Marking.parabolic ClassicalRoots.Marking.transport
  rw [Subgroup.map_map]
  rfl

theorem burnsideF4k_markingMap_root {kind : ClassicalRoots.Kind} {p exponent : ℕ} {H H' : Type}
    [Group H] [Group H'] (m : ClassicalRoots.Marking kind p exponent H) (e : H ≃* H')
    (r : ClassicalRoots.PositiveRoot) (b : Bool) :
    (burnsideF4k_markingMap m e).root r b = (m.root r b).map e.toMonoidHom := by
  unfold ClassicalRoots.Marking.root ClassicalRoots.Marking.transport
  rw [Subgroup.map_map]
  rfl

theorem burnsideF4k_fullImage_trans {K : Type} [Field K] [Finite K] {H H' : Type} [Group H] [Group H']
    (m : G2Native.FullModel K ≃* H) (e : H ≃* H') (X : Subgroup (G2Native.Parent K)) :
    G2Native.fullImage K (m.trans e) X = (G2Native.fullImage K m X).map e.toMonoidHom :=
  burnsideF4k_map_trans _ _ _

theorem burnsideF4k_smallImage_trans {K : Type} [Field K] [Finite K] {H H' : Type} [Group H]
    [Group H'] (m : G2Native.SmallModel K ≃* H) (e : H ≃* H') (X : Subgroup (G2Native.Parent K)) :
    G2Native.smallImage K (m.trans e) X = (G2Native.smallImage K m X).map e.toMonoidHom :=
  burnsideF4k_map_trans _ _ _

variable {E : Type} [Group E] {Gp : Subgroup E}

theorem burnsideF4k_restrict_eq (Y : Subgroup ↥Gp) (Z : Subgroup E) (hZ : Z = Y.map Gp.subtype) :
    Z.subgroupOf Gp =
      (Y.map (Subgroup.topEquiv (G := ↥Gp)).symm.toMonoidHom).map (⊤ : Subgroup ↥Gp).subtype := by
  rw [hZ, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective Gp.subtype_injective,
    Subgroup.map_map]
  have : ((⊤ : Subgroup ↥Gp).subtype.comp (Subgroup.topEquiv (G := ↥Gp)).symm.toMonoidHom) =
      MonoidHom.id ↥Gp := by
    ext x
    rfl
  rw [this, Subgroup.map_id]

end RestrictChart

section RestrictChart2

open CFSG.ASVolI.ChF

variable {E : Type} [Group E] {Gp : Subgroup E}

theorem burnsideF4k_chart_restrict {κ : GLKind} {p f : ℕ} {M₁ M₂ : Subgroup E}
    (chart : NativeChart κ p f Gp) (hm : chart.Matches M₁ M₂) :
    ∃ chart' : NativeChart κ p f (⊤ : Subgroup ↥Gp),
      chart'.Matches ((Gp ⊓ M₁).subgroupOf Gp) ((Gp ⊓ M₂).subgroupOf Gp) := by
  obtain ⟨hb, hpt, hl⟩ := hm
  let e : ↥Gp ≃* ↥(⊤ : Subgroup ↥Gp) := (Subgroup.topEquiv (G := ↥Gp)).symm
  have hm1 : (⊤ : Subgroup ↥Gp) ⊓ ((Gp ⊓ M₁).subgroupOf Gp ⊓ (Gp ⊓ M₂).subgroupOf Gp) =
      chart.borel.subgroupOf Gp := by
    ext x
    have hx := x.2
    simp only [Subgroup.mem_inf, Subgroup.mem_top, Subgroup.mem_subgroupOf, true_and]
    rw [← hb]
    simp only [Subgroup.mem_inf]
    tauto
  have hm2 : (⊤ : Subgroup ↥Gp) ⊓ (Gp ⊓ M₁).subgroupOf Gp = chart.points.subgroupOf Gp := by
    rw [top_inf_eq, ← hpt]
  have hm3 : (⊤ : Subgroup ↥Gp) ⊓ (Gp ⊓ M₂).subgroupOf Gp = chart.lines.subgroupOf Gp := by
    rw [top_inf_eq, ← hl]
  have hmatch := And.intro hm1 (And.intro hm2 hm3)
  rcases chart.coordinates with
    ⟨c, hk, marking, h1, h2, h3, h4, h5⟩ |
    ⟨hk, hp, hd, K, fK, finK, card, marking, h1, h2, h3, h4, h5⟩ |
    ⟨hk, hp, hd, K, fK, finK, card, marking, h1, h2, h3, h4, h5⟩ |
    ⟨hk, hp, hd, K, fK, finK, sigma, scope, marking, h1, h2, h3, h4, h5⟩ |
    ⟨hp, exponent, K, fK, finK, charK, scope,
      ⟨hk, hd, marking, h1, h2, h3, h4, h5⟩ | ⟨hk, hd, he, marking, h1, h2, h3, h4, h5⟩⟩
  · refine ⟨⟨chart.borel.subgroupOf Gp, chart.points.subgroupOf Gp, chart.lines.subgroupOf Gp,
      chart.longRoot.subgroupOf Gp, chart.shortRoot.subgroupOf Gp,
      Or.inl ⟨c, hk, burnsideF4k_markingMap marking e, ?_, ?_, ?_, ?_, ?_⟩⟩, hmatch⟩
    · rw [burnsideF4k_markingMap_borel]; exact burnsideF4k_restrict_eq _ _ h1
    · rw [burnsideF4k_markingMap_parabolic]; exact burnsideF4k_restrict_eq _ _ h2
    · rw [burnsideF4k_markingMap_parabolic]; exact burnsideF4k_restrict_eq _ _ h3
    · rw [burnsideF4k_markingMap_root]; exact burnsideF4k_restrict_eq _ _ h4
    · rw [burnsideF4k_markingMap_root]; exact burnsideF4k_restrict_eq _ _ h5
  · refine ⟨⟨chart.borel.subgroupOf Gp, chart.points.subgroupOf Gp, chart.lines.subgroupOf Gp,
      chart.longRoot.subgroupOf Gp, chart.shortRoot.subgroupOf Gp,
      Or.inr (Or.inl ⟨hk, hp, hd, K, fK, finK, card, marking.trans e, ?_, ?_, ?_, ?_, ?_⟩)⟩, hmatch⟩
    · rw [burnsideF4k_fullImage_trans]; exact burnsideF4k_restrict_eq _ _ h1
    · rw [burnsideF4k_fullImage_trans]; exact burnsideF4k_restrict_eq _ _ h2
    · rw [burnsideF4k_fullImage_trans]; exact burnsideF4k_restrict_eq _ _ h3
    · rw [burnsideF4k_fullImage_trans]; exact burnsideF4k_restrict_eq _ _ h4
    · rw [burnsideF4k_fullImage_trans]; exact burnsideF4k_restrict_eq _ _ h5
  · refine ⟨⟨chart.borel.subgroupOf Gp, chart.points.subgroupOf Gp, chart.lines.subgroupOf Gp,
      chart.longRoot.subgroupOf Gp, chart.shortRoot.subgroupOf Gp,
      Or.inr (Or.inr (Or.inl ⟨hk, hp, hd, K, fK, finK, card, marking.trans e, ?_, ?_, ?_, ?_, ?_⟩))⟩,
      hmatch⟩
    · rw [burnsideF4k_smallImage_trans]; exact burnsideF4k_restrict_eq _ _ h1
    · rw [burnsideF4k_smallImage_trans]; exact burnsideF4k_restrict_eq _ _ h2
    · rw [burnsideF4k_smallImage_trans]; exact burnsideF4k_restrict_eq _ _ h3
    · rw [burnsideF4k_smallImage_trans]; exact burnsideF4k_restrict_eq _ _ h4
    · rw [burnsideF4k_smallImage_trans]; exact burnsideF4k_restrict_eq _ _ h5
  · refine ⟨⟨chart.borel.subgroupOf Gp, chart.points.subgroupOf Gp, chart.lines.subgroupOf Gp,
      chart.longRoot.subgroupOf Gp, chart.shortRoot.subgroupOf Gp,
      Or.inr (Or.inr (Or.inr (Or.inl ⟨hk, hp, hd, K, fK, finK, sigma, scope, marking.trans e,
        ?_, ?_, ?_, ?_, ?_⟩)))⟩, hmatch⟩
    · rw [burnsideF4k_map_trans]; exact burnsideF4k_restrict_eq _ _ h1
    · rw [burnsideF4k_map_trans]; exact burnsideF4k_restrict_eq _ _ h2
    · rw [burnsideF4k_map_trans]; exact burnsideF4k_restrict_eq _ _ h3
    · rw [burnsideF4k_map_trans]; exact burnsideF4k_restrict_eq _ _ h4
    · rw [burnsideF4k_map_trans]; exact burnsideF4k_restrict_eq _ _ h5
  · refine ⟨⟨chart.borel.subgroupOf Gp, chart.points.subgroupOf Gp, chart.lines.subgroupOf Gp,
      chart.longRoot.subgroupOf Gp, chart.shortRoot.subgroupOf Gp,
      Or.inr (Or.inr (Or.inr (Or.inr ⟨hp, exponent, K, fK, finK, charK, scope,
        Or.inl ⟨hk, hd, marking.trans e, ?_, ?_, ?_, ?_, ?_⟩⟩)))⟩, hmatch⟩
    · rw [burnsideF4k_map_trans]; exact burnsideF4k_restrict_eq _ _ h1
    · rw [burnsideF4k_map_trans]; exact burnsideF4k_restrict_eq _ _ h2
    · rw [burnsideF4k_map_trans]; exact burnsideF4k_restrict_eq _ _ h3
    · rw [burnsideF4k_map_trans]; exact burnsideF4k_restrict_eq _ _ h4
    · rw [burnsideF4k_map_trans]; exact burnsideF4k_restrict_eq _ _ h5
  · refine ⟨⟨chart.borel.subgroupOf Gp, chart.points.subgroupOf Gp, chart.lines.subgroupOf Gp,
      chart.longRoot.subgroupOf Gp, chart.shortRoot.subgroupOf Gp,
      Or.inr (Or.inr (Or.inr (Or.inr ⟨hp, exponent, K, fK, finK, charK, scope,
        Or.inr ⟨hk, hd, he, marking.trans e, ?_, ?_, ?_, ?_, ?_⟩⟩)))⟩, hmatch⟩
    · rw [burnsideF4k_map_trans]; exact burnsideF4k_restrict_eq _ _ h1
    · rw [burnsideF4k_map_trans]; exact burnsideF4k_restrict_eq _ _ h2
    · rw [burnsideF4k_map_trans]; exact burnsideF4k_restrict_eq _ _ h3
    · rw [burnsideF4k_map_trans]; exact burnsideF4k_restrict_eq _ _ h4
    · rw [burnsideF4k_map_trans]; exact burnsideF4k_restrict_eq _ _ h5

end RestrictChart2

section RestrictHyp2

open CFSG.ASVolI.ChF

theorem burnsideF4k_parabolics_gen {E : Type} [Group E] {p : ℕ} {H B P₁ P₂ : Subgroup E}
    (hP : IsLieParabolics p H B P₁ P₂) : P₁ ⊔ P₂ = H := by
  obtain ⟨-, hne, -, hmax⟩ := hP
  obtain ⟨-, hP1H, -, hP1max⟩ := (hmax P₁).mpr (Or.inl rfl)
  obtain ⟨-, hP2H, -, hP2max⟩ := (hmax P₂).mpr (Or.inr rfl)
  by_contra hR
  have hRle : P₁ ⊔ P₂ ≤ H := sup_le hP1H hP2H
  have h1 : P₁ ⊔ P₂ = P₁ := by
    by_contra h
    exact hR (hP1max _ (lt_of_le_of_ne le_sup_left (Ne.symm h)) hRle)
  have h2 : P₁ ⊔ P₂ = P₂ := by
    by_contra h
    exact hR (hP2max _ (lt_of_le_of_ne le_sup_right (Ne.symm h)) hRle)
  exact hne (h1.symm.trans h2)

theorem burnsideF4k_mem_normalizer_subgroupOf {E : Type} [Group E] {Gp X : Subgroup E} (hX : X ≤ Gp)
    (g : ↥Gp) : g ∈ Subgroup.normalizer ((X.subgroupOf Gp : Subgroup ↥Gp) : Set ↥Gp) ↔
      (g : E) ∈ Subgroup.normalizer (X : Set E) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h x
    by_cases hx : x ∈ Gp
    · have := h ⟨x, hx⟩
      simpa [Subgroup.mem_subgroupOf] using this
    · constructor
      · intro hxX
        exact absurd (hX hxX) hx
      · intro hgx
        exfalso
        apply hx
        have h1 : (g : E)⁻¹ * ((g : E) * x * (g : E)⁻¹) * (g : E) ∈ Gp :=
          Gp.mul_mem (Gp.mul_mem (Gp.inv_mem g.2) (hX hgx)) g.2
        simpa [mul_assoc] using h1
  · intro h x
    have := h (x : E)
    simpa [Subgroup.mem_subgroupOf] using this

theorem burnsideF4k_restrict (hcompat : NativeChartCompatibilityGoal) {κ : GLKind} {p f : ℕ}
    {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E} (hyp : HypF_4_4 κ p f Gp M₁ M₂) :
    HypF_4_4 κ p f (⊤ : Subgroup ↥Gp) ((Gp ⊓ M₁).subgroupOf Gp) ((Gp ⊓ M₂).subgroupOf Gp) := by
  haveI := hyp.finite
  have hP := burnsideF4k_parabolics hcompat hyp
  obtain ⟨chart, hchart⟩ := hyp.lie_amalgam
  obtain ⟨chart', hchart'⟩ := burnsideF4k_chart_restrict chart hchart
  have hBB : (⊤ : Subgroup ↥Gp) ⊓ ((Gp ⊓ M₁).subgroupOf Gp ⊓ (Gp ⊓ M₂).subgroupOf Gp) =
      (Gp ⊓ (M₁ ⊓ M₂)).subgroupOf Gp := by
    ext x
    have hx := x.2
    simp only [Subgroup.mem_inf, Subgroup.mem_top, Subgroup.mem_subgroupOf, true_and]
    tauto
  refine ⟨⟨inferInstance, burnsideF4k_isGenLie_congr (Subgroup.topEquiv (G := ↥Gp)).symm hyp.model,
    inferInstance, ?_, ?_, ⟨chart', hchart'⟩, fun e => ⟨e, Subgroup.mem_top _, 1,
      Subgroup.one_mem _, (mul_one e).symm⟩, ?_⟩, fun _ => rfl⟩
  ·
    rw [eq_bot_iff]
    intro z hz
    have h1 : (z : E) ∈ Subgroup.centralizer (Gp : Set E) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      have := (Subgroup.mem_centralizer_iff.mp hz) ⟨g, hg⟩ (Subgroup.mem_top _)
      exact congrArg Subtype.val this
    rw [hyp.centralizer_trivial] at h1
    exact Subtype.ext (Subgroup.mem_bot.mp h1)
  ·
    apply Subgroup.map_injective Gp.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le inf_le_left,
      Subgroup.map_subgroupOf_eq_of_le inf_le_left, burnsideF4k_parabolics_gen hP, Subgroup.map_top,
      Subgroup.range_subtype]
  ·
    intro g hg
    rw [hBB, burnsideF4k_mem_normalizer_subgroupOf inf_le_left] at hg
    rw [top_inf_eq, burnsideF4k_mem_normalizer_subgroupOf inf_le_left]
    exact hyp.dynkin g hg

end RestrictHyp2

section RegFinal

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
  CFSG.ASVolI.ChF

theorem burnsideF4k_split_aux {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hs : ∀ e : E, ∃ n ∈ Gp, ∃ h ∈ M₁ ⊓ M₂, e = n * h) {a : E} (ha : a ∈ M₁) (haM : a ∉ M₂) :
    ∃ n ∈ Gp ⊓ M₁, ∃ h ∈ M₁ ⊓ M₂, n ∉ M₂ ∧ a = n * h := by
  obtain ⟨n, hn, h, hh, rfl⟩ := hs a
  refine ⟨n, ⟨hn, ?_⟩, h, hh, fun hn2 => haM (M₂.mul_mem hn2 (Subgroup.mem_inf.mp hh).2), rfl⟩
  have := M₁.mul_mem ha (M₁.inv_mem (Subgroup.mem_inf.mp hh).1)
  simpa using this

theorem burnsideF4k_Reg_of_F45 (h5 : F_4_5) (hcompat : NativeChartCompatibilityGoal) :
    burnsideF4k_Reg := by
  intro κ p f E _ Gp M₁ M₂ hyp
  haveI := hyp.finite
  have hp := burnsideF4a_prime_of_isGenLie hyp.model
  have hyp' := burnsideF4k_restrict hcompat hyp
  have hP' := burnsideF4k_parabolics hcompat hyp'
  have h6 := ((h5 κ p f ↥Gp ⊤ _ _ hyp' (incl _ _) rfl).2.2.2.2.2.1 rfl) (incl _ _).xv
    (incl _ _).lv CosetGeom.adj_γ₀_γ₁
  obtain ⟨hreg1, hreg2⟩ := burnsideF4k_reg_of_six hp hP' (incl _ _) (incl_faithful _ _)
    h6.2.2.1 h6.2.2.2.1
  have hX : Gp ⊓ (M₁ ⊓ M₂) ≤ Gp := inf_le_left
  have hX1 : Gp ⊓ M₁ ≤ Gp := inf_le_left
  have hBB : (⊤ : Subgroup ↥Gp) ⊓ ((Gp ⊓ M₁).subgroupOf Gp ⊓ (Gp ⊓ M₂).subgroupOf Gp) =
      (Gp ⊓ (M₁ ⊓ M₂)).subgroupOf Gp := by
    ext x
    have hx := x.2
    simp only [Subgroup.mem_inf, Subgroup.mem_top, Subgroup.mem_subgroupOf, true_and]
    tauto
  have hpB : ∀ s : ↥Gp, s ∈ pCoreOf p ((⊤ : Subgroup ↥Gp) ⊓ ((Gp ⊓ M₁).subgroupOf Gp ⊓
      (Gp ⊓ M₂).subgroupOf Gp)) ↔ (s : E) ∈ pCoreOf p (Gp ⊓ (M₁ ⊓ M₂)) := by
    intro s
    rw [hBB, ← burnsideF4k_pCoreOf_subgroupOf p hX]
    exact (Subgroup.mem_map_iff_mem Gp.subtype_injective).symm
  have hpP : ∀ s : ↥Gp, s ∈ pCoreOf p ((⊤ : Subgroup ↥Gp) ⊓ (Gp ⊓ M₁).subgroupOf Gp) ↔
      (s : E) ∈ pCoreOf p (Gp ⊓ M₁) := by
    intro s
    rw [top_inf_eq, ← burnsideF4k_pCoreOf_subgroupOf p hX1]
    exact (Subgroup.mem_map_iff_mem Gp.subtype_injective).symm
  refine ⟨?_, ?_⟩
  · intro a b ha hb haM hbM
    obtain ⟨na, hna, ha', hha, hna2, rfl⟩ := burnsideF4k_split_aux hyp.split ha haM
    obtain ⟨nb, hnb, hb', hhb, hnb2, rfl⟩ := burnsideF4k_split_aux hyp.split hb hbM
    obtain ⟨s', hs', hmem⟩ := hreg1 ⟨na, hna.1⟩ ⟨nb, hnb.1⟩ (Subgroup.mem_subgroupOf.mpr hna)
      (Subgroup.mem_subgroupOf.mpr hnb)
      (fun h => hna2 (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp h)).2)
      (fun h => hnb2 (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp h)).2)
    refine ⟨(s' : E), (hpB s').mp hs', ?_⟩
    have h2 : nb⁻¹ * (s' : E) * na ∈ M₂ := (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hmem)).2
    have e : (nb * hb')⁻¹ * (s' : E) * (na * ha') = hb'⁻¹ * (nb⁻¹ * (s' : E) * na) * ha' := by
      group
    rw [e]
    exact M₂.mul_mem (M₂.mul_mem (M₂.inv_mem (Subgroup.mem_inf.mp hhb).2) h2)
      (Subgroup.mem_inf.mp hha).2
  · intro a ha haM s hs has
    obtain ⟨na, hna, ha', hha, hna2, rfl⟩ := burnsideF4k_split_aux hyp.split ha haM
    have hsG : s ∈ Gp := (Subgroup.mem_inf.mp (CFSG.LieType.BorelTits.pCoreOf_le p _ hs)).1
    have hs' : (⟨s, hsG⟩ : ↥Gp) ∈ pCoreOf p ((⊤ : Subgroup ↥Gp) ⊓ ((Gp ⊓ M₁).subgroupOf Gp ⊓
        (Gp ⊓ M₂).subgroupOf Gp)) := (hpB _).mpr hs
    have h2 : na⁻¹ * s * na ∈ M₂ := by
      have e : na⁻¹ * s * na = ha' * ((na * ha')⁻¹ * s * (na * ha')) * ha'⁻¹ := by group
      rw [e]
      exact M₂.mul_mem (M₂.mul_mem (Subgroup.mem_inf.mp hha).2 has)
        (M₂.inv_mem (Subgroup.mem_inf.mp hha).2)
    have h3 := hreg2 ⟨na, hna.1⟩ (Subgroup.mem_subgroupOf.mpr hna)
      (fun h => hna2 (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp h)).2) ⟨s, hsG⟩ hs'
      (Subgroup.mem_subgroupOf.mpr ⟨Gp.mul_mem (Gp.mul_mem (Gp.inv_mem hna.1) hsG) hna.1, h2⟩)
    exact (hpP _).mp h3

end RegFinal

open CFSG.ASVolI.ChF in
theorem burnsideF4k_F416_of_F45 (hF : F_4_6) (h5 : F_4_5) (hcompat : NativeChartCompatibilityGoal) :
    F_4_16 :=
  burnsideF4k_F416 hF hcompat (burnsideF4k_Reg_of_F45 h5 hcompat)

end CFSG.ASVolI
