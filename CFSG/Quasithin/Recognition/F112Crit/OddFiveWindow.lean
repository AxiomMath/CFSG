module

public import CFSG.Quasithin.Recognition.F112Crit.TorusCompSmul
public import CFSG.Quasithin.Recognition.F112Crit.Theorem75
public import CFSG.Quasithin.Recognition.F112Crit.CoprimeCentralizer

public section

namespace CFSG.Quasithin.F112Crit

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open Subgroup
open scoped Pointwise

open CosetGeom (graph stab ballStab nbrs vtype γ₀ Vv)

variable {G : Type} [Group G] [Finite G] {G₀ G₁ G₂ T Z : Subgroup G}

theorem Vv_le_stab_of_dist_le (hc : CritAmalgam G₀ G₁ G₂ T Z) {γ x : CosetGeom G₀ G₁ G₂}
    (hγ : vtype γ = false) (hd : CosetGeom.dist γ x ≤ critB G₀ G₁ G₂ Z) : Vv Z γ ≤ stab x := by
  have hG := hc.amalgam.gen
  have hb := two_le_critB hc
  obtain ⟨μ, hμx, hγμ⟩ : ∃ μ, (graph G₀ G₁ G₂).Adj x μ ∧
      CosetGeom.dist γ μ < critB G₀ G₁ G₂ Z := by
    rcases Nat.eq_zero_or_pos (CosetGeom.dist γ x) with h0 | hpos
    · obtain rfl := (CosetGeom.dist_eq_zero_iff hG).mp h0
      obtain ⟨μ, hμ⟩ := CosetGeom.exists_adj γ
      exact ⟨μ, hμ, by rw [CosetGeom.dist_eq_one_iff_adj.mpr hμ]; omega⟩
    · obtain ⟨μ, hμ, hdμ⟩ := CosetGeom.exists_adj_dist_eq hG
        (show CosetGeom.dist γ x = (CosetGeom.dist γ x - 1) + 1 by omega)
      exact ⟨μ, hμ, by omega⟩
  refine (lemma72 hc hγ hγμ).trans ((CosetGeom.pCoreOf_stab_le_ballStab_one hc.amalgam μ).trans
    (CosetGeom.ballStab_le_stab_of_dist_le ?_))
  rw [CosetGeom.dist_comm]
  exact (CosetGeom.dist_eq_one_iff_adj.mpr hμx).le

private theorem dist_vert_le (hG : G₀ = G₁ ⊔ G₂) {s : ℕ}
    (P : F6.GoldAmL3T.Arc (graph G₀ G₁ G₂) s) (j : ℕ) :
    ∀ i, j ≤ i → i ≤ s → CosetGeom.dist (P.vert j) (P.vert i) ≤ i - j := by
  intro i
  induction i with
  | zero =>
    intro hj _
    obtain rfl : j = 0 := by omega
    rw [CosetGeom.dist_self]
  | succ k ih =>
    intro hj hk
    rcases Nat.eq_or_lt_of_le hj with h | h
    · rw [h, CosetGeom.dist_self]
      omega
    · have h1 := ih (by omega) (by omega)
      have h2 : CosetGeom.dist (P.vert k) (P.vert (k + 1)) = 1 :=
        CosetGeom.dist_eq_one_iff_adj.mpr (P.adj k (by omega))
      have h3 := CosetGeom.dist_triangle hG (P.vert j) (P.vert k) (P.vert (k + 1))
      omega

private theorem dist_vert_five_le (hG : G₀ = G₁ ⊔ G₂)
    (P : F6.GoldAmL3T.Arc (graph G₀ G₁ G₂) 10) {i : ℕ} (hi : i ≤ 10) :
    CosetGeom.dist (P.vert 5) (P.vert i) ≤ 5 := by
  rcases le_total 5 i with h | h
  · have := dist_vert_le hG P 5 i h hi
    omega
  · have := dist_vert_le hG P i 5 h (by omega)
    rw [CosetGeom.dist_comm]
    omega

private theorem exists_ne_nbr {V : Type} {Γ : SimpleGraph V} {Δ : Set V} {sm : V → Prop}
    (h : Fan86.Tutte.SubdivCubic Γ Δ sm) {e a : V} (he : e ∈ Δ) (hesm : ¬ sm e) (ha : a ∈ Δ)
    (hea : Γ.Adj e a) : ∃ b, b ∈ Δ ∧ Γ.Adj e b ∧ b ≠ a := by
  obtain ⟨y₁, y₂, hne, hy⟩ := h.two e he hesm
  rcases (hy a).1 ⟨ha, hea⟩ with rfl | rfl
  · exact ⟨y₂, ((hy y₂).2 (Or.inr rfl)).1, ((hy y₂).2 (Or.inr rfl)).2, hne.symm⟩
  · exact ⟨y₁, ((hy y₁).2 (Or.inl rfl)).1, ((hy y₁).2 (Or.inl rfl)).2, hne⟩

theorem Vv_le_ballStab_of_window (hc : CritAmalgam G₀ G₁ G₂ T Z) {X : Subgroup G}
    {δ x₀ y γ : CosetGeom G₀ G₁ G₂} (hXodd : Odd (Nat.card X)) (hXδ : X ≤ stab δ)
    (hΔ : TorusGraph X δ) (hx₀ : x₀ ∈ torusComp X δ) (hx₀v : vtype x₀ = false)
    (hy : y ∈ torusComp X δ) (hyv : vtype y = true) (hdy : CosetGeom.dist x₀ y ≤ 5)
    (hγ : vtype γ = false) (hdγ : CosetGeom.dist γ x₀ + 5 ≤ critB G₀ G₁ G₂ Z) :
    Vv Z γ ≤ ballStab 1 y := by
  have hG := hc.amalgam.gen
  have hXx₀ : X ≤ stab x₀ := le_stab_of_mem_torusComp hXδ hx₀
  have hXy : X ≤ ballStab 1 y := hΔ.small_le y hy hyv
  set W : Subgroup G := ⨆ (γ' : CosetGeom G₀ G₁ G₂) (_ : vtype γ' = false ∧
    CosetGeom.dist γ' x₀ + 5 ≤ critB G₀ G₁ G₂ Z), Vv Z γ' with hWdef
  have hW2 : IsPGroup 2 W := (pCoreOf_isPGroup 2 (stab x₀)).to_le
    (iSup₂_le fun γ' hγ' => lemma72 hc hγ'.1 (by have := hγ'.2; omega))
  have hWB : W ≤ ballStab 5 x₀ := by
    refine iSup₂_le fun γ' hγ' => fun g hg => CosetGeom.mem_ballStab.mpr fun v hv => ?_
    have h := CosetGeom.dist_triangle hG γ' x₀ v
    have h' := hγ'.2
    exact Vv_le_stab_of_dist_le hc hγ'.1 (by omega) hg
  have hWy : W ≤ stab y := hWB.trans (CosetGeom.ballStab_le_stab_of_dist_le hdy)
  have hXW' : ∀ x ∈ X, conjSub x W ≤ W := by
    intro x hx
    obtain ⟨x', rfl⟩ : ∃ x' : ↥G₀, (x' : G) = x := ⟨⟨x, CosetGeom.stab_le x₀ (hXx₀ hx)⟩, rfl⟩
    have hx' : x' • x₀ = x₀ := CosetGeom.smul_eq_of_mem_stab (hXx₀ hx)
    rw [conjSub_le_iff]
    refine iSup₂_le fun γ' hγ' => ?_
    rw [le_conjSub_iff, inv_inv, ← CosetGeom.Vv_smul hc.normalizes x' γ']
    refine le_iSup₂_of_le (x' • γ') ⟨?_, ?_⟩ le_rfl
    · rw [CosetGeom.vtype_smul]
      exact hγ'.1
    · rw [← hx', CosetGeom.dist_smul]
      exact hγ'.2
  have hXW : X ≤ normalizer (W : Set G) := fun x hx =>
    F7.mem_normalizer_of_conj_le (hXW' x hx) (hXW' x⁻¹ (inv_mem hx))
  have hXB : X ≤ normalizer (ballStab 1 y : Set G) :=
    (hXy.trans (CosetGeom.ballStab_le_stab 1 y)).trans (CosetGeom.le_normalizer_ballStab 1 y)
  have hXW₁ : X ≤ normalizer ((W ⊓ ballStab 1 y : Subgroup G) : Set G) :=
    F7.le_normalizer_inf hXW hXB
  intro g hg
  have hgW : g ∈ W := (le_iSup₂_of_le γ ⟨hγ, hdγ⟩ le_rfl : Vv Z γ ≤ W) hg
  have hcomm : ∀ x ∈ X, g * x * g⁻¹ * x⁻¹ ∈ W ⊓ ballStab 1 y := by
    intro x hx
    refine mem_inf.mpr ⟨?_, ?_⟩
    · have h1 : x * g⁻¹ * x⁻¹ ∈ W := (mem_normalizer_iff.mp (hXW hx) g⁻¹).mp (inv_mem hgW)
      have e : g * x * g⁻¹ * x⁻¹ = g * (x * g⁻¹ * x⁻¹) := by group
      rw [e]
      exact mul_mem hgW h1
    · have h1 : g * x * g⁻¹ ∈ ballStab 1 y :=
        (mem_normalizer_iff.mp (CosetGeom.le_normalizer_ballStab 1 y (hWy hgW)) x).mp (hXy hx)
      exact mul_mem h1 (inv_mem (hXy hx))
  obtain ⟨n, hn, c, hcW, hcX, rfl⟩ :=
    exists_mul_centralizer_of_comm_mem hW2 hXodd inf_le_left hXW hXW₁ hgW hcomm
  refine mul_mem (mem_inf.mp hn).2 ?_
  have hcB : c ∈ ballStab 5 x₀ := hWB hcW
  have hc0 : c ∈ G₀ := CosetGeom.stab_le x₀ (CosetGeom.ballStab_le_stab 5 x₀ hcB)
  obtain ⟨c', rfl⟩ : ∃ c' : ↥G₀, (c' : G) = c := ⟨⟨c, hc0⟩, rfl⟩
  have hcn : (c' : G) ∈ normalizer (X : Set G) := by
    rw [mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rw [hcX h hh, mul_inv_cancel_right]
      exact hh
    · intro hh
      have e1 := hcX _ hh
      have e : h = (c' : G) * h * (c' : G)⁻¹ :=
        calc h = (c' : G)⁻¹ * (((c' : G) * h * (c' : G)⁻¹) * c') := by group
          _ = (c' : G)⁻¹ * (c' * ((c' : G) * h * (c' : G)⁻¹)) := by rw [← e1]
          _ = (c' : G) * h * (c' : G)⁻¹ := by group
      rw [e]
      exact hh
  have hcx₀ : c' • x₀ = x₀ := CosetGeom.smul_eq_of_mem_stab (CosetGeom.ballStab_le_stab 5 x₀ hcB)
  have hstab : ∀ m : ↥G₀, (m : G) ∈ normalizer (X : Set G) → ∀ v, v ∈ torusComp X δ →
      m • v ∈ torusComp X δ → m ∈ MulAction.stabilizer (↥G₀) (torusComp X δ) :=
    fun m hm v hv hmv => MulAction.mem_stabilizer_iff.mpr (smul_torusComp_eq hm hv hmv)
  obtain ⟨P, hP5, hP0, hPΔ⟩ := hΔ.subdiv.exists_arc hx₀ (by simp [hx₀v])
  have hPc : ∀ i, i ≤ 10 → c' • P.vert i = P.vert i := fun i hi =>
    CosetGeom.smul_eq_of_mem_stab (CosetGeom.mem_ballStab.mp hcB (P.vert i)
      (by rw [← hP5]; exact dist_vert_five_le hG P hi))
  have hfix : ∀ v ∈ torusComp X δ, c' • v = v := by
    refine Fan86.Tutte.SubdivCubic.fixes_of_fixes_arc (fun a u v => CosetGeom.smul_adj a)
      (MulAction.stabilizer (↥G₀) (torusComp X δ)) ?_ ?_ ?_ ?_ hΔ.subdiv (n := c') ?_ P hP0 hPΔ
      hPc
    · intro m hm v hv
      rw [← MulAction.mem_stabilizer_iff.mp hm]
      exact Set.smul_mem_smul_set hv
    · intro m _ v
      rw [CosetGeom.vtype_smul]
    · intro y₁ hy₁ hsm₁ y₂ hy₂ hsm₂
      obtain ⟨m, hm, hmy⟩ := hΔ.trans y₁ hy₁ hsm₁ y₂ hy₂ hsm₂
      exact ⟨m, hstab m hm y₁ hy₁ (by rw [hmy]; exact hy₂), hmy⟩
    · intro y₁ hy₁ hsm₁ e e' he he'
      obtain ⟨m, hm, hmy, hme⟩ := hΔ.loc y₁ hy₁ hsm₁ e e' he he'
      exact ⟨m, hstab m hm y₁ hy₁ (by rw [hmy]; exact hy₁), hmy, hme⟩
    · exact hstab c' hcn x₀ hx₀ (by rw [hcx₀]; exact hx₀)
  refine CosetGeom.mem_ballStab.mpr fun v hv => CosetGeom.mem_stab_of_smul_eq (hfix v ?_)
  rcases (CosetGeom.dist_le_one_iff hG).mp hv with rfl | hadj
  · exact hy
  · exact hΔ.subdiv.nbr_mem y hy hyv v hadj

theorem false_of_pCoreOf_inf_trans (hc : CritAmalgam G₀ G₁ G₂ T Z)
    (hb : Odd (critB G₀ G₁ G₂ Z)) (hb5 : 5 ≤ critB G₀ G₁ G₂ Z)
    (hU : ∀ μ : CosetGeom G₀ G₁ G₂, vtype μ = false → ∀ δ ∈ nbrs μ, ∀ ε ∈ nbrs μ, ∀ ε' ∈ nbrs μ,
      ε ≠ δ → ε' ≠ δ → ∃ g : ↥G₀, (g : G) ∈ stab μ ⊓ stab δ ∧ g • ε = ε')
    (hHall : ∀ μ δ : CosetGeom G₀ G₁ G₂, vtype μ = false → δ ∈ nbrs μ →
      ∃ X : Subgroup G, IsEdgeHall μ δ X)
    (hTor : ∀ (μ δ : CosetGeom G₀ G₁ G₂) (X : Subgroup G), vtype μ = false → δ ∈ nbrs μ →
      IsEdgeHall μ δ X → TorusGraph X δ)
    (hN : ∀ δ μ μ' : CosetGeom G₀ G₁ G₂, vtype δ = true → μ ∈ nbrs δ → μ' ∈ nbrs δ → μ ≠ μ' →
      ∀ ε ∈ nbrs μ', ∀ ε' ∈ nbrs μ', ε ≠ δ → ε' ≠ δ →
        ∃ r : ↥G₀, (r : G) ∈ pCoreOf 2 (stab δ) ⊓ pCoreOf 2 (stab μ) ∧ r • ε = ε') :
    False := by
  have hG := hc.amalgam.gen
  obtain ⟨y, hdy, hy⟩ := exists_dist_eq_critB hc
  set b := critB G₀ G₁ G₂ Z with hbdef
  obtain ⟨x₄, hyx₄, hd₄⟩ := CosetGeom.exists_adj_dist_eq hG
    (show CosetGeom.dist (γ₀ G₀ G₁ G₂) y = (b - 1) + 1 by omega)
  obtain ⟨x₃, hx₄x₃, hd₃⟩ := CosetGeom.exists_adj_dist_eq hG
    (show CosetGeom.dist (γ₀ G₀ G₁ G₂) x₄ = (b - 2) + 1 by omega)
  obtain ⟨x₂, hx₃x₂, hd₂⟩ := CosetGeom.exists_adj_dist_eq hG
    (show CosetGeom.dist (γ₀ G₀ G₁ G₂) x₃ = (b - 3) + 1 by omega)
  obtain ⟨w, hx₂w, hdw⟩ := CosetGeom.exists_adj_dist_eq hG
    (show CosetGeom.dist (γ₀ G₀ G₁ G₂) x₂ = (b - 4) + 1 by omega)
  obtain ⟨v, hwv, hdv⟩ := CosetGeom.exists_adj_dist_eq hG
    (show CosetGeom.dist (γ₀ G₀ G₁ G₂) w = (b - 5) + 1 by omega)
  have hyv : vtype y = true := by
    rw [vtype_eq_of_dist hc CosetGeom.vtype_γ₀ b y hdy]
    exact decide_eq_true hb
  have hx₄v : vtype x₄ = false := vtype_eq_false_of_mem_nbrs hyv hyx₄
  have hx₃v : vtype x₃ = true := vtype_eq_true_of_mem_nbrs hx₄v hx₄x₃
  have hx₂v : vtype x₂ = false := vtype_eq_false_of_mem_nbrs hx₃v hx₃x₂
  have hwt : vtype w = true := vtype_eq_true_of_mem_nbrs hx₂v hx₂w
  have hvv : vtype v = false := vtype_eq_false_of_mem_nbrs hwt hwv
  have hyx₃ : y ≠ x₃ := fun h => by rw [h] at hdy; omega
  have hx₄x₂ : x₄ ≠ x₂ := fun h => by rw [h] at hd₄; omega
  have hwx₃ : w ≠ x₃ := fun h => by rw [h] at hdw; omega
  obtain ⟨X₀, hX₀⟩ := hHall x₄ x₃ hx₄v hx₄x₃
  have hT₀ := hTor x₄ x₃ X₀ hx₄v hx₄x₃ hX₀
  obtain ⟨hX₀le, -, -⟩ := id hX₀
  have hX₀4 : X₀ ≤ stab x₄ := hX₀le.trans inf_le_left
  have hX₀3 : X₀ ≤ stab x₃ := hX₀le.trans inf_le_right
  have hx₄Δ₀ : x₄ ∈ torusComp X₀ x₃ :=
    mem_torusComp_of_adj hX₀3 (mem_torusComp_self X₀ x₃) hx₄x₃.symm hX₀4
  obtain ⟨y₀, hy₀Δ, hx₄y₀, hy₀x₃⟩ := exists_ne_nbr hT₀.subdiv hx₄Δ₀ (by simp [hx₄v])
    (mem_torusComp_self X₀ x₃) hx₄x₃
  obtain ⟨g, hg, hgy⟩ := hU x₄ hx₄v x₃ hx₄x₃ y₀ hx₄y₀ y hyx₄.symm hy₀x₃ hyx₃
  have hX : IsEdgeHall x₄ x₃ (conjSub (g : G) X₀) := by
    have h := hX₀.smul g
    rwa [CosetGeom.smul_eq_of_mem_stab (mem_inf.mp hg).1,
      CosetGeom.smul_eq_of_mem_stab (mem_inf.mp hg).2] at h
  set X := conjSub (g : G) X₀ with hXdef
  have hT := hTor x₄ x₃ X hx₄v hx₄x₃ hX
  obtain ⟨hXle, hXodd, -⟩ := id hX
  have hX4 : X ≤ stab x₄ := hXle.trans inf_le_left
  have hX3 : X ≤ stab x₃ := hXle.trans inf_le_right
  have hXy : X ≤ stab y := by
    rw [← hgy, CosetGeom.stab_smul]
    exact conjSub_mono _ (le_stab_of_mem_torusComp hX₀3 hy₀Δ)
  have hx₄Δ : x₄ ∈ torusComp X x₃ :=
    mem_torusComp_of_adj hX3 (mem_torusComp_self X x₃) hx₄x₃.symm hX4
  have hyΔ : y ∈ torusComp X x₃ := mem_torusComp_of_adj hX3 hx₄Δ hyx₄.symm hXy
  have hX2 : X ≤ stab x₂ := (hT.small_le x₃ (mem_torusComp_self X x₃) hx₃v).trans
    (CosetGeom.ballStab_le_stab_of_dist_le (CosetGeom.dist_eq_one_iff_adj.mpr hx₃x₂).le)
  have hx₂Δ : x₂ ∈ torusComp X x₃ :=
    mem_torusComp_of_adj hX3 (mem_torusComp_self X x₃) hx₃x₂ hX2
  obtain ⟨u, huΔ, hx₂u, hux₃⟩ := exists_ne_nbr hT.subdiv hx₂Δ (by simp [hx₂v])
    (mem_torusComp_self X x₃) hx₃x₂.symm
  have hut : vtype u = true := vtype_eq_true_of_mem_nbrs hx₂v hx₂u
  obtain ⟨r, hr, hrw⟩ := hN x₃ x₄ x₂ hx₃v hx₄x₃.symm hx₃x₂ hx₄x₂ w hx₂w u hx₂u hwx₃ hux₃
  have hry : r • y = y := CosetGeom.smul_eq_of_mem_stab
    ((CosetGeom.pCoreOf_stab_le_ballStab_one hc.amalgam x₄).trans
      (CosetGeom.ballStab_le_stab_of_dist_le (CosetGeom.dist_eq_one_iff_adj.mpr hyx₄.symm).le)
      (mem_inf.mp hr).2)
  have hux₀ : (graph G₀ G₁ G₂).Adj u (r • v) := by
    rw [← hrw]
    exact (CosetGeom.smul_adj r).mpr hwv
  have hXu : X ≤ ballStab 1 u := hT.small_le u huΔ hut
  have hXx₀ : X ≤ stab (r • v) :=
    hXu.trans (CosetGeom.ballStab_le_stab_of_dist_le (CosetGeom.dist_eq_one_iff_adj.mpr hux₀).le)
  have hx₀Δ : r • v ∈ torusComp X x₃ := mem_torusComp_of_adj hX3 huΔ hux₀ hXx₀
  have hx₀v : vtype (r • v) = false := by
    rw [CosetGeom.vtype_smul]
    exact hvv
  have hdx₀y : CosetGeom.dist (r • v) y ≤ 5 := by
    have t1 := CosetGeom.dist_triangle hG (r • v) u y
    have t2 := CosetGeom.dist_triangle hG u x₂ y
    have t3 := CosetGeom.dist_triangle hG x₂ x₃ y
    have t4 := CosetGeom.dist_triangle hG x₃ x₄ y
    have d1 : CosetGeom.dist (r • v) u = 1 := CosetGeom.dist_eq_one_iff_adj.mpr hux₀.symm
    have d2 : CosetGeom.dist u x₂ = 1 := CosetGeom.dist_eq_one_iff_adj.mpr hx₂u.symm
    have d3 : CosetGeom.dist x₂ x₃ = 1 := CosetGeom.dist_eq_one_iff_adj.mpr hx₃x₂.symm
    have d4 : CosetGeom.dist x₃ x₄ = 1 := CosetGeom.dist_eq_one_iff_adj.mpr hx₄x₃.symm
    have d5 : CosetGeom.dist x₄ y = 1 := CosetGeom.dist_eq_one_iff_adj.mpr hyx₄.symm
    omega
  have hγv : vtype (r • γ₀ G₀ G₁ G₂) = false := by
    rw [CosetGeom.vtype_smul]
    exact CosetGeom.vtype_γ₀
  have hdγ : CosetGeom.dist (r • γ₀ G₀ G₁ G₂) (r • v) + 5 ≤ b := by
    rw [CosetGeom.dist_smul, hdv]
    omega
  have hwin := Vv_le_ballStab_of_window hc hXodd hX3 hT hx₀Δ hx₀v hyΔ hyv hdx₀y hγv hdγ
  rw [CosetGeom.Vv_smul_γ₀ hc.normalizes r, ← hry, CosetGeom.ballStab_smul, conjSub_le_iff,
    conjSub_conjSub_inv] at hwin
  exact hy hwin

end CFSG.Quasithin.F112Crit

end
