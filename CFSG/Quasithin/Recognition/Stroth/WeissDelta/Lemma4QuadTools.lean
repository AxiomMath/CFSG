module

public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.Lemma4Setup
public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.Lemma4Transfer
public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.Lemma5
public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.LocalTypes

public section

open scoped Pointwise commutatorElement

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Stroth CFSG.Geometry.GeneralizedPolygons
  CFSG.GH74.GLS.SP CFSG.GH74.BNPair CFSG.QuasithinUnique
  CFSG.Quasithin.H13.F431.TwoF4 CFSG.Quasithin.H13.F431.Un
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

namespace CFSG.Quasithin.Stroth.WeissDelta

variable {V : Type} {Γ : SimpleGraph V} {H : Type} [Group H] [MulAction H V] [GraphAction H Γ]

private theorem commutator_mem_fixingSubgroup_of_left {a b : H} {z : V}
    (ha : a ∈ fixingSubgroup H (Γ.neighborSet z)) (hb : b • z = z) :
    ⁅a, b⁆ ∈ fixingSubgroup H (Γ.neighborSet z) := by
  rw [mem_fixingSubgroup_iff]
  intro x hx
  have hbz : b⁻¹ • z = z := by
    have h := congrArg (fun v => b⁻¹ • v) hb
    simpa using h.symm
  have hb1x : b⁻¹ • x ∈ Γ.neighborSet z := by
    rw [SimpleGraph.mem_neighborSet] at hx ⊢
    have h := (GraphAction.adj_smul b⁻¹ z x).mpr hx
    rwa [hbz] at h
  have ha1 : a⁻¹ • (b⁻¹ • x) = b⁻¹ • x :=
    (mem_fixingSubgroup_iff H).mp (Subgroup.inv_mem _ ha) _ hb1x
  have hax : a • x = x := (mem_fixingSubgroup_iff H).mp ha x hx
  have h1 : ⁅a, b⁆ • x = a • (b • (a⁻¹ • (b⁻¹ • x))) := by
    rw [commutatorElement_def]
    simp only [mul_smul]
  rw [h1, ha1, smul_inv_smul, hax]

private theorem commutator_mem_fixingSubgroup_of_right {a b : H} {z : V}
    (ha : a • z = z) (hb : b ∈ fixingSubgroup H (Γ.neighborSet z)) :
    ⁅a, b⁆ ∈ fixingSubgroup H (Γ.neighborSet z) := by
  have h : ⁅b, a⁆ ∈ fixingSubgroup H (Γ.neighborSet z) :=
    commutator_mem_fixingSubgroup_of_left hb ha
  have h' : ⁅a, b⁆ = ⁅b, a⁆⁻¹ := by
    rw [commutatorElement_inv]
  rw [h']
  exact Subgroup.inv_mem _ h

private theorem mem_window_rootGroup_spec (W : ClosedGoodPath H Γ) (a : ℤ) {u : H}
    (hu : u ∈ pathRootGroup H Γ (W.window a 4)) :
    u ∈ fixingSubgroup H (Γ.neighborSet (W.x (a + 1))) ∧
      u ∈ fixingSubgroup H (Γ.neighborSet (W.x (a + 2))) ∧
        u ∈ fixingSubgroup H (Γ.neighborSet (W.x (a + 3))) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [mem_fixingSubgroup_iff]
    intro w hw
    have h := (mem_pathRootGroup.mp hu) 1 (by norm_num) (by norm_num) w ?_
    · exact h
    · rwa [ClosedGoodPath.window_apply W a (s := 4) (by norm_num : (1 : ℕ) ≤ 4)]
  · rw [mem_fixingSubgroup_iff]
    intro w hw
    have h := (mem_pathRootGroup.mp hu) 2 (by norm_num) (by norm_num) w ?_
    · exact h
    · rwa [ClosedGoodPath.window_apply W a (s := 4) (by norm_num : (2 : ℕ) ≤ 4)]
  · rw [mem_fixingSubgroup_iff]
    intro w hw
    have h := (mem_pathRootGroup.mp hu) 3 (by norm_num) (by norm_num) w ?_
    · exact h
    · rwa [ClosedGoodPath.window_apply W a (s := 4) (by norm_num : (3 : ℕ) ≤ 4)]

private theorem commutator_window_rootGroup_le (W : ClosedGoodPath H Γ) (a : ℤ) :
    ⁅pathRootGroup H Γ (W.window a 4), pathRootGroup H Γ (W.window (a + 2) 4)⁆ ≤
      pathRootGroup H Γ (W.window (a + 1) 4) := by
  rw [Subgroup.commutator_le]
  intro u hu w hw
  obtain ⟨hu1, hu2, hu3⟩ := mem_window_rootGroup_spec W a hu
  obtain ⟨hw1, hw2, hw3⟩ := mem_window_rootGroup_spec W (a + 2) hw
  have hw1' : w ∈ fixingSubgroup H (Γ.neighborSet (W.x (a + 3))) := by
    simpa [show a + 2 + 1 = a + 3 by ring] using hw1
  have hw2' : w ∈ fixingSubgroup H (Γ.neighborSet (W.x (a + 4))) := by
    simpa [show a + 2 + 2 = a + 4 by ring] using hw2
  rw [mem_pathRootGroup]
  intro i hi1 hi3 v hv
  have hwin : (W.window (a + 1) 4) i = W.x (a + 1 + (i : ℤ)) :=
    ClosedGoodPath.window_apply W (a + 1) (s := 4) (by omega)
  rw [hwin] at hv
  interval_cases i
  ·
    have huw : w • W.x (a + 2) = W.x (a + 2) := by
      apply (mem_fixingSubgroup_iff H).mp hw1' (W.x (a + 2))
      rw [SimpleGraph.mem_neighborSet]
      have h := (W.adj (a + 2)).symm
      rwa [show a + 2 + 1 = a + 3 by ring] at h
    have hmem : ⁅u, w⁆ ∈ fixingSubgroup H (Γ.neighborSet (W.x (a + 2))) :=
      commutator_mem_fixingSubgroup_of_left hu2 huw
    have hvx : v ∈ Γ.neighborSet (W.x (a + 2)) := by
      rw [SimpleGraph.mem_neighborSet]
      rwa [show a + 1 + ((1 : ℕ) : ℤ) = a + 2 by ring] at hv
    exact (mem_fixingSubgroup_iff H).mp hmem v hvx
  ·
    have hmem : ⁅u, w⁆ ∈ fixingSubgroup H (Γ.neighborSet (W.x (a + 3))) :=
      Subgroup.commutator_le_self _
        (Subgroup.commutator_mem_commutator hu3 hw1')
    have hvx : v ∈ Γ.neighborSet (W.x (a + 3)) := by
      rw [SimpleGraph.mem_neighborSet]
      rwa [show a + 1 + ((2 : ℕ) : ℤ) = a + 3 by ring] at hv
    exact (mem_fixingSubgroup_iff H).mp hmem v hvx
  ·
    have hwu : u • W.x (a + 4) = W.x (a + 4) := by
      apply (mem_fixingSubgroup_iff H).mp hu3 (W.x (a + 4))
      rw [SimpleGraph.mem_neighborSet]
      have h := W.adj (a + 3)
      rwa [show a + 3 + 1 = a + 4 by ring] at h
    have hmem : ⁅u, w⁆ ∈ fixingSubgroup H (Γ.neighborSet (W.x (a + 4))) :=
      commutator_mem_fixingSubgroup_of_right hwu hw2'
    have hvx : v ∈ Γ.neighborSet (W.x (a + 4)) := by
      rw [SimpleGraph.mem_neighborSet]
      rwa [show a + 1 + ((3 : ℕ) : ℤ) = a + 4 by ring] at hv
    exact (mem_fixingSubgroup_iff H).mp hmem v hvx


private theorem commutator_window_neg_two (W : ClosedGoodPath H Γ) :
    ⁅pathRootGroup H Γ (W.window (-2) 4), pathRootGroup H Γ (W.window 0 4)⁆ ≤
      pathRootGroup H Γ (W.window (-1) 4) := by
  have h := commutator_window_rootGroup_le W (-2)
  simpa [show (-2 : ℤ) + 2 = 0 by norm_num, show (-2 : ℤ) + 1 = -1 by norm_num] using h

private theorem mem_secondKernel_smul_iff (g : H) (z : V) (x : H) :
    x ∈ secondKernel H Γ (g • z) ↔ g⁻¹ * x * g ∈ secondKernel H Γ z := by
  rw [mem_secondKernel_iff, mem_secondKernel_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · intro w hw
      have h := h1 (g • w) ((GraphAction.adj_smul g z w).mpr hw)
      calc
        (g⁻¹ * x * g) • w = g⁻¹ • (x • (g • w)) := by
          rw [mul_smul, mul_smul]
        _ = g⁻¹ • (g • w) := by rw [h]
        _ = w := inv_smul_smul g w
    · intro v hv w hw
      have hvg : Γ.Adj (g • z) (g • v) := (GraphAction.adj_smul g z v).mpr hv
      have hvw : Γ.Adj (g • v) (g • w) := (GraphAction.adj_smul g v w).mpr hw
      have h := h2 (g • v) hvg (g • w) hvw
      calc
        (g⁻¹ * x * g) • w = g⁻¹ • (x • (g • w)) := by
          rw [mul_smul, mul_smul]
        _ = g⁻¹ • (g • w) := by rw [h]
        _ = w := inv_smul_smul g w
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · intro w hw
      have hzw : Γ.Adj z (g⁻¹ • w) := by
        have h := (GraphAction.adj_smul g⁻¹ (g • z) w).mpr hw
        rwa [inv_smul_smul] at h
      have h := h1 (g⁻¹ • w) hzw
      calc
        x • w = g • ((g⁻¹ * x * g) • (g⁻¹ • w)) := by
          calc
            x • w = (x * g) • (g⁻¹ • w) := by rw [mul_smul, smul_inv_smul]
            _ = (g * (g⁻¹ * x * g)) • (g⁻¹ • w) := by
              congr 1
              group
            _ = g • ((g⁻¹ * x * g) • (g⁻¹ • w)) := by rw [mul_smul]
        _ = g • (g⁻¹ • w) := by rw [h]
        _ = w := smul_inv_smul g w
    · intro v hv w hw
      have hzv : Γ.Adj z (g⁻¹ • v) := by
        have h := (GraphAction.adj_smul g⁻¹ (g • z) v).mpr hv
        rwa [inv_smul_smul] at h
      have hzvw : Γ.Adj (g⁻¹ • v) (g⁻¹ • w) :=
        (GraphAction.adj_smul g⁻¹ v w).mpr hw
      have h := h2 (g⁻¹ • v) hzv (g⁻¹ • w) hzvw
      calc
        x • w = g • ((g⁻¹ * x * g) • (g⁻¹ • w)) := by
          calc
            x • w = (x * g) • (g⁻¹ • w) := by rw [mul_smul, smul_inv_smul]
            _ = (g * (g⁻¹ * x * g)) • (g⁻¹ • w) := by
              congr 1
              group
            _ = g • ((g⁻¹ * x * g) • (g⁻¹ • w)) := by rw [mul_smul]
        _ = g • (g⁻¹ • w) := by rw [h]
        _ = w := smul_inv_smul g w

private theorem mem_take_four_spec {p : GPath Γ 6} {u : H}
    (hu : u ∈ pathRootGroup H Γ (p.take 4 (by norm_num))) :
    u ∈ fixingSubgroup H (Γ.neighborSet (p 1)) ∧
      u ∈ fixingSubgroup H (Γ.neighborSet (p 2)) ∧
        u ∈ fixingSubgroup H (Γ.neighborSet (p 3)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [mem_fixingSubgroup_iff]
    intro w hw
    exact (mem_pathRootGroup.mp hu) 1 (by norm_num) (by norm_num) w (by
      rwa [GPath.take_apply_of_le p 4 (by norm_num) (by norm_num : (1 : ℕ) ≤ 4)])
  · rw [mem_fixingSubgroup_iff]
    intro w hw
    exact (mem_pathRootGroup.mp hu) 2 (by norm_num) (by norm_num) w (by
      rwa [GPath.take_apply_of_le p 4 (by norm_num) (by norm_num : (2 : ℕ) ≤ 4)])
  · rw [mem_fixingSubgroup_iff]
    intro w hw
    exact (mem_pathRootGroup.mp hu) 3 (by norm_num) (by norm_num) w (by
      rwa [GPath.take_apply_of_le p 4 (by norm_num) (by norm_num : (3 : ℕ) ≤ 4)])

private theorem mem_drop_two_spec {p : GPath Γ 6} {u : H}
    (hu : u ∈ pathRootGroup H Γ (p.drop 2 (by norm_num))) :
    u ∈ fixingSubgroup H (Γ.neighborSet (p 3)) ∧
      u ∈ fixingSubgroup H (Γ.neighborSet (p 4)) ∧
        u ∈ fixingSubgroup H (Γ.neighborSet (p 5)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [mem_fixingSubgroup_iff]
    intro w hw
    exact (mem_pathRootGroup.mp hu) 1 (by norm_num) (by norm_num) w (by
      rwa [GPath.drop_apply p 2 (by norm_num) (by norm_num : (1 : ℕ) ≤ 6 - 2)])
  · rw [mem_fixingSubgroup_iff]
    intro w hw
    exact (mem_pathRootGroup.mp hu) 2 (by norm_num) (by norm_num) w (by
      rwa [GPath.drop_apply p 2 (by norm_num) (by norm_num : (2 : ℕ) ≤ 6 - 2)])
  · rw [mem_fixingSubgroup_iff]
    intro w hw
    exact (mem_pathRootGroup.mp hu) 3 (by norm_num) (by norm_num) w (by
      rwa [GPath.drop_apply p 2 (by norm_num) (by norm_num : (3 : ℕ) ≤ 6 - 2)])

private theorem mem_mid_four_iff {p : GPath Γ 6} {u : H} :
    u ∈ pathRootGroup H Γ ((p.drop 1 (by norm_num)).take 4 (by norm_num)) ↔
      u ∈ fixingSubgroup H (Γ.neighborSet (p 2)) ∧
        u ∈ fixingSubgroup H (Γ.neighborSet (p 3)) ∧
          u ∈ fixingSubgroup H (Γ.neighborSet (p 4)) := by
  constructor
  · intro hu
    refine ⟨?_, ?_, ?_⟩
    · rw [mem_fixingSubgroup_iff]
      intro w hw
      exact (mem_pathRootGroup.mp hu) 1 (by norm_num) (by norm_num) w (by
        rwa [GPath.take_apply_of_le (p.drop 1 (by norm_num)) 4 (by norm_num)
          (by norm_num : (1 : ℕ) ≤ 4), GPath.drop_apply p 1 (by norm_num)
          (by norm_num : (1 : ℕ) ≤ 6 - 1)])
    · rw [mem_fixingSubgroup_iff]
      intro w hw
      exact (mem_pathRootGroup.mp hu) 2 (by norm_num) (by norm_num) w (by
        rwa [GPath.take_apply_of_le (p.drop 1 (by norm_num)) 4 (by norm_num)
          (by norm_num : (2 : ℕ) ≤ 4), GPath.drop_apply p 1 (by norm_num)
          (by norm_num : (2 : ℕ) ≤ 6 - 1)])
    · rw [mem_fixingSubgroup_iff]
      intro w hw
      exact (mem_pathRootGroup.mp hu) 3 (by norm_num) (by norm_num) w (by
        rwa [GPath.take_apply_of_le (p.drop 1 (by norm_num)) 4 (by norm_num)
          (by norm_num : (3 : ℕ) ≤ 4), GPath.drop_apply p 1 (by norm_num)
          (by norm_num : (3 : ℕ) ≤ 6 - 1)])
  · rintro ⟨h2, h3, h4⟩
    rw [mem_pathRootGroup]
    intro i hi1 hi3 w hw
    interval_cases i
    · have hw' : Γ.Adj (p 2) w := by
        rwa [GPath.take_apply_of_le (p.drop 1 (by norm_num)) 4 (by norm_num)
          (by norm_num : (1 : ℕ) ≤ 4), GPath.drop_apply p 1 (by norm_num)
          (by norm_num : (1 : ℕ) ≤ 6 - 1)] at hw
      exact (mem_fixingSubgroup_iff H).mp h2 w hw'
    · have hw' : Γ.Adj (p 3) w := by
        rwa [GPath.take_apply_of_le (p.drop 1 (by norm_num)) 4 (by norm_num)
          (by norm_num : (2 : ℕ) ≤ 4), GPath.drop_apply p 1 (by norm_num)
          (by norm_num : (2 : ℕ) ≤ 6 - 1)] at hw
      exact (mem_fixingSubgroup_iff H).mp h3 w hw'
    · have hw' : Γ.Adj (p 4) w := by
        rwa [GPath.take_apply_of_le (p.drop 1 (by norm_num)) 4 (by norm_num)
          (by norm_num : (3 : ℕ) ≤ 4), GPath.drop_apply p 1 (by norm_num)
          (by norm_num : (3 : ℕ) ≤ 6 - 1)] at hw
      exact (mem_fixingSubgroup_iff H).mp h4 w hw'


private theorem commute_of_mem_zpowers {g x y : H} (hx : x ∈ Subgroup.zpowers g)
    (hy : y ∈ Subgroup.zpowers g) : x * y = y * x := by
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hx
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hy
  rw [← hm, ← hn, ← zpow_add, ← zpow_add]
  congr 1
  omega

private theorem conj_mem_fixingSubgroup {g x : H} {z : V} (hg : g • z = z)
    (hx : x ∈ fixingSubgroup H (Γ.neighborSet z)) :
    g * x * g⁻¹ ∈ fixingSubgroup H (Γ.neighborSet z) := by
  have h := fixingSubgroup_neighborSet_smul (H := H) (Γ := Γ) g z
  rw [hg] at h
  rw [h]
  exact Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hx

private theorem conj_mem_zpowers_sup_of_mem_socTorus (W : ClosedGoodPath H Γ)
    (hL : LocalFacts H Γ (W.x 1)) {b c t : H}
    (hbT : b ∈ socTorus H Γ (W.x 1) (W.x 0) (W.x 2))
    (hcT : c ∈ socTorus H Γ (W.x 1) (W.x 0) (W.x 2))
    (htT : t ∈ socTorus H Γ (W.x 1) (W.x 0) (W.x 2))
    (hbgen : socTorus H Γ (W.x 1) (W.x 0) (W.x 2) ≤
      Subgroup.zpowers b ⊔ fixingSubgroup H (Γ.neighborSet (W.x 1))) :
    t * c * t⁻¹ ∈ Subgroup.zpowers c ⊔ fixingSubgroup H (Γ.neighborSet (W.x 1)) := by
  let T := socTorus H Γ (W.x 1) (W.x 0) (W.x 2)
  let F := fixingSubgroup H (Γ.neighborSet (W.x 1))
  have hT_le_stab : T ≤ MulAction.stabilizer H (W.x 1) :=
    le_trans inf_le_left (le_trans inf_le_left (socleAt_le_stabilizer hL.kernel_le))
  have hbN : b ∈ Subgroup.normalizer (F : Set H) :=
    stabilizer_le_normalizer_fixingSubgroup (hT_le_stab hbT)
  have hbpowN : Subgroup.zpowers b ≤ Subgroup.normalizer (F : Set H) :=
    Subgroup.zpowers_le.mpr hbN
  have hprod : (↑(Subgroup.zpowers b ⊔ F) : Set H) = ↑(Subgroup.zpowers b) * ↑F :=
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ hbpowN
  have ht_sup : t ∈ (↑(Subgroup.zpowers b ⊔ F) : Set H) := hbgen htT
  have hc_sup : c ∈ (↑(Subgroup.zpowers b ⊔ F) : Set H) := hbgen hcT
  rw [hprod] at ht_sup hc_sup
  obtain ⟨bt, hbt, ft, hft, ht_eq⟩ := ht_sup
  obtain ⟨bc, hbc, fc, hfc, hc_eq⟩ := hc_sup
  have hbcInvF : bc⁻¹ * ft * bc ∈ F := by
    have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hbpowN hbc)) ft).mp hft
    simpa using h
  have hc_eq' : bc * fc = c := hc_eq
  have hstep1 : ft * bc * ft⁻¹ = bc * ((bc⁻¹ * ft * bc) * ft⁻¹) := by group
  have hstep2 : ft * fc * ft⁻¹ ∈ F :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hft hfc) (Subgroup.inv_mem _ hft)
  have hpow_comm : bt * bc = bc * bt := commute_of_mem_zpowers hbt hbc
  let Y : H := bt * (((bc⁻¹ * ft * bc) * ft⁻¹) * (ft * fc * ft⁻¹)) * bt⁻¹
  have hbt_fix : bt • W.x 1 = W.x 1 :=
    smul_eq_self_of_mem_zpowers hbt (MulAction.mem_stabilizer_iff.mp (hT_le_stab hbT))
  have hYF : Y ∈ F :=
    conj_mem_fixingSubgroup hbt_fix
      (Subgroup.mul_mem _ (Subgroup.mul_mem _ hbcInvF (Subgroup.inv_mem _ hft)) hstep2)
  have hkey : t * c * t⁻¹ = c * (fc⁻¹ * Y) := by
    calc
      t * c * t⁻¹ = (bt * ft) * (bc * fc) * (bt * ft)⁻¹ := by rw [← ht_eq, ← hc_eq]
      _ = bt * (ft * bc * ft⁻¹) * (ft * fc * ft⁻¹) * bt⁻¹ := by group
      _ = bt * (bc * ((bc⁻¹ * ft * bc) * ft⁻¹)) *
          (ft * fc * ft⁻¹) * bt⁻¹ := by rw [hstep1]
      _ = (bt * bc * bt⁻¹) * Y := by
        show bt * (bc * ((bc⁻¹ * ft * bc) * ft⁻¹)) * (ft * fc * ft⁻¹) * bt⁻¹ =
          (bt * bc * bt⁻¹) * (bt * (((bc⁻¹ * ft * bc) * ft⁻¹) * (ft * fc * ft⁻¹)) * bt⁻¹)
        group
      _ = bc * Y := by
        rw [hpow_comm]
        group
      _ = (bc * fc) * (fc⁻¹ * Y) := by group
      _ = c * (fc⁻¹ * Y) := by
        show bc * fc * (fc⁻¹ * Y) = c * (fc⁻¹ * Y)
        rw [hc_eq']
  rw [hkey]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers c))
    (Subgroup.mem_sup_right (Subgroup.mul_mem _ (Subgroup.inv_mem _ hfc) hYF))


theorem commutator_pathRootGroup_le_and_ne_bot [Finite H] (hM : MoufangCondition H Γ 4)
    (hW : WeissFree H Γ 4) (hne : ∀ v w : V, Γ.Adj v w → ∃ u, Γ.Adj v u ∧ u ≠ w)
    (h3 : ∀ v w w' : V, Γ.Adj v w → Γ.Adj v w' → ∃ u, Γ.Adj v u ∧ u ≠ w ∧ u ≠ w')
    (hval : ∀ v w : V, Γ.Adj v w → ∃ e : ℕ, Nat.card {y : V // Γ.Adj v y ∧ y ≠ w} = 2 ^ e)
    (hL : ∀ z, LocalFacts H Γ z) (hR : ∀ z, RootFacts H Γ 4 z) {p : GPath Γ 6} (hp : p.NoBack)
    (hnc : ∀ q : GPath Γ 4, q.NoBack → q 4 = p 0 →
      ∃ a ∈ pathRootGroup H Γ q, ∃ b ∈ pathRootGroup H Γ q, a * b ≠ b * a) :
    ⁅pathRootGroup H Γ (p.take 4 (by norm_num)), pathRootGroup H Γ (p.drop 2 (by norm_num))⁆ ≤
        pathRootGroup H Γ ((p.drop 1 (by norm_num)).take 4 (by norm_num)) ∧
      ⁅pathRootGroup H Γ (p.take 4 (by norm_num)), pathRootGroup H Γ (p.drop 2 (by norm_num))⁆ ≠
        ⊥ := by
  have hU2mem : ∀ {u : H}, u ∈ pathRootGroup H Γ (p.take 4 (by norm_num)) →
      u ∈ fixingSubgroup H (Γ.neighborSet (p 1)) ∧
        u ∈ fixingSubgroup H (Γ.neighborSet (p 2)) ∧
          u ∈ fixingSubgroup H (Γ.neighborSet (p 3)) := fun hu => mem_take_four_spec hu
  constructor
  · rw [Subgroup.commutator_le]
    intro a ha b hb
    obtain ⟨ha1, ha2, ha3⟩ := hU2mem ha
    obtain ⟨hb3, hb4, hb5⟩ := mem_drop_two_spec hb
    rw [mem_mid_four_iff]
    refine ⟨?_, ?_, ?_⟩
    · have hb2 : b • p 2 = p 2 := by
        apply (mem_fixingSubgroup_iff H).mp hb3 (p 2)
        rw [SimpleGraph.mem_neighborSet]
        exact (p.adj 2 (by norm_num)).symm
      exact commutator_mem_fixingSubgroup_of_left ha2 hb2
    · exact Subgroup.commutator_le_self _
        (Subgroup.commutator_mem_commutator ha3 hb3)
    · have ha4 : a • p 4 = p 4 := by
        apply (mem_fixingSubgroup_iff H).mp ha3 (p 4)
        rw [SimpleGraph.mem_neighborSet]
        exact p.adj 3 (by norm_num)
      exact commutator_mem_fixingSubgroup_of_right ha4 hb4
  · intro hbot
    have hcomm : ∀ a ∈ pathRootGroup H Γ (p.take 4 (by norm_num)),
        ∀ b ∈ pathRootGroup H Γ (p.drop 2 (by norm_num)), a * b = b * a := by
      intro a ha b hb
      have hmem : ⁅a, b⁆ ∈
          ⁅pathRootGroup H Γ (p.take 4 (by norm_num)),
            pathRootGroup H Γ (p.drop 2 (by norm_num))⁆ :=
        Subgroup.commutator_mem_commutator ha hb
      rw [hbot] at hmem
      exact commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp hmem)
    have hU2_le_G2 : pathRootGroup H Γ (p.take 4 (by norm_num)) ≤ secondKernel H Γ (p 2) := by
      intro u hu
      obtain ⟨hu1, hu2, hu3⟩ := hU2mem hu
      rw [mem_secondKernel_iff]
      refine ⟨?_, ?_⟩
      · intro w hw
        exact (mem_fixingSubgroup_iff H).mp hu2 w hw
      · intro v hv w hw
        by_cases hv3 : v = p 3
        · subst hv3
          exact (mem_fixingSubgroup_iff H).mp hu3 w hw
        · have hp1ne : p 1 ≠ p 3 := by
            have h := hp 1 (by norm_num)
            rwa [show 1 + 2 = 3 by norm_num] at h
          have hqnb : (p.drop 2 (by norm_num)).rev.NoBack :=
            (hp.drop 2 (by norm_num)).rev
          obtain ⟨⟨b, hbU4⟩, hbv, -⟩ :=
            pathRootGroup_regular_of_weissFree (n := 4) (by norm_num) hM hW
              (p := (p.drop 2 (by norm_num)).rev) hqnb (y := p 1) (y' := v)
              (by
                show Γ.Adj ((p.drop 2 (by norm_num)).rev 4) (p 1)
                rw [GPath.rev_apply _ (by norm_num), show 4 - 4 = 0 by norm_num,
                  GPath.drop_apply p 2 (by norm_num) (by norm_num : (0 : ℕ) ≤ 6 - 2)]
                exact (p.adj 1 (by norm_num)).symm) hv
              (by
                show p 1 ≠ (p.drop 2 (by norm_num)).rev 3
                rw [GPath.rev_apply _ (by norm_num), show 4 - 3 = 1 by norm_num,
                  GPath.drop_apply p 2 (by norm_num) (by norm_num : (1 : ℕ) ≤ 6 - 2)]
                exact hp1ne)
              (by
                show v ≠ (p.drop 2 (by norm_num)).rev 3
                rw [GPath.rev_apply _ (by norm_num), show 4 - 3 = 1 by norm_num,
                  GPath.drop_apply p 2 (by norm_num) (by norm_num : (1 : ℕ) ≤ 6 - 2)]
                exact hv3)
          rw [pathRootGroup_rev_eq] at hbU4
          have hu_conj : b⁻¹ * u * b = u := by
            have h := hcomm u hu b hbU4
            calc
              b⁻¹ * u * b = b⁻¹ * (u * b) := by group
              _ = b⁻¹ * (b * u) := by rw [h]
              _ = u := by group
          have hb1v : b⁻¹ • v = p 1 := by
            rw [← hbv]
            exact inv_smul_smul b (p 1)
          have hx : b⁻¹ • w ∈ Γ.neighborSet (p 1) := by
            rw [SimpleGraph.mem_neighborSet]
            have h := (GraphAction.adj_smul b⁻¹ v w).mpr hw
            rwa [hb1v] at h
          have hfix : u • (b⁻¹ • w) = b⁻¹ • w :=
            (mem_fixingSubgroup_iff H).mp hu1 _ hx
          calc
            u • w = u • (b • (b⁻¹ • w)) := by rw [smul_inv_smul]
            _ = b • ((b⁻¹ * u * b) • (b⁻¹ • w)) := by
              calc
                u • (b • (b⁻¹ • w)) = (u * b) • (b⁻¹ • w) := by rw [← mul_smul]
                _ = (b * (b⁻¹ * u * b)) • (b⁻¹ • w) := by
                  congr 1
                  group
                _ = b • ((b⁻¹ * u * b) • (b⁻¹ • w)) := by rw [mul_smul]
            _ = b • (u • (b⁻¹ • w)) := by rw [hu_conj]
            _ = b • (b⁻¹ • w) := by rw [hfix]
            _ = w := smul_inv_smul b w
    obtain ⟨y', hy'adj, hy'ne0, hy'ne2⟩ :=
      h3 (p 1) (p 0) (p 2) (p.adj 0 (by norm_num)).symm (p.adj 1 (by norm_num))
    obtain ⟨g, hgstab, hg2⟩ :=
      exists_smul_of_mem_stabPath_take (n := 4) (by norm_num) hM hne
        (s := 6) (p := p) hp (i := 1) (by norm_num) (by norm_num) (by norm_num)
        (p.adj 1 (by norm_num)) hy'adj
        (by
          intro h
          exact (hp 0 (by norm_num)) h.symm)
        hy'ne0
    have hg0 : g • p 0 = p 0 := by
      have h := GPath.mem_stabPath_iff.mp hgstab 0 (by norm_num)
      rwa [GPath.take_apply_of_le p 1 (by norm_num) (by norm_num : (0 : ℕ) ≤ 1)] at h
    have hg1 : g • p 1 = p 1 := by
      have h := GPath.mem_stabPath_iff.mp hgstab 1 (by norm_num)
      rwa [GPath.take_apply_of_le p 1 (by norm_num) (by norm_num : (1 : ℕ) ≤ 1)] at h
    have hA_G2 : ∀ x ∈ pathRootGroup H Γ (g • p.take 4 (by norm_num)),
        x ∈ secondKernel H Γ y' := by
      intro x hx
      have hx' : g⁻¹ * x * g ∈ pathRootGroup H Γ (p.take 4 (by norm_num)) := by
        rw [pathRootGroup_smul_eq] at hx
        obtain ⟨u, hu, hu_eq⟩ := Subgroup.mem_map.mp hx
        have hxu : g⁻¹ * x * g = u := by
          change g * u * g⁻¹ = x at hu_eq
          rw [← hu_eq]
          group
        rwa [hxu]
      have hxG2 : g⁻¹ * x * g ∈ secondKernel H Γ (p 2) := hU2_le_G2 hx'
      have h : x ∈ secondKernel H Γ (g • p 2) :=
        (mem_secondKernel_smul_iff g (p 2) x).mpr hxG2
      rwa [hg2] at h
    have hA_le_stab : pathRootGroup H Γ (g • p.take 4 (by norm_num)) ≤
        MulAction.stabilizer H (p 0) := by
      intro x hx
      rw [pathRootGroup_smul_eq] at hx
      obtain ⟨u, hu, hu_eq⟩ := Subgroup.mem_map.mp hx
      obtain ⟨hu1, -, -⟩ := hU2mem hu
      have hu_fix0 : u • p 0 = p 0 := by
        apply (mem_fixingSubgroup_iff H).mp hu1 (p 0)
        rw [SimpleGraph.mem_neighborSet]
        exact (p.adj 0 (by norm_num)).symm
      rw [MulAction.mem_stabilizer_iff]
      rw [← hu_eq]
      change (g * u * g⁻¹) • p 0 = p 0
      rw [mul_smul, mul_smul]
      have hginv0 : g⁻¹ • p 0 = p 0 := by
        have h := congrArg (fun v => g⁻¹ • v) hg0
        simpa using h.symm
      rw [hginv0, hu_fix0]
      exact hg0
    have hA_norm : pathRootGroup H Γ (g • p.take 4 (by norm_num)) ≤
        Subgroup.normalizer (fixingSubgroup H (Γ.neighborSet (p 0)) : Set H) :=
      hA_le_stab.trans stabilizer_le_normalizer_fixingSubgroup
    let q2 : GPath Γ 4 := (p.take 4 (by norm_num)).rev
    have hq2_nb : q2.NoBack := (hp.take 4 (by norm_num)).rev
    have hq2_4 : q2 4 = p 0 := by
      show ((p.take 4 (by norm_num)).rev) 4 = p 0
      rw [GPath.rev_apply _ (by norm_num)]
      rw [show 4 - 4 = 0 by norm_num]
      exact GPath.take_apply_of_le p 4 (by norm_num) (by norm_num : (0 : ℕ) ≤ 4)
    have hq2_3 : q2 3 = p 1 := by
      show ((p.take 4 (by norm_num)).rev) 3 = p 1
      rw [GPath.rev_apply _ (by norm_num)]
      rw [show 4 - 3 = 1 by norm_num]
      exact GPath.take_apply_of_le p 4 (by norm_num) (by norm_num : (1 : ℕ) ≤ 4)
    obtain ⟨ω', hω'adj, hω'ne⟩ := hne (p 0) (p 1) (p.adj 0 (by norm_num))
    let qrev : GPath Γ 4 := (g • p.take 4 (by norm_num)).rev
    have hsmul_nb : (g • p.take 4 (by norm_num)).NoBack := by
      intro i hi
      have h := (hp.take 4 (by norm_num)) i hi
      rw [GPath.smul_apply, GPath.smul_apply]
      intro heq
      apply h
      have := congrArg (fun v => g⁻¹ • v) heq
      simpa using this
    have hqrev_nb : qrev.NoBack := hsmul_nb.rev
    have hqrev_4 : qrev 4 = p 0 := by
      show ((g • p.take 4 (by norm_num)).rev) 4 = p 0
      rw [GPath.rev_apply _ (by norm_num)]
      rw [show 4 - 4 = 0 by norm_num]
      rw [GPath.smul_apply, GPath.take_apply_of_le p 4 (by norm_num) (by norm_num : (0 : ℕ) ≤ 4)]
      exact hg0
    have hqrev_3 : qrev 3 = p 1 := by
      show ((g • p.take 4 (by norm_num)).rev) 3 = p 1
      rw [GPath.rev_apply _ (by norm_num)]
      rw [show 4 - 3 = 1 by norm_num]
      rw [GPath.smul_apply, GPath.take_apply_of_le p 4 (by norm_num) (by norm_num : (1 : ℕ) ≤ 4)]
      exact hg1
    have hQtorus : ∀ t ∈ socTorus H Γ (p 0) (qrev 3) ω',
        ∀ x ∈ pathRootGroup H Γ (p.take 4 (by norm_num)),
          t * x * t⁻¹ ∈ pathRootGroup H Γ (p.take 4 (by norm_num)) ⊔
            fixingSubgroup H (Γ.neighborSet (p 0)) := by
      intro t ht x hx
      have hq23 : q2 3 = qrev 3 := by rw [hq2_3, hqrev_3]
      rw [← hq23] at ht
      have hx2 : x ∈ pathRootGroup H Γ q2 := by
        rw [show q2 = (p.take 4 (by norm_num)).rev from rfl, pathRootGroup_rev_eq]
        exact hx
      have h := pathRootGroup_torus_conj_mem (n := 4) (by norm_num) hM hne
        (fun z => (hL z).kernel_le) (q := q2) hq2_nb (ω' := ω') (by rwa [hq2_4]) hω'ne t ht x hx2
      rwa [pathRootGroup_rev_eq, hq2_4] at h
    have hQ2 : IsPGroup 2 ↥(pathRootGroup H Γ (p.take 4 (by norm_num))) :=
      pathRootGroup_isPGroup (n := 4) (by norm_num) hW hval (hp.take 4 (by norm_num))
    have hQstab : pathRootGroup H Γ (p.take 4 (by norm_num)) ≤
        MulAction.stabilizer H (p 0) ⊓ MulAction.stabilizer H (qrev 3) := by
      intro u hu
      obtain ⟨hu1, hu2, -⟩ := hU2mem hu
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · rw [MulAction.mem_stabilizer_iff]
        exact (mem_fixingSubgroup_iff H).mp hu1 (p 0) (by
          rw [SimpleGraph.mem_neighborSet]
          exact (p.adj 0 (by norm_num)).symm)
      · rw [hqrev_3, MulAction.mem_stabilizer_iff]
        exact (mem_fixingSubgroup_iff H).mp hu2 (p 1) (by
          rw [SimpleGraph.mem_neighborSet]
          exact (p.adj 1 (by norm_num)).symm)
    have hle := (hR (p 0)).le_root qrev hqrev_nb hqrev_4 ω' hω'adj
      (by rw [hqrev_3]; exact hω'ne) (pathRootGroup H Γ (p.take 4 (by norm_num)))
      hQstab hQ2 hQtorus
    have hU2_le_sup : pathRootGroup H Γ (p.take 4 (by norm_num)) ≤
        pathRootGroup H Γ (g • p.take 4 (by norm_num)) ⊔
          fixingSubgroup H (Γ.neighborSet (p 0)) := by
      rw [pathRootGroup_rev_eq] at hle
      exact hle
    have hprod : (↑(pathRootGroup H Γ (g • p.take 4 (by norm_num)) ⊔
        fixingSubgroup H (Γ.neighborSet (p 0))) : Set H) =
        ↑(pathRootGroup H Γ (g • p.take 4 (by norm_num))) *
          ↑(fixingSubgroup H (Γ.neighborSet (p 0))) :=
      Subgroup.coe_mul_of_left_le_normalizer_right _ _ hA_norm
    obtain ⟨a, ha, b, hb, hab⟩ := hnc q2 hq2_nb hq2_4
    rw [pathRootGroup_rev_eq] at ha hb
    have hb_sup : b ∈ (↑(pathRootGroup H Γ (g • p.take 4 (by norm_num)) ⊔
        fixingSubgroup H (Γ.neighborSet (p 0))) : Set H) := hU2_le_sup hb
    rw [hprod] at hb_sup
    obtain ⟨a', ha', k, hk, hb_eq⟩ := hb_sup
    have hC2 := commutator_secondKernel_eq_bot (H := H) (Γ := Γ) hW hne
      (y := p 2) (z := p 1) (y' := y') (p.adj 1 (by norm_num)).symm hy'adj
      (fun h => hy'ne2 h.symm)
    have haG2 : a ∈ secondKernel H Γ (p 2) := hU2_le_G2 ha
    have ha'G2 : a' ∈ secondKernel H Γ y' := hA_G2 a' ha'
    have hmem_aa' : ⁅a, a'⁆ ∈ (⊥ : Subgroup H) := by
      rw [← hC2]
      exact Subgroup.commutator_mem_commutator haG2 ha'G2
    have hcomm_aa' : a * a' = a' * a :=
      commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp hmem_aa')
    have ha_fix0 : a • p 0 = p 0 := by
      obtain ⟨ha1, -, -⟩ := hU2mem ha
      exact (mem_fixingSubgroup_iff H).mp ha1 (p 0) (by
        rw [SimpleGraph.mem_neighborSet]
        exact (p.adj 0 (by norm_num)).symm)
    have hmem_ak : ⁅a, k⁆ ∈ fixingSubgroup H (Γ.neighborSet (p 0)) :=
      commutator_mem_fixingSubgroup_of_right ha_fix0 hk
    have ha'_fix0 : a' • p 0 = p 0 := MulAction.mem_stabilizer_iff.mp (hA_le_stab ha')
    have hconjG : (fixingSubgroup H (Γ.neighborSet (p 0))).map
        (MulAut.conj a').toMonoidHom = fixingSubgroup H (Γ.neighborSet (p 0)) := by
      have h := fixingSubgroup_neighborSet_smul (H := H) (Γ := Γ) a' (p 0)
      rw [ha'_fix0] at h
      exact h.symm
    have hmemG : a' * ⁅a, k⁆ * a'⁻¹ ∈ fixingSubgroup H (Γ.neighborSet (p 0)) := by
      have hmemmap := Subgroup.mem_map_of_mem (MulAut.conj a').toMonoidHom hmem_ak
      rw [hconjG] at hmemmap
      change a' * ⁅a, k⁆ * a'⁻¹ ∈ fixingSubgroup H (Γ.neighborSet (p 0)) at hmemmap
      exact hmemmap
    have hcalc : ⁅a, b⁆ = a' * ⁅a, k⁆ * a'⁻¹ := by
      rw [show b = a' * k from hb_eq.symm, commutatorElement_def, commutatorElement_def]
      calc
        a * (a' * k) * a⁻¹ * (a' * k)⁻¹ = (a * a') * k * a⁻¹ * k⁻¹ * a'⁻¹ := by group
        _ = (a' * a) * k * a⁻¹ * k⁻¹ * a'⁻¹ := by rw [hcomm_aa']
        _ = a' * (a * k * a⁻¹ * k⁻¹) * a'⁻¹ := by group
    have hmemU : a' * ⁅a, k⁆ * a'⁻¹ ∈ pathRootGroup H Γ (p.take 4 (by norm_num)) := by
      have hmem : ⁅a, b⁆ ∈ pathRootGroup H Γ (p.take 4 (by norm_num)) :=
        Subgroup.commutator_le_self _ (Subgroup.commutator_mem_commutator ha hb)
      rwa [hcalc] at hmem
    have hbot8 : fixingSubgroup H (Γ.neighborSet (p 0)) ⊓
        pathRootGroup H Γ (p.take 4 (by norm_num)) = ⊥ :=
      fixingSubgroup_inf_pathRootGroup_eq_bot (n := 4) (by norm_num) hW
        (hp.take 4 (by norm_num))
    have hmem_bot : a' * ⁅a, k⁆ * a'⁻¹ ∈ (⊥ : Subgroup H) := by
      rw [← hbot8]
      exact Subgroup.mem_inf.mpr ⟨hmemG, hmemU⟩
    have hone : ⁅a, b⁆ = 1 := by
      rw [hcalc, Subgroup.mem_bot.mp hmem_bot]
    exact hab (commutatorElement_eq_one_iff_mul_comm.mp hone)

theorem ClosedGoodPath.false_of_mem_socleAt [Finite H] (hM : MoufangCondition H Γ 4)
    (hW : WeissFree H Γ 4) (hne : ∀ v w : V, Γ.Adj v w → ∃ u, Γ.Adj v u ∧ u ≠ w)
    (h3 : ∀ v w w' : V, Γ.Adj v w → Γ.Adj v w' → ∃ u, Γ.Adj v u ∧ u ≠ w ∧ u ≠ w')
    (hval : ∀ v w : V, Γ.Adj v w → ∃ e : ℕ, Nat.card {y : V // Γ.Adj v y ∧ y ≠ w} = 2 ^ e)
    (hL : ∀ z, LocalFacts H Γ z) (hR : ∀ z, RootFacts H Γ 4 z) (W : ClosedGoodPath H Γ)
    (hZ1 : ZassenhausFacts H Γ (W.x 1))
    (hnc : ∀ q : GPath Γ 4, q.NoBack → q 4 = W.x 0 →
      ∃ a ∈ pathRootGroup H Γ q, ∃ b ∈ pathRootGroup H Γ q, a * b ≠ b * a)
    {c : H} (hcH : c ∈ W.kernelAt 0) (hc2 : c ∈ fixingSubgroup H (Γ.neighborSet (W.x 2)))
    (hcs : c ∈ socleAt H Γ (W.x 1)) (hc1 : c ∉ fixingSubgroup H (Γ.neighborSet (W.x 1))) :
    False := by
  let p : GPath Γ 6 := W.window 0 6
  have hp : p.NoBack := W.window_noBack 0 6
  have hp0 : p 0 = W.x 0 := by
    rw [show p = W.window 0 6 from rfl,
      ClosedGoodPath.window_apply W 0 (s := 6) (by norm_num : (0 : ℕ) ≤ 6)]
    norm_num
  have hp2 : p 2 = W.x 2 := by
    rw [show p = W.window 0 6 from rfl,
      ClosedGoodPath.window_apply W 0 (s := 6) (by norm_num : (2 : ℕ) ≤ 6)]
    norm_num
  have hnc' : ∀ q : GPath Γ 4, q.NoBack → q 4 = p 0 →
      ∃ a ∈ pathRootGroup H Γ q, ∃ b ∈ pathRootGroup H Γ q, a * b ≠ b * a := by
    intro q hq hq0
    exact hnc q hq (by rw [hq0, hp0])
  obtain ⟨hleV, hneV⟩ :=
    commutator_pathRootGroup_le_and_ne_bot hM hW hne h3 hval hL hR hp hnc'
  have hcommU2 : ∀ u ∈ pathRootGroup H Γ (p.take 4 (by norm_num)), c * u = u * c := by
    intro u hu
    refine commute_of_mem_fixingSubgroup_inf_stabPath (n := 4) (by norm_num) hW
      (hp.take 4 (by norm_num)) ?_ hu
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have h0 : (p.take 4 (by norm_num)) 0 = W.x 0 := by
        rw [GPath.take_apply_of_le p 4 (by norm_num) (by norm_num : (0 : ℕ) ≤ 4)]
        exact hp0
      rw [h0]
      exact hcH.1
    · rw [GPath.mem_stabPath_iff]
      intro j hj
      have h := (ClosedGoodPath.mem_stab_iff.mp hcH.2) (0 + (j : ℤ))
      rw [GPath.take_apply_of_le p 4 (by norm_num) hj,
        ClosedGoodPath.window_apply W 0 (s := 6) (by omega)]
      simpa using h
  have hcommU4 : ∀ u ∈ pathRootGroup H Γ (p.drop 2 (by norm_num)), c * u = u * c := by
    intro u hu
    refine commute_of_mem_fixingSubgroup_inf_stabPath (n := 4) (by norm_num) hW
      (hp.drop 2 (by norm_num)) ?_ hu
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have h0 : (p.drop 2 (by norm_num)) 0 = W.x 2 := by
        rw [GPath.drop_apply p 2 (by norm_num) (by norm_num : (0 : ℕ) ≤ 6 - 2)]
        exact hp2
      rw [h0]
      exact hc2
    · rw [GPath.mem_stabPath_iff]
      intro j hj
      have h := (ClosedGoodPath.mem_stab_iff.mp hcH.2) (2 + (j : ℤ))
      rw [GPath.drop_apply p 2 (by norm_num) hj]
      have hpj : p (2 + j) = W.x (2 + (j : ℤ)) := by
        rw [show p = W.window 0 6 from rfl,
          ClosedGoodPath.window_apply W 0 (s := 6) (by omega)]
        push_cast
        ring_nf
      rw [hpj]
      simpa using h
  have hcommV : ∀ x ∈ ⁅pathRootGroup H Γ (p.take 4 (by norm_num)),
      pathRootGroup H Γ (p.drop 2 (by norm_num))⁆, c * x = x * c := by
    intro x hx
    have hcentral : ⁅pathRootGroup H Γ (p.take 4 (by norm_num)),
        pathRootGroup H Γ (p.drop 2 (by norm_num))⁆ ≤
        Subgroup.centralizer ({c} : Set H) := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst y
      have hca : (MulAut.conj c).toMonoidHom a = a := by
        change c * a * c⁻¹ = a
        rw [hcommU2 a ha]
        group
      have hcb : (MulAut.conj c).toMonoidHom b = b := by
        change c * b * c⁻¹ = b
        rw [hcommU4 b hb]
        group
      have hconj : (MulAut.conj c).toMonoidHom ⁅a, b⁆ = ⁅a, b⁆ := by
        rw [map_commutatorElement, hca, hcb]
      have hconj' : c * ⁅a, b⁆ * c⁻¹ = ⁅a, b⁆ := by
        change c * ⁅a, b⁆ * c⁻¹ = ⁅a, b⁆ at hconj
        exact hconj
      calc
        c * ⁅a, b⁆ = (c * ⁅a, b⁆ * c⁻¹) * c := by group
        _ = ⁅a, b⁆ * c := by rw [hconj']
    exact (Subgroup.mem_centralizer_iff.mp (hcentral hx)) c (by simp)
  obtain ⟨v0, hvne0⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hneV
  let v : H := v0
  have hvV : v ∈ ⁅pathRootGroup H Γ (p.take 4 (by norm_num)),
      pathRootGroup H Γ (p.drop 2 (by norm_num))⁆ := v0.2
  have hvne : v ≠ 1 := fun h => hvne0 (Subtype.ext h)
  have hvV' : v ∈ pathRootGroup H Γ ((p.drop 1 (by norm_num)).take 4 (by norm_num)) := hleV hvV
  obtain ⟨hv2, hv3, hv4⟩ := mem_mid_four_iff.mp hvV'
  have hv2' : v ∈ fixingSubgroup H (Γ.neighborSet (W.x 2)) := by
    rwa [hp2] at hv2
  have hv3' : v ∈ fixingSubgroup H (Γ.neighborSet (W.x 3)) := by
    have hp3 : p 3 = W.x 3 := by
      rw [show p = W.window 0 6 from rfl,
        ClosedGoodPath.window_apply W 0 (s := 6) (by norm_num : (3 : ℕ) ≤ 6)]
      norm_num
    rwa [hp3] at hv3
  have hx1x0 : Γ.Adj (W.x 1) (W.x 0) := (W.adj 0).symm
  have hx1x2 : Γ.Adj (W.x 1) (W.x 2) := W.adj 1
  have hx0x2 : W.x 0 ≠ W.x 2 := W.ne_add_two 0
  have hv_fix1 : v • W.x 1 = W.x 1 :=
    (mem_fixingSubgroup_iff H).mp hv2' (W.x 1) (W.adj 1).symm
  have hv_fix2 : v • W.x 2 = W.x 2 :=
    (mem_fixingSubgroup_iff H).mp hv3' (W.x 2) (by
      rw [SimpleGraph.mem_neighborSet]
      exact (W.adj 2).symm)
  have hv_adj : Γ.Adj (W.x 1) (v • W.x 0) := by
    have h := (GraphAction.adj_smul v (W.x 1) (W.x 0)).mpr hx1x0
    rwa [hv_fix1] at h
  have hv_ne2 : v • W.x 0 ≠ W.x 2 := by
    intro h
    apply hx0x2
    have h' : v • W.x 0 = v • W.x 2 := by rw [h, hv_fix2]
    exact smul_left_cancel v h'
  let qv : GPath Γ 4 := ((p.drop 1 (by norm_num)).take 4 (by norm_num)).rev
  have hqv_nb : qv.NoBack := ((hp.drop 1 (by norm_num)).take 4 (by norm_num)).rev
  have hvVq : v ∈ pathRootGroup H Γ qv := by
    rw [show qv = ((p.drop 1 (by norm_num)).take 4 (by norm_num)).rev from rfl,
      pathRootGroup_rev_eq]
    exact hvV'
  have hqv_4 : qv 4 = W.x 1 := by
    show (((p.drop 1 (by norm_num)).take 4 (by norm_num)).rev) 4 = W.x 1
    rw [GPath.rev_apply _ (by norm_num), show 4 - 4 = 0 by norm_num,
      GPath.take_apply_of_le (p.drop 1 (by norm_num)) 4 (by norm_num) (by norm_num : (0 : ℕ) ≤ 4),
      GPath.drop_apply p 1 (by norm_num) (by norm_num : (0 : ℕ) ≤ 6 - 1)]
    rw [show p 1 = W.x 1 by
      rw [show p = W.window 0 6 from rfl,
        ClosedGoodPath.window_apply W 0 (s := 6) (by norm_num : (1 : ℕ) ≤ 6)]
      norm_num]
  have hqv_3 : qv 3 = W.x 2 := by
    show (((p.drop 1 (by norm_num)).take 4 (by norm_num)).rev) 3 = W.x 2
    rw [GPath.rev_apply _ (by norm_num), show 4 - 3 = 1 by norm_num,
      GPath.take_apply_of_le (p.drop 1 (by norm_num)) 4 (by norm_num) (by norm_num : (1 : ℕ) ≤ 4),
      GPath.drop_apply p 1 (by norm_num) (by norm_num : (1 : ℕ) ≤ 6 - 1)]
    rw [show p 2 = W.x 2 by
      rw [show p = W.window 0 6 from rfl,
        ClosedGoodPath.window_apply W 0 (s := 6) (by norm_num : (2 : ℕ) ≤ 6)]
      norm_num]
  have hv_ne0 : v • W.x 0 ≠ W.x 0 := by
    intro hfix
    apply hvne
    refine pathRootGroup_eq_one_of_fix_of_weissFree (n := 4) (by norm_num) hW hqv_nb hvVq ?_ ?_ hfix
    · rw [hqv_4]
      exact hx1x0
    · rw [hqv_3]
      exact hx0x2
  have hc0 : c • W.x 0 = W.x 0 := (ClosedGoodPath.mem_stab_iff.mp hcH.2) 0
  have hvc : v * c = c * v := (hcommV v hvV).symm
  have hcvx : c • (v • W.x 0) = v • W.x 0 := by
    rw [← mul_smul, ← hvc, mul_smul, hc0]
  have hcT : c ∈ socTorus H Γ (W.x 1) (W.x 0) (W.x 2) := by
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hcs, ?_⟩, ?_⟩
    · rw [MulAction.mem_stabilizer_iff]
      exact (ClosedGoodPath.mem_stab_iff.mp hcH.2) 0
    · rw [MulAction.mem_stabilizer_iff]
      exact (ClosedGoodPath.mem_stab_iff.mp hcH.2) 2
  obtain ⟨b, hbT, -, hbgen0⟩ :=
    (hL (W.x 1)).torusGen (W.x 0) (W.x 2) hx1x0 hx1x2 hx0x2
      (socTorus H Γ (W.x 1) (W.x 0) (W.x 2)) le_rfl le_sup_left
  have hbgen : socTorus H Γ (W.x 1) (W.x 0) (W.x 2) ≤
      Subgroup.zpowers b ⊔ fixingSubgroup H (Γ.neighborSet (W.x 1)) := by
    rw [Subgroup.zpowers_eq_closure]
    exact hbgen0
  have hM_le : Subgroup.zpowers c ≤
      MulAction.stabilizer H (W.x 1) ⊓ MulAction.stabilizer H (W.x 0) ⊓
        MulAction.stabilizer H (W.x 2) := by
    refine Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨?_, ?_⟩, ?_⟩)
    · rw [MulAction.mem_stabilizer_iff]
      exact (socleAt_le_stabilizer (hL (W.x 1)).kernel_le) hcs
    · rw [MulAction.mem_stabilizer_iff]
      exact (ClosedGoodPath.mem_stab_iff.mp hcH.2) 0
    · rw [MulAction.mem_stabilizer_iff]
      exact (ClosedGoodPath.mem_stab_iff.mp hcH.2) 2
  have hM_norm : ∀ t ∈ socTorus H Γ (W.x 1) (W.x 0) (W.x 2),
      ∀ m ∈ Subgroup.zpowers c,
        t * m * t⁻¹ ∈ Subgroup.zpowers c ⊔ fixingSubgroup H (Γ.neighborSet (W.x 1)) := by
    intro t htT m hm
    have ht_fix : t • W.x 1 = W.x 1 :=
      MulAction.mem_stabilizer_iff.mp
        ((le_trans inf_le_left (le_trans inf_le_left
          (socleAt_le_stabilizer (hL (W.x 1)).kernel_le))) htT)
    have htc : t * c * t⁻¹ ∈
        Subgroup.zpowers c ⊔ fixingSubgroup H (Γ.neighborSet (W.x 1)) :=
      conj_mem_zpowers_sup_of_mem_socTorus W (hL (W.x 1)) hbT hcT htT hbgen
    have htF : (fixingSubgroup H (Γ.neighborSet (W.x 1))).map
        (MulAut.conj t).toMonoidHom = fixingSubgroup H (Γ.neighborSet (W.x 1)) := by
      have h := fixingSubgroup_neighborSet_smul (H := H) (Γ := Γ) t (W.x 1)
      rw [ht_fix] at h
      exact h.symm
    have hmapK : (Subgroup.zpowers c ⊔ fixingSubgroup H (Γ.neighborSet (W.x 1))).map
        (MulAut.conj t).toMonoidHom ≤
        Subgroup.zpowers c ⊔ fixingSubgroup H (Γ.neighborSet (W.x 1)) := by
      rw [Subgroup.map_sup, MonoidHom.map_zpowers, htF]
      exact sup_le (Subgroup.zpowers_le.mpr htc) le_sup_right
    have hmK : (MulAut.conj t).toMonoidHom m ∈
        Subgroup.zpowers c ⊔ fixingSubgroup H (Γ.neighborSet (W.x 1)) :=
      hmapK (Subgroup.mem_map_of_mem (MulAut.conj t).toMonoidHom (Subgroup.mem_sup_left hm))
    simpa [MulAut.conj_apply] using hmK
  rcases hZ1.dichotomy (W.x 0) (W.x 2) hx1x0 hx1x2 hx0x2 (Subgroup.zpowers c) hM_le hM_norm with
    hle | hfix
  · exact hc1 (hle (Subgroup.mem_zpowers c))
  · rcases hfix (v • W.x 0) hv_adj (fun m hm => smul_eq_self_of_mem_zpowers hm hcvx) with
      h | h
    · exact hv_ne0 h
    · exact hv_ne2 h


theorem ClosedGoodPath.secondKernel_ne_bot_of_le (hM : MoufangCondition H Γ 4)
    (hW : WeissFree H Γ 4)
    (h3 : ∀ v w w' : V, Γ.Adj v w → Γ.Adj v w' → ∃ u, Γ.Adj v u ∧ u ≠ w ∧ u ≠ w')
    (W : ClosedGoodPath H Γ)
    (hF3 : ¬ W.HasThirdFix (W.kernelAt 0) 3)
    (h2 : W.kernelAt 0 ≤ fixingSubgroup H (Γ.neighborSet (W.x 2))) :
    secondKernel H Γ (W.x 0) ≠ ⊥ := by
  let Uminus : Subgroup H := pathRootGroup H Γ (W.window (-2) 4)
  let Uplus : Subgroup H := pathRootGroup H Γ (W.window 0 4)
  let Wone : Subgroup H := pathRootGroup H Γ (W.window (-1) 4)
  have hcommMinus : ∀ h ∈ W.kernelAt 0, ∀ u ∈ Uminus, h * u = u * h := by
    intro h hh u hu
    have hu1 : u ∈ fixingSubgroup H (Γ.neighborSet (W.x 1)) := by
      simpa using (mem_window_rootGroup_spec W (-2) hu).2.2
    have hu_fix2 : u • W.x 2 = W.x 2 :=
      (mem_fixingSubgroup_iff H).mp hu1 (W.x 2) (W.adj 1)
    have hKp : W.kernelAt 0 ≤ GPath.stabPath (H := H) (W.window (-2) 4) :=
      (inf_le_right : W.kernelAt 0 ≤ W.stab).trans (W.stab_le_stabPath_window (-2) 4)
    have hb : Γ.Adj ((W.window (-2) 4) 4) (W.x 3) := by
      rw [ClosedGoodPath.window_apply W (-2) (s := 4) (by norm_num : (4 : ℕ) ≤ 4)]
      norm_num
      exact W.adj 2
    have hb1 : W.x 3 ≠ (W.window (-2) 4) 3 := by
      rw [ClosedGoodPath.window_apply W (-2) (s := 4) (by norm_num : (3 : ℕ) ≤ 4)]
      norm_num
      exact (W.ne_add_two 1).symm
    have hKb : ∀ g ∈ W.kernelAt 0, g • W.x 3 = W.x 3 :=
      fun g hg => (ClosedGoodPath.mem_stab_iff.mp hg.2) 3
    have hfix : ∀ g ∈ W.kernelAt 0, g • u • W.x 3 = u • W.x 3 := by
      intro g hg
      have hgG : g ∈ fixingSubgroup H (Γ.neighborSet (W.x 2)) := h2 hg
      apply (mem_fixingSubgroup_iff H).mp hgG
      rw [SimpleGraph.mem_neighborSet]
      have h := (GraphAction.adj_smul u (W.x 2) (W.x 3)).mpr (W.adj 2)
      rwa [hu_fix2] at h
    exact (forall_smul_smul_eq_iff_commute (n := 4) (by norm_num) hW
      (W.window_noBack (-2) 4) hKp hb hb1 hKb hu).mp hfix h hh
  have hcommPlus : ∀ h ∈ W.kernelAt 0, ∀ u ∈ Uplus, h * u = u * h := by
    intro h hh u hu
    refine commute_of_mem_fixingSubgroup_inf_stabPath (n := 4) (by norm_num) hW
      (W.window_noBack 0 4) ?_ hu
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have h0 : (W.window 0 4) 0 = W.x 0 := by
        rw [ClosedGoodPath.window_apply W 0 (s := 4) (by norm_num : (0 : ℕ) ≤ 4)]
        norm_num
      simpa [h0] using hh.1
    · exact (inf_le_right : W.kernelAt 0 ≤ W.stab).trans
        (W.stab_le_stabPath_window 0 4) hh
  have hcentral : ⁅Uminus, Uplus⁆ ≤ Subgroup.centralizer (W.kernelAt 0 : Set H) := by
    rw [Subgroup.commutator_le]
    intro u hu w hw
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hcu : (MulAut.conj h).toMonoidHom u = u := by
      change h * u * h⁻¹ = u
      rw [hcommMinus h hh u hu]
      group
    have hcw : (MulAut.conj h).toMonoidHom w = w := by
      change h * w * h⁻¹ = w
      rw [hcommPlus h hh w hw]
      group
    have hconj : (MulAut.conj h).toMonoidHom ⁅u, w⁆ = ⁅u, w⁆ := by
      rw [map_commutatorElement, hcu, hcw]
    have hconj' : h * ⁅u, w⁆ * h⁻¹ = ⁅u, w⁆ := by
      change h * ⁅u, w⁆ * h⁻¹ = ⁅u, w⁆ at hconj
      exact hconj
    calc
      h * ⁅u, w⁆ = (h * ⁅u, w⁆ * h⁻¹) * h := by group
      _ = ⁅u, w⁆ * h := by rw [hconj']
  have hC_W1 : ∀ u ∈ Wone, (∀ h ∈ W.kernelAt 0, h * u = u * h) → u = 1 := by
    intro u hu hcomm
    by_contra hu1
    apply hF3
    have hu0 : u ∈ fixingSubgroup H (Γ.neighborSet (W.x 0)) := by
      simpa using (mem_window_rootGroup_spec W (-1) hu).1
    have hu1' : u ∈ fixingSubgroup H (Γ.neighborSet (W.x 1)) := by
      simpa using (mem_window_rootGroup_spec W (-1) hu).2.1
    have hu2 : u ∈ fixingSubgroup H (Γ.neighborSet (W.x 2)) := by
      simpa using (mem_window_rootGroup_spec W (-1) hu).2.2
    have hu_fix2 : u • W.x 2 = W.x 2 :=
      (mem_fixingSubgroup_iff H).mp hu1' (W.x 2) (W.adj 1)
    have hu_fix3 : u • W.x 3 = W.x 3 :=
      (mem_fixingSubgroup_iff H).mp hu2 (W.x 3) (W.adj 2)
    refine ⟨u • W.x 4, ?_, ?_, ?_, ?_⟩
    · have h := (GraphAction.adj_smul u (W.x 3) (W.x 4)).mpr (W.adj 3)
      rwa [hu_fix3] at h
    · intro hz
      have hx24 : W.x 2 = W.x 4 := by
        have h : u • W.x 4 = u • W.x 2 := by
          rw [hz, hu_fix2]
          norm_num
        exact (smul_left_cancel u h).symm
      exact (W.ne_add_two 2) hx24
    · intro hz
      apply hu1
      refine pathRootGroup_eq_one_of_fix_of_weissFree (n := 4) (by norm_num) hW
        (W.window_noBack (-1) 4) hu ?_ ?_ hz
      · rw [show (W.window (-1) 4) 4 = W.x 3 by
          rw [ClosedGoodPath.window_apply W (-1) (s := 4) (by norm_num : (4 : ℕ) ≤ 4)]
          norm_num]
        exact W.adj 3
      · rw [show (W.window (-1) 4) 3 = W.x 2 by
          rw [ClosedGoodPath.window_apply W (-1) (s := 4) (by norm_num : (3 : ℕ) ≤ 4)]
          norm_num]
        exact (W.ne_add_two 2).symm
    · intro h hh
      have hhu : h * u = u * h := hcomm h hh
      calc
        h • (u • W.x 4) = (h * u) • W.x 4 := by rw [mul_smul]
        _ = (u * h) • W.x 4 := by rw [hhu]
        _ = u • (h • W.x 4) := by rw [mul_smul]
        _ = u • W.x 4 := by rw [(ClosedGoodPath.mem_stab_iff.mp hh.2) 4]
  have hcommBot : ⁅Uminus, Uplus⁆ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have hcentx : x ∈ Subgroup.centralizer (W.kernelAt 0 : Set H) := hcentral hx
    change x ∈ ⁅pathRootGroup H Γ (W.window (-2) 4),
      pathRootGroup H Γ (W.window 0 4)⁆ at hx
    have hxW : x ∈ Wone := commutator_window_neg_two W hx
    exact hC_W1 x hxW (fun h hh => (Subgroup.mem_centralizer_iff.mp hcentx) h hh)
  have hUminus_le_G2 : Uminus ≤ secondKernel H Γ (W.x 0) := by
    intro u hu
    rw [mem_secondKernel_iff]
    refine ⟨?_, ?_⟩
    · have hu0 : u ∈ fixingSubgroup H (Γ.neighborSet (W.x 0)) := by
        simpa using (mem_window_rootGroup_spec W (-2) hu).2.1
      intro w hw
      exact (mem_fixingSubgroup_iff H).mp hu0 w hw
    · intro y hy w hw
      by_cases hy1 : y = W.x 1
      · subst hy1
        have hu1 : u ∈ fixingSubgroup H (Γ.neighborSet (W.x 1)) := by
          simpa using (mem_window_rootGroup_spec W (-2) hu).2.2
        exact (mem_fixingSubgroup_iff H).mp hu1 w hw
      ·
        obtain ⟨⟨w0, hw0U⟩, hw0y, -⟩ :=
          pathRootGroup_regular_of_weissFree (n := 4) (by norm_num) hM hW
            (p := (W.window 0 4).rev) ((W.window_noBack 0 4).rev) (y := W.x (-1)) (y' := y)
            (by
              show Γ.Adj ((W.window 0 4).rev 4) (W.x (-1))
              rw [GPath.rev_apply _ (by norm_num), show 4 - 4 = 0 by norm_num,
                ClosedGoodPath.window_apply W 0 (s := 4) (by norm_num : (0 : ℕ) ≤ 4)]
              exact (W.adj (-1)).symm) hy
            (by
              show W.x (-1) ≠ (W.window 0 4).rev 3
              rw [GPath.rev_apply _ (by norm_num), show 4 - 3 = 1 by norm_num,
                ClosedGoodPath.window_apply W 0 (s := 4) (by norm_num : (1 : ℕ) ≤ 4)]
              exact W.ne_add_two (-1))
            (by
              show y ≠ (W.window 0 4).rev 3
              rw [GPath.rev_apply _ (by norm_num), show 4 - 3 = 1 by norm_num,
                ClosedGoodPath.window_apply W 0 (s := 4) (by norm_num : (1 : ℕ) ≤ 4)]
              exact hy1)
        have hw0Uplus : w0 ∈ Uplus := by
          rw [pathRootGroup_rev_eq] at hw0U
          exact hw0U
        have hwu : w0 * u = u * w0 := by
          have hmem : ⁅u, w0⁆ ∈ (⊥ : Subgroup H) := by
            rw [← hcommBot]
            exact Subgroup.commutator_mem_commutator hu hw0Uplus
          exact (commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp hmem)).symm
        have hu_eq : u = w0 * u * w0⁻¹ := by
          rw [hwu]
          group
        have hxmap : u ∈ pathRootGroup H Γ (w0 • W.window (-2) 4) := by
          rw [pathRootGroup_smul_eq]
          refine Subgroup.mem_map.mpr ⟨u, hu, ?_⟩
          change w0 * u * w0⁻¹ = u
          exact hu_eq.symm
        have hq1 : (w0 • W.window (-2) 4) 1 = w0 • W.x (-1) := by
          rw [GPath.smul_apply, ClosedGoodPath.window_apply W (-2) (s := 4)
            (by norm_num : (1 : ℕ) ≤ 4)]
          norm_num
        have hfix_y : u ∈ fixingSubgroup H (Γ.neighborSet y) := by
          rw [← hw0y]
          rw [mem_fixingSubgroup_iff]
          intro z hz
          have hz' : Γ.Adj ((w0 • W.window (-2) 4) 1) z := by rwa [hq1]
          exact (mem_pathRootGroup.mp hxmap) 1 (by norm_num) (by norm_num) z hz'
        exact (mem_fixingSubgroup_iff H).mp hfix_y w hw
  have hUminus_ne_bot : Uminus ≠ ⊥ := by
    obtain ⟨u, hxu, hux1, hux3⟩ :=
      h3 (W.x 2) (W.x 1) (W.x 3) (W.adj 1).symm (W.adj 2)
    obtain ⟨⟨g, hgU⟩, hgx, -⟩ :=
      pathRootGroup_regular_of_weissFree (n := 4) (by norm_num) hM hW
        (p := W.window (-2) 4) (W.window_noBack (-2) 4) (y := W.x 3) (y' := u)
        (by
          rw [ClosedGoodPath.window_apply W (-2) (s := 4) (by norm_num : (4 : ℕ) ≤ 4)]
          norm_num
          exact W.adj 2) hxu
        (by
          rw [ClosedGoodPath.window_apply W (-2) (s := 4) (by norm_num : (3 : ℕ) ≤ 4)]
          norm_num
          exact (W.ne_add_two 1).symm)
        hux1
    intro hbot
    have hg1 : (g : H) = 1 := by
      have hgU' : g ∈ Uminus := hgU
      rw [hbot] at hgU'
      exact Subgroup.mem_bot.mp hgU' 
    exact hux3 (by
      rw [← hgx]
      change g • W.x 3 = W.x 3
      rw [hg1, one_smul])
  intro hbot
  apply hUminus_ne_bot
  rw [eq_bot_iff]
  intro u hu
  have hmem := hUminus_le_G2 hu
  rw [hbot] at hmem
  exact Subgroup.mem_bot.mp hmem


end CFSG.Quasithin.Stroth.WeissDelta

end
