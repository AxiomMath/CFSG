module

public import CFSG.RankThree.GF2n.Smith81.S81TCond
public import CFSG.RankThree.GF2n.Smith81.S81BNCore
public import CFSG.RankThree.GF2n.Smith81.S81Lane28
public import CFSG.RankThree.GF2n.Smith81.S81BConj
public import CFSG.RankThree.GF2n.Smith81.S81WConjE45
public import CFSG.RankThree.GF2n.Smith81.S81WGeomE7
public import CFSG.RankThree.GF2n.Smith81.S81WGeomD6
public import CFSG.RankThree.GF2n.Smith81.S81WTacitE5
public import CFSG.RankThree.GF2n.Smith81.TiLemmaC

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom
  CFSG.RankThree.GF2n.Smith81.E7Model CFSG.RankThree.GF2n.Smith81.D6Spin
  CFSG.RankThree.GF2n.Smith81.MinuscT


@[expose] def ElemBoundE5Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), Smith1981Below (Nat.card G) →
    SmithECfg M Q Z B → InCaseE5 M Q Z B → ∀ [(Q.subgroupOf M).Normal], ∀ n : ℕ, Width Q Z n →
      ∀ A : Subgroup (↥M ⧸ Q.subgroupOf M), A ≤ bar M Q (Lgen M (LB M Q B)) →
        IsElemAbelian 2 A → Nat.card A ≤ Nat.card Z ^ (n - 1)

@[expose] def ElemBoundE4Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), Smith1981Below (Nat.card G) →
    SmithECfg M Q Z B → InCaseE4 M Q Z B → ∀ [(Q.subgroupOf M).Normal], ∀ n : ℕ, Width Q Z n →
      ∀ A : Subgroup (↥M ⧸ Q.subgroupOf M), A ≤ bar M Q (Lgen M (LB M Q B)) →
        IsElemAbelian 2 A → Nat.card A ≤ Nat.card Z ^ (n - 1)

@[expose] def Smith28aE5Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), Smith1981Below (Nat.card G) →
    SmithECfg M Q Z B → InCaseE5 M Q Z B → ∀ (X : Subgroup G) (x : G), Sit M Q Z X x →
      Q ⊓ QB X ≠ ⊥

@[expose] def Smith28aE4Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), Smith1981Below (Nat.card G) →
    SmithECfg M Q Z B → InCaseE4 M Q Z B → ∀ (X : Subgroup G) (x : G), Sit M Q Z X x →
      Q ⊓ QB X ≠ ⊥

section Eight

variable {G : Type} [Group G] [Finite G]

theorem smith28aE5_of_normQuot (hN : NormQuotE5Statement) (hB : ElemBoundE5Statement) :
    Smith28aE5Statement := by
  intro G _ _ M Q Z B IH hc h5 X x hs hQ
  haveI := hc.ctx.normal_Q_in_M
  obtain ⟨n, m, hw, hnm⟩ := hc.e.exists_width
  have h115 := smith115Statement_holds G M Q Z X x hs n hw hQ
  have hel : IsElemAbelian 2 (Lx M X) := h115.1.mono le_sup_right
  have hLQ : Lx M X ⊓ Q = ⊥ := by
    refine eq_bot_iff.mpr fun g hg => ?_
    have h1 : g ∈ Q ⊓ QB X := ⟨hg.2, hg.1.1⟩
    rw [hQ] at h1
    exact h1
  have hcard : Nat.card Z ^ n ≤ Nat.card ↥(Lx M X) := hs.card_Lx_ge hw
  have hLH0 : Lx M X ≤ H0 M Z := Lx_le_H0 hs (smith_1_12 hs)
  have hL2 : IsPGroup 2 (Lx M X) :=
    ((IsZConjugate.isPGroup_QB hs.hyp hs.conj).to_le (inf_le_left : Lx M X ≤ QB X))
  have hidx := hN G M Q Z B IH hc h5 (Lx M X) hLH0 hL2
  have hSM : Lx M X ⊓ Lgen M (LB M Q B) ≤ M := inf_le_left.trans inf_le_right
  have hSQ : (Lx M X ⊓ Lgen M (LB M Q B)) ⊓ Q = ⊥ :=
    eq_bot_iff.mpr fun g hg => by
      have : g ∈ Lx M X ⊓ Q := ⟨hg.1.1, hg.2⟩
      rw [hLQ] at this
      exact this
  have hSel : IsElemAbelian 2 (Lx M X ⊓ Lgen M (LB M Q B)) := hel.mono inf_le_left
  have hle : bar M Q (Lx M X ⊓ Lgen M (LB M Q B)) ≤ bar M Q (Lgen M (LB M Q B)) :=
    Subgroup.map_mono fun y hy => hy.2
  have hbound := hB G M Q Z B IH hc h5 n hw (bar M Q (Lx M X ⊓ Lgen M (LB M Q B))) hle
    ((hSel.subgroupOf M).map _)
  rw [card_bar_eq_of_inf_eq_bot hSM hSQ] at hbound
  have hq : 4 ≤ Nat.card Z := hc.ctx.hyp.q4
  have hn : 1 ≤ n := by have := hnm.ten_le; omega
  have hpow : Nat.card Z ^ n = Nat.card Z * Nat.card Z ^ (n - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hpos : 0 < Nat.card Z ^ (n - 1) := pow_pos (by omega) _
  nlinarith

theorem smith28aE4_of_normQuot (hN : NormQuotE4Statement) (hB : ElemBoundE4Statement) :
    Smith28aE4Statement := by
  intro G _ _ M Q Z B IH hc h4 X x hs hQ
  haveI := hc.ctx.normal_Q_in_M
  obtain ⟨n, m, hw, hnm⟩ := hc.e.exists_width
  have h115 := smith115Statement_holds G M Q Z X x hs n hw hQ
  have hel : IsElemAbelian 2 (Lx M X) := h115.1.mono le_sup_right
  have hLQ : Lx M X ⊓ Q = ⊥ := by
    refine eq_bot_iff.mpr fun g hg => ?_
    have h1 : g ∈ Q ⊓ QB X := ⟨hg.2, hg.1.1⟩
    rw [hQ] at h1
    exact h1
  have hcard : Nat.card Z ^ n ≤ Nat.card ↥(Lx M X) := hs.card_Lx_ge hw
  have hLH0 : Lx M X ≤ H0 M Z := Lx_le_H0 hs (smith_1_12 hs)
  have hL2 : IsPGroup 2 (Lx M X) :=
    ((IsZConjugate.isPGroup_QB hs.hyp hs.conj).to_le (inf_le_left : Lx M X ≤ QB X))
  have hidx := hN G M Q Z B IH hc h4 (Lx M X) hLH0 hL2
  have hSM : Lx M X ⊓ Lgen M (LB M Q B) ≤ M := inf_le_left.trans inf_le_right
  have hSQ : (Lx M X ⊓ Lgen M (LB M Q B)) ⊓ Q = ⊥ :=
    eq_bot_iff.mpr fun g hg => by
      have : g ∈ Lx M X ⊓ Q := ⟨hg.1.1, hg.2⟩
      rw [hLQ] at this
      exact this
  have hSel : IsElemAbelian 2 (Lx M X ⊓ Lgen M (LB M Q B)) := hel.mono inf_le_left
  have hle : bar M Q (Lx M X ⊓ Lgen M (LB M Q B)) ≤ bar M Q (Lgen M (LB M Q B)) :=
    Subgroup.map_mono fun y hy => hy.2
  have hbound := hB G M Q Z B IH hc h4 n hw (bar M Q (Lx M X ⊓ Lgen M (LB M Q B))) hle
    ((hSel.subgroupOf M).map _)
  rw [card_bar_eq_of_inf_eq_bot hSM hSQ] at hbound
  have hq : 4 ≤ Nat.card Z := hc.ctx.hyp.q4
  have hn : 1 ≤ n := by have := hnm.ten_le; omega
  have hpow : Nat.card Z ^ n = Nat.card Z * Nat.card Z ^ (n - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hpos : 0 < Nat.card Z ^ (n - 1) := pow_pos (by omega) _
  nlinarith

end Eight

theorem smith28E5_of_cond (h28a : Smith28aE5Statement) (hcond : E5_28CondStatement) :
    Smith28E5Statement := fun G _ _ M Q Z B IH hc h5 X x hs =>
  hcond G M Q Z B IH hc h5 X x hs (h28a G M Q Z B IH hc h5 X x hs)

theorem smith28E4_of_cond (h28a : Smith28aE4Statement) (hcond : E4_28CondStatement) :
    Smith28E4Statement := fun G _ _ M Q Z B IH hc h4 X x hs =>
  hcond G M Q Z B IH hc h4 X x hs (h28a G M Q Z B IH hc h4 X x hs)

section Nonfusion

variable {G : Type} [Group G]

private theorem exists_conj_of_isZConjugate_T {Z A X : Subgroup G} (hA : IsZConjugate Z A)
    (hX : IsZConjugate Z X) : ∃ g : G, X = conjSubgroup g A := by
  obtain ⟨y, rfl⟩ := hA
  obtain ⟨g₀, rfl⟩ := hX
  refine ⟨g₀ * y⁻¹, ?_⟩
  rw [← conjSubgroup_mul, inv_mul_cancel_right]

private theorem exists_sit_of_isConj_T {M Q Z : Subgroup G} (H : StrothHyp M Q Z) {z x : G}
    (hz : z ∈ Z) (hz1 : z ≠ 1) (hzx : IsConj z x) (hM : x ∈ M) (hQ : x ∉ Q) :
    ∃ X : Subgroup G, Sit M Q Z X x := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp hzx
  exact ⟨_, Sit.of_conj H hz hz1 hM hQ⟩

end Nonfusion

section NonfusionE5

variable {G : Type} [Group G] [Finite G]

theorem le_QB_of_sum_mem_E5 (hFE1 : Smith24E5UniformStatement)
    (hLine : ∀ (K : Type) [Field K] [Finite K] [CharP K 2],
      MinuscLine (EAut K) (w0 : V K) (rootRad7 K))
    (hTacit : ETacitE5Statement) (h34 : Stroth34Statement)
    {M Q Z B : Subgroup G} (IH : Smith1981Below (Nat.card G)) (hc : SmithECfg M Q Z B)
    (h5 : InCaseE5 M Q Z B) {X Y D : Subgroup G} (hX : Ctx M Q Z X) (hY : Ctx M Q Z Y)
    (hD : Ctx M Q Z D) {x y : G} (hx : x ∈ X) (hy : y ∈ Y) (hx1 : x ≠ 1) (hy1 : y ≠ 1)
    (hxy : x * y ∈ D) (hxy1 : x * y ≠ 1) (hne : Y ⊔ Z ≠ X ⊔ Z) : Y ≤ QB X := by
  obtain ⟨K, _, _, hK2, γ, M₀, hg⟩ := stroth_globalModelData hc.ctx.hyp
  obtain ⟨ψ, φ, d⟩ := hFE1 G M Q Z B IH hc.toRemCfg h5 K γ M₀ hg
  have hw : Width Q Z 28 := by
    obtain ⟨t, -, hQ, -⟩ := h5
    simpa [Width] using hQ
  have hTac := hTacit G M Q Z B IH hc h5 X hX
  have hcard : Nat.card ↥(Q ⊓ QB X) = Nat.card Z ^ (28 + 1) :=
    (stroth_3_5 h34 hX hw (by norm_num) hTac.1 hTac.2).2.2.2
  exact d.le_QB_of_sum_mem hg e7MinuscGeom (hLine K) hX hY hD hcard hx hy hx1 hy1 hxy hxy1 hne

theorem smith212ENonfusedE5_of_cond (hFE1 : Smith24E5UniformStatement)
    (hLine : ∀ (K : Type) [Field K] [Finite K] [CharP K 2],
      MinuscLine (EAut K) (w0 : V K) (rootRad7 K))
    (hTacit : ETacitE5Statement) (h34 : Stroth34Statement)
    (h28a : Smith28aE5Statement) (hcond : E5_28CondStatement) :
    Smith212ENonfusedE5Statement := by
  intro G _ _ M Q Z B IH hc h5 z hz hz1 x hxM hxQ hzx w hw hw1 hfus
  have H : StrothHyp M Q Z := hc.ctx.hyp
  have hZQ : Z ≤ Q := H.Z_normal.1
  obtain ⟨X, hs⟩ := exists_sit_of_isConj_T H hz hz1 hzx hxM hxQ
  have hQX : Q ⊓ QB X ≠ ⊥ := h28a G M Q Z B IH hc h5 X x hs
  obtain ⟨A, hAc, hAQ, hAZ, hAX, hAXne, -⟩ :=
    smith29_of_exists hs (hcond G M Q Z B IH hc h5 X x hs hQX)
  obtain ⟨y, hAy, hQBA, -⟩ := hAc.QB_eq H
  have hcA : SmithECfg (conjSubgroup y M) (conjSubgroup y Q) A (conjSubgroup y B) := by
    rw [hAy]
    exact hc.conj y
  have h5A : InCaseE5 (conjSubgroup y M) (conjSubgroup y Q) A (conjSubgroup y B) := by
    rw [hAy]
    exact h5.conj y
  have hHA := hcA.ctx.hyp
  have hXz : IsZConjugate Z X := hs.conj
  have hZz : IsZConjugate Z Z := IsZConjugate.self Z
  have hXQ : X ≤ QB A := (hAc.le_QB_iff H hXz).mpr hAX
  have hZQA : Z ≤ QB A := (hAc.le_QB_iff H hZz).mpr (by rw [H.QB_Z]; exact hAQ)
  have hx1 : x ≠ 1 := hs.ne_one
  have hxw1 : x * w ≠ 1 := by
    intro h
    apply hxQ
    rw [eq_inv_of_mul_eq_one_left h]
    exact Q.inv_mem (hZQ hw)
  obtain ⟨D, hDz, hxwD⟩ := exists_isZConjugate_mem hz (hzx.trans hfus)
  have hDQ : D ≤ QB A :=
    hAc.le_QB_of_mem H hDz hxw1 hxwD ((QB A).mul_mem (hXQ hs.mem) (hZQA hw))
  have hDA : D ≠ A := by
    intro h
    have h1 : x * w ∈ Q := hAQ (h ▸ hxwD)
    apply hxQ
    simpa using Q.mul_mem h1 (Q.inv_mem (hZQ hw))
  have hXc : Ctx (conjSubgroup y M) (conjSubgroup y Q) A X :=
    ⟨hHA, exists_conj_of_isZConjugate_T hAc hXz, by rw [← hQBA]; exact hXQ, hAXne.symm⟩
  have hZc : Ctx (conjSubgroup y M) (conjSubgroup y Q) A Z :=
    ⟨hHA, exists_conj_of_isZConjugate_T hAc hZz, by rw [← hQBA]; exact hZQA, hAZ.symm⟩
  have hDc : Ctx (conjSubgroup y M) (conjSubgroup y Q) A D :=
    ⟨hHA, exists_conj_of_isZConjugate_T hAc hDz, by rw [← hQBA]; exact hDQ, hDA⟩
  have hne : Z ⊔ A ≠ X ⊔ A := by
    intro h
    have hx' : x ∈ Z ⊔ A := h ▸ (Subgroup.mem_sup_left hs.mem : x ∈ X ⊔ A)
    exact hxQ ((sup_le hZQ hAQ : Z ⊔ A ≤ Q) hx')
  have hZX : Z ≤ QB X :=
    le_QB_of_sum_mem_E5 hFE1 hLine hTacit h34 IH hcA h5A hXc hZc hDc hs.mem hw hx1 hw1 hxwD
      hxw1 hne
  have hbot := Z_inf_QB_eq_bot hs (smith_1_12 hs)
  have hmem : w ∈ Z ⊓ QB X := ⟨hw, hZX hw⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hw1 hmem

end NonfusionE5

section NonfusionE4

variable {G : Type} [Group G] [Finite G]

theorem le_QB_of_sum_mem_E4 (hFE1 : Smith24E4UniformStatement)
    (hLine : ∀ (K : Type) [Field K] [Finite K] [CharP K 2],
      MinuscLine (EAut0 K) (p0 K) (rootRad0 K))
    (hTacit : ETacitE4Statement) (h34 : Stroth34Statement)
    {M Q Z B : Subgroup G} (IH : Smith1981Below (Nat.card G)) (hc : SmithECfg M Q Z B)
    (h4 : InCaseE4 M Q Z B) {X Y D : Subgroup G} (hX : Ctx M Q Z X) (hY : Ctx M Q Z Y)
    (hD : Ctx M Q Z D) {x y : G} (hx : x ∈ X) (hy : y ∈ Y) (hx1 : x ≠ 1) (hy1 : y ≠ 1)
    (hxy : x * y ∈ D) (hxy1 : x * y ≠ 1) (hne : Y ⊔ Z ≠ X ⊔ Z) : Y ≤ QB X := by
  obtain ⟨K, _, _, hK2, γ, M₀, hg⟩ := stroth_globalModelData hc.ctx.hyp
  obtain ⟨ψ, φ, d⟩ := hFE1 G M Q Z B IH hc.toRemCfg h4 K γ M₀ hg
  have hw : Width Q Z 16 := by
    obtain ⟨t, -, hQ, -⟩ := h4
    simpa [Width] using hQ
  have hTac := hTacit G M Q Z B IH hc h4 X hX
  have hcard : Nat.card ↥(Q ⊓ QB X) = Nat.card Z ^ (16 + 1) :=
    (stroth_3_5 h34 hX hw (by norm_num) hTac.1 hTac.2).2.2.2
  exact d.le_QB_of_sum_mem hg d6MinuscGeom (hLine K) hX hY hD hcard hx hy hx1 hy1 hxy hxy1 hne

theorem smith212ENonfusedE4_of_cond (hFE1 : Smith24E4UniformStatement)
    (hLine : ∀ (K : Type) [Field K] [Finite K] [CharP K 2],
      MinuscLine (EAut0 K) (p0 K) (rootRad0 K))
    (hTacit : ETacitE4Statement) (h34 : Stroth34Statement)
    (h28a : Smith28aE4Statement) (hcond : E4_28CondStatement) :
    Smith212ENonfusedE4Statement := by
  intro G _ _ M Q Z B IH hc h4 z hz hz1 x hxM hxQ hzx w hw hw1 hfus
  have H : StrothHyp M Q Z := hc.ctx.hyp
  have hZQ : Z ≤ Q := H.Z_normal.1
  obtain ⟨X, hs⟩ := exists_sit_of_isConj_T H hz hz1 hzx hxM hxQ
  have hQX : Q ⊓ QB X ≠ ⊥ := h28a G M Q Z B IH hc h4 X x hs
  obtain ⟨A, hAc, hAQ, hAZ, hAX, hAXne, -⟩ :=
    smith29_of_exists hs (hcond G M Q Z B IH hc h4 X x hs hQX)
  obtain ⟨y, hAy, hQBA, -⟩ := hAc.QB_eq H
  have hcA : SmithECfg (conjSubgroup y M) (conjSubgroup y Q) A (conjSubgroup y B) := by
    rw [hAy]
    exact hc.conj y
  have h4A : InCaseE4 (conjSubgroup y M) (conjSubgroup y Q) A (conjSubgroup y B) := by
    rw [hAy]
    exact h4.conj y
  have hHA := hcA.ctx.hyp
  have hXz : IsZConjugate Z X := hs.conj
  have hZz : IsZConjugate Z Z := IsZConjugate.self Z
  have hXQ : X ≤ QB A := (hAc.le_QB_iff H hXz).mpr hAX
  have hZQA : Z ≤ QB A := (hAc.le_QB_iff H hZz).mpr (by rw [H.QB_Z]; exact hAQ)
  have hx1 : x ≠ 1 := hs.ne_one
  have hxw1 : x * w ≠ 1 := by
    intro h
    apply hxQ
    rw [eq_inv_of_mul_eq_one_left h]
    exact Q.inv_mem (hZQ hw)
  obtain ⟨D, hDz, hxwD⟩ := exists_isZConjugate_mem hz (hzx.trans hfus)
  have hDQ : D ≤ QB A :=
    hAc.le_QB_of_mem H hDz hxw1 hxwD ((QB A).mul_mem (hXQ hs.mem) (hZQA hw))
  have hDA : D ≠ A := by
    intro h
    have h1 : x * w ∈ Q := hAQ (h ▸ hxwD)
    apply hxQ
    simpa using Q.mul_mem h1 (Q.inv_mem (hZQ hw))
  have hXc : Ctx (conjSubgroup y M) (conjSubgroup y Q) A X :=
    ⟨hHA, exists_conj_of_isZConjugate_T hAc hXz, by rw [← hQBA]; exact hXQ, hAXne.symm⟩
  have hZc : Ctx (conjSubgroup y M) (conjSubgroup y Q) A Z :=
    ⟨hHA, exists_conj_of_isZConjugate_T hAc hZz, by rw [← hQBA]; exact hZQA, hAZ.symm⟩
  have hDc : Ctx (conjSubgroup y M) (conjSubgroup y Q) A D :=
    ⟨hHA, exists_conj_of_isZConjugate_T hAc hDz, by rw [← hQBA]; exact hDQ, hDA⟩
  have hne : Z ⊔ A ≠ X ⊔ A := by
    intro h
    have hx' : x ∈ Z ⊔ A := h ▸ (Subgroup.mem_sup_left hs.mem : x ∈ X ⊔ A)
    exact hxQ ((sup_le hZQ hAQ : Z ⊔ A ≤ Q) hx')
  have hZX : Z ≤ QB X :=
    le_QB_of_sum_mem_E4 hFE1 hLine hTacit h34 IH hcA h4A hXc hZc hDc hs.mem hw hx1 hw1 hxwD
      hxw1 hne
  have hbot := Z_inf_QB_eq_bot hs (smith_1_12 hs)
  have hmem : w ∈ Z ⊓ QB X := ⟨hw, hZX hw⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hw1 hmem

end NonfusionE4

section Assembly


theorem smith28E5_of_uniform (hFE1 : Smith24E5UniformStatement) (hForm : Smith24E5FormStatement)
    (hN : NormQuotE5Statement) (hB : ElemBoundE5Statement) (hCl : E5InvolClassesStatement) :
    Smith28E5Statement :=
  smith28E5_of_cond (smith28aE5_of_normQuot hN hB) (e528Cond_of_uniform hFE1 hForm hN hCl)

theorem smith28E4_of_uniform (hFE1 : Smith24E4UniformStatement) (hForm : Smith24E4FormStatement)
    (hN : NormQuotE4Statement) (hB : ElemBoundE4Statement) (hCl : E4InvolClassesStatement) :
    Smith28E4Statement :=
  smith28E4_of_cond (smith28aE4_of_normQuot hN hB) (e428Cond_of_uniform hFE1 hForm hN hCl)

theorem smith212ENonfusedE5_of_uniform (hFE1 : Smith24E5UniformStatement)
    (hForm : Smith24E5FormStatement) (hN : NormQuotE5Statement) (hB : ElemBoundE5Statement)
    (hCl : E5InvolClassesStatement)
    (hLine : ∀ (K : Type) [Field K] [Finite K] [CharP K 2],
      MinuscLine (EAut K) (w0 : V K) (rootRad7 K))
    (hGen : StrothGenByBStatement) (h34 : Stroth34Statement) :
    Smith212ENonfusedE5Statement :=
  smith212ENonfusedE5_of_cond hFE1 hLine (eTacitE5_of_uniform hFE1 hGen) h34
    (smith28aE5_of_normQuot hN hB) (e528Cond_of_uniform hFE1 hForm hN hCl)

theorem smith212ENonfusedE4_of_uniform (hFE1 : Smith24E4UniformStatement)
    (hForm : Smith24E4FormStatement) (hN : NormQuotE4Statement) (hB : ElemBoundE4Statement)
    (hCl : E4InvolClassesStatement)
    (hLine : ∀ (K : Type) [Field K] [Finite K] [CharP K 2],
      MinuscLine (EAut0 K) (p0 K) (rootRad0 K))
    (hGen : StrothGenByBStatement) (h34 : Stroth34Statement) :
    Smith212ENonfusedE4Statement :=
  smith212ENonfusedE4_of_cond hFE1 hLine (eTacitE4_of_uniform hFE1 hGen) h34
    (smith28aE4_of_normQuot hN hB) (e428Cond_of_uniform hFE1 hForm hN hCl)

end Assembly

end CFSG.RankThree.GF2n.Smith81
