module

public import CFSG.RankThree.GF2n.Stroth80.Sec103
public import CFSG.RankThree.GF2n.Stroth80.Sec10AuxFrame
public import CFSG.RankThree.GF2n.Stroth80.Sec10ConjFix
public import CFSG.RankThree.GF2n.Stroth80.Sec10RootChoice

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Sit.ctx_conj {Y : Subgroup G} {t : G} (hs : Sit M Q Z Y t) {h : G}
    (hQ : h * t * h⁻¹ ∈ Q) (hZ : h * t * h⁻¹ ∉ Z) : Ctx M Q Z (conjSubgroup h Y) := by
  obtain ⟨g, hg⟩ := hs.conj
  have hX : conjSubgroup h Y = conjSubgroup (h * g) Z := by rw [hg, conjSubgroup_conjSubgroup]
  have hmem : h * t * h⁻¹ ∈ conjSubgroup h Y := mem_conjSubgroup.mpr (by
    rw [show h⁻¹ * (h * t * h⁻¹) * h = t by group]; exact hs.mem)
  have hne : h * t * h⁻¹ ≠ 1 := fun h1 => hs.ne_one (by
    calc t = h⁻¹ * (h * t * h⁻¹) * h := by group
      _ = 1 := by rw [h1]; group)
  rw [hX] at hmem ⊢
  obtain ⟨g', hg'Q, hg'⟩ := stroth_2_6 hs.hyp hQ hZ
    ⟨h * g, (h * g)⁻¹ * (h * t * h⁻¹) * (h * g), mem_conjSubgroup.mp hmem, by group⟩
  have heq := conjSubgroup_eq_of_mem_ne_one hs.hyp hne hg' hmem
  refine ⟨hs.hyp, ⟨h * g, rfl⟩, heq ▸ hg'Q, fun hXZ => hZ ?_⟩
  rw [hXZ] at hmem
  exact hmem

theorem Good101.false_of_conj_fix (h34 : Stroth34Statement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {t : G} (ht : Good101 M Q Z B t) {Y : Subgroup G} (hs : Sit M Q Z Y t) {c : G}
    (hcQ : c ∈ Q) (hcW : c ∉ Wt Q (Vt M (LB M Q B) B Z t)) {h : G}
    (hht : h * t * h⁻¹ = t * (c * t * c⁻¹)) {α s : G} (hα : α ∈ Q ⊓ QB Y) (hsY : s ∈ Y)
    (hs1 : s ≠ 1) (hfix : h * (α * s) * h⁻¹ = α * s) : False := by
  have hx : h * t * h⁻¹ = ⁅t, c⁆ := by
    rw [hht, conj_eq_mul_comm_of_mul_self hs.x_sq c, ← mul_assoc, hs.x_sq, one_mul]
  have hxQ : ⁅t, c⁆ ∈ Q := by
    rw [← commutatorElement_inv]
    exact Q.inv_mem (hc.comm_mem_Q ht.2.1 hcQ)
  have hxV : ⁅t, c⁆ ∉ Vt M (LB M Q B) B Z t := fun hV =>
    ht.comm_not_mem_Tt h34 H hcQ hcW (ht.Vt_le_Tt h34 H hV)
  have hX := Sit.ctx_conj hs (hx ▸ hxQ) (hx ▸ fun hZ => hxV (sec39_Z_le_Vt hZ))
  obtain ⟨μ, hμ, hμX⟩ := H.rootTrans h34 hspread _ hX
  have hfix' : h⁻¹ * (α * s) * h = α * s := by
    calc h⁻¹ * (α * s) * h = h⁻¹ * (h * (α * s) * h⁻¹) * h := by rw [hfix]
      _ = α * s := by group
  have hrQB : α * s ∈ QB (conjSubgroup h Y) := by
    rw [QB_conj, mem_conjSubgroup, hfix']
    exact (QB Y).mul_mem hα.2 (IsZConjugate.le_QB_self hs.hyp hs.conj hsY)
  have hrX : α * s ∈ QB (conjSubgroup h Y) ⊓ M :=
    ⟨hrQB, M.mul_mem (hc.hyp.Q_normal.1 hα.1) ((smith_1_12 hs).1 hsY).1⟩
  have hsL : s ∈ conjSubgroup μ (LB M Q B) := by
    rw [← hc.LB_conj hμ, hμX, show s = α⁻¹ * (α * s) by group]
    exact (LB M Q _).mul_mem (Subgroup.mem_sup_left (Q.inv_mem hα.1))
      (Subgroup.mem_sup_right hrX)
  have hXV := sec39_conjB_le_Vt (B := B) (Z := Z) hμ hsL
  rw [ht.Vt_eq_of_mem_root h34 hspread H hs hsY hs1, hμX] at hXV
  apply hxV
  apply hXV
  rw [← hx, mem_conjSubgroup, show h⁻¹ * (h * t * h⁻¹) * h = t by group]
  exact hs.mem

private theorem not_mem_Vt_conj_frame (h34 : Stroth34Statement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {t : G} (ht : Good101 M Q Z B t) {Y : Subgroup G} (hs : Sit M Q Z Y t) {c : G}
    (hcQ : c ∈ Q)
    {hc' : Ctx (Subgroup.normalizer (conjSubgroup c Y : Set G)) (QB (conjSubgroup c Y))
      (conjSubgroup c Y) B} (H' : Sec10Hyp hc' n)
    (ht' : Good101 (Subgroup.normalizer (conjSubgroup c Y : Set G)) (QB (conjSubgroup c Y))
      (conjSubgroup c Y) B t) {α : G} (hα : α ∈ Q ⊓ QB Y)
    (hαV : α ∉ Vt M (LB M Q B) B Z t) :
    α ∉ Vt (Subgroup.normalizer (conjSubgroup c Y : Set G))
      (LB (Subgroup.normalizer (conjSubgroup c Y : Set G)) (QB (conjSubgroup c Y)) B) B
      (conjSubgroup c Y) t := by
  intro hαV'
  obtain ⟨g, hg⟩ := hs.conj
  have hY' : conjSubgroup c Y = conjSubgroup (c * g) Z := by rw [hg, conjSubgroup_conjSubgroup]
  have hαY : α ∉ conjSubgroup c Y := fun hY => hαV (by
    have h1 : α ∈ conjSubgroup c Y ⊓ Q := ⟨hY, hα.1⟩
    rw [conjSubgroup_inf_eq_bot hcQ hs.X_inf_Q, Subgroup.mem_bot] at h1
    rw [h1]
    exact Subgroup.one_mem _)
  exact hαV (ht.mem_Vt_of_isRoot h34 hspread H hs hα
    ((isRoot_conj_iff hY').mp (Good101.isRoot_of_mem_Vt H' ht' hαV' hαY)))

theorem Good101.inf_QB_le_Vt_of_not_caseA_of_three_le (h34 : Stroth34Statement)
    (hspread : StrothNoA2SpreadStatement) (hA : Stroth103CaseAStatement) {hc : Ctx M Q Z B}
    {n : ℕ} (H : Sec10Hyp hc n) {t : G} (ht : Good101 M Q Z B t) {Y : Subgroup G}
    (hs : Sit M Q Z Y t) (hB : ¬ CaseA Q Z t) {m : ℕ} (hm : SLMNat hc t m) (hm3 : 3 ≤ m) :
    Q ⊓ QB Y ≤ Vt M (LB M Q B) B Z t := by
  intro α hα
  by_contra hαV
  obtain ⟨c, hcQ, hcα, hcB, hcW⟩ := hm.exists_mem_centralizer_not_mem_Wt hm3 hα.1
  obtain ⟨D, hD, hDY, hYD, hDc, hDB⟩ :=
    ht.exists_root_group_centralizer h34 hspread H hs hm hm3 hcQ
  obtain ⟨hc', H', ht', hs', μ, hμ, hμD⟩ :=
    ht.exists_conj_frame h34 hspread H hs hB hcQ hcB hcW hD hDY hYD hDc hDB
  have hα' : α ∈ QB (conjSubgroup c Y) ⊓ QB Y := ⟨mem_QB_conj_of_mem_centralizer hα.2
    (Subgroup.mem_centralizer_singleton_iff.mpr hcα.symm), hα.2⟩
  have hαV' := not_mem_Vt_conj_frame h34 hspread H ht hs hcQ H' ht' hα hαV
  have hB' : ¬ CaseA (QB (conjSubgroup c Y)) (conjSubgroup c Y) t := fun hA' =>
    hαV' (hA G _ _ _ B hc' n t Y H' ht' hs' hA' hα')
  have hαU' : α ∉ Ut (QB (conjSubgroup c Y)) (conjSubgroup c Y) t := fun hU =>
    hαV' (ht'.inf_QB_inf_Ut_le_Vt_of_not_caseA h34 hspread H' hs' hB' ⟨hα', hU⟩)
  have hz : c * t * c⁻¹ ∈ conjSubgroup c Y := mem_conjSubgroup.mpr (by
    rw [show c⁻¹ * (c * t * c⁻¹) * c = t by group]; exact hs.mem)
  have hz1 : c * t * c⁻¹ ≠ 1 := fun h1 => hs.ne_one (by
    calc t = c⁻¹ * (c * t * c⁻¹) * c := by group
      _ = 1 := by rw [h1]; group)
  have hBY : B ≤ QB Y := hc.hyp.le_QB_of_mem_QB hc.conj hs.conj hs.mem hs.ne_one ht.2.2.2.1
  obtain ⟨h, -, hht, s, hsY, hs1, hfix⟩ := H'.exists_conj_fix_of_not_caseA h34 hs' hB' hα' hαU'
    hμ hBY (by rw [hμD]; exact hDY) (fun h => hDB (le_of_eq (hμD.symm.trans h.symm))) hz hz1
  exact ht.false_of_conj_fix h34 hspread H hs hcQ hcW hht hα hsY hs1 hfix

theorem stroth_10_3_caseB (h34 : Stroth34Statement) (hspread : StrothNoA2SpreadStatement)
    (hA : Stroth103CaseAStatement) : Stroth103CaseBStatement := by
  intro G _ _ M Q Z B hc n H hno t Y ht hs hB
  obtain ⟨m, hm2, hm⟩ := SLlike.exists_SLMNat (H.slLike ht)
  have hm3 : 3 ≤ m := by
    rcases Nat.lt_or_ge m 3 with h | h
    · exact absurd (show m = 2 by omega ▸ hm) (hno t ht)
    · exact h
  exact ht.inf_QB_le_Vt_of_not_caseA_of_three_le h34 hspread hA H hs hB hm hm3

end CFSG.RankThree.GF2n.Stroth80
