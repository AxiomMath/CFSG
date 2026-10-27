module

public import CFSG.RankThree.GF2n.Stroth80.Sec103Root
public import CFSG.RankThree.GF2n.Stroth80.Sec10Four

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Good101.mem_Vt_of_conj (h34 : Stroth34Statement) (hspread : StrothNoA2SpreadStatement)
    {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n) {t : G} (ht : Good101 M Q Z B t)
    {Y : Subgroup G} (hs : Sit M Q Z Y t) {α : G} (hα : α ∈ Q ⊓ QB Y)
    (hconj : ∃ g : G, g * t * g⁻¹ = t * α) : α ∈ Vt M (LB M Q B) B Z t := by
  by_cases hα1 : α = 1
  · rw [hα1]; exact (Vt M (LB M Q B) B Z t).one_mem
  exact ht.mem_Vt_of_isRoot h34 hspread H hs hα (Sit.isRoot_of_conj hs hα hα1 hconj)

theorem Good101.exists_conj_of_mem_Vt (h34 : Stroth34Statement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {t : G} (ht : Good101 M Q Z B t) {Y : Subgroup G} (hs : Sit M Q Z Y t) {a : G}
    (ha : a ∈ Q ⊓ QB Y) (haV : a ∈ Vt M (LB M Q B) B Z t) :
    ∃ k ∈ Q, k * t * k⁻¹ = t * a := by
  by_cases ha1 : a = 1
  · exact ⟨1, Q.one_mem, by rw [ha1]; group⟩
  have haZ : a ∉ Z := fun hZ => ha1 (by
    have : a ∈ Z ⊓ QB Y := ⟨hZ, ha.2⟩
    rwa [Z_inf_QB_eq_bot hs (smith_1_12 hs), Subgroup.mem_bot] at this)
  exact ht.exists_conj_of_isRoot h34 hspread H hs ha (ht.isRoot_of_mem_Vt H haV haZ)

theorem Good101.good103_of_le_Vt (h34 : Stroth34Statement) (hspread : StrothNoA2SpreadStatement)
    {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n) {t : G} (ht : Good101 M Q Z B t)
    {Y : Subgroup G} (hs : Sit M Q Z Y t) (hle : Q ⊓ QB Y ≤ Vt M (LB M Q B) B Z t) :
    Good103 M Q Z B t := by
  refine ⟨ht, le_antisymm (H.Vt_le (stroth_5_7 h34 hspread) ht) ?_⟩
  rw [inf_QB_zpowers_eq hs]
  exact sup_le hle sec39_Z_le_Vt

theorem Sit.of_mem_root {Y : Subgroup G} {t : G} (hs : Sit M Q Z Y t) {y : G} (hy : y ∈ Y)
    (hy1 : y ≠ 1) : Sit M Q Z Y y := by
  have h12 := smith_1_12 hs
  refine ⟨hs.hyp, hs.conj, hy, hy1, (Subgroup.mem_inf.mp (h12.1 hy)).1, fun hyQ => hy1 ?_⟩
  have : y ∈ Y ⊓ Q := ⟨hy, hyQ⟩
  rwa [h12.2, Subgroup.mem_bot] at this

theorem Good101.root_le_QB (hc : Ctx M Q Z B) {t : G} (ht : Good101 M Q Z B t)
    {Y : Subgroup G} (hs : Sit M Q Z Y t) : Y ≤ QB B := by
  have hBY : B ≤ QB Y := hc.hyp.le_QB_of_mem_QB hc.conj hs.conj hs.mem hs.ne_one ht.2.2.2.1
  have hne : B ≠ Y := by
    intro h
    have htB : t ∈ B := by rw [h]; exact hs.mem
    exact ht.2.2.1 (hc.le htB)
  exact hc.hyp.le_QB_of_le_QB hc.conj hs.conj hne hBY

theorem Good101.mem_conj_LB_of_mem_root (h34 : Stroth34Statement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {t : G} (ht : Good101 M Q Z B t) {Y : Subgroup G} (hs : Sit M Q Z Y t) {y : G}
    (hy : y ∈ Y) {m : G} (hm : m ∈ M) (htm : t ∈ conjSubgroup m (LB M Q B)) :
    y ∈ conjSubgroup m (LB M Q B) := by
  obtain ⟨w, hwQ, a, ha, ha1, haQB⟩ :=
    H.exists_conj_mem_QB_zpowers (stroth_5_7 h34 hspread) ht hm htm
  have hwm : w * m ∈ M := M.mul_mem (hc.hyp.Q_normal.1 hwQ) hm
  have hX : Ctx M Q Z (conjSubgroup (w * m) B) := hc.conj_of_mem hwm
  have htX : t ∈ QB (conjSubgroup (w * m) B) := hX.mem_QB_of_inf_QB_zpowers hs ha ha1 haQB
  have hXY : conjSubgroup (w * m) B ≤ QB Y :=
    hc.hyp.le_QB_of_mem_QB hX.conj hs.conj hs.mem hs.ne_one htX
  have hne : conjSubgroup (w * m) B ≠ Y := by
    intro h
    have htX' : t ∈ conjSubgroup (w * m) B := by rw [h]; exact hs.mem
    exact ht.2.2.1 (hX.le htX')
  have hYX : Y ≤ QB (conjSubgroup (w * m) B) := hc.hyp.le_QB_of_le_QB hX.conj hs.conj hne hXY
  have hyM : y ∈ M := (Subgroup.mem_inf.mp ((smith_1_12 hs).1 hy)).1
  have hwLB : w ∈ conjSubgroup m (LB M Q B) := by
    have h1 : w ∈ conjSubgroup m Q := by rw [hc.conj_Q_eq hm]; exact hwQ
    exact Subgroup.map_mono sec39_Q_le_LB h1
  have hLB : LB M Q (conjSubgroup (w * m) B) = conjSubgroup m (LB M Q B) := by
    rw [hc.LB_conj hwm, conjSubgroup_mul,
      conjSubgroup_eq_self_iff.mpr (Subgroup.le_normalizer hwLB)]
  rw [← hLB]
  exact Subgroup.mem_sup_right ⟨hYX hy, hyM⟩

theorem Good101.of_mem_root_good101 (h34 : Stroth34Statement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {t : G} (ht : Good101 M Q Z B t) {Y : Subgroup G} (hs : Sit M Q Z Y t) {y : G}
    (hy : y ∈ Y) (hy1 : y ≠ 1) : Good101 M Q Z B y := by
  have hsy := Sit.of_mem_root hs hy hy1
  obtain ⟨g, hg⟩ := hs.conj
  have hy0 : g⁻¹ * y * g ∈ Z := by
    have h := hy
    rw [hg] at h
    exact mem_conjSubgroup.mp h
  refine ⟨⟨g, g⁻¹ * y * g, hy0, fun h1 => hy1 ?_, by group⟩, hsy.memM, hsy.notQ,
    ht.root_le_QB hc hs hy, fun hR => ht.2.2.2.2 ?_⟩
  · calc y = g * (g⁻¹ * y * g) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group
  · refine le_antisymm (le_trans ?_ hR.le) (le_Rt (LB M Q B) ht.mem_LB)
    refine iSup₂_le fun m hm => iSup_le fun htm => ?_
    exact le_iSup₂_of_le m hm (le_iSup_of_le (ht.mem_conj_LB_of_mem_root h34 hspread H hs hy
      hm htm) le_rfl)

theorem Good101.mem_conj_LB_iff_of_mem_root (h34 : Stroth34Statement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {t : G} (ht : Good101 M Q Z B t) {Y : Subgroup G} (hs : Sit M Q Z Y t) {y : G}
    (hy : y ∈ Y) (hy1 : y ≠ 1) {m : G} (hm : m ∈ M) :
    y ∈ conjSubgroup m (LB M Q B) ↔ t ∈ conjSubgroup m (LB M Q B) :=
  ⟨fun hym => (ht.of_mem_root_good101 h34 hspread H hs hy hy1).mem_conj_LB_of_mem_root h34
    hspread H (Sit.of_mem_root hs hy hy1) hs.mem hm hym,
   fun htm => ht.mem_conj_LB_of_mem_root h34 hspread H hs hy hm htm⟩

theorem Good101.Rt_eq_of_mem_root (h34 : Stroth34Statement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {t : G} (ht : Good101 M Q Z B t) {Y : Subgroup G} (hs : Sit M Q Z Y t) {y : G}
    (hy : y ∈ Y) (hy1 : y ≠ 1) : Rt M (LB M Q B) y = Rt M (LB M Q B) t :=
  iSup_congr fun _ => iSup_congr fun hm =>
    iSup_congr_Prop (ht.mem_conj_LB_iff_of_mem_root h34 hspread H hs hy hy1 hm) fun _ => rfl

theorem Good101.Vt_eq_of_mem_root (h34 : Stroth34Statement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {t : G} (ht : Good101 M Q Z B t) {Y : Subgroup G} (hs : Sit M Q Z Y t) {y : G}
    (hy : y ∈ Y) (hy1 : y ≠ 1) : Vt M (LB M Q B) B Z y = Vt M (LB M Q B) B Z t :=
  congrArg (Z ⊔ ·) <| iSup_congr fun _ => iSup_congr fun hm =>
    iSup_congr_Prop (ht.mem_conj_LB_iff_of_mem_root h34 hspread H hs hy hy1 hm) fun _ => rfl

theorem Good101.CN_eq_of_mem_root (h34 : Stroth34Statement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {t : G} (ht : Good101 M Q Z B t) {Y : Subgroup G} (hs : Sit M Q Z Y t) {y : G}
    (hy : y ∈ Y) (hy1 : y ≠ 1) : hc.CN y = hc.CN t := by
  ext r
  change r ∈ CNt M (LB M Q B) B Z y ↔ r ∈ CNt M (LB M Q B) B Z t
  simp only [CNt, ht.Rt_eq_of_mem_root h34 hspread H hs hy hy1,
    ht.Vt_eq_of_mem_root h34 hspread H hs hy hy1]

theorem SLMNat.iff_of_mem_root (h34 : Stroth34Statement) (hspread : StrothNoA2SpreadStatement)
    {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n) {t : G} (ht : Good101 M Q Z B t)
    {Y : Subgroup G} (hs : Sit M Q Z Y t) {y : G} (hy : y ∈ Y) (hy1 : y ≠ 1) {m : ℕ} :
    SLMNat hc y m ↔ SLMNat hc t m := by
  unfold SLMNat
  rw [ht.Rt_eq_of_mem_root h34 hspread H hs hy hy1, ht.Vt_eq_of_mem_root h34 hspread H hs hy hy1,
    ht.CN_eq_of_mem_root h34 hspread H hs hy hy1]

theorem Good103.iff_of_mem_root (h34 : Stroth34Statement) (hspread : StrothNoA2SpreadStatement)
    {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n) {t : G} (ht : Good101 M Q Z B t)
    {Y : Subgroup G} (hs : Sit M Q Z Y t) {y : G} (hy : y ∈ Y) (hy1 : y ≠ 1) :
    Good103 M Q Z B y ↔ Good103 M Q Z B t := by
  have hsy := Sit.of_mem_root hs hy hy1
  unfold Good103
  rw [ht.Vt_eq_of_mem_root h34 hspread H hs hy hy1, inf_QB_zpowers_eq hsy, inf_QB_zpowers_eq hs]
  exact ⟨fun h => ⟨ht, h.2⟩, fun h => ⟨ht.of_mem_root_good101 h34 hspread H hs hy hy1, h.2⟩⟩

end CFSG.RankThree.GF2n.Stroth80
