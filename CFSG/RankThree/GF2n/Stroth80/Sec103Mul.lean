module

public import CFSG.RankThree.GF2n.Stroth80.Sec103Three
public import CFSG.RankThree.GF2n.Stroth80.Sec10Five

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Tt_mul_of_mem_Z (hc : Ctx M Q Z B) {V : Subgroup G} {t w : G} (hw : w ∈ Z)
    (htw : t * w = w * t) : Tt Q Z V (t * w) = Tt Q Z V t := by
  have hcomm : ⁅Wt Q V, Subgroup.zpowers (t * w)⁆ = ⁅Wt Q V, Subgroup.zpowers t⁆ := by
    refine le_antisymm ?_ ?_
    · rw [Subgroup.commutator_le]
      intro x hx y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      have hxQ : x ∈ Q := (Subgroup.mem_inf.mp hx).1
      have hcw : Commute x (w ^ k) := (Z_central hc.hyp (Z.zpow_mem hw k) hxQ).symm
      have h1 : ⁅x, (t * w) ^ k⁆ = ⁅x, t ^ k⁆ := by
        rw [Commute.mul_zpow (show Commute t w from htw) k,
          commutatorElement_mul_right_eq_mul_conj, hcw.commutator_eq, mul_one]
        group
      rw [h1]
      exact Subgroup.commutator_mem_commutator hx (Subgroup.zpow_mem_zpowers t k)
    · rw [Subgroup.commutator_le]
      intro x hx y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      have hxQ : x ∈ Q := (Subgroup.mem_inf.mp hx).1
      have hcw : Commute x (w ^ k) := (Z_central hc.hyp (Z.zpow_mem hw k) hxQ).symm
      have h1 : ⁅x, t ^ k * w ^ k⁆ = ⁅x, t ^ k⁆ := by
        rw [commutatorElement_mul_right_eq_mul_conj, hcw.commutator_eq, mul_one]
        group
      rw [← h1, ← Commute.mul_zpow (show Commute t w from htw) k]
      exact Subgroup.commutator_mem_commutator hx (Subgroup.zpow_mem_zpowers (t * w) k)
  unfold Tt
  rw [hcomm]

private theorem caseA_le_Vt (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {t w : G} (ht : Good103 M Q Z B t) (hw : w ∈ Z) (htw : Good101 M Q Z B (t * w))
    {Y' : Subgroup G} (hs' : Sit M Q Z Y' (t * w)) (hA : CaseA Q Z (t * w)) :
    Q ⊓ QB Y' ≤ Vt M (LB M Q B) B Z t := by
  have htw' : t * w = w * t :=
    mul_inv_eq_iff_eq_mul.mp (hc.LB_centralizes_Z ht.1.mem_LB w hw)
  have hUt : Q ⊓ QB Y' ≤ Ut Q Z (t * w) :=
    Good101.inf_QB_le_Ut_of_caseA hc hs' hA
  have hT : Q ⊓ QB Y' ≤ Tt Q Z (Vt M (LB M Q B) B Z (t * w)) (t * w) :=
    fun x hx => Good101.inf_QB_inf_Ut_le_Tt h34 hspread H htw hs' ⟨hx, hUt hx⟩
  have hV : Vt M (LB M Q B) B Z (t * w) = Vt M (LB M Q B) B Z t :=
    Vt_mul_of_mem_Q hc (hc.Z_le_Q hw)
  have hTt : Tt Q Z (Vt M (LB M Q B) B Z (t * w)) (t * w) =
      Tt Q Z (Vt M (LB M Q B) B Z t) t := by
    rw [hV, Tt_mul_of_mem_Z hc hw htw']
  rw [hTt, ← stroth_10_5 h34 h311a hspread G M Q Z B hc n t H ht] at hT
  exact hT

private theorem caseB_le_Vt (h34 : Stroth34Statement) (hspread : StrothNoA2SpreadStatement)
    {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n) {t w : G}
    (ht : Good103 M Q Z B t) (hw : w ∈ Z) (htw : Good101 M Q Z B (t * w))
    {Y' : Subgroup G} (hs' : Sit M Q Z Y' (t * w)) (hA : ¬ CaseA Q Z (t * w)) :
    Q ⊓ QB Y' ≤ Vt M (LB M Q B) B Z t := by
  rw [CaseA] at hA
  push Not at hA
  obtain ⟨y, hyQ, hy⟩ := hA w⁻¹ (Z.inv_mem hw)
  have hy' : y * (t * w) * y⁻¹ = t := by
    rw [hy]
    group
  have hmem : t ∈ conjSubgroup y Y' := by
    rw [mem_conjSubgroup]
    have e : y⁻¹ * t * y = t * w := by
      conv_lhs => rw [show t = y * (t * w) * y⁻¹ from hy'.symm]
      group
    rw [e]
    exact hs'.mem
  have hsY : Sit M Q Z (conjSubgroup y Y') t := by
    obtain ⟨g, hg⟩ := hs'.conj
    refine ⟨hs'.hyp, ⟨y * g, by rw [hg, conjSubgroup_mul]⟩, hmem, ?_,
      ht.1.2.1, ht.1.2.2.1⟩
    intro h1
    exact ht.1.2.2.1 (by rw [h1]; exact Q.one_mem)
  have hle : Q ⊓ QB (conjSubgroup y Y') ≤ Vt M (LB M Q B) B Z t := by
    rw [← inf_QB_zpowers_eq hsY, ht.2]
    exact le_sup_left
  have hconjV : conjSubgroup y⁻¹ (Vt M (LB M Q B) B Z t) ≤ Vt M (LB M Q B) B Z t := by
    intro v hv
    have hwV : y * v * y⁻¹ ∈ Vt M (LB M Q B) B Z t := by
      simpa using mem_conjSubgroup.mp hv
    have hcomm : ⁅y⁻¹, y * v * y⁻¹⁆ ∈ Z :=
      (Ctx.mem_CN.mp (hc.Q_le_CN ht.1.mem_LB (Q.inv_mem hyQ))).2 _ hwV
    have e : v = ⁅y⁻¹, y * v * y⁻¹⁆ * (y * v * y⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact (Vt M (LB M Q B) B Z t).mul_mem (sec39_Z_le_Vt hcomm) hwV
  intro x hx
  have hxQ : x ∈ Q := (Subgroup.mem_inf.mp hx).1
  have hxY' : x ∈ QB Y' := (Subgroup.mem_inf.mp hx).2
  have hyx : y * x * y⁻¹ ∈ Q ⊓ QB (conjSubgroup y Y') := by
    refine ⟨Q.mul_mem (Q.mul_mem hyQ hxQ) (Q.inv_mem hyQ), ?_⟩
    rw [QB_conj]
    exact Subgroup.mem_map_of_mem _ hxY'
  have hxV : y * x * y⁻¹ ∈ Vt M (LB M Q B) B Z t := hle hyx
  refine hconjV ?_
  rw [mem_conjSubgroup]
  simpa using hxV

theorem Good103.mul_of_mem_Z (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {t w : G} (ht : Good103 M Q Z B t) (hw : w ∈ Z) (htw : Good101 M Q Z B (t * w)) :
    Good103 M Q Z B (t * w) := by
  obtain ⟨Y', hs'⟩ := Good101.exists_sit hc htw
  refine Good101.good103_of_le_Vt h34 hspread H htw hs' ?_
  rw [Vt_mul_of_mem_Q hc (hc.Z_le_Q hw)]
  by_cases hA : CaseA Q Z (t * w)
  · exact caseA_le_Vt h34 h311a hspread H ht hw htw hs' hA
  · exact caseB_le_Vt h34 hspread H ht hw htw hs' hA

end CFSG.RankThree.GF2n.Stroth80
