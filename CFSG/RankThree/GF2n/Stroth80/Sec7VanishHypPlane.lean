module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.GF2n.Smith81.Sec1Types
public import CFSG.RankThree.GF2n.Stroth80.Sec39Rt
public import CFSG.RankThree.GF2n.Stroth80.Sec5Defs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] {Q Z C D : Subgroup G} {t h : G}

theorem hypPlane_conj_iff (hQn : h ∈ Subgroup.normalizer (Q : Set G))
    (hZn : h ∈ Subgroup.normalizer (Z : Set G)) :
    HypPlane Q Z (conjSubgroup h C) (conjSubgroup h D) t ↔ HypPlane Q Z C D (h⁻¹ * t * h) := by
  have hsup : conjSubgroup h (D ⊔ Z) = conjSubgroup h D ⊔ Z := by
    have h1 : conjSubgroup h (D ⊔ Z) = conjSubgroup h D ⊔ conjSubgroup h Z := by
      unfold conjSubgroup
      exact Subgroup.map_sup _ _ _
    rw [h1, conjSubgroup_eq_self_iff.mpr hZn]
  have hcQ : ∀ y, y ∈ Q ↔ h⁻¹ * y * h ∈ Q := fun y => by
    have := Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hQn) y
    rwa [inv_inv] at this
  have hcQ' : ∀ y, y ∈ Q ↔ h * y * h⁻¹ ∈ Q := fun y => Subgroup.mem_normalizer_iff.mp hQn y
  unfold HypPlane
  constructor
  · rintro ⟨c, hc, hct, b, hb, hne⟩
    refine ⟨h⁻¹ * c * h, (hcQ c).mp hc, ?_, h⁻¹ * b * h, mem_conjSubgroup.mp hb, ?_⟩
    · have e : ⁅h⁻¹ * c * h, h⁻¹ * t * h⁆ = h⁻¹ * ⁅c, t⁆ * h := by
        simp only [commutatorElement_def]; group
      rw [e]
      have hm : ⁅c, t⁆ ∈ conjSubgroup h (D ⊔ Z) := by rw [hsup]; exact hct
      exact mem_conjSubgroup.mp hm
    · have e : ⁅h⁻¹ * b * h, h⁻¹ * c * h⁆ = h⁻¹ * ⁅b, c⁆ * h := by
        simp only [commutatorElement_def]; group
      rw [e]
      intro h1
      apply hne
      have h2 : h * (h⁻¹ * ⁅b, c⁆ * h) * h⁻¹ = h * 1 * h⁻¹ := by rw [h1]
      simpa [mul_assoc] using h2
  · rintro ⟨c, hc, hct, b, hb, hne⟩
    have hb' : h * b * h⁻¹ ∈ conjSubgroup h C := by
      rw [mem_conjSubgroup]
      have e3 : h⁻¹ * (h * b * h⁻¹) * h = b := by group
      rw [e3]
      exact hb
    refine ⟨h * c * h⁻¹, (hcQ' c).mp hc, ?_, h * b * h⁻¹, hb', ?_⟩
    · have e : ⁅h * c * h⁻¹, t⁆ = h * ⁅c, h⁻¹ * t * h⁆ * h⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [e]
      have hm : h * ⁅c, h⁻¹ * t * h⁆ * h⁻¹ ∈ conjSubgroup h (D ⊔ Z) := by
        rw [mem_conjSubgroup]
        have e2 : h⁻¹ * (h * ⁅c, h⁻¹ * t * h⁆ * h⁻¹) * h = ⁅c, h⁻¹ * t * h⁆ := by group
        rw [e2]
        exact hct
      rw [hsup] at hm
      exact hm
    · have e : ⁅h * b * h⁻¹, h * c * h⁻¹⁆ = h * ⁅b, c⁆ * h⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [e]
      intro h1
      apply hne
      have h2 : h⁻¹ * (h * ⁅b, c⁆ * h⁻¹) * h = h⁻¹ * 1 * h := by rw [h1]
      simpa [mul_assoc] using h2

theorem hypPlane_mul_mem_Q {q : G} (hq : q ∈ Q) (hQt : ∀ y ∈ Q, ⁅y, t⁆ ∈ Q)
    (hQQ : ∀ y ∈ Q, ∀ y' ∈ Q, ⁅y, y'⁆ ∈ Z) :
    HypPlane Q Z C D (q * t) ↔ HypPlane Q Z C D t := by
  have key : ∀ c ∈ Q, ⁅c, q * t⁆ ∈ D ⊔ Z ↔ ⁅c, t⁆ ∈ D ⊔ Z := by
    intro c hc
    have hy : ⁅c, t⁆ ∈ Q := hQt c hc
    have e : ⁅c, q * t⁆ = ⁅c, q⁆ * ⁅c, t⁆ * ⁅⁅c, t⁆⁻¹, q⁆ := by
      simp only [commutatorElement_def]; group
    have hz1 : ⁅c, q⁆ ∈ D ⊔ Z := Subgroup.mem_sup_right (hQQ c hc q hq)
    have hz2 : ⁅⁅c, t⁆⁻¹, q⁆ ∈ D ⊔ Z := Subgroup.mem_sup_right (hQQ _ (Q.inv_mem hy) q hq)
    rw [e]
    constructor
    · intro hm
      have h3 := (D ⊔ Z).mul_mem ((D ⊔ Z).mul_mem ((D ⊔ Z).inv_mem hz1) hm)
        ((D ⊔ Z).inv_mem hz2)
      convert h3 using 1
      group
    · intro hm
      exact (D ⊔ Z).mul_mem ((D ⊔ Z).mul_mem hz1 hm) hz2
  unfold HypPlane
  constructor
  · rintro ⟨c, hc, hm, b, hb, hne⟩
    exact ⟨c, hc, (key c hc).mp hm, b, hb, hne⟩
  · rintro ⟨c, hc, hm, b, hb, hne⟩
    exact ⟨c, hc, (key c hc).mpr hm, b, hb, hne⟩

theorem hypPlane_conj_R [Finite G] {M B : Subgroup G}
    (hc : Ctx M Q Z B) {t h r : G}
    (ht : t ∈ LB M Q B) (hh : h ∈ Rt M (LB M Q B) t) (hr : r ∈ Rt M (LB M Q B) t) :
    HypPlane Q Z (conjSubgroup h B) (conjSubgroup (r * h) B) t ↔
      HypPlane Q Z B (conjSubgroup (h⁻¹ * r * h) B) t := by
  have hRM : ∀ x ∈ Rt M (LB M Q B) t, x ∈ M := fun x hx => hc.Rt_le_M t hx
  have hQh : h ∈ Subgroup.normalizer (Q : Set G) := hc.hyp.Q_normal.2 (hRM h hh)
  have hZh : h ∈ Subgroup.normalizer (Z : Set G) := hc.hyp.Z_normal.2 (hRM h hh)
  have hk : h⁻¹ * r * h ∈ Rt M (LB M Q B) t :=
    (Rt M (LB M Q B) t).mul_mem ((Rt M (LB M Q B) t).mul_mem
      ((Rt M (LB M Q B) t).inv_mem hh) hr) hh
  have e : conjSubgroup (r * h) B = conjSubgroup h (conjSubgroup (h⁻¹ * r * h) B) := by
    rw [← conjSubgroup_mul]
    congr 1
    group
  rw [e, hypPlane_conj_iff hQh hZh]
  have htM : t ∈ M := hc.LB_le_M ht
  have hQt : ∀ y ∈ Q, ⁅y, t⁆ ∈ Q := fun y hy => by
    have e1 : ⁅y, t⁆ = y * (t * y⁻¹ * t⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e1]
    exact Q.mul_mem hy ((Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 htM) y⁻¹).mp
      (Q.inv_mem hy))
  have hQQ : ∀ y ∈ Q, ∀ y' ∈ Q, ⁅y, y'⁆ ∈ Z := fun y hy y' hy' =>
    CFSG.RankThree.GF2n.Smith81.comm_mem_Z hc.hyp hy hy'
  have e2 : h⁻¹ * t * h = ⁅h⁻¹, t⁆ * t := by
    simp only [commutatorElement_def]; group
  rw [e2]
  exact hypPlane_mul_mem_Q (hc.Rt_comm_mem_Q ((Rt M (LB M Q B) t).inv_mem hh)) hQt hQQ

end CFSG.RankThree.GF2n.Stroth80
