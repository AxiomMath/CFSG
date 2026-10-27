module

public import CFSG.RankThree.GF2n.Stroth80.Sec4Model
public import CFSG.RankThree.GF2n.Stroth80.Sec4Stmt
public import CFSG.GroupTheory.Fitting.CharacteristicP

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

@[expose] def Stroth45Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n : ℕ), Width Q Z n → 2 < n → NoA2 Q Z (LB M Q B) → GenByB M Q B →
    layer (Mbar M Q) ≠ ⊥ ∧
    (CFSG.IsQuasisimple ↥(layer (Mbar M Q)) ∨
      (∃ X Y : Subgroup (Mbar M Q), X ⊔ Y = layer (Mbar M Q) ∧ X ⊓ Y = ⊥ ∧
        (∀ x ∈ X, ∀ y ∈ Y, Commute x y) ∧ CFSG.IsQuasisimple ↥X ∧
        IsSLModel 2 (Nat.card Z) ↥Y) ∨
      (∃ X₁ X₂ X₃ : Subgroup (Mbar M Q), X₁ ⊔ X₂ ⊔ X₃ = layer (Mbar M Q) ∧
        X₁ ⊓ X₂ = ⊥ ∧ (X₁ ⊔ X₂) ⊓ X₃ = ⊥ ∧
        (∀ x ∈ X₁, ∀ y ∈ X₂, Commute x y) ∧ (∀ x ∈ X₁ ⊔ X₂, ∀ y ∈ X₃, Commute x y) ∧
        IsSLModel 2 (Nat.card Z) ↥X₁ ∧ IsSLModel 2 (Nat.card Z) ↥X₂ ∧
        IsSLModel 2 (Nat.card Z) ↥X₃ ∧
        IsQSNormalIn X₁ (bar M Q (Lgen M (LB M Q B))) ∧
        IsQSNormalIn X₂ (bar M Q (Lgen M (LB M Q B))) ∧
        IsQSNormalIn X₃ (bar M Q (Lgen M (LB M Q B)))))

section


theorem stroth45_layer_ne_bot (h34 : Stroth34Statement) (h44 : Stroth44Statement) :
    ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
      (hc : Ctx M Q Z B) (n : ℕ), Width Q Z n → 2 < n → NoA2 Q Z (LB M Q B) → GenByB M Q B →
      layer (Mbar M Q) ≠ ⊥ := by
  intro G _ _ M Q Z B hN hc n hw hn hno hgen hl
  classical
  have hF : generalizedFitting (Mbar M Q) = fittingSubgroup (Mbar M Q) := by
    rw [generalizedFitting.eq_sup, hl, sup_bot_eq]
  have hcent : Subgroup.centralizer (fittingSubgroup (Mbar M Q) : Set (Mbar M Q)) ≤
      fittingSubgroup (Mbar M Q) := by
    have := CFSG.centralizer_generalizedFitting_le (Mbar M Q)
    rwa [hF] at this
  haveI hFn : (fittingSubgroup (Mbar M Q)).Normal := CFSG.fittingSubgroup_normal
  haveI : Group.IsNilpotent ↥(fittingSubgroup (Mbar M Q)) := CFSG.fittingSubgroup_nilpotent
  have hodd : Odd (Nat.card ↥(fittingSubgroup (Mbar M Q))) :=
    odd_card_of_normal_nilpotent hc.pCore_two_Mbar _
  haveI hHn : (bar M Q (H0 M Z)).Normal := hc.normal_bar_H0
  set A : Subgroup (Mbar M Q) := fittingSubgroup (Mbar M Q) ⊓ bar M Q (H0 M Z) with hAdef
  haveI hAn : A.Normal := inferInstance
  have hLH : LB M Q B ≤ H0 M Z := fun t ht => ⟨hc.LB_le_M ht, Subgroup.mem_centralizer_iff.mpr
    fun z hz => by
      have := hc.LB_centralizes_Z ht z hz
      calc z * t = (t * z * t⁻¹) * t := by rw [this]
        _ = t * z := by group⟩
  have hΛH : bar M Q (LB M Q B) ≤ bar M Q (H0 M Z) :=
    Subgroup.map_mono (fun x hx => hLH hx)
  have hA0 : A = ⊥ := h44 G M Q Z B hc n hw hn hno hgen A inf_le_right
    (fun x _ => by
      rw [Subgroup.normalizer_eq_top_iff.mpr hAn]
      exact Subgroup.mem_top x)
    (Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le inf_le_left))
  have hcomm : ∀ f ∈ fittingSubgroup (Mbar M Q), ∀ h ∈ bar M Q (H0 M Z), f * h = h * f := by
    intro f hf h hh
    have hF1 : f * h * f⁻¹ * h⁻¹ ∈ fittingSubgroup (Mbar M Q) := by
      have := (fittingSubgroup (Mbar M Q)).mul_mem hf
        (Subgroup.Normal.conj_mem inferInstance f⁻¹ ((fittingSubgroup (Mbar M Q)).inv_mem hf) h)
      simpa [mul_assoc] using this
    have hH1 : f * h * f⁻¹ * h⁻¹ ∈ bar M Q (H0 M Z) :=
      (bar M Q (H0 M Z)).mul_mem (hHn.conj_mem h hh f) ((bar M Q (H0 M Z)).inv_mem hh)
    have h2 : f * h * f⁻¹ * h⁻¹ ∈ A := ⟨hF1, hH1⟩
    rw [hA0, Subgroup.mem_bot] at h2
    calc f * h = (f * h * f⁻¹ * h⁻¹) * (h * f) := by group
      _ = h * f := by rw [h2, one_mul]
  have hHbot : bar M Q (H0 M Z) = ⊥ := by
    refine le_bot_iff.mp ?_
    intro h hh
    have h1 : h ∈ fittingSubgroup (Mbar M Q) :=
      hcent (Subgroup.mem_centralizer_iff.mpr fun f hf => hcomm f hf h hh)
    have h2 : h ∈ A := ⟨h1, hh⟩
    rwa [hA0] at h2
  have h4 := hc.four_le_card_bar_LB h34 hw hn hno hgen
  have hΛbot : bar M Q (LB M Q B) = ⊥ := le_bot_iff.mp (hHbot ▸ hΛH)
  rw [hΛbot, Subgroup.card_bot] at h4
  omega

end

end CFSG.RankThree.GF2n.Stroth80
