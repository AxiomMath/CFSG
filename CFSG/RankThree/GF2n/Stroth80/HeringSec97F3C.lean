module

public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.GF2n.Smith81.Lin26Roots

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix Pointwise

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

namespace HS9

theorem conj_eq_of_le {x : G} {S : Subgroup G} (h : conjSubgroup x S ≤ S) :
    conjSubgroup x S = S :=
  Subgroup.eq_of_le_of_card_ge h (by rw [card_conjSubgroup])

theorem conj_le_of_forall {x : G} {S T : Subgroup G} (h : ∀ s ∈ S, x * s * x⁻¹ ∈ T) :
    conjSubgroup x S ≤ T := by
  intro y hy
  have h1 : x⁻¹ * y * x ∈ S := mem_conjSubgroup.mp hy
  have h2 := h _ h1
  rwa [show x * (x⁻¹ * y * x) * x⁻¹ = y by group] at h2

theorem Q_conj_V (hc : Ctx M Q Z B) {F : Subgroup G} (hcF : Ctx M Q Z F) {q : G} (hq : q ∈ Q) :
    conjSubgroup q (Z ⊔ B ⊔ F) = Z ⊔ B ⊔ F := by
  apply conj_eq_of_le
  rw [conjSubgroup_sup']
  have h1 : conjSubgroup q (Z ⊔ B) = Z ⊔ B :=
    conjSubgroup_eq_self_iff.mpr (Smith81.Ctx.Q_le_normalizer_ZB hc hq)
  have h2 : conjSubgroup q (Z ⊔ F) = Z ⊔ F :=
    conjSubgroup_eq_self_iff.mpr (Smith81.Ctx.Q_le_normalizer_ZB hcF hq)
  have h3 : conjSubgroup q F ≤ Z ⊔ B ⊔ F :=
    ((Subgroup.map_mono (le_sup_right : F ≤ Z ⊔ F)).trans h2.le).trans
      (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
  rw [h1]
  exact sup_le le_sup_left h3

theorem QB_inf_M_conj_V (hc : Ctx M Q Z B) {F : Subgroup G} (hFB : F ≤ QB B) {x : G}
    (hxB : x ∈ QB B) (hxM : x ∈ M) : conjSubgroup x (Z ⊔ B ⊔ F) = Z ⊔ B ⊔ F := by
  have hZV : Z ≤ Z ⊔ B ⊔ F := le_sup_left.trans le_sup_left
  have hBV : B ≤ Z ⊔ B ⊔ F := le_sup_right.trans le_sup_left
  have hFV : F ≤ Z ⊔ B ⊔ F := le_sup_right
  apply conj_eq_of_le
  rw [conjSubgroup_sup', conjSubgroup_sup']
  refine sup_le (sup_le ?_ ?_) ?_
  · rw [hc.conj_Z_eq hxM]
    exact hZV
  · refine conj_le_of_forall fun b hb => ?_
    have : x * b * x⁻¹ = b := by
      rw [← Smith81.Ctx.B_central_QB hc hb hxB]
      group
    rw [this]
    exact hBV hb
  · refine conj_le_of_forall fun f hf => ?_
    have hc1 : ⁅x, f⁆ ∈ B := Smith81.Ctx.QB_comm_mem hc hxB (hFB hf)
    have e : x * f * x⁻¹ = ⁅x, f⁆ * f := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Subgroup.mul_mem _ (hBV hc1) (hFV hf)

theorem QF_inf_M_conj_V (hc : Ctx M Q Z B) {F : Subgroup G} (hcF : Ctx M Q Z F)
    (hBF : B ≤ QB F) {x : G} (hxF : x ∈ QB F) (hxM : x ∈ M) :
    conjSubgroup x (Z ⊔ B ⊔ F) = Z ⊔ B ⊔ F := by
  have hZV : Z ≤ Z ⊔ B ⊔ F := le_sup_left.trans le_sup_left
  have hBV : B ≤ Z ⊔ B ⊔ F := le_sup_right.trans le_sup_left
  have hFV : F ≤ Z ⊔ B ⊔ F := le_sup_right
  apply conj_eq_of_le
  rw [conjSubgroup_sup', conjSubgroup_sup']
  refine sup_le (sup_le ?_ ?_) ?_
  · rw [hc.conj_Z_eq hxM]
    exact hZV
  · refine conj_le_of_forall fun b hb => ?_
    have hc1 : ⁅x, b⁆ ∈ F := Smith81.Ctx.QB_comm_mem hcF hxF (hBF hb)
    have e : x * b * x⁻¹ = ⁅x, b⁆ * b := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Subgroup.mul_mem _ (hFV hc1) (hBV hb)
  · refine conj_le_of_forall fun f hf => ?_
    have : x * f * x⁻¹ = f := by
      rw [← Smith81.Ctx.B_central_QB hcF hf hxF]
      group
    rw [this]
    exact hFV hf

theorem mem_sup_sup_iff (hc : Ctx M Q Z B) {F : Subgroup G} (hFQ : F ≤ Q) {p : G}
    (hp : p ∈ Z ⊔ B ⊔ F) : ∃ z ∈ Z, ∃ b ∈ B, ∃ f ∈ F, p = z * b * f := by
  have h : ((Z ⊔ B ⊔ F : Subgroup G) : Set G) = ((Z ⊔ B : Subgroup G) : Set G) * (F : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left (Z ⊔ B) F
      (hFQ.trans (Smith81.Ctx.Q_le_normalizer_ZB hc))
  have hp' : p ∈ ((Z ⊔ B ⊔ F : Subgroup G) : Set G) := hp
  rw [h] at hp'
  obtain ⟨w, hw, f, hf, rfl⟩ := hp'
  obtain ⟨z, hz, b, hb, rfl⟩ := (Smith81.Ctx.mem_sup_iff hc).mp hw
  exact ⟨z, hz, b, hb, f, hf, rfl⟩

theorem exists_ne_one_mem (hc : Ctx M Q Z B) : ∃ b ∈ B, b ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hbot : B = ⊥ := (Subgroup.eq_bot_iff_forall B).mpr hcon
  obtain ⟨g, hg⟩ := hc.conj
  have h4 := hc.hyp.q4
  have : Nat.card B = Nat.card Z := by rw [hg, card_conjSubgroup]
  rw [hbot, Subgroup.card_bot] at this
  omega

end HS9

end CFSG.RankThree.GF2n.Stroth80
