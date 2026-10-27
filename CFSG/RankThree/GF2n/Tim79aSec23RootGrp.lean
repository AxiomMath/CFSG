module

public import CFSG.RankThree.GF2n.Tim79aSec23Inv

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.GroupTheory
open scoped commutatorElement

theorem isPGroup_rootGroup_sup {Y : Type} [Group Y] [Finite Y] {D : Set Y}
    (hD : CFSG.Timmesfeld.IsRootInvolutionSet D) {d e : Y} (hd : d ∈ D) (he : e ∈ D)
    (h4 : orderOf (d * e) = 4) :
    IsPGroup 2 ↥(CFSG.Timmesfeld.rootGroup D d ⊔ CFSG.Timmesfeld.rootGroup D e) := by
  haveI := CFSG.Timmesfeld.isNilpotent_sup_rootGroup hD hd he h4
  have hcl : Subgroup.closure ((CFSG.Timmesfeld.rootGroup D d : Set Y) ∪
      (CFSG.Timmesfeld.rootGroup D e : Set Y)) =
      CFSG.Timmesfeld.rootGroup D d ⊔ CFSG.Timmesfeld.rootGroup D e := by
    rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
  rw [← hcl]
  refine isPGroup_closure_of_le_nilpotent (A := CFSG.Timmesfeld.rootGroup D d ⊔
    CFSG.Timmesfeld.rootGroup D e) ?_ ?_
  · rintro x (hx | hx)
    · exact Subgroup.mem_sup_left hx
    · exact Subgroup.mem_sup_right hx
  · rintro x (hx | hx)
    · exact CFSG.Timmesfeld.mul_self_eq_one_of_mem_rootGroup hD hd hx
    · exact CFSG.Timmesfeld.mul_self_eq_one_of_mem_rootGroup hD he hx

variable {G : Type} [Group G] {M V Q P H : Subgroup G} [Finite G]

namespace MinCex

variable (hc : MinCex M V Q P H)
include hc

theorem false_of_le_rootGroup (hd : Sec23Data V H)
    (hnd : ∃ d ∈ Dy V H, ∃ e ∈ Dy V H, orderOf (d * e) = 4)
    {d : Xbar V H ⧸ Subgroup.center (Xbar V H)} (hdD : d ∈ Dtilde V H)
    (hle : Vtilde V H ≤ CFSG.Timmesfeld.rootGroup (Dtilde V H) d) : False := by
  have hH := hc.tilde_hyp hd hnd
  haveI := hH.finite
  obtain ⟨d₁, hd₁, e₁, he₁, h41⟩ := hH.nondeg
  obtain ⟨g, hg⟩ := isConj_iff.mp (hH.isConj hd₁ hdD)
  have he₂ : g * e₁ * g⁻¹ ∈ Dtilde V H := hH.conj_mem g he₁
  have h4 : orderOf (d * (g * e₁ * g⁻¹)) = 4 := by
    rw [← hg, show g * d₁ * g⁻¹ * (g * e₁ * g⁻¹) = g * (d₁ * e₁) * g⁻¹ by group,
      CFSG.Timmesfeld.orderOf_conj_eq, h41]
  obtain ⟨y, hy⟩ := isConj_iff.mp (hH.isConj hdD he₂)
  set π := QuotientGroup.mk' (Subgroup.center (Xbar V H)) with hπ
  obtain ⟨ŷ, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center (Xbar V H)) y
  have hpair : IsPGroup 2 ↥(CFSG.Timmesfeld.rootGroup (Dtilde V H) d ⊔
      CFSG.Timmesfeld.rootGroup (Dtilde V H) (g * e₁ * g⁻¹)) :=
    isPGroup_rootGroup_sup hH.root hdD he₂ h4
  have hF : CFSG.Timmesfeld.rootGroup (Dtilde V H) (g * e₁ * g⁻¹) =
      (CFSG.Timmesfeld.rootGroup (Dtilde V H) d).map (MulAut.conj (π ŷ)).toMonoidHom := by
    rw [← hy]
    exact CFSG.Timmesfeld.rootGroup_conj hH.isClass _ d
  have hVF : conjSubgroup (π ŷ) (Vtilde V H) ≤
      CFSG.Timmesfeld.rootGroup (Dtilde V H) (g * e₁ * g⁻¹) := by
    rw [hF]
    exact Subgroup.map_mono hle
  have h2g : IsPGroup 2 ↥(Vtilde V H ⊔ conjSubgroup (π ŷ) (Vtilde V H)) :=
    hpair.to_le (sup_le_sup hle hVF)
  have hcomm := hc.commute_of_isPGroup_tilde h2g
  obtain ⟨a, haV, haD, ha1⟩ := hc.exists_vy_mem_Dy hd
  have haD' : π a ∈ Dtilde V H := ⟨a, haD, rfl⟩
  have haE : π a ∈ CFSG.Timmesfeld.rootSet (Dtilde V H) d :=
    CFSG.Timmesfeld.mem_rootSet_of_mem_rootGroup hH.isClass hdD haD' (hle ⟨a, haV, rfl⟩)
  have hbD : π ŷ * π a * (π ŷ)⁻¹ ∈ Dtilde V H := hH.conj_mem _ haD'
  have hbF : π ŷ * π a * (π ŷ)⁻¹ ∈ CFSG.Timmesfeld.rootGroup (Dtilde V H) (g * e₁ * g⁻¹) := by
    rw [hF]
    exact ⟨π a, hle ⟨a, haV, rfl⟩, rfl⟩
  have hbE : π ŷ * π a * (π ŷ)⁻¹ ∈ CFSG.Timmesfeld.rootSet (Dtilde V H) (g * e₁ * g⁻¹) :=
    CFSG.Timmesfeld.mem_rootSet_of_mem_rootGroup hH.isClass he₂ hbD hbF
  have h4ab := CFSG.Timmesfeld.orderOf_mul_eq_four_of_mem_rootSet hH.root hdD he₂ haE hbE h4
  have hc1 := hcomm a haV (ŷ * a * ŷ⁻¹) (mem_conjSubgroup.mpr (by
    rw [show ŷ⁻¹ * (ŷ * a * ŷ⁻¹) * ŷ = a by group]; exact haV))
  have hc2 : π a * (π ŷ * π a * (π ŷ)⁻¹) = (π ŷ * π a * (π ŷ)⁻¹) * π a := by
    have := congrArg π hc1
    simpa [map_mul, map_inv] using this
  have ha2 : π a * π a = 1 := by
    rw [← map_mul, hc.vy_sq haV, map_one]
  have hb2 : (π ŷ * π a * (π ŷ)⁻¹) * (π ŷ * π a * (π ŷ)⁻¹) = 1 := by
    calc _ = π ŷ * (π a * π a) * (π ŷ)⁻¹ := by group
      _ = 1 := by rw [ha2]; group
  set B := π ŷ * π a * (π ŷ)⁻¹ with hB
  have hsq : (π a * B) * (π a * B) = 1 := by
    calc (π a * B) * (π a * B) = π a * (B * π a) * B := by group
      _ = π a * (π a * B) * B := by rw [← hc2]
      _ = (π a * π a) * (B * B) := by group
      _ = 1 := by rw [ha2, hb2, mul_one]
  have hdvd : orderOf (π a * B) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hsq)
  rw [h4ab] at hdvd
  norm_num at hdvd

end MinCex

end CFSG.RankThree.GF2n.Tim79a
