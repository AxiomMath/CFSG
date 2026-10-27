module

public import CFSG.RankThree.PartTwo.Sec12.Item128BarProofBar
import CFSG.RankThree.PartTwo.Sec13.Item13SLTwo
public import CFSG.RankThree.PartTwo.Sec12.Item128BarProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec12.Proof128

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec13 (lBarA omegaA)

section SL

variable {G : Type} [Group G] [Finite G]

theorem false_of_isSLThreePiTwo {A K : Subgroup G} (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (h27 : Nat.card A = 27) {a c : G} (haA : a ∈ A) (hcA : c ∈ A) (ha1 : a ≠ 1) (hc1 : c ≠ 1)
    (hca : c ∉ Subgroup.zpowers a) (hK : K ∈ thetaComponentsAt 3 a)
    (hAN : A ≤ Subgroup.normalizer (K : Set G)) (hcK : c ∈ K)
    (hX : Sec4.IsSLThreePiTwo (lBarA a K A)) : False := by
  obtain ⟨π, p, f, F, _, ⟨D⟩⟩ := Sec13.exists_sLTwoData hX
  have hAH := le_normalizer_zpowers_of_isElemAbelian hA haA
  set X := lBarA a K A with hXdef
  set Λ := (Sec12.lBar a K).subgroupOf X with hΛ
  set Ab := (aBar K hAH).range with hAb
  have hΛn : Λ.Normal := lBar_normal hAN
  have hΛp : Group.IsPerfect Λ := by
    have := isPerfect_lBar hK
    exact Group.IsPerfect.ofSurjective
      (f := (Subgroup.subgroupOfEquivOfLe Sec13.lBar_le_lBarA).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe Sec13.lBar_le_lBarA).symm.surjective
  have hΛ1 : Λ ≠ ⊥ := by
    intro hb
    apply lBar_ne_bot hK
    rw [eq_bot_iff]
    intro x hx
    have hxΛ : (⟨x, Sec13.lBar_le_lBarA hx⟩ : X) ∈ Λ := hx
    rw [hb, Subgroup.mem_bot] at hxΛ
    exact (Subgroup.mem_bot).mpr (congrArg Subtype.val hxΛ)
  have hq2 : 2 < p ^ f := by
    by_contra hq
    have hp := D.piField.prime
    have hf := D.piField.one_le
    have h2 : p ^ f = 2 := by
      have : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow (by omega) _)
      omega
    have := Sec13.SLTwoData.isSolvable_of_two D h2
    have : Group.IsSolvable Λ := Group.isSolvable_of_isSolvable_injective Λ.subtype_injective
    have : Nontrivial Λ := (Subgroup.nontrivial_iff_ne_bot Λ).mpr hΛ1
    exact Group.IsPerfect.not_isSolvable Λ inferInstance
  have hL₀ : D.L₀ = Λ := le_antisymm (D.le_of_normal hq2 hΛn hΛp hΛ1) (D.le_of_isPerfect hΛp)
  have hsup : D.L₀ ⊔ Ab = ⊤ := by
    rw [hL₀]
    exact lBar_sup_range_aBar hK hAN hAH
  have hAb27 : Nat.card Ab = 27 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective (aBar_injective hA hAH)).toEquiv, h27]
  have h9 := D.card_inf_sup_eq_nine hAb27 hsup
  have haK : a ∈ K := by
    have h1 : aBar K hAH ⟨a, haA⟩ ∈ D.L₀ := D.center_le (aBar_mem_center hA haA hK hAH)
    rw [hL₀] at h1
    have h3 : (⟨a, hAH haA⟩ : Subgroup.normalizer (Subgroup.zpowers a : Set G)) ^ 3 ^ 1 = 1 :=
      Subtype.ext (by simpa using hA.2 a haA)
    exact Sec13.mem_of_mk_mem_lBar hK h3 (Subgroup.mem_subgroupOf.mp h1)
  have hAK9 : 9 ≤ Nat.card (A ⊓ K : Subgroup G) := by
    have hle : Subgroup.zpowers c ⊔ Subgroup.zpowers a ≤ A ⊓ K :=
      sup_le (Subgroup.zpowers_le.mpr ⟨hcA, hcK⟩) (Subgroup.zpowers_le.mpr ⟨haA, haK⟩)
    rw [← card_zpowers_sup_eq_nine hA haA hcA ha1 hc1 hca]
    exact Subgroup.card_le_of_le hle
  have hcard := card_lBar_inf_range hA hK hAH
  have hle : Λ ⊓ Ab ≤ Ab ⊓ (D.L₀ ⊔ Subgroup.centralizer (D.L₀ : Set X)) := fun x hx =>
    ⟨hx.2, Subgroup.mem_sup_left (hL₀ ▸ hx.1)⟩
  have heq : Λ ⊓ Ab = Ab ⊓ (D.L₀ ⊔ Subgroup.centralizer (D.L₀ : Set X)) :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [h9, hcard]; exact hAK9)
  have hu : D.u ∈ D.L₀ ⊔ Ab := hsup ▸ Subgroup.mem_top _
  obtain ⟨l, hl, y, hy, hly⟩ := Subgroup.mem_sup_of_normal_left.mp hu
  have hyS : y ∈ Ab ⊓ (D.L₀ ⊔ Subgroup.centralizer (D.L₀ : Set X)) := by
    refine ⟨hy, ?_⟩
    have e : y = l⁻¹ * D.u := by rw [← hly]; group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (D.L₀.inv_mem hl))
      (Subgroup.mem_sup_right D.mem_centralizer)
  rw [← heq] at hyS
  have hyL : y ∈ D.L₀ := hL₀ ▸ hyS.1
  exact D.not_mem (hly ▸ D.L₀.mul_mem hl hyL)

end SL

end CFSG.RankThree.PartTwo.Sec12.Proof128
