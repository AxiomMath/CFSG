module

public import CFSG.RankThree.GF2n.Tim78S44
public import CFSG.RankThree.GF2n.Tim78S45Aux

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n
open scoped commutatorElement

variable {G : Type} [Group G]

namespace Hyp4

variable [Finite G] {M B Q P T : Subgroup G} (H : Hyp4 M B Q P T)
include H

section Root


theorem inf_conj_B_T_eq_bot (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput) {g : G}
    (hBgB : conjSubgroup g B ≠ B) : conjSubgroup g B ⊓ T = ⊥ := by
  rw [eq_bot_iff]
  intro u hu
  obtain ⟨huBg, huT⟩ := Subgroup.mem_inf.mp hu
  have hu' : g⁻¹ * u * g ∈ B := by
    have := huBg
    rwa [mem_conjSubgroup] at this
  have h1 := H.tim78_4_3 hCen hU _ hu' g (by rwa [show g * (g⁻¹ * u * g) * g⁻¹ = u by group])
  rw [show g * (g⁻¹ * u * g) * g⁻¹ = u by group] at h1
  have : u ∈ B ⊓ conjSubgroup g B := ⟨h1, huBg⟩
  rwa [inf_conjSubgroup_eq_bot_of_isTI H.ti hBgB] at this

theorem tim78_4_5 (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput) :
    ∀ g : G, conjSubgroup g B ⊓ Q ≠ ⊥ → conjSubgroup g B ≤ P := by
  intro g hE
  by_contra hBgnP
  set Bg := conjSubgroup g B with hBgdef
  have hBgB : Bg ≠ B := fun h => hBgnP (h ▸ H.B_le_P)
  have hBBg : B ⊓ Bg = ⊥ := inf_conjSubgroup_eq_bot_of_isTI H.ti hBgB
  obtain ⟨⟨e, heE⟩, he1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hE
  have he1' : e ≠ 1 := fun h => he1 (Subtype.ext h)
  have heBg : e ∈ Bg := (Subgroup.mem_inf.mp heE).1
  have heQ : e ∈ Q := (Subgroup.mem_inf.mp heE).2
  have hBMg : B ≤ conjSubgroup g M := fun b hb =>
    H.centralizer_le_conj heBg he1' (Subgroup.mem_centralizer_singleton_iff.mpr
      (H.center_Q hb heQ))
  have hBgM : Bg ≤ M := H.conj_le_M_of_le_conj hBMg
  have hBBgc : ∀ a ∈ B, ∀ b ∈ Bg, a * b = b * a := H.commute_of_conj_le_M hBgM
  have hBgP : Bg ⊓ P = ⊥ := by
    by_contra hne
    exact hBgnP (H.tim78_4_4 hCen hU g hne)
  have hBgT : Bg ⊓ T = ⊥ := H.inf_conj_B_T_eq_bot hCen hU hBgB
  have hkey := H.commutator_conj_mem_B hBBg hBBgc heBg heQ he1' hBgM hBgP hBgT
  have hTP : T ≤ Subgroup.normalizer (P : Set G) := le_normalizer_of_comm fun t ht p hp =>
    (Subgroup.mem_centralizer_iff.mp (H.T_le_centralizer_P ht) p hp).symm
  have hBgQT : ∀ y ∈ Bg, ∀ q ∈ Q, ⁅y, q⁆ ∈ T := by
    intro y hy q hq
    have hq' := hq
    rw [H.Q_eq_sup] at hq'
    obtain ⟨p, hp, t, ht, rfl⟩ := exists_mul_of_mem_sup hTP hq'
    have e0 : ⁅y, p * t⁆ = ⁅y, p⁆ * (p * ⁅y, t⁆ * p⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e0]
    refine T.mul_mem (H.B_le_T (hkey y hy p hp)) ?_
    have h1 : ⁅y, t⁆ ∈ T := by
      have e1 : ⁅y, t⁆ = (y * t * y⁻¹) * t⁻¹ := rfl
      rw [e1]
      exact T.mul_mem ((Subgroup.mem_normalizer_iff.mp (H.M_le_normalizer_T (hBgM hy)) t).mp ht)
        (T.inv_mem ht)
    exact (Subgroup.mem_normalizer_iff.mp (H.M_le_normalizer_T (H.P_le_M hp)) _).mp h1
  have hQ : Bg ≤ Q := by
    refine H.le_Q_of_root hCen hU hBgM (E := Bg ⊓ Q) inf_le_left inf_le_right hE ?_
    intro c hcQ hcN a ha
    have hce : c * e = e * c := by
      have h1 : ⁅c, e⁆ ∈ Bg ⊓ Q := by
        have e0 : ⁅c, e⁆ = (c * e * c⁻¹) * e⁻¹ := rfl
        rw [e0]
        exact (Bg ⊓ Q).mul_mem (hcN e heE) ((Bg ⊓ Q).inv_mem heE)
      have h2 : ⁅c, e⁆ ∈ B := H.commutator_mem hcQ heQ
      have h3 : ⁅c, e⁆ ∈ B ⊓ Bg := ⟨h2, h1.1⟩
      rw [hBBg, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h3
      exact h3
    have hcN' : c ∈ Subgroup.normalizer (Bg : Set G) := by
      have := H.centralizer_le_conj heBg he1' (Subgroup.mem_centralizer_singleton_iff.mpr hce)
      rwa [← H.normalizer_conj_eq g] at this
    have h1 : ⁅a, c⁆ ∈ Bg := by
      have e0 : ⁅a, c⁆ = a * (c * a⁻¹ * c⁻¹) := by simp only [commutatorElement_def]; group
      rw [e0]
      exact Bg.mul_mem ha ((Subgroup.mem_normalizer_iff.mp hcN' a⁻¹).mp (Bg.inv_mem ha))
    have h2 : ⁅a, c⁆ ∈ T := hBgQT a ha c hcQ
    have h3 : ⁅a, c⁆ ∈ Bg ⊓ T := ⟨h1, h2⟩
    rw [hBgT, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h3
    exact h3.symm
  exact hBgnP (H.conj_le_P hQ)

end Root

end Hyp4

end CFSG.RankThree.GF2n.Tim78
