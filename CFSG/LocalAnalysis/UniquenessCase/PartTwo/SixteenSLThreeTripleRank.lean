module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Fix
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3L3CoverB
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3L3Bridge
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedL3ABB2B
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedL3BA2ABA
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3A5Lift
import CFSG.Quasithin.Background.ConjugateSectionAction

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.ConjugateSection CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s168e3_mBarGT_two_of_sl_three_sum_three
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (_hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (_hthin : ∀ q : ℕ, q.Prime → q ≠ 2 →
      CFSG.Open.pRank q (lBar V₀ V hV L) ≤ 1)
    (hrow : s16h_H5L3Sum (lBar V₀ V hV L)
      (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 3) :
    MBarGT D.M V₀ V 2 := by
  classical
  let W := Vtil V₀ V hV
  let A : Subgroup (MulAut W) := Mbar D.M V₀ V hV
  let H : Subgroup (MulAut W) := lBar V₀ V hV L
  let U : Subgroup W := commSub (⊤ : Subgroup W) H
  let Z : Subgroup W := U ⊓ fixV H
  have hW : ∀ w : W, w ^ 2 = 1 := s15_Infra_vtil_sq_eq_one V₀ V hV
  have hrow' : s16h_H5L3Sum H U Z 3 := hrow
  obtain ⟨t, htA, ht2, htne, htr, hc⟩ := c.conc
  have hbound : ∀ τ ∈ A, τ ^ 2 = 1 → τ ≠ 1 →
      2 ^ (2 + 1) ≤ Nat.card ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers τ)) := by
    intro τ hτA hτ2 hτne
    have hspan : (⨆ X : {X : Subgroup W // X ∈ conjSubs A U}, X.1) = ⊤ := by
      simpa only [A, H, U, iSup_subtype] using hc.1
    obtain ⟨X, u, hu, htu⟩ := exists_not_fixed_of_iSup_eq_top hspan hτne
    obtain ⟨g, hgA, hXeq⟩ := X.2
    have huU : u ∈ U.map g.toMonoidHom := by
      rw [hXeq] at hu
      exact hu
    obtain ⟨v, hvU, hgv⟩ := Subgroup.mem_map.mp huU
    let a : MulAut W := g⁻¹ * τ * g
    have haA : a ∈ A := by
      show g⁻¹ * τ * g ∈ A
      exact A.mul_mem (A.mul_mem (A.inv_mem hgA) hτA) hgA
    have ha2 : a ^ 2 = 1 := by
      rw [show a = g⁻¹ * τ * g from rfl, pow_two]
      calc (g⁻¹ * τ * g) * (g⁻¹ * τ * g) = g⁻¹ * (τ * τ) * g := by group
        _ = g⁻¹ * 1 * g := by rw [← pow_two, hτ2]
        _ = 1 := by group
    have haC : a ∉ centSub U := by
      intro haCent
      have hav : a v = v := (mem_centSub.mp haCent) v hvU
      have hτgv : τ (g v) = g v := by
        have h1 : g⁻¹ (τ (g v)) = v := by
          simpa [a, MulAut.mul_apply] using hav
        calc τ (g v) = g (g⁻¹ (τ (g v))) := by simp
          _ = g v := by rw [h1]
      have hgv' : g v = u := hgv
      rw [hgv'] at hτgv
      exact htu hτgv
    have hrankA : 3 ≤ rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers a)) := by
      by_cases haN : a ∈ Subgroup.normalizer (H : Set (MulAut W))
      ·
        have hUmem : a ∈ stabSub U :=
          StabLat.mem_stabSub_commSub (X := H) (Y := ⊤) (g := a)
            (mem_stabSub.2 fun _ => by simp) haN
        have hUstab : Subgroup.zpowers a ≤ stabSub U := Subgroup.zpowers_le.mpr hUmem
        have hFmem : a ∈ stabSub (fixV H) := by
          rw [mem_stabSub]
          intro z
          constructor
          · intro hz
            have hmem : a⁻¹ ∈ Subgroup.normalizer (H : Set (MulAut W)) :=
              (Subgroup.normalizer (H : Set (MulAut W))).inv_mem haN
            simpa using fixV_apply_mem_of_mem_normalizer (L := H) hmem hz
          · intro hz
            exact fixV_apply_mem_of_mem_normalizer (L := H) haN hz
        have hZmem : a ∈ stabSub Z := by
          rw [mem_stabSub]
          intro z
          constructor
          · intro hz
            exact ⟨(mem_stabSub.mp hUmem z).mp hz.1, (mem_stabSub.mp hFmem z).mp hz.2⟩
          · intro hz
            exact ⟨(mem_stabSub.mp hUmem z).mpr hz.1, (mem_stabSub.mp hFmem z).mpr hz.2⟩
        have hZstab : Subgroup.zpowers a ≤ stabSub Z := Subgroup.zpowers_le.mpr hZmem
        have hbridge := s16h_e3_l3_rk_commSub_autSec_add (τ := a) (U := U) (Z := Z)
          inf_le_left hUstab hZstab
        have hsec : 3 ≤ rk ↥(commSub (⊤ : Subgroup (Sec U Z))
            (autSec (Subgroup.zpowers a) U Z)) :=
          s16h_e3_l3_cover_section_commSub_three hW hrow' ha2 haN haC
        have hsupinf := rk_sup_add_rk_inf (commSub U (Subgroup.zpowers a)) Z
        have hC : 3 ≤ rk ↥(commSub U (Subgroup.zpowers a)) := by omega
        exact le_trans hC (rk_mono (commSub_mono le_top le_rfl))
      ·
        have hle := s16h_e3_two_inf_map_le_fixV A H t a hc haA ha2 haN
        have hker : U ⊓ U.map a.toMonoidHom ≤ Z :=
          le_inf inf_le_left hle
        have hrank := s16h_e3_rank_le_of_inf_map_le hW U Z a ha2 hker
        have hthree := s16h_e3_l3_three_sum_rank H U Z hrow'
        omega
    have hrk : rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers a)) =
        rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers τ)) := by
      have hconj := s15_Infra_commSub_top_map_conj (Subgroup.zpowers τ) g⁻¹
      have hz : (Subgroup.zpowers τ).map (MulAut.conj g⁻¹).toMonoidHom =
          Subgroup.zpowers a := by
        rw [MonoidHom.map_zpowers]
        rfl
      rw [hz] at hconj
      rw [hconj]
      unfold rk
      rw [Subgroup.card_map_of_injective (g⁻¹).injective]
    have hτrank : 3 ≤ rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers τ)) := by
      rwa [← hrk]
    have hcard := card_eq_two_pow hW
      (commSub (⊤ : Subgroup W) (Subgroup.zpowers τ))
    rw [hcard]
    simpa using Nat.pow_le_pow_right (by norm_num : 0 < 2) hτrank
  have hbound' : ∀ τ ∈ Mbar D.M V₀ V c.setting.hyp16.hyp125.isElemAbelian,
      τ ^ 2 = 1 → τ ≠ 1 →
      2 ^ (2 + 1) ≤ Nat.card ↥(commSub (⊤ : Subgroup (Vtil V₀ V
        c.setting.hyp16.hyp125.isElemAbelian)) (Subgroup.zpowers τ)) := by
    intro τ hτ hτ2 hτ1
    exact hbound τ (by simpa [A] using hτ) hτ2 hτ1
  refine s16h_e3_mBarGT_of_rank D c.setting.hyp16.hyp125 (n := 2) hbound' ?_
  exact ⟨t, by simpa [A] using htA, ht2, htne⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
