module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Fix
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5JPAlt
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3AltBridge
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3A5Rank
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedL3ABB2B
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3A5Lift
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSmallComponentBounds
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenAltFiveTripleParabolic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenThreeOrbitExclusion
import CFSG.Quasithin.Background.ConjugateSectionAction
import CFSG.Quasithin.Background.D2Y5
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightSum
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10NatRank2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.ConjugateSection CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s168e3_mBarGT_two_of_alt_five_sum_three
    {D : UC22.Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hrow : s16h_H5A5Sum (lBar V₀ V hV L)
      (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 3) :
    UC22.MBarGT D.M V₀ V 2 := by
  classical
  let W := Vtil V₀ V hV
  let A : Subgroup (MulAut W) := Mbar D.M V₀ V hV
  let H : Subgroup (MulAut W) := lBar V₀ V hV L
  let U : Subgroup W := commSub (⊤ : Subgroup W) H
  let Z : Subgroup W := U ⊓ fixV H
  have hW : ∀ w : W, w ^ 2 = 1 := s15_Infra_vtil_sq_eq_one V₀ V hV
  have hrow' : s16h_H5A5Sum H U Z 3 := by
    simpa only [H, U, Z, wTil, lBar] using hrow
  obtain ⟨hA5, hsum⟩ := s16h_a5Sum_alt hrow'
  have hZ : Z = ⊥ := by
    have h := s16jp_row_A5 (W := W) hW (L := H)
      ⟨3, le_rfl, by simpa only [U, Z, s16h_H5A5Sum] using hrow'⟩
    simpa only [Z, U] using h
  have hsum0 : SumOfNat (fun H U Z => AlternatingNatural H U Z 5) H U ⊥ 3 := by
    rwa [hZ] at hsum
  have h12 : 12 ≤ rk ↥U := by
    have h4 : ∀ I : Subgroup W, (fun H U Z => AlternatingNatural H U Z 5) H I ⊥ →
        4 ≤ rk ↥I := by
      intro I hI
      have h := s16c1610_rk_alternatingNatural_odd (n := 5) (by decide) hI
      omega
    have h := s16e_rk_sumOfNat_ge (N := fun H U Z => AlternatingNatural H U Z 5)
      (H := H) (U := U) (k := 3) (b := 4) h4 hsum0
    simpa using h
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
        have hHstab : H ≤ stabSub U := by
          intro l hl
          exact StabLat.mem_stabSub_commSub (X := H) (Y := ⊤) (g := l)
            (mem_stabSub.2 fun _ => by simp) (Subgroup.le_normalizer hl)
        have hstabL : ∀ l ∈ H, a * l * a⁻¹ ∈ H := fun l hl =>
          (Subgroup.mem_normalizer_iff.mp haN l).mp hl
        have h8 := s16h_e3_commSub_ge_eight_of_stab hA5 hW hsum0 hHstab hUmem hstabL haC
        have h8' : 8 ≤ Nat.card ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers a)) :=
          le_trans h8 (Nat.card_le_card_of_injective
            (Subgroup.inclusion (commSub_mono (le_top : U ≤ ⊤) le_rfl))
            (Subgroup.inclusion_injective _))
        have hcard := card_eq_two_pow hW (commSub (⊤ : Subgroup W) (Subgroup.zpowers a))
        rw [hcard] at h8'
        have h2 : 2 ^ 3 ≤ 2 ^ rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers a)) := by
          rw [show (2 : ℕ) ^ 3 = 8 by norm_num]
          exact h8'
        exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h2
      ·
        have hle := s16h_e3_two_inf_map_le_fixV A H t a hc haA ha2 haN
        have hker : U ⊓ U.map a.toMonoidHom ≤ Z := le_inf inf_le_left hle
        have hrank := s16h_e3_rank_le_of_inf_map_le hW U Z a ha2 hker
        rw [hZ] at hrank
        have h12' : 12 ≤ rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers a)) := by
          simpa [rk_bot] using le_trans h12 hrank
        omega
    have hrk : rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers a)) =
        rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers τ)) := by
      rw [← commV_eq_commSub, ← commV_eq_commSub]
      have h := rk_commV_zpowers_conj (V := W) (g := g⁻¹) (y := τ)
      have ha : g⁻¹ * τ * (g⁻¹)⁻¹ = a := by simp [a]
      rw [ha] at h
      exact h
    have hτrank : 3 ≤ rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers τ)) := by
      rwa [← hrk]
    have hcard := card_eq_two_pow hW (commSub (⊤ : Subgroup W) (Subgroup.zpowers τ))
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

theorem s168e3_s15_ne_three_of_alt_five_sum_three
    {D : UC22.Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (h82 : F08.R82 D)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hrow : s16h_H5A5Sum (lBar V₀ V hV L)
      (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 3) :
    s15 D.M V₀ V hV L ≠ 3 := by
  intro hs
  obtain ⟨hA5, hsum⟩ := s16h_a5Sum_alt hrow
  have hHcard : Nat.card ↥(lBar V₀ V hV L) = 60 := s16h_e3_card_isAlt_five hA5
  have hsimple : IsSimpleGroup ↥(lBar V₀ V hV L) := s16h_e3_isSimpleGroup_of_isAlt hA5
  have hthin : ∀ q : ℕ, q.Prime → q ≠ 2 →
      CFSG.Open.pRank q (lBar V₀ V hV L) ≤ 1 :=
    fun q hq hq2 => pRank_le_one_of_card_eq_sixty hHcard hq hq2
  have hthree : 3 ∣ Nat.card ↥(lBar V₀ V hV L) := by
    rw [hHcard]
    norm_num
  have hnine : ¬ 3 ^ 2 ∣ Nat.card ↥(lBar V₀ V hV L) := by
    rw [hHcard]
    norm_num
  have hm : UC22.MBarGT D.M V₀ V 2 :=
    s168e3_mBarGT_two_of_alt_five_sum_three c hrow
  have hP := s168e3_alt_five_orbit_three_parabolic c hcomp hs hA5
  exact s168e3_false_of_three_orbit_parabolic c h82 hcomp hsimple hthin hs hthree hnine hm hP

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
