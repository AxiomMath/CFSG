module

public import CFSG.Quasithin.Background.F918V2B
public import CFSG.Quasithin.Background.F918V2G1
public import CFSG.Quasithin.Background.F918V2G2
public import CFSG.Quasithin.Background.F918V2G4
public import CFSG.Quasithin.Background.F918V2GD
public import CFSG.Quasithin.Background.F918N9
public import CFSG.Quasithin.EmptyFaithful.S153ZC
public import CFSG.Quasithin.Background.F918V2CC

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open scoped Pointwise

theorem d391Deep_proved (hZ35 : Z35Main) (hB56 : AsB56) (hB51 : AsB51)
    (hA21 : AsA21SQTKSection) (hNC : AsA36NoOddCover) (i2 : D35InspSum) : D391Deep := by
  have hD35 : D35 := d35_of_z35Main hZ35 hA21 hNC
  intro W _ _ M Mp T L V hMp hD hqM hcase A hA hAT hA3 hAr hAf
  obtain ⟨hVc, hlt'⟩ := hcase
  subst hMp
  by_contra hne
  have hlt : V < orbSup T V := Z391.v2g_lt hlt'
  have hC := Z391.v2g_hC hD
  obtain ⟨-, ⟨t, htT, htV⟩, h4all, -⟩ := hD35 W M Mp T Mp V hD hlt hC
  obtain ⟨h4, hsum⟩ := h4all t htT htV
  have hMpM : Mp ≤ M := le_of_mem_cComp hD.hyp.comp
  have hTX : M ≤ Subgroup.normalizer (Mp : Set (MulAut W)) := hD.hyp.Mp_normal
  have hWM : ∀ t ∈ M, ∀ w ∈ (⊤ : Subgroup W), t • w ∈ (⊤ : Subgroup W) := fun _ _ _ _ => trivial
  let instQ : MulDistribMulAction ↥M (W ⧸ modFix Mp (⊤ : Subgroup W)) := quotAct hTX hWM
  set π : W →* (W ⧸ modFix Mp (⊤ : Subgroup W)) :=
    QuotientGroup.mk' (modFix Mp (⊤ : Subgroup W)) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hπM : ∀ (g : ↥M) (w : W), g • π w = π ((g : MulAut W) w) := fun g w => rfl
  have hker : π.ker = fixV Mp := by
    rw [hπ, QuotientGroup.ker_mk']
    exact (fixed_eq_inf_fixV Mp ⊤).trans (top_inf_eq _)
  have htM : t ∈ M := hD.hyp.sylow.1 htT
  set tM : ↥M := ⟨t, htM⟩ with htMdef
  have htT' : (tM : MulAut W) ∈ T := htT
  have htV' : (tM : MulAut W) ∉ stabSub V := htV
  have hni := Z391.v2g_noniso hD hlt hC π hπM hker tM htT' htV'
  have hbase := Z391.v2g_twoTypeBase hD π hπs hπM hker tM htT' htV' h4 hni
  have htypes := d391_types hD35 hD hlt hC π hπs hπM hker tM hni
  have hTT : Z391.TwoType (Mp.subgroupOf M) (T.subgroupOf M) (V.map π) tM := ⟨hbase, htypes⟩
  have hnot := Z391.v2g_hnot hD hVc π hπM hker tM htT' hne
  have hAM : A ≤ M := hAT.trans hD.hyp.sylow.1
  have hAΓ : A.subgroupOf M ≤ T.subgroupOf M := fun x hx => hAT hx
  have hAc : ∀ x ∈ A.subgroupOf M, ∀ y ∈ A.subgroupOf M, x * y = y * x :=
    fun x hx y hy => Subtype.ext (hA.2.2.1 _ hx _ hy)
  have hA2' : ∀ x ∈ A.subgroupOf M, x ^ 2 = 1 := fun x hx =>
    Subtype.ext (by simpa using hA.2.2.2 (x : MulAut W) hx)
  have h2 := Z391.two_type_count2 hTT hAΓ hAc hA2' hnot
  have hA₀A : (A.subgroupOf M).map M.subtype = A := Subgroup.map_subgroupOf_eq_of_le hAM
  have hN1 : Z391.nB (A.subgroupOf M) (⊤ : Subgroup (W ⧸ modFix Mp (⊤ : Subgroup W))) ≤
      rkIdx (fixV A) := by
    have := Z391.nB_top_le_rkIdx_fixV π hπs hπM (A.subgroupOf M)
    rwa [hA₀A] at this
  have hrA : 0 < rk ↥A := hA.rk_pos
  have hN2 : rkIdx (fixV A) ≤ 2 * rk ↥A := by
    have h := hAr
    unfold rAV at h
    have hpos : (0 : ℚ) < (rk ↥A : ℚ) := by exact_mod_cast hrA
    rw [div_le_iff₀ hpos] at h
    exact_mod_cast h
  have hX' := Z391.v2g_orbSup_map π hπM hker tM hsum.1
  obtain ⟨-, hVcomm, hVlt, -⟩ := mem_irrPlus_top_iff.1 hD.hyp.irr
  have hq : CFSG.IsQuasisimple ↥Mp := hD.hyp.quasi
  have hTn : T ≤ Subgroup.normalizer (Mp : Set (MulAut W)) := by
    calc T ≤ Subgroup.normalizer (conjClosure Mp T : Set (MulAut W)) :=
          le_normalizer_conjClosure Mp T
      _ = Subgroup.normalizer (Mp : Set (MulAut W)) := by rw [← hD.hyp.Mp_eq]
  have hGN : Mp ⊔ T ≤ Subgroup.normalizer (Mp : Set (MulAut W)) :=
    sup_le Subgroup.le_normalizer hTn
  have hN : ∀ g ∈ Mp ⊔ T, ∀ l ∈ Mp, g * l * g⁻¹ ∈ Mp := fun g hg l hl =>
    ((Subgroup.mem_normalizer_iff.1 (hGN hg)) l).1 hl
  have hG := n1_sup_le_stabSub_sec hD.hyp
  have hGV : Mp ⊔ T ≤ stabSub (orbSup T V) := hG.trans inf_le_left
  have hGC : Mp ⊔ T ≤ stabSub (orbSup T V ⊓ fixV Mp) := hG.trans inf_le_right
  have hAG : A ≤ Mp ⊔ T := hAT.trans le_sup_right
  have hAV : A ≤ stabSub (orbSup T V) := hAG.trans hGV
  have hAC : A ≤ stabSub (orbSup T V ⊓ fixV Mp) := hAG.trans hGC
  have hntVT : ¬ Mp ≤ centSec (orbSup T V) (orbSup T V ⊓ fixV Mp) := by
    intro h
    have h1 : commSub (orbSup T V) Mp ≤ orbSup T V ⊓ fixV Mp := by
      rw [commSub, Subgroup.closure_le]
      rintro _ ⟨x, hx, w, hw, rfl⟩
      exact (h hx).2 w hw
    have h2 : commSub V Mp ≤ fixV Mp :=
      (commSub_mono (le_orbSup T V) le_rfl).trans (h1.trans inf_le_right)
    rw [hVcomm] at h2
    exact absurd (inf_eq_left.2 h2) hVlt.ne
  have hf : A ⊓ centSec (orbSup T V) (orbSup T V ⊓ fixV Mp) = ⊥ :=
    Z391.inf_centSec_eq_bot hq le_sup_left hAG hN hGV hGC hntVT hAf
  have hIsA2 : IsA2 (Mp ⊔ T) A := ⟨hAG, hA.2.1, hA.2.2⟩
  have hA2s := Z391.isA2_autSec hIsA2 hAV hAC hf
  have hrkA : rk ↥(autSec A (orbSup T V) (orbSup T V ⊓ fixV Mp)) = rk ↥A :=
    B5.rk_autSec_eq hAV hAC hf
  have hZ := z35_of_d3Std hD hlt hC
  have h2' : 2 * Z391.nB (A.subgroupOf M) ((orbSup T V).map π) ≤
      Z391.nB (A.subgroupOf M) (⊤ : Subgroup (W ⧸ modFix Mp (⊤ : Subgroup W))) := by
    rw [hX']
    exact h2
  have hnB : Z391.nB (A.subgroupOf M) ((orbSup T V).map π) ≤ rk ↥A := by omega
  have hr := Z391.v2g_ffBridge π hπM hker hD.hyp.exp hAM hA.2.2 hA.2.1 hAV hAC hf hnB
  obtain ⟨n, hn⟩ := x_core_sumNatDual hB56 hB51 hA21 hZ rfl (autSec_mono hAT _ _)
    hA2s.2.2 hA2s.2.1 hr
  have hle := Z391.rkIdx_fixV_autSec_le_nB π hπM (A.subgroupOf M) (orbSup T V)
  rw [hA₀A, hker] at hle
  by_cases h3 : Z391.ThreeCopies (Mp.subgroupOf M) (V.map π)
  · exfalso
    have h3' := Z391.two_type_count3 hTT hAΓ hAc hA2' h3
    rw [hX'.symm] at h3'
    have hexpS : ∀ s : Sec (orbSup T V) (orbSup T V ⊓ fixV Mp), s ^ 2 = 1 :=
      CFSG.QuasithinUnique.Bridge.sec_sq_eq_one hD.hyp.exp _ _
    have hnormal : autSec A (orbSup T V) (orbSup T V ⊓ fixV Mp) ≤
        Subgroup.normalizer (autSec Mp (orbSup T V) (orbSup T V ⊓ fixV Mp) :
          Set (MulAut (Sec (orbSup T V) (orbSup T V ⊓ fixV Mp)))) :=
      (autSec_mono hAT _ _).trans (n6_Tb_le_normalizer hZ)
    have hrk := sumNatDual_rank_bound hexpS hn i2 hA2s.2.2 hA2s.2.1 hnormal
    omega
  · obtain ⟨S₀, hS₀, hS₀iso, hS₀d, hdec, hdis, hall⟩ := Z391.two_type_struct hTT hnot h3
    obtain ⟨hE1, hE2, hOnto, hFaith, hYE⟩ :=
      Z391.v2g_natData hA21 hNC hZ35 hD hlt hC π hπs hπM hker tM htT' htV' ⟨n, hn⟩
    exact hne (Z391.v2g_final hD π hπs hπM hker tM htT' hTT hS₀ hS₀iso hS₀d hdec hdis hall hE1 hE2
      hOnto hFaith hYE)

theorem d391Deep_of_inspections (hB42 : AsB42) (hB51 : AsB51) (hB56 : AsB56)
    (hA21 : AsA21SQTKSection) (hNC : AsA36NoOddCover) (i1 : D35InspTwo) (i2 : D35InspSum)
    (i3 : D35InspUniq) (i4 : D35InspB42) : D391Deep :=
  d391Deep_proved (z35Main_of_inputs hB42 hB51 hB56 hA21 i1 i2 i3 i4) hB56 hB51 hA21 hNC i2

end CFSG.Quasithin
