module

public import CFSG.Quasithin.Vol2.Ch3T326PA

public section

namespace CFSG.Quasithin.H13.T326

open CFSG.Quasithin CFSG.Quasithin.SmithD321 CFSG.Quasithin.SmithD39Two CFSG.Quasithin.Z391
  CFSG.Quasithin.SmithD391 CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Open

variable {W : Type} [CommGroup W] [Finite W]

theorem sideHyps_of_nat (hA21 : AsA21SQTKSection)
    (hB42 : AsB42) (h9 : A38B42) {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
    {t : MulAut W} {A : Subgroup (MulAut W)} {r : ℚ} (hS : D321Sit M Mp T L V t A r)
    (hVt : ∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v) (hU : commSub (orbSup T V) L = V)
    (hAC : A ⊓ Subgroup.centralizer (Mp : Set (MulAut W)) = ⊥)
    (hAL : A ≤ Subgroup.normalizer (L : Set (MulAut W))) (hL3 : IsPSL 3 2 1 ↥L)
    (hnat : BinaryNaturalSL L V (V ⊓ fixV Mp) 3 1) :
    SideHyp hS.hD.hyp.Mp_normal L V ∧
      SideHyp hS.hD.hyp.Mp_normal (conjAutSub t L) (V.map t.toMonoidHom) ∧
      commV L ⊓ fixV Mp = ⊥ := by
  have hSide := sideHyp_of_nat hA21 hB42 h9 hS hVt hU hAC hAL hL3 hnat
  have hSide' := sideHyp_of_nat hA21 hB42 h9 hS.swapV (D321Base.swapV_fix hS.toD321Base hVt)
    (D321Base.swapV_caseIIa hS.toD321Base hU) hAC (le_normalizer_Lt hS hAL)
    (isPSL32_conjAutSub t hL3) (binaryNaturalSL_conj hS.toD321Base hnat)
  refine ⟨hSide, hSide', ?_⟩
  have hUU : commV L ⊓ commV (conjAutSub t L) ≤ fixV Mp := fun w hw => by
    rw [hS.hMp, fixV_sup]
    exact ⟨hS.commV_Lt_le_fixV hVt hw.2, hS.commV_le_fixV hVt hw.1⟩
  have hA1 : A ≠ ⊥ := fun h => by
    have h1 := hS.rk_pos
    rw [h, rk_bot] at h1
    exact lt_irrefl _ h1
  have hAr : nSec A ⊤ ⊥ ≤ 2 * rk ↥A := by
    have h1 := hS.rkIdx_le
    have h2 := rk_add_rkIdx (fixV A)
    unfold nSec
    rw [secFix_bot, top_inf_eq, rk_top]
    omega
  have hAC' : A ⊓ Subgroup.centralizer (L : Set (MulAut W)) ⊓
      Subgroup.centralizer ((conjAutSub t L : Subgroup (MulAut W)) : Set (MulAut W)) = ⊥ := by
    rw [eq_bot_iff]
    rintro a ⟨⟨haA, haL⟩, haLt⟩
    have haL' : ∀ h ∈ L, h * a = a * h :=
      Subgroup.mem_centralizer_iff.1 (haL : a ∈ Subgroup.centralizer (L : Set (MulAut W)))
    have haLt' : ∀ h ∈ conjAutSub t L, h * a = a * h :=
      Subgroup.mem_centralizer_iff.1 (haLt : a ∈ Subgroup.centralizer
        ((conjAutSub t L : Subgroup (MulAut W)) : Set (MulAut W)))
    have hcMp : a ∈ A ⊓ Subgroup.centralizer (Mp : Set (MulAut W)) := by
      refine ⟨haA, Subgroup.mem_centralizer_iff.2 fun x hx => ?_⟩
      obtain ⟨b, hb, c, hc, rfl⟩ := hS.exists_mul_of_mem_Mp hx
      rw [mul_assoc, haLt' c hc, ← mul_assoc, haL' b hb, mul_assoc]
    rwa [hAC] at hcMp
  exact commV_inf_fixV_eq_bot hS.exp hS.t_mem rfl hSide hSide' hUU hS.A_le hAL
    (le_normalizer_Lt hS hAL) hS.elemAb.2 hS.elemAb.1 hA1 hAr hAC'

end CFSG.Quasithin.H13.T326
