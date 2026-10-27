module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSLFourEightCover
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNaturalTransitiveTI
public import CFSG.ClassicalGroups.SpecialLinear.Transitive

public section

noncomputable section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.H13.VolI CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open Matrix

variable {G : Type} [Group G] [Finite G]

private theorem s168e3_false_of_sl_four_eight_natural_aux
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hs : s15 D.M V₀ V hV L = 1)
    {K : Type} [Field K] [Finite K]
    (hKcard : Nat.card K = 2 ^ 3)
    (hR : (FFModel.nat (StatedSL 4 K)).Realizes (lBar V₀ V hV L)
      (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L))) : False := by
  classical
  let H := lBar V₀ V hV L
  let W := Vtil V₀ V hV
  have hK8 : Nat.card K = 8 := by
    rw [hKcard]
    norm_num
  have hwt : wTil V₀ V hV L = ⊤ := wTil_eq_top_of_case163_2 c.conc hs
  have hR' : (FFModel.nat (StatedSL 4 K)).Realizes H ⊤ (fixV H) := by
    have h := hR
    rw [hwt, top_inf_eq] at h
    exact h
  have hW2 : ∀ w : W, w ^ 2 = 1 := s15_Infra_vtil_sq_eq_one V₀ V hV
  have hcomm : commV H = ⊤ := by
    rw [commV_eq_commSub]
    simpa [H, wTil, lBar] using hwt
  have hZbot : fixV H = ⊥ :=
    s16_sl_four_eight_cover (K := K) hK8 hW2 le_rfl hcomm hR'
  obtain ⟨π, b, hπs, hbs, hbk, hbe⟩ :=
    topBot_data (D := FFModel.nat (StatedSL 4 K)) rfl rfl hR'
  have hb_inj : Function.Injective b := by
    intro u v huv
    have h1 : b (u * v⁻¹) = 1 := by
      rw [map_mul, map_inv, huv, mul_inv_cancel]
    have h2 : u * v⁻¹ ∈ fixV H := (hbk (u * v⁻¹)).1 h1
    have h3 : u * v⁻¹ = 1 := by simpa [hZbot] using h2
    exact mul_inv_eq_one.mp h3
  let e : W ≃* Multiplicative (Fin 4 → K) :=
    MulEquiv.ofBijective (b : W →* Multiplicative (Fin 4 → K)) ⟨hb_inj, hbs⟩
  have hρ : ∀ (A : ↥(StatedSL 4 K)) (w : W),
      Multiplicative.toAdd (e (((π A : ↥H) : MulAut W) w)) =
        (((A : ↥(StatedSL 4 K)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ
          Multiplicative.toAdd (e w) := fun A w =>
    congrArg Multiplicative.toAdd (hbe A w)
  have hHA : H ≤ Mbar D.M V₀ V hV := by
    simpa only [H, lBar, Mbar] using barSub_mono V₀ V hV c.setting.hyp151.le
  have htr : ∀ x y : W, x ≠ 1 → y ≠ 1 →
      ∃ a ∈ Mbar D.M V₀ V hV, a x = y := by
    intro x y hx hy
    have hex : e x ≠ 1 := by
      intro h
      exact hx (by simpa [hZbot] using (hbk x).1 h)
    have hey : e y ≠ 1 := by
      intro h
      exact hy (by simpa [hZbot] using (hbk y).1 h)
    have hx0 : Multiplicative.toAdd (e x) ≠ 0 := by
      intro h
      have h1 : e x = 1 := by
        rw [← ofAdd_toAdd (e x), h, ofAdd_zero]
      exact hex h1
    have hy0 : Multiplicative.toAdd (e y) ≠ 0 := by
      intro h
      have h1 : e y = 1 := by
        rw [← ofAdd_toAdd (e y), h, ofAdd_zero]
      exact hey h1
    obtain ⟨A, hA, hAx⟩ := CFSG.ClassicalGroups.SpecialLinear.exists_statedSL_mulVec_eq
      (m := 4) (K := K) (by norm_num) hx0 hy0
    let A' : ↥(StatedSL 4 K) := ⟨A, hA⟩
    refine ⟨((π A' : ↥H) : MulAut W), hHA (π A').2, ?_⟩
    have hb1 : b (((π A' : ↥H) : MulAut W) x) = b y := by
      change e (((π A' : ↥H) : MulAut W) x) = e y
      apply Multiplicative.toAdd.injective
      rw [hρ A' x, hAx]
    exact hb_inj hb1
  exact s168e3_false_of_transitive c htr

theorem s168e3_false_of_sl_four_eight_natural
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hs : s15 D.M V₀ V hV L = 1)
    (hN : BinaryNaturalSL (lBar V₀ V hV L) (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 4 3) : False := by
  obtain ⟨K, hKf, hKfin, hKcard, hR⟩ := hN
  exact @s168e3_false_of_sl_four_eight_natural_aux G _ _ D V₀ V L hV c hs K hKf hKfin
    hKcard hR

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
