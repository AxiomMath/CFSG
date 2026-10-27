module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNaturalTransitiveTI
public import CFSG.Quasithin.H13.VolII16SL3
public import CFSG.ClassicalGroups.SpecialLinear.Transitive

public section

noncomputable section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.H13.VolI CFSG.ClassicalGroups.SpecialLinear Matrix

variable {G : Type} [Group G] [Finite G]

theorem s168e3_false_of_sl_three_natural
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hs : s15 D.M V₀ V hV L = 1) {a : ℕ} (ha : 1 < a)
    (hN : BinaryNaturalSL (lBar V₀ V hV L) (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 3 a) : False := by
  classical
  obtain ⟨K, hKfield, hKfin, hKcard, hR⟩ := hN
  let : Field K := hKfield
  let : Finite K := hKfin
  let H : Subgroup (MulAut (Vtil V₀ V hV)) := lBar V₀ V hV L
  have hwT : wTil V₀ V hV L = ⊤ := wTil_eq_top_of_case163_2 c.conc hs
  have hRtop : (FFModel.nat (StatedSL 3 K)).Realizes H ⊤ (fixV H) := by
    simpa [H, hwT] using hR
  have hcomm : commV H = ⊤ := by
    rw [commV_eq_commSub]
    exact hwT
  have hZbot : fixV H = ⊥ :=
    sl3_cover ha hKcard (s15_Infra_vtil_sq_eq_one V₀ V hV) (le_refl _) hcomm hRtop
  obtain ⟨π₀, b₀, -, -, hbk, hbe⟩ :=
    topBot_data (D := FFModel.nat (StatedSL 3 K)) rfl rfl hRtop
  let π : ↥(StatedSL 3 K) →* ↥H := π₀
  let b : Vtil V₀ V hV →* Multiplicative (Fin 3 → K) := b₀
  have hbk' : ∀ w : Vtil V₀ V hV, b w = 1 ↔ w ∈ fixV H := hbk
  have hbe' : ∀ (γ : ↥(StatedSL 3 K)) (w : Vtil V₀ V hV),
      b (((π γ : ↥H) : MulAut (Vtil V₀ V hV)) w) =
        natAct (StatedSL 3 K) γ (b w) := hbe
  have hbker : ∀ w : Vtil V₀ V hV, b w = 1 ↔ w = 1 := by
    intro w
    rw [hbk' w, hZbot, Subgroup.mem_bot]
  have hker : b.ker = ⊥ := by
    ext w
    rw [MonoidHom.mem_ker, hbker w, Subgroup.mem_bot]
  have hbinj : Function.Injective b := (MonoidHom.ker_eq_bot_iff b).mp hker
  have hHle : H ≤ Mbar D.M V₀ V hV :=
    barSub_mono V₀ V hV c.setting.hyp151.le
  have htr : ∀ x y : Vtil V₀ V hV, x ≠ 1 → y ≠ 1 →
      ∃ a ∈ Mbar D.M V₀ V hV, a x = y := by
    intro x y hx1 hy1
    have hbx0 : Multiplicative.toAdd (b x) ≠ 0 := by
      intro h
      apply hx1
      apply hbinj
      apply Multiplicative.toAdd.injective
      rw [h, map_one, toAdd_one]
    have hby0 : Multiplicative.toAdd (b y) ≠ 0 := by
      intro h
      apply hy1
      apply hbinj
      apply Multiplicative.toAdd.injective
      rw [h, map_one, toAdd_one]
    obtain ⟨A, hA, hAeq⟩ :=
      exists_statedSL_mulVec_eq (m := 3) (K := K) (by norm_num) hbx0 hby0
    let γ : ↥(StatedSL 3 K) := ⟨A, hA⟩
    let abar : MulAut (Vtil V₀ V hV) := ((π γ : ↥H) : MulAut (Vtil V₀ V hV))
    have habarH : abar ∈ H := (π γ).2
    have habarM : abar ∈ Mbar D.M V₀ V hV := hHle habarH
    refine ⟨abar, habarM, ?_⟩
    apply hbinj
    have hnat : natAct (StatedSL 3 K) γ (b x) = b y := by
      change Multiplicative.ofAdd
        ((A : Matrix (Fin 3) (Fin 3) K) *ᵥ Multiplicative.toAdd (b x)) = b y
      rw [hAeq]
      simp
    have hstep : b (abar x) = natAct (StatedSL 3 K) γ (b x) := hbe' γ x
    rw [hstep]
    exact hnat
  exact s168e3_false_of_transitive c htr

theorem s168e3_false_of_sl_three_four
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV) (hs : s15 D.M V₀ V hV L = 1)
    (hN : BinaryNaturalSL (lBar V₀ V hV L) (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 3 2) : False :=
  s168e3_false_of_sl_three_natural c hs (by norm_num) hN

theorem s168e3_false_of_sl_three_eight
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV) (hs : s15 D.M V₀ V hV L = 1)
    (hN : BinaryNaturalSL (lBar V₀ V hV L) (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 3 3) : False :=
  s168e3_false_of_sl_three_natural c hs (by norm_num) hN

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
