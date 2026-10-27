module

public import CFSG.Quasithin.Vol2.KGNatSL3PointFacts
public import CFSG.Quasithin.Vol2.Ch11SecCFacts2

public section

namespace CFSG.Quasithin.Vol2.KGNat

open CFSG.Open CFSG.Quasithin Matrix CFSG.ClassicalInvolution.ModelFacts.OddCover
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp specialLinearGroupEquivStatedSL
  specialLinearGroupEquivStatedSL_coe)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {K : Type} [Field K]

theorem fix_Usl_iff (x : Fin 3 → K) :
    (∀ a b c : K, uMat a b c *ᵥ x = x) ↔ x ∈ stdLine K := by
  constructor
  · intro h
    have h1 := congrFun (h 1 0 0) 0
    have h2 := congrFun (h 0 0 1) 1
    rw [uMat_mulVec] at h1 h2
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_mul, zero_mul, add_zero] at h1 h2
    exact ⟨by simpa using h1, by simpa using h2⟩
  · rintro ⟨h1, h2⟩ a b c
    rw [uMat_mulVec]
    exact vec3_eq (by simp [h1, h2]) (by simp [h1, h2]) (by simp)

theorem mem_gmap_stdLine_iff {g : Matrix.SpecialLinearGroup (Fin 3) K} {x : Fin 3 → K} :
    x ∈ gmap g (stdLine K) ↔ ∃ t : K, x = t • ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0]) := by
  rw [mem_gmap]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨(((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ x) 0, ?_⟩
    rw [← Matrix.mulVec_smul]
    conv_lhs => rw [← g_ginv_mulVec g x]
    congr 1
    exact vec3_eq (by simp) (by rw [h1]; simp) (by rw [h2]; simp)
  · rintro ⟨t, rfl⟩
    rw [Matrix.mulVec_smul, ginv_g_mulVec]
    exact ⟨by simp, by simp⟩

section Real

variable {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)} {Z : Subgroup W}
  {π : ↥(StatedSL 3 K) →* ↥H} {f : W → (Fin 3 → K)}

theorem fixedW_iff (hf : IsCoord (linModelNat (StatedSL 3 K)) H Z π f)
    {P : Subgroup (MulAut W)} {g : Matrix.SpecialLinearGroup (Fin 3) K}
    (hg : ∀ x : MulAut W, x ∈ P ↔ ∃ u ∈ Usl K, x = ((rho3 π (g * u * g⁻¹) : ↥H) : MulAut W))
    (w : W) : (∀ s ∈ P, s w * w⁻¹ ∈ Z) ↔ f w ∈ gmap g (stdLine K) := by
  rw [mem_gmap, ← fix_Usl_iff]
  constructor
  · intro h a b c
    have h1 := h _ ((hg _).mpr ⟨uSL a b c, uSL_mem_Usl a b c, rfl⟩)
    rw [← hf.ker, hf.map_mul_inv, hf.act3, sub_eq_zero, gconj_mulVec] at h1
    have h2 := congrArg (fun x => ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) *ᵥ x) h1
    simp only [ginv_g_mulVec] at h2
    rw [← coe_uSL]
    exact h2
  · intro h s hs
    obtain ⟨u, ⟨a, b, c, rfl⟩, rfl⟩ := (hg s).mp hs
    rw [← hf.ker, hf.map_mul_inv, hf.act3, sub_eq_zero, gconj_mulVec, coe_uSL, h a b c,
      g_ginv_mulVec]

theorem exists_scalar_of_stab (hf : IsCoord (linModelNat (StatedSL 3 K)) H Z π f)
    {g A : Matrix.SpecialLinearGroup (Fin 3) K}
    (hA : ∀ w, f w ∈ gmap g (stdLine K) → f (((rho3 π A : ↥H) : MulAut W) w) ∈ gmap g (stdLine K)) :
    ∃ c : K, ∀ w, f w ∈ gmap g (stdLine K) →
      f (((rho3 π A : ↥H) : MulAut W) w) = c • f w := by
  obtain ⟨w₀, hw₀⟩ := hf.surj ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0])
  have h0 : f w₀ ∈ gmap g (stdLine K) := mem_gmap_stdLine_iff.mpr ⟨1, by rw [hw₀, one_smul]⟩
  obtain ⟨c, hc⟩ := mem_gmap_stdLine_iff.mp (hA w₀ h0)
  refine ⟨c, fun w hw => ?_⟩
  obtain ⟨t, ht⟩ := mem_gmap_stdLine_iff.mp hw
  have hA0 : (A : Matrix (Fin 3) (Fin 3) K) *ᵥ ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0]) =
      c • ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0]) := by
    rw [← hc, hf.act3, hw₀]
  rw [hf.act3, ht, Matrix.mulVec_smul, hA0, smul_smul, smul_smul, mul_comm]

end Real

theorem factTorusLineSL3_holds : Ch11.SecC.FactTorusLineSL3 := by
  intro F _ _ n hn hF W _ _ hW H Z π hπ S hS
  obtain ⟨f, hf⟩ := exists_isCoord (linModelNat _) hπ
  obtain ⟨g, hg⟩ := exists_sylow_eq_conj_Usl hF (by omega) hf hS
  have hfix := fixedW_iff hf hg
  refine ⟨?_, fun y hy hyN => ?_⟩
  · rw [Nat.card_congr (Equiv.subtypeEquivRight hfix)]
    change Nat.card ↥(hf.pre (gmap g (stdLine F)).toAddSubgroup) = _
    have h := Subgroup.relIndex_mul_card Z (hf.pre (gmap g (stdLine F)).toAddSubgroup)
    rw [inf_eq_left.mpr (hf.le_pre _), ← hf.card_img, hf.img_pre] at h
    have hc : Nat.card ↥(gmap g (stdLine F)).toAddSubgroup = 2 ^ n :=
      (card_gmap g (stdLine F)).trans (card_stdLine.trans hF)
    rw [← h, hc]
  · obtain ⟨A, hA⟩ := (rho3_bijective hf).2 ⟨y, hy⟩
    have hyA : y = ((rho3 π A : ↥H) : MulAut W) := by rw [hA]
    have hmaps : ∀ w, f w ∈ gmap g (stdLine F) →
        f (((rho3 π A : ↥H) : MulAut W) w) ∈ gmap g (stdLine F) := by
      intro w hw
      rw [← hyA, ← hfix]
      intro s hs
      have hs' : y⁻¹ * s * y ∈ S := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hyN) s).mp hs
        rwa [inv_inv] at this
      have h1 := (hfix w).mpr hw _ hs'
      have hy0 : ∀ v, f v = 0 → f (y v) = 0 := by
        intro v hv
        rw [hyA, hf.act3, hv, Matrix.mulVec_zero]
      have h2 : f (y (((y⁻¹ * s * y) w) * w⁻¹)) = 0 := hy0 _ ((hf.ker _).mpr h1)
      rw [← hf.ker]
      rw [map_mul, map_inv] at h2
      rwa [show y ((y⁻¹ * s * y) w) = s (y w) by simp [MulAut.mul_apply]] at h2
    obtain ⟨c, hc⟩ := exists_scalar_of_stab hf hmaps
    by_cases hc1 : c = 1
    · left
      intro w hw
      rw [← hf.ker, hf.map_mul_inv, hyA, hc w ((hfix w).mp hw), hc1, one_smul, sub_self]
    · right
      intro w hw hyw
      rw [← hf.ker, hf.map_mul_inv, hyA, hc w ((hfix w).mp hw)] at hyw
      have h1 : (c - 1) • f w = 0 := by
        rw [sub_smul, one_smul]
        exact hyw
      rw [← hf.ker]
      exact (smul_eq_zero.mp h1).resolve_left (sub_ne_zero.mpr hc1)

theorem tSL_mulVec (t : Kˣ × Kˣ) (x : Fin 3 → K) :
    ((tSL t : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ x =
      ![(t.1 : K) * x 0, (t.2 : K) * x 1, (((t.1 * t.2)⁻¹ : Kˣ) : K) * x 2] := by
  change tMat t *ᵥ x = _
  funext i
  fin_cases i <;> simp [tMat, Matrix.mulVec_diagonal]

section PointB

variable {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)} {Z : Subgroup W}
  {π : ↥(StatedSL 3 K) →* ↥H} {f : W → (Fin 3 → K)}

theorem act_diag (hf : IsCoord (linModelNat (StatedSL 3 K)) H Z π f)
    (g : Matrix.SpecialLinearGroup (Fin 3) K) (c : Kˣ) {w : W}
    (hw : f w ∈ gmap g (stdLine K)) :
    f (((rho3 π (g * tSL (c, 1) * g⁻¹) : ↥H) : MulAut W) w) = (c : K) • f w := by
  obtain ⟨t, ht⟩ := mem_gmap_stdLine_iff.mp hw
  have he : ((tSL (c, 1) : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
      ![1, 0, 0] = (c : K) • ![1, 0, 0] := by
    rw [tSL_mulVec]
    exact vec3_eq (by simp) (by simp) (by simp)
  rw [hf.act3, gconj_mulVec, ht, Matrix.mulVec_smul, ginv_g_mulVec, Matrix.mulVec_smul, he,
    Matrix.mulVec_smul, Matrix.mulVec_smul, smul_comm]

theorem mem_stab_diag (hf : IsCoord (linModelNat (StatedSL 3 K)) H Z π f)
    (g : Matrix.SpecialLinearGroup (Fin 3) K) (c : Kˣ) :
    ((rho3 π (g * tSL (c, 1) * g⁻¹) : ↥H) : MulAut W) ∈
      Ch11.SecA.stabW (hf.pre (gmap g (stdLine K)).toAddSubgroup) := by
  rw [hf.rho3_mem_stabW_iff (hf.le_pre _), hf.img_pre]
  intro y
  change y ∈ gmap g _ ↔ _ ∈ gmap g _
  rw [mem_gmap, mem_gmap, conj_mulVec, tSL_mulVec, mem_stdLine, mem_stdLine]
  simp

end PointB

end CFSG.Quasithin.Vol2.KGNat
