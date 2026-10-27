module

public import CFSG.Quasithin.Vol2.KGNatSL3Torus
public import CFSG.Quasithin.Vol2.Ch11SecBFacts

public section

namespace CFSG.Quasithin.Vol2.KGNat

open CFSG.Open CFSG.Quasithin Matrix CFSG.ClassicalInvolution.ModelFacts.OddCover
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp specialLinearGroupEquivStatedSL
  specialLinearGroupEquivStatedSL_coe)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {K : Type} [Field K] {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)}
  {π : ↥(StatedSL 3 K) →* ↥H} {f : W → (Fin 3 → K)}

theorem exists_scalar_of_mem_stab (hf : IsCoord (linModelNat (StatedSL 3 K)) H ⊥ π f)
    (g : Matrix.SpecialLinearGroup (Fin 3) K) {s : MulAut W}
    (hs : s ∈ H ⊓ Ch11.SecA.stabW (hf.pre (gmap g (stdLine K)).toAddSubgroup)) :
    ∃ c : Kˣ, ∀ w, f w ∈ gmap g (stdLine K) → f (s w) = (c : K) • f w := by
  obtain ⟨hsH, hsU⟩ := hs
  obtain ⟨A, hA⟩ := (rho3_bijective hf).2 ⟨s, hsH⟩
  have hsA : s = ((rho3 π A : ↥H) : MulAut W) := by rw [hA]
  have hmaps : ∀ w, f w ∈ gmap g (stdLine K) →
      f (((rho3 π A : ↥H) : MulAut W) w) ∈ gmap g (stdLine K) := fun w hw => by
    rw [← hsA]
    exact (Ch11.SecA.mem_stabW.mp hsU w).mp hw
  obtain ⟨c, hc⟩ := exists_scalar_of_stab hf hmaps
  have hc0 : c ≠ 0 := by
    intro h0
    obtain ⟨w₀, hw₀⟩ := hf.surj ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0])
    have h1 : f w₀ ∈ gmap g (stdLine K) := mem_gmap_stdLine_iff.mpr ⟨1, by rw [hw₀, one_smul]⟩
    have h2 := hc w₀ h1
    rw [h0, zero_smul, hf.ker, Subgroup.mem_bot, map_eq_one_iff _ (MulEquiv.injective _)] at h2
    rw [h2, hf.map_one] at hw₀
    have h3 := congrArg (fun x => ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) *ᵥ x) hw₀
    simp only [Matrix.mulVec_zero, ginv_g_mulVec] at h3
    exact one_ne_zero (congrFun h3 0).symm
  exact ⟨Units.mk0 c hc0, fun w hw => by rw [hsA, hc w hw, Units.val_mk0]⟩

theorem injective_of_bot (hf : IsCoord (linModelNat (StatedSL 3 K)) H ⊥ π f) {a b : W}
    (h : f a = f b) : a = b :=
  mul_inv_eq_one.mp (Subgroup.mem_bot.mp ((hf.eq_iff a b).mp h))

theorem factPointSL3B_holds : Ch11.SecB.FactPointSL3 := by
  intro K _ _ n hn hK W _ _ hW H π hπ P hP U hU
  obtain ⟨f, hf⟩ := exists_isCoord (linModelNat _) hπ
  obtain ⟨g, hg⟩ := exists_sylow_eq_conj_Usl hK (by omega) hf hP
  rw [← hK] at hU
  rw [eq_U1_of_isFlagW hW hf hg hU, ← stdLine_eq_flagSpace]
  obtain ⟨l, hl⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hmem : ∀ c : Kˣ, ((rho3 π (g * tSL (c, 1) * g⁻¹) : ↥H) : MulAut W) ∈
      H ⊓ Ch11.SecA.stabW (hf.pre (gmap g (stdLine K)).toAddSubgroup) :=
    fun c => ⟨(rho3 π _).2, mem_stab_diag hf g c⟩
  refine ⟨⟨_, hmem l, fun s hs => ?_⟩, fun u hu w hw hu1 hw1 => ?_,
    fun s hs u hu hu1 hsu w hw => ?_⟩
  · obtain ⟨c, hc⟩ := exists_scalar_of_mem_stab hf g hs
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hl c)
    refine ⟨k, fun u hu => injective_of_bot hf ?_⟩
    have hpow : ((rho3 π (g * tSL (l, 1) * g⁻¹) : ↥H) : MulAut W) ^ k =
        ((rho3 π (g * tSL (l ^ k, 1) * g⁻¹) : ↥H) : MulAut W) := by
      rw [← Subgroup.coe_zpow, ← map_zpow, conj_zpow, ← map_zpow,
        show ((l, 1) : Kˣ × Kˣ) ^ k = (l ^ k, 1) from Prod.ext (by simp) (by simp)]
    rw [hc u hu, hpow, act_diag hf g _ hu, hk]
  · obtain ⟨α, hα⟩ := mem_gmap_stdLine_iff.mp hu
    obtain ⟨β, hβ⟩ := mem_gmap_stdLine_iff.mp hw
    have hα0 : α ≠ 0 := fun h0 => hu1 (injective_of_bot hf (by rw [hα, h0, zero_smul,
      hf.map_one]))
    have hβ0 : β ≠ 0 := fun h0 => hw1 (injective_of_bot hf (by rw [hβ, h0, zero_smul,
      hf.map_one]))
    refine ⟨_, hmem (Units.mk0 (β / α) (div_ne_zero hβ0 hα0)), injective_of_bot hf ?_⟩
    rw [act_diag hf g _ hu, Units.val_mk0, hα, hβ, smul_smul, div_mul_cancel₀ _ hα0]
  · obtain ⟨c, hc⟩ := exists_scalar_of_mem_stab hf g hs
    have hfu0 : f u ≠ 0 := fun h0 => hu1 (injective_of_bot hf (by rw [h0, hf.map_one]))
    have hc1 : (c : K) = 1 := by
      have h1 := hc u hu
      rw [hsu] at h1
      have h2 : ((c : K) - 1) • f u = 0 := by rw [sub_smul, one_smul, ← h1, sub_self]
      exact sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right hfu0)
    exact injective_of_bot hf (by rw [hc w hw, hc1, one_smul])

end CFSG.Quasithin.Vol2.KGNat
