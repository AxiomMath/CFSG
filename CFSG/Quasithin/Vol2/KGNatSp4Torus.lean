module

public import CFSG.Quasithin.Vol2.KGNatSp4Transv
public import CFSG.Quasithin.Vol2.Ch11SecCFacts2

public section

namespace CFSG.Quasithin.Vol2.KGNat

open CFSG.Open CFSG.Quasithin Matrix CFSG.ClassicalInvolution.ModelFacts.OddCover
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)

variable {K : Type} [Field K] {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)}
  {Z : Subgroup W} {π : ↥(StatedSp 2 K) →* ↥H} {f : W → (Fin 2 ⊕ Fin 2 → K)}

theorem exists_scalar_of_stab_sp (hf : IsCoord (linModelNat (StatedSp 2 K)) H Z π f)
    {g γ : StatedSp 2 K}
    (hA : ∀ w, f w ∈ gmapSp g (spLine K) → f (((π γ : ↥H) : MulAut W) w) ∈ gmapSp g (spLine K)) :
    ∃ c : K, ∀ w, f w ∈ gmapSp g (spLine K) → f (((π γ : ↥H) : MulAut W) w) = c • f w := by
  obtain ⟨w₀, hw₀⟩ := hf.surj (mat 2 K g *ᵥ vec4 1 0 0 0)
  have h0 : f w₀ ∈ gmapSp g (spLine K) := mem_gmapSp_spLine_iff.mpr ⟨1, by rw [hw₀, one_smul]⟩
  obtain ⟨c, hc⟩ := mem_gmapSp_spLine_iff.mp (hA w₀ h0)
  refine ⟨c, fun w hw => ?_⟩
  obtain ⟨t, ht⟩ := mem_gmapSp_spLine_iff.mp hw
  have hA0 : mat 2 K γ *ᵥ (mat 2 K g *ᵥ vec4 1 0 0 0) = c • (mat 2 K g *ᵥ vec4 1 0 0 0) := by
    rw [← hc, hf.act4, hw₀]
  rw [hf.act4, ht, Matrix.mulVec_smul, hA0, smul_smul, smul_smul, mul_comm]

theorem factTorusLineSp4_holds : Ch11.SecC.FactTorusLineSp4 := by
  intro F _ _ n hn hF W _ _ hW H Z π hπ S hS
  obtain ⟨f, hf⟩ := exists_isCoord (linModelNat _) hπ
  obtain ⟨g, hg⟩ := exists_sylow_eq_conj_Usp hF (by omega) hf hS
  have hfix := fixedW_iff_sp hf hg
  refine ⟨?_, fun y hy hyN => ?_⟩
  · rw [Nat.card_congr (Equiv.subtypeEquivRight hfix)]
    change Nat.card ↥(hf.pre (gmapSp g (spLine F)).toAddSubgroup) = _
    have h := Subgroup.relIndex_mul_card Z (hf.pre (gmapSp g (spLine F)).toAddSubgroup)
    rw [inf_eq_left.mpr (hf.le_pre _), ← hf.card_img, hf.img_pre] at h
    have hc : Nat.card ↥(gmapSp g (spLine F)).toAddSubgroup = 2 ^ n :=
      (card_gmapSp g (spLine F)).trans (card_spLine.trans hF)
    rw [← h, hc]
  · obtain ⟨γ, hγ⟩ : ∃ γ : StatedSp 2 F, π γ = ⟨y, hy⟩ := hf.onto ⟨y, hy⟩
    have hyγ : y = ((π γ : ↥H) : MulAut W) := by rw [hγ]
    have hmaps : ∀ w, f w ∈ gmapSp g (spLine F) →
        f (((π γ : ↥H) : MulAut W) w) ∈ gmapSp g (spLine F) := by
      intro w hw
      rw [← hyγ, ← hfix]
      intro s hs
      have hs' : y⁻¹ * s * y ∈ S := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hyN) s).mp hs
        rwa [inv_inv] at this
      have h1 := (hfix w).mpr hw _ hs'
      have hy0 : ∀ v, f v = 0 → f (y v) = 0 := by
        intro v hv
        rw [hyγ, hf.act4, hv, Matrix.mulVec_zero]
      have h2 : f (y (((y⁻¹ * s * y) w) * w⁻¹)) = 0 := hy0 _ ((hf.ker _).mpr h1)
      rw [← hf.ker]
      rw [map_mul, map_inv] at h2
      rwa [show y ((y⁻¹ * s * y) w) = s (y w) by simp [MulAut.mul_apply]] at h2
    obtain ⟨c, hc⟩ := exists_scalar_of_stab_sp hf hmaps
    by_cases hc1 : c = 1
    · left
      intro w hw
      rw [← hf.ker, hf.map_mul_inv, hyγ, hc w ((hfix w).mp hw), hc1, one_smul, sub_self]
    · right
      intro w hw hyw
      rw [← hf.ker, hf.map_mul_inv, hyγ, hc w ((hfix w).mp hw)] at hyw
      have h1 : (c - 1) • f w = 0 := by
        rw [sub_smul, one_smul]
        exact hyw
      rw [← hf.ker]
      exact (smul_eq_zero.mp h1).resolve_left (sub_ne_zero.mpr hc1)

end CFSG.Quasithin.Vol2.KGNat
