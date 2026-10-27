module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5OutLieVC

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.OL5

open Matrix Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp CFSG.LocalAnalysis.EvenBN.U5 CFSG.Quasithin.H13.Sec53F.Unit
  CFSG.Quasithin.H13.Sec53F CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
  CFSG.RankThree.PartOne.U5K

variable {f : ℕ} {K : Type} [Field K] (hK : UnitaryFieldData 2 f K)

theorem un5v_cj_mem_N' {K₁ : Subgroup (MulAut (hypPSU hK 2 1))} (hP : Pi hK ≤ K₁)
    {g : hypPSU hK 2 1} (hg : g ∈ u5LnP hK) :
    MulAut.conj g ∈ K₁ ⊓ autStab (u5LnP hK) := by
  refine ⟨hP ⟨g, rfl⟩, fun x => ?_⟩
  rw [MulAut.conj_apply]
  constructor
  · intro hx
    exact mul_mem (mul_mem hg hx) (inv_mem hg)
  · intro hx
    have := mul_mem (mul_mem (inv_mem hg) hx) hg
    simpa [mul_assoc] using this

theorem un5v_stab_le_normalizer_Q {α : MulAut (hypPSU hK 2 1)} (hα : α ∈ autStab (u5LnP hK)) :
    α ∈ Subgroup.normalizer (un5vQ hK : Set (MulAut (hypPSU hK 2 1))) := by
  rw [Subgroup.mem_normalizer_iff]
  intro ρ
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨α y, (hα y).1 hy, (aut5_mul_cj5_mul_inv hK α y).symm⟩
  · rintro ⟨y, hy, hyρ⟩
    have hα' := (autStab (u5LnP hK)).inv_mem hα
    refine ⟨α⁻¹ y, (hα' y).1 hy, ?_⟩
    have e := aut5_mul_cj5_mul_inv hK α⁻¹ y
    have : ρ = α⁻¹ * (α * ρ * α⁻¹) * α := by group
    rw [this, ← hyρ]
    exact e.symm.trans (by group)

theorem un5v_normalizes_Vh (hf : 2 ≤ f) {α : MulAut (hypPSU hK 2 1)}
    (hα : α ∈ autStab (u5LnP hK)) :
    α ∈ Subgroup.normalizer (Vh hK : Set (MulAut (hypPSU hK 2 1))) := by
  have := un5v_normalizer_center_pCore (un5v_stab_le_normalizer_Q hK hα)
  rwa [un5v_center_pCore_Q hK hf] at this

theorem un5_V_eq (hf : 2 ≤ f) {K₁ : Subgroup (MulAut (hypPSU hK 2 1))} (hP : Pi hK ≤ K₁) :
    Vh hK = centerOf (pCoreOf 2 (K₁ ⊓ autStab (u5LnP hK))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := finite_mulAut_hyp hK
  set N' := K₁ ⊓ autStab (u5LnP hK) with hN'
  have hVN : Vh hK ≤ N' := by
    rw [un5v_Vh_eq]
    rintro _ ⟨y, hy, rfl⟩
    exact un5v_cj_mem_N' hK hP (un5v_V'_le hK hf hy)
  have hVR : Vh hK ≤ pCoreOf 2 N' :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hVN
      (fun α hα => un5v_normalizes_Vh hK hf hα.2) (un5v_isPGroup_Vh hK)
  have hRS : pCoreOf 2 N' ≤ Sh hK := by
    refine core_Sh (u5_center_eq_bot hK) (un5v_four_le hf)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _) ?_
    intro ρ hρP hρS
    obtain ⟨g, rfl⟩ := hρP
    have hg := un5v_cj_mem_normalizer_Vh hK (mem_normalizer_Vh_of_Sh (u5_center_eq_bot hK) hρS)
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ (un5v_cj_mem_N' hK hP hg)
  rcases un5v_irr hK hRS hVR (fun A hA => CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
    (un5v_cj_mem_N' hK hP (g := hypProj hK 2 1 (lev A hA))
      ⟨lev A hA, un5v_lev_mem_u5LnStab hK A hA, rfl⟩)) with h | h
  · rw [h]
    ext x
    rw [mem_centerOf_iff]
    exact ⟨fun hx => ⟨hx, fun s hs => Vh_comm hs hx⟩, fun hx => hx.1⟩
  · rw [h, un5v_centerOf_eq_zOf, zOf_Sh (u5_center_eq_bot hK)]

end CFSG.Quasithin.H13.F431.Un.OL5
