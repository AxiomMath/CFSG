module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5OutLieV
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModU5

public section

namespace CFSG.Quasithin.H13.F431.Un.OL5

open Matrix Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp CFSG.LocalAnalysis.EvenBN.U5 CFSG.Quasithin.H13.Sec53F.Unit
  CFSG.Quasithin.H13.Sec53F

variable {f : ℕ} {K : Type} [Field K] (hK : UnitaryFieldData 2 f K)

theorem un5v_normalizer_V : Subgroup.normalizer
    ((((Vsub hK).map (hypProj hK 2 1) : Subgroup (hypPSU hK 2 1))) : Set (hypPSU hK 2 1)) =
      u5LnP hK := by
  have hY := u5_yamStd (h := hK)
  refine le_antisymm ?_ u5LnP_le_normalizer
  rcases hY.coatom₁.le_iff.1 (u5LnP_le_normalizer (h := hK)) with hN | hN
  · exfalso
    exact map_Vsub_ne_bot (h := hK)
      (hY.no_normal _ (Subgroup.normalizer_eq_top_iff.1 hN) isPGroup_map_Vsub)
  · exact hN.le

theorem un5v_Vh_eq : Vh hK = ((Vsub hK).map (hypProj hK 2 1)).map
    (MulAut.conj : hypPSU hK 2 1 →* MulAut (hypPSU hK 2 1)) := by
  rw [Vh, Subgroup.map_map]
  rfl

theorem un5v_cj_mem_normalizer_Vh {g : hypPSU hK 2 1}
    (hg : MulAut.conj g ∈ Subgroup.normalizer (Vh hK : Set (MulAut (hypPSU hK 2 1)))) :
    g ∈ u5LnP hK := by
  have inj := conj_injective (u5_center_eq_bot hK)
  rw [← un5v_normalizer_V hK, Subgroup.mem_normalizer_iff]
  intro x
  rw [Subgroup.mem_normalizer_iff] at hg
  have h1 := hg (MulAut.conj x)
  rw [un5v_Vh_eq hK, Subgroup.mem_map_iff_mem inj] at h1
  rw [h1, ← map_inv, ← map_mul, ← map_mul, Subgroup.mem_map_iff_mem inj]

theorem un5v_lev_mem_u5LnStab (A : Matrix (Fin 2) (Fin 2) K) (hA : IsUnit A.det) :
    lev A hA ∈ u5LnStab hK := by
  rw [mem_u5LnStab_iff, mat_lev]
  intro a b hb ha
  rcases hb with rfl | rfl <;> rcases ha with rfl | rfl | rfl <;>
    simp [ιe₁, ιe₂, ιz, ιf₁, ιf₂, oddDiag]

theorem un5v_irr {R : Subgroup (MulAut (hypPSU hK 2 1))} (hRS : R ≤ Sh hK) (hVR : Vh hK ≤ R)
    (hL : ∀ (A : Matrix (Fin 2) (Fin 2) K) (hA : IsUnit A.det),
      innM hK (lev A hA) ∈ Subgroup.normalizer (R : Set (MulAut (hypPSU hK 2 1)))) :
    R = Vh hK ∨ R = Sh hK := by
  set R'' : Subgroup (hypSU hK 2 1) := R.comap (innM hK) ⊓ Ssub hK with hR''
  have hSS : R'' ≤ Ssub hK := inf_le_right
  have hLev : ∀ (A : Matrix (Fin 2) (Fin 2) K) (hA : IsUnit A.det), ∀ r ∈ R'',
      lev A hA * r * (lev A hA)⁻¹ ∈ R'' := by
    intro A hA r hr
    refine ⟨?_, lev_conj_mem_Ssub A hA hr.2⟩
    have h1 := (Subgroup.mem_normalizer_iff.1 (hL A hA) (innM hK r)).1 hr.1
    rw [← map_inv, ← map_mul, ← map_mul] at h1
    exact h1
  have hzR : z₁SU hK ∈ R'' :=
    ⟨hVR (un5_V_zt hK).1, Vsub_le_Ssub (ZPsub_le_Vsub z₁SU_mem_ZPsub)⟩
  have hmap : R = R''.map (innM hK) := by
    ext ρ
    constructor
    · intro hρ
      obtain ⟨s, hs, rfl⟩ := hRS hρ
      exact ⟨s, ⟨hρ, hs⟩, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      exact hs.1
  rcases irreducible_Ssub hSS hLev with h | h | h
  · exfalso
    have := hzR
    rw [h, Subgroup.mem_bot] at this
    exact z₁SU_ne_one this
  · exact Or.inl (hmap.trans (by rw [h]; rfl))
  · exact Or.inr (hmap.trans (by rw [h]; rfl))

end CFSG.Quasithin.H13.F431.Un.OL5
