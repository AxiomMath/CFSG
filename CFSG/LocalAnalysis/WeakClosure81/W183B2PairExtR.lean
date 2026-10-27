module

public import CFSG.LocalAnalysis.WeakClosure81.W183B2Defs
public import CFSG.LocalAnalysis.WeakClosure81.W183Mem
public import CFSG.CGT.PushingUpLit.Transport

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open
  CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

namespace Ctx188

variable {D : Data G} {V₀ V H : Subgroup G} {i : ℕ}

theorem pair_k_eq (x : Ctx188 D V₀ V H i 3) (M : ModDataE H (eOmegaZ H D.T)) {g₁ g₂ : G}
    (hg₂ : Gam183 V H (eOmegaZ H D.T) i g₂) :
    mOfG (M.img (vInH V H g₁))
      (M.img (vInH V H g₁) ⊓ Subgroup.normalizer (M.img (vInH V H g₂) : Set _)) =
      E3.mQuot (vInH V H g₁) (conjSubgroup D.M g₂) := by
  have hAH : vInH V H g₁ ≤ H := inf_le_right
  have hAab : IsElemAbelian 2 (vInH V H g₁) :=
    (E3.isElemAbelian_conjSubgroup x.hyp.setting.isElemAbelian g₁).mono inf_le_left
  have hclaim : M.img (vInH V H g₁ ⊓ conjSubgroup D.M g₂) =
      M.img (vInH V H g₁) ⊓ Subgroup.normalizer (M.img (vInH V H g₂) : Set _) := by
    ext r
    constructor
    · intro hr
      obtain ⟨j, hjmem, rfl⟩ := M.mem_img.1 hr
      obtain ⟨hjA, hjM⟩ := Subgroup.mem_inf.1 hjmem
      exact Subgroup.mem_inf.2 ⟨M.mem_img.2 ⟨j, hjA, rfl⟩,
        Hyp183.img_normalizer_of_mem_conj x.hyp M j.2 hjM⟩
    · intro hr
      obtain ⟨hrA, hrN⟩ := Subgroup.mem_inf.1 hr
      obtain ⟨j, hjA, rfl⟩ := M.mem_img.1 hrA
      have hjM : (j : G) ∈ conjSubgroup D.M g₂ :=
        x.mem_conj_M_of_img_normalizer M hg₂ j.2 hrN
      exact M.mem_img.2 ⟨j, Subgroup.mem_inf.2 ⟨hjA, hjM⟩, rfl⟩
  have hC : vInH V H g₁ ⊓ Subgroup.centralizer (eOmegaZ H D.T : Set G) ≤
      vInH V H g₁ ⊓ conjSubgroup D.M g₂ := by
    intro c hc
    obtain ⟨hcA, hcC⟩ := Subgroup.mem_inf.1 hc
    refine Subgroup.mem_inf.2 ⟨hcA, ?_⟩
    have hcH : c ∈ H := hAH hcA
    have h1 : M.ρ ⟨c, hcH⟩ = 1 := (M.ρ_eq_one_iff _).2 hcC
    refine x.mem_conj_M_of_img_normalizer M hg₂ hcH ?_
    rw [h1]
    exact Subgroup.one_mem _
  calc mOfG (M.img (vInH V H g₁))
        (M.img (vInH V H g₁) ⊓ Subgroup.normalizer (M.img (vInH V H g₂) : Set _))
      = mOfG (M.img (vInH V H g₁)) (M.img (vInH V H g₁ ⊓ conjSubgroup D.M g₂)) := by
        rw [hclaim]
    _ = E3.mQuot (vInH V H g₁) (vInH V H g₁ ⊓ conjSubgroup D.M g₂) :=
        M.mOf_img hAH hAab inf_le_left hC
    _ = E3.mQuot (vInH V H g₁) (conjSubgroup D.M g₂) := mQuot_inf_left _ _

theorem pair_mQuot_bounds (x : Ctx188 D V₀ V H i 3) {g₁ g₂ : G}
    (hg₁ : Gam183 V H (eOmegaZ H D.T) i g₁) :
    E3.mQuot (vInH V H g₁) (conjSubgroup D.M g₂) ≤
        E3.mQuot (conjSubgroup V g₁) (conjSubgroup D.M g₂) ∧
      E3.mQuot (conjSubgroup V g₁) (conjSubgroup D.M g₂) ≤
        E3.mQuot (vInH V H g₁) (conjSubgroup D.M g₂) + i := by
  have hPab : IsElemAbelian 2 (conjSubgroup V g₁) :=
    E3.isElemAbelian_conjSubgroup x.hyp.setting.isElemAbelian g₁
  have hAP : vInH V H g₁ ≤ conjSubgroup V g₁ := inf_le_left
  have hApG : IsPGroup 2 (vInH V H g₁) := (hPab.mono hAP).isPGroup
  have hPpG : IsPGroup 2 (conjSubgroup V g₁) := hPab.isPGroup
  refine ⟨?_, ?_⟩
  · have hne : (conjSubgroup D.M g₂).relIndex (conjSubgroup V g₁) ≠ 0 :=
      Subgroup.index_ne_zero_of_finite
    have hle := Subgroup.relIndex_le_of_le_right hAP hne
    rw [E3.relIndex_eq_two_pow hApG, E3.relIndex_eq_two_pow hPpG] at hle
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hle
  · calc E3.mQuot (conjSubgroup V g₁) (conjSubgroup D.M g₂)
        = E3.mQuot (conjSubgroup V g₁) (conjSubgroup V g₁ ⊓ conjSubgroup D.M g₂) :=
          (mQuot_inf_left _ _).symm
      _ ≤ E3.mQuot (conjSubgroup V g₁) (vInH V H g₁ ⊓ conjSubgroup D.M g₂) :=
          E3.mQuot_mono (inf_le_inf_right _ hAP)
      _ = E3.mQuot (vInH V H g₁) (vInH V H g₁ ⊓ conjSubgroup D.M g₂) +
            E3.mQuot (conjSubgroup V g₁) (vInH V H g₁) := E3.mQuot_add inf_le_left hAP
      _ ≤ E3.mQuot (vInH V H g₁) (conjSubgroup D.M g₂) + i := by
          rw [mQuot_inf_left]
          have h2 : E3.mQuot (conjSubgroup V g₁) (vInH V H g₁) ≤ i := hg₁.1
          omega

theorem pair_one_le_mQuot (x : Ctx188 D V₀ V H i 3) (M : ModDataE H (eOmegaZ H D.T)) {g₁ g₂ : G}
    (hnot : ¬ M.img (vInH V H g₁) ≤ Subgroup.normalizer (M.img (vInH V H g₂) : Set _)) :
    1 ≤ E3.mQuot (vInH V H g₁) (conjSubgroup D.M g₂) := by
  by_contra h0
  have h0' : E3.mQuot (vInH V H g₁) (conjSubgroup D.M g₂) = 0 := by omega
  have hAab : IsElemAbelian 2 (vInH V H g₁) :=
    (E3.isElemAbelian_conjSubgroup x.hyp.setting.isElemAbelian g₁).mono inf_le_left
  have h1 : E3.mQuot (vInH V H g₁) (vInH V H g₁ ⊓ conjSubgroup D.M g₂) = 0 := by
    rw [mQuot_inf_left]
    exact h0'
  have h2 : vInH V H g₁ ⊓ conjSubgroup D.M g₂ = vInH V H g₁ :=
    (E3.mQuot_eq_zero_iff hAab.isPGroup inf_le_left).1 h1
  apply hnot
  intro r hr
  obtain ⟨j, hjA, rfl⟩ := M.mem_img.1 hr
  have hjM : (j : G) ∈ conjSubgroup D.M g₂ := by
    have hj : (j : G) ∈ vInH V H g₁ ⊓ conjSubgroup D.M g₂ := by
      rw [h2]
      exact hjA
    exact (Subgroup.mem_inf.1 hj).2
  exact Hyp183.img_normalizer_of_mem_conj x.hyp M j.2 hjM

end Ctx188

end CFSG.LocalAnalysis.WeakClosure81

end
