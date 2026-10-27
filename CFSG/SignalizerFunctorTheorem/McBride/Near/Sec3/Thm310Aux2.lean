module

public import CFSG.SignalizerFunctorTheorem.McBride.Models.ModelFacts
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.Thm310Aux1

public section

open CFSG.Open
open CFSG.SignalizerFunctorTheorem.McBride
open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Thm310

variable {Γ : Type u} [Group Γ] [Finite Γ]

theorem cenIn_mem_iPairsY {p : ℕ} {A X Y X₁ X₂ B : Subgroup Γ} (h : NearAsolvAction p A X)
    (hP : (X₁, X₂) ∈ iPairsY A X Y) (hBA : B ≤ A) (hB : B ≤ secCenIn A X₁ X₂) :
    (cenIn X₁ (B : Set Γ), cenIn X₂ (B : Set Γ)) ∈ iPairsY A X Y := by
  obtain ⟨hCS, -⟩ := Thm34.chiefSetting_qimg h hP.1
  have hch := Thm32.chief_of_mem_iPairsY hP
  have hinf := Thm32.inf_eq_of_mem_iPairsY hP
  have hX₁ := Thm32.isDAIn_left_of_mem_iPairsY hP
  have hX₂ := Thm32.isDAIn_right_of_mem_iPairsY hP
  set D := cenIn X (A : Set Γ) with hD
  have hDX : D ≤ X := inf_le_left
  have hDA : D ≤ Subgroup.centralizer (A : Set Γ) := inf_le_right
  have hGX : X₁ ⊔ D ≤ X := sup_le hX₁.1 hDX
  have hcop : Nat.Coprime p (Nat.card ↥(X₁ ⊔ D)) :=
    h.nearPSolvable.1.coprime_dvd_right (Subgroup.card_dvd_of_le hGX)
  have S : Thm32.BackSetting p A D X₁ X₂ B := ⟨h.prime, h.elemAbelian, hDA, hcop, hch, hBA⟩
  have hqB : AChief.qimg X₂ B ≤ Subgroup.centralizer
      ((AChief.qimg X₂ X₁ : Subgroup (AChief.QG X₂)) : Set (AChief.QG X₂)) := by
    refine qimg_le_centralizer_of_comm fun b hb y hy => ?_
    obtain ⟨-, hbs⟩ := Subgroup.mem_inf.mp (hB hb)
    exact (mem_sectionCentralizer_iff.mp hbs).2.2 y hy
  have hqX₁ : AChief.qimg X₂ X₁ ≤ Subgroup.centralizer
      ((AChief.qimg X₂ B : Subgroup (AChief.QG X₂)) : Set (AChief.QG X₂)) :=
    Subgroup.le_centralizer_iff.mp hqB
  have hDq : AChief.qimg X₂ D ≤ Subgroup.centralizer
      ((AChief.qimg X₂ B : Subgroup (AChief.QG X₂)) : Set (AChief.QG X₂)) :=
    Thm32.qimg_le_centralizer S.D_le_cen_B
  have hcen1 : cenIn (AChief.qimg X₂ X₁) (AChief.qimg X₂ B : Set (AChief.QG X₂)) =
      AChief.qimg X₂ X₁ := inf_eq_left.mpr hqX₁
  have hcen2 : cenIn (AChief.qimg X₂ (X₁ ⊔ D)) (AChief.qimg X₂ B : Set (AChief.QG X₂)) =
      AChief.qimg X₂ (X₁ ⊔ D) := by
    refine inf_eq_left.mpr ?_
    rw [SolQuot.qimg_sup S.X₁_le_nrm S.D_le_nrm]
    exact sup_le hqX₁ hDq
  have hns : ¬ Group.IsSolvable ↥(cenIn (AChief.qimg X₂ X₁)
      (AChief.qimg X₂ B : Set (AChief.QG X₂))) := by
    rw [hcen1]
    exact hCS.not_isSolvable
  have hch' : IsChiefFactorOf (AChief.qimg X₂ A ⊔ cenIn (AChief.qimg X₂ (X₁ ⊔ D))
      (AChief.qimg X₂ B : Set (AChief.QG X₂))) (cenIn (AChief.qimg X₂ X₁)
        (AChief.qimg X₂ B : Set (AChief.QG X₂))) ⊥ := by
    rw [hcen1, hcen2, sup_comm]
    exact hCS.chief
  have hsol : sol (cenIn (AChief.qimg X₂ (X₁ ⊔ D))
      (AChief.qimg X₂ B : Set (AChief.QG X₂))) = ⊥ := by
    rw [hcen2]
    exact hCS.sol_eq_bot
  refine Thm32.mem_iPairsY_of ?_ ?_ ?_ ?_ ?_
  · exact ⟨inf_le_left.trans hX₁.1, Thm32.le_normalizer_inf hX₁.2
      ((sup_le S.D_le_cen_B S.A_le_cen_B).trans Subgroup.le_normalizer)⟩
  · exact ⟨inf_le_left.trans hX₂.1, Thm32.le_normalizer_inf hX₂.2
      ((sup_le S.D_le_cen_B S.A_le_cen_B).trans Subgroup.le_normalizer)⟩
  · exact S.isChiefFactorOf_cen hns hch'
  · exact S.secCenIn_cen h.solvable_cen hns hch' hsol
  · calc cenIn X₂ (B : Set Γ) ⊓ D = X₂ ⊓ D :=
        le_antisymm (inf_le_inf_right _ inf_le_left)
          (le_inf (le_inf inf_le_left (inf_le_right.trans S.D_le_cen_B)) inf_le_right)
      _ = Y := hinf

theorem semisimple_pow_five
    {p : ℕ} (hp3 : p = 3) {A G : Subgroup Γ}
    (h : SemisimpleAction p A G) :
    ∀ x ∈ CFSG.fittingSubgroupOf (cenIn G (A : Set Γ)), x ^ 5 = 1 := by
  intro x hx
  set D : Subgroup Γ := cenIn G (A : Set Γ) with hDdef
  have hxD : x ∈ D := Subgroup.map_subtype_le _ hx
  have hDG : D ≤ G := inf_le_left
  have hxG : x ∈ G := hDG hxD
  have hdp := h.isDirectProduct_lcal
  have hFD : CFSG.fittingSubgroupOf D ≤ G := (Subgroup.map_subtype_le _).trans hDG
  have key : (⟨x, hxG⟩ : ↥G) ^ 5 = 1 := by
    apply hdp.ext_coord
    intro J hJ
    rw [map_pow, map_one]
    have hmem : ((hdp.coord hJ ⟨x, hxG⟩ : J) : Γ) ∈
        projIn (lcal G) J (CFSG.fittingSubgroupOf D) :=
      (hdp.mem_projIn_iff hJ).mpr ⟨⟨x, hxG⟩, hx, rfl⟩
    have hDP : projIn (lcal G) J D = cenIn J (norIn A J) := h.projIn_cenIn hJ
    have hPJ : projIn (lcal G) J (CFSG.fittingSubgroupOf D) ≤
        CFSG.fittingSubgroupOf (cenIn J (norIn A J)) := by
      refine Thm210.le_fittingSubgroupOf_of_nilpotent ?_ ?_ ?_
      · rw [← hDP]
        exact Thm210.projIn_mono J (Subgroup.map_subtype_le _)
      · rw [← hDP]
        refine Thm210.le_normalizer_of_conj_mem ?_
        exact Thm210.projIn_conj_mem hdp hJ fun y hy z hz =>
          Thm210.fittingSubgroupOf_conj_mem hy hz
      · exact Thm210.isNilpotent_projIn hdp hJ hFD (Thm210.isNilpotent_fittingSubgroupOf D)
    have hw := hPJ hmem
    obtain ⟨f, hf, -, hC₀, -, -⟩ := h.exists_frame_data hJ
    have hcard : Nat.card ↥(fixedFitting f) = 5 :=
      (NearSimple.p_eq_three (h.nearSimple hJ) hf hp3).2
    rw [← hC₀] at hw
    obtain ⟨w, hw1, hw2⟩ := hw
    have hw5 : (⟨w, hw1⟩ : ↥(fixedFitting f)) ^ 5 = 1 := by
      have := pow_card_eq_one' (G := ↥(fixedFitting f)) (x := ⟨w, hw1⟩)
      rwa [hcard] at this
    apply Subtype.ext
    have h6 : (w : Γ) ^ 5 = 1 := by
      have := congrArg (fun z : ↥(fixedFitting f) => ((z : ↥J) : Γ)) hw5
      simpa using this
    simpa [← hw2] using h6
  simpa using congrArg Subtype.val key

theorem core_pow_five
    {p : ℕ} (hp3 : p = 3) {A G K D : Subgroup Γ}
    (H : Thm32.ChiefSetting p A G K D) (hD : cenIn G (A : Set Γ) = D) :
    ∀ x ∈ CFSG.fittingSubgroupOf D, x ^ 5 = 1 := by
  have hmin : IsChiefFactorOf (G ⊔ A) (layerIn G) ⊥ := by
    rw [H.layerIn_eq]
    exact H.chief
  have hL : Lemma212.Hyp p A G := ⟨H.near, H.sol_eq_bot, hmin, H.prod_eq⟩
  have hKk : kOf G = K := hL.layerIn_eq.symm.trans H.layerIn_eq
  have hs : SemisimpleAction p A (kOf G) := hL.semisimpleAction
  have hDK : D ⊓ K = cenIn (kOf G) (A : Set Γ) := by
    rw [hKk, ← hD, inf_comm]
    exact Thm211.inf_cenIn_eq H.K_le
  intro x hx
  have hx' : x ∈ CFSG.fittingSubgroupOf (cenIn (kOf G) (A : Set Γ)) := by
    rw [← hDK, ← (Thm34.core34 H hD).1]
    exact hx
  exact semisimple_pow_five hp3 hs x hx'

theorem pow_five_mem_of_mem_fittingPre
    {p : ℕ} (hp3 : p = 3) {A X D Y X₁ X₂ : Subgroup Γ}
    (h : NearAsolvAction p A X) (hD : cenIn X (A : Set Γ) = D)
    (hP : (X₁, X₂) ∈ iPairsY A X Y) [(Y.subgroupOf D).Normal] :
    ∀ x ∈ fittingPre D Y, x ^ 5 ∈ Y := by
  subst hD
  obtain ⟨hCS, hcen⟩ := Thm34.chiefSetting_qimg h hP.1
  have hch := Thm32.chief_of_mem_iPairsY hP
  have hDn : cenIn X (A : Set Γ) ≤ AChief.nrm X₂ :=
    (le_sup_right.trans le_sup_left).trans hch.1.2
  have hYeq : cenIn X (A : Set Γ) ⊓ X₂ = Y := by
    rw [inf_comm]
    exact Thm32.inf_eq_of_mem_iPairsY hP
  have e1 := Thm34.fittingPre_eq_inf_qpre hDn hYeq
  intro x hx
  rw [e1] at hx
  obtain ⟨hxD, hxq⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨hxn, hxF⟩ := SolQuot.mem_qpre_iff.mp hxq
  have h5 := core_pow_five hp3 hCS hcen _ hxF
  have hker : (⟨x, hxn⟩ : ↥(AChief.nrm X₂)) ^ 5 ∈ X₂.subgroupOf (AChief.nrm X₂) := by
    rw [← QuotientGroup.eq_one_iff]
    change AChief.qmap X₂ _ = 1
    rw [map_pow]
    exact h5
  have hx5 : x ^ 5 ∈ X₂ := by
    have := Subgroup.mem_subgroupOf.mp hker
    simpa using this
  rw [← hYeq]
  exact Subgroup.mem_inf.mpr ⟨pow_mem hxD 5, hx5⟩

end CFSG.SignalizerFunctorTheorem.McBride.Near.Thm310
