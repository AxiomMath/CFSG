module

public import CFSG.LocalAnalysis.StandardType.GGF4ReflGroup

public section

namespace CFSG.StandardType.F4Model

namespace F4Rep

variable {W : Type} [Group W] (R : F4Rep W)

private theorem cls_eq_of_forall_ne_cls {κ : Type*} (S : Finset κ) {tL tK : W} {t : κ → W}
    (hL : R.IsRefl tL) (hK : R.IsRefl tK) (ht : ∀ i ∈ S, R.IsRefl (t i))
    (hLK : R.cls tK ≠ R.cls tL) (hKS : ∀ i ∈ S, R.cls (t i) ≠ R.cls tK) :
    ∀ i ∈ S, R.cls (t i) = R.cls tL := by
  intro i hi
  rcases R.cls_eq_one_or_two (ht i hi) with hti | hti <;>
    rcases R.cls_eq_one_or_two hL with hLi | hLi <;>
    rcases R.cls_eq_one_or_two hK with hKi | hKi <;>
    simp_all

private theorem false_of_forall_commute {κ : Type*} (S : Finset κ) {tL : W} {t : κ → W}
    (hL : R.IsRefl tL) (ht : ∀ i ∈ S, R.IsRefl (t i))
    (hcomm : ∀ i ∈ S, ∀ j ∈ S, Commute tL (t i) → Commute tL (t j) → t i = t j)
    (hcls : ∀ i ∈ S, R.cls (t i) = R.cls tL) (hall : ∀ i ∈ S, Commute tL (t i))
    (hgen : Subgroup.centralizer ({tL} : Set W) ⊔
      ⨆ i ∈ S, Subgroup.centralizer ({t i} : Set W) = ⊤) : False := by
  rcases S.eq_empty_or_nonempty with rfl | ⟨i₀, hi₀⟩
  · have hbot : (⨆ i ∈ (∅ : Finset κ), Subgroup.centralizer ({t i} : Set W)) = ⊥ := by simp
    have htop : Subgroup.centralizer ({tL} : Set W) = ⊤ := by
      simpa [hbot] using hgen
    have hne := R.centralizer_sup_ne_top hL hL rfl (Commute.refl tL)
    rw [sup_idem] at hne
    exact hne htop
  · have hle : Subgroup.centralizer ({tL} : Set W) ⊔
        ⨆ i ∈ S, Subgroup.centralizer ({t i} : Set W) ≤
        Subgroup.centralizer ({tL} : Set W) ⊔
          Subgroup.centralizer ({t i₀} : Set W) := by
      refine sup_le le_sup_left ?_
      refine iSup_le fun i => iSup_le fun hi => ?_
      rw [hcomm i hi i₀ hi₀ (hall i hi) (hall i₀ hi₀)]
      exact le_sup_right
    have htop : Subgroup.centralizer ({tL} : Set W) ⊔
        Subgroup.centralizer ({t i₀} : Set W) = ⊤ := top_le_iff.mp (hgen ▸ hle)
    exact R.centralizer_sup_ne_top hL (ht i₀ hi₀) (hcls i₀ hi₀) (hall i₀ hi₀) htop

private theorem false_of_exists_not_commute {κ : Type*} (S : Finset κ) {tL tK : W}
    {t : κ → W} (hL : R.IsRefl tL) (hK : R.IsRefl tK) (ht : ∀ i ∈ S, R.IsRefl (t i))
    (hplane : ∀ i ∈ S, ¬ Commute tL (t i) → ∀ s : W, R.IsRefl s → Commute s tL →
      Commute s (t i) → Commute s tK)
    (hLK : R.cls tK ≠ R.cls tL) (hcls : ∀ i ∈ S, R.cls (t i) = R.cls tL)
    (hni : ∃ i ∈ S, ¬ Commute tL (t i)) : False := by
  obtain ⟨i, hi, hni⟩ := hni
  obtain ⟨s, hs, hsL, hsi, hsK⟩ :=
    R.exists_commute_commute_not_commute hL (ht i hi) hK (hcls i hi) hLK hni
  exact hsK (hplane i hi hni s hs hsL hsi)

theorem exists_conj_of_cover {κ : Type*} (S : Finset κ) {tL tK : W} {t : κ → W}
    (hL : R.IsRefl tL) (hK : R.IsRefl tK) (ht : ∀ i ∈ S, R.IsRefl (t i))
    (hcomm : ∀ i ∈ S, ∀ j ∈ S, Commute tL (t i) → Commute tL (t j) → t i = t j)
    (hplane : ∀ i ∈ S, ¬ Commute tL (t i) → ∀ s : W, R.IsRefl s → Commute s tL →
      Commute s (t i) → Commute s tK)
    (hgen : Subgroup.centralizer ({tL} : Set W) ⊔ ⨆ i ∈ S, Subgroup.centralizer ({t i} : Set W) =
      ⊤) :
    ∃ w : W, w * tK * w⁻¹ = tL ∨ ∃ i ∈ S, w * tK * w⁻¹ = t i := by
  classical
  by_cases hLK : R.cls tK = R.cls tL
  · obtain ⟨w, hw⟩ := R.exists_conj_of_cls_eq hK hL hLK
    exact ⟨w, Or.inl hw⟩
  · by_cases hKS : ∃ i ∈ S, R.cls (t i) = R.cls tK
    · obtain ⟨i, hi, hcls⟩ := hKS
      obtain ⟨w, hw⟩ := R.exists_conj_of_cls_eq hK (ht i hi) hcls.symm
      exact ⟨w, Or.inr ⟨i, hi, hw⟩⟩
    · push Not at hKS
      have hcls := R.cls_eq_of_forall_ne_cls S hL hK ht hLK hKS
      by_cases hall : ∀ i ∈ S, Commute tL (t i)
      · exact (R.false_of_forall_commute S hL ht hcomm hcls hall hgen).elim
      · push Not at hall
        exact (R.false_of_exists_not_commute S hL hK ht hplane hLK hcls hall).elim

end F4Rep

end CFSG.StandardType.F4Model

end
