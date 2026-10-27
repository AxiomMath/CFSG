module

public import CFSG.Quasithin.Vol2.Ch10SecQ2Orb
public import CFSG.Quasithin.Vol2.Ch10SecQ2Comb

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecE.C10P02

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {hyp : Hyp10 G T L I} {t : G}
  (D : Case2Data hyp t)

theorem tau_ne_one (i : Fin 4) : D.tau i ≠ 1 := by
  have h₁ : ∀ σ : Equiv.Perm (Fin 5), σ ≠ 1 → ((D.θ₁.symm σ : ↥D.K₁) :
      MulAut (IntMod (fsuVM T L I) (SecA.isElemAbelian_fsuVM hyp))) ≠ 1 := by
    intro σ hσ h
    exact hσ ((MulEquiv.map_eq_one_iff D.θ₁.symm).mp (Subtype.ext h))
  have h₂ : ∀ σ : Equiv.Perm (Fin 5), σ ≠ 1 → ((D.θ₂.symm σ : ↥D.K₂) :
      MulAut (IntMod (fsuVM T L I) (SecA.isElemAbelian_fsuVM hyp))) ≠ 1 := by
    intro σ hσ h
    exact hσ ((MulEquiv.map_eq_one_iff D.θ₂.symm).mp (Subtype.ext h))
  fin_cases i
  exacts [h₁ sA sA_ne_one, h₁ sB sB_ne_one, h₂ sA sA_ne_one, h₂ sB sB_ne_one]

theorem gam_self : gam D (fsuVM T L I) = ∅ := by
  have hV := SecA.isElemAbelian_fsuVM hyp
  have hab := hV.1
  have hbot : autI hV (fsuVM T L I) = ⊥ := autI_eq_bot_of_le_centralizer hV fun v hv =>
    Subgroup.mem_centralizer_iff.mpr fun w hw => setLike_mul_comm hw hv
  refine Finset.eq_empty_of_forall_notMem fun i hi => ?_
  rw [mem_gam, hbot, Subgroup.mem_bot] at hi
  exact tau_ne_one D i hi

theorem Yg_empty : D.Yg ∅ = ⊥ := by
  refine eq_bot_iff.mpr fun p hp => ?_
  obtain ⟨S, hS, rfl⟩ := D.mem_Yg.mp hp
  rw [Finset.subset_empty.mp hS, D.tauS_empty]
  exact Subgroup.one_mem _

theorem normalizer_baum_le_normalizer (hT : ¬ 2 ∣ T.index)
    (hC0 : T ⊓ Subgroup.centralizer (fsuL0 T L : Set G) = ⊥)
    (hCV : T ⊓ Subgroup.centralizer (fsuVM T L I : Set G) ≤ fsuVM T L I)
    {q : Fin 4 → Subgroup.normalizer (fsuVM T L I : Set G)} (hqT : ∀ i, (q i : G) ∈ T)
    (hq2 : ∀ i, (q i : G) ^ 2 = 1) (hqc : ∀ i j, (q i : G) * q j = q j * q i)
    (hqτ : ∀ i, convI (SecA.isElemAbelian_fsuVM hyp) (q i) = D.tau i)
    {ρ : Subgroup.normalizer (fsuVM T L I : Set G)} (hρT : (ρ : G) ∈ T)
    (hρ : convI (SecA.isElemAbelian_fsuVM hyp) ρ * D.tau 0 *
      (convI (SecA.isElemAbelian_fsuVM hyp) ρ)⁻¹ = D.tau 1)
    {s : Subgroup.normalizer (fsuVM T L I : Set G)} (hsT : (s : G) ∈ T) {j₀ j₁ : Fin 4}
    (hj₀ : j₀ = 2 ∨ j₀ = 3) (hj₁ : j₁ = 2 ∨ j₁ = 3) (hj : j₀ ≠ j₁)
    (hs₀ : convI (SecA.isElemAbelian_fsuVM hyp) s * D.tau 0 *
      (convI (SecA.isElemAbelian_fsuVM hyp) s)⁻¹ = D.tau j₀)
    (hs₁ : convI (SecA.isElemAbelian_fsuVM hyp) s * D.tau 1 *
      (convI (SecA.isElemAbelian_fsuVM hyp) s)⁻¹ = D.tau j₁) :
    Subgroup.normalizer (baum T : Set G) ≤ Subgroup.normalizer (fsuVM T L I : Set G) := by
  classical
  have hV := SecA.isElemAbelian_fsuVM hyp
  have hVS : fsuVM T L I ≤ baum T := (D.fsuVM_le_baum hC0 hCV).2
  have hTN : T ≤ Subgroup.normalizer (baum T : Set G) := le_normalizer_baum T
  have hTV : T ≤ Subgroup.normalizer (fsuVM T L I : Set G) := SecA.le_normalizer_fsuVM T L I
  have hodd : Odd (orbF (Subgroup.normalizer (baum T : Set G)) (fsuVM T L I)).card :=
    odd_card_orbF hTN hTV hT
  have ha01 := card_filter_gam_eq D (hTN hρT) hρ
  have ha0 := card_filter_gam_eq D (hTN hsT) hs₀
  have ha1 := card_filter_gam_eq D (hTN hsT) hs₁
  set a : Fin 4 → ℕ := fun i =>
    ((orbF (Subgroup.normalizer (baum T : Set G)) (fsuVM T L I)).filter
      fun B => i ∈ gam D B).card with ha
  have h23 : a 2 = a 0 ∧ a 3 = a 0 := by
    rcases hj₀ with rfl | rfl <;> rcases hj₁ with rfl | rfl
    · exact absurd rfl hj
    · exact ⟨ha0.symm, ha1.symm.trans ha01.symm⟩
    · exact ⟨ha1.symm.trans ha01.symm, ha0.symm⟩
    · exact absurd rfl hj
  have hall : ∀ i, a i = a 0 := by
    intro i
    fin_cases i
    exacts [rfl, ha01.symm, h23.1, h23.2]
  have key := eq_empty_of_doubleCount (orbF (Subgroup.normalizer (baum T : Set G)) (fsuVM T L I))
    (gam D) hodd (gam_self D) (fun i j => (hall i).trans (hall j).symm)
    fun B hB => sum_card_symmDiff_eq D hC0 hCV hqT hq2 hqc hqτ hVS hB
  intro x hx
  have hB : cjSub x (fsuVM T L I) ∈ orbF (Subgroup.normalizer (baum T : Set G)) (fsuVM T L I) :=
    mem_orbF.mpr ⟨x, hx, rfl⟩
  obtain ⟨h1, h2, h3⟩ := props_of_mem_orbF hVS hV hB
  obtain ⟨hY, -, -⟩ := cls D hC0 hCV hqT hq2 hqc hqτ h1 h2 h3
  rw [key _ hB, Yg_empty] at hY
  have hBT : cjSub x (fsuVM T L I) ≤ T := h1.trans inf_le_left
  have hC := (autI_eq_bot_iff hV (hBT.trans hTV)).mp hY
  have hle : cjSub x (fsuVM T L I) ≤ fsuVM T L I := fun y hy => hCV ⟨hBT hy, hC hy⟩
  exact cjSub_eq_iff.mp (Subgroup.eq_of_le_of_card_ge hle h3.ge)

end CFSG.Quasithin.Vol2.Ch10.SecE.C10P02
