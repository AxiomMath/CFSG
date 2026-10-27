module

public import CFSG.Quasithin.Vol2.Ch10SecEE3Tau

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecE

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique Equiv

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

namespace Case2Data

variable {hyp : Hyp10 G T L I} {t : G} (D : Case2Data hyp t)

theorem tauS_pair01 : D.tauS {0, 1} = ((D.θ₁.symm (sA * sB) : ↥D.K₁) : MulAut _) := by
  simp [tauS, pr]

theorem tauS_pair23 : D.tauS {2, 3} = ((D.θ₂.symm (sA * sB) : ↥D.K₂) : MulAut _) := by
  simp [tauS, pr]

theorem parts_of_mul {S : Finset (Fin 4)}
    {a b : MulAut (IntMod (fsuVM T L I) (SecA.isElemAbelian_fsuVM hyp))} (ha : a ∈ D.K₁)
    (hb : b ∈ D.K₂) (h : a * b = D.tauS S) :
    a = ((D.θ₁.symm (pr (decide (0 ∈ S)) (decide (1 ∈ S))) : ↥D.K₁) : MulAut _) ∧
      b = ((D.θ₂.symm (pr (decide (2 ∈ S)) (decide (3 ∈ S))) : ↥D.K₂) : MulAut _) :=
  eq_of_mul_eq_mul D.inf ha (D.θ₁.symm _).2 hb (D.θ₂.symm _).2 h

theorem tauS_inter_01 (S : Finset (Fin 4)) :
    D.tauS (S ∩ {0, 1}) = ((D.θ₁.symm (pr (decide (0 ∈ S)) (decide (1 ∈ S))) : ↥D.K₁) :
      MulAut _) := by
  simp [tauS, pr]

theorem fixV_Yg_inf_one (γ : Finset (Fin 4)) :
    fixV (D.Yg γ) ⊓ commV D.K₁ = fixV (D.Yg γ ⊓ D.P₁) ⊓ commV D.K₁ := by
  refine le_antisymm (inf_le_inf_right _ (fixV_le_fixV inf_le_left)) ?_
  rintro w ⟨hw, hw₁⟩
  refine ⟨?_, hw₁⟩
  rintro _ ⟨S, hS, rfl⟩
  have ha : D.tauS (S ∩ {0, 1}) ∈ D.Yg γ ⊓ D.P₁ := by
    refine ⟨⟨S ∩ {0, 1}, Finset.inter_subset_left.trans hS, rfl⟩, ?_⟩
    rw [D.tauS_inter_01]
    exact (D.memP₁ _ (D.θ₁.symm _).2).mpr (by simpa using pr_mem_eFour _ _)
  have h1 := hw _ ha
  rw [tauS, MulAut.mul_apply, D.triv₂ (D.θ₂.symm _).2 hw₁, ← D.tauS_inter_01]
  exact h1

theorem exact_Yg_inf_one (γ : Finset (Fin 4)) :
    Nat.card ↥(D.Yg γ ⊓ D.P₁) * Nat.card ↥(fixV (D.Yg γ ⊓ D.P₁) ⊓ commV D.K₁) = 16 := by
  refine (factor_bound D.equiv₁ inf_le_left D.memP₁ inf_le_right).2.mpr fun h => ?_
  have h01 : ({0, 1} : Finset (Fin 4)) ⊆ γ := by
    rw [← D.tauS_pair01] at h
    exact D.tauS_mem_Yg_iff.mp h.1
  refine ⟨?_, (D.memP₁ _ (D.θ₁.symm _).2).mpr (by simpa using (by decide : sA ∈ eFour))⟩
  rw [← D.tau_zero]
  exact D.tau_mem_Yg_iff.mpr (h01 (by simp))

theorem exact_Yg_projTwo (γ : Finset (Fin 4)) :
    Nat.card ↥(D.prodSetting.projTwo (D.Yg γ)) *
      Nat.card ↥(fixV (D.prodSetting.projTwo (D.Yg γ)) ⊓ commV D.K₂) = 16 := by
  refine (factor_bound D.equiv₂ inf_le_left D.memP₂ (D.prodSetting.projTwo_le _)).2.mpr
    fun h => ?_
  obtain ⟨-, a, ha, hab⟩ := (D.prodSetting.mem_projTwo_iff (D.Yg_le_P γ)).mp h
  obtain ⟨S, hS, e⟩ := D.mem_Yg.mp hab
  obtain ⟨-, hb⟩ := D.parts_of_mul ha.1 (D.θ₂.symm _).2 e.symm
  have hb' := D.θ₂.symm.injective (Subtype.ext hb)
  obtain ⟨h2, h3⟩ := pr_inj true true _ _ ((by decide : pr true true = sA * sB).trans hb')
  have h2S : (2 : Fin 4) ∈ γ := hS (by simpa using h2.symm)
  refine (D.prodSetting.mem_projTwo_iff (D.Yg_le_P γ)).mpr
    ⟨(D.memP₂ _ (D.θ₂.symm _).2).mpr (by simpa using (by decide : sA ∈ eFour)), 1,
      Subgroup.one_mem _, ?_⟩
  rw [one_mul, ← D.tau_two]
  exact D.tau_mem_Yg_iff.mpr h2S

theorem exact_Yg (γ : Finset (Fin 4)) :
    Nat.card ↥(D.Yg γ) * Nat.card ↥(fixV (D.Yg γ) ⊓ (commV D.K₁ ⊔ commV D.K₂)) =
      Nat.card ↥(commV D.K₁ ⊔ commV D.K₂) := by
  obtain ⟨e, -, -, -⟩ := D.prodSetting.card_mul_card_fixV_le_aux D.bound₁ D.bound₂
    (D.Yg_le_P γ)
  rw [e, D.fixV_Yg_inf_one, D.exact_Yg_inf_one, D.exact_Yg_projTwo, D.prodSetting.card_sup,
    D.card_commV₁, D.card_commV₂]

theorem card_fixV_Yg (hC0 : T ⊓ Subgroup.centralizer (fsuL0 T L : Set G) = ⊥)
    (γ : Finset (Fin 4)) : Nat.card ↥(fixV (D.Yg γ)) * 2 ^ γ.card = 256 := by
  have h := D.exact_Yg γ
  rw [D.prodSetting.card_sup, D.card_commV₁, D.card_commV₂, D.commV_sup_eq_top hC0,
    inf_top_eq, D.card_Yg] at h
  rw [mul_comm]
  exact h

end Case2Data

end CFSG.Quasithin.Vol2.Ch10.SecE
