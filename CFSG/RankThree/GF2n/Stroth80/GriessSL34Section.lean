module

public import CFSG.RankThree.FFModules.TransvectionConj
public import CFSG.LieType.Steinberg.RankTwo.Statement

public section

namespace CFSG.RankThree.GF2n.Stroth80

open scoped MatrixGroups commutatorElement
open Matrix CFSG.RankThree.FFModules CFSG.LieType.Steinberg
open CFSG.LieType.Universal.SpecialLinear

section Lift

variable {E H : Type*} [Group E] [Group H]

open _root_.Classical in
noncomputable def liftIn (ρ : E →* H) (A : Subgroup E) (g : H) : E :=
  if h : ∃ a ∈ A, ρ a = g then h.choose else 1

theorem liftIn_spec {ρ : E →* H} {A : Subgroup E} {g : H} (hg : g ∈ A.map ρ) :
    liftIn ρ A g ∈ A ∧ ρ (liftIn ρ A g) = g := by
  classical
  have h : ∃ a ∈ A, ρ a = g := Subgroup.mem_map.1 hg
  unfold liftIn
  rw [dif_pos h]
  exact h.choose_spec

theorem eq_of_map_eq_of_inf_ker {ρ : E →* H} {A : Subgroup E} (hA : A ⊓ ρ.ker = ⊥) {a b : E}
    (ha : a ∈ A) (hb : b ∈ A) (h : ρ a = ρ b) : a = b := by
  have hab : a * b⁻¹ ∈ A ⊓ ρ.ker := Subgroup.mem_inf.2
    ⟨A.mul_mem ha (A.inv_mem hb), by rw [MonoidHom.mem_ker, map_mul, map_inv, h, mul_inv_cancel]⟩
  rw [hA, Subgroup.mem_bot, mul_inv_eq_one] at hab
  exact hab

end Lift

section Split

variable {K : Type} [Field K]

theorem sl_x_eq_transvection {γ : Fin 2 → ℤ} (h : (SL.pairOf 2 γ).1 ≠ (SL.pairOf 2 γ).2) (c : K) :
    SL.x 2 K γ c = SpecialLinearGroup.transvection h c := by
  unfold SL.x
  rw [dif_pos h]

theorem sl_x_mem_transvectionGroup (γ : Fin 2 → ℤ) (c : K) :
    SL.x 2 K γ c ∈
      transvectionGroup (K ∙ (Pi.single (SL.pairOf 2 γ).1 1 : Fin 3 → K)) := by
  by_cases h : (SL.pairOf 2 γ).1 ≠ (SL.pairOf 2 γ).2
  · rw [sl_x_eq_transvection h]
    exact transvection_mem_single h c
  · unfold SL.x
    rw [dif_neg h]
    exact Subgroup.one_mem _

omit [Field K] in
theorem pairOf_add_fst_of_chain_left {α β : Fin 2 → ℤ}
    (hα : α ∈ CFSG.LieType.RootSystem.roots (isFiniteType_A 2) ∅)
    (hβ : β ∈ CFSG.LieType.RootSystem.roots (isFiniteType_A 2) ∅) (hαβ : α + β ≠ 0)
    (h : (SL.pairOf 2 α).2 = (SL.pairOf 2 β).1) :
    (SL.pairOf 2 (α + β)).1 = (SL.pairOf 2 α).1 := by
  obtain ⟨-, hα'⟩ := SL.pairOf_spec hα
  obtain ⟨-, hβ'⟩ := SL.pairOf_spec hβ
  have hil : (SL.pairOf 2 α).1 ≠ (SL.pairOf 2 β).2 := fun e => hαβ (by
    apply toStd_injective 2
    rw [SL.toStd_add, hα', hβ', e, h, toStd_zero]
    abel)
  have hsum : toStd 2 (α + β) = Pi.single (SL.pairOf 2 α).1 1 - Pi.single (SL.pairOf 2 β).2 1 := by
    rw [SL.toStd_add, hα', hβ', h]
    abel
  rw [SL.pairOf_eq hil hsum]

omit [Field K] in
theorem pairOf_add_fst_of_chain_right {α β : Fin 2 → ℤ}
    (hα : α ∈ CFSG.LieType.RootSystem.roots (isFiniteType_A 2) ∅)
    (hβ : β ∈ CFSG.LieType.RootSystem.roots (isFiniteType_A 2) ∅) (hαβ : α + β ≠ 0)
    (h : (SL.pairOf 2 β).2 = (SL.pairOf 2 α).1) :
    (SL.pairOf 2 (α + β)).1 = (SL.pairOf 2 β).1 := by
  rw [add_comm α β] at hαβ ⊢
  exact pairOf_add_fst_of_chain_left hβ hα hαβ h

theorem sl_x_add (γ : Fin 2 → ℤ) (c d : K) : SL.x 2 K γ (c + d) = SL.x 2 K γ c * SL.x 2 K γ d := by
  by_cases h : (SL.pairOf 2 γ).1 ≠ (SL.pairOf 2 γ).2
  · rw [sl_x_eq_transvection h, sl_x_eq_transvection h, sl_x_eq_transvection h,
      SpecialLinearGroup.transvection_add]
  · unfold SL.x
    rw [dif_neg h, dif_neg h, dif_neg h, mul_one]

variable [Finite K]

theorem exists_section_of_rowLifts {E : Type} [Group E] (ρ : E →* SL(3, K))
    (𝒜 : Fin 3 → Subgroup E) (hinj : ∀ r, 𝒜 r ⊓ ρ.ker = ⊥)
    (hsurj : ∀ r, transvectionGroup (K ∙ (Pi.single r 1 : Fin 3 → K)) ≤ (𝒜 r).map ρ)
    (hnorm : ∀ r (e : E), ρ e ∈ Subgroup.normalizer
      (transvectionGroup (K ∙ (Pi.single r 1 : Fin 3 → K)) : Set SL(3, K)) →
      e ∈ Subgroup.normalizer (𝒜 r : Set E)) :
    ∃ φ : SL(3, K) →* E, ∀ g, ρ (φ g) = g := by
  classical
  obtain ⟨hB, hgen, huniv, -⟩ := RankTwo.sl3_rankTwoPresentation.{0} K
  obtain ⟨O⟩ := hB.2.1
  set y : (Fin 2 → ℤ) → K → E := fun γ c => liftIn ρ (𝒜 (SL.pairOf 2 γ).1) (SL.x 2 K γ c)
    with hydef
  have hy : ∀ γ c, y γ c ∈ 𝒜 (SL.pairOf 2 γ).1 ∧ ρ (y γ c) = SL.x 2 K γ c := fun γ c =>
    liftIn_spec (hsurj _ (sl_x_mem_transvectionGroup γ c))
  have hA : ∀ γ ∈ (SL.Φ (m := 2) (F := K)).roots, ∀ c d, y γ (c + d) = y γ c * y γ d :=
    fun γ _ c d => eq_of_map_eq_of_inf_ker (hinj _) (hy γ (c + d)).1
      ((𝒜 _).mul_mem (hy γ c).1 (hy γ d).1)
      (by rw [(hy γ (c + d)).2, map_mul, (hy γ c).2, (hy γ d).2, sl_x_add])
  have hBf : CommutatorFormula y O (SL.commC (m := 2)) := by
    intro α hα β hβ hαβ c d
    obtain ⟨hij, hαs⟩ := SL.pairOf_spec (m := 2) hα
    obtain ⟨hkl, hβs⟩ := SL.pairOf_spec (m := 2) hβ
    have hnopp : ¬ ((SL.pairOf 2 α).1 = (SL.pairOf 2 β).2 ∧
        (SL.pairOf 2 α).2 = (SL.pairOf 2 β).1) := by
      rintro ⟨e1, e2⟩
      apply hαβ
      apply toStd_injective 2
      rw [SL.toStd_add, hαs, hβs, e1, e2, toStd_zero]
      abel
    have hfac : ∀ p ∈ O.list α β, p = (1, 1) ∧ SL.Chain α β := fun p hp =>
      (SL.mem_expPairs_iff hα hβ hαβ p).1 ((O.mem_iff α hα β hβ hαβ p).1 hp)
    have hyα := hy α c
    have hyβ := hy β d
    obtain ⟨r, hL, hR⟩ : ∃ r, ⁅y α c, y β d⁆ ∈ 𝒜 r ∧
        ((O.list α β).map fun p => y (p.1 • α + p.2 • β)
          ((SL.commC α β p : K) * c ^ p.1 * d ^ p.2)).prod ∈ 𝒜 r := by
      by_cases hik : (SL.pairOf 2 α).1 = (SL.pairOf 2 β).1
      · refine ⟨(SL.pairOf 2 α).1, ?_, ?_⟩
        · have hb : y β d ∈ 𝒜 (SL.pairOf 2 α).1 := hik ▸ hyβ.1
          rw [commutatorElement_def]
          exact (𝒜 _).mul_mem ((𝒜 _).mul_mem ((𝒜 _).mul_mem hyα.1 hb) ((𝒜 _).inv_mem hyα.1))
            ((𝒜 _).inv_mem hb)
        · refine (𝒜 _).list_prod_mem fun z hz => ?_
          obtain ⟨p, hp, -⟩ := List.mem_map.1 hz
          exfalso
          rcases (hfac p hp).2 with h | h
          · exact hij (hik.trans h.symm)
          · exact hkl (h.trans hik).symm
      · by_cases hli : (SL.pairOf 2 β).2 = (SL.pairOf 2 α).1
        · have hjk : (SL.pairOf 2 α).2 ≠ (SL.pairOf 2 β).1 := fun h => hnopp ⟨hli.symm, h⟩
          have hna : y α c ∈ Subgroup.normalizer (𝒜 (SL.pairOf 2 β).1 : Set E) := by
            refine hnorm _ _ ?_
            rw [hyα.2, SL.x_eq hij hαs]
            exact mem_normalizer_of_mulVec_eq
              (transvection_mulVec_single_of_ne hij (fun h => hjk h.symm) c)
          refine ⟨(SL.pairOf 2 β).1, ?_, ?_⟩
          · have e : ⁅y α c, y β d⁆ = (y α c * y β d * (y α c)⁻¹) * (y β d)⁻¹ := by
              rw [commutatorElement_def]
            rw [e]
            exact (𝒜 _).mul_mem ((Subgroup.mem_normalizer_iff.1 hna _).1 hyβ.1)
              ((𝒜 _).inv_mem hyβ.1)
          · refine (𝒜 _).list_prod_mem fun z hz => ?_
            obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hz
            obtain ⟨rfl, -⟩ := hfac p hp
            simp only [one_smul]
            have hrow := pairOf_add_fst_of_chain_right hα hβ hαβ hli
            have := (hy (α + β) ((SL.commC α β (1, 1) : K) * c ^ 1 * d ^ 1)).1
            rwa [hrow] at this
        · have hnb : y β d ∈ Subgroup.normalizer (𝒜 (SL.pairOf 2 α).1 : Set E) := by
            refine hnorm _ _ ?_
            rw [hyβ.2, SL.x_eq hkl hβs]
            exact mem_normalizer_of_mulVec_eq
              (transvection_mulVec_single_of_ne hkl (fun h => hli h.symm) d)
          refine ⟨(SL.pairOf 2 α).1, ?_, ?_⟩
          · have e : ⁅y α c, y β d⁆ = y α c * (y β d * (y α c)⁻¹ * (y β d)⁻¹) := by
              rw [commutatorElement_def]
              group
            rw [e]
            exact (𝒜 _).mul_mem hyα.1
              ((Subgroup.mem_normalizer_iff.1 hnb _).1 ((𝒜 _).inv_mem hyα.1))
          · refine (𝒜 _).list_prod_mem fun z hz => ?_
            obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hz
            obtain ⟨rfl, hch⟩ := hfac p hp
            have hjk : (SL.pairOf 2 α).2 = (SL.pairOf 2 β).1 := hch.resolve_right hli
            simp only [one_smul]
            have hrow := pairOf_add_fst_of_chain_left hα hβ hαβ hjk
            have := (hy (α + β) ((SL.commC α β (1, 1) : K) * c ^ 1 * d ^ 1)).1
            rwa [hrow] at this
    refine eq_of_map_eq_of_inf_ker (hinj r) hL hR ?_
    rw [map_commutatorElement, hyα.2, hyβ.2, SL.commutatorFormula O α hα β hβ hαβ c d,
      map_list_prod, List.map_map]
    congr 1
    refine List.map_congr_left fun p _ => ?_
    simp only [Function.comp_apply, (hy _ _).2]
  obtain ⟨φ, hφ, -⟩ := huniv O (SL.commC (m := 2)) (SL.commutatorFormula O) E y hA hBf
  have hcomp : ρ.comp φ = MonoidHom.id _ := by
    refine MonoidHom.eq_of_eqOn_dense hgen fun g hg => ?_
    simp only [Set.mem_iUnion] at hg
    obtain ⟨γ, hγ, hgX⟩ := hg
    obtain ⟨c, rfl⟩ := ((hB.1 γ hγ).1 g).1 hgX
    simp only [MonoidHom.coe_comp, Function.comp_apply, hφ γ hγ c, (hy γ c).2, MonoidHom.id_apply]
  exact ⟨φ, fun g => DFunLike.congr_fun hcomp g⟩

end Split

end CFSG.RankThree.GF2n.Stroth80
