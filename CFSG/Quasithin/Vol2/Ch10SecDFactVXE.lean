module

public import CFSG.Quasithin.Vol2.Ch10SecDFactX
public import CFSG.Quasithin.Vol2.Ch10SecDFacts211b

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

omit [Finite G] in
theorem exists_comm_of_mem_V1 (h3 : Case10_1_1Three T L I) (hc : fsuCVM T L I = ⊥) {x : G}
    (hxN : x ∈ Subgroup.normalizer (fsuUL T L I : Set G)) {v : G} (hv : v ∈ fsuUL T L I)
    (hv1 : v ≠ 1) (hxv : x * v = v * x) (hx3 : x ^ 3 = 1)
    (hxC : x ∉ Subgroup.centralizer (fsuUL T L I : Set G)) {a : G} (ha : a ∈ fsuUL T L I) :
    ∃ b ∈ fsuUL T L I, a = x * b * x⁻¹ * b⁻¹ ∨ a = x * b * x⁻¹ * b⁻¹ * v := by
  obtain ⟨_, ⟨D⟩⟩ := nonempty_l3Data h3 hc
  have hβinj : Function.Injective D.β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have := (D.ker_β u).mp hu
    rw [Subgroup.mem_bot] at this
    exact Subtype.ext this
  set σ := conjAct (fsuUL T L I) ⟨x, hxN⟩ with hσdef
  obtain ⟨γ, hγ⟩ := D.exists_rho (g := σ) (by rw [autOn_L_V1_eq_top h3 hc]; trivial)
  set β' : ↥(fsuUL T L I) → CFSG.Quasithin.L3.Vec :=
    fun w => Multiplicative.toAdd (D.β ⟨w, trivial⟩) with hβ'def
  have hβmul : ∀ w₁ w₂ : ↥(fsuUL T L I), β' (w₁ * w₂) = β' w₁ + β' w₂ := by
    intro w₁ w₂
    have e : (⟨w₁ * w₂, trivial⟩ : ↥(⊤ : Subgroup ↥(fsuUL T L I))) =
        ⟨w₁, trivial⟩ * ⟨w₂, trivial⟩ := rfl
    simp only [hβ'def]
    rw [e, map_mul, toAdd_mul]
  have hβinv : ∀ w : ↥(fsuUL T L I), β' w⁻¹ = - β' w := by
    intro w
    have e : (⟨w⁻¹, trivial⟩ : ↥(⊤ : Subgroup ↥(fsuUL T L I))) = (⟨w, trivial⟩)⁻¹ := rfl
    simp only [hβ'def]
    rw [e, map_inv, toAdd_inv]
  have hβeq : ∀ w₁ w₂ : ↥(fsuUL T L I), β' w₁ = β' w₂ → (w₁ : G) = w₂ := by
    intro w₁ w₂ h
    have := hβinj (Multiplicative.toAdd.injective h)
    exact congrArg (fun w : ↥(⊤ : Subgroup ↥(fsuUL T L I)) => ((w : ↥(fsuUL T L I)) : G)) this
  have hβρ : ∀ w : ↥(fsuUL T L I), β' (σ w) = CFSG.Quasithin.L3.act γ (β' w) := by
    intro w
    have h1 := D.β_rho γ w trivial trivial
    rw [hγ] at h1
    exact congrArg Multiplicative.toAdd h1
  have hσv : σ ⟨v, hv⟩ = ⟨v, hv⟩ := by
    apply Subtype.ext
    rw [hσdef, conjAct_apply_coe]
    change x * v * x⁻¹ = v
    rw [hxv, mul_inv_cancel_right]
  have hfix : CFSG.Quasithin.L3.act γ (β' ⟨v, hv⟩) = β' ⟨v, hv⟩ := by
    rw [← hβρ, hσv]
  have hc0 : β' ⟨v, hv⟩ ≠ 0 := by
    intro h0
    apply hv1
    have h1 : β' ⟨v, hv⟩ = β' 1 := by
      rw [h0]
      simp only [hβ'def]
      have e : (⟨1, trivial⟩ : ↥(⊤ : Subgroup ↥(fsuUL T L I))) = 1 := rfl
      rw [e, map_one, toAdd_one]
    exact hβeq _ _ h1
  have hγ3 : γ ^ 3 = 1 := by
    apply D.rho_injective
    rw [map_pow, hγ, map_one, hσdef, ← map_pow]
    refine (conjAct_eq_one_iff _).mpr ?_
    have e : ((⟨x, hxN⟩ ^ 3 : Subgroup.normalizer (fsuUL T L I : Set G)) : G) = 1 := by
      rw [Subgroup.coe_pow]
      exact hx3
    rw [e]
    exact Subgroup.one_mem _
  have hγ1 : γ ≠ 1 := by
    intro h1
    apply hxC
    have : σ = 1 := by rw [← hγ, h1, map_one]
    exact (conjAct_eq_one_iff ⟨x, hxN⟩).mp this
  obtain ⟨u, hu⟩ := L3.eq_fix_add_comm γ _ hc0 hfix hγ3 hγ1 (β' ⟨a, ha⟩)
  obtain ⟨⟨b, hbtop⟩, hb'⟩ := D.β_surj (Multiplicative.ofAdd u)
  have hbu : β' b = u := congrArg Multiplicative.toAdd hb'
  have hcoe : ((σ b * b⁻¹ : ↥(fsuUL T L I)) : G) = x * (b : G) * x⁻¹ * (b : G)⁻¹ := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hσdef, conjAct_apply_coe]
  refine ⟨b, b.2, ?_⟩
  rcases hu with hu | hu
  · left
    have key : a = ((σ b * b⁻¹ : ↥(fsuUL T L I)) : G) := hβeq ⟨a, ha⟩ _ (by
      rw [hβmul, hβinv, hβρ, hbu, hu, sub_eq_add_neg]
      rfl)
    rw [key, hcoe]
  · right
    have key : a = ((σ b * b⁻¹ * ⟨v, hv⟩ : ↥(fsuUL T L I)) : G) := hβeq ⟨a, ha⟩ _ (by
      rw [hβmul, hβmul, hβinv, hβρ, hbu, hu, sub_eq_add_neg]
      rfl)
    rw [key, Subgroup.coe_mul, hcoe]

theorem factVXE_of
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) :
    FactVXE := by
  intro G _ _ T L I h h3 hc t v₁ v₂ hd
  have hd' := hd
  obtain ⟨ht, htn, hv1, hv11, hv2, hv21⟩ := hd'
  obtain ⟨x, hxL, hxX, hxo, hxC⟩ := exists_odd_mem_Xz h37 h38 h h3 hc hd
  have hxz : x ∈ fsuL0 T L ⊓ Subgroup.centralizer ({v₁ * v₂} : Set G) := (oTwoUpper_le _) hxX
  have hx3 := pow_three_eq_one_of_mem h37 h38 h h3 hc hd hxz hxo
  have hxE := fsuL0_inf_centralizer_z_le h37 h38 h hc hd hxz
  have hxv1 : x * v₁ = v₁ * x := ((Subgroup.mem_centralizer_iff.mp hxE) v₁
    (Subgroup.subset_closure (Set.mem_insert _ _))).symm
  have hxN : x ∈ Subgroup.normalizer (fsuUL T L I : Set G) := L_le_normalizer_V1 hxL
  have hXV : Xz T L (v₁ * v₂) ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    ((oTwoUpper_le _).trans inf_le_left).trans (SecA.fsuL0_le_normalizer_fsuVM T L I)
  have hTX : T ≤ Subgroup.normalizer (Xz T L (v₁ * v₂) : Set G) :=
    T_le_normalizer_Xz (T_le_centralizer_z h37 h38 h h3 hc hd)
  have hE1 : v₁ ∈ Subgroup.closure {v₁, v₂} := Subgroup.subset_closure (Set.mem_insert _ _)
  have hE2 : v₂ ∈ Subgroup.closure {v₁, v₂} :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hle2 : ⁅fsuVM T L I, CFSG.conjugate L t⁆ ≤ fsuVM T L I :=
    commutator_le_left_of_le_normalizer
      ((SecA.conjugate_le_fsuL0 ht).trans (SecA.fsuL0_le_normalizer_fsuVM T L I))
  have hcommX : ∀ y ∈ Xz T L (v₁ * v₂), ∀ b ∈ fsuVM T L I,
      y * b * y⁻¹ * b⁻¹ ∈ ⁅fsuVM T L I, Xz T L (v₁ * v₂)⁆ := by
    intro y hy b hb
    have := Subgroup.commutator_mem_commutator hy hb
    rw [commutatorElement_def, Subgroup.commutator_comm] at this
    exact this
  have hV1 : fsuUL T L I ≤ ⁅fsuVM T L I, Xz T L (v₁ * v₂)⁆ ⊔ Subgroup.closure {v₁, v₂} := by
    intro a ha
    obtain ⟨b, hb, hab | hab⟩ := exists_comm_of_mem_V1 h3 hc hxN hv1.1 hv11 hxv1 hx3 hxC ha
    · rw [hab]
      exact Subgroup.mem_sup_left (hcommX x hxX b (V1_le_V hb))
    · rw [hab]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (hcommX x hxX b (V1_le_V hb)))
        (Subgroup.mem_sup_right hE1)
  have hV2 : ⁅fsuVM T L I, CFSG.conjugate L t⁆ ≤
      ⁅fsuVM T L I, Xz T L (v₁ * v₂)⁆ ⊔ Subgroup.closure {v₁, v₂} := by
    intro a ha
    have hat : t * a * t⁻¹ ∈ fsuUL T L I := by
      rw [V2_eq_conjugate ht, SecA.mem_conjugate_iff] at ha
      exact ha
    have hyX : t⁻¹ * x * t ∈ Xz T L (v₁ * v₂) := by
      have := (Subgroup.mem_normalizer_iff.mp (hTX (T.inv_mem ht)) x).mp hxX
      simpa using this
    have hv12 : t⁻¹ * v₁ * t = v₂ := by
      rw [← conj_v2 h37 h38 h h3 hc hd]
      group
    obtain ⟨b, hb, hab | hab⟩ := exists_comm_of_mem_V1 h3 hc hxN hv1.1 hv11 hxv1 hx3 hxC hat
    all_goals
      have hbt : t⁻¹ * b * t ∈ fsuVM T L I := by
        have := (Subgroup.mem_normalizer_iff.mp (SecA.le_normalizer_fsuVM T L I (T.inv_mem ht))
          b).mp (V1_le_V hb)
        simpa using this
      have hc' := hcommX _ hyX _ hbt
    · have e : a = (t⁻¹ * x * t) * (t⁻¹ * b * t) * (t⁻¹ * x * t)⁻¹ * (t⁻¹ * b * t)⁻¹ := by
        calc a = t⁻¹ * (t * a * t⁻¹) * t := by group
          _ = t⁻¹ * (x * b * x⁻¹ * b⁻¹) * t := by rw [hab]
          _ = _ := by group
      rw [e]
      exact Subgroup.mem_sup_left hc'
    · have e : a = (t⁻¹ * x * t) * (t⁻¹ * b * t) * (t⁻¹ * x * t)⁻¹ * (t⁻¹ * b * t)⁻¹ *
          (t⁻¹ * v₁ * t) := by
        calc a = t⁻¹ * (t * a * t⁻¹) * t := by group
          _ = t⁻¹ * (x * b * x⁻¹ * b⁻¹ * v₁) * t := by rw [hab]
          _ = _ := by group
      rw [e, hv12]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hc') (Subgroup.mem_sup_right hE2)
  refine le_antisymm ((SecA.fsuVM_eq_sup h37 h38 h ht htn).le.trans (sup_le hV1 hV2))
    (sup_le (commutator_le_left_of_le_normalizer hXV) ?_)
  rw [Subgroup.closure_le]
  rintro w (rfl | rfl)
  · exact V1_le_V hv1.1
  · exact hle2 hv2.1

end CFSG.Quasithin.Vol2.Ch10.SecD
