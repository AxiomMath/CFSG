module

public import CFSG.Quasithin.H13.L32NLem14331c

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

namespace L14331

@[expose] def c012 : Equiv.Perm (Fin 6) := Equiv.swap 0 1 * Equiv.swap 1 2

@[expose] def c345 : Equiv.Perm (Fin 6) := Equiv.swap 3 4 * Equiv.swap 4 5

theorem c012_c345 : c012 ^ 3 = 1 ∧ c012 ≠ 1 ∧ c345 ^ 3 = 1 ∧ c345 ≠ 1 ∧
    c012 * c345 = c345 * c012 ∧ c345 ≠ c012 ∧ c345 ≠ c012 ^ 2 ∧
    Equiv.Perm.sign c012 = 1 ∧ Equiv.Perm.sign c345 = 1 := by
  decide +kernel

theorem perm_six_center : ∀ σ : Equiv.Perm (Fin 6),
    σ * Equiv.swap 0 1 = Equiv.swap 0 1 * σ →
    σ * (Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 3 4 * Equiv.swap 4 5) =
      (Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 3 4 * Equiv.swap 4 5) * σ →
    σ = 1 := by
  decide +kernel

theorem sign_of_pow_three {σ : Equiv.Perm (Fin 6)} (h : σ ^ 3 = 1) : Equiv.Perm.sign σ = 1 := by
  have h1 : Equiv.Perm.sign σ ^ 3 = 1 := by rw [← map_pow, h, map_one]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h2 | h2
  · exact h2
  · rw [h2] at h1
    exact absurd h1 (by decide)

variable {W : Type} [Group W]

theorem orderOf_eq_three {x : W} (h3 : x ^ 3 = 1) (h1 : x ≠ 1) : orderOf x = 3 :=
  orderOf_eq_prime h3 h1

theorem sign_comm (σ τ : Equiv.Perm (Fin 6)) : Equiv.Perm.sign (σ * τ * σ⁻¹ * τ⁻¹) = 1 := by
  simp only [map_mul, map_inv]
  rw [mul_comm (Equiv.Perm.sign σ) (Equiv.Perm.sign τ), mul_inv_cancel_right, mul_inv_cancel]

theorem closureProp_of_perm {Γ : Subgroup W} {t : W} (ht : t ∈ Γ) (ht1 : t ≠ 1)
    (φ : ↥Γ ≃* Equiv.Perm (Fin 6)) : ClosureProp Γ t := by
  intro N hNΓ hΓN htN
  have hNn : (N.subgroupOf Γ).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hΓN
  set M' : Subgroup (Equiv.Perm (Fin 6)) := (N.subgroupOf Γ).map (φ : ↥Γ →* Equiv.Perm (Fin 6))
    with hM'
  have hM'n : M'.Normal := hNn.map _ φ.surjective
  have hσ1 : φ ⟨t, ht⟩ ≠ 1 := fun h => ht1 (by
    have := φ.injective (h.trans φ.map_one.symm)
    exact congrArg Subtype.val this)
  have hσM : φ ⟨t, ht⟩ ∈ M' := Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr htN)
  have hA : alternatingGroup (Fin 6) ≤ M' := by
    have hsimple : IsSimpleGroup ↥(alternatingGroup (Fin 6)) :=
      alternatingGroup.isSimpleGroup (by simp)
    have hn : (M'.subgroupOf (alternatingGroup (Fin 6))).Normal :=
      Subgroup.Normal.subgroupOf hM'n _
    rcases hn.eq_bot_or_eq_top with hb | htop
    ·
      exfalso
      have hcomm : ∀ τ : Equiv.Perm (Fin 6), φ ⟨t, ht⟩ * τ = τ * φ ⟨t, ht⟩ := by
        intro τ
        set σ := φ ⟨t, ht⟩
        have hc : σ * τ * σ⁻¹ * τ⁻¹ ∈ M' := by
          have h2 : σ * (τ * σ⁻¹ * τ⁻¹) ∈ M' :=
            M'.mul_mem hσM (hM'n.conj_mem _ (M'.inv_mem hσM) τ)
          simpa [mul_assoc] using h2
        have hmem : (⟨σ * τ * σ⁻¹ * τ⁻¹, (Equiv.Perm.mem_alternatingGroup).mpr (sign_comm σ τ)⟩ :
            ↥(alternatingGroup (Fin 6))) ∈ M'.subgroupOf (alternatingGroup (Fin 6)) := hc
        rw [hb, Subgroup.mem_bot] at hmem
        have h1 : σ * τ * σ⁻¹ * τ⁻¹ = 1 := congrArg Subtype.val hmem
        calc σ * τ = σ * τ * σ⁻¹ * τ⁻¹ * (τ * σ) := by group
          _ = τ * σ := by rw [h1, one_mul]
      exact hσ1 (perm_six_center _ (hcomm _) (hcomm _))
    · intro x hx
      have : (⟨x, hx⟩ : ↥(alternatingGroup (Fin 6))) ∈ M'.subgroupOf (alternatingGroup (Fin 6)) :=
        by rw [htop]; exact Subgroup.mem_top _
      exact this
  have hmemN : ∀ γ : ↥Γ, φ γ ∈ alternatingGroup (Fin 6) → (γ : W) ∈ N := by
    intro γ hγ
    obtain ⟨μ, hμM, hμ⟩ := Subgroup.mem_map.mp (hA hγ)
    have : μ = γ := φ.injective hμ
    rw [← this]
    exact Subgroup.mem_subgroupOf.mp hμM
  obtain ⟨c1, c11, c2, c21, c12, c21', c22, s1, s2⟩ := c012_c345
  refine ⟨fun γ hγ h3 => hmemN ⟨γ, hγ⟩ ((Equiv.Perm.mem_alternatingGroup).mpr
    (sign_of_pow_three (by rw [← map_pow, show (⟨γ, hγ⟩ : ↥Γ) ^ 3 = 1 from Subtype.ext h3,
      map_one]))), ?_⟩
  set y₁ := φ.symm c012
  set y₂ := φ.symm c345
  have hy₁ : φ y₁ = c012 := φ.apply_symm_apply _
  have hy₂ : φ y₂ = c345 := φ.apply_symm_apply _
  have ho₁ : orderOf (y₁ : W) = 3 := by
    rw [Subgroup.orderOf_coe, ← MulEquiv.orderOf_eq φ, hy₁]
    exact orderOf_eq_three c1 c11
  have ho₂ : orderOf (y₂ : W) = 3 := by
    rw [Subgroup.orderOf_coe, ← MulEquiv.orderOf_eq φ, hy₂]
    exact orderOf_eq_three c2 c21
  refine ⟨y₁, hmemN y₁ (by rw [hy₁]; exact (Equiv.Perm.mem_alternatingGroup).mpr s1),
    y₂, hmemN y₂ (by rw [hy₂]; exact (Equiv.Perm.mem_alternatingGroup).mpr s2), ho₁, ho₂, ?_, ?_⟩
  · have : y₁ * y₂ = y₂ * y₁ := φ.injective (by rw [map_mul, map_mul, hy₁, hy₂, c12])
    exact congrArg Subtype.val this
  · refine not_mem_zpowers_of_three ho₁ ?_ ?_ ?_
    · intro h
      apply c21
      rw [← hy₂, show y₂ = 1 from Subtype.ext h, map_one]
    · intro h
      apply c21'
      rw [← hy₂, ← hy₁, show y₂ = y₁ from Subtype.ext h]
    · intro h
      apply c22
      rw [← hy₂, ← hy₁, show y₂ = y₁ ^ 2 from Subtype.ext (by rw [h]; rfl), map_pow]

theorem closureProp_of_alt {Γ : Subgroup W} {t : W} (ht : t ∈ Γ) (ht1 : t ≠ 1)
    (φ : ↥Γ ≃* ↥(alternatingGroup (Fin 6))) : ClosureProp Γ t := by
  intro N hNΓ hΓN htN
  have hNn : (N.subgroupOf Γ).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hΓN
  have hsimple : IsSimpleGroup ↥(alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by simp)
  set M' := (N.subgroupOf Γ).map (φ : ↥Γ →* ↥(alternatingGroup (Fin 6))) with hM'
  have hM'n : M'.Normal := hNn.map _ φ.surjective
  have hσ1 : φ ⟨t, ht⟩ ≠ 1 := fun h => ht1 (by
    have := φ.injective (h.trans φ.map_one.symm)
    exact congrArg Subtype.val this)
  have hσM : φ ⟨t, ht⟩ ∈ M' := Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr htN)
  have htop : M' = ⊤ := by
    rcases hM'n.eq_bot_or_eq_top with hb | htop
    · rw [hb, Subgroup.mem_bot] at hσM
      exact absurd hσM hσ1
    · exact htop
  have hmemN : ∀ γ : ↥Γ, (γ : W) ∈ N := by
    intro γ
    obtain ⟨μ, hμM, hμ⟩ := Subgroup.mem_map.mp (htop ▸ Subgroup.mem_top (φ γ) : φ γ ∈ M')
    have : μ = γ := φ.injective hμ
    rw [← this]
    exact Subgroup.mem_subgroupOf.mp hμM
  obtain ⟨c1, c11, c2, c21, c12, c21', c22, s1, s2⟩ := c012_c345
  set a₁ : ↥(alternatingGroup (Fin 6)) := ⟨c012, (Equiv.Perm.mem_alternatingGroup).mpr s1⟩
  set a₂ : ↥(alternatingGroup (Fin 6)) := ⟨c345, (Equiv.Perm.mem_alternatingGroup).mpr s2⟩
  refine ⟨fun γ hγ _ => hmemN ⟨γ, hγ⟩, ?_⟩
  set y₁ := φ.symm a₁
  set y₂ := φ.symm a₂
  have hy₁ : φ y₁ = a₁ := φ.apply_symm_apply _
  have hy₂ : φ y₂ = a₂ := φ.apply_symm_apply _
  have ho₁ : orderOf (y₁ : W) = 3 := by
    rw [Subgroup.orderOf_coe, ← MulEquiv.orderOf_eq φ, hy₁, Subgroup.orderOf_mk]
    exact orderOf_eq_three c1 c11
  have ho₂ : orderOf (y₂ : W) = 3 := by
    rw [Subgroup.orderOf_coe, ← MulEquiv.orderOf_eq φ, hy₂, Subgroup.orderOf_mk]
    exact orderOf_eq_three c2 c21
  have hval : ∀ {x y : ↥Γ}, φ x = φ y → (x : W) = y := fun h => congrArg Subtype.val
    (φ.injective h)
  refine ⟨y₁, hmemN y₁, y₂, hmemN y₂, ho₁, ho₂, ?_, ?_⟩
  · have : φ (y₁ * y₂) = φ (y₂ * y₁) := by
      rw [map_mul, map_mul, hy₁, hy₂]
      exact Subtype.ext c12
    exact hval this
  · refine not_mem_zpowers_of_three ho₁ ?_ ?_ ?_
    · intro h
      apply c21
      have : φ y₂ = φ 1 := by rw [show y₂ = 1 from Subtype.ext h]
      rw [hy₂, map_one] at this
      exact congrArg Subtype.val this
    · intro h
      apply c21'
      have : φ y₂ = φ y₁ := by rw [show y₂ = y₁ from Subtype.ext h]
      rw [hy₂, hy₁] at this
      exact congrArg Subtype.val this
    · intro h
      apply c22
      have : φ y₂ = φ (y₁ ^ 2) := by rw [show y₂ = y₁ ^ 2 from Subtype.ext (by rw [h]; rfl)]
      rw [hy₂, map_pow, hy₁] at this
      exact congrArg Subtype.val this

end L14331

namespace L14328

open L14331

variable {G : Type} [Group G] [Finite G] {T L V V₂ : Subgroup G} [IsMulCommutative ↥V]

namespace Ctx

variable {g z b l : G} (C : Ctx G T L V V₂ g z b l) (D : HatModelU (fsuU T V))
include C

theorem rho_a_mem (h14325 : Lemma14325One) (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13)
    (h12810 : Lemma12_8_10) (h12813 : Lemma12_8_13) {e : G}
    (he : e ∈ centerOf (i128 T L V (fsuV1 T V))) (he1 : e ≠ 1)
    (hN : l⁻¹ * e * l ∈ Subgroup.normalizer (fsuU T V : Set G)) :
    D.ρ ⟨l⁻¹ * e * l, hN⟩ ∈ D.img (l32nH T V) ∧ D.ρ ⟨l⁻¹ * e * l, hN⟩ ≠ 1 := by
  have ha := C.conj_mem_zIl he
  have haH : l⁻¹ * e * l ∈ l32nH T V := L14332.conj_zU_le h12813 C.setting C.gP C.gN ha.1
  have ha1 : l⁻¹ * e * l ≠ 1 := fun h => he1 (by
    calc e = l * (l⁻¹ * e * l) * l⁻¹ := by group
      _ = 1 := by rw [h]; group)
  obtain ⟨hN', hρ1, -⟩ := C.rho_eq_of_ne D h14325 h1222 h12213 h12810 h12813 ha ha1
  exact ⟨L128A.HatU.rho_mem_img D haH hN, hρ1⟩

theorem false_of_case_iii (h14325 : Lemma14325One) (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13)
    (h12810 : Lemma12_8_10) (h12813 : Lemma12_8_13)
    (hQ : centralizerMod (fsuV1 T V) (l32nH T V) (fsuU T V) = pCoreOf 2 (l32nH T V))
    (hm3 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥(l32nH T V)) ≤ 2) {e : G}
    (he : e ∈ centerOf (i128 T L V (fsuV1 T V))) (he1 : e ≠ 1)
    (hiii : Case14323iii T V g D) : False := by
  refine C.false_of_closure D h14325 h1222 h12813 hQ hm3 he he1 fun hN => ?_
  obtain ⟨hmem, hρ1⟩ := C.rho_a_mem D h14325 h1222 h12213 h12810 h12813 he he1 hN
  rcases hiii.iso with h | h
  · obtain ⟨φ⟩ := h
    exact closureProp_of_alt hmem hρ1 φ
  · obtain ⟨φ⟩ := h
    exact closureProp_of_perm hmem hρ1 φ

end Ctx

end L14328

end CFSG.Quasithin.H13
