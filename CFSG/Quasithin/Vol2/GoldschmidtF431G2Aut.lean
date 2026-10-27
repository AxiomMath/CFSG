module

public import CFSG.Quasithin.Vol2.GoldschmidtF431G2ModelPar
public import CFSG.Quasithin.Vol2.GoldschmidtF431G2Root
public import CFSG.Quasithin.Vol2.GoldschmidtF431F45L3Ctx

public noncomputable section

namespace CFSG.Quasithin.H13.F431.G2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin
  CFSG.Quasithin.H13.Sec53F.G2 CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2
  CFSG.GH74.GLS.Stage4.Hex

section Generic

theorem autStab_sup {D : Type} [Group D] {A B : Subgroup D} {φ : MulAut D}
    (hA : φ ∈ autStab A) (hB : φ ∈ autStab B) : φ ∈ autStab (A ⊔ B) := by
  refine F431.F45.mem_autStab_of_map_eq ?_
  rw [Subgroup.map_sup, F431.F45.map_eq_of_mem_autStab hA, F431.F45.map_eq_of_mem_autStab hB]

theorem three_le_card_of_pow {K : Type} {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f) :
    3 ≤ Nat.card K := by
  rw [hK]
  calc 3 ≤ 2 ^ 2 := by norm_num
    _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf

end Generic

variable {K : Type} [Field K]

theorem fieldAut_xe (σ : K ≃+* K) (γ : Fin Tag.G2.rank → ℤ) (s : K) :
    fieldAut K σ (xe γ s) = xe γ (σ s) := by
  apply Subtype.ext
  rw [fieldAut_apply]
  exact Units.ext (entrywise_pinnedX σ.toRingHom γ s)

theorem fieldAut_xe_one (σ : K ≃+* K) (γ : Fin Tag.G2.rank → ℤ) :
    fieldAut K σ (xe γ 1) = xe γ 1 := by
  rw [fieldAut_xe, map_one]

theorem fieldAut_xa_one (σ : K ≃+* K) : fieldAut K σ (xa 1) = xa 1 := fieldAut_xe_one σ rA

theorem fieldAut_xr_one (σ : K ≃+* K) : fieldAut K σ (xr 1) = xr 1 := fieldAut_xe_one σ rR

theorem fieldAut_xu_one (σ : K ≃+* K) : fieldAut K σ (xu 1) = xu 1 := fieldAut_xe_one σ rU

theorem fieldAut_xv_one (σ : K ≃+* K) : fieldAut K σ (xv 1) = xv 1 := fieldAut_xe_one σ rV

theorem fieldAut_xb_one (σ : K ≃+* K) : fieldAut K σ (xb 1) = xb 1 := fieldAut_xe_one σ rB

theorem fieldAut_xc_one (σ : K ≃+* K) : fieldAut K σ (xc 1) = xc 1 := fieldAut_xe_one σ rC

theorem fieldAut_mem_autStab_of_forward (H : Subgroup (C K))
    (h : ∀ (σ : K ≃+* K), ∀ x ∈ H, fieldAut K σ x ∈ H) (σ : K ≃+* K) :
    fieldAut K σ ∈ autStab H := by
  intro x
  refine ⟨h σ x, fun hx => ?_⟩
  have := h σ⁻¹ _ hx
  rwa [map_inv, MulAut.inv_apply_self] at this

theorem fieldAut_mem_autStab_Xe (σ : K ≃+* K) (γ : Fin Tag.G2.rank → ℤ) :
    fieldAut K σ ∈ autStab (Xe K γ) := by
  refine fieldAut_mem_autStab_of_forward _ (fun σ x hx => ?_) σ
  obtain ⟨s, rfl⟩ := hx
  exact ⟨σ s, (fieldAut_xe σ γ s).symm⟩

theorem fieldAut_mem_autStab_Q1 (σ : K ≃+* K) : fieldAut K σ ∈ autStab (Q1 K) :=
  autStab_sup (autStab_sup (autStab_sup (autStab_sup (fieldAut_mem_autStab_Xe σ rA)
    (fieldAut_mem_autStab_Xe σ rU)) (fieldAut_mem_autStab_Xe σ rV))
    (fieldAut_mem_autStab_Xe σ rB)) (fieldAut_mem_autStab_Xe σ rC)

theorem fieldAut_mem_autStab_V (σ : K ≃+* K) : fieldAut K σ ∈ autStab (V K) :=
  autStab_sup (fieldAut_mem_autStab_Xe σ rB) (fieldAut_mem_autStab_Xe σ rC)

theorem fieldAut_mem_autStab_simpleNeg (σ : K ≃+* K) (i : Fin Tag.G2.rank) :
    fieldAut K σ ∈ autStab (simpleNegSubgroup Tag.G2 K i) := by
  refine fieldAut_mem_autStab_of_forward _ (fun σ x hx => ?_) σ
  obtain ⟨c, hc⟩ := mem_simpleNegSubgroup.1 hx
  refine mem_simpleNegSubgroup.2 ⟨σ c, ?_⟩
  rw [fieldAut_apply, hc]
  exact units_map_entrywiseHom_yUnit σ.toRingHom i c

section Stab

variable [Finite K] [CharP K 2]

theorem fieldAut_mem_autStab_U (σ : K ≃+* K) : fieldAut K σ ∈ autStab (U K) := by
  refine fieldAut_mem_autStab_of_forward _ (fun σ x hx => ?_) σ
  exact (g2_F_U (fieldAut K σ) ⟨σ, rfl⟩ x).2 hx

theorem fieldAut_mem_autStab_torusSub (σ : K ≃+* K) :
    fieldAut K σ ∈ autStab (torusSub Tag.G2 K) := by
  refine fieldAut_mem_autStab_of_forward _ (fun σ x hx => ?_) σ
  exact g2_F_H (fieldAut K σ) ⟨σ, rfl⟩ x hx

theorem fieldAut_mem_autStab_borelSub (σ : K ≃+* K) :
    fieldAut K σ ∈ autStab (borelSub Tag.G2 K) := by
  rw [← posUnipotentSub_sup_torusSub]
  exact autStab_sup (fieldAut_mem_autStab_U σ) (fieldAut_mem_autStab_torusSub σ)

theorem fieldAut_mem_autStab_Pmin (σ : K ≃+* K) (i : Fin Tag.G2.rank) :
    fieldAut K σ ∈ autStab (Pmin K i) := by
  have h : Pmin K i = borelSub Tag.G2 K ⊔ simpleNegSubgroup Tag.G2 K i :=
    CFSG.QuasithinUnique.Setup.X6.parabolicSubgroup_subgroupOf_eq i
  rw [h]
  exact autStab_sup (fieldAut_mem_autStab_borelSub σ) (fieldAut_mem_autStab_simpleNeg σ i)

end Stab

theorem exists_conj_fieldAut {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f)
    (φ : MulAut (C K)) : ∃ (g : C K) (σ : K ≃+* K), φ = MulAut.conj g * fieldAut K σ := by
  obtain ⟨hex, -⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.even_G2_exact_automorphism_normal_form hf K hK
  obtain ⟨⟨g, σ₀⟩, hgσ, -⟩ := hex φ
  refine ⟨g, σ₀, MulEquiv.ext fun h => Subtype.ext ?_⟩
  rw [hgσ h, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
    Subgroup.coe_inv, fieldAut_apply]

theorem xa_one_mem_Pmin (i : Fin Tag.G2.rank) : xa (1 : K) ∈ Pmin K i :=
  Subgroup.mem_subgroupOf.2 (borelGroup_le_parabolicSubgroup _
    (Subgroup.mem_sup_right (mem_U_iff.1 (xa_mem_U 1))))

section Normalizer

variable
  [Finite K]

theorem isCoatom_Pmin (hK : 3 ≤ Nat.card K) (i : Fin Tag.G2.rank) : IsCoatom (Pmin K i) := by
  have hi : i = idx true ∨ i = idx false := by revert i; decide
  have key : ∀ b : Bool, IsCoatom (Pmin K (idx b)) := fun b => by
    have h := BN.isCoatom_P (g2ModelSystem K hK) b
    rw [← map_Pmin hK b] at h
    exact (OrderIso.isCoatom_iff (MulEquiv.mapSubgroup (mk K)) _).1 h
  rcases hi with rfl | rfl <;> exact key _

theorem normalizer_Pmin (hK : 3 ≤ Nat.card K) (i : Fin Tag.G2.rank) :
    Subgroup.normalizer (Pmin K i : Set (C K)) = Pmin K i := by
  have hc := isCoatom_Pmin hK i
  have hs := isSimpleGroup_adjointGroup hK
  rcases hc.le_iff.1 (Subgroup.le_normalizer (H := Pmin K i)) with h | h
  · exfalso
    have hn : (Pmin K i).Normal := Subgroup.normalizer_eq_top_iff.1 h
    rcases hn.eq_bot_or_eq_top with h0 | h1
    · have := xa_one_mem_Pmin (K := K) i
      rw [h0, Subgroup.mem_bot, xa_eq_one_iff] at this
      exact one_ne_zero this
    · exact hc.1 h1
  · exact h

theorem mem_Pmin_of_conj_mul_mem_autStab [CharP K 2] (hK : 3 ≤ Nat.card K) {g : C K}
    {σ : K ≃+* K} {i : Fin Tag.G2.rank}
    (h : MulAut.conj g * fieldAut K σ ∈ autStab (Pmin K i)) : g ∈ Pmin K i := by
  have hc : MulAut.conj g ∈ autStab (Pmin K i) := by
    have := (autStab (Pmin K i)).mul_mem h ((autStab (Pmin K i)).inv_mem
      (fieldAut_mem_autStab_Pmin σ i))
    simpa using this
  have hg : g ∈ Subgroup.normalizer (Pmin K i : Set (C K)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have := hc y
    rwa [MulAut.conj_apply] at this
  rwa [normalizer_Pmin hK i] at hg

theorem exists_of_autStab_Pmin [CharP K 2] {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f)
    (i : Fin Tag.G2.rank) {φ : MulAut (C K)} (h : φ ∈ autStab (Pmin K i)) :
    ∃ g ∈ Pmin K i, ∃ σ : K ≃+* K, φ = MulAut.conj g * fieldAut K σ := by
  obtain ⟨g, σ, rfl⟩ := exists_conj_fieldAut hf hK φ
  exact ⟨g, mem_Pmin_of_conj_mul_mem_autStab (three_le_card_of_pow hf hK) h, σ, rfl⟩

theorem exists_of_autStab_Pr_Pa [CharP K 2] {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f)
    {φ : MulAut (C K)}
    (h : φ ∈ autStab (Pmin K ⟨1, by decide⟩) ⊓ autStab (Pmin K ⟨0, by decide⟩)) :
    ∃ b ∈ Pmin K ⟨1, by decide⟩ ⊓ Pmin K ⟨0, by decide⟩, ∃ σ : K ≃+* K,
      φ = MulAut.conj b * fieldAut K σ ∧ φ (xc 1) = b * xc 1 * b⁻¹ ∧
        φ (xv 1) = b * xv 1 * b⁻¹ := by
  obtain ⟨g, σ, rfl⟩ := exists_conj_fieldAut hf hK φ
  have h3 := three_le_card_of_pow hf hK
  refine ⟨g, ⟨mem_Pmin_of_conj_mul_mem_autStab h3 h.1, mem_Pmin_of_conj_mul_mem_autStab h3 h.2⟩,
    σ, rfl, ?_, ?_⟩
  · rw [MulAut.mul_apply, fieldAut_xc_one, MulAut.conj_apply]
  · rw [MulAut.mul_apply, fieldAut_xv_one, MulAut.conj_apply]

end Normalizer

end CFSG.Quasithin.H13.F431.G2
