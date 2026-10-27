module

public import CFSG.Quasithin.EmptyFaithful.S153E51A
public import CFSG.Quasithin.EmptyFaithful.S153E52A

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S153E

section Fifty2

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

omit [Finite G] in
theorem card_tildeOf_mul (X : Subgroup G) (hZX : quasithinOmegaOneCenter T ≤ X)
    (hXN : X ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G)) :
    Nat.card ↥(tildeOf (quasithinOmegaOneCenter T) X) * Nat.card ↥(quasithinOmegaOneCenter T) =
      Nat.card ↥X := by
  have h2 := relIndex_secImg (A := Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
    (B := quasithinOmegaOneCenter T) (T := quasithinOmegaOneCenter T) (H := X) le_rfl hZX hXN
  have h3 : secImg (Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
      (quasithinOmegaOneCenter T) (quasithinOmegaOneCenter T) = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨x, hx, rfl⟩ := mem_secImg.1 hy
    rw [Subgroup.mem_bot]
    exact secMk_eq_one_iff.2 hx
  rw [h3, Subgroup.relIndex_bot_left] at h2
  have h4 := Subgroup.relIndex_mul_card (quasithinOmegaOneCenter T) X
  rw [inf_eq_left.2 hZX] at h4
  have h5 : Nat.card ↥(tildeOf (quasithinOmegaOneCenter T) X) =
      (quasithinOmegaOneCenter T).relIndex X := h2
  rw [h5]
  exact h4

theorem card_U_eq_eight (cx : Ctx15350 T Mc M V₁ V₂ t)
    (h4 : Nat.card ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)) = 4) :
    Nat.card ↥(UH153 T M V₁ Mc) = 8 := by
  have hZU : quasithinOmegaOneCenter T ≤ UH153 T M V₁ Mc := (Z_le_ZS cx).trans (ZS_le_U cx)
  have hUN : UH153 T M V₁ Mc ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
    (U_le_T cx).trans ((T_le_Mc cx).trans (Mc_le_normalizer_Z cx))
  have := card_tildeOf_mul (UH153 T M V₁ Mc) hZU hUN
  rw [h4, cx.c.hyp.lemma_15_3_2_two.2] at this
  omega

theorem inf_centralizer_U_eq_ZS (cx : Ctx15350 T Mc M V₁ V₂ t) (h1 : ¬ VZ T M ≤ pCoreOf 2 Mc)
    (h8 : Nat.card ↥(UH153 T M V₁ Mc) = 8) :
    UH153 T M V₁ Mc ⊓ Subgroup.centralizer (VZ T M : Set G) = ZS153 T M V₁ := by
  have hZSle : ZS153 T M V₁ ≤ UH153 T M V₁ Mc ⊓ Subgroup.centralizer (VZ T M : Set G) := by
    refine le_inf (ZS_le_U cx) fun z hz => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact B2F.isElemAbelian_comm cx.c.hyp.elemAbelian hv (ZS_le_V cx hz)
  have hnotU : ¬ UH153 T M V₁ Mc ≤ Subgroup.centralizer (VZ T M : Set G) := by
    intro hle
    obtain ⟨n, hn, hn1⟩ := exists_ne_one_autI_U cx h1
    have hbot := autI_eq_bot_of_le_centralizer cx.c.hyp.elemAbelian hle
    rw [hbot, Subgroup.mem_bot] at hn
    exact hn1 hn
  have h4 : Nat.card ↥(ZS153 T M V₁) = 4 := Decomp153.card_ZS cx.c.hyp cx.c.decomp
  set C := UH153 T M V₁ Mc ⊓ Subgroup.centralizer (VZ T M : Set G) with hC
  have hd : Nat.card ↥C ∣ 8 := by
    rw [← h8]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hge : 4 ≤ Nat.card ↥C := by
    rw [← h4]
    exact Subgroup.card_le_of_le hZSle
  have hne : Nat.card ↥C ≠ 8 := by
    intro h8'
    apply hnotU
    have : C = UH153 T M V₁ Mc :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h8, h8'])
    rw [← this]
    exact inf_le_right
  have hC4 : Nat.card ↥C = 4 := by
    have hb := Nat.le_of_dvd (by norm_num) hd
    generalize Nat.card ↥C = c at hd hge hne hb ⊢
    interval_cases c <;> omega
  exact (Subgroup.eq_of_le_of_card_ge hZSle (by rw [h4, hC4])).symm

theorem commutator_pCoreY_U_le (cx : Ctx15350 T Mc M V₁ V₂ t)
    (hCU : UH153 T M V₁ Mc ⊓ Subgroup.centralizer (VZ T M : Set G) = ZS153 T M V₁) :
    ∀ x ∈ pCoreOf 2 (Y153 Mc M), ∀ u ∈ UH153 T M V₁ Mc, x * u * x⁻¹ * u⁻¹ ∈ VZ T M := by
  intro x hx u hu
  have hxY : x ∈ Y153 Mc M ⊓ Subgroup.centralizer (VZ T M : Set G) := by
    rw [← cx.r49.case_one.1]
    exact hx
  have hxC := hxY.2
  have hxMc : x ∈ Mc :=
    cx.c.hyp.qtfe.centralizer_le_mc (cx.c.hyp.centralizer_VZ_le hxC)
  have huN : u ∈ Subgroup.normalizer (VZ T M : Set G) := U_le_N cx hu
  have h1 : x * u * x⁻¹ ∈ UH153 T M V₁ Mc := U_conj_mem hxMc hu
  have h2 : u * x⁻¹ * u⁻¹ ∈ Subgroup.centralizer (VZ T M : Set G) :=
    (Subgroup.mem_normalizer_iff.mp (B2F.normalizer_le_normalizer_centralizer (VZ T M) huN) x⁻¹).mp
      ((Subgroup.centralizer (VZ T M : Set G)).inv_mem hxC)
  have hU : x * u * x⁻¹ * u⁻¹ ∈ UH153 T M V₁ Mc :=
    (UH153 T M V₁ Mc).mul_mem h1 ((UH153 T M V₁ Mc).inv_mem hu)
  have hC : x * u * x⁻¹ * u⁻¹ ∈ Subgroup.centralizer (VZ T M : Set G) := by
    have e : x * u * x⁻¹ * u⁻¹ = x * (u * x⁻¹ * u⁻¹) := by group
    rw [e]
    exact (Subgroup.centralizer (VZ T M : Set G)).mul_mem hxC h2
  have : x * u * x⁻¹ * u⁻¹ ∈ ZS153 T M V₁ := by
    rw [← hCU]
    exact ⟨hU, hC⟩
  exact ZS_le_V cx this

theorem commutator_pCoreY_Y_le (cx : Ctx15350 T Mc M V₁ V₂ t)
    (hY : Y153 Mc M = ⁅Y153 Mc M, UH153 T M V₁ Mc⁆)
    (h8 : ∀ x ∈ pCoreOf 2 (Y153 Mc M), ∀ u ∈ UH153 T M V₁ Mc, x * u * x⁻¹ * u⁻¹ ∈ VZ T M) :
    ∀ x ∈ pCoreOf 2 (Y153 Mc M), ∀ y ∈ Y153 Mc M, x * y * x⁻¹ * y⁻¹ ∈ VZ T M := by
  have hVN : Y153 Mc M ⊔ UH153 T M V₁ Mc ≤ Subgroup.normalizer (VZ T M : Set G) :=
    sup_le ((Y153_le Mc M).trans cx.c.hyp.le_normalizer) (U_le_N cx)
  have hAN : Y153 Mc M ⊔ UH153 T M V₁ Mc ≤
      Subgroup.normalizer (pCoreOf 2 (Y153 Mc M) : Set G) := by
    refine sup_le (le_normalizer_pCoreOf 2 (Y153 Mc M)) ?_
    exact ((U_le_T cx).trans (T_le_M cx)).trans
      ((le_normalizer_Y153 Mc M).trans (normalizer_le_normalizer_pCoreOf 2 (Y153 Mc M)))
  set C' : Subgroup G := centralizerMod (VZ T M) (Y153 Mc M ⊔ UH153 T M V₁ Mc)
    (pCoreOf 2 (Y153 Mc M)) with hC'
  have hUC : UH153 T M V₁ Mc ≤ C' := by
    intro u hu
    refine ⟨Subgroup.mem_sup_right hu, U_le_N cx hu, fun a ha => ?_⟩
    have := h8 a ha u hu
    have e : u * a * u⁻¹ * a⁻¹ = (a * u * a⁻¹ * u⁻¹)⁻¹ := by group
    rw [e]
    exact (VZ T M).inv_mem this
  have hconj : ∀ g ∈ Y153 Mc M ⊔ UH153 T M V₁ Mc, ∀ c ∈ C', g * c * g⁻¹ ∈ C' := by
    intro g hg c hc
    obtain ⟨hcS, hcN, hcA⟩ := hc
    refine ⟨(Y153 Mc M ⊔ UH153 T M V₁ Mc).mul_mem
      ((Y153 Mc M ⊔ UH153 T M V₁ Mc).mul_mem hg hcS)
      ((Y153 Mc M ⊔ UH153 T M V₁ Mc).inv_mem hg), ?_, fun a ha => ?_⟩
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hVN hg) hcN) (Subgroup.inv_mem _ (hVN hg))
    · have ha' : g⁻¹ * a * g ∈ pCoreOf 2 (Y153 Mc M) := by
        have := (Subgroup.mem_normalizer_iff.mp (hAN ((Y153 Mc M ⊔ UH153 T M V₁ Mc).inv_mem hg)) a).mp ha
        simpa using this
      have h1 := hcA _ ha'
      have h2 : g * (c * (g⁻¹ * a * g) * c⁻¹ * (g⁻¹ * a * g)⁻¹) * g⁻¹ ∈ VZ T M :=
        (Subgroup.mem_normalizer_iff.mp (hVN hg) _).mp h1
      have e : g * c * g⁻¹ * a * (g * c * g⁻¹)⁻¹ * a⁻¹ =
          g * (c * (g⁻¹ * a * g) * c⁻¹ * (g⁻¹ * a * g)⁻¹) * g⁻¹ := by group
      rw [e]
      exact h2
  have hYC : Y153 Mc M ≤ C' := by
    have hle : ⁅Y153 Mc M, UH153 T M V₁ Mc⁆ ≤ C' := by
      rw [Subgroup.commutator_le]
      intro y hy u hu
      have hyS : y ∈ Y153 Mc M ⊔ UH153 T M V₁ Mc := Subgroup.mem_sup_left hy
      have h1 : y * u * y⁻¹ ∈ C' := hconj y hyS u (hUC hu)
      have e : ⁅y, u⁆ = (y * u * y⁻¹) * u⁻¹ := by simp [commutatorElement_def, mul_assoc]
      rw [e]
      exact C'.mul_mem h1 (C'.inv_mem (hUC hu))
    exact hY.le.trans hle
  intro x hx y hy
  have h1 := (hYC hy).2.2 x hx
  have e : x * y * x⁻¹ * y⁻¹ = (y * x * y⁻¹ * x⁻¹)⁻¹ := by group
  rw [e]
  exact (VZ T M).inv_mem h1

end Fifty2

end S153E

end CFSG.Quasithin
