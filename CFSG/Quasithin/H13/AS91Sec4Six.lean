module

public import CFSG.Quasithin.H13.AS91Sec4SixE

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.AS91

open Subgroup Module CFSG.Open CFSG.LargeExtraspecial CFSG.Quasithin CFSG.Quasithin.HatM22
open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA
open CFSG.GF2Type.Smith1979.GammaU.Viol CFSG.GF2Type.Smith1979.GammaU.Enum
open CFSG.GF2Type.Smith1979.IdxFour

variable {G : Type} [Group G] [Finite G]

theorem card_mul_self_le_of_comm (S : Setting G) {X : Subgroup G} (hX : X ≤ S.QG)
    (hz : S.z ∈ X) (hc : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) :
    Nat.card X * Nat.card X ≤ 2 ^ (2 * S.width + 2) := by
  have hle : X ≤ S.QG ⊓ centralizer (X : Set G) :=
    le_inf hX fun x hx => mem_centralizer_iff.mpr fun y hy => hc y hy x hx
  rw [← card_QG_inf_centralizer_mul S hX hz]
  exact Nat.mul_le_mul_right _ (Subgroup.card_le_of_le hle)

namespace Data41

variable {z : G} {h : HypJ4 G z} (D : Data41 h)

theorem QG_le_G13 : h.setting.QG ≤ D.G13 := QG_le_pre _

theorem mem_E_of_eq_one_or_z
    {x : G} (hx : x = 1 ∨ x = z) : x ∈ D.E := by
  rcases hx with rfl | rfl
  · exact one_mem _
  · exact D.E1_le_E D.z_mem_E1

section J

variable
  (hOut : KG82HatM22Out) (hTw : KG82HatM22Twelve)

include hOut hTw

theorem card_le_of_comm {A : Subgroup G} (hAT : A ≤ D.T)
    (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) :
    Nat.card A ≤ 2 ^ 11 ∧ (Nat.card A = 2 ^ 11 → D.E1 ≤ A) := by
  have hAM : A ≤ h.setting.M := hAT.trans (pre_le_M _)
  let f : ↥A →* (V12 ≃ₗ[ZMod 2] V12) := (D.Φo.comp h.setting.ρ).comp (Subgroup.inclusion hAM)
  have hfP : f.range ≤ Two.pGrp := by
    rintro _ ⟨x, rfl⟩
    exact rho_mem_of_mem_pre (hAT x.2) (hAM x.2)
  have hfc : ∀ x ∈ f.range, ∀ y ∈ f.range, x * y = y * x := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    rw [← map_mul, ← map_mul, show x * y = y * x from Subtype.ext (hA x x.2 y y.2)]
  have hker : f.ker = h.setting.QG.subgroupOf A := by
    ext x
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    constructor
    · intro h1
      have h2 : D.Φo (h.setting.ρ (Subgroup.inclusion hAM x)) = D.Φo 1 := by
        rw [map_one]
        exact h1
      exact (h.setting.ρ_eq_one_iff _).mp (D.Φo_injective h2)
    · intro hx
      show D.Φo (h.setting.ρ (Subgroup.inclusion hAM x)) = 1
      rw [(h.setting.ρ_eq_one_iff _).mpr hx, map_one]
  have hcardA : Nat.card A = Nat.card (A ⊓ h.setting.QG : Subgroup G) * Nat.card f.range := by
    have h1 := Subgroup.card_mul_index f.ker
    rw [Subgroup.index_ker, hker, card_subgroupOf_eq] at h1
    exact h1.symm
  have hYX : A ⊓ h.setting.QG ≤ h.setting.clPre (h.setting.clSub (A ⊓ h.setting.QG)) :=
    h.setting.le_clPre_clSub inf_le_right
  have hXc : ∀ x ∈ h.setting.clPre (h.setting.clSub (A ⊓ h.setting.QG)),
      ∀ y ∈ h.setting.clPre (h.setting.clSub (A ⊓ h.setting.QG)), x * y = y * x := by
    intro x hx y hy
    refine (h.setting.polar_cl_eq_zero_iff hx.1 hy.1).mp ?_
    obtain ⟨x', hx'Y, hx'Q, hx'⟩ := h.setting.mem_clSub_iff.mp hx.2
    obtain ⟨y', hy'Y, hy'Q, hy'⟩ := h.setting.mem_clSub_iff.mp hy.2
    rw [← hx', ← hy']
    exact (h.setting.polar_cl_eq_zero_iff hx'Q hy'Q).mpr (hA x' hx'Y.1 y' hy'Y.1)
  have hX128 : Nat.card (h.setting.clPre (h.setting.clSub (A ⊓ h.setting.QG))) ≤ 128 := by
    have h1 := card_mul_self_le_of_comm h.setting (h.setting.clPre_le_QG _)
      (h.setting.z_mem_clPre _) hXc
    rw [h.setting_width] at h1
    norm_num at h1
    nlinarith
  have hXW := h.setting.card_clPre (h.setting.clSub (A ⊓ h.setting.QG))
  have hsub : ⇑D.ψV '' (h.setting.clSub (A ⊓ h.setting.QG) : Set h.setting.Qt) ⊆
      Two.fixSet (f.range : Set (V12 ≃ₗ[ZMod 2] V12)) := by
    rintro _ ⟨v, hv, rfl⟩ U ⟨x, rfl⟩
    obtain ⟨y, hyY, hyQ, rfl⟩ := h.setting.mem_clSub_iff.mp hv
    show D.Φo (h.setting.ρ (Subgroup.inclusion hAM x)) (D.ψV (h.setting.cl y)) =
      D.ψV (h.setting.cl y)
    rw [Φo_apply_ψV, h.setting.ρ_cl _ hyQ]
    show D.ψV (h.setting.cl ((x : G) * y * (x : G)⁻¹)) = _
    rw [hA x x.2 y hyY.1, mul_inv_cancel_right]
  have hWfix : Nat.card (h.setting.clSub (A ⊓ h.setting.QG)) ≤
      (Two.fixSet (f.range : Set (V12 ≃ₗ[ZMod 2] V12))).ncard := by
    calc Nat.card (h.setting.clSub (A ⊓ h.setting.QG)) =
        (⇑D.ψV '' (h.setting.clSub (A ⊓ h.setting.QG) : Set h.setting.Qt)).ncard := by
          rw [Set.ncard_image_of_injective _ D.ψV.injective]
          exact Nat.card_coe_set_eq _
      _ ≤ _ := Set.ncard_le_ncard hsub
  have hYle := Subgroup.card_le_of_le hYX
  rcases Two.card_mul_le hfP hfc with h512 | ⟨hfix, h16⟩
  ·
    have hle : Nat.card A ≤ 1024 := by
      rw [hcardA]
      have hm : Nat.card (h.setting.clPre (h.setting.clSub (A ⊓ h.setting.QG))) ≤
          2 * min 64 (Two.fixSet (f.range : Set (V12 ≃ₗ[ZMod 2] V12))).ncard := by omega
      calc Nat.card (A ⊓ h.setting.QG : Subgroup G) * Nat.card f.range ≤
          (2 * min 64 (Two.fixSet (f.range : Set (V12 ≃ₗ[ZMod 2] V12))).ncard) *
            Nat.card f.range := Nat.mul_le_mul_right _ (hYle.trans hm)
        _ = 2 * (Nat.card f.range *
            min 64 (Two.fixSet (f.range : Set (V12 ≃ₗ[ZMod 2] V12))).ncard) := by ring
        _ ≤ 1024 := by omega
    refine ⟨hle.trans (by norm_num), fun h2 => ?_⟩
    rw [h2] at hle
    norm_num at hle
  ·
    have hle : Nat.card A ≤ 2 ^ 11 := by
      rw [hcardA]
      calc Nat.card (A ⊓ h.setting.QG : Subgroup G) * Nat.card f.range ≤ 128 * 16 :=
          Nat.mul_le_mul (hYle.trans hX128) h16
        _ = 2 ^ 11 := by norm_num
    refine ⟨hle, fun h2 => ?_⟩
    have h2' : Nat.card (A ⊓ h.setting.QG : Subgroup G) * Nat.card f.range = 2048 := by
      rw [← hcardA, h2]
      norm_num
    have hY128 : Nat.card (A ⊓ h.setting.QG : Subgroup G) = 128 := by
      have h128 := hYle.trans hX128
      by_contra hne
      have h127 : Nat.card (A ⊓ h.setting.QG : Subgroup G) ≤ 127 := by omega
      have := Nat.mul_le_mul h127 h16
      omega
    have hXE : h.setting.clPre (h.setting.clSub (A ⊓ h.setting.QG)) ≤ D.E1 := by
      refine h.setting.clPre_mono fun v hv => ?_
      rw [D.mem_W1q, ← hfix]
      exact hsub ⟨v, hv, rfl⟩
    have hXeq : h.setting.clPre (h.setting.clSub (A ⊓ h.setting.QG)) = D.E1 := by
      refine Subgroup.eq_of_le_of_card_ge hXE ?_
      rw [D.card_E1]
      norm_num
      omega
    have hYeq : A ⊓ h.setting.QG = h.setting.clPre (h.setting.clSub (A ⊓ h.setting.QG)) :=
      Subgroup.eq_of_le_of_card_ge hYX (by omega)
    rw [← hXeq, ← hYeq]
    exact inf_le_left

theorem thompson_eq (hHat : HatM22SmallModules) : Open.thompsonSubgroup D.T = D.E := by
  have hEc := (D.isElemAbelian_E hHat hOut hTw).1
  have comm_of : ∀ B : Subgroup G, IsMulCommutative B → ∀ x ∈ B, ∀ y ∈ B, x * y = y * x :=
    fun B hB x hx y hy => congrArg Subtype.val (hB.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  rw [thompsonSubgroup_eq_iSup]
  apply le_antisymm
  · refine iSup_le fun A => iSup_le fun hAT => iSup_le fun hAc => iSup_le fun hAm => ?_
    have h1 := hAm D.E (D.E_le_T hOut hTw) hEc
    obtain ⟨h2, h3⟩ := D.card_le_of_comm hOut hTw hAT (comm_of A hAc)
    rw [D.card_E hOut hTw] at h1
    have hE1 := h3 (le_antisymm h2 h1)
    intro a ha
    exact D.mem_E.mpr fun y hy => comm_of A hAc y (hE1 hy) a ha
  · refine le_iSup_of_le D.E (le_iSup_of_le (D.E_le_T hOut hTw) (le_iSup_of_le hEc
      (le_iSup_of_le (fun B hBT hBc => ?_) le_rfl)))
    rw [D.card_E hOut hTw]
    exact (D.card_le_of_comm hOut hTw hBT (comm_of B hBc)).1

theorem QE_eq : h.setting.QG ⊔ D.E = pre h.setting (Two.ebGrp.comap D.Φo) := by
  apply le_antisymm
  · exact sup_le (QG_le_pre _) fun e he =>
      mem_pre_of_rho ⟨e, D.E_le_M he⟩ (D.Φo_mem_eb hOut hTw he (D.E_le_M he))
  · intro x hx
    obtain ⟨hxM, hxρ⟩ := mem_pre.mp hx
    obtain ⟨s, hsE, hsx⟩ := D.exists_mem_E hOut hTw (U := D.Φo (h.setting.ρ ⟨x, hxM⟩)) hxρ
    have hρ : h.setting.ρ s = h.setting.ρ ⟨x, hxM⟩ := D.Φo_injective hsx
    have h1 : h.setting.ρ (s⁻¹ * ⟨x, hxM⟩) = 1 := by
      rw [map_mul, map_inv, hρ, inv_mul_cancel]
    have hq : (s : G)⁻¹ * x ∈ h.setting.QG := (h.setting.ρ_eq_one_iff _).mp h1
    have e : x = s * ((s : G)⁻¹ * x) := by group
    rw [e]
    exact mul_mem (mem_sup_right hsE) (mem_sup_left hq)

theorem card_QE : Nat.card (h.setting.QG ⊔ D.E : Subgroup G) = 2 ^ 17 := by
  have hle : Two.ebGrp ≤ Two.nGrp := Two.ebGrp_le_pGrp.trans Two.pGrp_le_nGrp
  rw [D.QE_eq hOut hTw, card_pre (K := Two.ebGrp.comap D.Φo) (D.comap_le_Mbar hOut hTw hle),
    D.card_comap hOut hTw hle, Two.card_ebGrp, D.card_QG]
  norm_num

theorem exists_mul_of_mem_QE {x : G} (hx : x ∈ h.setting.QG ⊔ D.E) :
    ∃ e ∈ D.E, ∃ q ∈ h.setting.QG, x = e * q := by
  rw [D.QE_eq hOut hTw] at hx
  obtain ⟨hxM, hxρ⟩ := mem_pre.mp hx
  obtain ⟨s, hsE, hsx⟩ := D.exists_mem_E hOut hTw (U := D.Φo (h.setting.ρ ⟨x, hxM⟩)) hxρ
  have hρ : h.setting.ρ s = h.setting.ρ ⟨x, hxM⟩ := D.Φo_injective hsx
  have h1 : h.setting.ρ (s⁻¹ * ⟨x, hxM⟩) = 1 := by
    rw [map_mul, map_inv, hρ, inv_mul_cancel]
  exact ⟨s, hsE, (s : G)⁻¹ * x, (h.setting.ρ_eq_one_iff _).mp h1, by group⟩

theorem QE_elem {x y : G} (hx : x ∈ h.setting.QG ⊔ D.E) (hy : y ∈ h.setting.QG ⊔ D.E) :
    x * y * x⁻¹ * y⁻¹ ∈ D.E ∧ x * x ∈ D.E := by
  obtain ⟨e₁, he₁, q, hq, rfl⟩ := D.exists_mul_of_mem_QE hOut hTw hx
  obtain ⟨e₂, he₂, q', hq', rfl⟩ := D.exists_mul_of_mem_QE hOut hTw hy
  have hqG := D.QG_le_G13 hq
  have hq'G := D.QG_le_G13 hq'
  constructor
  · have e : e₁ * q * (e₂ * q') * (e₁ * q)⁻¹ * (e₂ * q')⁻¹ =
        e₁ * (q * e₂ * q⁻¹) * ((q * q' * q⁻¹) * e₁⁻¹ * (q * q' * q⁻¹)⁻¹) *
          (q * q' * q⁻¹ * q'⁻¹) * e₂⁻¹ := by group
    rw [e]
    refine mul_mem (mul_mem (mul_mem (mul_mem he₁ (D.conj_mem_E hqG he₂)) ?_) ?_) (inv_mem he₂)
    · exact D.conj_mem_E (mul_mem (mul_mem hqG hq'G) (inv_mem hqG)) (inv_mem he₁)
    · exact D.mem_E_of_eq_one_or_z (h.setting.commutator_eq_one_or_z hq hq')
  · have e : e₁ * q * (e₁ * q) = e₁ * (q * e₁ * q⁻¹) * (q * q) := by group
    rw [e]
    refine mul_mem (mul_mem he₁ (D.conj_mem_E hqG he₁)) (D.mem_E_of_eq_one_or_z ?_)
    rw [← pow_two]
    exact h.setting.sq_eq_one_or_z hq

end J

@[expose] noncomputable def toLoc46
    (hHat : HatM22SmallModules) (hOut : KG82HatM22Out) (hTw : KG82HatM22Twelve) :
    Loc46 G z where
  toLoc44 := D.toLoc44 hHat hOut hTw
  G13 := D.G13
  G13_le := D.G13_le
  QX_le := D.QX_le hOut hTw
  card_G13 := D.card_G13 hOut hTw
  T := D.sylowT hOut hTw
  T_le := D.T_le_G13
  center_T := D.center_T
  fix_T := D.fix_T hOut hTw
  T_le_normalizer := D.T_le_normalizer hOut hTw (D.exists_g₁ hOut hTw).choose_spec
    (D.exists_s₀ hOut hTw).choose_spec
  E := D.E
  E_eq := (D.thompson_eq hOut hTw hHat).symm
  E_elem := D.isElemAbelian_E hHat hOut hTw
  card_E := D.card_E hOut hTw
  E_le := D.E_le_G13 hOut hTw
  E_normal := fun _ hg _ he => D.conj_mem_E hg he
  card_QE := by
    rw [← h.setting_QG]
    exact D.card_QE hOut hTw
  QE_elem := fun x hx y hy => by
    rw [← h.setting_QG] at hx hy
    exact D.QE_elem hOut hTw hx hy

end Data41

end CFSG.Quasithin.H13.AS91
