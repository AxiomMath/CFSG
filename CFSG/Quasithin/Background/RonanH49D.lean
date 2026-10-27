module

public import CFSG.Quasithin.Background.RonanH49Base
public import CFSG.LieType.SteinbergBRAutGL32
public import CFSG.Quasithin.Background.HL3WrOff

public section

namespace CFSG.Quasithin.RonanH49

open CFSG.Quasithin CFSG.Quasithin.H.L3Wr
open scoped Matrix

open CFSG.LieType.SteinbergBR.AutGL32 in
@[expose] noncomputable def iotaSL : ↥SL32 →* ↥SL32 where
  toFun a := ⟨tau (a : GL (Fin 3) (ZMod 2)), mem_SL32 _⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul _ _ _)

theorem mat_iotaSL (a : ↥SL32) : mat (iotaSL a) = (mat a⁻¹)ᵀ := by
  change ((CFSG.LieType.SteinbergBR.AutGL32.tau (a : GL (Fin 3) (ZMod 2)) :
    GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) = _
  rw [CFSG.LieType.SteinbergBR.AutGL32.tau_val]
  rfl

@[expose] noncomputable def rhoT : ↥SL32 →* MulAut WMod :=
  rho.comp ((MonoidHom.id _).prod iotaSL)

theorem rhoT_apply (a : ↥SL32) : rhoT a = rho (a, iotaSL a) := rfl

theorem toAdd_rhoT (a : ↥SL32) (X : WMod) :
    Multiplicative.toAdd (rhoT a X) = mat a * Multiplicative.toAdd X * mat a⁻¹ := by
  rw [rhoT_apply, toAdd_rho]
  simp only [mat_iotaSL, Matrix.transpose_transpose]

theorem rhoT_injective : Function.Injective rhoT := by
  intro a b h
  have := rho_injective h
  exact (Prod.mk.inj this).1

theorem toAdd_dWd : Multiplicative.toAdd dWd = 1 := by
  decide

theorem toAdd_tau_dWd : Multiplicative.toAdd (tau dWd) = 1 := by
  rw [toAdd_tau, toAdd_dWd, Matrix.transpose_one]

theorem rhoT_mem_Cd (a : ↥SL32) : rhoT a ∈ Cd := by
  rw [mem_Cd]
  refine ⟨img_le_norm (rho_mem_img _), ?_⟩
  apply Multiplicative.toAdd.injective
  rw [toAdd_rhoT, toAdd_dWd, Matrix.mul_one, ← mat_mul, mul_inv_cancel, mat_one]

theorem tau_mem_Cd : tau ∈ Cd := by
  rw [mem_Cd]
  refine ⟨tau_mem_norm, ?_⟩
  apply Multiplicative.toAdd.injective
  rw [toAdd_tau_dWd, toAdd_dWd]

theorem mem_range_rhoT_of_mem_Cd {x : MulAut WMod} (hx : x ∈ Cd) (hxi : x ∈ img) :
    x ∈ rhoT.range := by
  obtain ⟨⟨a, b⟩, rfl⟩ := hxi
  have h := (mem_Cd.1 hx).2
  have h' : mat a * 1 * (mat b)ᵀ = 1 := by
    have := congrArg Multiplicative.toAdd h
    rw [toAdd_rho, toAdd_dWd] at this
    exact this
  refine ⟨a, ?_⟩
  have hb : (mat b)ᵀ = mat a⁻¹ := by
    calc (mat b)ᵀ = mat a⁻¹ * (mat a * 1 * (mat b)ᵀ) := by
          rw [Matrix.mul_one, ← Matrix.mul_assoc, mat_inv_mul, Matrix.one_mul]
      _ = mat a⁻¹ := by rw [h', Matrix.mul_one]
  have hb' : b = iotaSL a := by
    apply eq_of_mat_eq
    rw [mat_iotaSL, ← hb, Matrix.transpose_transpose]
  rw [rhoT_apply, hb']

theorem Cd_inf_img_eq : Cd ⊓ img = rhoT.range := by
  apply le_antisymm
  · intro x hx
    exact mem_range_rhoT_of_mem_Cd hx.1 hx.2
  · rintro _ ⟨a, rfl⟩
    exact ⟨rhoT_mem_Cd a, rho_mem_img _⟩

theorem Cd_le_norm : Cd ≤ norm := fun _ hx => (mem_Cd.1 hx).1

theorem card_Cd : Nat.card ↥Cd = 336 := by
  have h := card_inf_img_mul_two Cd_le_norm (fun h => tau_not_mem_img (h tau_mem_Cd))
  rw [Cd_inf_img_eq, ← Nat.card_congr (MonoidHom.ofInjective rhoT_injective).toEquiv, card_SL32] at h
  omega

theorem rhoT_range_le_Cd : rhoT.range ≤ Cd := by
  rintro _ ⟨a, rfl⟩
  exact rhoT_mem_Cd a

noncomputable abbrev Kc : Subgroup ↥Cd := rhoT.range.subgroupOf Cd

theorem Kc_normal : (Kc).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have hn' : (n : MulAut WMod) ∈ rhoT.range := Subgroup.mem_subgroupOf.1 hn
  have hni : (n : MulAut WMod) ∈ img := by
    obtain ⟨a, ha⟩ := hn'
    rw [← ha]
    exact rho_mem_img _
  rw [Subgroup.mem_subgroupOf]
  have hg : (g : MulAut WMod) ∈ norm := Cd_le_norm g.2
  have hgi : (g : MulAut WMod) * (n : MulAut WMod) * (g : MulAut WMod)⁻¹ ∈ img :=
    ((Subgroup.mem_normalizer_iff.1 hg) _).1 hni
  exact mem_range_rhoT_of_mem_Cd (Cd.mul_mem (Cd.mul_mem g.2 n.2) (Cd.inv_mem g.2)) hgi

noncomputable def eK : ↥Kc ≃* ↥SL32 :=
  (Subgroup.subgroupOfEquivOfLe rhoT_range_le_Cd).trans (MonoidHom.ofInjective rhoT_injective).symm

theorem rhoT_eK (k : ↥Kc) : rhoT (eK k) = ((k : ↥Cd) : MulAut WMod) := by
  have h := MonoidHom.apply_ofInjective_symm rhoT_injective
    (Subgroup.subgroupOfEquivOfLe rhoT_range_le_Cd k)
  exact h

noncomputable def PhiC : ↥Cd →* MulAut ↥SL32 :=
  haveI : (Kc).Normal := Kc_normal
  (MulAut.congr eK).toMonoidHom.comp MulAut.conjNormal

theorem rhoT_PhiC (x : ↥Cd) (a : ↥SL32) :
    rhoT (PhiC x a) = (x : MulAut WMod) * rhoT a * (x : MulAut WMod)⁻¹ := by
  haveI : (Kc).Normal := Kc_normal
  have hk : eK.symm a = ⟨⟨rhoT a, rhoT_mem_Cd a⟩, Subgroup.mem_subgroupOf.2 ⟨a, rfl⟩⟩ := by
    apply eK.injective
    rw [MulEquiv.apply_symm_apply]
    apply rhoT_injective
    rw [rhoT_eK]
  have e1 : PhiC x a = eK (MulAut.conjNormal x (eK.symm a)) := rfl
  rw [e1, rhoT_eK, MulAut.conjNormal_apply, hk]
  rfl

theorem tau_mul_rhoT_mul_inv (a : ↥SL32) : tau * rhoT a * tau⁻¹ = rho (iotaSL a, a) := by
  rw [rhoT_apply, tau_conj_rho]
  rfl

theorem PhiC_injective : Function.Injective PhiC := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hconj : ∀ a : ↥SL32, (x : MulAut WMod) * rhoT a * (x : MulAut WMod)⁻¹ = rhoT a := by
    intro a
    rw [← rhoT_PhiC, hx]
    rfl
  by_cases hxi : (x : MulAut WMod) ∈ img
  ·
    obtain ⟨a₀, ha₀⟩ := mem_range_rhoT_of_mem_Cd x.2 hxi
    have hc : ∀ c : GL (Fin 3) (ZMod 2), (a₀ : GL (Fin 3) (ZMod 2)) * c * (a₀ : GL (Fin 3) (ZMod 2))⁻¹ = c := by
      intro c
      have h1 := hconj ⟨c, mem_SL32 c⟩
      rw [← ha₀, ← map_inv, ← map_mul, ← map_mul] at h1
      have h2 := congrArg Subtype.val (rhoT_injective h1)
      exact h2
    have h1 : a₀ = 1 := by
      have : MulAut.conj (a₀ : GL (Fin 3) (ZMod 2)) = 1 := by
        refine MulEquiv.ext fun c => ?_
        rw [MulAut.conj_apply, hc c]
        rfl
      have h2 := CFSG.LieType.SteinbergBR.AutGL32.conj_injective (this.trans (map_one _).symm)
      exact Subtype.ext h2
    apply Subtype.ext
    rw [← ha₀, h1, map_one]
    rfl
  · exfalso
    obtain ⟨g, hg | hg⟩ := mem_norm_iff.1 (Cd_le_norm x.2)
    · exact hxi (hg ▸ rho_mem_img g)
    · have hc : ∀ c : GL (Fin 3) (ZMod 2),
          (g.1 : GL (Fin 3) (ZMod 2)) * CFSG.LieType.SteinbergBR.AutGL32.tau c *
            (g.1 : GL (Fin 3) (ZMod 2))⁻¹ = c := by
        intro c
        have h1 := hconj ⟨c, mem_SL32 c⟩
        rw [hg] at h1
        have e : rho g * tau * rhoT ⟨c, mem_SL32 c⟩ * (rho g * tau)⁻¹ =
            rho g * (tau * rhoT ⟨c, mem_SL32 c⟩ * tau⁻¹) * (rho g)⁻¹ := by group
        rw [e, tau_mul_rhoT_mul_inv] at h1
        have e2 : rho g = rho (g.1, g.2) := rfl
        rw [e2, ← map_inv, ← map_mul, ← map_mul] at h1
        have h2 := congrArg Subtype.val (congrArg Prod.fst (rho_injective h1))
        exact h2
      apply CFSG.LieType.SteinbergBR.AutGL32.tau_not_mem_inner
      refine ⟨(g.1 : GL (Fin 3) (ZMod 2))⁻¹, ?_⟩
      refine MulEquiv.ext fun c => ?_
      show (MulAut.conj ((g.1 : GL (Fin 3) (ZMod 2))⁻¹ : GL (Fin 3) (ZMod 2))) c = _
      rw [MulAut.conj_apply]
      have := hc c
      calc ((g.1 : GL (Fin 3) (ZMod 2))⁻¹ * c * ((g.1 : GL (Fin 3) (ZMod 2))⁻¹)⁻¹)
          = (g.1 : GL (Fin 3) (ZMod 2))⁻¹ * ((g.1 : GL (Fin 3) (ZMod 2)) *
              CFSG.LieType.SteinbergBR.AutGL32.tau c * (g.1 : GL (Fin 3) (ZMod 2))⁻¹) *
              ((g.1 : GL (Fin 3) (ZMod 2))⁻¹)⁻¹ := by rw [hc c]
        _ = CFSG.LieType.SteinbergBR.AutGL32.tau c := by group

theorem card_mulAut_SL32 : Nat.card (MulAut ↥SL32) = 336 := by
  let e : ↥SL32 ≃* GL (Fin 3) (ZMod 2) :=
    MulEquiv.ofBijective SL32.subtype ⟨Subtype.val_injective, fun g => ⟨⟨g, mem_SL32 g⟩, rfl⟩⟩
  rw [Nat.card_congr (MulAut.congr e).toEquiv]
  exact CFSG.LieType.SteinbergBR.AutGL32.card_mulAut_GL32

theorem Cd_equiv_mulAut : Nonempty (↥Cd ≃* MulAut ↥SL32) :=
  ⟨MulEquiv.ofBijective PhiC
    (PhiC_injective.bijective_of_nat_card_le (by rw [card_Cd, card_mulAut_SL32]))⟩

end CFSG.Quasithin.RonanH49
