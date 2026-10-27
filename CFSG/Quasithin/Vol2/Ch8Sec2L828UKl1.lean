module

public import CFSG.Quasithin.Vol2.Ch8Sec2L828UMod2

public section

namespace CFSG.Quasithin.H13

open CFSG.Open
open scoped commutatorElement IsMulCommutative
open CFSG.Quasithin.H13.L828T

section Kl1

variable {G : Type} [Group G] [Finite G] {T L I H : Subgroup G} {h : G} {k : ℕ}
  [IsMulCommutative ↥(fsuV T I)]

@[expose] noncomputable def ob5L {M : Type} [AddCommGroup M] [Module (ZMod 2) M] (f : AddMonoid.End M) :
    Module.End (ZMod 2) M where
  toFun := f
  map_add' := f.map_add
  map_smul' := fun a x => ZMod.map_smul f a x

theorem ob5L_apply {M : Type} [AddCommGroup M] [Module (ZMod 2) M] (f : AddMonoid.End M) (m : M) :
    ob5L f m = f m := rfl

theorem ob5L_mul {M : Type} [AddCommGroup M] [Module (ZMod 2) M] (f g : AddMonoid.End M) :
    ob5L (f * g) = ob5L f * ob5L g := by
  ext m
  rfl

theorem ob5_I_le_N_U (c : S828Ctx T L I H h k) :
    ch82I (fsuV T I) h ≤ Subgroup.normalizer (ch82U (fsuV T I) h : Set G) := by
  intro i hi
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [c.hcen x hx i hi]
    exact hx
  · intro hx
    have hi' : i⁻¹ ∈ ch82I (fsuV T I) h := (ch82I (fsuV T I) h).inv_mem hi
    have h1 := c.hcen _ hx i⁻¹ hi'
    have e : i⁻¹ * (i * x * i⁻¹) * i⁻¹⁻¹ = x := by group
    rw [e] at h1
    rw [h1]
    exact hx

theorem ob5_P_le_N0 (c : S828Ctx T L I H h k) :
    pCoreOf 2 (ch82I (fsuV T I) h) ≤ ob5N0 T I h := fun p hp =>
  Subgroup.mem_inf.mpr
    ⟨CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ ((CFSG.LieType.BorelTits.pCoreOf_le 2 _) hp),
      ob5_I_le_N_U c ((CFSG.LieType.BorelTits.pCoreOf_le 2 _) hp)⟩

theorem ob5_comm_of_commutator_mem_P [PtActCentralAbelian (pCoreOf 2 (ch82I (fsuV T I) h))
    (ch82U (fsuV T I) h)] (c : S828Ctx T L I H h k) (y κ : G)
    (hyN : y ∈ ob5N0 T I h) (hκN : κ ∈ ob5N0 T I h)
    (hc : κ * y * κ⁻¹ * y⁻¹ ∈ pCoreOf 2 (ch82I (fsuV T I) h)) :
    ob5rho c ⟨κ, hκN⟩ * ob5rho c ⟨y, hyN⟩ = ob5rho c ⟨y, hyN⟩ * ob5rho c ⟨κ, hκN⟩ := by
  have hcN : κ * y * κ⁻¹ * y⁻¹ ∈ ob5N0 T I h := ob5_P_le_N0 c hc
  have hcone : ob5rho c ⟨κ * y * κ⁻¹ * y⁻¹, hcN⟩ = 1 := by
    rw [ob5_rho_one_iff c]
    intro p hp
    have := c.hP2 _ hc p hp
    simpa [commutatorElement_def, mul_assoc] using this
  have e : κ * y = (κ * y * κ⁻¹ * y⁻¹) * (y * κ) := by group
  have hyκ : y * κ ∈ ob5N0 T I h := (ob5N0 T I h).mul_mem hyN hκN
  have hκy : κ * y ∈ ob5N0 T I h := (ob5N0 T I h).mul_mem hκN hyN
  have h1 : ob5rho c ⟨κ * y, hκy⟩ = ob5rho c ⟨κ * y * κ⁻¹ * y⁻¹, hcN⟩ * ob5rho c ⟨y * κ, hyκ⟩ := by
    rw [← map_mul]
    congr 1
    exact Subtype.ext e
  rw [hcone, one_mul] at h1
  rw [← map_mul, ← map_mul]
  exact (congrArg _ (Subtype.ext rfl : (⟨κ, hκN⟩ * ⟨y, hyN⟩ : ↥(ob5N0 T I h)) = ⟨κ * y, hκy⟩)).trans (h1.trans (congrArg _ (Subtype.ext rfl : (⟨y * κ, hyκ⟩ : ↥(ob5N0 T I h)) = ⟨y, hyN⟩ * ⟨κ, hκN⟩)))

end Kl1

end CFSG.Quasithin.H13
