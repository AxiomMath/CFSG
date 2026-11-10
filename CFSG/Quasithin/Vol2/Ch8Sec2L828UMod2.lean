module

public import CFSG.Quasithin.Vol2.Ch8Sec2L828UMod1

public section

namespace CFSG.Quasithin.H13

open CFSG.Open
open scoped commutatorElement IsMulCommutative
open CFSG.Quasithin.H13.L828T

section Mod2

variable {G : Type} [Group G] [Finite G] {T L I H : Subgroup G} {h : G} {k : ℕ}
  [IsMulCommutative ↥(fsuV T I)]

theorem ob5_QB_two_nsmul (c : S828Ctx T L I H h k)
    (x : QB (fsuV T I) (ch82B (fsuV T I) h) (ch82U (fsuV T I) h)) :
    (2 : ℕ) • x = 0 := by
  obtain ⟨b, rfl⟩ := QMod.mk_surjective _ _ x
  have hbb : (b : ↥(fsuV T I)) * (b : ↥(fsuV T I)) = 1 := by
    apply Subtype.ext
    have := c.hV.2 ((b : ↥(fsuV T I)) : G) (b : ↥(fsuV T I)).2
    rw [pow_two] at this
    exact this
  have h1 : b * b = 1 := Subtype.ext hbb
  rw [two_nsmul, ← QMod.mk_add, h1, QMod.mk_one]

noncomputable def ob5QBModule (c : S828Ctx T L I H h k) :
    Module (ZMod 2) (QB (fsuV T I) (ch82B (fsuV T I) h) (ch82U (fsuV T I) h)) :=
  AddCommGroup.zmodModule (ob5_QB_two_nsmul c)

abbrev ob5N0 (T I : Subgroup G) (h : G) : Subgroup G :=
  Subgroup.normalizer (pCoreOf 2 (ch82I (fsuV T I) h) : Set G) ⊓
    Subgroup.normalizer (ch82U (fsuV T I) h : Set G)

@[expose] noncomputable def ob5rho (c : S828Ctx T L I H h k)
    [PtActCentralAbelian (pCoreOf 2 (ch82I (fsuV T I) h)) (ch82U (fsuV T I) h)] :
    ↥(ob5N0 T I h) →* AddMonoid.End (QB (fsuV T I) (ch82B (fsuV T I) h) (ch82U (fsuV T I) h) ×
      QB (fsuV T I) (ch82B (fsuV T I) h) (ch82U (fsuV T I) h)) := by
  exact ptActRhoHom (ob5_ptActSetup c)

@[expose] noncomputable def ob5theta (c : S828Ctx T L I H h k)
    [PtActCentralAbelian (pCoreOf 2 (ch82I (fsuV T I) h)) (ch82U (fsuV T I) h)] :
    (QB (fsuV T I) (ch82B (fsuV T I) h) (ch82U (fsuV T I) h) ×
      QB (fsuV T I) (ch82B (fsuV T I) h) (ch82U (fsuV T I) h)) ≃+
      Additive (↥(pCoreOf 2 (ch82I (fsuV T I) h)) ⧸
        (ch82U (fsuV T I) h).subgroupOf (pCoreOf 2 (ch82I (fsuV T I) h))) := by
  exact ptActThetaEquiv (ob5_ptActSetup c)

theorem ob5_rho_one_iff (c : S828Ctx T L I H h k)
    [PtActCentralAbelian (pCoreOf 2 (ch82I (fsuV T I) h)) (ch82U (fsuV T I) h)] (g : G) (hg : g ∈ ob5N0 T I h) :
    ob5rho c ⟨g, hg⟩ = 1 ↔ ∀ p ∈ pCoreOf 2 (ch82I (fsuV T I) h),
      g * p * g⁻¹ * p⁻¹ ∈ ch82U (fsuV T I) h := by
  exact ptActRho_eq_one_iff (ob5_ptActSetup c) g hg

theorem ob5_theta_rho (c : S828Ctx T L I H h k)
    [PtActCentralAbelian (pCoreOf 2 (ch82I (fsuV T I) h)) (ch82U (fsuV T I) h)] (g : G) (hg : g ∈ ob5N0 T I h)
    (m : QB (fsuV T I) (ch82B (fsuV T I) h) (ch82U (fsuV T I) h) ×
      QB (fsuV T I) (ch82B (fsuV T I) h) (ch82U (fsuV T I) h)) :
    ob5theta c (ob5rho c ⟨g, hg⟩ m) = MonoidHom.toAdditive
      (ptActConj (pCoreOf 2 (ch82I (fsuV T I) h)) (ch82U (fsuV T I) h) g
        (Subgroup.mem_inf.mp hg).1 (Subgroup.mem_inf.mp hg).2) (ob5theta c m) := by
  show (ptActThetaEquiv (ob5_ptActSetup c)) (ptActRho (ob5_ptActSetup c) g hg m) = _
  rw [ptActRho_apply, AddEquiv.apply_symm_apply]
  rfl

theorem ob5_fix_M (c : S828Ctx T L I H h k)
    [PtActCentralAbelian (pCoreOf 2 (ch82I (fsuV T I) h)) (ch82U (fsuV T I) h)] (y : G) (hyN : y ∈ ob5N0 T I h)
    (hfix : ∀ p ∈ pCoreOf 2 (ch82I (fsuV T I) h),
      y * p * y⁻¹ * p⁻¹ ∈ ch82U (fsuV T I) h → p ∈ ch82U (fsuV T I) h)
    (m : QB (fsuV T I) (ch82B (fsuV T I) h) (ch82U (fsuV T I) h) ×
      QB (fsuV T I) (ch82B (fsuV T I) h) (ch82U (fsuV T I) h))
    (hm : ob5rho c ⟨y, hyN⟩ m = m) : m = 0 := by
  obtain ⟨⟨p, hpP⟩, hp⟩ := QuotientGroup.mk_surjective (Additive.toMul (ob5theta c m))
  have key : ob5theta c (ob5rho c ⟨y, hyN⟩ m) = ob5theta c m := by rw [hm]
  rw [ob5_theta_rho] at key
  have hθ : ob5theta c m = Additive.ofMul (QuotientGroup.mk ⟨p, hpP⟩) := by
    rw [hp]
    rfl
  rw [hθ] at key
  have key3 : ptActConj (pCoreOf 2 (ch82I (fsuV T I) h)) (ch82U (fsuV T I) h) y
      (Subgroup.mem_inf.mp hyN).1 (Subgroup.mem_inf.mp hyN).2 (QuotientGroup.mk ⟨p, hpP⟩) =
      QuotientGroup.mk ⟨p, hpP⟩ := Additive.ofMul.injective key
  rw [ptActConj_mk] at key3
  have hU : y * p * y⁻¹ * p⁻¹ ∈ ch82U (fsuV T I) h := (ptActMk_eq_iff _ _ _ _).mp key3
  have hpU : p ∈ ch82U (fsuV T I) h := hfix p hpP hU
  have hz : (QuotientGroup.mk ⟨p, hpP⟩ : ↥(pCoreOf 2 (ch82I (fsuV T I) h)) ⧸
      (ch82U (fsuV T I) h).subgroupOf (pCoreOf 2 (ch82I (fsuV T I) h))) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hpU)
  have hθ0 : ob5theta c m = 0 := by
    rw [hθ, hz]
    rfl
  exact (ob5theta c).map_eq_zero_iff.mp hθ0

end Mod2

end CFSG.Quasithin.H13
