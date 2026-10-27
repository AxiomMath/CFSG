module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.Quasithin.Vol2.Ch10SecKRPa
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.KRK

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

section PCore

variable {A C : Type*} [Group A] [Group C]

theorem isPGroup_of_map {f : A →* C} (hker : IsPGroup 2 f.ker) {N : Subgroup A}
    (hN : IsPGroup 2 (N.map f)) : IsPGroup 2 N := by
  intro x
  obtain ⟨k, hk⟩ := hN ⟨f x, x, x.2, rfl⟩
  have hk' : f ((x : A) ^ 2 ^ k) = 1 := by
    rw [map_pow]
    exact congrArg Subtype.val hk
  obtain ⟨m, hm⟩ := hker ⟨(x : A) ^ 2 ^ k, hk'⟩
  refine ⟨k + m, Subtype.ext ?_⟩
  have hm' : ((x : A) ^ 2 ^ k) ^ 2 ^ m = 1 := congrArg Subtype.val hm
  rw [pow_add, pow_mul]
  simpa using hm'

theorem comap_pCore_eq_of_surjective {f : A →* C} (hf : Function.Surjective f)
    (hker : IsPGroup 2 f.ker) : (CFSG.pCore 2 C).comap f = CFSG.pCore 2 A := by
  have hPC : IsPGroup 2 (CFSG.pCore 2 C) := CFSG.pCore_isPGroup
  have hPA : IsPGroup 2 (CFSG.pCore 2 A) := CFSG.pCore_isPGroup
  refine le_antisymm ?_ ?_
  · have hn : ((CFSG.pCore 2 C).comap f).Normal := CFSG.pCore_normal.comap f
    have h2 : IsPGroup 2 ((CFSG.pCore 2 C).comap f) :=
      isPGroup_of_map hker (hPC.to_le (Subgroup.map_comap_le _ _))
    exact le_sSup ⟨hn, h2⟩
  · rw [← Subgroup.map_le_iff_le_comap]
    have hn : ((CFSG.pCore 2 A).map f).Normal := CFSG.pCore_normal.map f hf
    exact le_sSup ⟨hn, hPA.map f⟩

theorem map_pCore_eq_of_surjective {f : A →* C} (hf : Function.Surjective f)
    (hker : IsPGroup 2 f.ker) : (CFSG.pCore 2 A).map f = CFSG.pCore 2 C := by
  rw [← comap_pCore_eq_of_surjective hf hker, Subgroup.map_comap_eq_self_of_surjective hf]

noncomputable def modO2EquivOfSurjective {f : A →* C} (hf : Function.Surjective f)
    (hker : IsPGroup 2 f.ker) : A ⧸ CFSG.pCore 2 A ≃* C ⧸ CFSG.pCore 2 C :=
  have hs : Function.Surjective ((QuotientGroup.mk' (CFSG.pCore 2 C)).comp f) :=
    (QuotientGroup.mk'_surjective _).comp hf
  have hk : ((QuotientGroup.mk' (CFSG.pCore 2 C)).comp f).ker = CFSG.pCore 2 A := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    exact comap_pCore_eq_of_surjective hf hker
  (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ hs)

end PCore

section Conj

variable {Γ : Type*} [Group Γ] (J : Subgroup Γ)

@[expose] def conjHom : ↥(Subgroup.normalizer (J : Set Γ)) →* MulAut ↥J where
  toFun n :=
    { toFun := fun x => ⟨(n : Γ) * x * (n : Γ)⁻¹, (Subgroup.mem_normalizer_iff.mp n.2 x).mp x.2⟩
      invFun := fun x => ⟨(n : Γ)⁻¹ * x * (n : Γ), by
        have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ n.2) x).mp x.2
        simpa only [inv_inv] using h⟩
      left_inv := fun x => Subtype.ext (by simp [mul_assoc])
      right_inv := fun x => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun x y => Subtype.ext (by simp [mul_assoc]) }
  map_one' := by
    ext x
    simp
  map_mul' n m := by
    ext x
    simp [mul_assoc]

theorem coe_conjHom_apply (n : ↥(Subgroup.normalizer (J : Set Γ))) (x : ↥J) :
    ((conjHom J n x : ↥J) : Γ) = (n : Γ) * x * (n : Γ)⁻¹ := rfl

variable {X : Type*} [Group X]

@[expose] noncomputable def descendHom : MulAut X →* MulAut (X ⧸ CFSG.pCore 2 X) where
  toFun ψ := QuotientGroup.congr _ _ ψ (CFSG.pCore_map_iso 2 ψ)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl
  map_mul' ψ φ := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl

end Conj

section Central

variable {Γ : Type*} [Group Γ]

theorem commute_of_conj_mul_inv_mem_center {J : Subgroup Γ} (hJ : ⁅J, J⁆ = J) {r : Γ}
    (hr : r ∈ Subgroup.normalizer (J : Set Γ))
    (hc : ∀ x ∈ J, ∀ y ∈ J, r * x * r⁻¹ * x⁻¹ * y = y * (r * x * r⁻¹ * x⁻¹)) :
    ∀ x ∈ J, r * x = x * r := by
  have hmem : ∀ x ∈ J, r * x * r⁻¹ * x⁻¹ ∈ J := fun x hx =>
    J.mul_mem ((Subgroup.mem_normalizer_iff.mp hr x).mp hx) (J.inv_mem hx)
  have hcomm : ∀ x ∈ J, ∀ y ∈ J, r * (x * y) * r⁻¹ * (x * y)⁻¹ =
      r * x * r⁻¹ * x⁻¹ * (r * y * r⁻¹ * y⁻¹) := by
    intro x hx y hy
    have h := hc y hy (r * x * r⁻¹) ((Subgroup.mem_normalizer_iff.mp hr x).mp hx)
    have h' := hc x hx (r * y * r⁻¹ * y⁻¹) (hmem y hy)
    calc r * (x * y) * r⁻¹ * (x * y)⁻¹
        = (r * x * r⁻¹) * (r * y * r⁻¹ * y⁻¹) * x⁻¹ := by group
      _ = (r * y * r⁻¹ * y⁻¹) * (r * x * r⁻¹) * x⁻¹ := by rw [h]
      _ = (r * y * r⁻¹ * y⁻¹) * (r * x * r⁻¹ * x⁻¹) := by group
      _ = r * x * r⁻¹ * x⁻¹ * (r * y * r⁻¹ * y⁻¹) := h'.symm
  let φ : ↥J →* ↥(Subgroup.center ↥J) :=
    { toFun := fun x => ⟨⟨_, hmem x x.2⟩,
        Subgroup.mem_center_iff.mpr fun y => Subtype.ext (hc x x.2 y y.2).symm⟩
      map_one' := Subtype.ext (Subtype.ext (by simp))
      map_mul' := fun x y => Subtype.ext (Subtype.ext (hcomm x x.2 y y.2)) }
  have hker : commutator ↥J ≤ φ.ker := Abelianization.commutator_subset_ker φ
  have htop : commutator ↥J = ⊤ := by
    apply Subgroup.map_injective J.subtype_injective
    rw [Subgroup.map_subtype_commutator, hJ, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  intro x hx
  have h1 : φ ⟨x, hx⟩ = 1 := hker (htop ▸ Subgroup.mem_top _)
  have h2 : r * x * r⁻¹ * x⁻¹ = 1 := congrArg (fun z : ↥(Subgroup.center ↥J) => ((z : ↥J) : Γ)) h1
  calc r * x = r * x * r⁻¹ * x⁻¹ * (x * r) := by group
    _ = x * r := by rw [h2, one_mul]

end Central

end CFSG.Quasithin.Vol2.Ch10.SecC.KRK
