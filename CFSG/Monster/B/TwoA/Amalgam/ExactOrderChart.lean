module

public import CFSG.Monster.B.TwoA.Amalgam.LocalLabelUnitary
public import CFSG.Monster.B.E6.StdF4FiberProd
public import CFSG.Monster.B.TwoA.Amalgam.ExactOrderCore
public import CFSG.Monster.B.TwoA.Amalgam.OrderThree
public import CFSG.Monster.B.TwoA.Amalgam.OrderThreeTTCore

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA
open CFSG.Monster.B.E6.StdF4 CFSG.LieType.Chevalley.C2E6Std
open CFSG.LieType.Chevalley.C2E6Std.FieldExtension (GStar)
open CFSG.Monster.B.Classical.UnitarySix (IsoPt ProjSU tPt projAct)

abbrev levelHom :
    ProjSU →* GStar :=
  (SemidirectProduct.inl : stdGroup →* GStar).comp (leviG.comp leviPSU.symm.toMonoidHom)

theorem levelHom_apply
    (p : ProjSU) :
    levelHom p = SemidirectProduct.inl (leviG (leviPSU.symm p)) :=
  rfl

theorem levelHom_injective :
    Function.Injective levelHom :=
  SemidirectProduct.inl_injective.comp (leviG_injective.comp leviPSU.symm.injective)

theorem natCard_levelHom_range :
    Nat.card levelHom.range = 9196830720 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective levelHom_injective).toEquiv,
    CFSG.Monster.B.TwoA.Fischer.card_projSU]

theorem exists_factor_levelHom
    {R : Type*} [Group R] (ψ : R →* GStar)
    (h : levelHom.range = ψ.range) :
    ∃ φ : R →* ProjSU, Function.Surjective φ ∧ ∀ a, levelHom (φ a) = ψ a := by
  have hmem : ∀ a, ψ a ∈ levelHom.range := fun a => h ▸ ⟨a, rfl⟩
  let φ : R →* ProjSU :=
    (MonoidHom.ofInjective levelHom_injective).symm.toMonoidHom.comp (ψ.codRestrict _ hmem)
  have hφ : ∀ a, levelHom (φ a) = ψ a := fun a =>
    MonoidHom.apply_ofInjective_symm levelHom_injective ⟨ψ a, hmem a⟩
  refine ⟨φ, fun p => ?_, hφ⟩
  obtain ⟨a, ha⟩ : levelHom p ∈ ψ.range := h ▸ ⟨p, rfl⟩
  exact ⟨a, levelHom_injective ((hφ a).trans ha)⟩

theorem natCard_zpowers_clabelS
    (u : CVert) : Nat.card (Subgroup.zpowers (clabelS u)) = 2 := by
  rw [Nat.card_zpowers, ← Subgroup.orderOf_coe, coe_clabelS, orderOf_clabel]

section Chart

variable {v w u : CVert}

theorem cnStab_le_vStab :
    cnGroup v w ⊓ vStab u ≤ vStab u := inf_le_right

theorem clabelS_mem_cnStab
    {z : CVert}
    (hz : z ∈ cgraph.neighborSet u ∩ cgraph.commonNeighbors v w) :
    clabelS z ∈ cnGroup v w ⊓ vStab u := by
  have H : ∀ x : CVert, LocalHom x := fun x => (nonempty_localHom x).some
  refine ⟨clabelS_mem_cnGroup hz.2, ?_⟩
  exact (H u).mem_stab _ |>.1 (clabelS_mem_stab H hz.1)

theorem levelHom_range_le_range
    (ρ : vStab u →* GStar)
    (τ : ↥(cgraph.neighborSet u ∩ cgraph.commonNeighbors v w) ≃ IsoPt)
    (hτ : ∀ (z : ↥(cgraph.neighborSet u ∩ cgraph.commonNeighbors v w)) (y : vStab u),
      ((y : Shat) : Dfull) = clabel z →
        ρ y = SemidirectProduct.inl (leviG (leviPSU.symm (tPt (τ z))))) :
    levelHom.range ≤ (ρ.comp (Subgroup.inclusion (cnStab_le_vStab (v := v) (w := w)))).range := by
  have e : levelHom.range = (⊤ : Subgroup ProjSU).map levelHom := MonoidHom.range_eq_map _
  refine e.trans_le ?_
  refine (congrArg (Subgroup.map levelHom) closure_range_tPt.symm).trans_le ?_
  refine (MonoidHom.map_closure levelHom _).trans_le ((Subgroup.closure_le _).2 ?_)
  rintro _ ⟨_, ⟨p, rfl⟩, rfl⟩
  have hz := clabelS_mem_cnStab (τ.symm p).2
  refine ⟨⟨clabelS (τ.symm p), hz⟩, ?_⟩
  have h := hτ (τ.symm p) (Subgroup.inclusion cnStab_le_vStab ⟨clabelS (τ.symm p), hz⟩) rfl
  simp only [Equiv.apply_symm_apply] at h
  exact (MonoidHom.comp_apply _ _ _).trans (h.trans (levelHom_apply _).symm)

theorem ker_comp_cnStab
    (ρ : vStab u →* GStar)
    (hker : ∀ y : vStab u, ρ y = 1 ↔ ((y : Shat) : Dfull) ∈ Subgroup.zpowers (clabel u)) :
    (ρ.comp (Subgroup.inclusion (cnStab_le_vStab (v := v) (w := w)))).ker =
      (Subgroup.zpowers (clabelS u)).subgroupOf (cnGroup v w ⊓ vStab u) := by
  ext y
  simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, hker, Subgroup.coe_inclusion,
    Subgroup.mem_subgroupOf, mem_zpowers_subtype_iff, coe_clabelS]

theorem natCard_cnStab_eq_range
    (hu : u ∈ cgraph.commonNeighbors v w) (ρ : vStab u →* GStar)
    (hker : ∀ y : vStab u, ρ y = 1 ↔ ((y : Shat) : Dfull) ∈ Subgroup.zpowers (clabel u)) :
    Nat.card (cnGroup v w ⊓ vStab u : Subgroup Shat) =
      Nat.card (ρ.comp (Subgroup.inclusion (cnStab_le_vStab (v := v) (w := w)))).range * 2 := by
  have hle : Subgroup.zpowers (clabelS u) ≤ cnGroup v w ⊓ vStab u := Subgroup.zpowers_le.2
    ⟨clabelS_mem_cnGroup hu, cvMul_clabelS_self (fun x => (nonempty_localHom x).some) u⟩
  have h2 : Nat.card (ρ.comp (Subgroup.inclusion (cnStab_le_vStab (v := v) (w := w)))).ker = 2 :=
    (Nat.card_congr (MulEquiv.subgroupCongr (ker_comp_cnStab ρ hker)).toEquiv).trans
      ((Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv).trans
        (natCard_zpowers_clabelS u))
  exact (Subgroup.card_eq_card_quotient_mul_card_subgroup _).trans (congrArg₂ (· * ·)
    (Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv) h2)

theorem levelHom_tPt_projAct_inv
    (g : ProjSU) (p : IsoPt) :
    levelHom (tPt ((projAct g)⁻¹ p)) = (levelHom g)⁻¹ * levelHom (tPt p) * levelHom g := by
  rw [← map_inv CFSG.Monster.B.Classical.UnitarySix.projAct,
    CFSG.Monster.B.Classical.UnitarySix.tPt_projAct, map_mul, map_mul, map_inv, inv_inv]

theorem tau_cvMul_eq
    (ρ : vStab u →* GStar) (iu : cgraph.neighborSet u ≃ rootClass)
    (τ : ↥(cgraph.neighborSet u ∩ cgraph.commonNeighbors v w) ≃ IsoPt)
    (hcompat : ∀ (y : vStab u) (z : cgraph.neighborSet u),
      SemidirectProduct.inl (iu (stabAct y z) : stdGroup) =
        (ρ y)⁻¹ * SemidirectProduct.inl (iu z : stdGroup) * ρ y)
    (hlab : ∀ (z : cgraph.neighborSet u) (y : vStab u), ((y : Shat) : Dfull) = clabel z →
      ρ y = SemidirectProduct.inl (iu z : stdGroup))
    (hτ : ∀ (z : ↥(cgraph.neighborSet u ∩ cgraph.commonNeighbors v w)) (y : vStab u),
      ((y : Shat) : Dfull) = clabel z →
        ρ y = SemidirectProduct.inl (leviG (leviPSU.symm (tPt (τ z)))))
    (φ : (cnGroup v w ⊓ vStab u : Subgroup Shat) →* ProjSU)
    (hφ : ∀ a, levelHom (φ a) = ρ (Subgroup.inclusion cnStab_le_vStab a))
    (a : (cnGroup v w ⊓ vStab u : Subgroup Shat))
    (x : ↥(cgraph.neighborSet u ∩ cgraph.commonNeighbors v w))
    (h : cvMul (x : CVert) (a : Shat) ∈ cgraph.neighborSet u ∩ cgraph.commonNeighbors v w) :
    τ ⟨_, h⟩ = (projAct (φ a))⁻¹ (τ x) := by
  have hiu : ∀ (y : CVert) (hy : y ∈ cgraph.neighborSet u ∩ cgraph.commonNeighbors v w),
      SemidirectProduct.inl (iu ⟨y, hy.1⟩ : stdGroup) = levelHom (tPt (τ ⟨y, hy⟩)) := by
    intro y hy
    have hx : clabelS y ∈ vStab u := cnStab_le_vStab (clabelS_mem_cnStab hy)
    exact (hlab ⟨y, hy.1⟩ ⟨_, hx⟩ rfl).symm.trans
      ((hτ ⟨y, hy⟩ ⟨_, hx⟩ rfl).trans (levelHom_apply _).symm)
  have e2 : SemidirectProduct.inl (iu ⟨_, h.1⟩ : stdGroup) =
      (ρ (Subgroup.inclusion cnStab_le_vStab a))⁻¹ *
        SemidirectProduct.inl (iu ⟨(x : CVert), x.2.1⟩ : stdGroup) *
        ρ (Subgroup.inclusion cnStab_le_vStab a) :=
    hcompat (Subgroup.inclusion cnStab_le_vStab a) ⟨(x : CVert), x.2.1⟩
  apply CFSG.Monster.B.Classical.UnitarySix.tPt_injective
  apply levelHom_injective
  calc levelHom (tPt (τ ⟨_, h⟩)) = SemidirectProduct.inl (iu ⟨_, h.1⟩ : stdGroup) :=
        (hiu _ h).symm
    _ = (ρ (Subgroup.inclusion cnStab_le_vStab a))⁻¹ *
          SemidirectProduct.inl (iu ⟨(x : CVert), x.2.1⟩ : stdGroup) *
          ρ (Subgroup.inclusion cnStab_le_vStab a) := e2
    _ = (ρ (Subgroup.inclusion cnStab_le_vStab a))⁻¹ * levelHom (tPt (τ x)) *
          ρ (Subgroup.inclusion cnStab_le_vStab a) :=
        congrArg (fun t => (ρ (Subgroup.inclusion cnStab_le_vStab a))⁻¹ * t *
          ρ (Subgroup.inclusion cnStab_le_vStab a)) (hiu x x.2)
    _ = (levelHom (φ a))⁻¹ * levelHom (tPt (τ x)) * levelHom (φ a) :=
        (congrArg (fun t => t⁻¹ * levelHom (tPt (τ x)) * t) (hφ a)).symm
    _ = levelHom (tPt ((projAct (φ a))⁻¹ (τ x))) := (levelHom_tPt_projAct_inv _ _).symm

variable (hw : w ∈ sphereThree v) (hu : u ∈ cgraph.commonNeighbors v w)
include hw hu

theorem two_mul_le_natCard_cnStab :
    2 * 9196830720 ≤ Nat.card (cnGroup v w ⊓ vStab u : Subgroup Shat) := by
  have hloc := native_local_unitary_transvection_map hw hu
  obtain ⟨ρ, -, -, hker, -, -, -, -, -, -, -, τ, hτ, -⟩ := hloc
  have h1 := Subgroup.card_le_of_le (levelHom_range_le_range ρ τ hτ)
  have h2 := natCard_levelHom_range
  have h3 := natCard_cnStab_eq_range hu ρ hker
  omega

theorem exists_chart_of_natCard_le
    (hup : Nat.card (cnGroup v w ⊓ vStab u : Subgroup Shat) ≤ 2 * 9196830720) :
    ∃ (τ : ↥(cgraph.neighborSet u ∩ cgraph.commonNeighbors v w) ≃ IsoPt)
      (φ : (cnGroup v w ⊓ vStab u : Subgroup Shat) →* ProjSU),
      Function.Surjective φ ∧
      (∀ a, φ a = 1 ↔ (a : Shat) ∈ Subgroup.zpowers (clabelS u)) ∧
      (∀ (z : ↥(cgraph.neighborSet u ∩ cgraph.commonNeighbors v w))
        (a : (cnGroup v w ⊓ vStab u : Subgroup Shat)), (a : Shat) = clabelS z →
          φ a = tPt (τ z)) ∧
      ∀ (a : (cnGroup v w ⊓ vStab u : Subgroup Shat))
        (x : ↥(cgraph.neighborSet u ∩ cgraph.commonNeighbors v w))
        (h : cvMul (x : CVert) (a : Shat) ∈ cgraph.neighborSet u ∩ cgraph.commonNeighbors v w),
        τ ⟨_, h⟩ = (projAct (φ a))⁻¹ (τ x) := by
  have hloc := native_local_unitary_transvection_map hw hu
  obtain ⟨ρ, iu, -, hker, hcompat, -, hlab, -, -, -, -, τ, hτ, -⟩ := hloc
  have hcard := natCard_cnStab_eq_range hu ρ hker
  have h1 := natCard_levelHom_range
  have heq : levelHom.range =
      (ρ.comp (Subgroup.inclusion (cnStab_le_vStab (v := v) (w := w)))).range :=
    Subgroup.eq_of_le_of_card_ge (levelHom_range_le_range ρ τ hτ) (by omega)
  have hfac := exists_factor_levelHom _ heq
  obtain ⟨φ, hφs, hφ⟩ := hfac
  have hφ' : ∀ a, levelHom (φ a) = ρ (Subgroup.inclusion cnStab_le_vStab a) := fun a =>
    (hφ a).trans (MonoidHom.comp_apply _ _ _)
  have hk := ker_comp_cnStab (v := v) (w := w) ρ hker
  refine ⟨τ, φ, hφs, fun a => ?_, fun z a ha => ?_,
    tau_cvMul_eq ρ iu τ hcompat hlab hτ φ hφ'⟩
  · have e := congrArg (fun K : Subgroup (cnGroup v w ⊓ vStab u : Subgroup Shat) => a ∈ K) hk
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_subgroupOf] at e
    exact levelHom_injective.eq_iff.symm.trans
      ((map_one levelHom).symm ▸ (hφ' a).symm ▸ Iff.of_eq e)
  · apply levelHom_injective
    refine (hφ' a).trans ((hτ z _ ?_).trans (levelHom_apply _).symm)
    exact (congrArg Subtype.val ha).trans (coe_clabelS _)

end Chart

end CFSG.Monster.B.TwoA.Amalgam
