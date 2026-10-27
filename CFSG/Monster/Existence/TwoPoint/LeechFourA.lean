module

public import CFSG.Monster.Existence.TwoPoint.LeechMG
public import CFSG.Monster.Existence.TwoPoint.LeechShape

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.ScalarKernel CFSG.Monster.Visible CFSG.Monster.VisQuot
  CFSG.Monster.VisCert CFSG.Monster.Generated CFSG.Monster.B.Short CFSG.Monster.B Subgroup

theorem leech_zmod_two_cases : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide

section Generic

variable {G : Type*} [Group G]

theorem leech_zpow_one_val (z r : G) : z ^ (1 : ZMod 2).val * r = z * r := by
  rw [ZMod.val_one, pow_one]

end Generic

theorem leech_mul_self_of_bL_eq_one {r₁ r₂ : Q} (hr₁ : IsShortCoord (coordOf r₁))
    (hr₂ : IsShortCoord (coordOf r₂)) (h12 : bL (phi0 (coordOf r₁)) (phi0 (coordOf r₂)) = 1) :
    (r₂ * r₁) * (r₂ * r₁) = zQ := by
  have hq₁ : r₁ * r₁ = 1 := (mul_self_eq_one_iff_qL r₁).2 (leech_qL_phi0_eq_zero hr₁)
  have hq₂ : r₂ * r₂ = 1 := (mul_self_eq_one_iff_qL r₂).2 (leech_qL_phi0_eq_zero hr₂)
  have hb : bL (phi0 (coordOf r₂)) (phi0 (coordOf r₁)) = 1 := (bL_comm _ _).trans h12
  have h5 : r₁⁻¹ * r₂ * r₁ = zQ * r₂ :=
    (leech_inv_mul_mul_eq_zpow_bL r₂ r₁).trans
      ((congrArg (fun b : ZMod 2 => zQ ^ b.val * r₂) hb).trans (leech_zpow_one_val zQ r₂))
  exact leech_mul_self_ab hq₂ hq₁ (leech_mul_eq_of_inv_mul_mul Short.zQ_mem_center hq₁ h5)

theorem leech_sq_rhoGriess_mul {r₁ r₂ : Q} (hr₁ : IsShortCoord (coordOf r₁))
    (hr₂ : IsShortCoord (coordOf r₂)) (h12 : bL (phi0 (coordOf r₁)) (phi0 (coordOf r₂)) = 1) :
    (rhoGriess r₁ * rhoGriess r₂) ^ 2 = xGriess := by
  have hab : rhoGriess r₁ * rhoGriess r₂ = rhoGriess (r₂ * r₁) := (rhoGriess_mul r₂ r₁).symm
  rw [pow_two, hab, ← rhoGriess_mul, leech_mul_self_of_bL_eq_one hr₁ hr₂ h12, rhoGriess_zQ]

theorem xGriess_ne_one : xGriess ≠ 1 := fun h => by
  have := orderOf_xGriess
  rw [h, orderOf_one] at this
  exact absurd this (by norm_num)

theorem leech_mem_cent2_iff {r₁ r₂ : Q} (hsq : (rhoGriess r₁ * rhoGriess r₂) ^ 2 = xGriess)
    (g : MGriess) : g ∈ cent2 (rhoGriess r₁) (rhoGriess r₂) ↔ g * rhoGriess r₁ = rhoGriess r₁ * g ∧
      g * rhoGriess r₂ = rhoGriess r₂ * g ∧ g * xGriess = xGriess * g := by
  constructor
  · intro hg
    obtain ⟨h1, h2⟩ := mem_inf.1 hg
    have h1' := mem_centralizer_singleton_iff.1 h1
    have h2' := mem_centralizer_singleton_iff.1 h2
    refine ⟨h1', h2', ?_⟩
    have := leech_commute_sq h1' h2'
    rwa [hsq] at this
  · rintro ⟨h1, h2, -⟩
    exact mem_inf.2 ⟨mem_centralizer_singleton_iff.2 h1, mem_centralizer_singleton_iff.2 h2⟩

theorem leech_cent2_le_cent {α β : MGriess} (h : (α * β) ^ 2 = xGriess) :
    cent2 α β ≤ cent xGriess := by
  intro g hg
  obtain ⟨h1, h2⟩ := mem_inf.1 hg
  have h3 := leech_commute_sq (mem_centralizer_singleton_iff.1 h1)
    (mem_centralizer_singleton_iff.1 h2)
  rw [h] at h3
  exact mem_centralizer_singleton_iff.2 h3

theorem leech_fourA_shape_of_rep
    {r₁ r₂ : Q} (hr₁ : IsShortCoord (coordOf r₁))
    (hr₂ : IsShortCoord (coordOf r₂)) (h12 : bL (phi0 (coordOf r₁)) (phi0 (coordOf r₂)) = 1) :
    IsConj tGriess (rhoGriess r₁) ∧ IsConj tGriess (rhoGriess r₂) ∧
      orderOf (rhoGriess r₁ * rhoGriess r₂) = 4 ∧
      (rhoGriess r₁ * rhoGriess r₂) ^ 2 = xGriess ∧
      ∃ (N : Subgroup ↥(cent2 (rhoGriess r₁) (rhoGriess r₂))) (_ : N.Normal),
        IsExtraspecialPGroup 2 N ∧ Nat.card N = 2 ^ 23 ∧
          Nonempty (↥(cent2 (rhoGriess r₁) (rhoGriess r₂)) ⧸ N ≃*
            ↥(Kstab (phi0 (coordOf r₁)) ⊓ Kstab (phi0 (coordOf r₂)))) := by
  have hsq := leech_sq_rhoGriess_mul hr₁ hr₂ h12
  refine ⟨leech_isConj_tGriess_rhoGriess hr₁, leech_isConj_tGriess_rhoGriess hr₂,
    leech_orderOf_eq_four_of_sq hsq xGriess_mul_self xGriess_ne_one, hsq, ?_⟩
  exact leech_exists_extraspecial_shape_of_mulEquiv
    (H := leechJ r₁ r₂) (H' := cent2 (rhoGriess r₁) (rhoGriess r₂))
    (X := ↥(Kstab (phi0 (coordOf r₁)) ⊓ Kstab (phi0 (coordOf r₂))))
    (equivLeechJ (leech_mem_cent2_iff hsq)).symm (leechJ_extraspecial_shape hr₁ hr₂ h12)

theorem leech_fourA_shape_gen
    {v₁ v₂ : L2} (h₁ : v₁ ∈ shortSet) (h₂ : v₂ ∈ shortSet)
    (h12 : bL v₁ v₂ = 1) :
    ∃ α β : MGriess, IsConj tGriess α ∧ IsConj tGriess β ∧ orderOf (α * β) = 4 ∧
      (α * β) ^ 2 = xGriess ∧
      ∃ (N : Subgroup ↥(cent2 α β)) (_ : N.Normal), IsExtraspecialPGroup 2 N ∧
        Nat.card N = 2 ^ 23 ∧ Nonempty (↥(cent2 α β) ⧸ N ≃* ↥(Kstab v₁ ⊓ Kstab v₂)) := by
  obtain ⟨r₁, hr₁, rfl⟩ := leech_exists_short_rep h₁
  obtain ⟨r₂, hr₂, rfl⟩ := leech_exists_short_rep h₂
  exact ⟨rhoGriess r₁, rhoGriess r₂, leech_fourA_shape_of_rep hr₁ hr₂ h12⟩

theorem leech_fourA_shape
    (v₂ : L2) (h₂ : v₂ ∈ shortSet) (h12 : bL Co2.v0 v₂ = 1) :
    ∃ α β : MGriess, IsConj tGriess α ∧ IsConj tGriess β ∧ orderOf (α * β) = 4 ∧
      (α * β) ^ 2 = xGriess ∧
      ∃ (N : Subgroup ↥(cent2 α β)) (_ : N.Normal), IsExtraspecialPGroup 2 N ∧
        Nat.card N = 2 ^ 23 ∧ Nonempty (↥(cent2 α β) ⧸ N ≃* ↥(Kstab Co2.v0 ⊓ Kstab v₂)) :=
  leech_fourA_shape_gen classOf_vMinus_mem_shortSet h₂ h12

theorem bL_eq_qL_add_of_short {v₁ v₂ : L2} (h₁ : v₁ ∈ shortSet) (h₂ : v₂ ∈ shortSet) :
    bL v₁ v₂ = qL (v₁ + v₂) := by
  have e1 : qL v₁ = 0 := h₁.elim fun _ hu => hu.2 ▸ qL_classOf_minVecs hu.1
  have e2 : qL v₂ = 0 := h₂.elim fun _ hu => hu.2 ▸ qL_classOf_minVecs hu.1
  rw [qL_add, e1, e2, zero_add, zero_add]

theorem leech_fourA_shape_of_qL
    (v₂ : L2) (h₂ : v₂ ∈ shortSet) (hq : qL (Co2.v0 + v₂) = 1) :
    ∃ α β : MGriess, IsConj tGriess α ∧ IsConj tGriess β ∧ orderOf (α * β) = 4 ∧
      (α * β) ^ 2 = xGriess ∧
      ∃ (N : Subgroup ↥(cent2 α β)) (_ : N.Normal), IsExtraspecialPGroup 2 N ∧
        Nat.card N = 2 ^ 23 ∧ Nonempty (↥(cent2 α β) ⧸ N ≃* ↥(Kstab Co2.v0 ⊓ Kstab v₂)) :=
  leech_fourA_shape v₂ h₂ ((bL_eq_qL_add_of_short classOf_vMinus_mem_shortSet h₂).trans hq)

theorem exists_leech_fourA_class :
    ∃ v₂ : L2, v₂ ∈ shortSet ∧ bL Co2.v0 v₂ = 1 := by
  by_contra hcon
  push Not at hcon
  have hinv : ∀ p : Pvis, ∀ w ∈ Submodule.span (ZMod 2) shortSet,
      modTwoEnd p.1.2 w ∈ Submodule.span (ZMod 2) shortSet := fun p w hw => by
    have h : Submodule.span (ZMod 2) shortSet ≤
        (Submodule.span (ZMod 2) shortSet).comap (modTwoEnd p.1.2) :=
      Submodule.span_le.2 fun w' hw' => Submodule.subset_span (modTwoEnd_mem_shortSet p.1.2 hw')
    exact h hw
  have hne : Submodule.span (ZMod 2) shortSet ≠ ⊥ := fun h =>
    Co2.v0_ne_zero (by
      have := Submodule.subset_span (R := ZMod 2) classOf_vMinus_mem_shortSet
      rw [h] at this
      exact this)
  have htop : Submodule.span (ZMod 2) shortSet = ⊤ :=
    (eq_bot_or_eq_top_of_invariant hinv).resolve_left hne
  have hker : Submodule.span (ZMod 2) shortSet ≤ LinearMap.ker (bL Co2.v0) := by
    rw [Submodule.span_le]
    intro w hw
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    exact (leech_zmod_two_cases _).resolve_right (hcon w hw)
  refine Co2.v0_ne_zero (bL_nondegenerate.1 _ fun y => ?_)
  have hy : y ∈ LinearMap.ker (bL Co2.v0) := hker (htop ▸ Submodule.mem_top)
  exact hy

end CFSG.Monster.Existence
