module

public import CFSG.Milestones.ASVolI.C121.P1d

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC CFSG.LieType.BorelTits
open scoped MatrixGroups commutatorElement

theorem burnsideC121_hom_trivial_of_perfect {A B : Type*} [Group A] [Group B]
    [Group.IsPerfect A] [Group.IsSolvable B] (f : A →* B) (a : A) : f a = 1 := by
  have hP : Group.IsPerfect f.range := Group.IsPerfect.range f
  have hS : Group.IsSolvable f.range := inferInstance
  by_contra h
  have : Nontrivial f.range := ⟨⟨⟨f a, a, rfl⟩, 1, fun e => h (congrArg Subtype.val e)⟩⟩
  exact absurd hS (Group.IsPerfect.not_isSolvable _)

theorem burnsideC121_perfect_centralizes_section {Ω : Type} [Group Ω] [Finite Ω]
    {L U Z : Subgroup Ω} (hU : IsElemAbelian 2 U) (hZU : Z ≤ U)
    (hLU : L ≤ Subgroup.normalizer (U : Set Ω)) (hLZ : L ≤ Subgroup.normalizer (Z : Set Ω))
    (hperf : ⁅L, L⁆ = L) (hcard : Nat.card U ≤ 4 * Nat.card Z) :
    ∀ l ∈ L, ∀ u ∈ U, l * u * l⁻¹ * u⁻¹ ∈ Z := by
  classical
  let ρ : ↥L →* MulAut (IntMod U hU) := convHom hU L hLU
  let N : Subgroup (IntMod U hU) := Z.comap (burnsideC121_valHom hU)
  have hW : B3.IsInv ρ (⊤ : Subgroup (IntMod U hU)) := fun _ _ _ => Subgroup.mem_top _
  have hN : B3.IsInv ρ N := by
    intro g w hw
    show (ρ g w).val ∈ Z
    rw [convHom_apply, convI_apply_val]
    exact (Subgroup.mem_normalizer_iff.1 (hLZ g.2) w.val).1 hw
  let σ := B3.secAct ρ hW hN
  have hcardSec : Nat.card (B3.Sec (⊤ : Subgroup (IntMod U hU)) N) ≤ 4 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf ⊤)
    have h2 : Nat.card ↥(⊤ : Subgroup (IntMod U hU)) = Nat.card U := by
      rw [Subgroup.card_top]
      rfl
    have h3 : Nat.card ↥(N.subgroupOf ⊤) = Nat.card Z := by
      have e1 : Nat.card ↥(N.subgroupOf ⊤) = Nat.card N :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_top).toEquiv
      rw [e1]
      refine Nat.card_congr ⟨fun x => ⟨x.1.val, x.2⟩, fun z => ⟨IntMod.mk hU ⟨z.1, hZU z.2⟩, z.2⟩,
        fun x => rfl, fun z => rfl⟩
    rw [h2, h3] at h1
    have hpos : 0 < Nat.card Z := Nat.card_pos
    by_contra hc
    push Not at hc
    have : 5 * Nat.card Z ≤ Nat.card U := by
      rw [h1]
      exact Nat.mul_le_mul_right _ hc
    omega
  have hsolv : Group.IsSolvable (MulAut (B3.Sec (⊤ : Subgroup (IntMod U hU)) N)) := by
    apply CFSG.GroupTheory.groups_order_below_sixty_solvable
    have hinj : Function.Injective
        (fun e : MulAut (B3.Sec (⊤ : Subgroup (IntMod U hU)) N) => e.toEquiv) :=
      fun a b h => MulEquiv.ext fun x => congrFun (congrArg DFunLike.coe h) x
    have h1 := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_perm] at h1
    have h2 : (Nat.card (B3.Sec (⊤ : Subgroup (IntMod U hU)) N)).factorial ≤ Nat.factorial 4 :=
      Nat.factorial_le hcardSec
    have h3 : Nat.factorial 4 = 24 := by decide
    omega
  have hLp : Group.IsPerfect ↥L := (Subgroup.isPerfect_iff).2 hperf
  have htriv := burnsideC121_hom_trivial_of_perfect σ
  intro l hl u hu
  have h1 := congrArg (fun e : MulAut (B3.Sec (⊤ : Subgroup (IntMod U hU)) N) =>
    e (QuotientGroup.mk ⟨IntMod.mk hU ⟨u, hu⟩, Subgroup.mem_top _⟩)) (htriv ⟨l, hl⟩)
  simp only [MulAut.one_apply] at h1
  have h2 : σ ⟨l, hl⟩ (QuotientGroup.mk ⟨IntMod.mk hU ⟨u, hu⟩, Subgroup.mem_top _⟩) =
      QuotientGroup.mk ⟨ρ ⟨l, hl⟩ (IntMod.mk hU ⟨u, hu⟩), Subgroup.mem_top _⟩ := rfl
  rw [h2, QuotientGroup.eq, Subgroup.mem_subgroupOf] at h1
  have h3 : ((ρ ⟨l, hl⟩ (IntMod.mk hU ⟨u, hu⟩)).val) = l * u * l⁻¹ := by
    show (convHom hU L hLU ⟨l, hl⟩ (IntMod.mk hU ⟨u, hu⟩)).val = _
    rw [convHom_apply, convI_apply_val]
    rfl
  have h4 : (((⟨ρ ⟨l, hl⟩ (IntMod.mk hU ⟨u, hu⟩), Subgroup.mem_top _⟩ :
      ↥(⊤ : Subgroup (IntMod U hU)))⁻¹ * ⟨IntMod.mk hU ⟨u, hu⟩, Subgroup.mem_top _⟩ :
      ↥(⊤ : Subgroup (IntMod U hU))) : IntMod U hU).val ∈ Z := h1
  rw [Subgroup.coe_mul, Subgroup.coe_inv, IntMod.val_mul, IntMod.val_inv, h3] at h4
  have h5 := Z.inv_mem h4
  have hxU : l * u * l⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.1 (hLU hl) u).1 hu
  have hcomm : u⁻¹ * (l * u * l⁻¹) = (l * u * l⁻¹) * u⁻¹ :=
    B2F.isElemAbelian_comm hU (U.inv_mem hu) hxU
  have e : ((l * u * l⁻¹)⁻¹ * (IntMod.mk hU ⟨u, hu⟩).val)⁻¹ = l * u * l⁻¹ * u⁻¹ := by
    show ((l * u * l⁻¹)⁻¹ * u)⁻¹ = l * u * l⁻¹ * u⁻¹
    rw [mul_inv_rev, inv_inv, hcomm]
  rwa [e] at h5

end CFSG.ASVolI
