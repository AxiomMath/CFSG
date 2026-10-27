module

public import CFSG.Quasithin.Background.A1cModuleCoprime
public import CFSG.Quasithin.Background.B2Thompson

public section

namespace CFSG.Quasithin

open CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G]

theorem isCompl_fixV_commV_of_odd {V : Type*} [CommGroup V] (X : Subgroup (MulAut V)) [Finite X]
    (hodd : Odd (Nat.card X)) (hV : ∀ v : V, v ^ 2 = 1) : IsCompl (fixV X) (commV X) := by
  have h := XMod.isCompl_fixed_commOf_of_odd (A := ↥X) (Q := V) hodd hV
  have h1 : XMod.fixed (↥X) (⊤ : Subgroup V) = fixV X := by
    ext v
    simp only [XMod.mem_fixed, Subgroup.mem_top, true_and, mem_fixV]
    constructor
    · intro hv x hx
      exact hv ⟨x, hx⟩
    · intro hv a
      exact hv a a.2
  have h2 : XMod.commOf (↥X) (⊤ : Subgroup V) = commV X := by
    unfold XMod.commOf commV
    congr 1
    ext w
    constructor
    · rintro ⟨a, l, -, rfl⟩
      exact ⟨a, a.2, l, rfl⟩
    · rintro ⟨x, hx, v, rfl⟩
      exact ⟨⟨x, hx⟩, v, Subgroup.mem_top _, rfl⟩
  rwa [h1, h2] at h

private theorem conjAct_coe' (V : Subgroup G) (g : Subgroup.normalizer (V : Set G)) (x : V) :
    ((conjAct V g x : V) : G) = g * x * (g : G)⁻¹ :=
  CFSG.Quasithin.AutOn.coe_conjAct_apply V g x

variable [Finite G]

theorem eq_one_of_mem_commutator_of_fixed {U P : Subgroup G} (hU : IsElemAbelian 2 U)
    (hPU : P ≤ Subgroup.normalizer (U : Set G))
    (hodd : Odd ((P ⊓ Subgroup.centralizer (U : Set G)).relIndex P)) {z : G} (hzU : z ∈ U)
    (hzP : z ∈ ⁅U, P⁆) (hfix : ∀ p ∈ P, p * z * p⁻¹ = z) : z = 1 := by
  let _ : CommGroup ↥U := commGroupOfElemAbelian hU
  have hcard : Odd (Nat.card (autOn P U)) := by rw [card_autOn_eq_relIndex hPU]; exact hodd
  have hsq : ∀ v : ↥U, v ^ 2 = 1 := fun v => Subtype.ext (by simpa [sq] using hU.2 v v.2)
  have hc := isCompl_fixV_commV_of_odd (autOn P U) hcard hsq
  have hz1 : (⟨z, hzU⟩ : ↥U) ∈ fixV (autOn P U) := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := hx
    apply Subtype.ext
    rw [conjAct_coe']
    exact hfix a (Subgroup.mem_subgroupOf.mp ha)
  have key : ∀ w ∈ ⁅U, P⁆, ∃ hw : w ∈ U, (⟨w, hw⟩ : ↥U) ∈ commV (autOn P U) := by
    intro w hw
    induction hw using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨u, hu, p, hp, rfl⟩ := hx
      have hpN := hPU hp
      have hu' : p * u⁻¹ * p⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp hpN u⁻¹).mp (U.inv_mem hu)
      have hxU : ⁅u, p⁆ ∈ U := by
        have : ⁅u, p⁆ = u * (p * u⁻¹ * p⁻¹) := by simp only [commutatorElement_def]; group
        rw [this]; exact U.mul_mem hu hu'
      refine ⟨hxU, ?_⟩
      let g : Subgroup.normalizer (U : Set G) := ⟨p, hpN⟩
      have hgmem : conjAct U g ∈ autOn P U := ⟨g, Subgroup.mem_subgroupOf.mpr hp, rfl⟩
      refine Subgroup.subset_closure ⟨conjAct U g, hgmem, ⟨u⁻¹, U.inv_mem hu⟩, ?_⟩
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
      rw [conjAct_coe']
      have hcomm : (p * u⁻¹ * p⁻¹) * u = u * (p * u⁻¹ * p⁻¹) := (setLike_mul_comm hu' hu : _)
      show p * u⁻¹ * p⁻¹ * u = _
      rw [hcomm]
      simp only [commutatorElement_def]; group
    | one => exact ⟨U.one_mem, (commV (autOn P U)).one_mem⟩
    | mul x y _ _ ihx ihy =>
      obtain ⟨hx, hx'⟩ := ihx
      obtain ⟨hy, hy'⟩ := ihy
      exact ⟨U.mul_mem hx hy, (commV (autOn P U)).mul_mem hx' hy'⟩
    | inv x _ ihx =>
      obtain ⟨hx, hx'⟩ := ihx
      exact ⟨U.inv_mem hx, (commV (autOn P U)).inv_mem hx'⟩
  obtain ⟨hzU', hz2⟩ := key z hzP
  have := Subgroup.disjoint_def.mp hc.1 hz1 hz2
  exact congrArg Subtype.val this

end CFSG.Quasithin
