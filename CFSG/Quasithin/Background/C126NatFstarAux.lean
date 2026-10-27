module

public import CFSG.Quasithin.Background.C126NatSL2
public import CFSG.Quasithin.Background.B2FactorizationBridge
public import CFSG.Quasithin.Background.C1GNDefs
public import CFSG.Quasithin.Background.G6PGroup

public section

namespace CFSG.Quasithin.C126.Nat

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement

variable {G : Type} [Group G]

theorem fstarPre_eq_of_generalizedFitting_eq_top {P V : Subgroup G}
    (hPN : P ≤ Subgroup.normalizer (V : Set G))
    (h : CFSG.generalizedFitting ↥(autOn P V) = ⊤) : fstarPre P V = P := by
  apply le_antisymm inf_le_left
  intro g hg
  refine Subgroup.mem_inf.2 ⟨hg, ⟨g, hPN hg⟩, ?_, rfl⟩
  refine Subgroup.mem_map.2 ⟨⟨conjAct V ⟨g, hPN hg⟩,
    ⟨⟨g, hPN hg⟩, Subgroup.mem_subgroupOf.2 hg, rfl⟩⟩, ?_, rfl⟩
  rw [h]
  exact Subgroup.mem_top _

section Residual

variable [Finite G] {P V : Subgroup G} (hV : IsElemAbelian 2 V)
  (hPN : P ≤ Subgroup.normalizer (V : Set G))

omit [Finite G] in
include hPN in
theorem le_normalizer_autI_twoResidual :
    autI hV P ≤ Subgroup.normalizer
      (autI hV (twoResidual P) : Set (MulAut (IntMod V hV))) := by
  have hkey : ∀ (g : G) (hg : g ∈ P), ∀ x ∈ autI hV (twoResidual P),
      convI hV ⟨g, hPN hg⟩ * x * (convI hV ⟨g, hPN hg⟩)⁻¹ ∈ autI hV (twoResidual P) := by
    intro g hg x hx
    obtain ⟨n, hn, rfl⟩ := (mem_autI hV).1 hx
    have hgn : g * (n : G) * g⁻¹ ∈ twoResidual P :=
      (Subgroup.mem_normalizer_iff.1 (le_normalizer_twoResidual P hg) _).1 hn
    have hgnN : g * (n : G) * g⁻¹ ∈ Subgroup.normalizer (V : Set G) :=
      hPN (P.mul_mem (P.mul_mem hg (twoResidual_le P hn)) (P.inv_mem hg))
    have := convI_mem_autI hV hgn hgnN
    convert this using 1
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  intro φ hφ
  obtain ⟨g, hgP, rfl⟩ := (mem_autI hV).1 hφ
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => hkey g hgP x hx, fun hx => ?_⟩
  have hginv : convI hV ⟨(g : G)⁻¹, hPN (P.inv_mem hgP)⟩ = (convI hV g)⁻¹ := by
    rw [← map_inv]
    rfl
  have := hkey (g : G)⁻¹ (P.inv_mem hgP) _ hx
  rw [hginv] at this
  convert this using 1
  group

include hPN in
theorem isTwoQuotient_autI_twoResidual :
    ∀ y ∈ autI hV P, ∃ k : ℕ, y ^ 2 ^ k ∈ autI hV (twoResidual P) := by
  intro y hy
  obtain ⟨g, hgP, rfl⟩ := (mem_autI hV).1 hy
  obtain ⟨k, hk⟩ := twoResidual_isTwoQuotient P g hgP
  refine ⟨k, ?_⟩
  have hgk : (g : G) ^ 2 ^ k ∈ Subgroup.normalizer (V : Set G) := Subgroup.pow_mem _ (hPN hgP) _
  have := convI_mem_autI hV hk hgk
  convert this using 1
  rw [← map_pow]
  rfl

include hPN in
theorem autI_twoResidual_eq_of_perfect {L : Subgroup (MulAut (IntMod V hV))}
    (hL : autI hV P = L) (hperf : ⁅L, L⁆ = L) : autI hV (twoResidual P) = autI hV P := by
  apply le_antisymm (autI_mono hV (twoResidual_le P))
  rw [hL]
  have hN'L : autI hV (twoResidual P) ≤ L := hL ▸ autI_mono hV (twoResidual_le P)
  have := twoResidual_le_of_isTwoQuotient hN'L (hL ▸ le_normalizer_autI_twoResidual hV hPN)
    (hL ▸ isTwoQuotient_autI_twoResidual hV hPN)
  rw [twoResidual_eq_of_perfect hperf] at this
  exact this

include hPN in
omit [Finite G] in
theorem exists_mul_mem_twoResidual (hN : autI hV (twoResidual P) = autI hV P) {g : G} (hg : g ∈ P) :
    ∃ o ∈ twoResidual P, g * o⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
  have hmem : convI hV ⟨g, hPN hg⟩ ∈ autI hV (twoResidual P) := hN ▸ convI_mem_autI hV hg (hPN hg)
  obtain ⟨o, ho, hconv⟩ := (mem_autI hV).1 hmem
  refine ⟨o, ho, ?_⟩
  have h1 : convI hV (⟨g, hPN hg⟩ * o⁻¹) = 1 := by rw [map_mul, map_inv, hconv, mul_inv_cancel]
  exact (convI_eq_one_iff hV _).1 h1

end Residual

section Incl

variable {P V : Subgroup G} (hV : IsElemAbelian 2 V)
  (hPN : P ≤ Subgroup.normalizer (V : Set G))

include hPN in
theorem exists_incl {L : Subgroup (MulAut (IntMod V hV))} (hL : autI hV P = L) :
    ∃ incl : ↥⁅V, P⁆ →* ↥(commV L),
      (∀ w, (incl w : IntMod V hV).val = (w : G)) ∧ Function.Surjective incl := by
  have hW1V : ⁅V, P⁆ ≤ V := Subgroup.le_normalizer_iff_commutator_le_left.mp hPN
  have hW1sub : ∀ x ∈ ⁅V, P⁆, ∃ hxV : x ∈ V, IntMod.mk hV ⟨x, hxV⟩ ∈ commV L := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨v, hv, k, hk, rfl⟩ := hx
      have hxV : ⁅v, k⁆ ∈ V := hW1V (Subgroup.commutator_mem_commutator hv hk)
      refine ⟨hxV, ?_⟩
      have hσ : convI hV ⟨k, hPN hk⟩ ∈ L := hL ▸ convI_mem_autI hV hk (hPN hk)
      have h2 := (commV L).inv_mem (G6.mem_commV_of_mem hσ (IntMod.mk hV ⟨v, hv⟩))
      have heq : IntMod.mk hV ⟨⁅v, k⁆, hxV⟩ =
          ((convI hV ⟨k, hPN hk⟩ (IntMod.mk hV ⟨v, hv⟩) * (IntMod.mk hV ⟨v, hv⟩)⁻¹))⁻¹ := by
        apply IntMod.val_injective
        show ⁅v, k⁆ = _
        rw [IntMod.val_inv, IntMod.val_mul, IntMod.val_inv, convI_apply_val]
        show ⁅v, k⁆ = (k * v * k⁻¹ * v⁻¹)⁻¹
        simp only [commutatorElement_def]
        group
      rw [heq]
      exact h2
    | one =>
      refine ⟨V.one_mem, ?_⟩
      have : IntMod.mk hV ⟨(1 : G), V.one_mem⟩ = 1 := IntMod.val_injective rfl
      rw [this]
      exact (commV L).one_mem
    | mul x y _ _ ihx ihy =>
      obtain ⟨hxV, hx⟩ := ihx
      obtain ⟨hyV, hy⟩ := ihy
      refine ⟨V.mul_mem hxV hyV, ?_⟩
      have : IntMod.mk hV ⟨x * y, V.mul_mem hxV hyV⟩ =
          IntMod.mk hV ⟨x, hxV⟩ * IntMod.mk hV ⟨y, hyV⟩ := IntMod.val_injective rfl
      rw [this]
      exact (commV L).mul_mem hx hy
    | inv x _ ih =>
      obtain ⟨hxV, hx⟩ := ih
      refine ⟨V.inv_mem hxV, ?_⟩
      have : IntMod.mk hV ⟨x⁻¹, V.inv_mem hxV⟩ = (IntMod.mk hV ⟨x, hxV⟩)⁻¹ :=
        IntMod.val_injective rfl
      rw [this]
      exact (commV L).inv_mem hx
  let incl : ↥⁅V, P⁆ →* ↥(commV L) :=
    { toFun := fun w => ⟨IntMod.mk hV ⟨w.1, (hW1sub w.1 w.2).1⟩, (hW1sub w.1 w.2).2⟩
      map_one' := Subtype.ext (IntMod.val_injective rfl)
      map_mul' := fun a b => Subtype.ext (IntMod.val_injective rfl) }
  refine ⟨incl, fun w => rfl, ?_⟩
  have hle : commV L ≤ ((commV L).subtype.comp incl).range := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨x, hx, v, rfl⟩
    obtain ⟨g, hgP, hconv⟩ := (mem_autI hV).1 (hL ▸ hx)
    have hcomm : ⁅(g : G), v.val⁆ ∈ ⁅V, P⁆ := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator hgP v.val_mem
    refine ⟨⟨⁅(g : G), v.val⁆, hcomm⟩, ?_⟩
    apply IntMod.val_injective
    show ⁅(g : G), v.val⁆ = (x v * v⁻¹).val
    rw [← hconv, IntMod.val_mul, convI_apply_val, IntMod.val_inv]
    simp only [commutatorElement_def]
  intro w
  obtain ⟨u, hu⟩ := hle w.2
  exact ⟨u, Subtype.ext hu⟩

end Incl

end CFSG.Quasithin.C126.Nat
