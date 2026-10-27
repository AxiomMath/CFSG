module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std3
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35C56b

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53
open scoped commutatorElement

namespace S35.C56

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

omit [Finite G] in
theorem conj_mem_of_le_normalizer {X N : Subgroup G} (h : X ≤ Subgroup.normalizer (N : Set G))
    {x a : G} (hx : x ∈ X) (ha : a ∈ N) : x * a * x⁻¹ ∈ N :=
  (Subgroup.mem_normalizer_iff.mp (h hx) a).mp ha

omit [Finite G] in
theorem Qv_le_stab_self (β : Geo H M) : Qv β ≤ stab β := pCoreOf_le 2 _

omit [Finite G] in
theorem Qv_normal (β : Geo H M) : stab β ≤ Subgroup.normalizer (Qv β : Set G) :=
  le_normalizer_pCoreOf 2 _

omit [Finite G] in
theorem Lr_le_stab (β : Geo H M) : Lr β ≤ stab β := oTwoRes_le _

omit [Finite G] in
theorem Lr_normal (β : Geo H M) : stab β ≤ Subgroup.normalizer (Lr β : Set G) :=
  le_normalizer_oTwoRes _

theorem Vn_comm (hS : Sit H M S) (β : Geo H M) {u w : G} (hu : u ∈ Vn β) (hw : w ∈ Vn β) :
    u * w = w * u :=
  congrArg Subtype.val ((Std.Vn_isElemAbelian hS β).1.is_comm.comm (⟨u, hu⟩ : Vn β) ⟨w, hw⟩)

theorem Vn_mul_self (hS : Sit H M S) (β : Geo H M) {u : G} (hu : u ∈ Vn β) : u * u = 1 := by
  rw [← pow_two]
  exact (Std.Vn_isElemAbelian hS β).2 u hu

omit [Finite G] in
theorem Q_conj (β : Geo H M) {x q : G} (hx : x ∈ stab β) (hq : q ∈ ⁅Qv β, Lr β⁆) :
    x * q * x⁻¹ ∈ ⁅Qv β, Lr β⁆ :=
  conj_mem_commutator (fun _ ha => conj_mem_of_le_normalizer (Qv_normal β) hx ha)
    (fun _ ha => conj_mem_of_le_normalizer (Lr_normal β) hx ha) q hq

omit [Finite G] in
theorem Q_le_Qv (β : Geo H M) : ⁅Qv β, Lr β⁆ ≤ Qv β := by
  have := Subgroup.le_normalizer_iff_commutator_le_right.mp
    ((Lr_le_stab β).trans (Qv_normal β))
  rw [Subgroup.commutator_comm] at this
  exact this

theorem comm_mem_Vn (hS : Sit H M S) {β : Geo H M} {E B : Subgroup G}
    (hE : stab β ≤ Subgroup.normalizer (E : Set G)) (hEW : E ≤ Wb β) (hEL : ⁅E, Lr β⁆ ≤ Vn β)
    (hBE : B ≤ E) {b q : G} (hb : b ∈ B) (hq : q ∈ ⁅Qv β, Lr β⁆) : ⁅b, q⁆ ∈ Vn β := by
  have hBs : B ≤ stab β := hBE.trans (hEW.trans ((Std.Wb_le_Qv hS β).trans (Qv_le_stab_self β)))
  have h := commutator_commutator_le (X := Qv β) (Y := Lr β) (Z := B) (N := Vn β) (E := E)
    ((Qv_le_stab_self β).trans (Std.Vn_normal β)) ((Lr_le_stab β).trans (Std.Vn_normal β))
    (hBs.trans (Std.Vn_normal β)) ((Qv_le_stab_self β).trans hE) hBE hEL
  have h1 : ⁅q, b⁆ ∈ Vn β := h (Subgroup.commutator_mem_commutator hq hb)
  rw [← commutatorElement_inv]
  exact (Vn β).inv_mem h1

theorem normalizer_commSpan (hS : Sit H M S) {β : Geo H M} (hβ : vtype β = false) {E B : Subgroup G}
    (hE : stab β ≤ Subgroup.normalizer (E : Set G)) (hEW : E ≤ Wb β) (hEL : ⁅E, Lr β⁆ ≤ Vn β)
    (hBE : B ≤ E) {b : G} (hb : b ∈ B) :
    Lr β ≤ Subgroup.normalizer (commSpan (Zv β) ⁅Qv β, Lr β⁆ b : Set G) := by
  have key : ∀ x ∈ Lr β, ∀ u ∈ commSpan (Zv β) ⁅Qv β, Lr β⁆ b,
      x * u * x⁻¹ ∈ commSpan (Zv β) ⁅Qv β, Lr β⁆ b := by
    intro x hx
    refine conj_mem_commSpan (V := Vn β) (fun u hu w hw => Vn_comm hS β hu hw) ?_
      (fun q hq => Q_conj β (Lr_le_stab β hx) hq) ?_ ?_
      (fun q hq => comm_mem_Vn hS hE hEW hEL hBE hb hq)
    · intro z hz
      have hc := (Std.Zv_central hS hβ) hz
      have : x * z = z * x := (Subgroup.mem_centralizer_iff.mp hc.2) x (Lr_le_stab β hx)
      rwa [this, mul_assoc, mul_inv_cancel, mul_one]
    · have h1 : ⁅x, b⁆ ∈ ⁅Lr β, E⁆ := Subgroup.commutator_mem_commutator hx (hBE hb)
      rw [Subgroup.commutator_comm] at h1
      exact hEL h1
    · intro v hv q hq
      exact S34.comm_Vn_Qv_le hS.glob hβ (Subgroup.commutator_mem_commutator hv (Q_le_Qv β hq))
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro u
  refine ⟨key x hx u, fun hu => ?_⟩
  have := key x⁻¹ ((Lr β).inv_mem hx) _ hu
  simpa [mul_assoc] using this

end S35.C56

end F53.Stellmacher

end CFSG.Quasithin
