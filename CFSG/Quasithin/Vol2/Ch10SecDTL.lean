module

public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS2
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Open CFSG.Quasithin.ASInputs

section Group

variable {V : Type*} [Group V]

theorem mem_zpowers_iff_of_sq {u x : V} (hu : u ^ 2 = 1) :
    x ∈ Subgroup.zpowers u ↔ x = 1 ∨ x = u := by
  constructor
  · intro hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hk : u ^ k = u ^ (k % 2) := by
      conv_lhs => rw [← Int.emod_add_mul_ediv k 2]
      rw [zpow_add, zpow_mul, zpow_two, ← pow_two, hu, one_zpow, mul_one]
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · left; rw [hk, h, zpow_zero]
    · right; rw [hk, h, zpow_one]
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _

theorem card_zpowers_of_sq {u : V} (hu : u ^ 2 = 1) (hu1 : u ≠ 1) :
    Nat.card (Subgroup.zpowers u) = 2 := by
  rw [Nat.card_zpowers]
  exact orderOf_eq_prime hu hu1

end Group

variable {V : Type} [CommGroup V]

theorem map_conj_transvGroup_le {Gm : Subgroup (MulAut V)} {g : MulAut V} (hg : g ∈ Gm)
    (X : Subgroup V) :
    (transvGroup Gm X).map (MulAut.conj g).toMonoidHom ≤ transvGroup Gm (X.map g.toMonoidHom) := by
  unfold transvGroup
  rw [MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨h, ⟨hh, hhX⟩, rfl⟩
  refine Subgroup.subset_closure ⟨Gm.mul_mem (Gm.mul_mem hg hh) (Gm.inv_mem hg), fun v => ?_⟩
  have e : ((MulAut.conj g).toMonoidHom h) v * v⁻¹ = g (h (g⁻¹ v) * (g⁻¹ v)⁻¹) := by
    show g (h (g⁻¹ v)) * v⁻¹ = g (h (g⁻¹ v) * (g⁻¹ v)⁻¹)
    rw [map_mul, map_inv, MulAut.apply_inv_self]
  rw [e]
  exact Subgroup.mem_map_of_mem g.toMonoidHom (hhX _)

theorem card_transvGroup_le [Finite V] {Gm : Subgroup (MulAut V)} {g : MulAut V} (hg : g ∈ Gm)
    (X : Subgroup V) :
    Nat.card (transvGroup Gm X) ≤ Nat.card (transvGroup Gm (X.map g.toMonoidHom)) := by
  have : Finite (MulAut V) :=
    Finite.of_injective (fun g : MulAut V => (g : V → V)) DFunLike.coe_injective
  rw [← Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
    (MulEquiv.injective _)]
  exact Subgroup.card_le_of_le (map_conj_transvGroup_le hg X)

theorem transvGroup_le (Gm : Subgroup (MulAut V)) (X : Subgroup V) : transvGroup Gm X ≤ Gm := by
  unfold transvGroup
  rw [Subgroup.closure_le]
  exact fun _ h => h.1

theorem map_zpowers_mulAut (g : MulAut V) (u : V) :
    (Subgroup.zpowers u).map g.toMonoidHom = Subgroup.zpowers (g u) :=
  MonoidHom.map_zpowers _ u

end CFSG.Quasithin.Vol2.Ch10.SecD
