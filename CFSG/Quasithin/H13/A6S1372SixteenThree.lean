module

public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B42A57E7
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeKVocab

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative

namespace A6Three

variable {V W : Type} [CommGroup V] [CommGroup W] {p : V →* W} {X : Subgroup (MulAut V)}
  {Y : Subgroup (MulAut W)}

theorem map_commV (hp : Function.Surjective p)
    (hXY : ∀ x ∈ X, ∃ y ∈ Y, ∀ v, p (x v) = y (p v))
    (hYX : ∀ y ∈ Y, ∃ x ∈ X, ∀ v, p (x v) = y (p v)) : (commV X).map p = commV Y := by
  refine le_antisymm ?_ ?_
  · rw [Subgroup.map_le_iff_le_comap, commV, Subgroup.closure_le]
    rintro _ ⟨x, hx, v, rfl⟩
    obtain ⟨y, hy, hxy⟩ := hXY x hx
    rw [SetLike.mem_coe, Subgroup.mem_comap, map_mul, map_inv, hxy]
    exact Subgroup.subset_closure ⟨y, hy, p v, rfl⟩
  · rw [commV, Subgroup.closure_le]
    rintro _ ⟨y, hy, w, rfl⟩
    obtain ⟨v, rfl⟩ := hp w
    obtain ⟨x, hx, hxy⟩ := hYX y hy
    refine ⟨x v * v⁻¹, Subgroup.subset_closure ⟨x, hx, v, rfl⟩, ?_⟩
    rw [map_mul, map_inv, hxy]

theorem mem_fixV_of_map [Group.IsPerfect ↥X] (hXY : ∀ x ∈ X, ∃ y ∈ Y, ∀ v, p (x v) = y (p v))
    (hker : ∀ x ∈ X, ∀ v, p v = 1 → x v = v) {c : V} (hc : p c ∈ fixV Y) : c ∈ fixV X := by
  have hδ : ∀ x ∈ X, x c * c⁻¹ ∈ p.ker := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hXY x hx
    rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, hc y hy, mul_inv_cancel]
  let δ : ↥X →* ↥p.ker :=
    { toFun := fun x => ⟨(x : MulAut V) c * c⁻¹, hδ x x.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => by
        apply Subtype.ext
        show ((a * b : ↥X) : MulAut V) c * c⁻¹ = ((a : MulAut V) c * c⁻¹) * ((b : MulAut V) c * c⁻¹)
        have h1 := hker a a.2 _ (hδ b b.2)
        have e : ((a * b : ↥X) : MulAut V) c * c⁻¹ =
            (a : MulAut V) ((b : MulAut V) c * c⁻¹) * ((a : MulAut V) c * c⁻¹) := by
          rw [Subgroup.coe_mul, MulAut.mul_apply, map_mul, map_inv]
          group
        rw [e, h1]
        exact mul_comm _ _ }
  intro x hx
  have hmem : (⟨x, hx⟩ : ↥X) ∈ δ.ker :=
    Abelianization.commutator_subset_ker δ
      (by rw [Group.IsPerfect.commutator_eq_top]; exact Subgroup.mem_top _)
  rw [MonoidHom.mem_ker] at hmem
  have h1 : x c * c⁻¹ = 1 := congrArg Subtype.val hmem
  exact mul_inv_eq_one.1 h1

end A6Three

end CFSG.Quasithin.H13.A6
