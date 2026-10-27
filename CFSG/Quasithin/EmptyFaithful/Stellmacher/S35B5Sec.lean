module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Stmt
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std3

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.B5

open S35.Std

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem Wb_le_Kb (hS : Sit H M S) (β : Geo H M) : Wb β ≤ Kb β := by
  refine le_inf (Wb_le_Qv hS β) ?_
  have h := comm_Vn_Wb hS β
  rw [Subgroup.commutator_comm] at h
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h

theorem sq_mem_of_comm (hS : Sit H M S) {β : Geo H M}
    (hcomm : ∀ x ∈ Wb β, ∀ y ∈ Wb β, x * y * x⁻¹ * y⁻¹ ∈ Vn β) :
    ∀ x ∈ Wb β, x ^ 2 ∈ Vn β := by
  let T : Subgroup G :=
    { carrier := {x | x ∈ Wb β ∧ x ^ 2 ∈ Vn β}
      one_mem' := ⟨(Wb β).one_mem, by simp⟩
      mul_mem' := fun {a b} ha hb => by
        refine ⟨(Wb β).mul_mem ha.1 hb.1, ?_⟩
        have hc := hcomm a ha.1 b hb.1
        have hbs : b ∈ stab β := pCoreOf_le 2 _ (Wb_le_Qv hS β hb.1)
        have hn := Subgroup.mem_normalizer_iff.mp (Vn_normal β hbs)
        have e : (a * b) ^ 2 = (a * b * a⁻¹ * b⁻¹) * (b * a ^ 2 * b⁻¹) * b ^ 2 := by
          simp only [pow_two]; group
        rw [e]
        exact (Vn β).mul_mem ((Vn β).mul_mem hc ((hn _).mp ha.2)) hb.2
      inv_mem' := fun {a} ha => by
        refine ⟨(Wb β).inv_mem ha.1, ?_⟩
        have : a⁻¹ ^ 2 = (a ^ 2)⁻¹ := by simp [pow_two, mul_inv_rev]
        rw [this]
        exact (Vn β).inv_mem ha.2 }
  have hle : Wb β ≤ T := Wb_le fun ρ hρ x hx =>
    ⟨Vn_le_Wb hρ hx, by
      rw [isElemAbelian_pow_eq_one (Vn_isElemAbelian hS ρ) hx]
      exact (Vn β).one_mem⟩
  exact fun x hx => (hle hx).2

theorem wb_isSec (hS : Sit H M S) (h15c : Claim15c H M) :
    ∀ β : Geo H M, vtype β = false → IsSec (stab β) (Vn β) (Wb β) := by
  intro β hβ
  have hcomm : ∀ x ∈ Wb β, ∀ y ∈ Wb β, x * y * x⁻¹ * y⁻¹ ∈ Vn β := fun x hx y hy =>
    h15c β hβ (Subgroup.commutator_mem_commutator hx (Wb_le_Kb hS β hy))
  exact ⟨Vn_le_Wb_self hS hβ, Wb_normal β, Vn_normal β, hcomm, sq_mem_of_comm hS hcomm⟩

end S35.B5

end F53.Stellmacher

end CFSG.Quasithin
