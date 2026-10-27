module

public import CFSG.LieType.BorelTits.UnitaryForm
public import CFSG.LieType.Universal.Unitary.Basic

public section

namespace CFSG.Timmesfeld.LieEmbed

open Matrix CFSG.LieType.Universal CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

section Count

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}

theorem card_traceZero (hF : Nat.card F = (2 ^ f) ^ 2) :
    Nat.card (traceZero (unitaryInvolution F 2 f)) = 2 ^ f := by
  set σ := unitaryInvolution F 2 f with hσdef
  let T : F →+ F :=
    { toFun := fun c => c + σ c
      map_zero' := by simp
      map_add' := fun a b => by rw [map_add]; ring }
  have hker : T.ker = traceZero σ := by
    ext c
    rfl
  have hrange : T.range = traceZero σ := by
    ext a
    rw [AddMonoidHom.mem_range]
    constructor
    · rintro ⟨c, rfl⟩
      show c + σ c + σ (c + σ c) = 0
      rw [map_add, unitaryInvolution_involutive hF, add_comm (σ c) c,
        CharTwo.add_self_eq_zero]
    · intro ha
      have h := (mem_traceZero σ).1 ha
      rw [add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at h
      obtain ⟨c, hc⟩ := exists_add_unitaryInvolution_eq hF h.symm
      exact ⟨c, hc⟩
  have hindex : (traceZero σ).index = Nat.card (traceZero σ) := by
    rw [← hker, AddSubgroup.index_ker, hrange, hker]
  have h1 := AddSubgroup.card_mul_index (traceZero σ)
  rw [hindex, hF, sq] at h1
  exact Nat.mul_self_inj.1 h1

end Count

end CFSG.Timmesfeld.LieEmbed
