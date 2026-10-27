module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80PFix
public import CFSG.Quasithin.EmptyFaithful.A38c15Sl3

public section

namespace CFSG.Quasithin.E2P.Asc80

open Matrix CFSG.Quasithin.A38c15
open scoped MatrixGroups

theorem exists_fixed_vector_three {U : Subgroup SL(3, ZMod 3)} (hU : IsPGroup 3 U) :
    ∃ w : Fin 3 → ZMod 3, w ≠ 0 ∧ ∀ u ∈ U, (u : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ w = w := by
  obtain ⟨w, hw0, hw⟩ := exists_fixed_ne_zero (V := Fin 3 → ZMod 3) (p := 3) (U := U) hU
    (by rw [Nat.card_eq_fintype_card]; simp)
  exact ⟨w, hw0, fun u hu => hw ⟨u, hu⟩⟩

theorem false_of_normal_three_group {Y : Subgroup SL(3, ZMod 3)} (hirr : IsIrreducibleSL3 Y)
    {U : Subgroup SL(3, ZMod 3)} (hU : IsPGroup 3 U) (hnorm : ∀ y ∈ Y, ∀ u ∈ U, y * u * y⁻¹ ∈ U)
    (hne : U ≠ ⊥) : False := by
  obtain ⟨w, hw0, hw⟩ := exists_fixed_vector_three hU
  let W : Submodule (ZMod 3) (Fin 3 → ZMod 3) :=
    { carrier := {v | ∀ u ∈ U, (u : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ v = v}
      add_mem' := fun {a b} ha hb u hu => by rw [Matrix.mulVec_add, ha u hu, hb u hu]
      zero_mem' := fun u _ => Matrix.mulVec_zero _
      smul_mem' := fun c a ha u hu => by rw [Matrix.mulVec_smul, ha u hu] }
  have hinv : ∀ g ∈ Y, ∀ v ∈ W, (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ v ∈ W := by
    intro g hg v hv u hu
    have hu' : g⁻¹ * u * g ∈ U := by simpa using hnorm g⁻¹ (Y.inv_mem hg) u hu
    have h1 : (g⁻¹ * u * g) • v = v := hv _ hu'
    have h2 : u • (g • v) = g • v := by
      calc u • (g • v) = (u * g) • v := (mul_smul u g v).symm
        _ = (g * (g⁻¹ * u * g)) • v := by congr 1; group
        _ = g • ((g⁻¹ * u * g) • v) := mul_smul g _ v
        _ = g • v := by rw [h1]
    exact h2
  rcases hirr W hinv with hbot | htop
  · apply hw0
    have hwW : w ∈ W := fun u hu => hw u hu
    rw [hbot] at hwW
    simpa using hwW
  · apply hne
    rw [eq_bot_iff]
    intro u hu
    have hall : ∀ v : Fin 3 → ZMod 3, (u : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ v = v := fun v => by
      have hv : v ∈ W := by rw [htop]; trivial
      exact hv u hu
    refine Subgroup.mem_bot.mpr (Subtype.ext ?_)
    ext i j
    have := congrFun (hall (Pi.single j 1)) i
    simpa [Matrix.mulVec_single_one, Matrix.one_apply, Pi.single_apply, eq_comm] using this

end CFSG.Quasithin.E2P.Asc80
