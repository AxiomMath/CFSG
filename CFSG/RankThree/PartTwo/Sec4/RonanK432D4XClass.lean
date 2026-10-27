module

public import CFSG.RankThree.PartTwo.Sec4.RonanK423D4Aux

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG.RankThree.PartTwo.Sec11 CFSG.RankThree.PartTwo.Sec19
open CFSG.RankThree.PartTwo.Sec4.RonanK423.D4 (layer_conj_nonempty layer_eq_Asub_of_mem_Bsub)

section Class


variable {n : ℕ} {X : Type} [Field X] [Finite X] {σ : X ≃+* X}

theorem center_Asub_eq_bot (P : D4Par n X σ) : Subgroup.center ↥(Asub σ) = ⊥ := by
  haveI := P.charP
  have h := Subgroup.map_center_eq (asubEquiv P)
  rw [CFSG.RankThree.PartOne.CTP.center_sl2_eq_bot, Subgroup.map_bot] at h
  exact h.symm

theorem isClassX_of_layer_center_ne_one (P : D4Par n X σ) {x : C0 σ} (hx3 : x ^ 3 = 1)
    (hx1 : x ≠ 1)
    (hZ : Nat.card ↥(Subgroup.center ↥⁅Subgroup.centralizer ({x} : Set (C0 σ)),
      Subgroup.centralizer ({x} : Set (C0 σ))⁆) ≠ 1) :
    IsClassX σ x := by
  rcases three_conj_dichotomy σ n P.one_le P.card P.frob hx3 hx1 with hX | ⟨g, hg⟩
  · exact hX
  · exfalso
    have hz3 : (g * x * g⁻¹) ^ 3 = 1 := by rw [conj_pow, hx3]; group
    have hz1 : g * x * g⁻¹ ≠ 1 := fun h => hx1 (by
      have := congrArg (fun y => g⁻¹ * y * g) h
      have e : g⁻¹ * (g * x * g⁻¹) * g = x := by group
      simp only [e] at this
      simpa using this)
    have hA := layer_eq_Asub_of_mem_Bsub P hg hz3 hz1
    obtain ⟨e⟩ := layer_conj_nonempty g x
    apply hZ
    rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv, hA, center_Asub_eq_bot P]
    simp

end Class

end CFSG.RankThree.PartTwo.Sec4.RonanK432
