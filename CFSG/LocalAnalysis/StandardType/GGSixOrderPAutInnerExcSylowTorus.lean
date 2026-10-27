module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutInnerExcCore
public import CFSG.LieType.SeitzGeneration.ExcTorusSylow
import CFSG.LieType.SeitzGeneration.ExcTorusArith
public import CFSG.LieType.SeitzGeneration.Lift
public import CFSG.LieType.SeitzGeneration.RegimesExcFamilies

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.SeitzGeneration

namespace OrdPInnerExc

theorem ggOrdPToralMax_of_sylowTorus {G : Type} [Group G] [Finite G] {p m : ℕ}
    (h : SylowTorus G p m) : GGOrdPToralMax G p := by
  obtain ⟨T, E, -, hconj, -, hE, hEel, -⟩ := h.exists_torus
  refine ggOrdPToralMax_of_conj_le hEel fun A hA => ?_
  obtain ⟨g, hg⟩ := hconj A (isPGroup_of_isElemAbelian hA)
  refine ⟨g⁻¹, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨t, ht, htx⟩ := Subgroup.mem_map.1 (hg hx)
  have hinv : (MulAut.conj g⁻¹).toMonoidHom x = t := by
    rw [← htx]
    show g⁻¹ * (g * t * g⁻¹) * g⁻¹⁻¹ = t
    group
  rw [hinv]
  refine hE t ht ?_
  have h1 := hA.2 x hx
  have h2 := map_pow (MulAut.conj g⁻¹).toMonoidHom x p
  rw [h1, map_one, hinv] at h2
  exact h2.symm

section Pullback

variable {U C : Type*} [Group U] [Group C] [Finite C] {p : ℕ}

theorem card_lt_of_card_lt_map {ψ : U →* C} (hcop : Nat.Coprime (Nat.card ψ.ker) p) {N : ℕ}
    (h : ∀ A : Subgroup C, IsElemAbelian p A → Nat.card A < N) {E : Subgroup U}
    (hE : IsElemAbelian p E) : Nat.card E < N :=
  (card_le_card_map hcop hE).trans_lt (h _ (isElemAbelian_map ψ hE))

end Pullback

section Order

theorem orderOf_natCast_eq_two_of_dvd_add_one {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : p ∣ q + 1) : orderOf (q : ZMod p) = 2 := by
  have : Fact p.Prime := ⟨hp⟩
  have h0 : ((q + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h
  rw [Nat.cast_add, Nat.cast_one] at h0
  have hq : (q : ZMod p) = -1 := eq_neg_of_add_eq_zero_left h0
  exact (CharP.orderOf_eq_two_iff p hp2).2 hq

theorem prime_le_seven_of_lt_eleven {p : ℕ} (hp : p.Prime) (h : p < 11) : p ≤ 7 := by
  by_contra hlt
  have h8 : 8 ≤ p := by omega
  have h10 : p ≤ 10 := by omega
  interval_cases p <;> exact absurd hp (by norm_num)

end Order

end OrdPInnerExc

end CFSG.StandardType
