module

public import CFSG.Quasithin.AppendixH.H9.ModelBasic

public section

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open

private theorem card_GL_four_two : Nat.card (GL (Fin 4) (ZMod 2)) = 20160 := by
  rw [Matrix.card_GL_field 4]
  simp [Fin.prod_univ_succ, ZMod.card]

private theorem factorization_card_GL_four_two :
    (Nat.card (GL (Fin 4) (ZMod 2))).factorization 2 = 6 := by
  rw [card_GL_four_two, Nat.factorization_def _ Nat.prime_two]
  have h : (20160 : ℕ) = 2 ^ 6 * 315 := by norm_num
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [h, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by norm_num), add_zero]

theorem inf_stabSub_V1n_eq_inf_Lg {T : Subgroup (MulAut (PairN 4))}
    (hT : IsSylowIn 2 T (Mg 4)) : T ⊓ stabSub (V1n 4) = T ⊓ Lg 4 := by
  have h := Mg_inf_stabSub_V1n (n := 4) (by norm_num)
  ext x
  refine ⟨fun hx => ⟨hx.1, ?_⟩, fun hx => ⟨hx.1, ?_⟩⟩
  · have hx' : x ∈ Mg 4 ⊓ stabSub (V1n 4) := ⟨hT.le hx.1, hx.2⟩
    rwa [h] at hx'
  · have hx' : x ∈ Mg 4 ⊓ stabSub (V1n 4) := by
      rw [h]
      exact hx.2
    exact hx'.2

theorem card_inf_stabSub_V1n_of_isSylowIn {T : Subgroup (MulAut (PairN 4))}
    (hT : IsSylowIn 2 T (Mg 4)) : Nat.card ↥(T ⊓ stabSub (V1n 4)) = 64 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnorm : ((Lg 4).subgroupOf (Mg 4)).Normal :=
    Subgroup.normal_of_index_eq_two (relIndex_Lg_Mg (by norm_num))
  have h := hT.inf_normal Lg_le_Mg hnorm
  rw [inf_stabSub_V1n_eq_inf_Lg hT, h.card_eq, card_Lg, factorization_card_GL_four_two]
  norm_num

end CFSG.ASVolI.ChH
