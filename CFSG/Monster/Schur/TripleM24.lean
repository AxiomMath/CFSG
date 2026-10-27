module

public import CFSG.Monster.Schur.TripleM12InM24
public import CFSG.Monster.Schur.TripleDefs
public import CFSG.Monster.Schur.TripleM12

public section

namespace CFSG.Monster.Schur

theorem noPerfectTripleCover_nativeM24 :
    NoPerfectTripleCover CFSG.Blueprint.NativeSporadic.M24 := by
  intro E _ π hπ hperf hk
  have hE : Nat.card E = Nat.card ↥CFSG.Blueprint.NativeSporadic.M24 * 3 := by
    rw [card_eq_card_mul_card_ker3 π hπ, hk]
  have : Finite E := Nat.finite_of_card_ne_zero (by
    rw [hE]
    exact Nat.mul_ne_zero Nat.card_pos.ne' (by norm_num))
  have hzc := ker_le_center_of_perfect π hk
  have hrel := m12_relators
  obtain ⟨S, hS1, hS2⟩ := exists_complement_m12 π hπ hk hzc m12h1 m12h2
    (hrel _ (by simp)) (hrel _ (by simp)) (hrel _ (by simp)) bound_m12Rels (by rw [m12_card])
  exact false_of_complement_sylow π hπ hk S hS1 (by rw [hS2]; exact m12_index)

end CFSG.Monster.Schur
