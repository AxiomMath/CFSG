module

public import CFSG.RankThree.PartTwo.Sec21.FF81GL6Red
public import CFSG.RankThree.PartTwo.Sec21.FF81GL6B3
public import CFSG.RankThree.PartTwo.Sec21.FF81GL6Syl
public import CFSG.RankThree.PartTwo.Sec21.FF81GL6Norm
public import CFSG.RankThree.PartTwo.Sec21.FF81GL6Sp
public import CFSG.RankThree.PartTwo.Sec21.FF81GL6Gen
public import CFSG.RankThree.PartTwo.Sec21.FF81GL6U0
public import CFSG.RankThree.PartTwo.Sec21.FF81GL6Sig
public import CFSG.RankThree.PartTwo.Sec21.FF81GL6Forms

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.GL6

private theorem sig_le_sp0 (i : Fin 3) : Sig i ≤ Sp0 := fun _ h => h.1

theorem sig0_sup_sig (j : Fin 3) (hj : j ≠ 2) : Sig0 ⊔ Sig j = Sp0 := by
  refine le_antisymm (sup_le (sig_le_sp0 2) (sig_le_sp0 j)) ?_
  rw [sp0_eq_closure_tvG, Subgroup.closure_le]
  rintro _ ⟨v, rfl⟩
  exact mem_sig_sup_of_tvM' j hj v (tvG v) rfl

theorem eq_sp0
    (X : Subgroup G6) (hX : X ⊓ Subgroup.centralizer {u0} = K0) (h81 : 81 ∣ Nat.card X) :
    X = Sp0 := by
  obtain ⟨σ, hσX, hσN, h1, h2⟩ :=
    exists_sigma_of (card_K0 card_sig0) card_B3 B3_le_K0 orderOf_u0 X hX h81
  have hK0 : K0 ≤ X := hX ▸ inf_le_left
  have hS0 : Sig0 ≤ X := le_trans le_sup_left hK0
  have hconj : ∀ H : Subgroup G6, H ≤ X → H.map (MulAut.conj σ).toMonoidHom ≤ X := by
    rintro H hH _ ⟨x, hx, rfl⟩
    exact X.mul_mem (X.mul_mem hσX (hH hx)) (X.inv_mem hσX)
  have hSj : ∃ j : Fin 3, j ≠ 2 ∧ Sig j ≤ X := by
    rcases map_sig0_of_mem_normalizer hσN h1 h2 with h | h
    · exact ⟨0, by decide, h ▸ hconj _ hS0⟩
    · exact ⟨1, by decide, h ▸ hconj _ hS0⟩
  obtain ⟨j, hj, hjX⟩ := hSj
  exact eq_sp0_of_le X hX K0_le_sp0 (sig0_sup_sig j hj ▸ sup_le hS0 hjX)

theorem kf_sp6GL6Cen :
    KF_Sp6GL6Cen :=
  kf_sp6GL6Cen_of exists_conj_u0 (fun φ hφ hC => exists_conj_sig0 φ hφ hC) eq_sp0
    card_sp0 sp0_eq_closure_transvections sp0_irreducible

end CFSG.RankThree.PartTwo.Sec21.FF81.GL6
