module

public import CFSG.RankThree.GF2n.Smith81.S81VModelU
public import CFSG.RankThree.GF2n.Smith81.S81VWitt

public section

namespace CFSG.RankThree.GF2n.Smith81.S81V

open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.RankThree.GF2n.Smith81.U6Cube Module Matrix

variable {F : Type} [Field F] [Finite F] [CharP F 2] {σ : F ≃+* F} {b : Fin 3 → Fin 6 → F}
  {K : Type} [Field K] [Finite K]

theorem nine_le_finrank_HermK (hσ : IsUnitaryInvolution σ) (hF : Nat.card F = Nat.card K ^ 2)
    (e₀ : K ≃+* Fσ σ) (hf : Frame σ e3uT0Vec b) : 9 ≤ finrank K (HermK σ e₀) := by
  have h1 : Nat.card K ^ 9 ≤ Nat.card (e3uU0 σ e₀) := u6_U_card (e := e₀) hσ hF
  have h2 : Nat.card (e3uU0 σ e₀) ≤ Nat.card (e3uU0Sub σ) := by
    refine Nat.card_le_card_of_surjective
      (fun g : e3uU0Sub σ => (⟨e3uWact σ e₀ g.1, Subgroup.mem_map_of_mem (e3uWact σ e₀) g.2⟩ :
        e3uU0 σ e₀)) ?_
    intro y
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  have h3 : Nat.card (e3uU0Sub σ) ≤ Nat.card (HermK σ e₀) := by
    rw [e3uU0Sub_eq_ptStab]
    refine Nat.card_le_card_of_surjective
      (fun H : HermK σ e₀ =>
        (⟨uK hσ.invol hf H, uK_mem_PtStab hσ.invol hf H⟩ : PtStab σ (W₀ F))) ?_
    intro g
    obtain ⟨H, hH⟩ := exists_uK_of_mem_PtStab (e₀ := e₀) hσ.invol hf g.2
    exact ⟨H, Subtype.ext hH.symm⟩
  have h4 : Nat.card (HermK σ e₀) = Nat.card K ^ finrank K (HermK σ e₀) :=
    Module.natCard_eq_pow_finrank
  have hK : 1 < Nat.card K := Finite.one_lt_card
  have h := h1.trans (h2.trans h3)
  rw [h4] at h
  exact (Nat.pow_le_pow_iff_right hK).mp h

end CFSG.RankThree.GF2n.Smith81.S81V
