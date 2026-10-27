module

public import CFSG.Quasithin.Vol2.Ch9KGFFQR
public import CFSG.Quasithin.Background.F918Z4bPrime
public import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear

public section

namespace CFSG.Quasithin.H13.Ch9.KGFF

open CFSG.Quasithin CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo

theorem autRankLe_psl2_sq {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ 2) : AutRankLe (PSL2 K) 3 := by
  have hodd : IsOddPrimePower (Nat.card K) := ⟨p, 2, hp, hp.odd_of_ne_two hp2, by norm_num, hK⟩
  have hΘ : Nat.card (K ≃+* K) = 2 :=
    (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic hp K hK).1
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hΘ]; norm_num)
  have : Finite (PSL2 K) := inferInstance
  have : Finite (MulAut (PSL2 K)) :=
    Finite.of_injective (fun α : MulAut (PSL2 K) => (α : PSL2 K → PSL2 K)) DFunLike.coe_injective
  have : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  intro E hE
  have h1 := card_le_mul_card_inf_ker (autFieldPart K) E
  rw [hΘ] at h1
  have hinj := pglAction_injective_of_finite K
  have hFr : E ⊓ (autFieldPart K).ker ≤ (pglAction K).range := fun α hα =>
    mem_range_pglAction_of_autFieldPart_eq_one (MonoidHom.mem_ker.mp hα.2)
  have h2 := card_le_four_of_isElemAb2_pgl2 hodd
    ((hE.mono (inf_le_left : E ⊓ (autFieldPart K).ker ≤ E)).comap _ hinj)
  rw [card_comap_of_le_range hinj hFr] at h2
  refine rk_le_of_card_le_two_pow hE.isPGroup ?_
  calc Nat.card ↥E ≤ 2 * Nat.card ↥(E ⊓ (autFieldPart K).ker) := h1
    _ ≤ 2 * 4 := Nat.mul_le_mul_left _ h2
    _ = 2 ^ 3 := by norm_num

theorem autRankLe_of_psl2_25 {L : Type} [Group L] (h : IsPSL 2 5 2 L) : AutRankLe L 3 := by
  obtain ⟨-, K, hKf, hKfin, hK, ⟨e⟩⟩ := h
  exact AutRankLe.of_mulEquiv
    (e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm)
    (autRankLe_psl2_sq Nat.prime_five (by norm_num) hK)

end CFSG.Quasithin.H13.Ch9.KGFF
