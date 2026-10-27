module

public import CFSG.Monster.B.TwoA.Unitary.CliqueBridge
public import CFSG.Monster.B.TwoA.Fischer.SliceOrderPSU
public import CFSG.Adapters.RankTwoModelTransports
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.Adapters.RankTwoModelTransports

theorem exists_isElemAbelian_card_two_pow_nine_of_lieModel_psu_six {X : Type} [Group X] [Finite X]
    (hX : CFSG.Blueprint.LieModel X .PSU 6 2 1) :
    ∃ A : Subgroup X, IsElemAbelian 2 A ∧ Nat.card A = 2 ^ 9 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, h10, -, hmax, -⟩ :=
    CFSG.Monster.B.TwoA.Unitary.Clique.unitary_six_maximal_clique_unipotent_kernel
  obtain ⟨hU, hc, -⟩ := h10 _ hmax
  obtain ⟨-, K, _, _, hK, ⟨e₁⟩⟩ := hX.statedClassicalModel (by decide)
  have := Fintype.ofFinite K
  have hFK : Fintype.card K = Fintype.card CFSG.Fischer.F4 := by
    rw [← Nat.card_eq_fintype_card, hK, CFSG.Fischer.F4.card]
    norm_num
  let φ : K ≃+* CFSG.Fischer.F4 := FiniteField.ringEquivOfCardEq hFK
  let e : StatedProj (StatedSU 6 (2 ^ 1) CFSG.Fischer.F4) ≃* X :=
    (statedProjCongr (glCongr φ) (glCongr_statedSU φ 6 (2 ^ 1))
      (glCongr_statedScalars φ)).symm.trans e₁.symm
  let ψ := CFSG.Monster.B.TwoA.Fischer.projSUStatedEquiv.trans e
  have h1 := (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 _).1 hU
  refine ⟨_, h1.map ψ.toMonoidHom, ?_⟩
  rw [Subgroup.card_map_of_injective ψ.injective, hc]

end CFSG.RankThree.GF2n.Parrott
