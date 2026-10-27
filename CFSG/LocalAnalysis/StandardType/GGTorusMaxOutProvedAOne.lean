module

public import CFSG.LocalAnalysis.StandardType.GGTorusMaxSieveDefs
import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011I1416Small
import CFSG.RankThree.PartTwo.Sec4.RonanK432L2Outer
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup

public section

namespace CFSG.StandardType.FrameRoute

theorem tmOut_A_one (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower) (hd : d.1 = .A 1 q)
    (J : Type) [Group J] [Finite J] (e : Nonempty (J ≃* (TauCeti.CFSGIndex.lie d).Group)) :
    Nat.card (MulAut J) ∣ Nat.card J * tmLieOut d.1 := by
  let p := q.p
  let f := q.exponent
  have hp : p.Prime := q.prime_p
  have hf : 1 ≤ f := q.exponent_pos
  have hcard : q.card = p ^ f := TauCeti.PrimePower.card_def q
  have hd_index : CFSG.AGLEmbedding.IsLinTwoIndex p f d := ⟨q, hd, rfl, rfl⟩
  obtain ⟨e1⟩ :=
    @CFSG.AGLEmbedding.nonempty_mulEquiv_psl2GF_of_isLinTwoIndex p f ⟨hp⟩ d hd_index
  obtain ⟨e2⟩ := e
  let e3 : J ≃* CFSG.AGLEmbedding.PSL2GF p f := e2.trans e1
  have h_aut : Nat.card (MulAut J) = p ^ f * ((p ^ f) ^ 2 - 1) * f :=
    @CFSG.LocalAnalysis.GLTheoremA.small_card_aut_psl J _ p f ⟨hp⟩ hf e3
  have h_card_J : Nat.card J = Nat.card (CFSG.AGLEmbedding.PSL2GF p f) :=
    Nat.card_congr e3.toEquiv
  have h_field_card : Nat.card (GaloisField p f) = p ^ f := by
    rw [GaloisField.card p f (by omega)]
  have h_order : Nat.card (CFSG.AGLEmbedding.PSL2GF p f) * Nat.gcd 2 (p ^ f - 1) =
      p ^ f * ((p ^ f) ^ 2 - 1) := by
    have h := CFSG.RankThree.PartTwo.Sec4.RonanK432.card_psl2_mul_gcd (GaloisField p f)
    simpa [CFSG.AGLEmbedding.PSL2GF, CFSG.GorensteinWalter.PSL2, h_field_card] using h
  have h_tm : tmLieOut d.1 = Nat.gcd 2 (p ^ f - 1) * f := by
    rw [hd]
    dsimp only [tmLieOut]
    rw [hcard]
    dsimp only [p, f]
    norm_num
  have h_eq : Nat.card (CFSG.AGLEmbedding.PSL2GF p f) * tmLieOut d.1 =
      p ^ f * ((p ^ f) ^ 2 - 1) * f := by
    rw [h_tm]
    calc
      Nat.card (CFSG.AGLEmbedding.PSL2GF p f) * (Nat.gcd 2 (p ^ f - 1) * f)
          = (Nat.card (CFSG.AGLEmbedding.PSL2GF p f) * Nat.gcd 2 (p ^ f - 1)) * f := by
            rw [Nat.mul_assoc]
      _ = (p ^ f * ((p ^ f) ^ 2 - 1)) * f := by rw [h_order]
  rw [h_aut, h_card_J, h_eq]

end CFSG.StandardType.FrameRoute

end
