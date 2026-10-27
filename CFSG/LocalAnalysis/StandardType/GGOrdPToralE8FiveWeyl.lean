module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarE8FiveIsotropic
import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompKac
import CFSG.LocalAnalysis.StandardType.GGTableBExcSylow
import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesCore

public section

namespace CFSG.StandardType.OrdPToralE8Five

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.CrossChar

local instance ordPToralE8FiveFactFive : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

local instance ordPToralE8FiveNeZeroRank : NeZero Tag.E8.rank := ⟨by decide⟩

private def kacG : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ :=
  !![4, 5, 7, 10, 8, 6, 4, 2; 5, 8, 10, 15, 12, 9, 6, 3; 7, 10, 14, 20, 16, 12, 8, 4;
    10, 15, 20, 30, 24, 18, 12, 6; 8, 12, 16, 24, 20, 15, 10, 5; 6, 9, 12, 18, 15, 12, 8, 4;
    4, 6, 8, 12, 10, 8, 6, 3; 2, 3, 4, 6, 5, 4, 3, 2]

private def kacPt (n0 n1 n2 n3 n4 n5 n6 n7 : ℕ) : Fin Tag.E8.rank → ZMod 5 :=
  TableBExc.redMod .E8 5 (Matrix.mulVec kacG
    ![(n0 : ℤ), (n1 : ℤ), (n2 : ℤ), (n3 : ℤ), (n4 : ℤ), (n5 : ℤ), (n6 : ℤ), (n7 : ℤ)])

private def wordPt (l : List (Fin Tag.E8.rank)) (x : Fin Tag.E8.rank → ZMod 5) :
    Fin Tag.E8.rank → ZMod 5 :=
  TableBExc.redMod .E8 5 (TableBExc.wordAct .E8 l (TableBExc.liftMod .E8 5 x))

private def kacWords : List (List (Fin Tag.E8.rank)) :=
  [[], [6, 7, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4], [6, 7, 5, 6, 3, 4, 5, 0, 2, 1, 3, 4],
    [7, 0, 2, 3, 4, 1, 3, 2, 0]]

private theorem kac_check : ∀ (lam : ZMod 5), lam * lam = -1 →
    ∀ (n0 : Fin 3) (n1 n2 : Fin 2) (n3 : Fin 1) (n4 n5 n6 : Fin 2) (n7 : Fin 3),
    2 * (n0 : ℕ) + 3 * n1 + 4 * n2 + 6 * n3 + 5 * n4 + 4 * n5 + 3 * n6 + 2 * n7 ≤ 5 →
    NoOffRest.bform .E8 5 (kacPt n0 n1 n2 n3 n4 n5 n6 n7) (kacPt n0 n1 n2 n3 n4 n5 n6 n7) = 0 →
    ∃ l ∈ kacWords, wordPt NoOffRest.wordE8W (wordPt l (kacPt n0 n1 n2 n3 n4 n5 n6 n7)) =
      lam • wordPt l (kacPt n0 n1 n2 n3 n4 n5 n6 n7) := by
  decide +kernel

private theorem torusAct_wordProd (l : List (Fin Tag.E8.rank)) (x : Fin Tag.E8.rank → ZMod 5) :
    TableBExc.torusAct .E8 5 ((coxeterSystem Tag.E8).wordProd l) x = wordPt l x := by
  rw [TableBExc.torusAct, TableBExc.wordProd_smul]
  rfl

theorem exists_torusAct_mem_eigE8_of_bform_eq_zero
    {lam : ZMod 5} (hlam : lam * lam = -1)
    {s : Fin Tag.E8.rank → ZMod 5} (hs : NoOffRest.bform .E8 5 s s = 0) :
    ∃ v : WeylGroup .E8, TableBExc.torusAct .E8 5 v s ∈ NoOffRest.eigE8 5 lam := by
  obtain ⟨w, μ, hwμ, hμ0, hμθ⟩ := kacE8.exists_normal 5 (by norm_num)
    (TableBExc.liftMod .E8 5 (ExcFrames.frameCoord .E8 5 s))
  have hws : TableBExc.torusAct .E8 5 w s = TableBExc.redMod .E8 5 (Matrix.mulVec kacG μ) := by
    have hdet := ExcFrames.isUnit_det_symmetrizedCartan (τ := .E8) (Or.inr (Or.inr rfl))
      (p := 5) (by norm_num)
    apply ExcFrames.frameCoord_injective hdet
    rw [← ExcFrames.adAct_frameCoord, ExcFrames.frameCoord_redMod, Matrix.mulVec_mulVec,
      show kacG = kacE8.G from rfl, kacE8.mul_G, show kacE8.N = 1 from rfl, one_smul,
      Matrix.one_mulVec]
    conv_lhs => rw [← TableBExc.redMod_liftMod (ExcFrames.frameCoord .E8 5 s)]
    rw [ExcFrames.adAct_redMod]
    funext i
    obtain ⟨k, hk⟩ := hwμ (w⁻¹ • (Pi.single i 1 : Fin Tag.E8.rank → ℤ))
    rw [smul_inv_smul, single_dotProduct, one_mul] at hk
    simp only [TableBExc.redMod]
    rw [show (w⁻¹ • (Pi.single i 1 : Fin Tag.E8.rank → ℤ)) ⬝ᵥ
        TableBExc.liftMod .E8 5 (ExcFrames.frameCoord .E8 5 s) = μ i - 5 * k by
      push_cast at hk; omega]
    push_cast
    simp [show (5 : ZMod 5) = 0 from rfl]
  have hiso : NoOffRest.bform .E8 5 (TableBExc.redMod .E8 5 (Matrix.mulVec kacG μ))
      (TableBExc.redMod .E8 5 (Matrix.mulVec kacG μ)) = 0 := by
    rw [← hws, NoOffRest.bform_torusAct, hs]
  have hθ : 2 * μ 0 + 3 * μ 1 + 4 * μ 2 + 6 * μ 3 + 5 * μ 4 + 4 * μ 5 + 3 * μ 6 + 2 * μ 7 ≤ 5 := by
    have h : kacE8.θ ⬝ᵥ μ =
        2 * μ 0 + 3 * μ 1 + 4 * μ 2 + 6 * μ 3 + 5 * μ 4 + 4 * μ 5 + 3 * μ 6 + 2 * μ 7 := by
      simp only [kacE8, dotProduct]
      show ∑ i : Fin 8, ![(2 : ℤ), 3, 4, 6, 5, 4, 3, 2] i * μ i = _
      rw [Fin.sum_univ_eight]
      rfl
    rw [← h]
    exact_mod_cast hμθ
  have h0 := hμ0 0
  have h1 := hμ0 1
  have h2 := hμ0 2
  have h3 := hμ0 3
  have h4 := hμ0 4
  have h5 := hμ0 5
  have h6 := hμ0 6
  have h7 := hμ0 7
  have hμ : (![((μ 0).toNat : ℤ), ((μ 1).toNat : ℤ), ((μ 2).toNat : ℤ), ((μ 3).toNat : ℤ),
      ((μ 4).toNat : ℤ), ((μ 5).toNat : ℤ), ((μ 6).toNat : ℤ), ((μ 7).toNat : ℤ)] :
      Fin Tag.E8.rank → ℤ) = μ := by
    funext i
    fin_cases i <;> exact Int.toNat_of_nonneg (hμ0 _)
  obtain ⟨l, -, hl⟩ := kac_check lam hlam ⟨(μ 0).toNat, by omega⟩ ⟨(μ 1).toNat, by omega⟩
    ⟨(μ 2).toNat, by omega⟩ ⟨(μ 3).toNat, by omega⟩ ⟨(μ 4).toNat, by omega⟩
    ⟨(μ 5).toNat, by omega⟩ ⟨(μ 6).toNat, by omega⟩ ⟨(μ 7).toNat, by omega⟩ (by simp only; omega)
    (by simp only [kacPt]; rw [hμ]; exact hiso)
  simp only [kacPt] at hl
  rw [hμ] at hl
  refine ⟨(coxeterSystem Tag.E8).wordProd l * w, ?_⟩
  rw [NoOffE8Five.mem_eigE8_iff, NoOffRest.torusLin_apply, TableBExc.torusAct_mul, hws,
    NoOffRest.weylE8W, torusAct_wordProd, torusAct_wordProd]
  exact hl

end CFSG.StandardType.OrdPToralE8Five

end
