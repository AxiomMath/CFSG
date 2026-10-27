module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinEMarked
public import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinDCell
public import CFSG.LocalAnalysis.StandardType.GGPhanOneNodePosition
public import CFSG.LocalAnalysis.StandardType.PhanEStdTwE6Nodes
public import CFSG.LocalAnalysis.StandardType.PhanEStdE8RootNodes
public import CFSG.LocalAnalysis.StandardType.GGSimplyLacedWeyl

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Phan.PhanE

section Universal

section Cell

open PsiDiag PsiDiagChar RankOneXfer in
theorem ggTwE6StdNodeInput_holds :
    ∀ (f : ℕ) (hq : 4 ≤ 2 ^ f) (F : Type) [Field F] [Finite F] [CharP F 2]
      (hF : Nat.card F = (2 ^ f) ^ 2),
      ∃ (j : Fin 6) (k : Type) (_ : Field k) (_ : Finite k) (_ : CharP k 2)
        (γ : Fin (ggU .twistedE6 0 f).D.rank → ℤ)
        (phi : Matrix.SpecialLinearGroup (Fin 2) k →* (ggU .twistedE6 0 f).K)
        (v : (ggU .twistedE6 0 f).K),
        Function.Injective phi ∧ γ ∈ (ggU .twistedE6 0 f).D.roots ∧
        (sl2UpperUniSub k).map phi = (ggU .twistedE6 0 f).D.rootGroup γ ∧
        (∀ a : kˣ, phi (sl2Diag a) ∈ ggTorus (ggU .twistedE6 0 f).D) ∧
        phi.range.map (MulAut.conj v).toMonoidHom =
          ((e6StdConfig F f hF (one_le_of_four_le_two_pow hq)).S.ι j).range := by
  intro f hq F _ _ _ hF
  obtain ⟨γ, phi, hphi, hγ, hup, hdiag, v, hv⟩ :=
    exists_e6_stdConfig_primitive_node hF (one_le_of_four_le_two_pow hq)
  exact ⟨1, GaloisField 2 f, inferInstance, inferInstance, inferInstance,
    γ, phi, v, hphi, hγ, hup, hdiag, hv⟩

open PsiDiag PsiDiagChar RankOneXfer CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint in
open PsiDiag PsiDiagChar RankOneXfer in
theorem ggE8StdNodeInput_holds :
    ∀ (f : ℕ) (hq : 4 ≤ 2 ^ f) (F : Type) [Field F] [Finite F] [CharP F 2]
      (hF : Nat.card F = (2 ^ f) ^ 2),
      ∃ (j : Fin 8) (k : Type) (_ : Field k) (_ : Finite k) (_ : CharP k 2)
        (γ : Fin (ggU .E8 0 f).D.rank → ℤ)
        (phi : Matrix.SpecialLinearGroup (Fin 2) k →* (ggU .E8 0 f).K)
        (v : (ggU .E8 0 f).K),
        Function.Injective phi ∧ γ ∈ (ggU .E8 0 f).D.roots ∧
        (sl2UpperUniSub k).map phi = (ggU .E8 0 f).D.rootGroup γ ∧
        (∀ a : kˣ, phi (sl2Diag a) ∈ ggTorus (ggU .E8 0 f).D) ∧
        phi.range.map (MulAut.conj v).toMonoidHom =
          ((e8StdConfig F f hF (one_le_of_four_le_two_pow hq)).S.ι j).range := by
  intro f hq F _ _ _ hF
  obtain ⟨phi, hphi, hup, hdiag, v, hv⟩ :=
    exists_e8_stdConfig_primitive_node (k := F) hF (one_le_of_four_le_two_pow hq)
  refine ⟨1, GaloisField 2 f, inferInstance, inferInstance, inferInstance,
    Pi.single (1 : Fin 8) 1, phi, v, hphi, ?_, hup, hdiag, hv⟩
  change (Pi.single (1 : Fin 8) 1 : Fin 8 → ℤ) ∈ (e8Datum (GaloisField 2 f)).roots
  exact (mem_adjDatum_roots).2 (isRoot_single .E8 (1 : Fin 8))

theorem ggSecFiveCompatJoinResNAt_E_of_member (hL1 : GGSecFiveL1PhanInput)
    (hRk1 : GGSecFiveRk1PhanInput) (hGen : GGSecFiveGenPhanInput) (hOrb : GGSecFiveOrbPhanInput)
    (hL2 : GGSecFiveL2PhanInput) (hPair : GGSecFivePhanPairInput)
    (hNbr : GGSecFiveNonSplitNbrInput) (hMem : GGSecFiveJoinMemberAt GGIsWeylMatrixE) :
    GGSecFiveCompatJoinResNAt GGIsWeylMatrixE := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hReg hrow hQ ι M e hpres hT hSix t n f ψ hψ hJ
  obtain ⟨r₀, -, hr₀, K, hK, t', n', f', ψ', hadm, hrk, hker', hrange', k', _, _, _, δ, model',
    hmember⟩ := hMem G p B Bs x L D J 𝒦 hcfg hReg hrow hQ ι M e hpres hT hSix t n f ψ hψ hJ
  obtain ⟨q, hq, -, hall⟩ :=
    ggSecFiveJoinE_markedTop hL1 hRk1 hGen hOrb hL2 hPair hNbr hcfg hReg hpres hT hSix hJ
  have hq1 : 1 ≤ q := one_le_of_four_le_two_pow hq
  have hF : Nat.card (GaloisField 2 (2 * q)) = (2 ^ q) ^ 2 := card_galoisField_two_mul 2 q hq1
  have hconn : GGSimplyLacedConnected M :=
    ggSimplyLacedConnected_of_weyl hpres.1 (fun i j hij => GGIsWeylMatrixE.le_three hT i j hij)
  have hA : ggAutomizerJoin L Bs 𝒦 ≤ ggAutomizer (ggG0 p B x L D J) Bs := by
    rw [hJ]
    exact ggAutomizerJoin_le_ggAutomizer L Bs 𝒦
  rcases hall (GaloisField 2 (2 * q)) hF with ⟨σ, -, ψ₀, hψ₀, hnode⟩ | ⟨σ, -, ψ₀, hψ₀, hnode⟩ |
      ⟨σ, -, ψ₀, hψ₀, hnode⟩
  · obtain ⟨j, k, _, _, _, γ, phi, v, hphi, hγ, hup, hdiag, hv⟩ :=
      ggTwE6StdNodeInput_holds q hq (GaloisField 2 (2 * q)) hF
    exact ggSecFiveCompat_of_phan_node hψ₀ e hconn hA hr₀ (σ j) _ (hnode j) hK hadm
      hrk hker' hrange' phi hphi hγ hup hdiag v hv model' hmember
  · exact ggSecFiveCompat_of_e7_stdConfig_node hψ₀ hF hq e hconn hA hr₀ (σ 0) 0 (hnode 0)
      hK hadm hrk hker' hrange' model' hmember
  · obtain ⟨j, k, _, _, _, γ, phi, v, hphi, hγ, hup, hdiag, hv⟩ :=
      ggE8StdNodeInput_holds q hq (GaloisField 2 (2 * q)) hF
    exact ggSecFiveCompat_of_phan_node hψ₀ e hconn hA hr₀ (σ j) _ (hnode j) hK hadm
      hrk hker' hrange' phi hphi hγ hup hdiag v hv model' hmember

end Cell

end Universal

end CFSG.StandardType

end
