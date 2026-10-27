module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthIdentDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthIdentActs
public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthRealize
public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthStd

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.StandardType.OrthTorus CFSG.Open CFSG.ClassicalInvolution.PhanDn
open CFSG.ClassicalInvolution.PhanDn.QTwo CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits
open CFSG.RankThree.Classical2 (orthDerived)

section Ident

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {Bs Y : Subgroup G}
  (Φ : OrthFrameCore p Bs Y)

theorem qtwoOrth_realize (hF : Nat.card Φ.F = 2)
    {w : MulAut (Fin Φ.r → Multiplicative (ZMod p))}
    (hw : w ∈ omSigned p Φ.r) :
    ∃ μ ∈ TauCeti.QuadraticMap.orthogonalGroup Φ.Q, ∀ f, μ * Φ.Δ.τ f * μ⁻¹ = Φ.Δ.τ (w f) :=
  Φ.exists_realize hF hw

theorem qtwoOrth_std (hF : Nat.card Φ.F = 2) (_hZ : Subgroup.center ↥Y = ⊥)
    (_hBs : IsElemAbelian p Bs) (m : ℕ) (hm : 3 ≤ m) (hr : Φ.r = m + 1) :
    ∃ (_ : Algebra Φ.F (GaloisField 2 2))
      (E : QuadExt Φ.F (GaloisField 2 2) (unitaryInvolution (GaloisField 2 2) 2 1))
      (χ : Φ.V ≃ₗ[Φ.F] (Fin (m + 1) → GaloisField 2 2)),
      (∀ v, Qn E (m + 1) (χ v) = Φ.Q v) ∧
      (∀ k : Fin Φ.r, (Φ.rank1 (omStd Φ.r (by omega) k)).map
          (LinearEquiv.autCongr χ).toMonoidHom = qtwoStdU E m hm (Fin.cast hr k)) ∧
      (∀ k k' : Fin Φ.r, ggCoxeterMatrixD (m + 1) (Fin.cast hr k) (Fin.cast hr k') = 3 →
        (Φ.rank2 (omStd Φ.r (by omega) k) (omStd Φ.r (by omega) k')).map
          (LinearEquiv.autCongr χ).toMonoidHom =
          qtwoStdW E m hm (Fin.cast hr k) (Fin.cast hr k')) := by
  obtain ⟨inst, E, χ, -, -, hQ, -, h1, h2⟩ := qtwoOrth_std_torus Φ hF m hm hr
  exact ⟨inst, E, χ, hQ, h1, h2⟩

end Ident

end CFSG.StandardType.QTwo

end
