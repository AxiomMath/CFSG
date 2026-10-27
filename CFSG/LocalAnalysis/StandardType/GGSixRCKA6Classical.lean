module

public import CFSG.LocalAnalysis.StandardType.GGSixA6RedAssembly
public import CFSG.LocalAnalysis.StandardType.GGSixRCKDefs
public import CFSG.LocalAnalysis.StandardType.GGInterfaceFive
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate1952
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate3951
public import Certificates.Certificate8033
public import Certificates.Certificate8064
public import Certificates.Certificate13659
public import Certificates.Certificate13660

public section

namespace CFSG.StandardType.RCKA6

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType
open CFSG.Blueprint.Chevalley (adjointGroup Tag)

private lemma rckCL_center_a6_eq_bot :
    Subgroup.center (alternatingGroup (Fin 6)) = ⊥ :=
  alternatingGroup.center_eq_bot (by rw [Nat.card_fin]; norm_num)

private lemma rckCL_quot_a6_of_quot {G H : Type} [Group G] [Group H]
    (e : G ⧸ Subgroup.center G ≃* alternatingGroup (Fin 6))
    (hJJ : G ⧸ Subgroup.center G ≃* H ⧸ Subgroup.center H) :
    Nonempty (alternatingGroup (Fin 6) ⧸ Subgroup.center (alternatingGroup (Fin 6)) ≃*
      H ⧸ Subgroup.center H) :=
  ⟨(QuotientGroup.quotientMulEquivOfEq rckCL_center_a6_eq_bot).trans
    (QuotientGroup.quotientBot.trans (e.symm.trans hJJ))⟩

theorem rck_A6_classical_noQuot
    {t : StatedLieTag} (ht : t = .PSL ∨ t = .PSU ∨ t = .POmegaPlus ∨ t = .POmegaMinus)
    (X : Type) [Group X] [Finite X] (n f : ℕ) (ψ : (ggU t n f).K →* X) (p : ℕ)
    (G₀ D J : Subgroup X) (hG₀ : GGPresentsG0 G₀ (ggU t n f).D t n f ψ) (hp : p.Prime)
    (hp2 : p ≠ 2) (hDN : D ≤ Subgroup.normalizer (G₀ : Set X))
    (hdiag : ∀ d ∈ D, GGPsiInnerDiag (ggU t n f).D ψ d) (hD : IsElemAbelian p D)
    (hD2 : Nat.card D = p ^ 2) (hJ : IsComponentOf J (G₀ ⊓ Subgroup.centralizer (D : Set X))) :
    ¬ Nonempty ((↥J ⧸ Subgroup.center ↥J) ≃* alternatingGroup (Fin 6)) := by
  rintro ⟨e⟩
  obtain ⟨⟨hadm, _hrk⟩, ⟨hr, hk⟩, _hperf, hLie⟩ := hG₀
  rcases ht with rfl | rfl | rfl | rfl
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := hadm.2.2.1; omega⟩
    obtain ⟨P, J', hP, hJ', hJJ⟩ :=
      A6Red.ggA6_transport_PSL m f X ψ p G₀ D J hr hk hLie hp hp2 hDN hdiag hD hD2 hJ
    exact A6Red.ggA6_not_shape_of_a6 (alternatingGroup (Fin 6)) J' ⟨MulEquiv.refl _⟩
      (rckCL_quot_a6_of_quot e hJJ.some) (A6Red.ggA6_shape_SL (m + 1) P hP J' hJ')
  · obtain ⟨P, J', hPU, hP, hJ', hJJ⟩ :=
      A6Red.ggA6_transport_PSU n f X ψ p G₀ D J hr hk hLie hp hp2 hDN hdiag hD hD2 hJ
    exact A6Red.ggA6_not_shape_of_a6 (alternatingGroup (Fin 6)) J' ⟨MulEquiv.refl _⟩
      (rckCL_quot_a6_of_quot e hJJ.some)
      (A6Red.ggA6_shape_SU f (by rw [GaloisField.card 2 (2 * f) (by have := hadm.2.1; omega), pow_mul'])
        n P hPU hP J' hJ')
  · obtain ⟨F, _, _, _, ι, _, _, Φ, P, J', hPO, hP, hPn, hJ', hJJ⟩ :=
      A6Red.ggA6_transport_Omega .POmegaPlus (Or.inl rfl) n f X ψ p G₀ D J hr hk hLie hp hp2 hDN hdiag
        hD hD2 hJ
    exact A6Red.ggA6_not_shape_of_a6 (alternatingGroup (Fin 6)) J' ⟨MulEquiv.refl _⟩
      (rckCL_quot_a6_of_quot e hJJ.some) (A6Red.ggA6_shape_Omega Φ P hPO hP hPn J' hJ')
  · obtain ⟨F, _, _, _, ι, _, _, Φ, P, J', hPO, hP, hPn, hJ', hJJ⟩ :=
      A6Red.ggA6_transport_Omega .POmegaMinus (Or.inr rfl) n f X ψ p G₀ D J hr hk hLie hp hp2 hDN hdiag
        hD hD2 hJ
    exact A6Red.ggA6_not_shape_of_a6 (alternatingGroup (Fin 6)) J' ⟨MulEquiv.refl _⟩
      (rckCL_quot_a6_of_quot e hJJ.some) (A6Red.ggA6_shape_Omega Φ P hPO hP hPn J' hJ')

end CFSG.StandardType.RCKA6
