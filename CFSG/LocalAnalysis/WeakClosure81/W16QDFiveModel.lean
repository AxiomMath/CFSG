module

public import CFSG.LocalAnalysis.WeakClosure81.W16QDFiveSev
public import CFSG.LocalAnalysis.WeakClosure81.W16QDFiveFpf

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.QuasithinUnique.Setup.Campbell
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11
open Subgroup

variable {G : Type} [Group G] [Finite G]

section Certified


namespace DichCfg

variable {M V₀ V U S H : Subgroup G} {X : Type} [Group X] {φ : ↥(conjClosure V H) →* X}

theorem exists_card_of_heis [Finite X] (d : DichCfg M V₀ V U S H φ) {p : ℕ}
    (h : Heis2p X (SevenK.barSub (conjClosure V H) φ V) p)
    (hexp : Monoid.exponent ↥(fusionOddCore X) = p)
    (hfaith : conjClosure V H ⊓ centralizer (iSub16 V H : Set G) ≤ iSub16 V H) :
    ∃ k : ℕ, Nat.card ↥(conjClosure V₀ H) = 2 ^ (p * k) ∧
      Nat.card ↥V₀ = 2 ^ ((p - 1) * k / 2) ∧
      ∀ z : ↥(conjClosure V H), φ z ∈ oddCoreCenter X → φ z ≠ 1 →
        conjClosure V₀ H ⊓ centralizer ({(z : G)} : Set G) = ⊥ := by
  classical
  have hIea : IsElemAbelian 2 (iSub16 V H) :=
    Cex16.isElemAbelian_iSub16 d.cfg.one d.cfg.std d.cfg.cex d.cfg.min.fam16
  have hHnorm : H ≤ Subgroup.normalizer (iSub16 V H : Set G) :=
    CFSG.Quasithin.le_normalizer_conjClosure (V ⊓ pCoreOf 2 H) H
  obtain ⟨D⟩ := exists_modDataE hIea hHnorm
  obtain ⟨k, hk1, hk2, hk3⟩ := w16q_seven_fifteen_apply d D h hexp hfaith
  refine ⟨k, ?_, ?_, ?_⟩
  · rw [← w16q_card_iSub_UAOf d D, hk1]
  · rw [← w16q_card_inf_iSub_UAOf d D, hk2]
  · exact w16q_fixedPointFree d D h hfaith hk1 hk3

end DichCfg

end Certified

end CFSG.LocalAnalysis.WeakClosure81

end
