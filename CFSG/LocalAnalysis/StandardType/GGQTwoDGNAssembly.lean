module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDGen
public import CFSG.LocalAnalysis.StandardType.GGQTwoDNbrDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoDGNUnit
public import CFSG.LocalAnalysis.StandardType.GGQTwoDGNUnitGen
public import CFSG.LocalAnalysis.StandardType.GGQTwoNbrG3Aux
public import CFSG.LocalAnalysis.StandardType.GGQTwoNbrRecAuxModel
public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub
import CFSG.LocalAnalysis.StandardType.GGInnerDiagBridgeSU
public import CFSG.LocalAnalysis.StandardType.GGQTwoDGNOrthReal

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Assembly CFSG.ClassicalInvolution.Phan

@[expose] def QTwoOrthJAnchorInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ), p.Prime → ∀ (Bs X J : Subgroup G) (x : G)
    (Φ : OrthTorus.OrthFrameCore p Bs X), Nat.card Φ.F = 2 → 5 ≤ Φ.r →
      Subgroup.center ↥X = ⊥ → x ∈ Bs → J ≤ X →
        IsComponentOf J (X ⊓ Subgroup.centralizer ({x} : Set G)) →
          ∃ x' y' : OmPlusIdx Φ.r,
            omPlusRefl p x' * omPlusRefl p y' ≠ omPlusRefl p y' * omPlusRefl p x' ∧
              Φ.img (Φ.rank2 x' y') ≤ J

section Inputs

@[expose] def GGQTwoDBsCardInputOn (R : ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)) (ι : Type) (M : CoxeterMatrix ι)
    (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)), GGQTwoDCfg p B Bs x L D J 𝒦 M e →
      ∀ (m : ℕ) (e' : Fin m ≃ ι), R m → M = (ggCoxeterMatrixD m).reindex e' →
        Nat.card ↥Bs = 3 ^ m

theorem ggQTwoDBsCardInput_of_selModule (h : GGQTwoDSelModuleInput) :
    GGQTwoDBsCardInputOn fun m => 7 ≤ m := by
  intro G _ _ p B Bs x L D J 𝒦 ι M e hcfg m e' hm hM
  obtain ⟨β, -⟩ := h G p B Bs x L D J 𝒦 ι M e hcfg m e' hm hM
  exact card_bs_of_module β

theorem ggQTwoGNInputOn_of_inputs {R : ℕ → Prop} (hR : ∀ m, R m → 6 ≤ m)
    (hLB : GGLBalanceInput) (hPJ : GGStdSubPrimeInput) (hCh : GGQTwoDL1ChartInputOn R)
    (hBsCard : GGQTwoDBsCardInputOn R) (hJA : QTwoOrthJAnchorInput) :
    GGQTwoGNInputOn R := by
  intro G _ _ p B Bs x L D J 𝒦 ι M e hcfg m e' hRm hM y K' hnbr _
  have hC : GGConfig p B Bs x L D J := hcfg.1.1.1
  have hp : p.Prime := hC.1.2.2.2.2.2.1.1
  have hchart := hCh G p B Bs x L D J 𝒦 ι M e hcfg m e' hRm hM K' (Or.inr ⟨y, hnbr⟩)
  rcases hchart with ⟨F, _, _, _, n, ψ, hF, hloc, hrange, hdiag, hfull⟩ | ⟨Φ, hF, h5, hZ⟩
  · have hp3 : p = 3 :=
      (Nat.prime_dvd_prime_iff_eq hloc.prime Nat.prime_three).mp (by simpa using hloc.dvd)
    subst hp3
    have hcard := hBsCard G 3 B Bs x L D J 𝒦 ι M e hcfg m e' hRm hM
    have hcent := qtwoDNbr_card_cent_le hC hnbr
    have hn : 5 ≤ n := by
      by_contra hlt
      have hlt' : n < 5 := not_le.mp hlt
      have h6 := hR m hRm
      have h1 : 3 ^ (n - 1) ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega : n - 1 ≤ 3)
      have h2 : 3 ^ m ≤ 3 ^ 3 * 3 ^ 2 := by
        rw [← hcard, hfull]
        exact Nat.mul_le_mul h1 hcent
      have h3 : 3 ^ 5 < 3 ^ m := Nat.pow_lt_pow_right (by norm_num) (by omega)
      omega
    exact qTwoD_gn_of_unitaryChart hC hLB hPJ hnbr hF hloc hrange hdiag hn
  · haveI : Fact p.Prime := ⟨hp⟩
    have hJX : J ≤ K' := le_of_ggNbr hLB hC.1 hC.2.2 (hPJ G p B x L D J hC.1 hC.2.2) hnbr
    have hcomp := ggIsComponentOf_inf_centralizer_nbr hC hnbr hJX
    have hxBs : x ∈ Bs := hC.2.1.1 hC.1.2.2.2.2.2.2.1.2.1
    obtain ⟨x', y', hnc, hle⟩ := hJA G p hp Bs K' J x Φ hF h5 hZ hxBs hJX hcomp
    exact qTwoD_gn_of_orthChart Φ hF hnc hle

theorem ggQTwoGNInput_of_inputs (hLB : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    (hCh : GGQTwoDL1ChartInput) (hSel : GGQTwoDSelModuleInput)
    (hJA : QTwoOrthJAnchorInput) : GGQTwoGNInput :=
  ggQTwoGNInputOn_of_inputs (fun m hm => by omega) hLB hPJ hCh
    (ggQTwoDBsCardInput_of_selModule hSel) hJA

end Inputs

end CFSG.StandardType.QTwo

end
