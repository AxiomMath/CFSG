module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKJPrimeTransport
import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open

private theorem s16k_field_two {K : Type} [Field K] [Finite K] (hcard : Nat.card K = 2) :
    Nonempty (K ≃+* ZMod 2) := by
  haveI : Fintype K := Fintype.ofFinite K
  have hK' : Fintype.card K = 2 := by rwa [← Nat.card_eq_fintype_card]
  exact ⟨(ZMod.ringEquivOfPrime K Nat.prime_two hK').symm⟩

private theorem s16k_bc_eq_one {K : Type} [Field K] (e : K ≃+* ZMod 2) {b c : K}
    (hpoly : ∀ s : K, s ^ 2 + b * s + c ≠ 0) : e b = 1 ∧ e c = 1 := by
  have hpoly' : ∀ t : ZMod 2, t ^ 2 + e b * t + e c ≠ 0 := by
    intro t h0
    apply hpoly (e.symm t)
    apply e.injective
    simpa using h0
  have h0 := hpoly' 0
  have h1 := hpoly' 1
  generalize e b = x at h0 h1 ⊢
  generalize e c = y at h0 h1 ⊢
  revert x y
  decide

theorem s16k_realizes_natOmega_map {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
    {I Z : Subgroup W} {ι : Type} [Fintype ι] [DecidableEq ι] {K L : Type} [Field K] [Field L]
    (φ : K ≃+* L) {QK : (ι → K) → K} {QL : (ι → L) → L}
    (hQ : ∀ v : ι → K, QL (φ ∘ v) = φ (QK v))
    (h : (FFModel.nat (StatedOmega QK)).Realizes H I Z) :
    (FFModel.nat (StatedOmega QL)).Realizes H I Z :=
  s15k_jp_nat_transport φ (CFSG.ClassicalInvolution.Upgrade.map_statedOmega φ hQ) h

theorem s16k_natOmegaPlus_zmod {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
    {I Z : Subgroup W} {n : ℕ} (h : NatOmegaPlus H I Z n 1) :
    (FFModel.nat (StatedOmega (StatedQuadPlus (n / 2) (ZMod 2)))).Realizes H I Z := by
  obtain ⟨-, F, hF, hfin, hcard, hreal⟩ := h
  obtain ⟨e⟩ := s16k_field_two (K := F) (by simpa using hcard)
  exact s16k_realizes_natOmega_map e
    (fun v => CFSG.ClassicalInvolution.Upgrade.statedQuadPlus_comp e v) hreal

theorem s16k_natOmegaMinus_zmod {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
    {I Z : Subgroup W} {n : ℕ} (h : NatOmegaMinus H I Z n 1) :
    (FFModel.nat (StatedOmega (StatedQuadMinus (n / 2) (ZMod 2) 1 1))).Realizes H I Z := by
  obtain ⟨-, F, hF, hfin, b, c, hcard, hpoly, hreal⟩ := h
  obtain ⟨e⟩ := s16k_field_two (K := F) (by simpa using hcard)
  obtain ⟨hb, hc⟩ := s16k_bc_eq_one e hpoly
  exact s16k_realizes_natOmega_map e
    (fun v => CFSG.ClassicalInvolution.Upgrade.statedQuadMinus_comp e hb hc v) hreal

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
