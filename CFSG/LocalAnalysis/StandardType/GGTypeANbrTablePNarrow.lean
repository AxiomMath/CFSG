module

public import CFSG.LocalAnalysis.StandardType.GGTypeANbrKnownDefs
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrLabels
public import CFSG.LocalAnalysis.StandardType.GGTPNNarrow

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open

private theorem tanb_two_le_of_dvd_two_pow_sub_one {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (h : p ∣ 2 ^ f - 1) : 2 ≤ f := by
  by_contra hf2
  have : f = 1 := by omega
  subst this
  norm_num at h
  exact hp.ne_one h

theorem ggTypeANbrTablePInput_of_narrow (hCD : GGTypeACompatDiagBInput)
    (hRig : GGLabelRigidInput)
    (hTA : GGNbrTablePNbrInputOnL GGRegimeTypeAL) : GGTypeANbrTablePInput := by
  intro G _ _ p B Bs x L D J n f y K hcfg
  have hcfg0 := hcfg
  obtain ⟨hconfig, hOp, hInn, hNoTr, hTAbr⟩ := hcfg
  intro _ hInn' y' K' hnbr labJ labK hΛJ hΛK hhJ hhK
  obtain ⟨φ₁, -, -, hk₁, -, -, hJ, -, -⟩ := hCD G p B Bs x L D J n f y K hcfg0
  have hp : p.Prime := GGTypeANbrCfg.prime hcfg0
  have hn : 3 ≤ n := GGTypeANbrCfg.three_le hcfg0
  have hf : 1 ≤ f := GGTypeANbrCfg.one_le_f hcfg0
  have hpf : p ∣ 2 ^ f - 1 := GGTypeANbrCfg.dvd_two_pow_sub_one hcfg0
  have hf2 : 2 ≤ f := tanb_two_le_of_dvd_two_pow_sub_one hp hf hpf
  have hLmod : StatedClassicalModel (L ⧸ Subgroup.center L) .PSL (n + 1) 2 f := hTAbr.1
  have hΛL : LargeEvenInLambda2 ⟨.A, n, f⟩ := largeEvenInLambda2_typeA hLmod
  have hhL : GGHasLabel ⟨.A, n, f⟩ (L ⧸ Subgroup.center L) := ggHasLabel_typeA hLmod
  have hΛJ₀ : LargeEvenInLambda2 ⟨.A, n - 1, f⟩ :=
    ⟨by show 1 ≤ f; omega, by show 1 ≤ n - 1; omega, fun _ => hf2⟩
  have hhJ₀ : GGHasLabel ⟨.A, n - 1, f⟩ (J ⧸ Subgroup.center J) :=
    ggHasLabel_J_of_lift hn hf hk₁ hJ
  have hreg : GGRegimeTypeAL p (Nat.card Bs) ⟨.A, n, f⟩ ⟨.A, n - 1, f⟩ labK :=
    ⟨rfl, hn, hf2, hpf, rfl⟩
  exact hTA G p B Bs x L D J y' K' hconfig hInn'.1 (hInn'.2 y' K' hnbr) hnbr
    ⟨.A, n, f⟩ ⟨.A, n - 1, f⟩ labK hΛL hΛJ₀ hΛK hreg hhL hhJ₀ hhK

end CFSG.StandardType

end
