module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporONCheck
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSmall
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public noncomputable section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10.ONK

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.AGLEmbedding.ParabHub Subgroup

theorem threeDvdOver_onR :
    ThreeDvdOver ↥onM120Chain.originalSubgroup := by
  intro T J hT hTJ hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hi : ¬ 2 ∣ T.index := by
    have h := hT.2.2
    have e : (T.subgroupOf ⊤).index = T.index := relIndex_top_right T
    rwa [e] at h
  exact onK_check.1 (hT.2.1.toSylow hi) J hTJ hne

theorem exists_onKY {r : ℕ} (hr : r = 5 ∨ r = 7) :
    ∃ y ∈ onM120Chain.originalSubgroup, orderOf y = r ∧ ∀ k : ℕ, 0 < k → k < r →
      Nat.card ↥(centralizer {y ^ k} ⊓ onM120Chain.originalSubgroup) = r :=
  onK_check.2.1 r hr

abbrev onKs (j : ℕ) : Equiv.Perm (Fin 32) := permOfArr 32 Data.T32Chain.generators[j]!

@[expose] def onKd (i : ℕ) : Equiv.Perm (Fin 32) := onKPerm 32 onKD[i]!

theorem onK_inv_cases {g : Equiv.Perm (Fin 32)}
    (hg : g ∈ onT32Chain.originalSubgroup) (h2 : g * g = 1) (h1 : g ≠ 1)
    (hc : ∀ j < 6, g * (onKs j * g * (onKs j)⁻¹) = onKs j * g * (onKs j)⁻¹ * g) :
    ∃ i < 7, g = onKd i :=
  onK_check.2.2.1 g hg h2 h1 hc

theorem onK_witness {i j : ℕ} (hi : i < 7) (hj : j < 7)
    (hc : onKd i * onKd j = onKd j * onKd i) (hiz : onKd i ≠ onz32) (hjz : onKd j ≠ onz32)
    (hji : onKd j ≠ onKd i) (hjiz : onKd j ≠ onKd i * onz32) :
    ∃ w : Equiv.Perm (Fin 32),
      ((∃ a < 6, ∃ b < 6, w = onKs a * onKs b * (onKs a)⁻¹ * (onKs b)⁻¹) ∨
        ∃ a < 6, w = onKs a ^ 4) ∧
      ¬ (w * onKd i = onKd i * w ∧ w * onKd j = onKd j * w) :=
  onK_check.2.2.2.1 i hi j hj hc hiz hjz hji hjiz

theorem onK_e :
    ∃ e ∈ onT32Chain.originalSubgroup, e * e = 1 ∧ e ≠ 1 ∧ e ≠ onz32 ∧
      ∀ t ∈ onT32Chain.originalSubgroup, t * e = e * t ∨ t * e = e * onz32 * t :=
  onK_check.2.2.2.2

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10.ONK
