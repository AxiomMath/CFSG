module

public import Certificates.Data.HePresCheck
public import CFSG.Certificates.Kernel.Misc.Coset.PG
public import Certificates.Kernel.CosetJ.CJHe0
public import Certificates.Kernel.CosetJ.CJHe1
public import Certificates.Kernel.CosetJ.CJHe2
public import Certificates.Kernel.CosetJ.CJHe3

public section

namespace CertificateChecks.KernelCosetJ.He

open CFSG.CosetTable CFSG.KC.MiscCoset CFSG.ComponentClassification.AS81.HePres.Native

theorem rels₀ : hePiRels.map encW = CFSG.KBRoute.CJHe0.rels := by decide +kernel
theorem rels₁ : hePiRelsH₁.map encW = CFSG.KBRoute.CJHe1.rels := by decide +kernel
theorem rels₂ : hePiRelsH₂.map encW = CFSG.KBRoute.CJHe2.rels := by decide +kernel
theorem rels₃ : hePiRelsH₃.map encW = CFSG.KBRoute.CJHe3.rels := by decide +kernel

theorem card_le : Finite (PG 8 hePiRels) ∧ Nat.card (PG 8 hePiRels) ≤ 4030387200 := by
  have h0 := CJHe0.t1
  unfold CFSG.KBRoute.CJHe0.T1.ok at h0
  have h1 := CJHe1.t1
  unfold CFSG.KBRoute.CJHe1.T1.ok at h1
  have h2 := CJHe2.t1
  unfold CFSG.KBRoute.CJHe2.T1.ok at h2
  have h3 := CJHe3.t1
  unfold CFSG.KBRoute.CJHe3.T1.ok at h3
  have c3 := card_le_of_tableOk hePiRelsH₃ rels₃ h3 (by decide) CFSG.KBRoute.CJHe3.top rfl
  have i2 := genSub_index_le_of_tableOk hePiRelsH₂ rels₂ h2 (by decide) CFSG.KBRoute.CJHe2.top
    (subsetOf _ [0, 1, 2, 3]) rfl
  have := c3.1
  have c2 := card_le_of_genSub_index hePiRelsH₂ _ i2.1 i2.2
  have := c2.1
  have i1 := genSub_index_le_of_tableOk hePiRelsH₁ rels₁ h1 (by decide) CFSG.KBRoute.CJHe1.top
    (subsetOf _ [0, 1, 2, 3, 4]) rfl
  have c1 := card_le_of_genSub_index hePiRelsH₁ _ i1.1 i1.2
  have := c1.1
  have i0 := genSub_index_le_of_tableOk hePiRels rels₀ h0 (by decide) CFSG.KBRoute.CJHe0.top
    (subsetOf _ [0, 1, 2, 3, 4, 6, 7]) rfl
  have c0 := card_le_of_genSub_index hePiRels _ i0.1 i0.2
  refine ⟨c0.1, c0.2.trans ?_⟩
  calc 29155 * Nat.card (PG _ hePiRelsH₁)
      ≤ 29155 * (45 * (3 * 1024)) :=
        Nat.mul_le_mul_left _ (c1.2.trans (Nat.mul_le_mul_left _
          (c2.2.trans (Nat.mul_le_mul_left _ c3.2))))
    _ = 4030387200 := by norm_num

end CertificateChecks.KernelCosetJ.He

end
