module

public import CFSG.Certificates.Kernel.BabyMonster.B11Facts
public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.BabyMonster.B11Facts
import Certificates.Kernel.BabyMonster.Seeds

public section

namespace Certificates

open CertificateChecks

open CFSG.Blueprint CFSG.KC.BM

open CFSG.Blueprint.NativeSporadic in
theorem certificate17706 : ∃ Y X0 X1 X2 X3, Y ∈ seedMonoid 2 4370 1 BSeed1 BSeed2 ∧
    X0 ∈ seedMonoid 2 4370 1 BSeed1 BSeed2 ∧ X1 ∈ seedMonoid 2 4370 1 BSeed1 BSeed2 ∧
    X2 ∈ seedMonoid 2 4370 1 BSeed1 BSeed2 ∧ X3 ∈ seedMonoid 2 4370 1 BSeed1 BSeed2 ∧
    CFSG.KC.BM.B11.Fact17706 Y X0 X1 X2 X3 := by
  have h := KernelBM.B11Mem.b11_mem.2 (NativeSporadic.seedMonoid 2 4370 1 NativeSporadic.BSeed1
    NativeSporadic.BSeed2) (by
      intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · rw [← CertificateChecks.KernelBM.genA₁_eq_stripMat]
        exact Submonoid.subset_closure (Set.mem_insert _ _)
      · rw [← CertificateChecks.KernelBM.genA₂_eq_stripMat]
        exact Submonoid.subset_closure (Set.mem_insert_of_mem _ rfl))
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at h
  obtain ⟨my, m0, m1, m2, m3, -⟩ := h
  exact ⟨_, _, _, _, _, my, m0, m1, m2, m3, KernelBM.B11.fact17706⟩

end Certificates
