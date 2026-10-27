module

public import CFSG.Certificates.Kernel.BabyMonster.E35Cyc
public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.BabyMonster.E35
import Certificates.Kernel.BabyMonster.Fi23Mem
import Certificates.Kernel.BabyMonster.Seeds

public section

namespace Certificates

open CertificateChecks

open CFSG.Blueprint CFSG.KC.BM

open CFSG.Blueprint.NativeSporadic in
theorem certificate431004 : ∃ X G, X ∈ seedMonoid 2 4370 1 BSeed1 BSeed2 ∧ G ∈ seedMonoid 2 4370 1 BSeed1 BSeed2 ∧
    CFSG.KC.BM.E35.CycFacts X G := by
  obtain ⟨hx, hg, h⟩ := KernelBM.E35.fact431004_of
  have hA1 : stripMat Seeds.A1 ∈ NativeSporadic.seedMonoid 2 4370 1 NativeSporadic.BSeed1
      NativeSporadic.BSeed2 := by
    rw [← CertificateChecks.KernelBM.genA₁_eq_stripMat]
    exact Submonoid.subset_closure (Set.mem_insert _ _)
  have hA2 : stripMat Seeds.A2 ∈ NativeSporadic.seedMonoid 2 4370 1 NativeSporadic.BSeed1
      NativeSporadic.BSeed2 := by
    rw [← CertificateChecks.KernelBM.genA₂_eq_stripMat]
    exact Submonoid.subset_closure (Set.mem_insert_of_mem _ rfl)
  obtain ⟨hU, hV⟩ := Fi23Mem.fi23_mem hA1 hA2
  have hle : Submonoid.closure {stripMat Fi23.U, stripMat Fi23.V} ≤
      NativeSporadic.seedMonoid 2 4370 1 NativeSporadic.BSeed1 NativeSporadic.BSeed2 :=
    Submonoid.closure_le.2 (by
      rintro _ (rfl | hy)
      · exact hU
      · rw [Set.mem_singleton_iff] at hy
        subst hy
        exact hV)
  exact ⟨_, _, hle hx, hle hg, h⟩

end Certificates
