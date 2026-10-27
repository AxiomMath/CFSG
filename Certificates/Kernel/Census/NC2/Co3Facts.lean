module

public import Certificates.Kernel.Census.NC2.Co3
public import CFSG.Certificates.Kernel.NC2LSound

public section

namespace CertificateChecks.KernelNC2.Co3

open CFSG.Blueprint

theorem facts : ∃ (t g x : NativeSporadic.Co3) (S : Subgroup NativeSporadic.Co3),
    orderOf t = 2 ∧ S ≤ Subgroup.centralizer {t} ∧ Nat.card S = 2 ^ 10 ∧
    g ∈ Subgroup.centralizer {t} ∧ x ∈ Subgroup.centralizer {t} ∧ x ≠ 1 ∧ Odd (orderOf x) ∧
    ∀ s ∈ S ⊓ S.map (MulAut.conj g).toMonoidHom, x * s = s * x := by
  have : Finite NativeSporadic.Co3 := inferInstance
  obtain ⟨t, g, x, S, h1, h2, h3, h4, h5, h6, h7, h8, -⟩ :=
    CFSG.KC.NC2L.nc2L_facts L.lay_ok (p := 2) (d := 22) rfl rfl L.decA L.decB L.LA_eq L.LB_eq
      (C := fun i => P.CL.getD i ⟨0, [], []⟩) (S := fun i => P.SL.getD i []) rfl
      (by rw [m_eq]; exact chain) nc2_K
  exact ⟨t, g, x, S, h1, h2, h3, h4, h5, h6, h7, h8⟩

end CertificateChecks.KernelNC2.Co3

end
