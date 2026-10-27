module

public import Certificates.Kernel.Census.NC2.Ly
public import CFSG.Certificates.Kernel.NC2LSound

public section

namespace CertificateChecks.KernelNC2.Ly

open CFSG.Blueprint

theorem facts : ∃ (t g x : NativeSporadic.Ly) (S : Subgroup NativeSporadic.Ly),
    orderOf t = 2 ∧ S ≤ Subgroup.centralizer {t} ∧ Nat.card S = 2 ^ 8 ∧
    g ∈ Subgroup.centralizer {t} ∧ x ∈ Subgroup.centralizer {t} ∧ x ≠ 1 ∧ Odd (orderOf x) ∧
    ∀ s ∈ S ⊓ S.map (MulAut.conj g).toMonoidHom, x * s = s * x := by
  have : Finite NativeSporadic.Ly := inferInstance
  obtain ⟨t, g, x, S, h1, h2, h3, h4, h5, h6, h7, h8, -⟩ :=
    CFSG.KC.NC2L.nc2L_facts L.lay_ok (p := 5) (d := 111) rfl rfl L.decA L.decB L.LA_eq L.LB_eq
      (C := fun i => P.CL.getD i ⟨0, [], []⟩) (S := fun i => P.SL.getD i []) rfl
      (by rw [m_eq]; exact chain) nc2_K
  exact ⟨t, g, x, S, h1, h2, h3, h4, h5, h6, h7, h8⟩

end CertificateChecks.KernelNC2.Ly

end
