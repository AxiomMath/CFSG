module

public import Certificates.Kernel.Census.NC2.ON
public import CFSG.Certificates.Kernel.NC2LSound

public section

namespace CertificateChecks.KernelNC2.ON

open CFSG.Blueprint

theorem facts : ∃ (t g x : NativeSporadic.ON) (S : Subgroup NativeSporadic.ON),
    orderOf t = 2 ∧ S ≤ Subgroup.centralizer {t} ∧ Nat.card S = 2 ^ 9 ∧
    g ∈ Subgroup.centralizer {t} ∧ x ∈ Subgroup.centralizer {t} ∧ x ≠ 1 ∧ Odd (orderOf x) ∧
    ∀ s ∈ S ⊓ S.map (MulAut.conj g).toMonoidHom, x * s = s * x := by
  have : Finite NativeSporadic.ON := inferInstance
  obtain ⟨t, g, x, S, h1, h2, h3, h4, h5, h6, h7, h8, -⟩ :=
    CFSG.KC.NC2L.nc2L_facts L.lay_ok (p := 3) (d := 154) rfl rfl L.decA L.decB L.LA_eq L.LB_eq
      (C := fun i => P.CL.getD i ⟨0, [], []⟩) (S := fun i => P.SL.getD i []) rfl
      (by rw [m_eq]; exact chain) nc2_K
  exact ⟨t, g, x, S, h1, h2, h3, h4, h5, h6, h7, h8⟩

end CertificateChecks.KernelNC2.ON

end
