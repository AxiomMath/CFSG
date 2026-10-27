module

public import Certificates.Kernel.Census.NC2.Suz
public import CFSG.Certificates.Kernel.NC2LSound

public section

namespace CertificateChecks.KernelNC2.Suz

open CFSG.Blueprint

theorem facts : ∃ (t g x : NativeSporadic.Suz) (S : Subgroup NativeSporadic.Suz),
    orderOf t = 2 ∧ S ≤ Subgroup.centralizer {t} ∧ Nat.card S = 2 ^ 9 ∧
    g ∈ Subgroup.centralizer {t} ∧ x ∈ Subgroup.centralizer {t} ∧ x ≠ 1 ∧ Odd (orderOf x) ∧
    (∀ s ∈ S ⊓ S.map (MulAut.conj g).toMonoidHom, x * s = s * x) ∧
    7 ∣ Nat.card (Subgroup.centralizer ({t} : Set NativeSporadic.Suz)) := by
  have : Finite NativeSporadic.Suz := inferInstance
  obtain ⟨t, g, x, S, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
    CFSG.KC.NC2L.nc2L_facts L.lay_ok (p := 3) (d := 64) rfl rfl L.decA L.decB L.LA_eq L.LB_eq
      (C := fun i => P.CL.getD i ⟨0, [], []⟩) (S := fun i => P.SL.getD i []) rfl
      (by rw [m_eq]; exact chain) nc2_K
  exact ⟨t, g, x, S, h1, h2, h3, h4, h5, h6, h7, h8, h9 7 (List.mem_singleton.2 rfl)⟩

end CertificateChecks.KernelNC2.Suz

end
