module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7FactsInputs
public import CFSG.Certificates.Kernel.PermCent.AllPermsCSound
import CFSG.Certificates.Kernel.PermCent.CVSound
import CFSG.GH74.GLS.C3.Prop121.MooreFinite7
public import Certificates.Data.Kernel.PermCent.SmallK

public section

namespace CertificateChecks.KernelDirect.C9320

open CFSG.ClassicalInvolution.Hat2A7 CFSG.Certificates.Kernel.PkCV

@[expose] noncomputable def a7PowB : Bool :=
  (allPermsP 7 inferInstance).all fun x => x.2 || powOneC x.1 1 || powOneC x.1 2 ||
    powOneC x.1 3 || powOneC x.1 4 || powOneC x.1 5 || powOneC x.1 6 || powOneC x.1 7

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem a7PowB_eq : a7PowB = true := by
  decide +kernel

theorem a7_pow_le_seven :
    ∀ y : A7, y ^ 1 = 1 ∨ y ^ 2 = 1 ∨ y ^ 3 = 1 ∨ y ^ 4 = 1 ∨ y ^ 5 = 1 ∨ y ^ 6 = 1 ∨
      y ^ 7 = 1 := by
  intro y
  have hm := CFSG.GH74.GLS.C3.Prop121.mem_allPerms 7 (y : Equiv.Perm (Fin 7))
  rw [allPerms_eq 7 inferInstance, List.mem_map] at hm
  obtain ⟨x, hx, hxy⟩ := hm
  have hp := par_of_mem_allPermsP hx
  have hs : Equiv.Perm.sign (y : Equiv.Perm (Fin 7)) = 1 := Equiv.Perm.mem_alternatingGroup.1 y.2
  have h1 := List.all_eq_true.1 a7PowB_eq x hx
  rw [hp, hxy, hs] at h1
  have hk : ∀ k, powOneC x.1 k = true → y ^ k = 1 := by
    intro k hk
    rw [powOneC_eq, decide_eq_true_iff] at hk
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← hxy, ev_pow', hk, ev_one, Subgroup.coe_one]
  simp only [Bool.or_eq_true] at h1
  rcases h1 with (((((((h0 | h1) | h2) | h3) | h4) | h5) | h6) | h7)
  · exact absurd (of_decide_eq_true h0) (by decide)
  · exact Or.inl (hk 1 h1)
  · exact Or.inr (Or.inl (hk 2 h2))
  · exact Or.inr (Or.inr (Or.inl (hk 3 h3)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (hk 4 h4))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hk 5 h5)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hk 6 h6))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hk 7 h7))))))

end CertificateChecks.KernelDirect.C9320
