module

public import CFSG.Sporadic.Th.Recog.FibreExists
public import CFSG.Sporadic.Th.Recog.HIsoM
public import CFSG.Sporadic.Th.Recog.OneClass
public import CFSG.Sporadic.Th.Recog.MFactsA

public section

namespace CFSG.Sporadic.Th.Recog

open CFSG.Sporadic.Th

variable {G : Type} [Group G] [Finite G]

theorem centralizer_z_eq_M : Subgroup.centralizer ({Max3.z} : Set J) = Max3.M := by
  rw [Max3.z_eq_a]
  exact Kernel.centralizer_a_eq_M th_kernel_facts

variable {S : ThSetting G}

theorem FibreData.exists_mulEquiv (Fd : FibreData S) :
    ∃ e : S.toSetting.M ≃* Max3.M, ∀ h, (h, e h) ∈ Fd.F :=
  Fd.exists_mulEquiv_of exists_sqrt_z_comm_q0 (fun _ hn => cycleType_kap_ne_of_mul_self hn)
    exists_conj_q0_eq_mul_z exists_swap_z_q0 centralizer_z_eq_M

theorem FibreData.all_involutions_conj (Fd : FibreData S) :
    ∀ j : G, orderOf j = 2 → ∃ g : G, g * S.z * g⁻¹ = j := by
  obtain ⟨e, he⟩ := Fd.exists_mulEquiv
  exact Fd.all_involutions_conj_of e he card_centralizer_q0 ncard_involutions_centralizer_q0
    exists_not_commute_centralizer_q0 Fd.exists_swap

@[expose] noncomputable def ThSetting.core (S : ThSetting G) (hBB : A9FaithfulDimEight) :
    ThCore G where
  z := S.z
  ψ := (exists_fibreData S hBB).some.exists_mulEquiv.choose.symm
  conj := (exists_fibreData S hBB).some.all_involutions_conj

end CFSG.Sporadic.Th.Recog

end
