module

public import CFSG.Quasithin.Background.F7TwoInvL2Model
public import CFSG.Quasithin.Background.F7TwoInvSQTKFam
public import CFSG.Quasithin.Background.F7TwoInvTitsCheck
public import CFSG.Quasithin.Background.F7TwoInvTitsGen
public import CFSG.Sporadic.Schreier.TitsAutD
public import CFSG.Sporadic.Schreier.TitsOuter

public section

namespace CFSG.Quasithin.F7Two

open CFSG.Sporadic.Schreier.Tits CFSG.Blueprint


theorem titsD_involutory_aut_inner {φ : MulAut titsD} (h2 : φ * φ = 1) (h1 : φ ≠ 1) :
    ∃ u : titsD, orderOf u = 2 ∧ φ = MulAut.conj u := by
  obtain ⟨a, rfl⟩ := (titsConjEquiv : titsA ≃* MulAut titsD).surjective φ
  have hsq : a * a = 1 := titsConjEquiv.injective (by rw [map_mul, map_one]; exact h2)
  have hord : orderOf (a : Equiv.Perm (Fin 1755)) = 2 :=
    orderOf_eq_prime
      (by rw [sq]; exact congrArg (fun v : titsA => (v : Equiv.Perm (Fin 1755))) hsq)
      (fun h => h1 (by rw [show a = 1 from Subtype.ext h, map_one]))
  refine ⟨⟨a, titsA_involution_mem_D a.2 hord⟩, by rw [← Subgroup.orderOf_coe]; exact hord,
    MulEquiv.ext fun d => Subtype.ext ?_⟩
  exact (coe_titsConj_apply a d).trans (by simp [MulAut.conj_apply])

theorem invAutGenFamTits : InvAutGenFamTits := by
  intro S _ _ hS
  obtain ⟨e⟩ := titsModelEquiv S 2 1 hS
  refine invAutGen_of_mulEquiv_forall e fun φ h2 h1 => ?_
  obtain ⟨u, hu2, rfl⟩ := titsD_involutory_aut_inner h2 h1
  rcases titsD_involution_conj u hu2 with h | h
  · exact invAutGen_titsD_conj_of_check (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      invTitsZCheck h
  · exact invAutGen_titsD_conj_of_check (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      invTitsTCheck h

end CFSG.Quasithin.F7Two
