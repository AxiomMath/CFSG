module

public import CFSG.Quasithin.AppendixH.H9.ModelBasic
public import CFSG.Quasithin.AppendixH.H9.H92.ConjTransport.ConjugateStructure

public section

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open

private theorem conj_inv_mem_Lg {n : ℕ} {g : MulAut (PairN n)} (hg : g ∈ Mg n)
    {l : MulAut (PairN n)} (hl : l ∈ Lg n) : g⁻¹ * l * g ∈ Lg n := by
  simpa using conj_mem_Lg ((Mg n).inv_mem hg) hl

theorem conjAut_Lg_eq_of_mem_Mg {n : ℕ} {g : MulAut (PairN n)} (hg : g ∈ Mg n) :
    conjAut g (Lg n) = Lg n :=
  conjAut_eq_self_of_conj_mem (fun _ hl => conj_mem_Lg hg hl) (fun _ hl => conj_inv_mem_Lg hg hl)

end CFSG.ASVolI.ChH
