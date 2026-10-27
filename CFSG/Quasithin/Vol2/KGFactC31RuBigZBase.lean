
module

public import CFSG.Quasithin.Vol2.KGFactC31RuRefDefs

@[expose] public section

namespace CFSG.Quasithin.KGC31.Ru

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.Sporadic.RuSchreier CFSG.Quasithin.KGC31

section Facts

theorem mem_ruC_of_centralizer
    {U : Subgroup (Equiv.Perm (Fin 4060))} (hz : ruZ ∈ U)
    {g : Equiv.Perm (Fin 4060)} (hg : g ∈ ruP) (hc : g ∈ Subgroup.centralizer (U : Set _)) :
    g ∈ ruC := by
  rw [ruC_eq_centralizer]
  exact ⟨hg, Subgroup.mem_centralizer_singleton_iff.mpr
    (Subgroup.mem_centralizer_iff.mp hc ruZ hz).symm⟩

theorem centB_of_mem {k : ℕ} {v : Fin k → Equiv.Perm (Fin 4060)} {g : Equiv.Perm (Fin 4060)}
    (hc : g ∈ Subgroup.centralizer (refSub v : Set _)) : CentB v g := fun i =>
  (Subgroup.mem_centralizer_iff.mp hc (v i) (Subgroup.subset_closure ⟨i, rfl⟩)).symm

end Facts

end CFSG.Quasithin.KGC31.Ru

end
