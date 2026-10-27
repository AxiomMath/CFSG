
module

public import CFSG.Quasithin.Vol2.KGFactC31RuBigZBase

public import CFSG.Quasithin.Vol2.KGFactC31RuRef

public section

namespace CFSG.Quasithin.KGC31.Ru

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.Sporadic.RuSchreier CFSG.Quasithin.KGC31

section Facts

theorem bigZ_all :
    ∀ g ∈ ruC, BigZ g :=
  Certificates.certificate7233.2

theorem centralizer64_le : ruP ⊓ Subgroup.centralizer (u64 : Set (Equiv.Perm (Fin 4060))) ≤ u64 :=
  fun _ ⟨hg, hc⟩ => (bigZ_all _ (mem_ruC_of_centralizer ruZ_mem_u64 hg hc)).2.1 (centB_of_mem hc)

theorem centralizer3_le : ruP ⊓ Subgroup.centralizer (u3 : Set (Equiv.Perm (Fin 4060))) ≤ u64 :=
  fun _ ⟨hg, hc⟩ => (bigZ_all _ (mem_ruC_of_centralizer ruZ_mem_u3 hg hc)).2.2.1 (centB_of_mem hc)

theorem mem_V32E_of {g : Equiv.Perm (Fin 4060)} (hg : g ∈ ruP)
    (hc : g ∈ Subgroup.centralizer (uE : Set (Equiv.Perm (Fin 4060)))) (h2 : g * g = 1)
    (ho : OrbComm xE g 3) : g ∈ uV32E :=
  (bigZ_all _ (mem_ruC_of_centralizer ruZ_mem_uE hg hc)).1 (centB_of_mem hc) h2 ho

theorem pow_centralizer16 {g : Equiv.Perm (Fin 4060)} (hg : g ∈ ruP)
    (hc : g ∈ Subgroup.centralizer (u16 : Set (Equiv.Perm (Fin 4060)))) : g ^ 2 ^ 7 = 1 :=
  ((bigZ_all _ (mem_ruC_of_centralizer ruZ_mem_u16 hg hc)).2.2.2.1 (centB_of_mem hc)).1

theorem conj_g16_centralizer16 {g : Equiv.Perm (Fin 4060)} (hg : g ∈ ruP)
    (hc : g ∈ Subgroup.centralizer (u16 : Set (Equiv.Perm (Fin 4060)))) :
    g16 * g * g16⁻¹ ∈ Subgroup.centralizer (u16 : Set (Equiv.Perm (Fin 4060))) := by
  have h := ((bigZ_all _ (mem_ruC_of_centralizer ruZ_mem_u16 hg hc)).2.2.2.1
    (centB_of_mem hc)).2.1
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  have hle : u16 ≤ Subgroup.centralizer {g16 * g * g16⁻¹} :=
    refSub_le_of_forall fun i => Subgroup.mem_centralizer_singleton_iff.mpr (h i).symm
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hu)

theorem mem_V32p_of {g : Equiv.Perm (Fin 4060)} (hg : g ∈ ruP)
    (hc : g ∈ Subgroup.centralizer (u16 : Set (Equiv.Perm (Fin 4060)))) (h2 : g * g = 1)
    (ho : OrbComm x16 g 2) : g ∈ uV32p :=
  ((bigZ_all _ (mem_ruC_of_centralizer ruZ_mem_u16 hg hc)).2.2.2.1 (centB_of_mem hc)).2.2 h2 ho

theorem pow_normalizer16 {g : Equiv.Perm (Fin 4060)} (hg : g ∈ ruC)
    (hn : g ∈ Subgroup.normalizer (u16 : Set (Equiv.Perm (Fin 4060)))) : g ^ 2 ^ 10 = 1 := by
  refine (bigZ_all _ hg).2.2.2.2.1 fun i => ?_
  have h := (Subgroup.mem_normalizer_iff.mp hn (v16 i)).mp (Subgroup.subset_closure ⟨i, rfl⟩)
  rw [show u16 = refSub v16 from rfl, refSub_eq hv16, mem_eSub_iff] at h
  exact h

theorem pow_centralizer32 {g : Equiv.Perm (Fin 4060)} (hg : g ∈ ruP)
    (hc : g ∈ Subgroup.centralizer (u32 : Set (Equiv.Perm (Fin 4060)))) : g ^ 2 ^ 7 = 1 :=
  ((bigZ_all _ (mem_ruC_of_centralizer ruZ_mem_u32 hg hc)).2.2.2.2.2 (centB_of_mem hc)).1

theorem mem_u32_of {g : Equiv.Perm (Fin 4060)} (hg : g ∈ ruP)
    (hc : g ∈ Subgroup.centralizer (u32 : Set (Equiv.Perm (Fin 4060)))) (h2 : g * g = 1)
    (ho : OrbComm x32 g 2) : g ∈ u32 :=
  ((bigZ_all _ (mem_ruC_of_centralizer ruZ_mem_u32 hg hc)).2.2.2.2.2 (centB_of_mem hc)).2 h2 ho

end Facts

end CFSG.Quasithin.KGC31.Ru

end
