module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.RankThree.PartTwo.Sec19.F194Item316Glue

public section

namespace CFSG.RankThree.PartTwo.Sec19.SimsTheoremC

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo

@[expose] def sigma6 : alternatingGroup (Fin 6) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 4 5, by
    rw [Equiv.Perm.mem_alternatingGroup]
    simp [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap]⟩

theorem orderOf_sigma6 : orderOf sigma6 = 4 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide +kernel, fun m hm hm0 => ?_⟩
  interval_cases m <;> decide +kernel

theorem exists_orderOf_eq_four_alternatingGroup {n : ℕ} (hn : 6 ≤ n) :
    ∃ g : alternatingGroup (Fin n), orderOf g = 4 := by
  classical
  let f : Equiv.Perm (Fin 6) →* Equiv.Perm (Fin n) := Equiv.Perm.viaEmbeddingHom (Fin.castLEEmb hn)
  have hf : Function.Injective f := Equiv.Perm.viaEmbeddingHom_injective (Fin.castLEEmb hn)
  have hmem : f (sigma6 : Equiv.Perm (Fin 6)) ∈ alternatingGroup (Fin n) := by
    rw [Equiv.Perm.mem_alternatingGroup]
    show Equiv.Perm.sign (Equiv.Perm.viaEmbeddingHom (Fin.castLEEmb hn)
      (sigma6 : Equiv.Perm (Fin 6))) = 1
    rw [Equiv.Perm.viaEmbeddingHom_apply, Equiv.Perm.viaEmbedding, Equiv.Perm.sign_extendDomain]
    exact sigma6.2
  refine ⟨⟨_, hmem⟩, ?_⟩
  rw [Subgroup.orderOf_mk, orderOf_injective f hf, Subgroup.orderOf_coe, orderOf_sigma6]

variable {G : Type} [Group G] [Finite G]

end CFSG.RankThree.PartTwo.Sec19.SimsTheoremC
