module

import CFSG.Quasithin.SteinbergBSNaturalPlaneRoot
public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellSL2
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.Quasithin.SteinbergBK

open Subgroup Matrix CFSG CFSG.QuasithinUnique.Setup.Campbell
open scoped LinearAlgebra.Projectivization commutatorElement

variable {G : Type*} [Group G]

variable {k : Type*} [Field k] [Finite k]

theorem pCore_two_specialLinearGroup_eq_bot {n : ℕ} (hn : 1 ≤ n) (hk : Nat.card k = 2 ^ n) :
    pCore 2 (SpecialLinearGroup (Fin 2) k) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 (SpecialLinearGroup (Fin 2) k)))
  obtain ⟨ℓ, hℓ⟩ := SteinbergBS.exists_rootGrp_eq_map_sylow hn hk (MonoidHom.id _)
    Function.surjective_id S
  rw [Subgroup.map_id] at hℓ
  have hTS : pCore 2 (SpecialLinearGroup (Fin 2) k) ≤ (S : Subgroup _) := by
    have hsup : IsPGroup 2 ((S : Subgroup (SpecialLinearGroup (Fin 2) k)) ⊔
        pCore 2 (SpecialLinearGroup (Fin 2) k) : Subgroup _) :=
      IsPGroup.to_sup_of_normal_right S.isPGroup' pCore_isPGroup
    exact sup_eq_left.mp (S.is_maximal' hsup le_sup_left)
  obtain ⟨m, hm⟩ := exists_ne_point ℓ
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (SpecialLinearGroup (Fin 2) k) ℓ m
  rw [eq_bot_iff, ← rootGrp_inf_rootGrp (Ne.symm hm)]
  intro x hx
  refine ⟨hℓ ▸ hTS hx, ?_⟩
  change x ∈ rootGrp m
  rw [← hg, mem_rootGrp_smul_iff, ← hℓ]
  apply hTS
  have := (pCore_normal (p := 2) (G := SpecialLinearGroup (Fin 2) k)).conj_mem x hx g⁻¹
  simpa using this

variable {X : Type*} [Group X]

end CFSG.Quasithin.SteinbergBK
