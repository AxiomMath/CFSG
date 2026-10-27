module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qStructTwoOut
public import CFSG.Quasithin.Vol2.GoldschmidtF431SpLift

public section

namespace CFSG.Quasithin.H13.F431.Un

open CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13.F431
  CFSG.Quasithin.H13.F431.D4q.Struct
open CFSG.QuasithinUnique.Setup.Layer (isSylowTwoOf_map_mulEquiv)

universe u v

section Chain

variable {Mb : Type u} [Group Mb] {Mb' : Type v} [Group Mb'] (θ : Mb ≃* Mb')
  {T N N' : Subgroup Mb}

theorem unOut_chain_map {i j : Mb} (h : Relation.ReflTransGen (fun a b : Mb => a ∈ T ∧ b ∈ T ∧
      ((∃ m ∈ N, m * a * m⁻¹ = b) ∨ (∃ m ∈ N', m * a * m⁻¹ = b))) i j) :
    Relation.ReflTransGen (fun a b : Mb' => a ∈ T.map θ.toMonoidHom ∧ b ∈ T.map θ.toMonoidHom ∧
      ((∃ m ∈ N.map θ.toMonoidHom, m * a * m⁻¹ = b) ∨
        (∃ m ∈ N'.map θ.toMonoidHom, m * a * m⁻¹ = b))) (θ i) (θ j) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih =>
    refine ih.tail ⟨Subgroup.mem_map_of_mem _ hs.1, Subgroup.mem_map_of_mem _ hs.2.1, ?_⟩
    rcases hs.2.2 with ⟨m, hm, e⟩ | ⟨m, hm, e⟩
    · exact Or.inl ⟨θ m, Subgroup.mem_map_of_mem _ hm, by simpa using congrArg θ e⟩
    · exact Or.inr ⟨θ m, Subgroup.mem_map_of_mem _ hm, by simpa using congrArg θ e⟩

theorem unOut_centerOf_pCoreOf_map (X : Subgroup Mb) :
    centerOf (pCoreOf 2 (X.map θ.toMonoidHom)) = (centerOf (pCoreOf 2 X)).map θ.toMonoidHom := by
  rw [pCoreOf_map_of_injective θ.toMonoidHom θ.injective, centerOf_map_eq]

theorem unOut_centerOf_perfectCore_map (X : Subgroup Mb) :
    centerOf (perfectCore (X.map θ.toMonoidHom)) =
      (centerOf (perfectCore X)).map θ.toMonoidHom := by
  rw [perfectCore_map_of_injective θ.toMonoidHom θ.injective, centerOf_map_eq]

theorem unOut_map_comap (E : Subgroup Mb') : (E.comap θ.toMonoidHom).map θ.toMonoidHom = E :=
  Subgroup.map_comap_eq_self_of_surjective θ.surjective E

end Chain

end CFSG.Quasithin.H13.F431.Un
