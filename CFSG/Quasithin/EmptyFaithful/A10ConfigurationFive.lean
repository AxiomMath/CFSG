module

public import CFSG.Quasithin.EmptyFaithful.A10ConfigurationCaseX

public section

namespace CFSG.Quasithin.A10

open CFSG.Open CFSG.Quasithin

variable {G : Type*} [Group G]

namespace Emb

variable {T M : Subgroup G} (E : Emb G T M)

theorem centralizer_z_ne_T [Finite G] (hG : IsSimpleGroup G) (hT : quasithinIsSylowTwo T)
    (hM : quasithinIsMaxTwoLocal M) : Subgroup.centralizer ({E.z} : Set G) ≠ T := by
  intro hGz
  have hnwc := E.not_weakly_closed hG hT hGz
  have hzK := E.zK_eq_full hT hM hGz hnwc
  have hK := E.card_K hT hM hGz hnwc
  obtain ⟨c, hcK, hcY, hc3⟩ := E.exists_c hzK hK
  exact E.false_of_caseB hG ⟨hT, hM, hGz, hzK⟩ hK hcK hcY hc3

theorem T_le_centralizer_z : T ≤ Subgroup.centralizer ({E.z} : Set G) := by
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  subst hh
  exact (E.z_central hy).symm

theorem mem_T_of_mem_M_centralizer_z {y : G} (hyM : y ∈ M) (hy : y * E.z = E.z * y) : y ∈ T := by
  obtain ⟨w, rfl⟩ := E.mem_M.1 hyM
  have hw : w * z0 = z0 * w := E.injective (by rw [map_mul, map_mul]; exact hy)
  exact E.mem_T_iff.2 ⟨w, centralizer_z0_Wc w hw, rfl⟩

theorem lemma_13_9_5 [Finite G] (hG : IsSimpleGroup G) (hT : quasithinIsSylowTwo T)
    (hM : quasithinIsMaxTwoLocal M) :
    T < Subgroup.centralizer ({E.z} : Set G) ∧ ¬ Subgroup.centralizer ({E.z} : Set G) ≤ M := by
  have hlt : T < Subgroup.centralizer ({E.z} : Set G) :=
    lt_of_le_of_ne E.T_le_centralizer_z (E.centralizer_z_ne_T hG hT hM).symm
  refine ⟨hlt, fun hle => ?_⟩
  apply E.centralizer_z_ne_T hG hT hM
  refine le_antisymm (fun y hy => ?_) E.T_le_centralizer_z
  exact E.mem_T_of_mem_M_centralizer_z (hle hy) ((Subgroup.mem_centralizer_iff.mp hy E.z rfl).symm)

end Emb

end CFSG.Quasithin.A10
