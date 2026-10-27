module

public import CFSG.Quasithin.H13.L32AC52a
public import CFSG.Quasithin.H13.L32AC51h
public import CFSG.Quasithin.EmptyFaithful.SBc11List

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open Equiv Equiv.Perm

namespace Lin

theorem isPSL_of_mulEquiv {X : Type} [Group X] {m : ℕ} (hm : 3 ≤ m) (e : X ≃* SLn m) :
    IsPSL m 2 1 X := by
  refine ⟨⟨Nat.prime_two, le_rfl, by omega, fun h => ?_, fun h => ?_⟩, ZMod 2, inferInstance,
    inferInstance, by rw [card_zmod_two, pow_one],
    ⟨e.trans (CFSG.QuasithinUnique.Vol2Native.A312L.slEquivStatedProj card_zmod_two m)⟩⟩
  · have := congrArg Prod.fst h
    simp only at this
    omega
  · have := congrArg Prod.fst h
    simp only at this
    omega

end Lin

theorem alt_small_solvable {n : ℕ} (hn : n ≤ 4) : Group.IsSolvable ↥(alternatingGroup (Fin n)) := by
  refine isSolvable_of_isTwoThree ?_
  have h1 : Nat.card ↥(alternatingGroup (Fin n)) ∣ 24 := by
    have h2 := Subgroup.card_subgroup_dvd_card (alternatingGroup (Fin n))
    rw [Nat.card_perm, Nat.card_fin] at h2
    exact h2.trans ((Nat.factorial_dvd_factorial hn).trans (by decide))
  exact IsTwoThree.of_dvd (⟨3, 1, by norm_num⟩ : IsTwoThree 24) h1

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

theorem false_of_alt_small {K : Subgroup G} (hK : K ∈ cComp H) {n : ℕ} (hn : n ≤ 4)
    (hA : IsAlt n (cStar K)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨φ⟩ := hA
  have hsA := alt_small_solvable hn
  have hsK : Group.IsSolvable (cStar K) :=
    Group.isSolvable_of_isSolvable_injective (f := φ.toMonoidHom) φ.injective
  have hN : Group.IsSolvable ↥((pCoreOf 2 K).subgroupOf K) := by
    have hp : IsPGroup 2 ↥((pCoreOf 2 K).subgroupOf K) :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K).comap_of_injective K.subtype
        K.subtype_injective
    have := hp.isNilpotent
    infer_instance
  have hsol : Group.IsSolvable ↥K :=
    Group.isSolvable_of_ker_le_range ((pCoreOf 2 K).subgroupOf K).subtype
      (QuotientGroup.mk' ((pCoreOf 2 K).subgroupOf K)) (by
        rw [QuotientGroup.ker_mk', Subgroup.range_subtype])
  have h1 := (isSolvable_iff_perfectCore_eq_bot K).mp hsol
  rw [perfectCore_eq_self_of_perfect (perfect_of_mem_cComp hK)] at h1
  exact ne_bot_of_mem_cComp hK h1

theorem kstar_cases (h47 : Lemma14_7_47) (h49 : Lemma14_7_49) (h50 : Lemma14_7_50)
    (h51 : Lemma14_7_51) (S : Setting147 G T L V H) {K : Subgroup G} (hK : K ∈ cComp H) :
    IsAlt 5 (cStar K) ∨ IsPSU 3 3 1 (cStar K) := by
  rcases (h47 _ T L V H S K hK).2 with ⟨n, hP⟩ | ⟨n, hA⟩ | hU
  · exact absurd hP (h51 _ T L V H S K hK n)
  · rcases (by omega : n ≤ 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ 9 ≤ n) with
      hn | rfl | rfl | rfl | rfl | hn
    · exact (false_of_alt_small hK hn hA).elim
    · exact Or.inl hA
    · exact absurd hA (h49 _ T L V H S K hK).2
    · exact absurd hA (h50 _ T L V H S K hK)
    · obtain ⟨φ⟩ := hA
      exact absurd (Lin.isPSL_of_mulEquiv (m := 4) (by norm_num)
        (φ.trans Lin.slFourEquivAlt8.symm)) (h51 _ T L V H S K hK 4)
    · exact (false_of_alt_nine_le S hK hn hA).elim
  · exact Or.inr hU

end CFSG.Quasithin.H13.L32A.C
