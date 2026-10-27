module

public import CFSG.Quasithin.Vol2.Ch1Comm
import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.Quasithin

namespace R3c23

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_pCoreOf_of_mem_pCore {X : Subgroup G} {x : ↥X} (hx : x ∈ CFSG.pCore 2 ↥X) :
    (x : G) ∈ pCoreOf 2 X := (CFSG.mem_openPCoreOf_iff x).mpr hx

theorem pair_structure {X T L : Subgroup G} (h38 : A38Part3 (↥X ⧸ CFSG.pCore 2 ↥X))
    (hT : IsSylowTwoOf T X) (hL : L ∈ cComp X) (hXeq : X = L ⊔ T)
    (hTN : ¬ T ≤ Subgroup.normalizer (L : Set G)) :
    ∃ t ∈ T, t ∉ Subgroup.normalizer (L : Set G) ∧
      L.map (MulAut.conj t).toMonoidHom ∈ cComp X ∧
      ⁅L, L.map (MulAut.conj t).toMonoidHom⁆ ≤ pCoreOf 2 X ∧
      ∀ x ∈ X, L.map (MulAut.conj x).toMonoidHom = L ∨
        L.map (MulAut.conj x).toMonoidHom = L.map (MulAut.conj t).toMonoidHom := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNn : (CFSG.pCore 2 ↥X).Normal := CFSG.pCore_normal
  have hLX : L ≤ X := le_of_mem_cComp hL
  have hTX : T ≤ X := hT.1
  have hLb := modO2Image_mem_cComp hL
  have hTb := isSylowTwoOf_top_map_of_surjective (isSylowTwoOf_top_subgroupOf hT)
    (QuotientGroup.mk' (CFSG.pCore 2 ↥X)) (QuotientGroup.mk'_surjective _)
  obtain ⟨-, hL2⟩ := h38 _ hLb
  rcases hL2 _ hTb with ⟨hnorm, -, -⟩ | ⟨tb, htbT, htbn, -, hcc, hcomm, -, -, -⟩
  · exfalso
    have hn : (L.subgroupOf X).Normal :=
      normal_of_normal_map_of_mem_cComp (CFSG.pCore 2 ↥X) (isSolvable_pCore_two_group ↥X)
        (subgroupOf_mem_cComp hL) hnorm
    exact hTN (hTX.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hLX).1 hn))
  · obtain ⟨t', ht'T, rfl⟩ := htbT
    have htT : (t' : G) ∈ T := ht'T
    have ht_not : (t' : G) ∉ Subgroup.normalizer (L : Set G) := by
      intro hN
      apply htbn
      have hs'N : t' ∈ Subgroup.normalizer ((L.subgroupOf X : Subgroup ↥X) : Set ↥X) := by
        rw [Subgroup.mem_normalizer_iff]
        intro x
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
        have := Subgroup.mem_normalizer_iff.mp hN (x : G)
        simpa using this
      exact Subgroup.le_normalizer_map (QuotientGroup.mk' (CFSG.pCore 2 ↥X)) ⟨t', hs'N, rfl⟩
    have hLt : L.map (MulAut.conj (t' : G)).toMonoidHom ∈ cComp X :=
      map_conj_mem_cComp hL t'.2
    have hLtX := le_of_mem_cComp hLt
    refine ⟨(t' : G), htT, ht_not, hLt, ?_, ?_⟩
    · rw [Subgroup.commutator_le]
      intro a ha b hb
      have haX := hLX ha
      have hbX := hLtX hb
      have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥X) ⟨a, haX⟩ ∈ modO2Image X L :=
        ⟨⟨a, haX⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
      have h2 : QuotientGroup.mk' (CFSG.pCore 2 ↥X) ⟨b, hbX⟩ ∈
          (modO2Image X L).map
            (MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥X) t')).toMonoidHom := by
        rw [← modO2Image_conj t']
        exact ⟨⟨b, hbX⟩, Subgroup.mem_subgroupOf.mpr hb, rfl⟩
      have h3 := Subgroup.commutator_mem_commutator h1 h2
      rw [hcomm, Subgroup.mem_bot, ← map_commutatorElement, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff] at h3
      exact mem_pCoreOf_of_mem_pCore h3
    · intro x hx
      have hLx : L.map (MulAut.conj x).toMonoidHom ∈ cComp X := map_conj_mem_cComp hL hx
      have hLxb := modO2Image_mem_cComp hLx
      have htop : modO2Image X L ⊔ (T.subgroupOf X).map (QuotientGroup.mk' (CFSG.pCore 2 ↥X)) =
          ⊤ := by
        unfold modO2Image
        rw [← Subgroup.map_sup, ← Subgroup.subgroupOf_sup hLX hTX, ← hXeq,
          Subgroup.subgroupOf_self, Subgroup.map_top]
        exact MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)
      rw [htop] at hcc
      rw [hcc] at hLxb
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hLxb
      rcases hLxb with h | h
      · exact Or.inl (modO2Image_injOn X hLx hL h)
      · exact Or.inr (modO2Image_injOn X hLx hLt (h.trans (modO2Image_conj t').symm))

end R3c23

end CFSG.Quasithin
