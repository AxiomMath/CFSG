module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.RankThree.PartOne.SolD3

@[expose] def SylowSpecial (G : Type*) [Group G] : Prop :=
  ∀ Q : Sylow 2 G, Subgroup.center ↥(Q : Subgroup G) ≤ commutator ↥(Q : Subgroup G)

theorem map_commutator_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (commutator A).map e.toMonoidHom = commutator B := by
  rw [commutator, commutator, Subgroup.map_commutator,
    Subgroup.map_top_of_surjective _ e.surjective]

theorem center_le_commutator_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : Subgroup.center A ≤ commutator A) : Subgroup.center B ≤ commutator B := by
  intro z hz
  have h1 : e.symm z ∈ Subgroup.center A := by
    rw [← Subgroup.map_center_eq e.symm]
    exact Subgroup.mem_map_of_mem e.symm.toMonoidHom hz
  have h2 : e (e.symm z) ∈ (commutator A).map e.toMonoidHom := ⟨e.symm z, h h1, rfl⟩
  rw [map_commutator_mulEquiv] at h2
  simpa using h2

theorem SylowSpecial.map_mulEquiv {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    (hG : SylowSpecial G) (e : G ≃* H) : SylowSpecial H := by
  intro Q
  let S := Q.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hmap : (S : Subgroup G).map e.toMonoidHom = (Q : Subgroup H) := by
    simp [S, Subgroup.map_map]
  let eS : ↥(S : Subgroup G) ≃* ↥(Q : Subgroup H) :=
    (e.subgroupMap (S : Subgroup G)).trans (MulEquiv.subgroupCongr hmap)
  exact center_le_commutator_of_mulEquiv eS (hG S)

theorem SylowSpecial.of_one {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (h : Subgroup.center ↥(S : Subgroup G) ≤ commutator ↥(S : Subgroup G)) : SylowSpecial G := by
  intro Q
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S Q
  have hmap : (S : Subgroup G).map (MulAut.conj g).toMonoidHom = (Q : Subgroup G) := by
    change (g • S : Sylow 2 G).toSubgroup = Q.toSubgroup
    rw [hg]
  let eS : ↥(S : Subgroup G) ≃* ↥(Q : Subgroup G) :=
    ((MulAut.conj g).subgroupMap (S : Subgroup G)).trans (MulEquiv.subgroupCongr hmap)
  exact center_le_commutator_of_mulEquiv eS h

theorem SylowSpecial.of_card {G : Type*} [Group G] [Finite G] (R : Subgroup G)
    (hcard : Nat.card ↥R = 2 ^ (Nat.card G).factorization 2)
    (h : Subgroup.center ↥R ≤ commutator ↥R) : SylowSpecial G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact SylowSpecial.of_one (Sylow.ofCard R hcard) h

end CFSG.RankThree.PartOne.SolD3
