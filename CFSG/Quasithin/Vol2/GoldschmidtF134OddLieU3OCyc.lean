module

public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieCfg
public import CFSG.LocalAnalysis.SectionRank.OddCover.CyclicSylow
public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.Quasithin.H13.NQCore.U3O

open CFSG.Assembly.LowTwoRank

theorem isCyclic_of_isPGroup_of_surjective {G G' : Type*} [Group G] [Finite G] [Group G']
    {f : G →* G'} (hf : Function.Surjective f) {p : ℕ} [Fact p.Prime]
    (hG : ∀ P : Sylow p G, IsCyclic (P : Subgroup G)) (Q : Subgroup G') (hQ : IsPGroup p Q) :
    IsCyclic Q := by
  have : Finite G' := Finite.of_surjective f hf
  obtain ⟨S', hS'⟩ := hQ.exists_le_sylow
  obtain ⟨S, rfl⟩ := Sylow.mapSurjective_surjective hf p S'
  have : IsCyclic (S : Subgroup G) := hG S
  have : IsCyclic ((S : Subgroup G).map f) :=
    isCyclic_of_surjective (f.subgroupMap S) (MonoidHom.subgroupMap_surjective f S)
  have hS'' : Q ≤ (S : Subgroup G).map f := by
    rw [← Sylow.coe_mapSurjective hf S]
    exact hS'
  exact Subgroup.isCyclic_of_le hS''

theorem isCyclic_of_isPGroup {X : Type} [Group X] {r p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hpr : p ≠ r) (hp1 : ¬ p ∣ r + 1) (hX : StatedClassicalModel X .PSU 3 r 1)
    (Q : Subgroup X) (hQ : IsPGroup p Q) : IsCyclic Q := by
  obtain ⟨⟨hr, -⟩, K, _, _, hK, ⟨e⟩⟩ := hX
  rw [pow_one] at hK
  have hcyc := (CFSG.SectionRank.OddCover.prime_classical_three_cyclic_odd_sylows hr (ε := -1)
    (H := StatedSU 3 (r ^ 1) K) (Or.inr ⟨rfl, hK, by rw [pow_one]⟩)).1 p hp2 hpr (by
      intro h
      apply hp1
      have h' : (p : ℤ) ∣ ((r + 1 : ℕ) : ℤ) := by
        push_cast
        simpa using h
      exact_mod_cast h')
  have hQ' : IsPGroup p (Q.map e.toMonoidHom) := hQ.map e.toMonoidHom
  have hc := isCyclic_of_isPGroup_of_surjective (QuotientGroup.mk'_surjective _) hcyc _ hQ'
  exact isCyclic_of_surjective (Q.equivMapOfInjective e.toMonoidHom e.injective).symm.toMonoidHom
    (Q.equivMapOfInjective e.toMonoidHom e.injective).symm.surjective

theorem false_of_not_dvd {X : Type} [Group X] {r p a : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p)
    (hpr : p ≠ r) (hp1 : ¬ p ∣ r + 1) (hX : StatedClassicalModel X .PSU 3 r 1) (ha : 2 ≤ a)
    {Q : Subgroup X} (hQ : Nat.card Q = p ^ a) (hQe : ∀ x ∈ Q, x ^ p = 1) : False := by
  have hpg : IsPGroup p Q := IsPGroup.of_card hQ
  exact not_isCyclic_of_card_pow ha hQ hQe (isCyclic_of_isPGroup (by omega) hpr hp1 hX Q hpg)

end CFSG.Quasithin.H13.NQCore.U3O
