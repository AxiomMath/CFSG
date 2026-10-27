module

public import CFSG.Timmesfeld.Bridge.Connectivity
public import CFSG.Timmesfeld.Bridge.StrongEmbedding
public import CFSG.StronglyEmbedded.BenderNormalSeries
public import CFSG.Dihedral.DisconnectedInvolutionGraph.QuaternionRankOne

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Open CFSG.Timmesfeld.Connectivity CFSG.DisconnectedInvolutionGraph.Helpers

theorem isBenderGroup_of_fusionIsBenderGroup {X : Type*} [Group X] (h : fusionIsBenderGroup X) :
    CFSG.BenderSuzuki.IsBenderGroup X := by
  rcases h with ⟨f, hf, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩
  · exact .isPSL2 f hf e
  · have hmodel : CFSG.Theory.Comparator.PSU3Model f = PSU3 2 f := CFSG.Models.benderPSU3Model_eq_psu3 f
    exact .isPSU3 f hf (e.trans (MulEquiv.subgroupCongr hmodel.symm))
  · have hmodel : CFSG.Theory.Comparator.SzModel a = Sz a := CFSG.Models.benderSzModel_eq_sz a
    exact .isSuzuki a ha (e.trans (MulEquiv.subgroupCongr hmodel.symm))

theorem not_orderOf_mul_eq_four_of_fusionIsBenderGroup {X : Type*} [Group X] [Finite X]
    (h : fusionIsBenderGroup X) {s t : X} (hs : orderOf s = 2) (ht : orderOf t = 2) :
    orderOf (s * t) ≠ 4 := by
  obtain ⟨q, k, hB⟩ := exists_fusionBenderBorel_of_isBenderGroup
    (isBenderGroup_of_fusionIsBenderGroup h)
  exact not_orderOf_mul_eq_four (fun Q => (hB Q).1) hs ht

variable {G : Type} [Group G] {D : Set G}

theorem mem_of_odd_index {N : Subgroup G} [N.Normal] (hN : Odd N.index) {x : G}
    (hx : x * x = 1) : x ∈ N := by
  obtain ⟨k, hk⟩ := hN
  have hpow : x ^ N.index ∈ N := Subgroup.pow_index_mem N x
  have hsq : x ^ 2 = 1 := by rw [pow_two, hx]
  rwa [hk, pow_succ, pow_mul, hsq, one_pow, one_mul] at hpow

theorem noCommutingDistinctInvolutions_of_sylow [Finite G]
    (h : ∀ S : Sylow 2 G, IsCyclic (S : Subgroup G) ∨
      ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup G) ≃* QuaternionGroup (2 ^ (r - 2)))) :
    NoCommutingDistinctInvolutions G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 G))
  rcases h S with hcyc | ⟨r, -, he⟩
  · have : IsCyclic (S : Subgroup G) := hcyc
    exact (no_commuting_distinct_involutions_sylow_iff S).2
      fun first second _ => cyclic_involutions_unique first second
  · exact quaternion_sylow_no_commuting_distinct_involutions S (r - 2) he

theorem commConnected_of_noPolar (hA : Asc73Input) (h : Hyp G D) (hNP : Moufang.NoPolar D) :
    Closure.CommConnected D := by
  have := h.finite
  have hN : IsNormalSet D := fun g x hx => conj_mem_of_isClass h.isClass g hx
  apply commConnected_of_reach
  intro x hx y hy
  by_contra hxy
  have hSE := (fusionStronglyEmbedded_iff _).2
    (hA G D hN h.root h.gen hNP ⟨x, hx, y, hy, hxy⟩ x hx)
  obtain ⟨d, hd, e, he, h4⟩ := h.nondeg
  have hd2 := h.root.mul_self_eq_one hd
  have he2 := h.root.mul_self_eq_one he
  obtain ⟨hzD, hdz, -, hede⟩ := sq_mem_of_orderOf_eq_four h.root hd he h4
  rcases bender_strongly_embedded_normal_series G _ hSE with
    hS | ⟨M, N, hM, hNn, hMN, -, hMo, hNo, hB⟩
  ·
    have hne : d ≠ (d * e) ^ 2 := by
      intro hdz'
      have h1 : e * d * e = 1 := by rw [hede, ← hdz', hd2]
      have h2 : d = 1 := by
        calc d = e * (e * d * e) * e := by
              rw [show e * (e * d * e) * e = (e * e) * d * (e * e) by group, he2, one_mul,
                mul_one]
          _ = 1 := by rw [h1, mul_one, he2]
      exact absurd (h.root.orderOf_eq_two hd) (by rw [h2, orderOf_one]; decide)
    have hNC := noCommutingDistinctInvolutions_of_sylow hS
    have heq := hNC ⟨d, h.root.orderOf_eq_two hd⟩ ⟨(d * e) ^ 2, h.root.orderOf_eq_two hzD⟩ hdz.eq
    exact hne (congrArg Subtype.val heq)
  ·
    have hM1 : M = ⊥ := h.oddCore M hM hMo
    have hdN : d ∈ N := mem_of_odd_index hNo hd2
    have heN : e ∈ N := mem_of_odd_index hNo he2
    set π : N →* N ⧸ M.subgroupOf N := QuotientGroup.mk' (M.subgroupOf N)
    have hinj : Function.Injective π := by
      rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hM1, Subgroup.bot_subgroupOf]
    have hord : ∀ (x : G) (hx : x ∈ N), orderOf (π ⟨x, hx⟩) = orderOf x := fun x hx => by
      rw [orderOf_injective π hinj, Subgroup.orderOf_mk]
    refine not_orderOf_mul_eq_four_of_fusionIsBenderGroup hB
      (s := π ⟨d, hdN⟩) (t := π ⟨e, heN⟩) (by rw [hord]; exact h.root.orderOf_eq_two hd)
      (by rw [hord]; exact h.root.orderOf_eq_two he) ?_
    rw [← map_mul, show (⟨d, hdN⟩ : N) * ⟨e, heN⟩ = ⟨d * e, N.mul_mem hdN heN⟩ from rfl, hord, h4]

end CFSG.Timmesfeld.Bridge
