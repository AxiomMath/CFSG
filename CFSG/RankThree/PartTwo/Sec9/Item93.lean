module

public import CFSG.RankThree.PartTwo.Sec11.Item112

public section

namespace CFSG.RankThree.PartTwo.Sec9

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped commutatorElement

@[expose] def Hyp92InvTwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R : Subgroup G), Hyp92 G A c L a R 1 → ¬ Sec8.InvTwoBarNontrivial A L

@[expose] def Hyp92FixedCore : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R : Subgroup G), Hyp92 G A c L a R 1 → ∀ e ∈ A, e ∉ Subgroup.zpowers c →
      ∀ (he : e ∈ Subgroup.normalizer (L : Set G))
        (N : Subgroup (MulAut (L ⧸ aschbacherSolvableCore 3 L))),
        (∀ ν ∈ N, ν * Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨e, he⟩) =
          Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨e, he⟩) * ν) →
        ¬ 3 ∣ Nat.card N →
        (∀ ℓ : L ⧸ aschbacherSolvableCore 3 L,
          Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨e, he⟩) ℓ = ℓ →
            ∀ ν ∈ N, MulAut.conj ℓ * ν * (MulAut.conj ℓ)⁻¹ ∈ N) →
        N = ⊥

@[expose] def Hyp92NormalizerL : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R : Subgroup G) (n : ℕ), Hyp92 G A c L a R n →
      Subgroup.normalizer (Subgroup.zpowers c : Set G) ≤ Subgroup.normalizer (L : Set G)

theorem item93_of (h45 : Sec4.Item4_5) (hF1 : Hyp92InvTwo) (hK : Hyp92FixedCore)
    (hNL : Hyp92NormalizerL) : Item93 := by
  intro G _ _ A c L a R n h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hn0 : n ≠ 0 := by
    rintro rfl
    obtain ⟨K, _, _, h1 | h1⟩ := h.isSLThreePiAt
    · have h2 : 1 < Nat.card K := Finite.one_lt_card
      rw [h1.1] at h2
      norm_num at h2
    · norm_num at h1
  by_contra hn
  obtain rfl : n = 1 := by omega
  have hG := h.toTheoremFourHyp
  have hAe := h.mem_partTwoF.1
  have hexp : ∀ x ∈ A, x ^ 3 = 1 := hAe.2
  have hcomm : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hA3 : IsPGroup 3 A := fun u => ⟨1, Subtype.ext (by simpa using hexp u u.2)⟩
  have hcA := h.mem_A
  have hc1 := h.ne_one
  have hco : orderOf c = 3 := orderOf_eq_prime (hexp c hcA) hc1
  have hAL : A ≤ Subgroup.normalizer (L : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hG hAe hcA hc1 L h.mem_thetaComponentsAt
  rcases h.invTwo_or_commutator with (hi | ⟨A', hA'A, hcard, hcA', hnot⟩) | ⟨-, hU8⟩
  · exact hF1 G A c L a R h hi
  rotate_left
  · have h8 := h.isSLThreePiAt
    rw [show (2 : ℕ) ^ (3 * 1) = 8 by norm_num] at h8
    exact hU8 h8
  apply hnot
  have h27 := h.card_eq
  have hA'9 : Nat.card A' = 9 := by omega
  obtain ⟨e, heA', hec⟩ : ∃ e ∈ A', e ∉ Subgroup.zpowers c := by
    by_contra hcon
    push Not at hcon
    have hle : A' ≤ Subgroup.zpowers c := hcon
    have := Subgroup.card_le_of_le hle
    rw [hA'9, Nat.card_zpowers, hco] at this
    norm_num at this
  have heA := hA'A heA'
  have hA'eq : Subgroup.closure ({c, e} : Set G) = A' := by
    have hle : Subgroup.closure ({c, e} : Set G) ≤ A' := by
      rw [Subgroup.closure_le]
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with hy | hy <;> rw [hy]
      · exact hcA'
      · exact heA'
    have h1 : Subgroup.zpowers c ≤ Subgroup.closure ({c, e} : Set G) :=
      Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
    have h9 := three_mul_card_le_of_le_of_ne hA3 (hle.trans hA'A) h1 (fun h => hec (by
      rw [h]
      exact Subgroup.subset_closure (by simp)))
    rw [Nat.card_zpowers, hco] at h9
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hA'9]; omega)
  set C := Subgroup.centralizer (A' : Set G) with hC
  set X := inSubgroup (aschbacherSolvableCore 3) C with hX
  have hcen : ∀ z : G, z * c = c * z → z * e = e * z → z ∈ C := by
    intro z hzc hze
    rw [hC, ← hA'eq, Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact hzc.symm
    · exact hze.symm
  have hXC : X ≤ C := Subgroup.map_subtype_le _
  have hCc : C ≤ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.centralizer_le (by simpa using hcA')
  have hCe : C ≤ Subgroup.centralizer ({e} : Set G) :=
    Subgroup.centralizer_le (by simpa using heA')
  have hXN : X ≤ Subgroup.normalizer (L : Set G) := fun x hx =>
    hNL G A c L a R 1 h (Sec10.mem_normalizer_zpowers_of_conj_mem (by
      rw [Subgroup.mem_centralizer_singleton_iff.mp (hCc (hXC hx)), mul_inv_cancel_right]
      exact Subgroup.mem_zpowers c))
  have hAX : A ≤ Subgroup.normalizer (X : Set G) := by
    intro y hy
    apply Sec6.normalizer_le_normalizer_theta C
    apply Subgroup.le_normalizer
    rw [hC, Subgroup.mem_centralizer_iff]
    intro z hz
    exact hcomm z (hA'A hz) y hy
  set ρ := (Sec4.thetaQuotMulAut L).comp (Sec4.compAction L) with hρ
  have heN := hAL heA
  set N : Subgroup (MulAut (L ⧸ aschbacherSolvableCore 3 L)) :=
    (X.subgroupOf (Subgroup.normalizer (L : Set G))).map ρ with hNdef
  have hNbot : N = ⊥ := by
    refine hK G A c L a R h e heA hec heN N ?_ ?_ ?_
    · rintro _ ⟨⟨x, hxN⟩, hx, rfl⟩
      have hxX : x ∈ X := Subgroup.mem_subgroupOf.mp hx
      have hxe : x * e = e * x := Subgroup.mem_centralizer_singleton_iff.mp (hCe (hXC hxX))
      have h1 : (⟨x, hxN⟩ : Subgroup.normalizer (L : Set G)) * ⟨e, heN⟩ =
          ⟨e, heN⟩ * ⟨x, hxN⟩ := Subtype.ext hxe
      have h2 := congrArg ρ h1
      rw [map_mul, map_mul] at h2
      exact h2
    · intro h3
      have h1 : Nat.card N ∣ Nat.card X := by
        refine (Subgroup.card_map_dvd _ ρ).trans ?_
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXN).toEquiv]
      exact Sec11.not_three_dvd_card_inSubgroup_theta C (h3.trans h1)
    · intro ℓ hℓ ν hν
      obtain ⟨⟨x, hxN⟩, hx, rfl⟩ := hν
      induction ℓ using QuotientGroup.induction_on with
      | H y =>
        obtain ⟨z, hz, hze⟩ := Sec11.exists_lift_of_fixed heN (hexp e heA) y hℓ
        have hzC : (z : G) ∈ C := by
          refine hcen z ?_ hze.symm
          exact (Subgroup.mem_centralizer_singleton_iff.mp
            (Sec6.le_centralizer_of_mem_thetaComponentsAt h.mem_thetaComponentsAt z.2))
        have hzX : (z : G) ∈ Subgroup.normalizer (X : Set G) :=
          Sec6.normalizer_le_normalizer_theta C (Subgroup.le_normalizer hzC)
        have hzxN : (z : G) * x * (z : G)⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
          Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.le_normalizer z.2) hxN)
            (Subgroup.inv_mem _ (Subgroup.le_normalizer z.2))
        refine ⟨⟨(z : G) * x * (z : G)⁻¹, hzxN⟩, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
        · exact (Subgroup.mem_normalizer_iff.mp hzX x).mp (Subgroup.mem_subgroupOf.mp hx)
        · rw [← hz, ← Sec11.thetaQuotMulAut_compAction_of_mem L z.2]
          have e1 : (⟨(z : G) * x * (z : G)⁻¹, hzxN⟩ : Subgroup.normalizer (L : Set G)) =
              ⟨z, Subgroup.le_normalizer z.2⟩ * ⟨x, hxN⟩ * (⟨z, Subgroup.le_normalizer z.2⟩)⁻¹ :=
            rfl
          rw [e1, map_mul, map_mul, map_inv]
          rfl
  have hXCL : X ≤ Sec4.thetaQuotCentralizer L := by
    intro x hx
    have h1 : ρ ⟨x, hXN hx⟩ ∈ N := ⟨⟨x, hXN hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    rw [hNbot, Subgroup.mem_bot] at h1
    exact ⟨⟨x, hXN hx⟩, h1, rfl⟩
  refine le_trans ?_ hXCL
  rw [Subgroup.commutator_le]
  intro x hx y hy
  rw [commutatorElement_def]
  have h1 : y * x⁻¹ * y⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp (hAX hy) x⁻¹).mp (X.inv_mem hx)
  rw [show x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) by group]
  exact X.mul_mem hx h1

end CFSG.RankThree.PartTwo.Sec9
