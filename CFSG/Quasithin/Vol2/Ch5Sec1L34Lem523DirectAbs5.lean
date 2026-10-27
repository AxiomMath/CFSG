module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem523DirectAbs4
public import CFSG.GroupTheory.Fitting.SelfCentralizingComponent
public import CFSG.Milestones.ASVolI.H4

public section

namespace CFSG.Quasithin.H13.Abs523

variable {V : Type} [CommGroup V] [Finite V]

theorem rk_ge_three_of_irred (hH47 : CFSG.ASVolI.H_4_7) (K : Type) [Field K] [Finite K]
    [CharP K 2] (hK4 : Nat.card K = 4) {𝒦V : Subgroup (MulAut V)}
    {vV : MulAut V} (hvv : vV * vV = 1) (hvN : vV ∈ Subgroup.normalizer (𝒦V : Set (MulAut V)))
    (hV2 : ∀ x : V, x ^ 2 = 1) [IsSimpleGroup ↥𝒦V] (hab : ¬ IsMulCommutative ↥𝒦V)
    (hiso : Nonempty (↥𝒦V ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) K))
    (hirrK : ∀ U : Subgroup V, (∀ k ∈ 𝒦V, ∀ u ∈ U, k u ∈ U) → U ≠ ⊥ → U = ⊤)
    (hVne : (⊤ : Subgroup V) ≠ ⊥) (hvne : vV ≠ 1) :
    3 ≤ CFSG.Quasithin.rk ↥(CFSG.Quasithin.commV (Subgroup.zpowers vV)) := by
  set M : Subgroup (MulAut V) := 𝒦V ⊔ Subgroup.zpowers vV with hM
  have h𝒦M : 𝒦V ≤ M := le_sup_left
  have hMN : M ≤ Subgroup.normalizer (𝒦V : Set (MulAut V)) := by
    apply sup_le
    · exact fun k hk => Subgroup.le_normalizer hk
    · rw [Subgroup.zpowers_le]
      exact hvN
  have hQnorm : (𝒦V.subgroupOf M).Normal := by
    rw [Subgroup.normal_subgroupOf_iff h𝒦M]
    intro h k hh hk
    exact (Subgroup.mem_normalizer_iff.mp (hMN hk) h).mp hh
  have hcomp : CFSG.IsComponent (𝒦V.subgroupOf M) := by
    haveI := hQnorm
    exact ⟨CFSG.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe h𝒦M)
      (isQuasisimple_of_simple_nonab ↥𝒦V hab), Subgroup.Normal.isSubnormal hQnorm⟩
  have hcent : Subgroup.centralizer ((𝒦V.subgroupOf M : Subgroup ↥M) : Set ↥M) = ⊥ := by
    rw [eq_bot_iff]
    intro c hc
    rw [Subgroup.mem_bot]
    have hc' : ∀ k ∈ 𝒦V, k * (c : MulAut V) = (c : MulAut V) * k := by
      intro k hk
      have h1 := Subgroup.mem_centralizer_iff.mp hc ⟨k, h𝒦M hk⟩
        (Subgroup.mem_subgroupOf.mpr hk)
      have h2 := congrArg Subtype.val h1
      simpa using h2
    apply Subtype.ext
    rw [Subgroup.coe_one]
    exact eq_one_of_commutes hvN hvv hV2 hab hirrK c.2 hc'
  have hgf : CFSG.generalizedFitting ↥M = 𝒦V.subgroupOf M :=
    CFSG.generalizedFitting_eq_of_isComponent_of_centralizer_eq_bot _ hcomp hcent
  have hK : Nat.card K = (2 ^ 1) ^ 2 := by
    rw [hK4]
    norm_num
  have hne : Nonempty (↥(CFSG.generalizedFitting ↥M) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) K) := by
    rw [hgf]
    obtain ⟨e⟩ := hiso
    exact ⟨(Subgroup.subgroupOfEquivOfLe h𝒦M).trans e⟩
  have hirr : CFSG.ASVolI.ChH.IsIrredOn
      (Subgroup.map M.subtype (CFSG.generalizedFitting ↥M)) ⊤ := by
    rw [hgf, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr h𝒦M]
    refine ⟨hVne, fun U _ hU => ?_⟩
    by_cases h : U = ⊥
    · exact Or.inl h
    · exact Or.inr (hirrK U hU h)
  have hvM : vV ∈ M := (le_sup_right : Subgroup.zpowers vV ≤ M) (Subgroup.mem_zpowers vV)
  have hord : orderOf vV = 2 := orderOf_eq_prime (by rw [sq, hvv]) hvne
  exact (hH47 V hV2 M K hK hne hirr vV hvM hord).1

end CFSG.Quasithin.H13.Abs523
