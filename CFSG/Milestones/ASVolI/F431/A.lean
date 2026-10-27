module

public import CFSG.Milestones.ASVolI.F431.JFinal
public import CFSG.Milestones.ASVolI.F4Small
public import CFSG.SignalizerFunctorTheorem.NonLocalExc.Unipotent
import all CFSG.Milestones.ASVolI.F4

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF

section FrattiniTwo

theorem burnsideF4m_oPPrime_eq_of_borel {E : Type} [Group E] [Finite E] {H S : Subgroup E}
    (hS : IsSylowOf 2 S H) (hB : IsPGroup 2 ↥(H ⊓ Subgroup.normalizer (S : Set E))) :
    oPPrime 2 H = H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hSH, hS2, hSi⟩ := hS
  have hmem : ∀ x ∈ H ⊓ Subgroup.normalizer (S : Set E), x ∈ oPPrime 2 H := by
    intro x hx
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hB ⟨x, hx⟩
    exact Subgroup.subset_closure ⟨hx.1, k, by rw [← Subgroup.orderOf_mk x hx]; exact hk⟩
  refine le_antisymm (burnsideF4d_oPPrime_le H) ?_
  have hNle : oPPrime 2 H ≤ H := burnsideF4d_oPPrime_le H
  haveI hN : ((oPPrime 2 H).subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNle).mpr (burnsideF4d_le_normalizer_oPPrime H)
  have hS'2 : IsPGroup 2 ↥(S.subgroupOf H) := hS2.comap_subtype
  have hSi' : ¬ 2 ∣ (S.subgroupOf H).index := hSi
  let P : Sylow 2 ↥H := hS'2.toSylow hSi'
  have hPN : (P : Subgroup ↥H) ≤ (oPPrime 2 H).subgroupOf H := by
    intro g hg
    have hg' : g ∈ S.subgroupOf H := (IsPGroup.mem_toSylow hS'2 hSi').mp hg
    exact hmem g ⟨g.2, Subgroup.le_normalizer hg'⟩
  have htop := Sylow.normalizer_sup_eq_top' P hPN
  have hnorm : Subgroup.normalizer ((P : Subgroup ↥H) : Set ↥H) ≤ (oPPrime 2 H).subgroupOf H := by
    intro g hg
    have hPe : (P : Subgroup ↥H) = S.subgroupOf H := IsPGroup.toSylow_coe hS'2 hSi'
    rw [hPe, ← Subgroup.subgroupOf_normalizer_eq hSH] at hg
    exact hmem g ⟨g.2, hg⟩
  intro x hx
  have h1 : (⊤ : Subgroup ↥H) ≤ (oPPrime 2 H).subgroupOf H := htop ▸ sup_le hnorm le_rfl
  exact h1 (Subgroup.mem_top (⟨x, hx⟩ : ↥H))

end FrattiniTwo

section BorelTwo

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

set_option linter.unusedSectionVars false


theorem burnsideF4m_torusGroup_eq_bot {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    {τ : Tag} : torusGroup τ K = ⊥ := by
  have h2 : Nat.card Kˣ = 1 := by rw [Nat.card_units, hK]
  haveI : Subsingleton Kˣ := (Nat.card_eq_one_iff_unique.1 h2).1
  rw [eq_bot_iff, torusGroup, Subgroup.closure_le]
  rintro _ ⟨⟨i, u⟩, rfl⟩
  rw [Subsingleton.elim u 1]
  simp [torusElt_one]

theorem burnsideF4m_isPGroup_g2_fullImage {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    {H : Type} [Group H] (marking : G2Native.FullModel K ≃* H) :
    IsPGroup 2 ↥(G2Native.fullImage K marking (G2Native.positiveBorel K)) := by
  haveI : CharP K 2 := by
    have : Fintype K := Fintype.ofFinite K
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact charP_of_card_eq_prime_pow (f := 1) (by rw [← Nat.card_eq_fintype_card, hK, pow_one])
  have hU : IsPGroup 2 ↥(G2Native.positiveBorel K) :=
    IsPGroup.of_card (n := 6) (by rw [burnsideF4c_card_positiveBorel hK]; norm_num)
  unfold G2Native.fullImage G2Native.fullLocal
  exact (hU.map _).map _

theorem burnsideF4m_isPGroup_reeBorel {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) : IsPGroup 2 ↥(ExceptionalRoots.reeBorel K 0) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : ExceptionalRoots.reeBorel K 0 ≤ posUnipotent Tag.F4 K := by
    refine inf_le_right.trans ?_
    rw [burnsideF4gF4_absoluteBorel_eq, borelGroup, burnsideF4m_torusGroup_eq_bot hK, bot_sup_eq]
  exact (CFSG.SignalizerFunctorTheorem.NonLocalExc.isPGroup_posUnipotent 2).to_le h1

theorem burnsideF4m_isPGroup_borel {κ : GLKind} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 κ 2 1 Gp M₁ M₂) (hκ : κ = .G2 ∨ κ = .F4tw) :
    IsPGroup 2 ↥(Gp ⊓ (M₁ ⊓ M₂)) := by
  obtain ⟨chart, hB, -, -⟩ := hyp.lie_amalgam
  rw [hB]
  rcases hκ with rfl | rfl
  · rcases chart.coordinates with
      ⟨c', hk, -⟩ | ⟨-, -, -, K, fK, finK, card, marking, h1, -⟩ |
      ⟨hk, -⟩ | ⟨hk, -⟩ | ⟨-, exponent, K, fK, finK, charK, scope, ⟨hk, -⟩ | ⟨hk, -⟩⟩
    · exact absurd hk (by cases c' <;> decide)
    · rw [h1]
      have hK : Nat.card K = 2 := by rw [card, pow_one]
      exact (burnsideF4m_isPGroup_g2_fullImage hK marking).map _
    all_goals exact absurd hk (by decide)
  · rcases chart.coordinates with
      ⟨c', hk, -⟩ | ⟨hk, -⟩ | ⟨hk, -⟩ | ⟨hk, -⟩ |
      ⟨-, exponent, K, fK, finK, charK, scope, ⟨-, hd, marking, h1, -⟩ | ⟨hk, -⟩⟩
    · exact absurd hk (by cases c' <;> decide)
    · exact absurd hk (by decide)
    · exact absurd hk (by decide)
    · exact absurd hk (by decide)
    · have he : exponent = 0 := by omega
      subst he
      rw [h1]
      have hK : Nat.card K = 2 := by
        have h := scope
        unfold ExceptionalRoots.ReeScope at h
        simpa using h
      exact (((burnsideF4m_isPGroup_reeBorel hK).comap_subtype).map _ |>.map _).map _
    · exact absurd hk (by decide)

end BorelTwo

section GenByTwo

set_option linter.unusedSectionVars false


theorem burnsideF4m_genByTwoRest : burnsideF4j_GenByTwoInputRest := by
  intro κ f E _ Gp M₁ M₂ hyp hκ hf
  subst hf
  haveI := hyp.finite
  obtain ⟨⟨S, hS, hB⟩, -⟩ := burnsideF4jb_parabolics ChF.nativeChartCompatibility hyp
  have h2 := burnsideF4m_isPGroup_borel hyp hκ
  rw [hB] at h2
  exact burnsideF4m_oPPrime_eq_of_borel hS h2

end GenByTwo

end CFSG.ASVolI
