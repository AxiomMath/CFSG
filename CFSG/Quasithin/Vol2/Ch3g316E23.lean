module

public import CFSG.Quasithin.Vol2.Ch3g316Gen
public import CFSG.Quasithin.Vol2.Ch3g316Foc
public import CFSG.Quasithin.Vol2.Ch3g316L2
public import CFSG.Quasithin.Vol2.Ch3g316A5

public section

namespace CFSG.Quasithin.Ch3g316

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem e23_gen (he23 : E2.E23Nonsolvable) {H T M₂ V D : Subgroup G}
    (hmp : MinParabolic H T M₂) (hsq : SQTKGroup ↥H) (hchar : CharTwo H)
    (hred : IsTwoReducedIn H V)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G)) (hns : ¬ Group.IsSolvable H)
    (hDP : D ≤ T ⊓ twoResidual H)
    (hDN : H ⊓ Subgroup.normalizer ((T ⊓ twoResidual H : Subgroup G) : Set G) ≤
      Subgroup.normalizer (D : Set G))
    (hC : ClC H T D) (hD : ClD H T D) :
    T ⊓ twoResidual H ≤ D ⊔ pCoreOf 2 (twoResidual H) := by
  classical
  have hV := hred.2.2.1
  obtain ⟨hKJ, I, hIcard, hJI, hcomm, hind, hconj, htype, -, -, h2, h3⟩ :=
    he23 G H T M₂ V hV hmp hsq hchar hred hJ hns
  by_cases hL2 : ∀ L ∈ I, ∃ n : ℕ, E2.IsL2Natural L (fixV (autI hV (twoResidual H))) n
  · obtain ⟨hab, hmem⟩ :=
      l2_structure hV hmp hred hJ hKJ I hIcard hJI hcomm hind hL2 (h2 hL2).2.1
    have hPsyl : IsSylowTwoOf (T ⊓ twoResidual H) (twoResidual H) :=
      B6.isSylowTwoOf_inf_normal hmp.isSylow (twoResidual_le H) (le_normalizer_twoResidual H)
    refine sylow_le_sup_of_fusion (K := twoResidual H) (P := T ⊓ twoResidual H)
      (Q := pCoreOf 2 (twoResidual H)) (D := D) hPsyl (twoResidual_twoResidual H)
      (B6.pCoreOf_two_le_of_isSylowTwoOf hPsyl) (le_normalizer_pCoreOf 2 (twoResidual H)) hab ?_
    intro t ht y hy
    exact hC t ht (hmem t ht) y hy
  · have hA5 : ∀ L ∈ I, E2.IsA5Module L := by
      by_contra hall
      push Not at hall
      obtain ⟨L₀, hL₀, hL₀a⟩ := hall
      apply hL2
      intro L hL
      rcases htype L hL with h | h
      · exact h
      · exfalso
        obtain ⟨t, -, ht⟩ := hconj L hL L₀ hL₀
        rcases htype L₀ hL₀ with ⟨n, hn⟩ | h0
        · have h1 := Ch3n317A5.card_of_isL2Natural hn
          rw [← ht, Ch3n317A5.card_conjAut, Ch3n317A5.card_of_isA5Module h] at h1
          exact Ch3n317A5.two_pow_mul_ne_120 n h1.symm
        · exact hL₀a h0
    exact a5_gen hV hmp hred hJ hKJ I hIcard hJI hcomm hind hA5 (h3 hA5).2 hDP hDN hD

end CFSG.Quasithin.Ch3g316
