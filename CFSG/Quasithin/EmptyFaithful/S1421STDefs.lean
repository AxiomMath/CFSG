module

public import CFSG.Quasithin.EmptyFaithful.S1421L11
public import CFSG.Quasithin.EmptyFaithful.S1421Inputs
public import CFSG.Quasithin.Vol2.Ch12Sec8Six
public import CFSG.Quasithin.Background.F9Basic
public import CFSG.Quasithin.Background.A3Structure316

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace S1421

variable {G : Type} [Group G] [Finite G] {T M H K1 : Subgroup G}

structure L34Cfg (T M H K1 : Subgroup G) : Prop where
  cComp_mem : oTwoUpper H ∈ cComp (mcOf T)
  psl : IsPSL 3 2 2 (OTwoQuot (oTwoUpper H))
  graph : E2.IsDiagramNontrivial T (oTwoUpper H) (T ⊓ oTwoUpper H)
  hall : ∀ B : Subgroup G, IsHallOdd B (M ⊓ oTwoUpper H) → B ≤ K1 ∧ Nat.card B = 3
  eq_residual : oTwoUpper H = oPrimeResidualOf 3 (perfectCore (mcOf T))

theorem hypF98_of_abelian (st : Setting1427 T M H K1) (hU : IsMulCommutative ↥(uOfL22 T M)) :
    HypF98 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) (mcOf T) := by
  have h1281 := lemma_14_2_4 st.hyp st.facts
  have hHz : IsHz T M (yOfL22 T M) (mcOf T) := by
    have := h1281.isHz_normalizer
    rwa [normalizer_omegaOneCenter_eq_mcOf st.hyp] at this
  have h81 : HypF81 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (mcOf T) :=
    h1281.hypF81_of_commutator (fun _ hg => h1281.commutator_eq_bot_of_abelian hU hg) hHz
  exact h81.toHypF98 st.hyp.card_omegaOneCenter

end S1421

@[expose] def Lemma14212 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H K1 : Subgroup G), Setting1427 T M H K1 →
    pCoreOf 2 M ≤ S1421.sOf T K1 ∨ S1421.L34Cfg T M H K1

@[expose] def L34F98Impossible : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H K1 : Subgroup G), Setting1427 T M H K1 →
    S1421.L34Cfg T M H K1 →
    HypF98 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) (mcOf T) → False

@[expose] def L34NonabelianO2Y : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H K1 : Subgroup G), Setting1427 T M H K1 →
    S1421.L34Cfg T M H K1 → ¬ IsMulCommutative ↥(uOfL22 T M) →
      pCoreOf 2 (yOfL22 T M) ≤ S1421.sOf T K1

theorem lemma14213_of_inputs (h12 : Lemma14212) (hF : L34F98Impossible)
    (hN : L34NonabelianO2Y) : Lemma14213 := by
  intro G _ _ T M H K1 st hO
  rcases h12 G T M H K1 st with h | cfg
  · exact absurd h hO
  · by_cases hU : IsMulCommutative ↥(uOfL22 T M)
    · exact (hF G T M H K1 st cfg (S1421.hypF98_of_abelian st hU)).elim
    · exact hN G T M H K1 st cfg hU

end CFSG.Quasithin
