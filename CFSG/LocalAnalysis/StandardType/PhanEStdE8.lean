module

public import CFSG.LocalAnalysis.StandardType.PhanEAdjFrob
public import CFSG.LocalAnalysis.StandardType.PhanEAdjModel
public import CFSG.LocalAnalysis.StandardType.PhanEChevRank
public import CFSG.LocalAnalysis.StandardType.PhanEStdLeviOf
public import CFSG.LocalAnalysis.StandardType.PhanEStdLongest
public import CFSG.LocalAnalysis.StandardType.PhanEStdBuildingData
public import CFSG.LocalAnalysis.StandardType.PhanEStdPanel
public import CFSG.LocalAnalysis.StandardType.PhanEStdTransport
public import CFSG.LieType.Steinberg.Adjoint.Borel
public import CFSG.LieType.Chevalley.WeylRoots
public import CFSG.Timmesfeld.RankTwo.LevisExceptional

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.LieType.RootSystem CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint
open CFSG.Timmesfeld (edgeE simplyLacedLevis_e8)

variable (k : Type) [Field k] [Finite k] [CharP k 2]

theorem e8Datum_cartan : (e8Datum k).cartan = CartanMatrix.E 8 :=
  cartanE_eq 8

theorem coxeterMatrix_e8Datum :
    coxeterMatrix (e8Datum k).isFiniteType = CoxeterMatrix.E₈ :=
  coxeterMatrix_cartanE8 _ (e8Datum_cartan k)

noncomputable def e8W0 : (coxeterMatrix (e8Datum k).isFiniteType).Group :=
  (exists_longest_E8 (e8Datum k).isFiniteType (e8Datum_cartan k)).choose

theorem e8W0_isLongest :
    CFSG.Monster.B.Geometry.IsLongest (coxeterMatrix (e8Datum k).isFiniteType).toCoxeterSystem
      Set.univ (e8W0 k) :=
  (exists_longest_E8 (e8Datum k).isFiniteType (e8Datum_cartan k)).choose_spec.1

theorem e8W0_table (i : Fin (e8Datum k).rank) :
    weylAction (e8Datum k).isFiniteType (e8W0 k) (Pi.single i 1) = -Pi.single (id i) 1 :=
  (exists_longest_E8 (e8Datum k).isFiniteType (e8Datum_cartan k)).choose_spec.2.1 i

theorem e8W0_hop (i : Fin (e8Datum k).rank) :
    e8W0 k * (coxeterMatrix (e8Datum k).isFiniteType).toCoxeterSystem.simple i * e8W0 k =
      (coxeterMatrix (e8Datum k).isFiniteType).toCoxeterSystem.simple i :=
  (exists_longest_E8 (e8Datum k).isFiniteType (e8Datum_cartan k)).choose_spec.2.2 i

theorem e8_hedge_aux : ∀ i j : Fin 8, i < j → CoxeterMatrix.E₈ i j = 3 → edgeE 8 i j := by
  intro i j hij h
  fin_cases i <;> fin_cases j <;> simp_all [CoxeterMatrix.E₈, edgeE]

theorem e8_hedge : ∀ i j : Fin (e8Datum k).rank, i < j →
    coxeterMatrix (e8Datum k).isFiniteType i j = 3 → edgeE (e8Datum k).rank i j := by
  intro i j hij h
  rw [coxeterMatrix_e8Datum k] at h
  exact e8_hedge_aux i j hij h

variable {k} (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c)

@[expose] noncomputable def e8Frob :
    FrobData (e8Datum k) (CFSG.LieType.Chevalley.weylElement .E8 k)
      (Adjoint.torus (τ := .E8) k) (e8W0 k) :=
  adjFrobData θ hθ (e8W0_hop k)

theorem e8_nm_mul_self (i : Fin (e8Datum k).rank) :
    CFSG.LieType.Chevalley.weylElement .E8 k i *
      CFSG.LieType.Chevalley.weylElement .E8 k i = 1 :=
  adj_nm_mul_self (τ := .E8) k i

noncomputable def e8RankOne (hθne : ∃ c, θ c ≠ c) :
    RankOneField (e8_isCTGroupDatum k) (e8Frob θ hθ) :=
  (adjChevModel (rootOperatorFamily .E8) k).rankOneField
    (e8_isCTGroupDatum k) (e8Frob θ hθ) θ hθne
    (fun i c => adj_phi_xPar (τ := .E8) θ hθ (Pi.single i 1) c)

@[expose] noncomputable def e8PhiCompat :
    (adjChevModel (rootOperatorFamily .E8) k).PhiCompat (e8Frob θ hθ) θ where
  ρ := id
  ρ_single _ := rfl
  ρ_mem _ h := h
  phi_x γ _ c := adj_phi_xPar (τ := .E8) θ hθ γ c

@[expose] noncomputable def e8StdLevi (hnorm : ∀ s : k, s ≠ 0 → θ s = s → ∃ a : k, a * θ a = s) :
    StdLevi (e8Frob θ hθ) (nrep (e8_isCTGroupDatum k) (e8W0 k)) :=
  (adjChevModel (rootOperatorFamily .E8) k).stdLevi (e8Frob θ hθ)
    (e8_isCTGroupDatum k) (simplyLacedLevis_e8 k) θ hθ hnorm
    (fun i c => adj_phi_xPar (τ := .E8) θ hθ (Pi.single i 1) c)
    (fun i c => adj_phi_xPar (τ := .E8) θ hθ (-Pi.single i 1) c) (fun _ => rfl) (e8W0_table k)
    (e8_hedge k)

end CFSG.ClassicalInvolution.Phan.PhanE
