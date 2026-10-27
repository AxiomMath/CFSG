module

public import CFSG.LocalAnalysis.StandardType.PhanEMinFrob
public import CFSG.LocalAnalysis.StandardType.PhanEMinModel
public import CFSG.LocalAnalysis.StandardType.PhanEChevRank
public import CFSG.LocalAnalysis.StandardType.PhanEStdLeviOf
public import CFSG.LocalAnalysis.StandardType.PhanEStdLongest
public import CFSG.LocalAnalysis.StandardType.PhanEStdBuildingData
public import CFSG.LocalAnalysis.StandardType.PhanEStdPanel
public import CFSG.Timmesfeld.RankTwo.LevisExceptional
public import CFSG.LocalAnalysis.StandardType.PhanEStdTransport

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Blueprint.Chevalley CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.LieType.RootSystem CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Timmesfeld

variable (k : Type) [Field k] [Finite k] [CharP k 2]

theorem e7Datum_cartan : (e7Datum k).cartan = CartanMatrix.E 7 :=
  cartan_E7

theorem coxeterMatrix_e7Datum :
    coxeterMatrix (e7Datum k).isFiniteType = CoxeterMatrix.E₇ :=
  coxeterMatrix_cartanE7 _ (e7Datum_cartan k)

noncomputable def e7W0 : (coxeterMatrix (e7Datum k).isFiniteType).Group :=
  (exists_longest_E7 (e7Datum k).isFiniteType (e7Datum_cartan k)).choose

theorem e7W0_isLongest :
    CFSG.Monster.B.Geometry.IsLongest (coxeterMatrix (e7Datum k).isFiniteType).toCoxeterSystem
      Set.univ (e7W0 k) :=
  (exists_longest_E7 (e7Datum k).isFiniteType (e7Datum_cartan k)).choose_spec.1

theorem e7W0_table (i : Fin (e7Datum k).rank) :
    weylAction (e7Datum k).isFiniteType (e7W0 k) (Pi.single i 1) = -Pi.single (id i) 1 :=
  (exists_longest_E7 (e7Datum k).isFiniteType (e7Datum_cartan k)).choose_spec.2.1 i

theorem e7W0_hop (i : Fin (e7Datum k).rank) :
    e7W0 k * (coxeterMatrix (e7Datum k).isFiniteType).toCoxeterSystem.simple i * e7W0 k =
      (coxeterMatrix (e7Datum k).isFiniteType).toCoxeterSystem.simple i :=
  (exists_longest_E7 (e7Datum k).isFiniteType (e7Datum_cartan k)).choose_spec.2.2 i

theorem e7_hedge_aux : ∀ i j : Fin 7, i < j → CoxeterMatrix.E₇ i j = 3 → edgeE 7 i j := by
  intro i j hij h
  fin_cases i <;> fin_cases j <;> simp_all [CoxeterMatrix.E₇, edgeE]

theorem e7_hedge : ∀ i j : Fin (e7Datum k).rank, i < j →
    coxeterMatrix (e7Datum k).isFiniteType i j = 3 → edgeE (e7Datum k).rank i j := by
  intro i j hij h
  rw [coxeterMatrix_e7Datum k] at h
  exact e7_hedge_aux i j hij h

variable {k} (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c)

@[expose] noncomputable def e7Frob :
    FrobData (e7Datum k) (e7Data_valid.nm k) (e7Data_valid.torus k) (e7W0 k) :=
  minFrobData e7Data_valid isFiniteType_cartan_E7 θ hθ (e7W0_hop k)

theorem e7_nm_mul_self (i : Fin (e7Datum k).rank) :
    e7Data_valid.nm k i * e7Data_valid.nm k i = 1 :=
  minNm_mul_self_of_charTwo e7Data_valid k i

noncomputable def e7RankOne (hθne : ∃ c, θ c ≠ c) :
    RankOneField (e7Datum_isCTGroupDatum k) (e7Frob θ hθ) :=
  (minChevModel e7Data_valid isFiniteType_cartan_E7 k).rankOneField
    (e7Datum_isCTGroupDatum k) (e7Frob θ hθ) θ hθne
    (fun i c => minBC_xm e7Data_valid θ (Pi.single i 1) c)

@[expose] noncomputable def e7PhiCompat :
    (minChevModel e7Data_valid isFiniteType_cartan_E7 k).PhiCompat (e7Frob θ hθ) θ where
  ρ := id
  ρ_single _ := rfl
  ρ_mem _ h := h
  phi_x γ _ c := minBC_xm e7Data_valid θ γ c

@[expose] noncomputable def e7StdLevi [Finite k] (hnorm : ∀ s : k, s ≠ 0 → θ s = s →
    ∃ a : k, a * θ a = s) :
    StdLevi (e7Frob θ hθ) (nrep (e7Datum_isCTGroupDatum k) (e7W0 k)) :=
  (minChevModel e7Data_valid isFiniteType_cartan_E7 k).stdLevi (e7Frob θ hθ)
    (e7Datum_isCTGroupDatum k) (simplyLacedLevis_e7 k) θ hθ hnorm
    (fun i c => minBC_xm e7Data_valid θ (Pi.single i 1) c)
    (fun i c => minBC_xm e7Data_valid θ (-Pi.single i 1) c) (fun _ => rfl) (e7W0_table k)
    (e7_hedge k)

end CFSG.ClassicalInvolution.Phan.PhanE
