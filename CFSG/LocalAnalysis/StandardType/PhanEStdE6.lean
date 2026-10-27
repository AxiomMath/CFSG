module

public import CFSG.LocalAnalysis.StandardType.PhanEE6Frob
public import CFSG.LocalAnalysis.StandardType.PhanEMinModel
public import CFSG.LocalAnalysis.StandardType.PhanEChevRank
public import CFSG.LocalAnalysis.StandardType.PhanEStdLeviOf
public import CFSG.LocalAnalysis.StandardType.PhanEStdLongest
public import CFSG.LocalAnalysis.StandardType.PhanEStdBuildingData
public import CFSG.LocalAnalysis.StandardType.PhanEStdPanel
public import CFSG.LocalAnalysis.StandardType.PhanEStdTransport
public import CFSG.Timmesfeld.RankTwo.LevisExceptional

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Blueprint.Chevalley CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.LieType.RootSystem CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.TwistedE6 CFSG.Timmesfeld

variable (k : Type) [Field k] [Finite k] [CharP k 2]

theorem e6Datum_cartan : (e6Datum k).cartan = CartanMatrix.E 6 :=
  cartan_E6

theorem coxeterMatrix_e6Datum :
    coxeterMatrix (e6Datum k).isFiniteType = CoxeterMatrix.E₆ :=
  coxeterMatrix_cartanE6 _ (e6Datum_cartan k)

theorem rhoPerm_eq : ∀ i : Fin 6, rhoPerm i = rhoE6 i := by
  intro i
  fin_cases i <;> rfl

noncomputable def e6W0 : (coxeterMatrix (e6Datum k).isFiniteType).Group :=
  (exists_longest_E6 (e6Datum k).isFiniteType (e6Datum_cartan k)).choose

theorem e6W0_isLongest :
    CFSG.Monster.B.Geometry.IsLongest (coxeterMatrix (e6Datum k).isFiniteType).toCoxeterSystem
      Set.univ (e6W0 k) :=
  (exists_longest_E6 (e6Datum k).isFiniteType (e6Datum_cartan k)).choose_spec.1

theorem e6W0_table (i : Fin (e6Datum k).rank) :
    weylAction (e6Datum k).isFiniteType (e6W0 k) (Pi.single i 1) = -Pi.single (rhoPerm i) 1 := by
  have e : rhoPerm i = rhoE6 i := rhoPerm_eq i
  rw [e]
  exact (exists_longest_E6 (e6Datum k).isFiniteType (e6Datum_cartan k)).choose_spec.2.1 i

theorem e6W0_hop (i : Fin (e6Datum k).rank) :
    e6W0 k * (coxeterMatrix (e6Datum k).isFiniteType).toCoxeterSystem.simple i * e6W0 k =
      (coxeterMatrix (e6Datum k).isFiniteType).toCoxeterSystem.simple (rhoPerm i) := by
  have e : rhoPerm i = rhoE6 i := rhoPerm_eq i
  rw [e]
  exact (exists_longest_E6 (e6Datum k).isFiniteType (e6Datum_cartan k)).choose_spec.2.2 i

theorem e6_hedge_aux : ∀ i j : Fin 6, i < j → CoxeterMatrix.E₆ i j = 3 → edgeE 6 i j := by
  intro i j hij h
  fin_cases i <;> fin_cases j <;> simp_all [CoxeterMatrix.E₆, edgeE]

theorem e6_hedge : ∀ i j : Fin (e6Datum k).rank, i < j →
    coxeterMatrix (e6Datum k).isFiniteType i j = 3 → edgeE (e6Datum k).rank i j := by
  intro i j hij h
  rw [coxeterMatrix_e6Datum k] at h
  exact e6_hedge_aux i j hij h

variable {k} (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c)

@[expose] noncomputable def e6Frob :
    FrobData (e6Datum k) (e6Data_valid.nm k) (e6Data_valid.torus k) (e6W0 k) :=
  e6FrobData θ hθ (e6W0_hop k)

theorem e6_nm_mul_self (i : Fin (e6Datum k).rank) :
    e6Data_valid.nm k i * e6Data_valid.nm k i = 1 :=
  minNm_mul_self_of_charTwo e6Data_valid k i

noncomputable def e6RankOne (hθne : ∃ c, θ c ≠ c) :
    RankOneField (e6Datum_isCTGroupDatum k) (e6Frob θ hθ) :=
  (minChevModel e6Data_valid isFiniteType_cartan_E6 k).rankOneField
    (e6Datum_isCTGroupDatum k) (e6Frob θ hθ) θ hθne
    (fun i c => sigma_xm_single θ i c)

@[expose] noncomputable def e6PhiCompat :
    (minChevModel e6Data_valid isFiniteType_cartan_E6 k).PhiCompat (e6Frob θ hθ) θ where
  ρ := rho
  ρ_single i := rho_single i
  ρ_mem γ hγ := (e6Data_valid.mem_minDatum_roots isFiniteType_cartan_E6 k).2
    (isRoot_rho ((e6Data_valid.mem_minDatum_roots isFiniteType_cartan_E6 k).1 hγ))
  phi_x γ hγ c := sigma_xm_charTwo θ
    ((e6Data_valid.mem_minDatum_roots isFiniteType_cartan_E6 k).1 hγ) c

theorem rhoPerm_rhoPerm (i : Fin 6) : rhoPerm (rhoPerm i) = i := by
  have e1 : rhoPerm i = rhoE6 i := rhoPerm_eq i
  have e2 : rhoPerm (rhoE6 i) = rhoE6 (rhoE6 i) := rhoPerm_eq (rhoE6 i)
  rw [e1, e2]
  exact rhoE6_involutive i

@[expose] noncomputable def e6StdLevi (hnorm : ∀ s : k, s ≠ 0 → θ s = s → ∃ a : k, a * θ a = s) :
    StdLevi (e6Frob θ hθ) (nrep (e6Datum_isCTGroupDatum k) (e6W0 k)) :=
  (minChevModel e6Data_valid isFiniteType_cartan_E6 k).stdLevi (e6Frob θ hθ)
    (e6Datum_isCTGroupDatum k) (simplyLacedLevis_e6 k) θ hθ hnorm
    (fun i c => sigma_xm_single θ i c) (fun i c => sigma_xm_neg_single θ i c)
    (fun i => rhoPerm_rhoPerm i) (e6W0_table k) (e6_hedge k)

@[expose] noncomputable def e6FrobFixEquiv : fixedGroup k θ ≃* frobFix (e6Frob θ hθ) :=
  MulEquiv.refl _

end CFSG.ClassicalInvolution.Phan.PhanE
