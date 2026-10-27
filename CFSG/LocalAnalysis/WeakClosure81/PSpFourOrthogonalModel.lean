module

public import CFSG.ClassicalGroups.Orthogonal.FiveDimensionalSimilarity
public import CFSG.ClassicalGroups.Symplectic.OrthogonalFiveAutomorphisms
public import CFSG.GH74.GLS.SP.Final
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5Defs
public import CFSG.LieType.SeitzGeneration.Defs

public noncomputable section

namespace CFSG.LocalAnalysis.WeakClosure81

open Matrix QuadraticMap
open CFSG.ComponentClassification
open CFSG.ComponentClassification.CatalogueBOrthogonalFive
open CFSG.Assembly.LowTwoRank
open CFSG.Blueprint

theorem exists_orthogonal_model_of_lieModel_psp_prime
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = p)
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (hdim : Module.finrank K V = 5)
    (L₀ : Type) [Group L₀] [Finite L₀]
    (hLie : LieModel L₀ .PSp 2 p 1) :
    ∃ ρ : MulAut L₀ →* TauCeti.QuadraticMap.orthogonalGroup Q,
      Function.Injective ρ ∧
      ρ.range = QuadraticMap.specialOrthogonalWithin Q ∧
      (innAutOf L₀).map ρ =
        commutator (TauCeti.QuadraticMap.orthogonalGroup Q) ∧
      ∀ A S : Subgroup (MulAut L₀), AlmostSimpleData L₀ A S →
        commutator (TauCeti.QuadraticMap.orthogonalGroup Q) ≤ A.map ρ ∧
        A.map ρ ≤ QuadraticMap.specialOrthogonalWithin Q ∧
        CFSG.Quasithin.IsSylowIn 2 (S.map ρ) (A.map ρ) ∧
        commutator (TauCeti.QuadraticMap.orthogonalGroup Q) ⊔ S.map ρ = A.map ρ := by
  obtain ⟨K', hK'field, hK'fin, hK'card, ⟨eL'⟩⟩ :=
    CFSG.GH74.GLS.SP.exists_model_of_lieModel_psp (Gs := L₀) (p := p) (f := 1) hLie
  letI : Field K' := hK'field
  letI : Finite K' := hK'fin
  letI : Fintype K' := Fintype.ofFinite K'
  letI : Fintype K := Fintype.ofFinite K
  have hK'p : Nat.card K' = p := by simpa using hK'card
  have hpK : Nat.Prime (Nat.card K) := by rwa [hK]
  have hoddK : Odd (Nat.card K) := by
    rw [hK]
    exact hp.odd_of_ne_two hp2
  have hcard : Fintype.card K' = Fintype.card K := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK'p, hK]
  let φ : K' ≃+* K := FiniteField.ringEquivOfCardEq hcard
  let eP : StatedProj (StatedSp 2 K') ≃* StatedProj (StatedSp 2 K) :=
    CFSG.Adapters.RankTwoModelTransports.statedProjCongr
      (CFSG.Adapters.RankTwoModelTransports.glCongr
        (ι := Fin 2 ⊕ Fin 2) φ)
      (CFSG.Adapters.RankTwoModelTransports.glCongr_statedSp φ 2)
      (CFSG.Adapters.RankTwoModelTransports.glCongr_statedScalars
        (ι := Fin 2 ⊕ Fin 2) φ)
  let e₀ : L₀ ≃* StatedProj (StatedSp 2 K) := eL'.trans eP
  obtain ⟨d, psi, eO, hpsi, happly, hsymm, hdet, hSO, hD⟩ :=
    CFSG.ClassicalGroups.Orthogonal.exists_five_dimensional_orthogonal_similarity
      hoddK Q hQ hdim
  let SOQ : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q) :=
    QuadraticMap.specialOrthogonalWithin Q
  let SOR : Subgroup (TauCeti.QuadraticMap.orthogonalGroup (selfAdjointForm K)) :=
    QuadraticMap.specialOrthogonalWithin (selfAdjointForm K)
  let DQ : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q) :=
    commutator (TauCeti.QuadraticMap.orthogonalGroup Q)
  let DR : Subgroup (TauCeti.QuadraticMap.orthogonalGroup (selfAdjointForm K)) :=
    commutator (TauCeti.QuadraticMap.orthogonalGroup (selfAdjointForm K))
  have hSOsym : SOR.map eO.symm.toMonoidHom = SOQ := by
    dsimp [SOR, SOQ]
    rw [← hSO, Subgroup.map_map]
    have hcomp : eO.symm.toMonoidHom.comp eO.toMonoidHom = MonoidHom.id _ := by
      ext x
      simp
    change Subgroup.map (eO.symm.toMonoidHom.comp eO.toMonoidHom)
      (specialOrthogonalWithin Q) = specialOrthogonalWithin Q
    rw [hcomp, Subgroup.map_id]
  let eAut : MulAut (StatedProj (StatedSp 2 K)) ≃* SOR :=
    CFSG.ClassicalGroups.Symplectic.pspFourAutEquivSpecialOrthogonal hpK hoddK
  let eAutL : MulAut L₀ ≃* MulAut (StatedProj (StatedSp 2 K)) := MulAut.congr e₀
  let eD : StatedProj (StatedSp 2 K) ≃* DR :=
    CFSG.ClassicalGroups.Symplectic.pspFourEquivDerivedOrthogonal (K := K) hoddK
  let eSO : SOR ≃* SOQ :=
    (eO.symm.subgroupMap SOR).trans (MulEquiv.subgroupCongr hSOsym)
  let eρ : MulAut L₀ ≃* SOQ := (eAutL.trans eAut).trans eSO
  let ρ : MulAut L₀ →* TauCeti.QuadraticMap.orthogonalGroup Q :=
    SOQ.subtype.comp eρ.toMonoidHom
  let eDtransport : DR ≃* DQ := MulEquiv.commutatorCongr eO.symm
  have hρinj : Function.Injective ρ := by
    intro x y h
    exact eρ.injective (Subtype.ext h)
  have hρrange : ρ.range = SOQ := by
    change (SOQ.subtype.comp eρ.toMonoidHom).range = SOQ
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr eρ.surjective,
      Subgroup.map_top, Subgroup.range_subtype]
  have hρconj : ∀ x : L₀, ρ (MulAut.conj x) = (eDtransport (eD (e₀ x)) : TauCeti.QuadraticMap.orthogonalGroup Q) := by
    intro x
    dsimp [ρ, eρ, eSO, eAutL, eDtransport]
    rw [MulEquiv.coe_commutatorCongr_apply]
    change (eO.symm ((eAut ((MulAut.congr e₀) (MulAut.conj x))) : SOR) :
        TauCeti.QuadraticMap.orthogonalGroup Q) =
      (eO.symm ((eD (e₀ x) : DR)) : TauCeti.QuadraticMap.orthogonalGroup Q)
    rw [show (MulAut.congr e₀) (MulAut.conj x) = MulAut.conj (e₀ x) from
      CFSG.LieType.SeitzGeneration.mulAut_congr_conj e₀ x]
    exact congrArg (fun y : TauCeti.QuadraticMap.orthogonalGroup (selfAdjointForm K) =>
      (eO.symm y : TauCeti.QuadraticMap.orthogonalGroup Q))
      (CFSG.ClassicalGroups.Symplectic.pspFourAutEquivSpecialOrthogonal_conj
        hpK hoddK (e₀ x))
  have hinn : (innAutOf L₀).map ρ = DQ := by
    apply le_antisymm
    · intro y hy
      rw [Subgroup.mem_map] at hy
      obtain ⟨α, hα, rfl⟩ := hy
      rw [innAutOf, MonoidHom.mem_range] at hα
      obtain ⟨x, rfl⟩ := hα
      rw [hρconj x]
      exact (eDtransport (eD (e₀ x))).property
    · intro y hy
      rw [Subgroup.mem_map]
      let z : DR := eDtransport.symm ⟨y, hy⟩
      let psp : StatedProj (StatedSp 2 K) := eD.symm z
      let x : L₀ := e₀.symm psp
      refine ⟨MulAut.conj x, ?_, ?_⟩
      · rw [innAutOf, MonoidHom.mem_range]
        exact ⟨x, rfl⟩
      · rw [hρconj x]
        have hx : e₀ x = psp := e₀.apply_symm_apply psp
        rw [hx]
        dsimp [psp, z]
        simp
  refine ⟨ρ, hρinj, hρrange, hinn, ?_⟩
  intro A S hAS
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc DQ = (innAutOf L₀).map ρ := hinn.symm
      _ ≤ A.map ρ := Subgroup.map_mono hAS.1
  · calc A.map ρ ≤ (⊤ : Subgroup (MulAut L₀)).map ρ := Subgroup.map_mono le_top
      _ = ρ.range := Subgroup.map_top ρ
      _ = SOQ := hρrange
  · exact (CFSG.Quasithin.E1.isSylowIn_map_of_injective hρinj).mpr hAS.2.1
  · calc DQ ⊔ S.map ρ = (innAutOf L₀).map ρ ⊔ S.map ρ := by rw [hinn]
      _ = (innAutOf L₀ ⊔ S).map ρ := by rw [← Subgroup.map_sup]
      _ = A.map ρ := by rw [hAS.2.2]

end CFSG.LocalAnalysis.WeakClosure81
