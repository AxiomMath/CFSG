module

public import CFSG.RankThree.PartOne.KC.OrthogonalCommutatorBinary

public section

namespace CFSG.RankThree.PartOne.KCOrthComm

open CFSG CFSG.RankThree.LocalRank CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear CFSG.RankThree.Classical2
  CFSG.RankThree.Classical.SteinbergBY
open scoped commutatorElement

section Transport

variable {K : Type} [Field K] [Finite K] {d : ℕ} (Q : QuadraticForm K (Fin d → K)) {p : ℕ}

theorem odd_card_commutator_of_gates_proj {f : ℕ} (hg : OrthogonalGates Q f)
    (hnd : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K (Fin d → K), Module.finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    (hq : 3 < Nat.card K) (hp : p.Prime) (hp3 : 3 < p) (hpl : p ≠ ringChar K)
    (B : Subgroup (MulAut (ProjOrthDerived Q)))
    (hB : (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)).range ≤ B)
    (t : MulAut (ProjOrthDerived Q))
    (ht : t ∈ (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)).range)
    (htp : orderOf t = p) {A : Subgroup (MulAut (ProjOrthDerived Q))} (hA : IsPGroup p A)
    (hAB : A ≤ B ⊓ Subgroup.centralizer ({t} : Set (MulAut (ProjOrthDerived Q)))) :
    Odd (Nat.card (⁅inSubgroup (aschbacherSolvableCore p)
      (B ⊓ Subgroup.centralizer ({t} : Set (MulAut (ProjOrthDerived Q)))), A⁆ :
        Subgroup (MulAut (ProjOrthDerived Q)))) := by
  have := finite_linearEquiv_self (K := K) (V := Fin d → K)
  obtain ⟨a, rfl⟩ := ht
  have hinj := conj_injective_projOrthDerived hnd hT
  have ha : orderOf a = p := by
    rw [← htp]
    exact (orderOf_injective _ hinj a).symm
  exact orthogonal_inner_actor_commutators_odd_of_gates Q hnd hT hq
    (gateData_of_orthogonalGates Q hg hp hp3) hp hp3 hpl
    (fun x hxp => nonempty_plusData (oddOrderIsometry_of_orthDerived hp hpl hnd x hxp) hp hp3)
    B hB a ha hA hAB

theorem odd_card_commutator_of_mulEquiv {f : ℕ} (hg : OrthogonalGates Q f)
    (hnd : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K (Fin d → K), Module.finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    (hq : 3 < Nat.card K) (hp : p.Prime) (hp3 : 3 < p) (hpl : p ≠ ringChar K)
    {T : Type} [Group T] [Finite T] (Φ : T ≃* ProjOrthDerived Q) (B : Subgroup (MulAut T))
    (hB : (MulAut.conj : T →* MulAut T).range ≤ B) (t : MulAut T)
    (ht : t ∈ (MulAut.conj : T →* MulAut T).range) (htp : orderOf t = p)
    {A : Subgroup (MulAut T)} (hA : IsPGroup p A)
    (hAB : A ≤ B ⊓ Subgroup.centralizer ({t} : Set (MulAut T))) :
    Odd (Nat.card (⁅inSubgroup (aschbacherSolvableCore p)
      (B ⊓ Subgroup.centralizer ({t} : Set (MulAut T))), A⁆ : Subgroup (MulAut T))) := by
  set φ := MulAut.congr Φ with hφ
  have hB' : (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)).range ≤
      B.map φ.toMonoidHom := by
    rw [← CFSG.RankThree.PartOne.map_conj_range_mulAutCongr Φ]
    exact Subgroup.map_mono hB
  have ht' : φ t ∈ (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)).range := by
    rw [← CFSG.RankThree.PartOne.map_conj_range_mulAutCongr Φ]
    exact Subgroup.mem_map_of_mem _ ht
  have htp' : orderOf (φ t) = p := by
    rw [← htp]
    exact orderOf_injective φ.toMonoidHom φ.injective t
  have hA' : IsPGroup p (A.map φ.toMonoidHom) := IsPGroup.of_equiv hA (φ.subgroupMap A)
  have hAB' : A.map φ.toMonoidHom ≤
      B.map φ.toMonoidHom ⊓ Subgroup.centralizer ({φ t} : Set (MulAut (ProjOrthDerived Q))) := by
    have h1 := Subgroup.map_mono (f := φ.toMonoidHom) hAB
    rwa [Subgroup.map_inf _ _ _ φ.injective,
      CFSG.RankThree.PartOne.map_centralizer_singleton_mulEquiv] at h1
  have h2 := odd_card_commutator_of_gates_proj Q hg hnd hT hq hp hp3 hpl _ hB' (φ t) ht' htp' hA'
    hAB'
  rw [← CFSG.RankThree.PartOne.map_inSubgroup_theta_centralizer_mulEquiv hp φ B t,
    ← Subgroup.map_commutator, Subgroup.card_map_of_injective φ.injective] at h2
  exact h2

end Transport

end CFSG.RankThree.PartOne.KCOrthComm

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly.LowTwoRank CFSG.RankThree.LocalRank CFSG.RankThree.PartOne.KCOrthComm
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear CFSG.RankThree.Classical.SteinbergBY
open scoped commutatorElement

theorem orthogonal_large_field_inner_actor_local_core_commutators_odd (T : Type) [Group T]
    [Finite T] (c : StatedLieTag)
    (hc : c = .POmegaOdd ∨ c = .POmegaPlus ∨ c = .POmegaMinus) (ℓ f n p : ℕ)
    (h : StatedClassicalModel T c n ℓ f) (hp : p.Prime) (hp3 : 3 < p) (hpℓ : p ≠ ℓ)
    (hq : 3 < ℓ ^ f) (B : Subgroup (MulAut T))
    (hB : (MulAut.conj : T →* MulAut T).range ≤ B) (t : MulAut T)
    (ht : t ∈ (MulAut.conj : T →* MulAut T).range) (htp : orderOf t = p)
    (A : Subgroup (MulAut T)) (hA : IsPGroup p A)
    (hAB : A ≤ B ⊓ Subgroup.centralizer ({t} : Set (MulAut T))) :
    Odd (Nat.card (⁅inSubgroup (aschbacherSolvableCore p)
      (B ⊓ Subgroup.centralizer ({t} : Set (MulAut T))), A⁆ : Subgroup (MulAut T))) := by
  have h' := h
  rcases hc with rfl | rfl | rfl
  ·
    obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
    obtain ⟨hchar, hnd, hT, -⟩ := coordinate_model_witness_odd h' K hK e
    have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates T .POmegaOdd
      (Or.inl rfl) n ℓ f h' K hK e
    exact odd_card_commutator_of_mulEquiv (coordinateQuadOdd n K) hgates hnd hT
      (by rw [hK]; exact hq) hp hp3 (by rw [hchar]; exact hpℓ)
      ((coordinateOddWitnessEquiv K e).trans (matrixProjEquiv (coordinateQuadOdd n K))) B hB t ht
      htp hA hAB
  ·
    obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
    obtain ⟨hchar, hnd, hT, -⟩ := coordinate_model_witness_plus h' K hK e
    have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates T .POmegaPlus
      (Or.inr (Or.inl rfl)) n ℓ f h' K hK e
    exact odd_card_commutator_of_mulEquiv (coordinateQuadPlus n K) hgates hnd hT
      (by rw [hK]; exact hq) hp hp3 (by rw [hchar]; exact hpℓ)
      ((coordinatePlusWitnessEquiv K e).trans (matrixProjEquiv (coordinateQuadPlus n K))) B hB t ht
      htp hA hAB
  ·
    have hn : 1 ≤ n := by
      have := h.1.2.2
      omega
    obtain ⟨-, K, _, _, hK, b, c', hirr, ⟨e⟩⟩ := h
    obtain ⟨hchar, hnd, hT, -⟩ := coordinate_model_witness_minus h' K hK b c' hirr e
    have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates T .POmegaMinus
      (Or.inr (Or.inr rfl)) n ℓ f h' hn K hK b c' hirr e
    exact odd_card_commutator_of_mulEquiv (coordinateQuadMinus n K hn b c') hgates hnd hT
      (by rw [hK]; exact hq) hp hp3 (by rw [hchar]; exact hpℓ)
      ((coordinateMinusWitnessEquiv K hn b c' e).trans
        (matrixProjEquiv (coordinateQuadMinus n K hn b c'))) B hB t ht htp hA hAB

end CFSG.RankThree.PartOne
