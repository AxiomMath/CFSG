module

public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerChoiceTwoOmCoord
public import CFSG.RankThree.OrthogonalInvolutions.Dickson
public import CFSG.GroupTheory.WeirSylow.OrthogonalModels
public import CFSG.Open.LocalVocabulary
import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP9Coord
import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP9OrthFrame
import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP9SignOmega
import CFSG.RankThree.PartOne.S11d.OrthCaseH
import CFSG.RankThree.PartOne.S11d.OrthDicksonOmega
import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenFrame
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessEven
import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessOdd
import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldCentralizer
import CFSG.RankThree.PartOne.S11d.OutClassicalTwo
import CFSG.RankThree.PartOne.S11d.OutLinear
import CFSG.RankThree.PartOne.S11d.OutSymplectic
import CFSG.RankThree.PartOne.S11d.OutUnitary

public section

namespace CFSG.StandardType.FrameRoute

open Module QuadraticMap CFSG.Open CFSG.LocalAnalysis.GLTheoremA.S172C.Cent
  CFSG.RankThree.Classical2 CFSG.RankThree.OrthogonalInvolutions

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

omit [Finite K] in
private theorem p9Orth_finrank_eq {Q : QuadraticForm K V} {E : Subgroup (V ≃ₗ[K] V)}
    (C : ChoiceTwoOm.OmCoord K Q E) :
    finrank K V = 2 * C.s + finrank K C.W0 := by
  have hdim : finrank K (Fin C.s → K × K) = 2 * C.s := by
    rw [Module.finrank_pi_fintype]
    simp [Module.finrank_prod, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    ring
  calc
    finrank K V = finrank K ((Fin C.s → K × K) × C.W0) := C.Φ.finrank_eq.symm
    _ = finrank K (Fin C.s → K × K) + finrank K C.W0 := Module.finrank_prod
    _ = 2 * C.s + finrank K C.W0 := by rw [hdim]

private theorem p9Orth_tor_apply_eq_of_mem_polarPerp {Q : QuadraticForm K V}
    {E : Subgroup (V ≃ₗ[K] V)} {k : ℕ} {U : Fin k → Submodule K V}
    {e : Fin k → ↥(orthDerived Q)}
    (hEO : E ≤ orthDerived Q)
    (hF : IsPlaneFrame Q 3 U e (E.subgroupOf (orthDerived Q)))
    (C : ChoiceTwoOm.OmCoord K Q E) {v : V}
    (hv : v ∈ polarPerp Q (⨆ j, U j)) (f : Fin C.s → ZMod 3) : C.tor f v = v := by
  have hmem : (⟨C.tor f, hEO (C.tor_mem f)⟩ : ↥(orthDerived Q)) ∈
      E.subgroupOf (orthDerived Q) :=
    Subgroup.mem_subgroupOf.mpr (C.tor_mem f)
  exact hF.apply_eq_of_mem_polarPerp_iSup hmem hv

omit [Finite K] [FiniteDimensional K V] in
private theorem p9Orth_fst_eq_zero_of_fixed {Q : QuadraticForm K V} {E : Subgroup (V ≃ₗ[K] V)}
    (C : ChoiceTwoOm.OmCoord K Q E) {d : Fin C.s → K × K} {x : C.W0}
    (hfix : ∀ f : Fin C.s → ZMod 3, C.tor f (C.Φ (d, x)) = C.Φ (d, x)) : d = 0 := by
  funext i
  have hsingle := hfix (Pi.single i (1 : ZMod 3))
  rw [C.tor_acts] at hsingle
  have hd : ChoiceTwoOm.torC (Pi.single i (1 : ZMod 3)) d = d :=
    congrArg Prod.fst (C.Φ.injective hsingle)
  have hi : ChoiceTwoOm.zpow (1 : ZMod 3) (d i) = d i := by
    simpa [ChoiceTwoOm.torC_apply] using congrFun hd i
  exact ChoiceTwoOm.eq_zero_of_zpow_eq 1 (by decide) (d i) hi

private theorem p9Orth_exists_W0_of_mem_polarPerp {Q : QuadraticForm K V}
    {E : Subgroup (V ≃ₗ[K] V)} {k : ℕ} {U : Fin k → Submodule K V}
    {e : Fin k → ↥(orthDerived Q)}
    (hEO : E ≤ orthDerived Q)
    (hF : IsPlaneFrame Q 3 U e (E.subgroupOf (orthDerived Q)))
    (C : ChoiceTwoOm.OmCoord K Q E) {v : V} (hv : v ∈ polarPerp Q (⨆ j, U j)) :
    ∃ x : C.W0, C.Φ (0, x) = v := by
  refine ⟨(C.Φ.symm v).2, ?_⟩
  have hv' : C.Φ ((C.Φ.symm v).1, (C.Φ.symm v).2) = v := C.Φ.apply_symm_apply v
  have hfix : ∀ f : Fin C.s → ZMod 3,
      C.tor f (C.Φ ((C.Φ.symm v).1, (C.Φ.symm v).2)) =
        C.Φ ((C.Φ.symm v).1, (C.Φ.symm v).2) := by
    intro f
    rw [hv']
    exact p9Orth_tor_apply_eq_of_mem_polarPerp hEO hF C hv f
  have hd := p9Orth_fst_eq_zero_of_fixed C hfix
  calc
    C.Φ (0, (C.Φ.symm v).2) = C.Φ ((C.Φ.symm v).1, (C.Φ.symm v).2) := by rw [hd]
    _ = v := hv'

private theorem p9Orth_exists_hyperbolic_pair {Q : QuadraticForm K V}
    {E : Subgroup (V ≃ₗ[K] V)} {k : ℕ} {U : Fin k → Submodule K V}
    {e : Fin k → ↥(orthDerived Q)}
    (hEO : E ≤ orthDerived Q)
    (hF : IsPlaneFrame Q 3 U e (E.subgroupOf (orthDerived Q)))
    (C : ChoiceTwoOm.OmCoord K Q E) {f f' : V}
    (hf : f ∈ polarPerp Q (⨆ j, U j)) (hf' : f' ∈ polarPerp Q (⨆ j, U j))
    (hQf : Q f = 0) (hQf' : Q f' = 0) (hff' : polar Q f f' = 1) :
    ∃ x y : C.W0, Q x = 0 ∧ Q y = 0 ∧ polar Q x y = 1 := by
  obtain ⟨x, hx⟩ := p9Orth_exists_W0_of_mem_polarPerp hEO hF C hf
  obtain ⟨y, hy⟩ := p9Orth_exists_W0_of_mem_polarPerp hEO hF C hf'
  refine ⟨x, y, ?_, ?_, ?_⟩
  · have hform := C.form (0 : Fin C.s → K × K) x
    rw [hx, hQf] at hform
    simpa [ChoiceTwoOm.nrm] using hform.symm
  · have hform := C.form (0 : Fin C.s → K × K) y
    rw [hy, hQf'] at hform
    simpa [ChoiceTwoOm.nrm] using hform.symm
  · rw [← hff', ← hx, ← hy]
    have h1 : polar Q (C.Φ (0, x)) (C.Φ (0, y)) = polar Q (x : V) (y : V) := by
      have harg : C.Φ (0, x) + C.Φ (0, y) = C.Φ (0, x + y) := by
        rw [← map_add]
        congr 1
        exact Prod.ext (by funext i; simp) rfl
      rw [QuadraticMap.polar, QuadraticMap.polar, harg,
        C.form (0 : Fin C.s → K × K) (x + y),
        C.form (0 : Fin C.s → K × K) x,
        C.form (0 : Fin C.s → K × K) y]
      simp [ChoiceTwoOm.nrm]
    exact h1.symm

omit [Finite K] [FiniteDimensional K V] in
private theorem p9Orth_card {Q : QuadraticForm K V} {E : Subgroup (V ≃ₗ[K] V)}
    (C : ChoiceTwoOm.OmCoord K Q E) : Nat.card E = 3 ^ C.s := by
  have hbij : Function.Bijective
      (fun f : Fin C.s → ZMod 3 => (⟨C.tor f, C.tor_mem f⟩ : E)) := by
    refine ⟨fun f f' h => C.tor_injective (congrArg Subtype.val h), ?_⟩
    intro e
    obtain ⟨f, hf⟩ := C.mem_tor (e : V ≃ₗ[K] V) e.2
    exact ⟨f, Subtype.ext hf⟩
  have h := Nat.card_eq_of_bijective _ hbij
  rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin] at h
  exact h.symm

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
private theorem p9Orth_selfCent_subgroupOf {Q : QuadraticForm K V} {E : Subgroup (V ≃ₗ[K] V)}
    (hEO : E ≤ orthDerived Q)
    (hsc : ∀ g ∈ orthDerived Q, (∀ e ∈ E, g * e = e * g) → g ^ 3 = 1 → g ∈ E)
    (g : ↥(orthDerived Q)) (hcomm : ∀ x ∈ E.subgroupOf (orthDerived Q), g * x = x * g)
    (hg3 : g ^ 3 = 1) : g ∈ E.subgroupOf (orthDerived Q) := by
  rw [Subgroup.mem_subgroupOf]
  refine hsc (g : V ≃ₗ[K] V) g.2 (fun e he => ?_) ?_
  · let x : E.subgroupOf (orthDerived Q) := ⟨⟨e, hEO he⟩, Subgroup.mem_subgroupOf.mpr he⟩
    simpa [x] using congrArg (fun z : ↥(orthDerived Q) => (z : V ≃ₗ[K] V)) (hcomm x x.2)
  · simpa using congrArg (fun z : ↥(orthDerived Q) => (z : V ≃ₗ[K] V)) hg3

theorem exists_omCoord_of_selfCent_two (hK : Nat.card K = 2) {Q : QuadraticForm K V}
    (hQ : (polarBilin Q).Nondegenerate) {a : ℕ} (hdim : finrank K V = 2 * a) (ha : 4 ≤ a)
    {E : Subgroup (V ≃ₗ[K] V)}
    (hEΩ : E ≤ CFSG.RankThree.OrthogonalInvolutions.omegaGroup Q hQ) (hE : IsElemAbelian 3 E)
    (hsc : ∀ g ∈ CFSG.RankThree.OrthogonalInvolutions.omegaGroup Q hQ,
      (∀ e ∈ E, g * e = e * g) → g ^ 3 = 1 → g ∈ E) :
    ∃ C : ChoiceTwoOm.OmCoord K Q E,
      ((C.W0 = ⊥ ∧ C.s = a) ∨
        (C.s + 1 = a ∧ finrank K C.W0 = 2 ∧
          ∃ x y : C.W0, Q x = 0 ∧ Q y = 0 ∧ polar Q x y = 1)) ∧
      Nat.card E = 3 ^ C.s ∧
      (CFSG.GroupTheory.WeirSylow.IsPlusType Q ↔ Even C.s) ∧
      ∀ g ∈ CFSG.RankThree.OrthogonalInvolutions.omegaGroup Q hQ,
        (∀ e ∈ E, g * e = e * g) → g ∈ E := by
  classical
  have hT := CFSG.RankThree.PartOne.exists_threeSingular_of_dim Q hQ ha hdim
  have hω : CFSG.RankThree.OrthogonalInvolutions.omegaGroup Q hQ = orthDerived Q :=
    le_antisymm (CFSG.RankThree.PartOne.FieldFix.omegaGroup_le_orthDerived hQ hT)
      (CFSG.RankThree.PartOne.FieldFix.orthDerived_le_omegaGroup hQ)
  have hEO : E ≤ orthDerived Q := by
    intro g hg
    rw [← hω]
    exact hEΩ hg
  have hsc' : ∀ g ∈ orthDerived Q, (∀ e ∈ E, g * e = e * g) → g ^ 3 = 1 → g ∈ E :=
    fun g hg => hsc g (by rw [hω]; exact hg)
  obtain ⟨k, U, e, hF, halt⟩ :=
    CFSG.StandardType.OmNsRootGen.exists_planeFrame_of_selfCentralizing
      (F := K) (V := V) (Q := Q) (p := 3) (ℓ := a) hQ Nat.prime_three (by norm_num)
      (by rw [hK]) hdim (by omega) (hE.subgroupOf _) (p9Orth_selfCent_subgroupOf hEO hsc')
  obtain ⟨F, -⟩ := CFSG.StandardType.SevOm.exists_frame_of_isPlaneFrame
    (Q := Q) (p := 3) (k := k) (U := U) (e := e) (E := E) Nat.prime_three hEO hF
  obtain ⟨C, hCs⟩ := ChoiceTwoOm.exists_coord hK hQ hT hEO F
    fun g hg hg3 hcomm => hsc' g hg hcomm hg3
  have hdimV := p9Orth_finrank_eq C
  have hpos : (C.W0 = ⊥ ∧ C.s = a) ∨
      (C.s + 1 = a ∧ finrank K C.W0 = 2 ∧
        ∃ x y : C.W0, Q x = 0 ∧ Q y = 0 ∧ polar Q x y = 1) := by
    rcases halt with ⟨hk, -⟩ | ⟨hk, f, f', hf, hf', hQf, hQf', hff'⟩
    · refine Or.inl ⟨?_, by omega⟩
      have h0 : finrank K C.W0 = 0 := by omega
      exact Submodule.finrank_eq_zero.mp h0
    · exact Or.inr ⟨by omega, by omega,
        p9Orth_exists_hyperbolic_pair hEO hF C hf hf' hQf hQf' hff'⟩
  have hW0 := hpos.imp And.left And.right
  exact ⟨C, hpos, p9Orth_card C, ChoiceTwoOm.OmCoord.isPlusType_iff_even hK C hW0,
    fun g hg hcomm =>
      ChoiceTwoOm.OmCoord.mem_of_commute_tor hK hQ C hW0 hg
        (fun f => hcomm _ (C.tor_mem f))⟩

end CFSG.StandardType.FrameRoute
