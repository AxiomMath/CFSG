module

public import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddInner
public import CFSG.HardMathSupport.Timmesfeld.LinearRank.UnitaryDiagonal
public import CFSG.LieType.SeitzGeneration.Basic
import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPSL
import CFSG.Models.Blueprint

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Matrix CFSG.Open CFSG.LieType.SeitzGeneration CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

@[expose] def SeitzFourUOuterModel : Prop :=
  ∀ {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K), p ≠ 2 → ∀ {n : ℕ}, 3 ≤ n →
    ∀ E : Subgroup (MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))),
      IsElemAbelian 2 E → Nat.card E = 4 →
      ¬ E ≤ CFSG.ComponentClassification.OuterAutomorphisms.inner
        (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) → PlaneGen E

@[expose] def SeitzFourUGraphAniso : Prop :=
  ∀ {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K), p ≠ 2 → ∀ {n : ℕ}, 3 ≤ n →
    n ≤ 4 →
    ∀ E : Subgroup (MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))),
      IsElemAbelian 2 E → Nat.card E = 4 →
      ¬ E ≤ primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) →
      (∀ W : Submodule K (Fin n → K),
        (∀ x ∈ W, ∀ y ∈ W, gramForm h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) x y = 0) →
        (∀ e ∈ E, ∃ (A : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
          (φ : K ≃+* K),
          primeFormPsi h CFSG.HardMathSupport.Timmesfeld.LinearRank.isPrimeFormGram_one
            ⟨A, φ⟩ = e ∧
          ∀ w ∈ W, ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (fun i => φ (w i)) ∈ W) →
        W = ⊥) →
      PlaneGen E

private theorem not_map_conjNormal_le_inner {G : Type} [Group G] {L E : Subgroup G} [L.Normal]
    (hC : Subgroup.centralizer (L : Set G) = ⊥) (hEL : ¬ E ≤ L) :
    ¬ E.map (MulAut.conjNormal : G →* MulAut ↥L) ≤
      CFSG.ComponentClassification.OuterAutomorphisms.inner ↥L := by
  intro hle
  apply hEL
  intro e he
  obtain ⟨l, hl⟩ := hle ⟨e, he, rfl⟩
  have hcen : (l : G)⁻¹ * e ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 := congrArg (fun φ : MulAut ↥L => ((φ ⟨x, hx⟩ : ↥L) : G)) hl
    simp only [MulAut.conj_apply, MulAut.conjNormal_apply, Subgroup.coe_mul,
      Subgroup.coe_inv] at h1
    calc x * ((l : G)⁻¹ * e) = (l : G)⁻¹ * ((l : G) * x * (l : G)⁻¹) * e := by group
      _ = (l : G)⁻¹ * (e * x * e⁻¹) * e := by rw [h1]
      _ = (l : G)⁻¹ * e * x := by group
  rw [hC, Subgroup.mem_bot, inv_mul_eq_one] at hcen
  rw [← hcen]
  exact l.2

theorem seitzFourOuter_psu_of_model (hM : SeitzFourUOuterModel) :
    SeitzFourOuter fun X _ => ∃ n p f : ℕ, 3 ≤ n ∧ p ≠ 2 ∧ CFSG.Models.LieModel X .PSU n p f := by
  intro G _ _ L E hLn hLs hnab hP hC hE h4 hEL
  obtain ⟨n, p, f, hn, hp2, hm⟩ := hP
  have hm' : CFSG.Models.LieModel ↥L .PSU n p f := hm
  obtain ⟨⟨hp, hf, -⟩, K, _, _, hK, ⟨eS⟩⟩ :=
    CFSG.Models.LieModel.statedClassicalModel_of_ne_zero (by omega) hm'
  have h : UnitaryFieldData p f K := ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  obtain ⟨χ⟩ := nonempty_primeFormP_mulEquiv h
    (CFSG.HardMathSupport.Timmesfeld.LinearRank.isPrimeFormGram_one (n := n) (K := K))
  set ψ : ↥L ≃* primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    eS.trans ((unitaryPSUEquiv h (by omega)).symm.trans χ.symm) with hψ
  set A := E.map (MulAut.conjNormal : G →* MulAut ↥L) with hAdef
  have hA : IsElemAbelian 2 A := hE.map _
  have hA4 : Nat.card A = 4 := by
    rw [Subgroup.card_map_of_injective
      (Subgroup.conjNormal_injective_of_centralizer_eq_bot hC), h4]
  set A' := A.map (MulAut.congr ψ).toMonoidHom with hA'def
  have hA' : IsElemAbelian 2 A' := hA.map _
  have hA'4 : Nat.card A' = 4 := by
    rw [Subgroup.card_map_of_injective (MulAut.congr ψ).injective, hA4]
  have hA'I : ¬ A' ≤ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
    intro hle
    refine not_map_conjNormal_le_inner hC hEL fun a ha => ?_
    obtain ⟨y, hy⟩ := hle ⟨a, ha, rfl⟩
    refine ⟨ψ.symm y, ?_⟩
    have hy' : MulAut.conj (ψ.symm y) = MulAut.congr ψ.symm (MulAut.conj y) :=
      (CFSG.ComponentClassification.OuterAutomorphisms.congr_conj ψ.symm y).symm
    rw [hy', hy]
    ext x
    simp [MulAut.congr_apply]
  have hPA : PlaneGen A := (planeGen_map_congr ψ A).1 (hM h hp2 hn A' hA' hA'4 hA'I)
  exact iSup_centralizer_eq_of_seitzHyperGamma hC h4
    ((planeGen_iff_seitzHyperGamma Nat.prime_two (by rw [hA4]; norm_num)).1 hPA)

end CFSG.LocalAnalysis.WeakClosure81
