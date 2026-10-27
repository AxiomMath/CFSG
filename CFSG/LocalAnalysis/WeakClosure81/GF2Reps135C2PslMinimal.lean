module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinL4Four16Label
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PslChiPow
import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.EndFieldModel

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Matrix Module Finset Polynomial
open CFSG.LieType.SpecialLinear CFSG.LieType.SpecialLinear.ExteriorModel
open CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar
open CFSG.Quasithin.SmithCurtis
open scoped TensorProduct Polynomial

theorem w135c2_minimal_of_hasTwistedLabel {m f : ℕ} {K : Type} [Field K] [Fintype K]
    [CharP K 2] (hK : Fintype.card K = 2 ^ f)
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) (SpecialLinearGroup (Fin (m + 1)) K) W)
    [ρ.IsIrreducible] {ε : Fin f → Finset (Fin (m + 1))} (hε : HasTwistedLabel ρ ε) {s : ℕ}
    (hE : Nat.card (Module.End (MonoidAlgebra (ZMod 2) (SpecialLinearGroup (Fin (m + 1)) K))
      ρ.asModule) = 2 ^ s) :
    ∀ p : ℕ, 0 < p → p < s → ∃ r : Fin f, ε ⟨(r + p) % f, Nat.mod_lt _ r.pos⟩ ≠ ε r := by
  classical
  intro p hp0 hps
  by_contra hcon
  rw [not_exists] at hcon
  simp only [not_not] at hcon
  let E := Module.End (MonoidAlgebra (ZMod 2)
    (Matrix.SpecialLinearGroup (Fin (m + 1)) K)) ρ.asModule
  obtain ⟨k, _, _, _, _, y, χ, J, _, ht, hχ, _, _, _⟩ := hε
  haveI : Finite ((CFSG.LieType.RootSystem.coxeterMatrix
      (CFSG.LieType.Universal.SpecialLinear.isFiniteType_A m)).Group) :=
    CFSG.LieType.RootSystem.finite_group
      (CFSG.LieType.Universal.SpecialLinear.isFiniteType_A m)
  have hsimp : IsSimpleRep (CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ)) :=
    isSimpleRep_extendScalars_endFieldRep ρ k
  have hsplit : SplitOver k (curtisDatum m K 2).H := by
    have h := splitOver m K 2 k
    rwa [Subgroup.comap_id] at h
  obtain ⟨μ, hμ⟩ := ht.exists_mu (D := curtisDatum m K 2)
    (π := MonoidHom.id (Matrix.SpecialLinearGroup (Fin (m + 1)) K))
    (C := coverId m K 2) hsimp hsplit
  have hrange :=
    CFSG.HardMathSupport.GuralnickMalle.isCurtisType_fieldRange_eq_closure
      (ρ := ρ) (D := (coverId m K 2).datum) (k := k) hμ
  let C : Subfield k := TauCeti.frobeniusFixedSubfield k 2 p
  haveI : Finite C := TauCeti.finite_frobeniusFixedSubfield k 2 p hp0.ne'
  have hle : (algebraMap E k).fieldRange ≤ C := by
    rw [hrange]
    refine Subfield.closure_le.mpr ?_
    rintro x ⟨h, hh, rfl⟩
    have hh' : h ∈ (curtisDatum m K 2).H := hh
    change χ h ∈ TauCeti.frobeniusFixedSubfield k 2 p
    rw [TauCeti.mem_frobeniusFixedSubfield, hχ h hh']
    exact w135c2_slChiEps_pow_of_rotate (F := K) hK ε hcon h hh'
  have hmem : ∀ x : E, algebraMap E k x ∈ C :=
    fun x => hle (RingHom.mem_fieldRange.mpr ⟨x, rfl⟩)
  have hcardE : Nat.card E ≤ Nat.card C :=
    Nat.card_le_card_of_injective (fun x : E => (⟨algebraMap E k x, hmem x⟩ : C))
      (fun x y hxy => (algebraMap E k).injective (Subtype.ext_iff.mp hxy))
  have hCroot : (C : Set k) = (X ^ 2 ^ p - X : k[X]).rootSet k :=
    TauCeti.coe_frobeniusFixedSubfield_eq_rootSet k 2 p hp0.ne'
  have hcardC : Nat.card C ≤ 2 ^ p := by
    change (C : Set k).ncard ≤ 2 ^ p
    rw [hCroot]
    calc (Set.ncard ((X ^ 2 ^ p - X : k[X]).rootSet k))
        ≤ (X ^ 2 ^ p - X : k[X]).natDegree :=
          Polynomial.ncard_rootSet_le (X ^ 2 ^ p - X : k[X]) k
      _ = 2 ^ p := FiniteField.X_pow_card_pow_sub_X_natDegree_eq k hp0.ne' (by norm_num)
  have hle2 : 2 ^ s ≤ 2 ^ p := by
    rw [← hE]
    exact hcardE.trans hcardC
  have hlt : 2 ^ p < 2 ^ s := Nat.pow_lt_pow_right (by norm_num) hps
  exact absurd hlt (not_lt.mpr hle2)

end CFSG.LocalAnalysis.WeakClosure81
