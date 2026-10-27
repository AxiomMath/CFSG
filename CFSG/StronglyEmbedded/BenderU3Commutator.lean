module

import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderAutBasic
import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderAutUnitaryModel
import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphismCoord
import CFSG.StronglyEmbedded.BenderBinaryHermitian
import CFSG.StronglyEmbedded.MatrixGroups.PSU3Model
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderBasic

public section

namespace CFSG.StronglyEmbedded.BenderCentre

open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.ShultStronglyClosedTI
open CFSG.ShultStronglyClosedTI.UnitaryRootAutomorphism (coord_ext conj_snd_of_fst_eq_zero
  exists_fst_eq exists_trace_eq fst_commutator snd_commutator)
open CFSG.ComponentClassification.AschbacherToolkit.Bender (sylowCenter sylowCenter_le)
open CFSG.ComponentClassification.AschbacherToolkit.Bender.AutTransport (mem_map_iff
  mem_map_iff' mem_sylowCenter_map')
open CFSG.ComponentClassification.AschbacherToolkit.Bender.UnitaryAut (mem_sylowCenter_root)
open scoped commutatorElement

section Transport

private def CommutatorOnto {G : Type*} [Group G] (T : Subgroup G) : Prop :=
  ∀ r ∈ T, r ∉ sylowCenter T → ∀ z ∈ sylowCenter T, ∃ s ∈ T, ⁅s, r⁆ = z

private theorem CommutatorOnto.map {G G' : Type*} [Group G] [Group G'] {T : Subgroup G}
    (h : CommutatorOnto T) (e : G ≃* G') : CommutatorOnto (T.map e.toMonoidHom) := by
  intro r hr hrZ z hz
  obtain ⟨s, hs, hsz⟩ := h (e.symm r) ((mem_map_iff' e).mp hr)
    (fun h' => hrZ ((mem_sylowCenter_map' e).mpr h')) (e.symm z) ((mem_sylowCenter_map' e).mp hz)
  refine ⟨e s, (mem_map_iff e).mpr hs, ?_⟩
  calc ⁅e s, r⁆ = e ⁅s, e.symm r⁆ := by rw [map_commutatorElement, e.apply_symm_apply]
    _ = z := by rw [hsz, e.apply_symm_apply]

private theorem CommutatorOnto.sylow {G : Type*} [Group G] [Finite G] (R : Sylow 2 G)
    (h : CommutatorOnto (R : Subgroup G)) (T : Sylow 2 G) : CommutatorOnto (T : Subgroup G) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G R T
  have hT : (T : Subgroup G) = (R : Subgroup G).map (MulAut.conj g).toMonoidHom := by
    rw [← hg]
    rfl
  rw [hT]
  exact h.map (MulAut.conj g)

end Transport

section RootGroup

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private theorem commutatorOnto_root (J : HermitianForm 3 F) (q : ℕ)
    (hcard : Nat.card F = q ^ 2) (hfixed : Nat.card {x : F // J.conj x = x} = q) (hq : 2 ≤ q)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    CommutatorOnto (unitaryCoverRoot J hJ) := by
  rintro _ ⟨w, rfl⟩ hw z hz
  obtain ⟨v, rfl⟩ := sylowCenter_le _ hz
  have hw1 : w.1.1 ≠ 0 := fun h => hw ((mem_sylowCenter_root J q hcard hfixed hq hJ w).mpr h)
  have hv1 : v.1.1 = 0 := (mem_sylowCenter_root J q hcard hfixed hq hJ v).mp hz
  obtain ⟨u, hu⟩ := exists_trace_eq J q hcard hfixed (conj_snd_of_fst_eq_zero J hv1)
  obtain ⟨c, hc⟩ := exists_fst_eq J q hcard hfixed (u / J.conj w.1.1)
  refine ⟨hermitianUnipotentPSU J hJ c, ⟨c, rfl⟩, ?_⟩
  rw [← map_commutatorElement]
  congr 1
  refine coord_ext (by rw [fst_commutator, hv1]) ?_
  have hcw : J.conj w.1.1 ≠ 0 := (map_ne_zero J.conj).mpr hw1
  have e1 : u / J.conj w.1.1 * J.conj w.1.1 = u := div_mul_cancel₀ u hcw
  have e2 : w.1.1 * (J.conj u / w.1.1) = J.conj u := by field_simp
  rw [snd_commutator, hc, map_div₀, J.conj_involutive, e1, e2, ← hu, add_comm]

end RootGroup

theorem u3CommutatorOntoStatement_holds :
    ∀ (K : Type) [Group K] [Finite K] (n : ℕ), 2 ≤ n → Nonempty (K ≃* PSU3Model n) →
      ∀ S : Sylow 2 K, ∀ r ∈ (S : Subgroup K), r ∉ sylowCenter (S : Subgroup K) →
        ∀ z ∈ sylowCenter (S : Subgroup K), ∃ s ∈ (S : Subgroup K), ⁅s, r⁆ = z := by
  rintro K _ _ n hn ⟨e⟩ S
  let k := GaloisField 2 n
  let E := FiniteField.Extension k 2 2
  let J := binaryQuadraticHermitian n (by omega)
  have : CharP E 2 := CharP.of_ringHom_of_ne_zero (algebraMap k E) 2 (by norm_num)
  have hEcard : Nat.card E = (2 ^ n) ^ 2 := by
    rw [FiniteField.natCard_extension, GaloisField.card 2 n (by omega)]
  have hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n :=
    quadraticBinaryFrobenius_fixed_card n (by omega)
  have hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] := rfl
  obtain ⟨e₁⟩ := projectiveSpecialUnitary_equiv_PSU3Model J n hn hJ hEcard hfixed
  have : Finite (Matrix.ProjGenLinGroup (Fin 3) E) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_injective Subtype.val Subtype.coe_injective
  let φ : ProjectiveSpecialUnitaryMatrixGroup J ≃* K := e₁.trans e.symm
  let R := unitaryCoverSylow J n hn hEcard hfixed hJ
  have hR : CommutatorOnto (R : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) :=
    commutatorOnto_root J (2 ^ n) hEcard hfixed (Nat.le_self_pow (by omega) 2) hJ
  exact CommutatorOnto.sylow (R.mapSurjective (f := φ.toMonoidHom) φ.surjective) (hR.map φ) S

end CFSG.StronglyEmbedded.BenderCentre
