module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpPlaneFrameDefs
public import CFSG.LocalAnalysis.StandardType.GGSignedCoordBlocks
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniJoinTwo
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBDenseDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBDenseUniModel
import CFSG.LocalAnalysis.StandardType.GGSignedCoordConj
import CFSG.LocalAnalysis.StandardType.GGQTwoSUThreeDiagonalComm
import CFSG.LocalAnalysis.StandardType.GGSuNsRootGenRestrictedTriples
import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

variable {G : Type} [Group G] {p n : ℕ} {Bs : Subgroup G}

theorem ggBsCoordZeroOn_diagAut
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (d : Fin n → ZMod p) (hd : ∀ i, d i * d i = 1) (S : Set (Fin n)) :
    ggBsCoordZeroOn Bs (eta.trans (SpCoord.diagAut d hd)) S =
      ggBsCoordZeroOn Bs eta S := by
  ext g
  rw [mem_ggBsCoordZeroOn, mem_ggBsCoordZeroOn]
  constructor
  · rintro ⟨hg, hS⟩
    refine ⟨hg, fun i hi => ?_⟩
    have h := hS i hi
    change d i * Multiplicative.toAdd (eta ⟨g, hg⟩ i) = 0 at h
    change Multiplicative.toAdd (eta ⟨g, hg⟩ i) = 0
    have h' := congrArg (fun z => d i * z) h
    simpa only [← mul_assoc, hd i, one_mul, mul_zero] using h'
  · rintro ⟨hg, hS⟩
    refine ⟨hg, fun i hi => ?_⟩
    change d i * Multiplicative.toAdd (eta ⟨g, hg⟩ i) = 0
    have h := hS i hi
    change Multiplicative.toAdd (eta ⟨g, hg⟩ i) = 0 at h
    rw [h, mul_zero]

theorem ggBlockComm_diagAut
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (d : Fin n → ZMod p) (hd : ∀ i, d i * d i = 1) (S : Set (Fin n)) :
    ggBlockComm Bs (eta.trans (SpCoord.diagAut d hd)) S = ggBlockComm Bs eta S := by
  rw [ggBlockComm, ggBlockComm, ggBsCoordZeroOn_diagAut]

theorem map_ggAutomizer_diagAut_eq_aPermutationFull {X : Subgroup G}
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (d : Fin n → ZMod p) (hd : ∀ i, d i * d i = 1)
    (hA : (ggAutomizer X Bs).map (MulAut.congr eta).toMonoidHom =
      (aPermutationFull n p).map (MulAut.conj (SpCoord.diagAut d hd)).toMonoidHom) :
    (ggAutomizer X Bs).map
        (MulAut.congr (eta.trans (SpCoord.diagAut d hd))).toMonoidHom =
      aPermutationFull n p := by
  let δ := SpCoord.diagAut d hd
  have hδ : δ * δ = 1 := by
    ext v i
    change d i * (d i * Multiplicative.toAdd (v i)) = Multiplicative.toAdd (v i)
    rw [← mul_assoc, hd i, one_mul]
  have hmap : (ggAutomizer X Bs).map (MulAut.congr (eta.trans δ)).toMonoidHom =
      ((ggAutomizer X Bs).map (MulAut.congr eta).toMonoidHom).map
        (MulAut.conj δ).toMonoidHom := by
    rw [Subgroup.map_map]
    congr 1
  have hcomp : (MulAut.conj δ).toMonoidHom.comp (MulAut.conj δ).toMonoidHom =
      MonoidHom.id (MulAut (Fin n → Multiplicative (ZMod p))) := by
    apply MonoidHom.ext
    intro a
    change δ * (δ * a * δ⁻¹) * δ⁻¹ = a
    calc
      δ * (δ * a * δ⁻¹) * δ⁻¹ = (δ * δ) * a * (δ * δ)⁻¹ := by group
      _ = a := by rw [hδ]; simp
  rw [hmap, hA, Subgroup.map_map, hcomp, Subgroup.map_id]

theorem exists_diagAut_map_conj_aPermutationFull
    {δ : MulAut (Fin n → Multiplicative (ZMod p))} (hδ : δ ∈ bSignedFull n p) :
    ∃ (d : Fin n → ZMod p) (hd : ∀ i, d i * d i = 1),
      (aPermutationFull n p).map (MulAut.conj δ).toMonoidHom =
        (aPermutationFull n p).map (MulAut.conj (SpCoord.diagAut d hd)).toMonoidHom := by
  obtain ⟨d, hsign, hdconst⟩ := exists_signs_apply_const hδ
  let hd : ∀ i, d i * d i = 1 := fun i => SpCoord.coord_sign_mul_self (hsign i)
  have hdiag : SpCoord.diagAut d hd ∈ bSignedFull n p := by
    rw [bSignedFull_eq_signedPermSubgroup]
    change SpCoord.IsSignedPerm (SpCoord.diagAut d hd)
    exact ⟨1, d, hsign, fun f i => rfl⟩
  have hconst : δ (fun _ => Multiplicative.ofAdd (1 : ZMod p)) =
      SpCoord.diagAut d hd (fun _ => Multiplicative.ofAdd 1) := by
    funext i
    change Multiplicative.toAdd (δ (fun _ => Multiplicative.ofAdd (1 : ZMod p)) i) = d i * 1
    exact hdconst 1 i
  exact ⟨d, hd, aPermutationFull_map_conj_eq_of_apply_one hδ hdiag (Or.inl hconst)⟩

theorem GGSecFiveBCoordBDenseNbr.exists_unitary_frame_of_marking
    [Finite G] {B L D J X : Subgroup G} {x : G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGConfig 3 B Bs x L D J) (hlt : B < Bs) (hn : 5 ≤ n)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3)))
    (hDense : GGSecFiveBCoordBDenseNbr 3 Bs 𝒦 n eta X)
    (hmark : GGInnerDiagOnLabel
      (fun _ lab => lab = (⟨.twA, n - 1, 1⟩ : CFSG.Assembly.LargeEvenLabel)) 3 Bs X)
    (π : Equiv.Perm (Fin n)) :
    ∃ (d : Fin n → ZMod 3) (hd : ∀ i, d i * d i = 1)
      (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (σ : ↥(unitarySU 2 1 F n) →* G) (χ : Multiplicative (ZMod 3) →* Fˣ),
      UnitaryFieldData 2 1 F ∧
        GGSecFiveBPermUniLFrame Bs X (eta.trans (SpCoord.diagAut d hd)) π σ χ := by
  obtain ⟨-, δ, hδ, hAδ⟩ := hDense
  obtain ⟨d, hd, heq⟩ := exists_diagAut_map_conj_aPermutationFull hδ
  have hA : (ggAutomizer X Bs).map (MulAut.congr eta).toMonoidHom =
      (aPermutationFull n 3).map (MulAut.conj (SpCoord.diagAut d hd)).toMonoidHom :=
    hAδ.trans heq
  have hA' := map_ggAutomizer_diagAut_eq_aPermutationFull eta d hd hA
  obtain ⟨F, hFld, hFin, hChar, hN, φ, -, hM, hdiag⟩ :=
    exists_unitary_model_of_aPermutationFull_of_B_lt_Bs hcfg hlt hn
      (eta.trans (SpCoord.diagAut d hd)) hA' hmark
  obtain ⟨σ, χ, hF⟩ := exists_uniLFrame_of_model Nat.prime_three (by norm_num)
    hcfg.2.1.2.1 hcfg.2.1.2.2.2
    (card_inf_centralizer_le_of_aPermutationFull (by omega)
      (eta.trans (SpCoord.diagAut d hd)) hA')
    (by omega) (eta.trans (SpCoord.diagAut d hd)) hA' hN φ hM hdiag π
  exact ⟨d, hd, F, hFld, hFin, hChar, σ, χ, hM.field, hF⟩

theorem GGSecFiveBPermUniLFrame.le_sup_map_conj_of_original_swap
    {F : Type} [Field F] [Finite F] (h : UnitaryFieldData 2 1 F)
    (hp : p.Prime) (hn : 4 ≤ n) {X M : Subgroup G}
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (d : Fin n → ZMod p) (hd : ∀ i, d i * d i = 1)
    {π : Equiv.Perm (Fin n)} {σ : ↥(unitarySU 2 1 F n) →* G}
    {χ : Multiplicative (ZMod p) →* Fˣ}
    (hF : GGSecFiveBPermUniLFrame Bs X (eta.trans (SpCoord.diagAut d hd)) π σ χ)
    {i0 j0 : Fin n} (hij : i0 ≠ j0) {g : G}
    (hg : g ∈ Subgroup.normalizer (Bs : Set G))
    (hτ : MulAut.congr eta (ggConjAut Bs hg) =
      SpCoord.permAut (Equiv.swap i0 j0))
    (hM : ∀ S : Finset (Fin n), S.card = 3 → i0 ∉ S →
      ggBlockComm Bs eta (S : Set (Fin n)) ≤ M) :
    X ≤ M ⊔ M.map (MulAut.conj g).toMonoidHom := by
  refine hF.le_sup_map_conj_of_triples_of_covariance
    (SuNsRootGen.iSup_blockSU_triples_avoid_pair h hn
      (π.symm i0) (π.symm j0) (π.symm.injective.ne hij))
    (fun S hS => hF.map_blockSU_triple_le_ggBlockComm h hp S hS) ?_ ?_
  · intro S
    rw [ggBlockComm_diagAut, ggBlockComm_diagAut]
    exact ggBlockComm_map_conj (S := S) hg hτ
  · intro S hS hi
    rw [ggBlockComm_diagAut]
    exact hM S hS hi

end CFSG.StandardType

end
