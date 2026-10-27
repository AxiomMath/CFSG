module

import all CFSG.LieType.Universal.SymplecticExtras.Matrices
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2SpNatTwo
import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2Sp4TwoRootSix
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7Iso
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallSp6Smith

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal.Symplectic CFSG.LieType.Universal.Symplectic.SpExtras CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5 CFSG.Quasithin.SmithCurtis
open CFSG.QuasithinUnique.Setup.X7

section NT

variable {K : Type} [Field K] [Finite K] [CharP K 2] {k : Type} [Field k] [CharP k 2]

omit [Finite K] [CharP K 2] [CharP k 2] in
private theorem spNT_matMap_elt {n : ℕ} (φ : K →+* k)
    (r : TauCeti.GLSymplecticFin.RootSubgroupIndex n) (c : K) :
    matMap φ (mat n K) (elt r c) = 1 + φ c • E k r := by
  rw [matMap_apply, mat_elt, Matrix.map_add φ φ.map_add,
    Matrix.map_one φ (map_zero φ) (map_one φ),
    Matrix.map_smul' φ c (E K r) φ.map_mul,
    CFSG.SeitzReduction.F4Pilot.map_E_of_ringHomClass φ r]

omit [Finite K] [CharP K 2] [CharP k 2] in
private theorem spNT_natMap_elt {n : ℕ} (φ : K →+* k)
    (r : TauCeti.GLSymplecticFin.RootSubgroupIndex n) (c : K)
    (v : Fin n ⊕ Fin n → k) :
    matRep (matMap φ (mat n K)) (elt r c) v = v + φ c • Matrix.mulVec (E k r) v := by
  rw [matRep_apply, spNT_matMap_elt, Matrix.add_mulVec, Matrix.one_mulVec,
    Matrix.smul_mulVec]

omit [CharP k 2] in
private theorem spNT_natMap_fixU {n : ℕ} (hn : 2 ≤ n) (φ : K →+* k) :
    (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin n)) (1 : k)) ∈
      (spCurtisDatum n K).fixU (matRep (matMap φ (mat n K))) := by
  intro g hg
  change g ∈ ⨆ γ ∈ {γ | γ ∈ CFSG.LieType.RootSystem.roots (isFiniteType_cartanC n) ∅ ∧
    0 < CFSG.LieType.Steinberg.ht γ}, rootGroup n K γ at hg
  have hbelow := idBelow_of_mem_iSup 1 _ (fun γ hγ =>
    ⟨hγ.1, by
      have hpos : 0 < CFSG.LieType.Steinberg.ht γ := hγ.2
      simpa only [one_mul] using (show 1 ≤ CFSG.LieType.Steinberg.ht γ by omega)⟩) hg
  change Matrix.mulVec ((mat n K g).map φ)
    (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin n)) (1 : k)) = _
  ext a
  rw [Matrix.mulVec_single_one, Matrix.col_apply, Matrix.map_apply]
  have hlev : (1 : ℤ) * lvl (Sum.inl (⟨0, by omega⟩ : Fin n)) - (1 : ℤ) * lvl a < 1 := by
    rcases a with i | i <;> simp only [lvl] <;> omega
  rw [hbelow _ _ hlev]
  simp [Matrix.one_apply, Pi.single_apply]

omit [Finite K] [CharP K 2] [CharP k 2] in
private theorem spNT_natMap_diag {n : ℕ} (hn : 2 ≤ n) (φ : K →+* k) (t : Fin n → Kˣ) :
    matRep (matMap φ (mat n K)) (diagHom n K t)
      (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin n)) (1 : k)) =
      φ (t ⟨0, by omega⟩) • Pi.single (Sum.inl (⟨0, by omega⟩ : Fin n)) (1 : k) := by
  have hd : mat n K (diagHom n K t) =
      Matrix.diagonal (Sum.elim (fun i => (t i : K)) (fun i => ((t i)⁻¹ : Kˣ))) :=
    mat_equiv_diagonal t
  rw [matRep_apply, matMap_apply, Matrix.mulVec_single_one]
  ext a
  rw [Matrix.col_apply, Matrix.map_apply, hd]
  by_cases h : a = Sum.inl (⟨0, by omega⟩ : Fin n)
  · subst h
    simp [Pi.smul_apply]
  · rw [Matrix.diagonal_apply, if_neg h, Pi.smul_apply, Pi.single_apply, if_neg h]
    simp

omit [Finite K] in
private theorem spNT_natMap_weyl {n : ℕ} (hn : 2 ≤ n) (φ : K →+* k) (i : Fin n) :
    matRep (matMap φ (mat n K)) (weylRep n K i)
      (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin n)) (1 : k)) =
      if i.val = 0 then Pi.single (Sum.inl (⟨1, by omega⟩ : Fin n)) (1 : k)
      else Pi.single (Sum.inl (⟨0, by omega⟩ : Fin n)) (1 : k) := by
  by_cases hi : i.val = 0
  · rw [if_pos hi]
    have hi0 : i = ⟨0, by omega⟩ := Fin.ext hi
    rw [hi0]
    have h0 : (⟨0, by omega⟩ : Fin n).val + 1 < n := by show 0 + 1 < n; omega
    rw [CFSG.LieType.Universal.Symplectic.SpExtras.weylRep_eq_short h0]
    rw [show (-1 : K) = 1 from CharTwo.neg_eq 1]
    simp only [map_mul, Module.End.mul_apply, spNT_natMap_elt,
      sp_E_difference_mulVec_e0 (n := n) hn (a := (⟨0, by omega⟩ : Fin n))
        (b := (⟨1, h0⟩ : Fin n)) (ne_succ' h0) (by simp),
      sp_E_difference_mulVec_e0_of (n := n) hn (a := (⟨1, h0⟩ : Fin n))
        (b := (⟨0, by omega⟩ : Fin n)) (ne_succ' h0).symm rfl rfl,
      sp_E_difference_mulVec_e1 (n := n) hn (a := (⟨0, by omega⟩ : Fin n))
        (b := (⟨1, h0⟩ : Fin n)) (ne_succ' h0) rfl rfl,
      Matrix.mulVec_add, map_one, one_smul, add_zero, zero_add]
    abel_nf
    ext a
    simp [CharTwo.two_eq_zero]
  · rw [if_neg hi]
    by_cases hshort : i.val + 1 < n
    · rw [CFSG.LieType.Universal.Symplectic.SpExtras.weylRep_eq_short hshort]
      rw [show (-1 : K) = 1 from CharTwo.neg_eq 1]
      simp only [map_mul, Module.End.mul_apply, spNT_natMap_elt,
        sp_E_difference_mulVec_e0 (n := n) hn (a := i) (b := (⟨i.val + 1, hshort⟩ : Fin n))
          (ne_succ' hshort) (by simp),
        sp_E_difference_mulVec_e0 (n := n) hn (a := (⟨i.val + 1, hshort⟩ : Fin n)) (b := i)
          (ne_succ' hshort).symm hi,
        map_one, one_smul, add_zero]
    · rw [CFSG.LieType.Universal.Symplectic.SpExtras.weylRep_eq_long hshort]
      rw [show (-1 : K) = 1 from CharTwo.neg_eq 1]
      simp only [map_mul, Module.End.mul_apply, spNT_natMap_elt,
        sp_E_positiveLong_mulVec_e0 (n := n) hn i,
        sp_E_negativeLong_mulVec_e0 (n := n) hn hi,
        map_one, one_smul, add_zero]

private theorem spNT_natMap_hecke {n : ℕ} (hn : 2 ≤ n) (hK : 4 ≤ Nat.card K)
    (φ : K →+* k) (i : Fin n) :
    (spCurtisDatum n K).heckeT (matRep (matMap φ (mat n K))) i
      (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin n)) (1 : k)) = 0 := by
  classical
  let _ : Fintype K := Fintype.ofFinite K
  have hK' : 4 ≤ Fintype.card K := by
    rwa [← Nat.card_eq_fintype_card]
  let D := spCurtisDatum n K
  have : Fintype (D.X i) := Fintype.ofFinite _
  erw [CurtisDatum.heckeT_apply D]
  have hbij : Function.Bijective (fun c : K =>
      (⟨elt (simpleIdx i) c, (mem_X_iff i).mpr ⟨c, rfl⟩⟩ : D.X i)) := by
    refine ⟨fun c d hcd => elt_injective _ (congrArg Subtype.val hcd), fun x => ?_⟩
    obtain ⟨c, hc⟩ := (mem_X_iff i).mp x.2
    exact ⟨c, Subtype.ext hc.symm⟩
  rw [← hbij.sum_comp]
  simp only [map_mul, Module.End.mul_apply]
  change (∑ c : K, matRep (matMap φ (mat n K)) (elt (simpleIdx i) c)
    (matRep (matMap φ (mat n K)) (weylRep n K i)
      (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin n)) (1 : k)))) = 0
  rw [spNT_natMap_weyl hn φ i]
  have hcard : (Fintype.card K : k) = 0 := natCast_card_eq_zero_charTwo
  have hsum : ∑ c : K, φ c = 0 := sum_additive_eq_zero hK' φ.toAddMonoidHom
  by_cases hi : i.val = 0
  · rw [if_pos hi]
    have hterm : ∀ c : K, matRep (matMap φ (mat n K)) (elt (simpleIdx i) c)
        (Pi.single (Sum.inl (⟨1, by omega⟩ : Fin n)) (1 : k)) =
        Pi.single (Sum.inl (⟨1, by omega⟩ : Fin n)) (1 : k) +
          φ c • Pi.single (Sum.inl (⟨0, by omega⟩ : Fin n)) (1 : k) := by
      intro c
      have hi0 : i = ⟨0, by omega⟩ := Fin.ext hi
      rw [hi0, spNT_natMap_elt, sp_E_simpleIdx_zero_mulVec_e1 hn]
    rw [Finset.sum_congr rfl (fun c _ => hterm c), Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, ← Finset.sum_smul, ← Nat.cast_smul_eq_nsmul k, hcard, hsum]
    simp
  · rw [if_neg hi]
    have hterm : ∀ c : K, matRep (matMap φ (mat n K)) (elt (simpleIdx i) c)
        (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin n)) (1 : k)) =
        Pi.single (Sum.inl (⟨0, by omega⟩ : Fin n)) (1 : k) := by
      intro c
      rw [spNT_natMap_elt, sp_E_simpleIdx_mulVec_e0 hn i, smul_zero, add_zero]
    rw [Finset.sum_congr rfl (fun c _ => hterm c), Finset.sum_const, Finset.card_univ,
      ← Nat.cast_smul_eq_nsmul k, hcard]
    simp

end NT

theorem isCurtisType_spn_matMap {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} (hn : 2 ≤ n)
    (hK : 4 ≤ Nat.card K) {k : Type} [Field k] [CharP k 2] (φ : K →+* k)
    (χ : StatedSp n K → k)
    (hχ : ∀ t : Fin n → Kˣ, χ (diagHom n K t) = φ (t ⟨0, by omega⟩ : K)) :
    (spCurtisDatum n K).IsCurtisType (matRep (matMap φ (mat n K)))
      (Pi.single (Sum.inl ⟨0, by omega⟩) 1) χ 0 := by
  refine ⟨spNT_natMap_fixU hn φ, Pi.single_ne_zero_iff.mpr one_ne_zero, ?_, ?_⟩
  · intro h hh
    obtain ⟨t, rfl⟩ := spCurtisDatum_H_le hh
    rw [hχ]
    exact spNT_natMap_diag hn φ t
  · intro i
    simpa using spNT_natMap_hecke hn hK φ i

end CFSG.LocalAnalysis.WeakClosure81
