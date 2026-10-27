module

public import CFSG.Timmesfeld.Transvection.ModelRankSp
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Pairs
import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCFrame

public section

namespace CFSG.Timmesfeld.ARS.CaseM

open Matrix CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open CFSG.LieType.Universal.Symplectic
open CFSG.Timmesfeld CFSG.Timmesfeld.RankOne
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open scoped MatrixGroups

variable {n : ℕ} {F : Type} [Field F]

theorem form_eq_spForm (u v : Fin n ⊕ Fin n → F) : form u v = spForm u v := rfl

theorem exists_mat_mulVec_eq_pair {v w v' w' : Fin n ⊕ Fin n → F}
    (h : spForm v w = 1) (h' : spForm v' w' = 1) :
    ∃ g : StatedSp n F, SpExtras.mat n F g *ᵥ v = v' ∧
      SpExtras.mat n F g *ᵥ w = w' := by
  have hn : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := by omega
    subst hn0
    simp [spForm, dotProduct] at h
  let k : Fin n := ⟨0, hn⟩
  have hf : form v w = 1 := by rw [form_eq_spForm]; exact h
  have hf' : form v' w' = 1 := by rw [form_eq_spForm]; exact h'
  obtain ⟨g₁, hg₁v, hg₁w⟩ := exists_sp_apply_eq_at k v w hf
  obtain ⟨g₂, hg₂v, hg₂w⟩ := exists_sp_apply_eq_at k v' w' hf'
  refine ⟨g₂ * g₁⁻¹, ?_, ?_⟩
  · rw [map_mul, ← Matrix.mulVec_mulVec]
    have h1 : SpExtras.mat n F g₁⁻¹ *ᵥ v = Pi.single (Sum.inl k) 1 := by
      rw [← hg₁v, Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one,
        Matrix.one_mulVec]
    rw [h1, hg₂v]
  · rw [map_mul, ← Matrix.mulVec_mulVec]
    have h1 : SpExtras.mat n F g₁⁻¹ *ᵥ w = Pi.single (Sum.inr k) 1 := by
      rw [← hg₁w, Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one,
        Matrix.one_mulVec]
    rw [h1, hg₂w]

theorem commute_of_mat_mulVec_eq {v : Fin n ⊕ Fin n → F} {T : Subgroup (StatedSp n F)}
    (hT : IsTransGroup v T) {g : StatedSp n F} (hg : SpExtras.mat n F g *ᵥ v = v) :
    ∀ t ∈ T, g * t = t * g := by
  intro t ht
  obtain ⟨c, hc⟩ := (hT.1 t).1 ht
  have h1 : SpExtras.mat n F (g * t * g⁻¹) = SpExtras.mat n F t := by
    rw [mat_conj_of_mat_eq hc g, hg, ← hc]
  have h2 : g * t * g⁻¹ = t := SpExtras.mat_injective h1
  calc g * t = (g * t * g⁻¹) * g := by group
    _ = t * g := by rw [h2]

theorem normalizes_of_mat_mulVec_eq_smul {v : Fin n ⊕ Fin n → F}
    {T : Subgroup (StatedSp n F)} (hT : IsTransGroup v T) {g : StatedSp n F} {c : F}
    (hg : SpExtras.mat n F g *ᵥ v = c • v) :
    ∀ t ∈ T, g * t * g⁻¹ ∈ T := by
  intro t ht
  obtain ⟨a, ha⟩ := (hT.1 t).1 ht
  rw [hT.1]
  exact ⟨c * c * a, by rw [mat_conj_of_mat_eq ha g, hg, spTrans_smul]⟩

theorem mat_longBlock_mulVec_plane (k : Fin n) (s : SL(2, F)) (u : Fin 2 → F) :
    SpExtras.mat n F (longBlock F n k s) *ᵥ
        (u 0 • (Pi.single (Sum.inl k) 1 : Fin n ⊕ Fin n → F) +
          u 1 • (Pi.single (Sum.inr k) 1 : Fin n ⊕ Fin n → F)) =
      (((s : Matrix (Fin 2) (Fin 2) F) *ᵥ u) 0) •
          (Pi.single (Sum.inl k) 1 : Fin n ⊕ Fin n → F) +
        (((s : Matrix (Fin 2) (Fin 2) F) *ᵥ u) 1) •
          (Pi.single (Sum.inr k) 1 : Fin n ⊕ Fin n → F) := by
  rw [mat_longBlock, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
    Matrix.mulVec_single_one, Matrix.mulVec_single_one]
  ext r
  simp only [Pi.add_apply, Pi.smul_apply, Matrix.col_apply, smul_eq_mul]
  rcases r with i | i
  · by_cases hik : i = k
    · subst hik
      simp [CFSG.LieType.Steinberg.Sp.blockMat, Matrix.mulVec, Fin.sum_univ_two]
      ring
    · simp [CFSG.LieType.Steinberg.Sp.blockMat, hik, Pi.single_eq_of_ne,
        Matrix.one_apply, Matrix.mulVec, Fin.sum_univ_two]
  · by_cases hik : i = k
    · subst hik
      simp [CFSG.LieType.Steinberg.Sp.blockMat, Matrix.mulVec, Fin.sum_univ_two]
      ring
    · simp [CFSG.LieType.Steinberg.Sp.blockMat, hik, Pi.single_eq_of_ne,
        Matrix.one_apply, Matrix.mulVec, Fin.sum_univ_two]

theorem mat_longBlock_mulVec_perp (k : Fin n) (s : SL(2, F)) {x : Fin n ⊕ Fin n → F}
    (hx₁ : x (Sum.inl k) = 0) (hx₂ : x (Sum.inr k) = 0) :
    SpExtras.mat n F (longBlock F n k s) *ᵥ x = x := by
  rw [mat_longBlock]
  exact mulVec_eq_self_of_isSupp (isSupp_blockMat k _) (by
    intro t ht
    rcases mem_coords.1 ht with rfl | rfl
    · exact hx₁
    · exact hx₂)

theorem mat_longBlock_conj_mulVec_plane (k : Fin n) (g : StatedSp n F) (s : SL(2, F))
    (u : Fin 2 → F) :
    SpExtras.mat n F (g * longBlock F n k s * g⁻¹) *ᵥ
        (u 0 • (SpExtras.mat n F g *ᵥ Pi.single (Sum.inl k) 1) +
          u 1 • (SpExtras.mat n F g *ᵥ Pi.single (Sum.inr k) 1)) =
      (((s : Matrix (Fin 2) (Fin 2) F) *ᵥ u) 0) •
          (SpExtras.mat n F g *ᵥ Pi.single (Sum.inl k) 1) +
        (((s : Matrix (Fin 2) (Fin 2) F) *ᵥ u) 1) •
          (SpExtras.mat n F g *ᵥ Pi.single (Sum.inr k) 1) := by
  have hlin : ∀ v : Fin 2 → F,
      v 0 • (SpExtras.mat n F g *ᵥ (Pi.single (Sum.inl k) 1 : Fin n ⊕ Fin n → F)) +
          v 1 • (SpExtras.mat n F g *ᵥ Pi.single (Sum.inr k) 1) =
        SpExtras.mat n F g *ᵥ
          (v 0 • (Pi.single (Sum.inl k) 1 : Fin n ⊕ Fin n → F) +
            v 1 • Pi.single (Sum.inr k) 1) := by
    intro v
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
  have hcancel : ∀ y : Fin n ⊕ Fin n → F,
      SpExtras.mat n F g⁻¹ *ᵥ (SpExtras.mat n F g *ᵥ y) = y := by
    intro y
    rw [Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mulVec]
  have hmat : SpExtras.mat n F (g * longBlock F n k s * g⁻¹) =
      SpExtras.mat n F g * SpExtras.mat n F (longBlock F n k s) *
        SpExtras.mat n F g⁻¹ := by
    rw [map_mul, map_mul]
  rw [hlin u, hmat, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    hcancel, mat_longBlock_mulVec_plane, ← hlin (s *ᵥ u)]

theorem spForm_single_inl_single_inr (k : Fin n) :
    spForm (Pi.single (Sum.inl k) (1 : F) : Fin n ⊕ Fin n → F)
      (Pi.single (Sum.inr k) (1 : F) : Fin n ⊕ Fin n → F) = 1 := by
  rw [spForm, Matrix.mulVec_single_one, dotProduct, Finset.sum_eq_single (Sum.inl k)]
  · simp [spGram, fromBlocks, Matrix.one_apply]
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · simp

theorem spForm_longBlock_pair (k : Fin n) (g : StatedSp n F) :
    spForm (SpExtras.mat n F g *ᵥ Pi.single (Sum.inl k) 1)
        (SpExtras.mat n F g *ᵥ Pi.single (Sum.inr k) 1) =
      spForm (Pi.single (Sum.inl k) 1) (Pi.single (Sum.inr k) 1) := by
  rw [← form_eq_spForm, ← form_eq_spForm]
  exact form_mulVec g (Pi.single (Sum.inl k) 1) (Pi.single (Sum.inr k) 1)

theorem spTrans_single_inl (k : Fin n) (c : F) :
    spTrans (Pi.single (Sum.inl k) 1 : Fin n ⊕ Fin n → F) c =
      Matrix.transvection (Sum.inl k) (Sum.inr k) c := by
  rw [spTrans, spNil_inl, Matrix.transvection, Matrix.smul_single, smul_eq_mul, mul_one]

theorem spTrans_single_inr (k : Fin n) (c : F) :
    spTrans (Pi.single (Sum.inr k) 1 : Fin n ⊕ Fin n → F) (-c) =
      Matrix.transvection (Sum.inr k) (Sum.inl k) c := by
  rw [spTrans, spNil_inr, Matrix.transvection]
  simp only [smul_neg, neg_smul, neg_neg, Matrix.smul_single, smul_eq_mul, mul_one]

theorem mat_longBlock_upperElt (k : Fin n) (c : F) :
    SpExtras.mat n F (longBlock F n k (upperElt F c)) =
      spTrans (Pi.single (Sum.inl k) 1 : Fin n ⊕ Fin n → F) c := by
  rw [show upperElt F c = CFSG.LieType.Steinberg.sl2Upper c from rfl,
    longBlock_sl2Upper, SpExtras.mat_elt_positiveLong, spTrans_single_inl]

theorem mat_longBlock_lowerElt (k : Fin n) (c : F) :
    SpExtras.mat n F (longBlock F n k (lowerElt F c)) =
      spTrans (Pi.single (Sum.inr k) 1 : Fin n ⊕ Fin n → F) (-c) := by
  rw [show lowerElt F c = CFSG.LieType.Steinberg.sl2Lower c from rfl,
    longBlock_sl2Lower, SpExtras.mat_elt_negativeLong, spTrans_single_inr]

theorem isTransGroup_upper_longBlock (k : Fin n) :
    IsTransGroup (Pi.single (Sum.inl k) 1 : Fin n ⊕ Fin n → F)
      ((upperUnipotent F).map (longBlock F n k)) := by
  refine ⟨fun x => ?_, fun c => ?_⟩
  · rw [Subgroup.mem_map]
    constructor
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨c, rfl⟩ := (mem_upperUnipotent_iff F).1 hu
      exact ⟨c, mat_longBlock_upperElt k c⟩
    · rintro ⟨c, hc⟩
      refine ⟨upperElt F c, (mem_upperUnipotent_iff F).2 ⟨c, rfl⟩, ?_⟩
      exact SpExtras.mat_injective (by rw [mat_longBlock_upperElt, ← hc])
  · exact ⟨longBlock F n k (upperElt F c), mat_longBlock_upperElt k c⟩

theorem isTransGroup_lower_longBlock (k : Fin n) :
    IsTransGroup (Pi.single (Sum.inr k) 1 : Fin n ⊕ Fin n → F)
      ((lowerUnipotent F).map (longBlock F n k)) := by
  refine ⟨fun x => ?_, fun c => ?_⟩
  · rw [Subgroup.mem_map]
    constructor
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨c, rfl⟩ := (mem_lowerUnipotent_iff F).1 hu
      exact ⟨-c, mat_longBlock_lowerElt k c⟩
    · rintro ⟨c, hc⟩
      refine ⟨lowerElt F (-c), (mem_lowerUnipotent_iff F).2 ⟨-c, rfl⟩, ?_⟩
      exact SpExtras.mat_injective (by rw [mat_longBlock_lowerElt, neg_neg, ← hc])
  · exact ⟨longBlock F n k (lowerElt F (-c)), by rw [mat_longBlock_lowerElt, neg_neg]⟩

theorem isTransGroup_upper_longBlock_conj (k : Fin n) (g : StatedSp n F) :
    IsTransGroup (SpExtras.mat n F g *ᵥ (Pi.single (Sum.inl k) 1 : Fin n ⊕ Fin n → F))
      ((upperUnipotent F).map ((MulAut.conj g).toMonoidHom.comp (longBlock F n k))) := by
  simpa only [CFSG.Timmesfeld.ARS.conjSub, Subgroup.map_map] using
    (isTransGroup_upper_longBlock (F := F) k).conjSub g

theorem isTransGroup_lower_longBlock_conj (k : Fin n) (g : StatedSp n F) :
    IsTransGroup (SpExtras.mat n F g *ᵥ (Pi.single (Sum.inr k) 1 : Fin n ⊕ Fin n → F))
      ((lowerUnipotent F).map ((MulAut.conj g).toMonoidHom.comp (longBlock F n k))) := by
  simpa only [CFSG.Timmesfeld.ARS.conjSub, Subgroup.map_map] using
    (isTransGroup_lower_longBlock (F := F) k).conjSub g

theorem rootGroup_last_eq_map_upper (hn : 1 ≤ n) :
    (CFSG.LieType.Universal.Symplectic.rootDatum n F).rootGroup
        (Pi.single (⟨n - 1, by omega⟩ : Fin n) (1 : ℤ)) =
      (upperUnipotent F).map (longBlock F n ⟨n - 1, by omega⟩) := by
  exact (CFSG.Timmesfeld.Transvection.ModelRank.isTransGroup_rootGroup_last (K := F) hn).eq
    (isTransGroup_upper_longBlock (F := F) ⟨n - 1, by omega⟩)

end CFSG.Timmesfeld.ARS.CaseM
