module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.L3OvDefs
public import CFSG.LocalAnalysis.AGLEmbedding.LinearThreeKitRadical
import CFSG.RankThree.PartOne.KFOUT3.CycUnits
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614K136Torus
public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
open scoped MatrixGroups
open CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614K136
  (not_three_dvd_two_pow_sub_one)

variable {F : Type} [Field F]

private abbrev lineE2 : Submodule F (Fin 3 → F) := F ∙ (Pi.single 2 1 : Fin 3 → F)

private abbrev planeE01 : Submodule F (Fin 3 → F) := flagSpace 3 F 2

private theorem zNF_mulVec [CharP F 2] (v : Fin 3 → F) :
    (zNF F : Matrix (Fin 3) (Fin 3) F) *ᵥ v = ![v 1, v 0 + v 1, v 2] := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hneg : (-1 : F) = 1 := by
    have h11 : (1 : F) + 1 = 0 := by rw [one_add_one_eq_two, h2]
    exact neg_eq_of_add_eq_zero_right h11
  rw [show (zNF F : Matrix (Fin 3) (Fin 3) F) = !![0, -1, 0; 1, -1, 0; 0, 0, 1] from rfl]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h2, hneg]

private theorem one_add_zNF_add_sq [CharP F 2] :
    (1 : Matrix (Fin 3) (Fin 3) F) + (zNF F : Matrix (Fin 3) (Fin 3) F) +
        (zNF F : Matrix (Fin 3) (Fin 3) F) * (zNF F : Matrix (Fin 3) (Fin 3) F) =
      Matrix.diagonal ![0, 0, 1] := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have h3 : (1 : F) + 1 + 1 = 1 := by
    rw [show (1 : F) + 1 + 1 = 2 + 1 by ring, h2, zero_add]
  rw [show (zNF F : Matrix (Fin 3) (Fin 3) F) = !![0, -1, 0; 1, -1, 0; 0, 0, 1] from rfl]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal, h2, h3] <;>
    ring

private theorem zNF_add_sq_mulVec [CharP F 2] (v : Fin 3 → F) :
    ((1 : Matrix (Fin 3) (Fin 3) F) + (zNF F : Matrix (Fin 3) (Fin 3) F) +
        (zNF F : Matrix (Fin 3) (Fin 3) F) * (zNF F : Matrix (Fin 3) (Fin 3) F)) *ᵥ v =
      v 2 • (Pi.single 2 1 : Fin 3 → F) := by
  rw [one_add_zNF_add_sq]
  funext i
  rw [Matrix.mulVec_diagonal]
  fin_cases i <;> simp [Pi.single_apply]

private theorem zNF_mulVec_mem_plane [CharP F 2] {v : Fin 3 → F} (hv : v ∈ planeE01) :
    (zNF F : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ planeE01 := by
  rw [CFSG.AGLEmbedding.LinearThreeKit.mem_flagSpace_two_iff] at hv ⊢
  rw [zNF_mulVec]
  simpa using hv

private theorem sq_add_mul_add_sq_ne_zero [Finite F] [CharP F 2] {f : ℕ}
    (hcard : Nat.card F = 2 ^ f) (hodd : Odd f) {a b : F}
    (h : a ^ 2 + a * b + b ^ 2 = 0) : a = 0 ∧ b = 0 := by
  rcases eq_or_ne b 0 with rfl | hb
  · simp only [mul_zero, add_zero, zero_pow (by norm_num : 2 ≠ 0), add_zero] at h
    exact ⟨(pow_eq_zero_iff (by norm_num : 2 ≠ 0)).mp h, rfl⟩
  · exfalso
    set t := a * b⁻¹ with ht
    have hb2 : b ^ 2 ≠ 0 := pow_ne_zero 2 hb
    have hbt : b * t = a := by
      rw [ht]
      field_simp
    have htq : t ^ 2 + t + 1 = 0 := by
      have hmul : b ^ 2 * (t ^ 2 + t + 1) = 0 := by
        calc b ^ 2 * (t ^ 2 + t + 1) = (b * t) ^ 2 + (b * t) * b + b ^ 2 := by ring
          _ = a ^ 2 + a * b + b ^ 2 := by rw [hbt]
          _ = 0 := h
      exact (mul_eq_zero.mp hmul).resolve_left hb2
    exact CFSG.RankThree.PartOne.KFOUT3.quad_ne_zero
      (by rw [hcard]; exact not_three_dvd_two_pow_sub_one hodd) t htq

private theorem plane_eq_span_of_ne_zero [Finite F] [CharP F 2] {f : ℕ}
    (hcard : Nat.card F = 2 ^ f) (hodd : Odd f)
    {v : Fin 3 → F} (hv : v ∈ planeE01) (hv0 : v ≠ 0) :
    planeE01 = Submodule.span F {v, (zNF F : Matrix (Fin 3) (Fin 3) F) *ᵥ v} := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hv2 : v 2 = 0 := (CFSG.AGLEmbedding.LinearThreeKit.mem_flagSpace_two_iff).mp hv
  have hveq : v = ![v 0, v 1, 0] := by
    ext i; fin_cases i <;> simp [hv2]
  have hzv : (zNF F : Matrix (Fin 3) (Fin 3) F) *ᵥ v = ![v 1, v 0 + v 1, 0] := by
    rw [zNF_mulVec, hveq]; rfl
  set a := v 0 with ha
  set b := v 1 with hb
  have hzv' : (zNF F : Matrix (Fin 3) (Fin 3) F) *ᵥ v = ![b, a + b, 0] := by
    rw [hzv, ha, hb]
  set d := a ^ 2 + a * b + b ^ 2 with hd
  have hd0 : d ≠ 0 := by
    intro hzero
    have hab := sq_add_mul_add_sq_ne_zero hcard hodd (a := a) (b := b)
      (by rw [← hd]; exact hzero)
    apply hv0
    rw [hveq, hab.1, hab.2]
    simp
  have hcomb0 : d • (Pi.single 0 1 : Fin 3 → F) =
      (a + b) • v + b • ((zNF F : Matrix (Fin 3) (Fin 3) F) *ᵥ v) := by
    rw [hzv', hveq, hd]
    ext i
    fin_cases i <;> simp [Pi.single_apply] <;> ring_nf <;> simp [h2]
  have hcomb1 : d • (Pi.single 1 1 : Fin 3 → F) =
      b • v + a • ((zNF F : Matrix (Fin 3) (Fin 3) F) *ᵥ v) := by
    rw [hzv', hveq, hd]
    ext i
    fin_cases i <;> simp [Pi.single_apply] <;> ring_nf <;> simp [h2]
  have hvS : v ∈ Submodule.span F {v, (zNF F : Matrix (Fin 3) (Fin 3) F) *ᵥ v} :=
    Submodule.subset_span (Set.mem_insert _ _)
  have hzvS : (zNF F : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈
      Submodule.span F {v, (zNF F : Matrix (Fin 3) (Fin 3) F) *ᵥ v} :=
    Submodule.subset_span (Set.mem_insert_of_mem _ rfl)
  have he0 : (Pi.single 0 1 : Fin 3 → F) ∈
      Submodule.span F {v, (zNF F : Matrix (Fin 3) (Fin 3) F) *ᵥ v} := by
    have hmem := Submodule.smul_mem
      (Submodule.span F {v, (zNF F : Matrix (Fin 3) (Fin 3) F) *ᵥ v})
      d⁻¹ (Submodule.add_mem _ (Submodule.smul_mem _ (a + b) hvS) (Submodule.smul_mem _ b hzvS))
    rwa [← hcomb0, smul_smul, inv_mul_cancel₀ hd0, one_smul] at hmem
  have he1 : (Pi.single 1 1 : Fin 3 → F) ∈
      Submodule.span F {v, (zNF F : Matrix (Fin 3) (Fin 3) F) *ᵥ v} := by
    have hmem := Submodule.smul_mem
      (Submodule.span F {v, (zNF F : Matrix (Fin 3) (Fin 3) F) *ᵥ v})
      d⁻¹ (Submodule.add_mem _ (Submodule.smul_mem _ b hvS) (Submodule.smul_mem _ a hzvS))
    rwa [← hcomb1, smul_smul, inv_mul_cancel₀ hd0, one_smul] at hmem
  apply le_antisymm
  · intro w hw
    have hw2 : w 2 = 0 := (CFSG.AGLEmbedding.LinearThreeKit.mem_flagSpace_two_iff).mp hw
    have hweq : w = w 0 • (Pi.single 0 1 : Fin 3 → F) +
        w 1 • (Pi.single 1 1 : Fin 3 → F) := by
      ext i; fin_cases i <;> simp [Pi.single_apply, hw2]
    rw [hweq]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ he0) (Submodule.smul_mem _ _ he1)
  · refine Submodule.span_le.mpr ?_
    intro x hx
    rcases hx with rfl | rfl
    · exact hv
    · exact zNF_mulVec_mem_plane hv

private theorem mem_lineE2_iff [CharP F 2] {v : Fin 3 → F} :
    v ∈ lineE2 ↔ v 0 = 0 ∧ v 1 = 0 := by
  constructor
  · intro hv
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hv
    subst hc
    simp [Pi.smul_apply, Pi.single_apply]
  · rintro ⟨h0, h1⟩
    have hv : v = v 2 • (Pi.single 2 1 : Fin 3 → F) := by
      ext i; fin_cases i <;> simp [Pi.single_apply, h0, h1]
    rw [hv]
    exact Submodule.smul_mem lineE2 _ (Submodule.mem_span_singleton_self _)

private theorem zInvariant_eq_line_or_plane [Finite F] [CharP F 2] {f : ℕ}
    (hcard : Nat.card F = 2 ^ f) (hodd : Odd f)
    {W : Submodule F (Fin 3 → F)}
    (hzW : ∀ v ∈ W, (zNF F : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ W)
    (hW0 : W ≠ ⊥) (hWtop : W ≠ ⊤) :
    W = lineE2 ∨ W = planeE01 := by
  have hproj : ∀ v ∈ W, v 2 = 0 ∨ (Pi.single 2 1 : Fin 3 → F) ∈ W := by
    intro v hv
    have hzv : (zNF F : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ W := hzW v hv
    have hz2v : (zNF F : Matrix (Fin 3) (Fin 3) F) *ᵥ
        ((zNF F : Matrix (Fin 3) (Fin 3) F) *ᵥ v) ∈ W := hzW _ hzv
    set zM : Matrix (Fin 3) (Fin 3) F := (zNF F : Matrix (Fin 3) (Fin 3) F) with hzM
    have hzv' : zM *ᵥ v ∈ W := hzv
    have hz2v' : zM *ᵥ (zM *ᵥ v) ∈ W := hz2v
    have hmem : ((1 : Matrix (Fin 3) (Fin 3) F) + zM + zM * zM) *ᵥ v ∈ W := by
      rw [Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec]
      exact W.add_mem (W.add_mem hv hzv') hz2v'
    rw [show ((1 : Matrix (Fin 3) (Fin 3) F) + (zNF F : Matrix (Fin 3) (Fin 3) F) +
        (zNF F : Matrix (Fin 3) (Fin 3) F) * (zNF F : Matrix (Fin 3) (Fin 3) F)) =
        (1 : Matrix (Fin 3) (Fin 3) F) + zM + zM * zM from by rw [hzM]] at hmem
    rw [zNF_add_sq_mulVec] at hmem
    by_cases hv2 : v 2 = 0
    · exact Or.inl hv2
    · refine Or.inr ?_
      have h' : (v 2)⁻¹ • ((v 2) • (Pi.single 2 1 : Fin 3 → F)) ∈ W :=
        W.smul_mem _ hmem
      rwa [smul_smul, inv_mul_cancel₀ hv2, one_smul] at h'
  by_cases hline : (Pi.single 2 1 : Fin 3 → F) ∈ W
  · left
    have hline_le : lineE2 ≤ W := by
      rw [Submodule.span_singleton_le_iff_mem]
      exact hline
    by_contra hWne
    have hnotle : ¬ W ≤ lineE2 := fun hle => hWne (le_antisymm hle hline_le)
    obtain ⟨v, hvW, hvline⟩ := Set.not_subset.mp hnotle
    set p : Fin 3 → F := v - v 2 • (Pi.single 2 1 : Fin 3 → F) with hp
    have hpW : p ∈ W := by
      rw [hp]
      exact W.sub_mem hvW (W.smul_mem _ hline)
    have hp_plane : p ∈ planeE01 := by
      rw [CFSG.AGLEmbedding.LinearThreeKit.mem_flagSpace_two_iff]
      simp [hp]
    have hp0 : p ≠ 0 := by
      intro hp0
      apply hvline
      have hv_eq : v = p + v 2 • (Pi.single 2 1 : Fin 3 → F) := by
        rw [hp]; abel
      rw [hv_eq, hp0, zero_add]
      exact Submodule.smul_mem lineE2 _ (Submodule.mem_span_singleton_self _)
    have hzpW : (zNF F : Matrix (Fin 3) (Fin 3) F) *ᵥ p ∈ W := hzW p hpW
    have hplane_le : planeE01 ≤ W := by
      rw [plane_eq_span_of_ne_zero hcard hodd hp_plane hp0]
      refine Submodule.span_le.mpr ?_
      intro x hx
      rcases hx with rfl | rfl
      · exact hpW
      · exact hzpW
    have htop_le : (⊤ : Submodule F (Fin 3 → F)) ≤ W := by
      intro x _
      have hx1 : x - x 2 • (Pi.single 2 1 : Fin 3 → F) ∈ planeE01 := by
        rw [CFSG.AGLEmbedding.LinearThreeKit.mem_flagSpace_two_iff]
        simp
      have hx2 : x 2 • (Pi.single 2 1 : Fin 3 → F) ∈ lineE2 :=
        Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
      have hx : x = (x - x 2 • (Pi.single 2 1 : Fin 3 → F)) +
          x 2 • (Pi.single 2 1 : Fin 3 → F) := by abel
      rw [hx]
      exact W.add_mem (hplane_le hx1) (hline_le hx2)
    exact hWtop (le_antisymm le_top htop_le)
  · right
    have hle : W ≤ planeE01 := by
      intro v hv
      rcases hproj v hv with hv2 | he2
      · rwa [CFSG.AGLEmbedding.LinearThreeKit.mem_flagSpace_two_iff]
      · exact absurd he2 hline
    obtain ⟨p, hpW, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
    have hp_plane : p ∈ planeE01 := hle hpW
    have hzpW : (zNF F : Matrix (Fin 3) (Fin 3) F) *ᵥ p ∈ W := hzW p hpW
    have hplane_le : planeE01 ≤ W := by
      rw [plane_eq_span_of_ne_zero hcard hodd hp_plane hp0]
      refine Submodule.span_le.mpr ?_
      intro x hx
      rcases hx with rfl | rfl
      · exact hpW
      · exact hzpW
    exact le_antisymm hle hplane_le

private theorem conj_fixed_mulVec (g q : SL(3, F)) {v : Fin 3 → F}
    (h : (((g⁻¹ * q * g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F)) *ᵥ v = v) :
    (q : Matrix (Fin 3) (Fin 3) F) *ᵥ ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ v) =
      (g : Matrix (Fin 3) (Fin 3) F) *ᵥ v := by
  calc (q : Matrix (Fin 3) (Fin 3) F) *ᵥ ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ v)
      = ((q * g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ v := by
        rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec]
    _ = ((g * (g⁻¹ * q * g) : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ v := by
        congr 1
        group
    _ = (g : Matrix (Fin 3) (Fin 3) F) *ᵥ
          (((g⁻¹ * q * g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) := by
        rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec]
    _ = (g : Matrix (Fin 3) (Fin 3) F) *ᵥ v := by rw [h]

private theorem normalizer_le_stabilizer_fixedSubspace (Q : Subgroup SL(3, F)) :
    Subgroup.normalizer (Q : Set SL(3, F)) ≤
      stabilizer (CFSG.AGLEmbedding.LinearThreeKit.fixedSubspace Q) := by
  intro g hg
  refine mem_stabilizer_of_map_le ?_
  rintro _ ⟨v, hv, rfl⟩
  change (g : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈
    CFSG.AGLEmbedding.LinearThreeKit.fixedSubspace Q
  rw [CFSG.AGLEmbedding.LinearThreeKit.mem_fixedSubspace]
  intro q hq
  have hq' : g⁻¹ * q * g ∈ Q := by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) q).mp hq
    simpa using this
  exact conj_fixed_mulVec g q ((CFSG.AGLEmbedding.LinearThreeKit.mem_fixedSubspace.mp hv)
    (g⁻¹ * q * g) hq')

private theorem fixedSubspace_ne_top (Q : Subgroup SL(3, F)) (hQ : Q ≠ ⊥) :
    CFSG.AGLEmbedding.LinearThreeKit.fixedSubspace Q ≠ ⊤ := by
  intro htop
  apply hQ
  rw [Subgroup.eq_bot_iff_forall]
  intro q hq
  apply Subtype.ext
  ext i j
  have hfix : ∀ v : Fin 3 → F, (q : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v := by
    intro v
    have hv : v ∈ CFSG.AGLEmbedding.LinearThreeKit.fixedSubspace Q :=
      htop ▸ Submodule.mem_top
    exact (CFSG.AGLEmbedding.LinearThreeKit.mem_fixedSubspace.mp hv) q hq
  have := congrFun (hfix (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one, Matrix.one_apply, Pi.single_apply] using this

private def upperBlock (g : SL(3, F)) : Matrix (Fin 2) (Fin 2) F :=
  !![(g : Matrix (Fin 3) (Fin 3) F) 0 0, (g : Matrix (Fin 3) (Fin 3) F) 0 1;
     (g : Matrix (Fin 3) (Fin 3) F) 1 0, (g : Matrix (Fin 3) (Fin 3) F) 1 1]

private theorem upperBlock_one : upperBlock (1 : SL(3, F)) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upperBlock, Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply]

private theorem upperBlock_mul_of_right_zero {g h : SL(3, F)}
    (hg : (g : Matrix (Fin 3) (Fin 3) F) 0 2 = 0)
    (hg' : (g : Matrix (Fin 3) (Fin 3) F) 1 2 = 0) :
    upperBlock (g * h) = upperBlock g * upperBlock h := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upperBlock, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three,
      hg, hg']

private theorem upperBlock_mul_of_left_zero {g h : SL(3, F)}
    (hh : (h : Matrix (Fin 3) (Fin 3) F) 2 0 = 0)
    (hh' : (h : Matrix (Fin 3) (Fin 3) F) 2 1 = 0) :
    upperBlock (g * h) = upperBlock g * upperBlock h := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upperBlock, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three,
      hh, hh']

private theorem entries_of_mem_stabilizer_line [CharP F 2] {k : SL(3, F)}
    (hk : k ∈ stabilizer lineE2) :
    (k : Matrix (Fin 3) (Fin 3) F) 0 2 = 0 ∧
      (k : Matrix (Fin 3) (Fin 3) F) 1 2 = 0 := by
  have hmem : (k : Matrix (Fin 3) (Fin 3) F) *ᵥ (Pi.single 2 1 : Fin 3 → F) ∈ lineE2 := by
    rw [mem_stabilizer] at hk
    rw [← hk]
    exact Submodule.mem_map_of_mem (Submodule.mem_span_singleton_self _)
  rw [mem_lineE2_iff] at hmem
  simpa [Matrix.mulVec_single_one] using hmem

private theorem entries_of_mem_stabilizer_plane {k : SL(3, F)}
    (hk : k ∈ stabilizer planeE01) :
    (k : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 ∧
      (k : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 := by
  have he0 : (Pi.single 0 1 : Fin 3 → F) ∈ planeE01 := by
    rw [CFSG.AGLEmbedding.LinearThreeKit.mem_flagSpace_two_iff]; simp
  have he1 : (Pi.single 1 1 : Fin 3 → F) ∈ planeE01 := by
    rw [CFSG.AGLEmbedding.LinearThreeKit.mem_flagSpace_two_iff]; simp
  have h0 : (k : Matrix (Fin 3) (Fin 3) F) *ᵥ (Pi.single 0 1 : Fin 3 → F) ∈ planeE01 := by
    rw [mem_stabilizer] at hk
    rw [← hk]
    exact Submodule.mem_map_of_mem he0
  have h1 : (k : Matrix (Fin 3) (Fin 3) F) *ᵥ (Pi.single 1 1 : Fin 3 → F) ∈ planeE01 := by
    rw [mem_stabilizer] at hk
    rw [← hk]
    exact Submodule.mem_map_of_mem he1
  rw [CFSG.AGLEmbedding.LinearThreeKit.mem_flagSpace_two_iff] at h0 h1
  constructor
  · simpa [Matrix.mulVec_single_one] using h0
  · simpa [Matrix.mulVec_single_one] using h1

private theorem upperBlock_diag22_mul_of_right_zero {g h : SL(3, F)}
    (h0 : (h : Matrix (Fin 3) (Fin 3) F) 0 2 = 0)
    (h1 : (h : Matrix (Fin 3) (Fin 3) F) 1 2 = 0) :
    (((g * h : SL(3, F)) : Matrix (Fin 3) (Fin 3) F)) 2 2 =
      ((g : Matrix (Fin 3) (Fin 3) F) 2 2) * ((h : Matrix (Fin 3) (Fin 3) F) 2 2) := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three]
  simp [h0, h1]

private theorem upperBlock_diag22_mul_of_left_zero {g h : SL(3, F)}
    (h0 : (g : Matrix (Fin 3) (Fin 3) F) 2 0 = 0)
    (h1 : (g : Matrix (Fin 3) (Fin 3) F) 2 1 = 0) :
    (((g * h : SL(3, F)) : Matrix (Fin 3) (Fin 3) F)) 2 2 =
      ((g : Matrix (Fin 3) (Fin 3) F) 2 2) * ((h : Matrix (Fin 3) (Fin 3) F) 2 2) := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three]
  simp [h0, h1]

private noncomputable def upperBlockHom (K : Subgroup SL(3, F))
    (hmul : ∀ g h : K, upperBlock (F := F) (((g : K) : SL(3, F)) * ((h : K) : SL(3, F))) =
      upperBlock (F := F) (g : SL(3, F)) * upperBlock (F := F) (h : SL(3, F)))
    (hdet : ∀ g : K, (upperBlock (F := F) (g : SL(3, F))).det = 1) : K →* SL(2, F) where
  toFun g := ⟨upperBlock (F := F) (g : SL(3, F)), hdet g⟩
  map_one' := by
    apply Subtype.ext
    change upperBlock (F := F) ((1 : K) : SL(3, F)) = 1
    simpa using upperBlock_one (F := F)
  map_mul' g h := by
    apply Subtype.ext
    change upperBlock (F := F) (((g : K) : SL(3, F)) * ((h : K) : SL(3, F))) =
      upperBlock (F := F) (g : SL(3, F)) * upperBlock (F := F) (h : SL(3, F))
    exact hmul g h

private theorem det_eq_upperBlock_mul_of_right_zero {g : SL(3, F)}
    (h0 : (g : Matrix (Fin 3) (Fin 3) F) 0 2 = 0)
    (h1 : (g : Matrix (Fin 3) (Fin 3) F) 1 2 = 0) :
    (g : Matrix (Fin 3) (Fin 3) F).det =
      (upperBlock g).det * (g : Matrix (Fin 3) (Fin 3) F) 2 2 := by
  rw [Matrix.det_fin_three, upperBlock, Matrix.det_fin_two]
  simp [h0, h1]
  ring

private theorem det_eq_upperBlock_mul_of_left_zero {g : SL(3, F)}
    (h0 : (g : Matrix (Fin 3) (Fin 3) F) 2 0 = 0)
    (h1 : (g : Matrix (Fin 3) (Fin 3) F) 2 1 = 0) :
    (g : Matrix (Fin 3) (Fin 3) F).det =
      (upperBlock g).det * (g : Matrix (Fin 3) (Fin 3) F) 2 2 := by
  rw [Matrix.det_fin_three, upperBlock, Matrix.det_fin_two]
  simp [h0, h1]
  ring

private noncomputable def diagChar (K : Subgroup SL(3, F))
    (hmul22 : ∀ g h : K,
      (((((g : K) : SL(3, F)) * ((h : K) : SL(3, F))) : SL(3, F)) :
        Matrix (Fin 3) (Fin 3) F) 2 2 =
      ((g : Matrix (Fin 3) (Fin 3) F) 2 2) * ((h : Matrix (Fin 3) (Fin 3) F) 2 2))
    (hne : ∀ g : K, (g : Matrix (Fin 3) (Fin 3) F) 2 2 ≠ 0) : K →* Fˣ where
  toFun g := Units.mk0 ((g : Matrix (Fin 3) (Fin 3) F) 2 2) (hne g)
  map_one' := by
    apply Units.ext
    simp [Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply]
  map_mul' g h := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mk0, Units.val_mk0, Units.val_mk0]
    exact hmul22 g h

private theorem commutator_eq_top_of_subgroup {K : Subgroup SL(3, F)} (h : ⁅K, K⁆ = K) :
    commutator K = ⊤ := by
  apply Subgroup.map_injective K.subtype_injective
  rw [commutator_def, Subgroup.map_commutator]
  simp only [Subgroup.map_top, Subgroup.range_subtype]
  exact h

private theorem diagChar_eq_one (K : Subgroup SL(3, F))
    (hmul22 : ∀ g h : K,
      (((((g : K) : SL(3, F)) * ((h : K) : SL(3, F))) : SL(3, F)) :
        Matrix (Fin 3) (Fin 3) F) 2 2 =
      ((g : Matrix (Fin 3) (Fin 3) F) 2 2) * ((h : Matrix (Fin 3) (Fin 3) F) 2 2))
    (hne : ∀ g : K, (g : Matrix (Fin 3) (Fin 3) F) 2 2 ≠ 0)
    (hKK : ⁅K, K⁆ = K) (g : K) : diagChar K hmul22 hne g = 1 := by
  have hle : commutator K ≤ (diagChar K hmul22 hne).ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a ha b hb
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_commute.mpr (Commute.all _ _)
  have hKker : (⊤ : Subgroup K) ≤ (diagChar K hmul22 hne).ker := by
    rw [← commutator_eq_top_of_subgroup hKK]
    exact hle
  exact MonoidHom.mem_ker.mp (hKker (Subgroup.mem_top g))

private theorem block_det_one (K : Subgroup SL(3, F))
    (hmul22 : ∀ g h : K,
      (((((g : K) : SL(3, F)) * ((h : K) : SL(3, F))) : SL(3, F)) :
        Matrix (Fin 3) (Fin 3) F) 2 2 =
      ((g : Matrix (Fin 3) (Fin 3) F) 2 2) * ((h : Matrix (Fin 3) (Fin 3) F) 2 2))
    (hdetmul : ∀ g : K,
      (((g : K) : SL(3, F)) : Matrix (Fin 3) (Fin 3) F).det =
        (upperBlock (F := F) ((g : K) : SL(3, F))).det *
          (((g : K) : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) 2 2)
    (hKK : ⁅K, K⁆ = K) (g : K) :
    (upperBlock (F := F) ((g : K) : SL(3, F))).det = 1 := by
  have hne : ∀ g : K, (g : Matrix (Fin 3) (Fin 3) F) 2 2 ≠ 0 := by
    intro g h0
    have h := hdetmul g
    rw [(g : SL(3, F)).2, h0, mul_zero] at h
    exact one_ne_zero h
  have h22 : ((g : K) : Matrix (Fin 3) (Fin 3) F) 2 2 = 1 := by
    have := congrArg Units.val (diagChar_eq_one K hmul22 hne hKK g)
    simpa [diagChar] using this
  have h := hdetmul g
  rw [(g : SL(3, F)).2, h22, mul_one] at h
  exact h.symm

private noncomputable def diagMat (b : Fˣ) : Matrix (Fin 3) (Fin 3) F :=
  Matrix.diagonal ![ (b : F), (b : F), ((b⁻¹ * b⁻¹ : Fˣ) : F) ]

private theorem diagMat_det (b : Fˣ) : (diagMat b).det = 1 := by
  rw [diagMat, Matrix.det_diagonal, Fin.prod_univ_three]
  change ((b * b * (b⁻¹ * b⁻¹) : Fˣ) : F) = 1
  rw [show (b * b * (b⁻¹ * b⁻¹) : Fˣ) = 1 by group, Units.val_one]

private noncomputable def diagHom : Fˣ →* SL(3, F) where
  toFun b := ⟨diagMat b, diagMat_det b⟩
  map_one' := by
    apply Subtype.ext
    change diagMat 1 = 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [diagMat, Matrix.diagonal_apply, Matrix.one_apply]
  map_mul' b c := by
    apply Subtype.ext
    change diagMat (b * c) = diagMat b * diagMat c
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [diagMat, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply,
        Units.val_mul, _root_.mul_inv_rev, mul_comm, mul_left_comm, mul_assoc]

private theorem diagHom_apply (b : Fˣ) :
    (diagHom b : Matrix (Fin 3) (Fin 3) F) = diagMat b := rfl

private theorem diagHom_injective : Function.Injective (diagHom (F := F)) := by
  intro b c h
  have h00 : (b : F) = (c : F) := by
    have := congrFun (congrFun (congrArg (fun g : SL(3, F) =>
      (g : Matrix (Fin 3) (Fin 3) F)) h) 0) 0
    simpa [diagHom_apply, diagMat, Matrix.diagonal_apply] using this
  exact Units.ext h00

private theorem orderOf_diagHom (b : Fˣ) : orderOf (diagHom b) = orderOf b :=
  orderOf_injective (diagHom (F := F)) diagHom_injective b

private theorem diagHom_mulVec (b : Fˣ) (v : Fin 3 → F) :
    (diagHom b : Matrix (Fin 3) (Fin 3) F) *ᵥ v =
      ![ (b : F) * v 0, (b : F) * v 1, ((b⁻¹ * b⁻¹ : Fˣ) : F) * v 2 ] := by
  rw [diagHom_apply, diagMat]
  funext i
  rw [Matrix.mulVec_diagonal]
  fin_cases i <;> rfl

private theorem diagHom_commute_zNF (b : Fˣ) :
    diagHom b * zNF F = zNF F * diagHom b := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagHom_apply, diagMat, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_three, zNF, Matrix.diagonal_apply]

private theorem diagHom_mem_normalizer (b : Fˣ) :
    diagHom b ∈ Subgroup.normalizer (Subgroup.zpowers (zNF F) : Set SL(3, F)) := by
  have hconj : (MulAut.conj (diagHom b)) (zNF F) = zNF F := by
    rw [MulAut.conj_apply]
    calc diagHom b * zNF F * (diagHom b)⁻¹ =
        zNF F * diagHom b * (diagHom b)⁻¹ := by rw [diagHom_commute_zNF]
      _ = zNF F := by group
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  simpa [MonoidHom.map_zpowers] using congrArg Subgroup.zpowers hconj

private theorem upperBlock_zNF : upperBlock (zNF F) = !![0, -1; 1, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem upperBlock_zNF_ne_one : upperBlock (zNF F) ≠ 1 := by
  intro h
  have h00 : upperBlock (zNF F) 0 0 = (1 : Matrix (Fin 2) (Fin 2) F) 0 0 := by rw [h]
  rw [upperBlock_zNF] at h00
  norm_num at h00

private theorem diagHom_line_action [CharP F 2] (b : Fˣ) {w : Fin 3 → F} (hw : w ∈ lineE2) :
    (diagHom b : Matrix (Fin 3) (Fin 3) F) *ᵥ w =
      ((b⁻¹ * b⁻¹ : Fˣ) : F) • w := by
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
  rw [diagHom_mulVec]
  ext i
  fin_cases i <;> simp [Pi.smul_apply]

private theorem diagHom_line_quotient [CharP F 2] (b : Fˣ) (v : Fin 3 → F) :
    (diagHom b : Matrix (Fin 3) (Fin 3) F) *ᵥ v - (b : F) • v ∈ lineE2 := by
  rw [mem_lineE2_iff]
  rw [diagHom_mulVec]
  constructor <;> simp [Pi.sub_apply]

private theorem diagHom_plane_action [CharP F 2] (b : Fˣ) {w : Fin 3 → F} (hw : w ∈ planeE01) :
    (diagHom b : Matrix (Fin 3) (Fin 3) F) *ᵥ w = (b : F) • w := by
  have hw2 : w 2 = 0 := (CFSG.AGLEmbedding.LinearThreeKit.mem_flagSpace_two_iff).mp hw
  rw [diagHom_mulVec]
  ext i
  fin_cases i <;> simp [Pi.smul_apply, hw2]

private theorem diagHom_plane_quotient [CharP F 2] (b : Fˣ) (v : Fin 3 → F) :
    (diagHom b : Matrix (Fin 3) (Fin 3) F) *ᵥ v -
      ((b⁻¹ * b⁻¹ : Fˣ) : F) • v ∈ planeE01 := by
  rw [CFSG.AGLEmbedding.LinearThreeKit.mem_flagSpace_two_iff]
  rw [diagHom_mulVec]
  simp

private theorem coe_four_mulVec (a b c d : SL(3, F)) (v : Fin 3 → F) :
    (((a * b * c * d : SL(3, F)) : Matrix (Fin 3) (Fin 3) F)) *ᵥ v =
      (a : Matrix (Fin 3) (Fin 3) F) *ᵥ
        ((b : Matrix (Fin 3) (Fin 3) F) *ᵥ
          ((c : Matrix (Fin 3) (Fin 3) F) *ᵥ
            ((d : Matrix (Fin 3) (Fin 3) F) *ᵥ v))) := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec]

private theorem SL_mul_adjugate (g : SL(3, F)) :
    (g : Matrix (Fin 3) (Fin 3) F) * (g : Matrix (Fin 3) (Fin 3) F).adjugate = 1 := by
  rw [Matrix.mul_adjugate, g.2, one_smul]

private theorem adjugate_mul_SL (g : SL(3, F)) :
    (g : Matrix (Fin 3) (Fin 3) F).adjugate * (g : Matrix (Fin 3) (Fin 3) F) = 1 := by
  rw [Matrix.adjugate_mul, g.2, one_smul]

private theorem SL_mulVec_adjugate (g : SL(3, F)) (v : Fin 3 → F) :
    (g : Matrix (Fin 3) (Fin 3) F) *ᵥ
      ((g : Matrix (Fin 3) (Fin 3) F).adjugate *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, SL_mul_adjugate, Matrix.one_mulVec]

private theorem SL_adjugate_mulVec (g : SL(3, F)) (v : Fin 3 → F) :
    (g : Matrix (Fin 3) (Fin 3) F).adjugate *ᵥ
      ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, adjugate_mul_SL, Matrix.one_mulVec]

private theorem commutator_mem_elationGenerators (W : Submodule F (Fin 3 → F)) (g k : SL(3, F))
    (α β : F) (hα : α ≠ 0)
    (hgW : ∀ w ∈ W, (g : Matrix (Fin 3) (Fin 3) F) *ᵥ w = α • w)
    (hgQ : ∀ v, (g : Matrix (Fin 3) (Fin 3) F) *ᵥ v - β • v ∈ W)
    (hkW : ∀ w ∈ W, (k : Matrix (Fin 3) (Fin 3) F) *ᵥ w ∈ W)
    (hkWinv : ∀ w ∈ W,
      ((k⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ w ∈ W) :
    g * k * g⁻¹ * k⁻¹ ∈ elationGenerators W := by
  rw [CFSG.AGLEmbedding.LinearThreeKit.mem_elationGenerators_iff]
  have hkc : ((k⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      (k : Matrix (Fin 3) (Fin 3) F).adjugate := Matrix.SpecialLinearGroup.coe_inv k
  have hgc : ((g⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      (g : Matrix (Fin 3) (Fin 3) F).adjugate := Matrix.SpecialLinearGroup.coe_inv g
  have hkWinv' : ∀ w ∈ W,
      (k : Matrix (Fin 3) (Fin 3) F).adjugate *ᵥ w ∈ W := by
    intro w hw
    simpa [hkc] using hkWinv w hw
  have hkki : ∀ w : Fin 3 → F,
      (k : Matrix (Fin 3) (Fin 3) F) *ᵥ
        ((k : Matrix (Fin 3) (Fin 3) F).adjugate *ᵥ w) = w := by
    intro w
    exact SL_mulVec_adjugate k w
  have hgInvW : ∀ w ∈ W,
      (g : Matrix (Fin 3) (Fin 3) F).adjugate *ᵥ w = α⁻¹ • w := by
    intro w hw
    have h1 : (g : Matrix (Fin 3) (Fin 3) F).adjugate *ᵥ
        ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ w) = w := SL_adjugate_mulVec g w
    rw [hgW w hw, Matrix.mulVec_smul] at h1
    calc (g : Matrix (Fin 3) (Fin 3) F).adjugate *ᵥ w
        = α⁻¹ • (α • ((g : Matrix (Fin 3) (Fin 3) F).adjugate *ᵥ w)) := by
          rw [smul_smul, inv_mul_cancel₀ hα, one_smul]
      _ = α⁻¹ • w := by rw [h1]
  constructor
  · intro v
    set x : Fin 3 → F := (g : Matrix (Fin 3) (Fin 3) F).adjugate *ᵥ
      (((k : Matrix (Fin 3) (Fin 3) F).adjugate) *ᵥ v) with hx
    set y : Fin 3 → F := (k : Matrix (Fin 3) (Fin 3) F) *ᵥ x with hydef
    have hgx : (g : Matrix (Fin 3) (Fin 3) F) *ᵥ x =
        (k : Matrix (Fin 3) (Fin 3) F).adjugate *ᵥ v := by
      rw [hx]
      exact SL_mulVec_adjugate g _
    have hx1 : (k : Matrix (Fin 3) (Fin 3) F).adjugate *ᵥ v - β • x ∈ W := by
      have := hgQ x
      rwa [hgx] at this
    have hstep1 : v - β • y ∈ W := by
      have hk := hkW _ hx1
      have hcalc : (k : Matrix (Fin 3) (Fin 3) F) *ᵥ
          ((k : Matrix (Fin 3) (Fin 3) F).adjugate *ᵥ v - β • x) =
          v - β • y := by
        rw [Matrix.mulVec_sub, hkki, Matrix.mulVec_smul, hydef]
      simpa [hcalc] using hk
    have hy : β • y - v ∈ W := by
      simpa [neg_sub] using W.neg_mem hstep1
    have hgQy : (g : Matrix (Fin 3) (Fin 3) F) *ᵥ y - β • y ∈ W := hgQ y
    have hsum : (g : Matrix (Fin 3) (Fin 3) F) *ᵥ y - v ∈ W := by
      have := W.add_mem hgQy hy
      convert this using 1 <;> abel
    have hcoe : ((g * k * g⁻¹ * k⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ v =
        (g : Matrix (Fin 3) (Fin 3) F) *ᵥ
          ((k : Matrix (Fin 3) (Fin 3) F) *ᵥ
            ((g : Matrix (Fin 3) (Fin 3) F).adjugate *ᵥ
              ((k : Matrix (Fin 3) (Fin 3) F).adjugate *ᵥ v))) := by
      rw [coe_four_mulVec, hgc, hkc]
    rw [hcoe]
    exact hsum
  · intro w hw
    have hcoe : ((g * k * g⁻¹ * k⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ w =
        (g : Matrix (Fin 3) (Fin 3) F) *ᵥ
          ((k : Matrix (Fin 3) (Fin 3) F) *ᵥ
            ((g : Matrix (Fin 3) (Fin 3) F).adjugate *ᵥ
              ((k : Matrix (Fin 3) (Fin 3) F).adjugate *ᵥ w))) := by
      rw [coe_four_mulVec, hgc, hkc]
    rw [hcoe]
    rw [hgInvW _ (hkWinv' w hw), Matrix.mulVec_smul, hkki, Matrix.mulVec_smul,
      hgW w hw, smul_smul, inv_mul_cancel₀ hα, one_smul]

private theorem mulVec_mem_of_mem_stabilizer {W : Submodule F (Fin 3 → F)} {g : SL(3, F)}
    (hg : g ∈ stabilizer W) {v : Fin 3 → F} (hv : v ∈ W) :
    (g : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ W := by
  rw [mem_stabilizer] at hg
  rw [← hg]
  exact Submodule.mem_map_of_mem hv

private theorem commutator_mem_pCoreOf [CharP F 2] (K Y : Subgroup SL(3, F))
    (W : Submodule F (Fin 3 → F)) (b : Fˣ) (α β : F) (hα : α ≠ 0)
    (hzy : Subgroup.normalizer (Subgroup.zpowers (zNF F) : Set SL(3, F)) ≤ Y)
    (hyK : Y ≤ Subgroup.normalizer (K : Set SL(3, F)))
    (hKstab : K ≤ stabilizer W)
    (hgW : ∀ w ∈ W, (diagHom b : Matrix (Fin 3) (Fin 3) F) *ᵥ w = α • w)
    (hgQ : ∀ v : Fin 3 → F,
      (diagHom b : Matrix (Fin 3) (Fin 3) F) *ᵥ v - β • v ∈ W)
    {k : SL(3, F)} (hk : k ∈ K) :
    diagHom b * k * (diagHom b)⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 K := by
  have hgY : diagHom b ∈ Y := hzy (diagHom_mem_normalizer b)
  have hgN : diagHom b ∈ Subgroup.normalizer (K : Set SL(3, F)) := hyK hgY
  have hcommK : diagHom b * k * (diagHom b)⁻¹ * k⁻¹ ∈ K := by
    have hk' : diagHom b * k * (diagHom b)⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp hgN k).mp hk
    exact Subgroup.mul_mem K hk' (Subgroup.inv_mem K hk)
  have hkW : ∀ w ∈ W, (k : Matrix (Fin 3) (Fin 3) F) *ᵥ w ∈ W :=
    fun w hw => mulVec_mem_of_mem_stabilizer (hKstab hk) hw
  have hkWinv : ∀ w ∈ W,
      ((k⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ w ∈ W :=
    fun w hw => mulVec_mem_of_mem_stabilizer (hKstab (Subgroup.inv_mem K hk)) hw
  have hcommU : diagHom b * k * (diagHom b)⁻¹ * k⁻¹ ∈ elationSubgroup W :=
    mem_elationSubgroup_of_mem
      (commutator_mem_elationGenerators W (diagHom b) k α β hα hgW hgQ hkW hkWinv)
  have hinf : diagHom b * k * (diagHom b)⁻¹ * k⁻¹ ∈ K ⊓ elationSubgroup W :=
    ⟨hcommK, hcommU⟩
  have htwo : IsPGroup 2 ↥(K ⊓ elationSubgroup W) :=
    (CFSG.AGLEmbedding.LinearThreeKit.isPGroup_elationSubgroup 2 W).to_le inf_le_right
  have hnorm : K ≤ Subgroup.normalizer (K ⊓ elationSubgroup W : Set SL(3, F)) :=
    (le_inf Subgroup.le_normalizer
      (hKstab.trans
        (CFSG.AGLEmbedding.LinearThreeKit.stabilizer_le_normalizer_elationSubgroup W))).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hnorm htwo hinf

private theorem exists_prime_of_blockHom (hD : L3OvDickson) [Finite F] {f : ℕ}
    (hcard : Nat.card F = 2 ^ f) (hodd : Odd f)
    (K : Subgroup SL(3, F)) (β : K →* SL(2, F))
    (hKK : ⁅K, K⁆ = K) (hzK : zNF F ∈ K)
    (hβz : β ⟨zNF F, hzK⟩ ≠ 1) :
    ∃ r : ℕ, r.Prime ∧ 5 ≤ r ∧ r ∣ 2 ^ f - 1 ∧ r ∣ Nat.card K := by
  have hKperf : Group.IsPerfect K := by
    rw [Group.isPerfect_def]
    exact commutator_eq_top_of_subgroup hKK
  let H : Subgroup SL(2, F) := β.range
  have hHmap : H = Subgroup.map β ⊤ := by
    change β.range = Subgroup.map β ⊤
    exact MonoidHom.range_eq_map β
  have hHcomm : ⁅H, H⁆ = H := by
    have hperf : Group.IsPerfect H := by
      rw [hHmap]
      exact Group.IsPerfect.map β
    exact Subgroup.commutator_eq_self
  have hHne : H ≠ ⊥ := by
    intro hbot
    apply hβz
    have hmem : β ⟨zNF F, hzK⟩ ∈ H := β.mem_range.mpr ⟨⟨zNF F, hzK⟩, rfl⟩
    rw [hbot] at hmem
    exact Subgroup.mem_bot.mp hmem
  obtain ⟨r, hrprime, hr5, hrdvd, hrH⟩ := hD F f hcard hodd H hHcomm hHne
  refine ⟨r, hrprime, hr5, hrdvd, ?_⟩
  refine dvd_trans hrH ?_
  rw [hHmap]
  simpa using Subgroup.card_map_dvd (⊤ : Subgroup K) β

private theorem l3OvAlt_of_blockData (hD : L3OvDickson) [Finite F] [CharP F 2] {f : ℕ}
    (hcard : Nat.card F = 2 ^ f) (hodd : Odd f)
    (Y K : Subgroup SL(3, F)) (W : Submodule F (Fin 3 → F))
    (hzy : Subgroup.normalizer (Subgroup.zpowers (zNF F) : Set SL(3, F)) ≤ Y)
    (hyK : Y ≤ Subgroup.normalizer (K : Set SL(3, F)))
    (hKK : ⁅K, K⁆ = K) (hzK : zNF F ∈ K)
    (hKstab : K ≤ stabilizer W)
    (hmulBlock : ∀ g h : K,
      upperBlock (F := F) (((g : K) : SL(3, F)) * ((h : K) : SL(3, F))) =
        upperBlock (F := F) (g : SL(3, F)) * upperBlock (F := F) (h : SL(3, F)))
    (hmul22 : ∀ g h : K,
      (((((g : K) : SL(3, F)) * ((h : K) : SL(3, F))) : SL(3, F)) :
        Matrix (Fin 3) (Fin 3) F) 2 2 =
      ((g : Matrix (Fin 3) (Fin 3) F) 2 2) * ((h : Matrix (Fin 3) (Fin 3) F) 2 2))
    (hdetmul : ∀ g : K,
      (((g : K) : SL(3, F)) : Matrix (Fin 3) (Fin 3) F).det =
        (upperBlock (F := F) ((g : K) : SL(3, F))).det *
          (((g : K) : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) 2 2)
    (hβz : upperBlock (F := F) (zNF F) ≠ 1)
    (α β : Fˣ → F) (hα : ∀ b : Fˣ, α b ≠ 0)
    (hgW : ∀ (b : Fˣ) (w : Fin 3 → F), w ∈ W →
      (diagHom b : Matrix (Fin 3) (Fin 3) F) *ᵥ w = α b • w)
    (hgQ : ∀ (b : Fˣ) (v : Fin 3 → F),
      (diagHom b : Matrix (Fin 3) (Fin 3) F) *ᵥ v - β b • v ∈ W) :
    L3OvAlt Y K := by
  have hdet : ∀ g : K, (upperBlock (F := F) ((g : K) : SL(3, F))).det = 1 :=
    fun g => block_det_one K hmul22 hdetmul hKK g
  let βhom : K →* SL(2, F) := upperBlockHom K hmulBlock hdet
  have hβzK : βhom ⟨zNF F, hzK⟩ ≠ 1 := by
    intro h
    apply hβz
    exact congrArg Subtype.val h
  obtain ⟨r, hrprime, hr5, hrdvd, hrH⟩ :=
    exists_prime_of_blockHom hD hcard hodd K βhom hKK hzK hβzK
  have hrdvd' : r ∣ Nat.card Fˣ := by
    rw [Nat.card_units F, hcard]
    exact hrdvd
  haveI : Fact r.Prime := ⟨hrprime⟩
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' r hrdvd'
  have hgorder : orderOf (diagHom b) = r := by
    rw [orderOf_diagHom, hb]
  refine ⟨diagHom b, hzy (diagHom_mem_normalizer b), r, hrprime, hr5, hgorder, hrH, ?_⟩
  intro k hk
  exact commutator_mem_pCoreOf K Y W b (α b) (β b) (hα b) hzy hyK hKstab
    (hgW b) (hgQ b) hk

theorem l3OvMatrix_of_dickson (hD : L3OvDickson) : L3OvMatrix := by
  intro F _ _ _ f hcard hodd Y K hZY hYK hKK hzK hQ
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Q := CFSG.Open.pCoreOf 2 K
  let W := CFSG.AGLEmbedding.LinearThreeKit.fixedSubspace Q
  have hQp : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K
  have hWbot : W ≠ ⊥ :=
    CFSG.AGLEmbedding.LinearThreeKit.fixedSubspace_ne_bot 2 (by norm_num) hQp
  have hWtop : W ≠ ⊤ := fixedSubspace_ne_top Q hQ
  have hKnormQ : K ≤ Subgroup.normalizer (Q : Set SL(3, F)) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K
  have hKstab : K ≤ stabilizer W :=
    hKnormQ.trans (normalizer_le_stabilizer_fixedSubspace Q)
  have hzW : ∀ v ∈ W, (zNF F : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ W :=
    fun v hv => mulVec_mem_of_mem_stabilizer (hKstab hzK) hv
  have hclass := zInvariant_eq_line_or_plane hcard hodd hzW hWbot hWtop
  rcases hclass with hWline | hWplane
  · rw [hWline] at hKstab
    have hshape : ∀ k ∈ K, (k : Matrix (Fin 3) (Fin 3) F) 0 2 = 0 ∧
        (k : Matrix (Fin 3) (Fin 3) F) 1 2 = 0 :=
      fun k hk => entries_of_mem_stabilizer_line (hKstab hk)
    exact l3OvAlt_of_blockData hD hcard hodd Y K lineE2 hZY hYK hKK hzK hKstab
      (fun g h => upperBlock_mul_of_right_zero (hshape g g.2).1 (hshape g g.2).2)
      (fun g h => upperBlock_diag22_mul_of_right_zero (hshape h h.2).1 (hshape h h.2).2)
      (fun g => det_eq_upperBlock_mul_of_right_zero (hshape g g.2).1 (hshape g g.2).2)
      upperBlock_zNF_ne_one
      (fun b => ((b⁻¹ * b⁻¹ : Fˣ) : F)) (fun b => (b : F))
      (fun b => Units.ne_zero (b⁻¹ * b⁻¹))
      (fun b w hw => diagHom_line_action b hw)
      (fun b v => diagHom_line_quotient b v)
  · rw [hWplane] at hKstab
    have hshape : ∀ k ∈ K, (k : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 ∧
        (k : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 :=
      fun k hk => entries_of_mem_stabilizer_plane (hKstab hk)
    exact l3OvAlt_of_blockData hD hcard hodd Y K planeE01 hZY hYK hKK hzK hKstab
      (fun g h => upperBlock_mul_of_left_zero (hshape h h.2).1 (hshape h h.2).2)
      (fun g h => upperBlock_diag22_mul_of_left_zero (hshape g g.2).1 (hshape g g.2).2)
      (fun g => det_eq_upperBlock_mul_of_left_zero (hshape g g.2).1 (hshape g g.2).2)
      upperBlock_zNF_ne_one
      (fun b => (b : F)) (fun b => ((b⁻¹ * b⁻¹ : Fˣ) : F))
      (fun b => b.ne_zero)
      (fun b w hw => diagHom_plane_action b hw)
      (fun b v => diagHom_plane_quotient b v)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
