module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniShapeDefs
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeSplitR
import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniLiftThree
import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniLift
import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniRank
import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniCubeR
import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniNonCubeR
import CFSG.Assembly.GL83StatedBridge
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsCaseLSU
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeForm
import CFSG.LocalAnalysis.StandardType.GGSUNonsplitTwoBlockRestrict
import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUNormal
import CFSG.LinearAlgebra.LinearGroups.UnitaryFourOrder
import CFSG.LocalAnalysis.ComponentInitial.LinearUnitaryField
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUSlice

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly CFSG.AGLEmbedding CFSG.LocalAnalysis.ComponentInitial
open CFSG.LinearGroups CFSG.ClassicalGroups.UnitaryFlag

section UniShapeAux

open Matrix Module CFSG CFSG.Assembly CFSG.AGLEmbedding
open CFSG.LocalAnalysis.ComponentInitial CFSG.LinearGroups CFSG.ClassicalGroups.UnitaryFlag

private theorem uniShapeR_isHermIsometry_iff_stdHermForm {K : Type} [Field K] {f n : ℕ}
    (h : UnitaryFieldData 2 f K) {A : Matrix (Fin n) (Fin n) K} :
    IsHermIsometry (2 ^ f) A ↔
      ∀ x y, stdHermForm h n (A *ᵥ x) (A *ᵥ y) = stdHermForm h n x y := by
  simp only [IsHermIsometry, stdHermForm_apply, h.bar_apply]

private theorem uniShapeR_isHermIsometry_iff_mem_unitaryI {K : Type} [Field K] [Finite K] [CharP K 2]
    {f n : ℕ} (h : UnitaryFieldData 2 f K) {g : GL (Fin n) K} :
    IsHermIsometry (2 ^ f) (g : Matrix (Fin n) (Fin n) K) ↔
      g ∈ CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen.unitaryI h n := by
  rw [CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen.unitaryI]
  constructor
  · intro hg
    rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.mem_primeFormUnitary]
    have hmat := CFSG.StandardType.SUTB.map_bar_transpose_mul_of_isometry h
      ((uniShapeR_isHermIsometry_iff_stdHermForm h).mp hg)
    simpa using hmat
  · intro hg
    rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.mem_primeFormUnitary] at hg
    have hmat : ((g : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * (g : Matrix (Fin n) (Fin n) K) =
        1 := by
      simpa using hg
    exact (uniShapeR_isHermIsometry_iff_stdHermForm h).mpr
      (CFSG.ComponentClassification.Burgoyne.U.stdHermForm_mulVec h hmat)

private theorem uniShapeR_isometry_mem_normalizer {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ}
    (h : UnitaryFieldData 2 f K) {g : GL (Fin n) K}
    (hg : IsHermIsometry (2 ^ f) (g : Matrix (Fin n) (Fin n) K)) :
    g ∈ Subgroup.normalizer
      (LargeEvenSUGroup (Fin n) K (2 ^ f) : Set (GL (Fin n) K)) := by
  have hgn : g ∈ Subgroup.normalizer (Open.StatedSU n (2 ^ f) K : Set (GL (Fin n) K)) :=
    CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen.unitaryI_le_normalizer h
      ((uniShapeR_isHermIsometry_iff_mem_unitaryI h).mp hg)
  rwa [CFSG.Assembly.largeEvenSUGroup_eq_statedSU]

private theorem uniShapeR_normalizes_of_mem_normalizer {G : Type} [Group G] {H : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer H) : ∀ k ∈ H, g * k * g⁻¹ ∈ H :=
  fun k hk => (Subgroup.mem_normalizer_iff.mp hg k).mp hk

private theorem uniShapeR_isConjBy_mul {n q : ℕ} {K : Type} [Field K] {g g' : GL (Fin n) K}
    {a a' : MulAut (PSUg n K q)}
    (hnorm : ∀ k ∈ LargeEvenSUGroup (Fin n) K q, g' * k * g'⁻¹ ∈ LargeEvenSUGroup (Fin n) K q)
    (h1 : IsConjBy g a) (h2 : IsConjBy g' a') : IsConjBy (g * g') (a * a') := by
  intro x x' hx
  let x'' : ↥(LargeEvenSUGroup (Fin n) K q) :=
    ⟨g' * (x : GL (Fin n) K) * g'⁻¹, hnorm x x.2⟩
  have hx'' : (x'' : GL (Fin n) K) = g' * (x : GL (Fin n) K) * g'⁻¹ := rfl
  have h2' : a' (LargeEvenProjMk (LargeEvenSUGroup (Fin n) K q) x) =
      LargeEvenProjMk (LargeEvenSUGroup (Fin n) K q) x'' := h2 x x'' hx''
  have h1' : a (LargeEvenProjMk (LargeEvenSUGroup (Fin n) K q) x'') =
      LargeEvenProjMk (LargeEvenSUGroup (Fin n) K q) x' :=
    h1 x'' x' (by
      show (x' : GL (Fin n) K) = g * (x'' : GL (Fin n) K) * g⁻¹
      rw [hx, hx'']
      group)
  calc (a * a') (LargeEvenProjMk (LargeEvenSUGroup (Fin n) K q) x)
      = a (a' (LargeEvenProjMk (LargeEvenSUGroup (Fin n) K q) x)) := rfl
    _ = a (LargeEvenProjMk (LargeEvenSUGroup (Fin n) K q) x'') := by rw [h2']
    _ = LargeEvenProjMk (LargeEvenSUGroup (Fin n) K q) x' := h1'

private theorem uniShapeR_isConjBy_inv {n q : ℕ} {K : Type} [Field K] {g : GL (Fin n) K}
    {a : MulAut (PSUg n K q)} (h1 : IsConjBy g a) : IsConjBy g⁻¹ a⁻¹ := by
  intro x x' hx
  have hrel : (x : GL (Fin n) K) = g * (x' : GL (Fin n) K) * g⁻¹ := by rw [hx]; group
  have h := h1 x' x hrel
  calc a⁻¹ (LargeEvenProjMk (LargeEvenSUGroup (Fin n) K q) x)
      = a⁻¹ (a (LargeEvenProjMk (LargeEvenSUGroup (Fin n) K q) x')) := by rw [← h]
    _ = LargeEvenProjMk (LargeEvenSUGroup (Fin n) K q) x' := by
          rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]

private theorem uniShapeR_isConjBy_mul_central_iff {n q : ℕ} {K : Type} [Field K] {s : GL (Fin n) K}
    (hs : ∀ x : GL (Fin n) K, s * x = x * s) {A : GL (Fin n) K} {a : MulAut (PSUg n K q)} :
    IsConjBy (s * A) a ↔ IsConjBy A a := by
  have hrel_eq : ∀ x : GL (Fin n) K, (s * A) * x * (s * A)⁻¹ = A * x * A⁻¹ := by
    intro x
    rw [_root_.mul_inv_rev]
    calc (s * A) * x * (A⁻¹ * s⁻¹) = s * (A * x * A⁻¹) * s⁻¹ := by group
      _ = A * x * A⁻¹ := by rw [hs]; group
  constructor
  · intro h x x' hx
    exact h x x' (by
      show (x' : GL (Fin n) K) = (s * A) * (x : GL (Fin n) K) * (s * A)⁻¹
      rw [hx, hrel_eq x])
  · intro h x x' hx
    exact h x x' (by
      show (x' : GL (Fin n) K) = A * (x : GL (Fin n) K) * A⁻¹
      rw [hx, ← hrel_eq x])

end UniShapeAux

theorem uniR_shape {K : Type} [Field K] [Finite K] [CharP K 2] {q N : ℕ} (hK : Nat.card K = q ^ 2)
    (hq3 : 3 ∣ q + 1) (hN : 3 ≤ N)
    {Ā : Subgroup (MulAut (PSUg N K q))} {δ' : MulAut (PSUg N K q)}
    {J' : Subgroup (PSUg N K q)} (hR : RDatum Ā δ' J')
    (hĀI : ∀ a ∈ Ā, a ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin N) K q))
      (LargeEvenGUSet (Fin N) K q)) :
    UniShapeConcl q N Ā J' := by
  obtain ⟨f, hf, hq⟩ := CFSG.AGLEmbedding.ToralCensus.exists_eq_two_pow_of_card_eq_sq hK
  subst hq
  have h : UnitaryFieldData 2 f K :=
    CFSG.AGLEmbedding.ToralCensus.unitaryFieldData_of_card_eq_sq hK hf
  by_cases hN3 : N = 3
  ·
    subst hN3
    obtain ⟨Ahat, hL, hcard⟩ :=
      uni_lift_of_three_le (q := 2 ^ f) (n := 3) hK (le_refl 3) hĀI
    have hiso : ∀ g ∈ Ahat, IsHermIsometry (2 ^ f) (g : Matrix (Fin 3) (Fin 3) K) :=
      fun g hg => hL.iso g hg
    have hcube : ∀ g ∈ Ahat, ∃ c : Kˣ, g ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 3) c := by
      intro g hg
      obtain ⟨a, ha, hga⟩ := hL.induces g hg
      have hgN : g ∈ Subgroup.normalizer
          (LargeEvenSUGroup (Fin 3) K (2 ^ f) : Set (GL (Fin 3) K)) :=
        uniShapeR_isometry_mem_normalizer h (hL.iso g hg)
      have hnormg := uniShapeR_normalizes_of_mem_normalizer hgN
      have hga3 : IsConjBy (g ^ 3) (a ^ 3) := by
        have h2 : IsConjBy (g * g) (a * a) := uniShapeR_isConjBy_mul hnormg hga hga
        have h3 : IsConjBy ((g * g) * g) ((a * a) * a) := uniShapeR_isConjBy_mul hnormg h2 hga
        simpa [pow_succ, pow_two] using h3
      have hconj : IsConjBy (g ^ 3) (1 : MulAut (PSUg 3 K (2 ^ f))) := by
        rw [← hR.elem.2 a ha]
        exact hga3
      obtain ⟨c, -, hc⟩ := hL.ker (g ^ 3) (Ahat.pow_mem hg 3) hconj
      exact ⟨c, hc⟩
    have hcomm : ∀ g ∈ Ahat, ∀ k ∈ Ahat, ∃ c : Kˣ,
        g * k * g⁻¹ * k⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 3) c := by
      intro g hg k hk
      obtain ⟨a, ha, hga⟩ := hL.induces g hg
      obtain ⟨b, hb, hkb⟩ := hL.induces k hk
      have hgN : g ∈ Subgroup.normalizer
          (LargeEvenSUGroup (Fin 3) K (2 ^ f) : Set (GL (Fin 3) K)) :=
        uniShapeR_isometry_mem_normalizer h (hL.iso g hg)
      have hkN : k ∈ Subgroup.normalizer
          (LargeEvenSUGroup (Fin 3) K (2 ^ f) : Set (GL (Fin 3) K)) :=
        uniShapeR_isometry_mem_normalizer h (hL.iso k hk)
      have hnormg := uniShapeR_normalizes_of_mem_normalizer hgN
      have hnormgi := uniShapeR_normalizes_of_mem_normalizer (Subgroup.inv_mem _ hgN)
      have hnormk := uniShapeR_normalizes_of_mem_normalizer hkN
      have hnormki := uniShapeR_normalizes_of_mem_normalizer (Subgroup.inv_mem _ hkN)
      have hgk : IsConjBy (g * k) (a * b) := uniShapeR_isConjBy_mul hnormk hga hkb
      have hgki : IsConjBy (g * k * g⁻¹) (a * b * a⁻¹) :=
        uniShapeR_isConjBy_mul hnormgi hgk (uniShapeR_isConjBy_inv hga)
      have hfinal : IsConjBy (g * k * g⁻¹ * k⁻¹) (a * b * a⁻¹ * b⁻¹) :=
        uniShapeR_isConjBy_mul hnormki hgki (uniShapeR_isConjBy_inv hkb)
      have hab : a * b = b * a := CFSG.Open.IsElemAbelian.comm hR.elem ha hb
      have hone : a * b * a⁻¹ * b⁻¹ = 1 := by rw [hab]; group
      have hconj : IsConjBy (g * k * g⁻¹ * k⁻¹) (1 : MulAut (PSUg 3 K (2 ^ f))) := by
        rw [← hone]
        exact hfinal
      obtain ⟨c, -, hc⟩ := hL.ker (g * k * g⁻¹ * k⁻¹)
        (Ahat.mul_mem (Ahat.mul_mem (Ahat.mul_mem hg hk) (Ahat.inv_mem hg))
          (Ahat.inv_mem hk)) hconj
      exact ⟨c, hc⟩
    have hrank := uni_gu_three_rank (q := 2 ^ f) (k := 3) hK hq3 (Or.inr rfl) Ahat hiso hcomm hcube
    have hqpos : 0 < 2 ^ f + 1 := Nat.succ_pos _
    have hle : Nat.card Ā * (2 ^ f + 1) ≤ 9 * (2 ^ f + 1) := by
      rw [← hcard]
      simpa [show (3 : ℕ) ^ (3 - 1) = 9 by norm_num] using hrank
    have hle9 : Nat.card Ā ≤ 9 := Nat.le_of_mul_le_mul_right hle hqpos
    have h27 : (3 : ℕ) ^ 3 ≤ 9 := le_trans hR.card hle9
    exact absurd h27 (by norm_num)
  ·
    have hN4 : 4 ≤ N := by omega
    obtain ⟨Ahat, hL, hcard⟩ := uni_lift (q := 2 ^ f) (n := N) hK hN4 hĀI
    obtain ⟨d, hdA, hδ⟩ := hL.onto δ' hR.mem
    have hnormd : ∀ k ∈ LargeEvenSUGroup (Fin N) K (2 ^ f),
        d * k * d⁻¹ ∈ LargeEvenSUGroup (Fin N) K (2 ^ f) :=
      uniShapeR_normalizes_of_mem_normalizer (uniShapeR_isometry_mem_normalizer h (hL.iso d hdA))
    have hδ3 : IsConjBy (d ^ 3) (δ' ^ 3) := by
      have h2 : IsConjBy (d * d) (δ' * δ') := uniShapeR_isConjBy_mul hnormd hδ hδ
      have h3 : IsConjBy ((d * d) * d) ((δ' * δ') * δ') := uniShapeR_isConjBy_mul hnormd h2 hδ
      simpa [pow_succ, pow_two] using h3
    have hconj : IsConjBy (d ^ 3) (1 : MulAut (PSUg N K (2 ^ f))) := by
      rw [← hR.elem.2 δ' hR.mem]
      exact hδ3
    obtain ⟨c, hc, hdc⟩ := hL.ker (d ^ 3) (Ahat.pow_mem hdA 3) hconj
    by_cases hcube_exists : ∃ s : Kˣ, s ^ (2 ^ f + 1) = 1 ∧ s ^ 3 = c
    ·
      obtain ⟨s, hs, hsc⟩ := hcube_exists
      let d₁ : GL (Fin N) K := Matrix.GeneralLinearGroup.scalar (Fin N) s⁻¹ * d
      have hcenter : Matrix.GeneralLinearGroup.scalar (Fin N) s⁻¹ ∈
          Subgroup.center (GL (Fin N) K) := by
        rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
        exact ⟨s⁻¹, rfl⟩
      have hscomm : ∀ x : GL (Fin N) K,
          Matrix.GeneralLinearGroup.scalar (Fin N) s⁻¹ * x =
            x * Matrix.GeneralLinearGroup.scalar (Fin N) s⁻¹ :=
        fun x => (Subgroup.mem_center_iff.mp hcenter x).symm
      have hd₁A : d₁ ∈ Ahat := by
        refine Ahat.mul_mem ?_ hdA
        apply hL.scalars
        rw [inv_pow, hs, inv_one]
      have hd₁3 : d₁ ^ 3 = 1 := by
        have hpow : d₁ ^ 3 =
            (Matrix.GeneralLinearGroup.scalar (Fin N) s⁻¹) ^ 3 * d ^ 3 :=
          Commute.mul_pow
            ((commute_iff_eq (Matrix.GeneralLinearGroup.scalar (Fin N) s⁻¹) d).mpr
              (hscomm d)) 3
        rw [hpow, ← map_pow, hdc, ← map_mul]
        have hone : (s⁻¹) ^ 3 * c = 1 := by rw [← hsc]; group
        rw [hone, map_one]
      have hδ₁ : IsConjBy d₁ δ' :=
        (uniShapeR_isConjBy_mul_central_iff (s := Matrix.GeneralLinearGroup.scalar (Fin N) s⁻¹)
          hscomm (A := d) (a := δ')).mpr hδ
      exact uniR_cube hK hq3 hN4 hR hL hcard hd₁A hd₁3 hδ₁
    ·
      push Not at hcube_exists
      exact uniR_noncube hK hq3 hN4 hR hL hdA hdc hc hcube_exists hδ

end CFSG.StandardType.TablePThreeKG

end
