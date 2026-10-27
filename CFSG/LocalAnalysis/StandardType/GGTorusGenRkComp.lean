module

public import CFSG.LocalAnalysis.StandardType.GGSuDvdRootGenComp
public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitDvdAct
public import CFSG.LocalAnalysis.StandardType.GGTwE6SCFourCover
public import CFSG.LocalAnalysis.StandardType.GGTorusGenRkClass
public import CFSG.LocalAnalysis.StandardType.GGTableBLinUnitLCx

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.StandardType.LineU
open CFSG.LocalAnalysis.ComponentInitial

private def conjNAut {d n : ℕ} {K : Type} [Field K]
    (D : GL (Fin d) K)
    (hD : D ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K))) :
    MulAut ↥(unitarySU 2 n K d) where
  toFun := conjN D hD
  invFun := conjN D⁻¹ (Subgroup.inv_mem _ hD)
  left_inv s := by
    apply Subtype.ext
    rw [coe_conjN, coe_conjN]
    group
  right_inv s := by
    apply Subtype.ext
    rw [coe_conjN, coe_conjN]
    group
  map_mul' s u := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, coe_conjN]
    group

private theorem conjNAut_mul_diag {d n : ℕ} {K : Type} [Field K]
    {D : GL (Fin d) K}
    (hD : D ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)))
    {t : Fin d → K} (hDt : (D : Matrix (Fin d) (Fin d) K) = diagonal t)
    (s : ↥(unitarySU 2 n K d)) :
    (((conjNAut D hD s : ↥(unitarySU 2 n K d)) : GL (Fin d) K) :
        Matrix (Fin d) (Fin d) K) * diagonal t =
      diagonal t * ((s : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
  have h : (((conjNAut D hD s : ↥(unitarySU 2 n K d)) : GL (Fin d) K)) * D =
      D * (s : GL (Fin d) K) := by
    show (((conjN D hD s : ↥(unitarySU 2 n K d)) : GL (Fin d) K)) * D =
      D * (s : GL (Fin d) K)
    rw [coe_conjN]
    group
  have hm := congrArg (fun x : GL (Fin d) K => ((x : Matrix (Fin d) (Fin d) K))) h
  simp only [Units.val_mul] at hm
  rw [← hDt]
  exact hm

private theorem ker_le_center {d n : ℕ} {K : Type} [Field K] {L' : Type} [Group L']
    {φ : ↥(unitarySU 2 n K d) →* L'} (hφ : UnitTB.Model φ) :
    φ.ker ≤ Subgroup.center ↥(unitarySU 2 n K d) := by
  intro g hg
  obtain ⟨c, hc⟩ := hφ.ker g hg
  have hcomm : ∀ M : Matrix (Fin d) (Fin d) K,
      diagonal (fun _ => c) * M = M * diagonal (fun _ => c) := by
    intro M
    show Matrix.scalar (Fin d) c * M = M * Matrix.scalar (Fin d) c
    exact Matrix.scalar_comm c (fun r' => mul_comm c r') M
  rw [Subgroup.mem_center_iff]
  intro h
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, hc]
  first
    | exact hcomm _
    | exact (hcomm _).symm

open Classical in
theorem exists_class_of_isComponentOf_ggFix
    {d n : ℕ} {K : Type} [Field K] [Finite K] {L' : Type} [Group L']
    {φ : ↥(unitarySU 2 n K d) →* L'} (hφ : UnitTB.Model φ)
    {a : MulAut L'} {t : Fin d → K} (ha : ActsDiagU φ a t) {J' : Subgroup L'}
    (hJ : IsComponentOf J' (ggFix a)) :
    ∃ i₀ : Fin d, 2 ≤ (Finset.univ.filter fun i => t i = t i₀).card ∧
      J' = (TableBUE.blockSU (K := K) (n := n) (Finset.univ.filter fun i => t i = t i₀)).map φ := by
  classical
  have ht : ∀ k : Fin d, t k ≠ 0 := ActsDiagU.ne_zero ha
  obtain ⟨D, hD, hDt, hact⟩ := ha
  let δ : MulAut ↥(unitarySU 2 n K d) := conjNAut D hD
  have hδ : ∀ s : ↥(unitarySU 2 n K d),
      (((δ s : ↥(unitarySU 2 n K d)) : GL (Fin d) K) :
          Matrix (Fin d) (Fin d) K) * diagonal t =
        diagonal t * ((s : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) :=
    fun s => conjNAut_mul_diag hD hDt s
  have hker : φ.ker ≤ Subgroup.center ↥(unitarySU 2 n K d) := ker_le_center hφ
  have hcompat : ∀ s : ↥(unitarySU 2 n K d), a (φ s) = φ (δ s) := by
    intro s
    rw [hact s]
    rfl
  obtain ⟨Q, hQ, hQmap⟩ :=
    SCFourCover.exists_isComponentOf_map_eq (ψ := φ) hφ.surj hker (a := δ) (φ := a) hcompat hJ
  obtain ⟨i₀, hcard, hQeq⟩ :=
    eq_blockSU_of_isComponentOf_ggFix_diag hφ.field ht δ hδ hQ
  refine ⟨i₀, hcard, ?_⟩
  rw [hQeq] at hQmap
  exact hQmap.symm

private theorem blockExt_diagonal_conj {K : Type} [Field K] {d : ℕ}
    (S : Finset (Fin d)) (t : Fin d → K) (ht : ∀ i, t i ≠ 0)
    (M : Matrix (Fin S.card) (Fin S.card) K) :
    diagonal t * TableBUE.blockExt S M * diagonal (fun i => (t i)⁻¹) =
      TableBUE.blockExt S
        (diagonal (fun i => t (S.equivFin.symm i)) * M *
          diagonal (fun i => (t (S.equivFin.symm i))⁻¹)) := by
  classical
  ext i j
  by_cases hi : i ∈ S
  · by_cases hj : j ∈ S
    · simp [TableBUE.blockExt, hi, hj, Matrix.diagonal_mul, Matrix.mul_diagonal]
    · simp [TableBUE.blockExt, hi, hj, Matrix.diagonal_mul, Matrix.mul_diagonal]
  · by_cases hij : i = j
    · subst j
      simp [TableBUE.blockExt, hi, Matrix.diagonal_mul, Matrix.mul_diagonal, ht i]
    · simp [TableBUE.blockExt, hi, hij, Matrix.diagonal_mul, Matrix.mul_diagonal]

private theorem mem_unitarySU_of_blockExt {K : Type} [Field K] {d n : ℕ}
    (h : UnitaryFieldData 2 n K) (S : Finset (Fin d))
    (g : GL (Fin S.card) K) (v : ↥(unitarySU 2 n K d))
    (hv : ((v : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      TableBUE.blockExt S (g : Matrix (Fin S.card) (Fin S.card) K)) :
    g ∈ unitarySU 2 n K S.card := by
  have hb : TableBUE.IsBlockOn S ((v : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
    rw [hv]
    exact TableBUE.isBlockOn_blockExt _
  have hr : TableBUE.blockRes S ((v : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      (g : Matrix (Fin S.card) (Fin S.card) K) := by
    rw [hv, TableBUE.blockRes_blockExt]
  obtain ⟨hdet, hunit⟩ := (mem_unitarySU_iff h).mp v.2
  rw [mem_unitarySU_iff h]
  constructor
  · rw [← hr, ← TableBUE.det_eq_det_blockRes hb]
    exact hdet
  · have hu := congrArg (TableBUE.blockRes S) hunit
    rw [TableBUE.blockRes_mul (hb.map_transpose h.bar), TableBUE.blockRes_map_transpose,
      hr, TableBUE.blockRes_one] at hu
    exact hu

private theorem block_diag_conj_mem {K : Type} [Field K] {d n : ℕ}
    (h : UnitaryFieldData 2 n K) (S : Finset (Fin d))
    {D : GL (Fin d) K}
    (hD : D ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)))
    {t : Fin d → K} (hDt : (D : Matrix (Fin d) (Fin d) K) = diagonal t)
    {D' : GL (Fin S.card) K}
    (hD't : (D' : Matrix (Fin S.card) (Fin S.card) K) =
      diagonal (fun i => t (S.equivFin.symm i)))
    {g : GL (Fin S.card) K} (hg : g ∈ unitarySU 2 n K S.card) :
    D' * g * D'⁻¹ ∈ unitarySU 2 n K S.card := by
  let v := conjN D hD (TableBUE.blockExtSU S h ⟨g, hg⟩)
  apply mem_unitarySU_of_blockExt h S (D' * g * D'⁻¹) v
  simp only [v, coe_conjN, Units.val_mul, TableBUE.coe_blockExtSU]
  rw [hDt, coe_inv_diag hDt, hD't, coe_inv_diag hD't]
  exact blockExt_diagonal_conj S t (diag_ne_zero_of_eq hDt) _

theorem exists_diagonal_normalizer_block {K : Type} [Field K] {d n : ℕ}
    (h : UnitaryFieldData 2 n K) (S : Finset (Fin d))
    {D : GL (Fin d) K}
    (hD : D ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)))
    {t : Fin d → K} (hDt : (D : Matrix (Fin d) (Fin d) K) = diagonal t) :
    ∃ (D' : GL (Fin S.card) K)
      (hD' : D' ∈ Subgroup.normalizer
        (unitarySU 2 n K S.card : Set (GL (Fin S.card) K))),
      (D' : Matrix (Fin S.card) (Fin S.card) K) =
          diagonal (fun i => t (S.equivFin.symm i)) ∧
        ∀ u : ↥(unitarySU 2 n K S.card),
          TableBUE.blockExtSU S h (conjN D' hD' u) =
            conjN D hD (TableBUE.blockExtSU S h u) := by
  classical
  let z : Fin S.card → Kˣ := fun i =>
    Units.mk0 (t (S.equivFin.symm i)) (diag_ne_zero_of_eq hDt _)
  let D' : GL (Fin S.card) K := CFSG.SectionRank.OddCover.diagHom S.card z
  have hD't : (D' : Matrix (Fin S.card) (Fin S.card) K) =
      diagonal (fun i => t (S.equivFin.symm i)) := by
    simp [D', z, CFSG.SectionRank.OddCover.coe_diagHom]
  have hD' : D' ∈ Subgroup.normalizer
      (unitarySU 2 n K S.card : Set (GL (Fin S.card) K)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · exact block_diag_conj_mem h S hD hDt hD't
    · intro hg
      have hz := block_diag_conj_mem h S (Subgroup.inv_mem _ hD)
        (coe_inv_diag hDt) (coe_inv_diag hD't) hg
      have he : D'⁻¹ * (D' * g * D'⁻¹) * D' = g := by group
      simpa only [inv_inv, he] using hz
  refine ⟨D', hD', hD't, fun u => ?_⟩
  apply Subtype.ext
  apply Units.ext
  simp only [TableBUE.coe_blockExtSU, coe_conjN, Units.val_mul]
  rw [hDt, coe_inv_diag hDt, hD't, coe_inv_diag hD't]
  exact (blockExt_diagonal_conj S t (diag_ne_zero_of_eq hDt) _).symm

theorem actsDiagU_of_block {K : Type} [Field K] {d n : ℕ}
    {L' J' : Type} [Group L'] [Group J']
    {φ : ↥(unitarySU 2 n K d) →* L'} (hM : UnitTB.Model φ)
    (S : Finset (Fin d)) (ψ : ↥(unitarySU 2 n K S.card) →* J') (j : J' →* L')
    (hj : Function.Injective j)
    (hψ : ∀ u, j (ψ u) = φ (TableBUE.blockExtSU S hM.field u))
    {a : MulAut L'} {t : Fin d → K} (ha : ActsDiagU φ a t)
    (b : MulAut J') (hab : ∀ u, j (b u) = a (j u)) :
    ActsDiagU ψ b (fun i => t (S.equivFin.symm i)) := by
  obtain ⟨D, hD, hDt, hact⟩ := ha
  obtain ⟨D', hD', hD't, hemb⟩ := exists_diagonal_normalizer_block hM.field S hD hDt
  refine ⟨D', hD', hD't, fun u => ?_⟩
  apply hj
  rw [hab, hψ, hact, hψ, hemb]

open Classical in
theorem exists_model_of_isComponentOf_ggFix
    {d n : ℕ} {K : Type} [Field K] [Finite K] {L' : Type} [Group L']
    {φ : ↥(unitarySU 2 n K d) →* L'} (hM : UnitTB.Model φ)
    {a : MulAut L'} {t : Fin d → K} (ha : ActsDiagU φ a t) {J' : Subgroup L'}
    (hJ : IsComponentOf J' (ggFix a)) :
    ∃ i₀ : Fin d, let S := Finset.univ.filter fun i => t i = t i₀
      2 ≤ S.card ∧ ∃ ψ : ↥(unitarySU 2 n K S.card) →* ↥J',
        UnitTB.Model ψ ∧
          (∀ u, (ψ u : L') = φ (TableBUE.blockExtSU S hM.field u)) ∧
          (∀ (b : MulAut L') (s : Fin d → K), ActsDiagU φ b s →
            ∀ (bJ : MulAut ↥J'), (∀ z : J', (bJ z : L') = b z) →
              ActsDiagU ψ bJ (fun i => s (S.equivFin.symm i))) := by
  classical
  obtain ⟨i₀, hcard, hblock⟩ := exists_class_of_isComponentOf_ggFix hM ha hJ
  let S := Finset.univ.filter fun i => t i = t i₀
  let f := φ.comp (TableBUE.blockExtSU S hM.field)
  have hr : f.range = J' := by
    change (φ.comp (TableBUE.blockExtSU S hM.field)).range = J'
    rw [MonoidHom.range_comp, TableBUE.range_blockExtSU]
    exact hblock.symm
  let ψ : ↥(unitarySU 2 n K S.card) →* ↥J' :=
    f.codRestrict J' (fun u => by rw [← hr]; exact ⟨u, rfl⟩)
  have hψ : ∀ u, (ψ u : L') = φ (TableBUE.blockExtSU S hM.field u) := fun _ => rfl
  have hψM : UnitTB.Model ψ := by
    refine ⟨hM.field, ?_, ?_⟩
    · intro z
      have hz : (z : L') ∈ f.range := by rw [hr]; exact z.2
      obtain ⟨u, hu⟩ := hz
      exact ⟨u, Subtype.ext hu⟩
    · intro u hu
      have hu' : f u = 1 := congrArg (fun z : J' => (z : L')) hu
      have hf : f.rangeRestrict u = 1 := Subtype.ext hu'
      exact (hM.block S).ker u hf
  refine ⟨i₀, hcard, ψ, hψM, hψ, ?_⟩
  intro b s hb bJ hres
  exact actsDiagU_of_block hM S ψ J'.subtype Subtype.val_injective hψ hb bJ hres

theorem ggUnitaryModel_fix_mem_centralizer
    {G : Type} [Group G] [Finite G] {K : Type} [Field K] {n d p : ℕ}
    {Bs X : Subgroup G} (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hBs : CFSG.Open.IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    {ψ : ↥(unitarySU 2 n K d) →* ↥X} (hM : UnitTB.Model ψ) (hd : 3 ≤ d)
    (hdiag : ∀ a ∈ (ggGamma X hN).range, ∃ t : Fin d → K, ActsDiagU ψ a t)
    (b : Bs) (hb : ∀ φ ∈ ggAutomizer X Bs, φ b = b) :
    (b : G) ∈ Subgroup.centralizer (X : Set G) := by
  have hAp : ∀ a ∈ (ggGamma X hN).range, a ^ p = 1 := by
    rintro a ⟨z, rfl⟩
    have hz : z ^ p = 1 := Subtype.ext (hBs.2 (z : G) z.2)
    rw [← map_pow, hz, map_one]
  have hW := LineU.weyl_W_prop hM.field hd hM.ker hAp hdiag
  obtain ⟨t, ht⟩ := hdiag (ggGamma X hN b) ⟨b, rfl⟩
  apply (ggGamma_eq_one_iff X hN b).mp
  apply UnitTB.eq_one_of_conj_perm hM hd ht
  intro σ
  let v : X := ψ (permSU hM.field σ)
  have hvN : (v : G) ∈ Subgroup.normalizer (Bs : Set G) :=
    mem_normalizer_of_weyl hN hSC (hW v ⟨σ, rfl⟩)
  have hvfix : (v : G) * (b : G) * (v : G)⁻¹ = b := by
    exact congrArg Subtype.val
      (hb (ggConjAut Bs hvN) (ggConjAut_mem_ggAutomizer v.2 hvN))
  have hcomm : (v : G) * (b : G) = (b : G) * (v : G) := by
    have he := congrArg (fun z : G => z * (v : G)) hvfix
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using he
  have hbv : ggGamma X hN b v = v := by
    apply Subtype.ext
    change (b : G) * (v : G) * (b : G)⁻¹ = v
    rw [← hcomm, mul_inv_cancel_right]
  have hcommAut : MulAut.conj v * ggGamma X hN b = ggGamma X hN b * MulAut.conj v := by
    apply MulEquiv.ext
    intro z
    change v * (ggGamma X hN b) z * v⁻¹ = (ggGamma X hN b) (v * z * v⁻¹)
    rw [map_mul, map_mul, map_inv, hbv]
  change MulAut.conj v * ggGamma X hN b * (MulAut.conj v)⁻¹ = ggGamma X hN b
  rw [hcommAut, mul_inv_cancel_right]

end CFSG.StandardType
