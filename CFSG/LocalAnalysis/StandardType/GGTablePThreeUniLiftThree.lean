module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniModel
import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniLift
import CFSG.Assembly.GL83StatedBridge
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsCaseLSU
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeForm
import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUNormal
import CFSG.LocalAnalysis.StandardType.GGSUNonsplitTwoBlockRestrict
import CFSG.LocalAnalysis.GLTheoremA.CatA.L154Symp2
import CFSG.RankThree.PartTwo.KFacts.K71PSU3
import CFSG.Open.StatedAPI
import CFSG.GroupTheory.HallHigmanPiCore
import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUSlice
import CFSG.RankThree.PartTwo.Sec12.Notation
import CFSG.RankThree.PartTwo.Sec8.Statements

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly

section UniLiftPosAux

open Matrix Module CFSG CFSG.Assembly CFSG.AGLEmbedding

open CFSG.LocalAnalysis.ComponentInitial CFSG.LinearGroups CFSG.ClassicalGroups.UnitaryFlag

private theorem uniLiftThree_isHermIsometry_iff_stdHermForm {K : Type} [Field K] {f n : ℕ}
    (h : UnitaryFieldData 2 f K) {A : Matrix (Fin n) (Fin n) K} :
    IsHermIsometry (2 ^ f) A ↔
      ∀ x y, stdHermForm h n (A *ᵥ x) (A *ᵥ y) = stdHermForm h n x y := by
  simp only [IsHermIsometry, stdHermForm_apply, h.bar_apply]

private theorem uniLiftThree_isHermIsometry_iff_mem_unitaryI {K : Type} [Field K] [Finite K] [CharP K 2]
    {f n : ℕ} (h : UnitaryFieldData 2 f K) {g : GL (Fin n) K} :
    IsHermIsometry (2 ^ f) (g : Matrix (Fin n) (Fin n) K) ↔
      g ∈ CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen.unitaryI h n := by
  rw [CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen.unitaryI]
  constructor
  · intro hg
    rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.mem_primeFormUnitary]
    have hmat := CFSG.StandardType.SUTB.map_bar_transpose_mul_of_isometry h
      ((uniLiftThree_isHermIsometry_iff_stdHermForm h).mp hg)
    simpa using hmat
  · intro hg
    rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.mem_primeFormUnitary] at hg
    have hmat : ((g : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * (g : Matrix (Fin n) (Fin n) K) =
        1 := by
      simpa using hg
    exact (uniLiftThree_isHermIsometry_iff_stdHermForm h).mpr
      (CFSG.ComponentClassification.Burgoyne.U.stdHermForm_mulVec h hmat)

private theorem uniLiftThree_isHermIsometry_mul {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ}
    (h : UnitaryFieldData 2 f K) {g g' : GL (Fin n) K}
    (hg : IsHermIsometry (2 ^ f) (g : Matrix (Fin n) (Fin n) K))
    (hg' : IsHermIsometry (2 ^ f) (g' : Matrix (Fin n) (Fin n) K)) :
    IsHermIsometry (2 ^ f) ((g * g' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  rw [uniLiftThree_isHermIsometry_iff_mem_unitaryI h]
  exact Subgroup.mul_mem _ ((uniLiftThree_isHermIsometry_iff_mem_unitaryI h).mp hg)
    ((uniLiftThree_isHermIsometry_iff_mem_unitaryI h).mp hg')

private theorem uniLiftThree_isHermIsometry_inv {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ}
    (h : UnitaryFieldData 2 f K) {g : GL (Fin n) K}
    (hg : IsHermIsometry (2 ^ f) (g : Matrix (Fin n) (Fin n) K)) :
    IsHermIsometry (2 ^ f) ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  rw [uniLiftThree_isHermIsometry_iff_mem_unitaryI h]
  exact Subgroup.inv_mem _ ((uniLiftThree_isHermIsometry_iff_mem_unitaryI h).mp hg)

private theorem uniLiftThree_isHermIsometry_one {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ}
    (h : UnitaryFieldData 2 f K) :
    IsHermIsometry (2 ^ f) ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  rw [uniLiftThree_isHermIsometry_iff_mem_unitaryI h]
  exact Subgroup.one_mem _

private theorem uniLiftThree_isometry_normalizes_SU {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ}
    (h : UnitaryFieldData 2 f K) {g : GL (Fin n) K}
    (hg : IsHermIsometry (2 ^ f) (g : Matrix (Fin n) (Fin n) K)) :
    ∀ k ∈ LargeEvenSUGroup (Fin n) K (2 ^ f), g * k * g⁻¹ ∈ LargeEvenSUGroup (Fin n) K (2 ^ f) := by
  have hgn : g ∈ Subgroup.normalizer (Open.StatedSU n (2 ^ f) K : Set (GL (Fin n) K)) :=
    CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen.unitaryI_le_normalizer h
      ((uniLiftThree_isHermIsometry_iff_mem_unitaryI h).mp hg)
  intro k hk
  rw [CFSG.Assembly.largeEvenSUGroup_eq_statedSU] at hk ⊢
  exact (Subgroup.mem_normalizer_iff.mp hgn k).mp hk

private theorem uniLiftThree_isConjBy_mul {n q : ℕ} {K : Type} [Field K] {g g' : GL (Fin n) K}
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

private theorem uniLiftThree_isConjBy_inv {n q : ℕ} {K : Type} [Field K] {g : GL (Fin n) K}
    {a : MulAut (PSUg n K q)} (h1 : IsConjBy g a) : IsConjBy g⁻¹ a⁻¹ := by
  intro x x' hx
  have hrel : (x : GL (Fin n) K) = g * (x' : GL (Fin n) K) * g⁻¹ := by rw [hx]; group
  have h := h1 x' x hrel
  calc a⁻¹ (LargeEvenProjMk (LargeEvenSUGroup (Fin n) K q) x)
      = a⁻¹ (a (LargeEvenProjMk (LargeEvenSUGroup (Fin n) K q) x')) := by rw [← h]
    _ = LargeEvenProjMk (LargeEvenSUGroup (Fin n) K q) x' := by
          rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]

private theorem uniLiftThree_isConjBy_one {n q : ℕ} {K : Type} [Field K] :
    IsConjBy (1 : GL (Fin n) K) (1 : MulAut (PSUg n K q)) := by
  intro x x' hx
  have hxx : x' = x := Subtype.ext (by simpa using hx)
  subst hxx
  rw [MulAut.one_apply]

private theorem uniLiftThree_isConjBy_mul_central_iff {n q : ℕ} {K : Type} [Field K] {s : GL (Fin n) K}
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

private theorem uniLiftThree_isConjBy_eq {n q : ℕ} {K : Type} [Field K] {g : GL (Fin n) K}
    {a a' : MulAut (PSUg n K q)}
    (hnorm : ∀ k ∈ LargeEvenSUGroup (Fin n) K q, g * k * g⁻¹ ∈ LargeEvenSUGroup (Fin n) K q)
    (h : IsConjBy g a) (h' : IsConjBy g a') : a = a' := by
  ext y
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective
    ((LargeEvenScalars (Fin n) K).subgroupOf (LargeEvenSUGroup (Fin n) K q)) y
  subst hx
  let x' : ↥(LargeEvenSUGroup (Fin n) K q) :=
    ⟨g * (x : GL (Fin n) K) * g⁻¹, hnorm x x.2⟩
  have hx' : (x' : GL (Fin n) K) = g * (x : GL (Fin n) K) * g⁻¹ := rfl
  rw [h x x' hx', h' x x' hx']

private theorem uniLiftThree_isConjBy_scalar_one {n q : ℕ} {K : Type} [Field K] (c : Kˣ) :
    IsConjBy (GeneralLinearGroup.scalar (Fin n) c : GL (Fin n) K)
      (1 : MulAut (PSUg n K q)) := by
  simpa using (uniLiftThree_isConjBy_mul_central_iff (s := GeneralLinearGroup.scalar (Fin n) c)
    (fun x => (commute_scalar c x).eq.symm) (A := (1 : GL (Fin n) K))
    (a := (1 : MulAut (PSUg n K q)))).mpr uniLiftThree_isConjBy_one

end UniLiftPosAux

section UniLiftPosMain

open Matrix Module CFSG CFSG.Assembly CFSG.AGLEmbedding

theorem uni_lift_of_three_le {K : Type} [Field K] [Finite K] [CharP K 2] {q n : ℕ} (hK : Nat.card K = q ^ 2)
    (hn : 3 ≤ n) {Ā : Subgroup (MulAut (PSUg n K q))}
    (hĀI : ∀ a ∈ Ā, a ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin n) K q))
      (LargeEvenGUSet (Fin n) K q)) :
    ∃ Ahat : Subgroup (GL (Fin n) K), UniLift n q K Ā Ahat ∧ Nat.card Ahat = Nat.card Ā * (q + 1) := by
  obtain ⟨f, hf, hq⟩ := CFSG.AGLEmbedding.ToralCensus.exists_eq_two_pow_of_card_eq_sq hK
  subst hq
  have h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f K :=
    CFSG.AGLEmbedding.ToralCensus.unitaryFieldData_of_card_eq_sq hK hf
  haveI : NeZero n := ⟨by omega⟩
  haveI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_neZero n⟩⟩
  let Ahat : Subgroup (GL (Fin n) K) :=
    { carrier := {g | IsHermIsometry (2 ^ f) (g : Matrix (Fin n) (Fin n) K) ∧
        ∃ a ∈ Ā, IsConjBy g a}
      one_mem' := ⟨uniLiftThree_isHermIsometry_one h, 1, Ā.one_mem, uniLiftThree_isConjBy_one⟩
      mul_mem' := by
        rintro g g' ⟨hg, a, ha, hga⟩ ⟨hg', a', ha', hga'⟩
        exact ⟨uniLiftThree_isHermIsometry_mul h hg hg', a * a', Ā.mul_mem ha ha',
          uniLiftThree_isConjBy_mul (uniLiftThree_isometry_normalizes_SU h hg') hga hga'⟩
      inv_mem' := by
        rintro g ⟨hg, a, ha, hga⟩
        exact ⟨uniLiftThree_isHermIsometry_inv h hg, a⁻¹, Ā.inv_mem ha, uniLiftThree_isConjBy_inv hga⟩ }
  have hscal : ∀ c : Kˣ, c ^ (2 ^ f + 1) = 1 →
      GeneralLinearGroup.scalar (Fin n) c ∈ Ahat := by
    intro c hc
    have hnorm : h.norm (c : K) = 1 := by
      rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.norm_eq_pow]
      have hc' := congrArg (fun u : Kˣ => (u : K)) hc
      rw [Units.val_pow_eq_pow_val, Units.val_one] at hc'
      exact hc'
    exact ⟨(uniLiftThree_isHermIsometry_iff_mem_unitaryI h).mpr
        (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.scalar_mem_primeFormUnitary_one h hnorm),
      1, Ā.one_mem, uniLiftThree_isConjBy_scalar_one c⟩
  have honto : ∀ a ∈ Ā, ∃ g ∈ Ahat, IsConjBy g a := by
    intro a ha
    obtain ⟨A, hAGU, hAconj⟩ := hĀI a ha
    obtain ⟨z, P₁, hP₁mat, hP₁eq⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.K155XSp.l154s_guSet_decomp h hAGU
    have hP₁iso : IsHermIsometry (2 ^ f) (P₁ : Matrix (Fin n) (Fin n) K) :=
      (uniLiftThree_isHermIsometry_iff_stdHermForm h).mpr
        (CFSG.ComponentClassification.Burgoyne.U.stdHermForm_mulVec h hP₁mat)
    have hconj : IsConjBy P₁ a := by
      rw [hP₁eq] at hAconj
      exact (uniLiftThree_isConjBy_mul_central_iff (s := GeneralLinearGroup.scalar (Fin n) z)
        (fun x => (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar z x).eq.symm)
        (A := P₁) (a := a)).mp hAconj
    exact ⟨P₁, ⟨hP₁iso, a, ha, hconj⟩, hconj⟩
  have hker : ∀ g ∈ Ahat, IsConjBy g (1 : MulAut (PSUg n K (2 ^ f))) →
      ∃ c : Kˣ, c ^ (2 ^ f + 1) = 1 ∧ g = GeneralLinearGroup.scalar (Fin n) c := by
    intro g hg hconj
    have hgU : g ∈ CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen.unitaryI h n :=
      (uniLiftThree_isHermIsometry_iff_mem_unitaryI h).mp hg.1
    have hc : ∀ k ∈ Open.StatedSU n (2 ^ f) K,
        g * k * g⁻¹ * k⁻¹ ∈ Open.StatedScalars (Fin n) K := by
      intro k hk
      let kH : ↥(LargeEvenSUGroup (Fin n) K (2 ^ f)) := ⟨k, hk⟩
      let k' : ↥(LargeEvenSUGroup (Fin n) K (2 ^ f)) :=
        ⟨g * k * g⁻¹, uniLiftThree_isometry_normalizes_SU h hg.1 k hk⟩
      have hk'val : (k' : GL (Fin n) K) = g * k * g⁻¹ := rfl
      have heq : LargeEvenProjMk (LargeEvenSUGroup (Fin n) K (2 ^ f)) kH =
          LargeEvenProjMk (LargeEvenSUGroup (Fin n) K (2 ^ f)) k' := by
        simpa using hconj kH k' hk'val
      have hmem : kH⁻¹ * k' ∈
          (Open.StatedScalars (Fin n) K).subgroupOf (LargeEvenSUGroup (Fin n) K (2 ^ f)) := by
        have heq' : QuotientGroup.mk kH = QuotientGroup.mk k' := heq
        exact QuotientGroup.eq.mp heq'
      have hmemS : (k : GL (Fin n) K)⁻¹ * (g * k * g⁻¹) ∈ Open.StatedScalars (Fin n) K := by
        have := Subgroup.mem_subgroupOf.mp hmem
        simpa using this
      have hconjS : (g * k * g⁻¹) * ((k : GL (Fin n) K)⁻¹ * (g * k * g⁻¹)) *
          (g * k * g⁻¹)⁻¹ ∈ Open.StatedScalars (Fin n) K :=
        (Open.StatedScalars.normal (Fin n) K).conj_mem
          ((k : GL (Fin n) K)⁻¹ * (g * k * g⁻¹)) hmemS (g * k * g⁻¹)
      have hsimp : (g * k * g⁻¹) * ((k : GL (Fin n) K)⁻¹ * (g * k * g⁻¹)) *
          (g * k * g⁻¹)⁻¹ = g * k * g⁻¹ * k⁻¹ := by group
      rwa [hsimp] at hconjS
    have hcen : g ∈ Subgroup.center (GL (Fin n) K) :=
      CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen.mem_center_of_conj_statedSU h hn hgU hc
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hcen
    obtain ⟨c, hc_eq⟩ := hcen
    have hnorm : h.norm (c : K) = 1 :=
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.norm_eq_one_of_scalar_mem_primeFormUnitary
        h (by omega) (1 : GL (Fin n) K) (hc_eq ▸ hgU)
    refine ⟨c, ?_, hc_eq.symm⟩
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    rw [← CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.norm_eq_pow]
    exact hnorm
  have hlift : UniLift n (2 ^ f) K Ā Ahat :=
    { iso := fun _ hg => hg.1
      scalars := hscal
      induces := fun _ hg => hg.2
      onto := honto
      ker := hker }
  refine ⟨Ahat, hlift, ?_⟩
  let fh : Ahat →* Ā :=
    { toFun := fun g => ⟨Classical.choose g.2.2, (Classical.choose_spec g.2.2).1⟩
      map_one' := by
        apply Subtype.ext
        exact uniLiftThree_isConjBy_eq (uniLiftThree_isometry_normalizes_SU h (1 : Ahat).2.1)
          (Classical.choose_spec (1 : Ahat).2.2).2 uniLiftThree_isConjBy_one
      map_mul' := by
        intro g g'
        apply Subtype.ext
        exact uniLiftThree_isConjBy_eq (uniLiftThree_isometry_normalizes_SU h (g * g').2.1)
          (Classical.choose_spec (g * g').2.2).2
          (uniLiftThree_isConjBy_mul (uniLiftThree_isometry_normalizes_SU h g'.2.1)
            (Classical.choose_spec g.2.2).2 (Classical.choose_spec g'.2.2).2) }
  have hkerf : ∀ g : Ahat, fh g = 1 ↔
      IsConjBy (g : GL (Fin n) K) (1 : MulAut (PSUg n K (2 ^ f))) := by
    intro g
    constructor
    · intro hg
      have hch : Classical.choose g.2.2 = 1 :=
        congrArg (fun x : Ā => (x : MulAut (PSUg n K (2 ^ f)))) hg
      rw [← hch]
      exact (Classical.choose_spec g.2.2).2
    · intro hg
      apply Subtype.ext
      exact uniLiftThree_isConjBy_eq (uniLiftThree_isometry_normalizes_SU h g.2.1) (Classical.choose_spec g.2.2).2 hg
  have hsurj : Function.Surjective fh := by
    intro a
    obtain ⟨g, hgA, hgconj⟩ := honto a a.2
    refine ⟨⟨g, hgA⟩, ?_⟩
    apply Subtype.ext
    exact uniLiftThree_isConjBy_eq (uniLiftThree_isometry_normalizes_SU h hgA.1)
      (Classical.choose_spec hgA.2).2 hgconj
  let nU := CFSG.RankThree.PartTwo.KFacts.normOneUnits K (2 ^ f)
  let Φ : nU → fh.ker := fun c =>
    ⟨⟨GeneralLinearGroup.scalar (Fin n) (c : Kˣ), hscal (c : Kˣ) c.2⟩,
      (hkerf ⟨GeneralLinearGroup.scalar (Fin n) (c : Kˣ), hscal (c : Kˣ) c.2⟩).mpr
        (uniLiftThree_isConjBy_scalar_one (c : Kˣ))⟩
  let Ψ : fh.ker → nU := fun g =>
    ⟨Classical.choose (hker g.1 g.1.2 ((hkerf g.1).mp g.2)),
      (Classical.choose_spec (hker g.1 g.1.2 ((hkerf g.1).mp g.2))).1⟩
  have hΦΨ : Function.LeftInverse Ψ Φ := by
    intro c
    apply Subtype.ext
    apply Units.ext
    have hspec := (Classical.choose_spec
      (hker (Φ c).1 (Φ c).1.2 ((hkerf (Φ c).1).mp (Φ c).2))).2
    have h2 : (GeneralLinearGroup.scalar (Fin n) (c : Kˣ) : GL (Fin n) K) =
        GeneralLinearGroup.scalar (Fin n) (Classical.choose
          (hker (Φ c).1 (Φ c).1.2 ((hkerf (Φ c).1).mp (Φ c).2))) := hspec
    have hmat : Matrix.scalar (Fin n) ((c : Kˣ) : K) =
        Matrix.scalar (Fin n) ((Classical.choose
          (hker (Φ c).1 (Φ c).1.2 ((hkerf (Φ c).1).mp (Φ c).2)) : Kˣ) : K) := by
      simpa only [Matrix.GeneralLinearGroup.coe_scalar] using
        congrArg (fun u : GL (Fin n) K => (u : Matrix (Fin n) (Fin n) K)) h2
    exact (Matrix.scalar_inj.mp hmat).symm
  have hΨΦ : Function.RightInverse Ψ Φ := by
    intro g
    apply Subtype.ext
    apply Subtype.ext
    exact ((Classical.choose_spec (hker g.1 g.1.2 ((hkerf g.1).mp g.2))).2).symm
  have hbij : Function.Bijective Φ :=
    ⟨fun a b hab => by rw [← hΦΨ a, hab, hΦΨ b],
      fun b => ⟨Ψ b, hΨΦ b⟩⟩
  have hcard : Nat.card Ahat = Nat.card Ā * (2 ^ f + 1) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup fh.ker]
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange fh).toEquiv]
    rw [MonoidHom.range_eq_top.mpr hsurj]
    rw [Nat.card_congr (Subgroup.topEquiv (G := Ā)).toEquiv]
    rw [← Nat.card_congr (Equiv.ofBijective Φ hbij)]
    rw [CFSG.RankThree.PartTwo.KFacts.card_normOneUnits hK]
  exact hcard

end UniLiftPosMain

end CFSG.StandardType.TablePThreeKG

end
