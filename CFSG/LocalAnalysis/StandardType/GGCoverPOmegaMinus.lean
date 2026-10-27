module

public import CFSG.LocalAnalysis.StandardType.GGCoverPToral
public import CFSG.LocalAnalysis.StandardType.GGCoverPClassicalInner
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticOmega
public import CFSG.LocalAnalysis.StandardType.GGOmegaMinusRootGenConj
public import CFSG.LocalAnalysis.StandardType.GGOmegaMinusRootGenIso
import CFSG.Mathlib.GroupTheory.Automorphism.ConjCommute
import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
import CFSG.Open.StatedAPI
import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalSymplecticField

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

namespace CoverPOmMinus

open CFSG.Open
open CFSG.SeitzReduction.SymplecticPilot
open CFSG.ComponentClassification.ClassicalModelStatedBridge

private def IsMinusDiag {K : Type} [Field K] (p : ℕ) {m : ℕ} {b c : K}
    (h : LargeEvenOmega (LargeEvenQMinus m b c)) : Prop :=
  ∃ d : LargeEvenMinusIdx m → K,
    (∀ x, d x ^ p = 1) ∧ (∀ j : Fin 2, d (Sum.inr j) = 1) ∧
      ((h : GL (LargeEvenMinusIdx m) K) :
        Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K) = Matrix.diagonal d

private noncomputable def torusImage (K : Type) [Field K] [Finite K] [CharP K 2]
    (m p : ℕ) {b c : K} {ζ : Kˣ} (hζ : ζ ^ p = 1) :
    Set (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c))) :=
  (rMinusEquivStatedOmega K m b c).symm ''
    ((omMinusTorus (K := K) (m := m) (p := p) (b := b) (c := c) hζ).range :
      Set (StatedOmega (StatedQuadMinus (m + 1) K b c)))

private theorem pow_eq_one_of_isMinusDiag {K : Type} [Field K] [Finite K] [CharP K 2]
    {m p : ℕ} {b c : K} {h : LargeEvenOmega (LargeEvenQMinus m b c)}
    (hh : IsMinusDiag p h) : h ^ p = 1 := by
  obtain ⟨d, hdp, -, hmat⟩ := hh
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one, Units.val_pow_eq_pow_val, hmat, Matrix.diagonal_pow]
  change Matrix.diagonal (fun x => d x ^ p) = (1 : Matrix _ _ _)
  rw [show (fun x => d x ^ p) = fun _ => (1 : K) from funext hdp]
  simp [Matrix.diagonal_one]

private theorem frobBlock_commute_diagonal {K : Type} [Field K] {m : ℕ} {b c : K}
    {d : LargeEvenMinusIdx m → K} (hd : ∀ j : Fin 2, d (Sum.inr j) = 1) (k : ℕ) :
    Matrix.diagonal (fun x => d x ^ 2 ^ k) * LargeEvenFrobBlock m b c k =
      LargeEvenFrobBlock m b c k * Matrix.diagonal (fun x => d x ^ 2 ^ k) := by
  let d₁ : (Fin m ⊕ Fin m) → K := fun x => d (Sum.inl x)
  have hd1 : (fun x : LargeEvenMinusIdx m => d x ^ 2 ^ k) =
      Sum.elim (fun x => d₁ x ^ 2 ^ k) (fun _ : Fin 2 => (1 : K)) := by
    funext x
    rcases x with x | j
    · rfl
    · rw [hd j]; simp
  rw [hd1, LargeEvenFrobBlock, ← Matrix.fromBlocks_diagonal,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one,
    Matrix.diagonal_one]

private theorem coe_glReindex_symm_omMinusTorusGL {K : Type} [Field K] [Finite K] [CharP K 2]
    {m p : ℕ} [NeZero p] {ζ : Kˣ} (hζ : ζ ^ p = 1)
    (f : Fin m → Multiplicative (ZMod p)) :
    let t : Fin m → Kˣ := fun i => TableBSymp.zmodPowHom hζ (f i)
    let d : LargeEvenMinusIdx (m + 1 - 1) → K :=
      Sum.elim (Sum.elim (fun i => (t i : K)) (fun i => ((t i)⁻¹ : K))) (fun _ => 1)
    let g : GL (LargeEvenMinusIdx (m + 1 - 1)) K :=
      (glReindex K (Equiv.sumAssoc (Fin (m + 1 - 1)) (Fin (m + 1 - 1)) (Fin 2))).symm
        (omMinusTorusGL (K := K) (m := m) (p := p) (ζ := ζ) hζ f)
    ((g : Matrix (LargeEvenMinusIdx (m + 1 - 1)) (LargeEvenMinusIdx (m + 1 - 1)) K) =
      Matrix.diagonal d) := by
  intro t d g
  dsimp only [g]
  rw [coe_glReindex_symm, omMinusTorusGL_apply, kOmMDiag_coe,
    Matrix.reindex_apply, Matrix.submatrix_diagonal_equiv]
  congr 1
  funext x
  rcases x with x | j
  · rcases x with i | i
    · simp [d, t, kOmMWeight, omMinusTorusParam_apply, Equiv.sumAssoc]
    · simp [d, t, kOmMWeight, omMinusTorusParam_apply, Equiv.sumAssoc]
  · fin_cases j <;> simp [d, t, kOmMWeight, omMinusTorusParam_apply, Equiv.sumAssoc]

private theorem reindex_mem_omegaMinus {K : Type} [Field K] [Finite K] [CharP K 2]
    {m : ℕ} {b c : K} (T : StatedOmega (StatedQuadMinus (m + 1) K b c)) :
    (glReindex K (Equiv.sumAssoc (Fin (m + 1 - 1)) (Fin (m + 1 - 1)) (Fin 2))).symm T.1 ∈
      LargeEvenOmega (LargeEvenQMinus (m + 1 - 1) b c) := by
  set e := Equiv.sumAssoc (Fin (m + 1 - 1)) (Fin (m + 1 - 1)) (Fin 2)
  have hmap := map_glReindex_commutator_orthogonalGroup (K := K) (e := e)
    (Q := LargeEvenQMinus (m + 1 - 1) b c) (Q' := StatedQuadMinus (m + 1) K b c)
    (quadMinus_eq_comp (m + 1) b c)
  have hmap' : (LargeEvenOmega (LargeEvenQMinus (m + 1 - 1) b c)).map
      (glReindex K e).toMonoidHom = StatedOmega (StatedQuadMinus (m + 1) K b c) := by
    rw [show LargeEvenOmega (LargeEvenQMinus (m + 1 - 1) b c) =
      ⁅PGLModel.orthogonalGroup (LargeEvenQMinus (m + 1 - 1) b c),
        PGLModel.orthogonalGroup (LargeEvenQMinus (m + 1 - 1) b c)⁆ from rfl]
    simpa using hmap
  have hT' : T.1 ∈ (LargeEvenOmega (LargeEvenQMinus (m + 1 - 1) b c)).map
      (glReindex K e).toMonoidHom := by
    rw [hmap']
    exact T.2
  obtain ⟨x, hx, hxT⟩ := Subgroup.mem_map.mp hT'
  simpa [← hxT] using hx

private theorem omegaMinusProjEquiv_mk {K : Type} [Field K] [Finite K] [CharP K 2]
    {m : ℕ} {b c : K} (h : LargeEvenOmega (LargeEvenQMinus (m + 1 - 1) b c)) :
    omegaMinusProjEquiv (m + 1) b c
      (LargeEvenProjMk (LargeEvenOmega (LargeEvenQMinus (m + 1 - 1) b c)) h) =
      (omegaModelMinusEquiv (m + 1) b c)
        ⟨Matrix.ProjGenLinGroup.mk h.1, Subgroup.mem_map_of_mem _ h.2⟩ := by
  change (omegaModelMinusEquiv (m + 1) b c)
    ((StatedAPI.mapMkEquivStatedProj
      (LargeEvenOmega (LargeEvenQMinus (m + 1 - 1) b c))).symm
      (LargeEvenProjMk (LargeEvenOmega (LargeEvenQMinus (m + 1 - 1) b c)) h)) = _
  rfl

private theorem rMinusEquivStatedOmega_symm_apply {K : Type} [Field K] [Finite K] [CharP K 2]
    (m : ℕ) (b c : K) (T : StatedOmega (StatedQuadMinus (m + 1) K b c)) :
    (rMinusEquivStatedOmega K m b c).symm T =
      LargeEvenProjMk (LargeEvenOmega (LargeEvenQMinus (m + 1 - 1) b c))
        ⟨(glReindex K (Equiv.sumAssoc (Fin (m + 1 - 1)) (Fin (m + 1 - 1)) (Fin 2))).symm T.1,
          reindex_mem_omegaMinus T⟩ := by
  set e := Equiv.sumAssoc (Fin (m + 1 - 1)) (Fin (m + 1 - 1)) (Fin 2)
  let h : LargeEvenOmega (LargeEvenQMinus (m + 1 - 1) b c) :=
    ⟨(glReindex K e).symm T.1, reindex_mem_omegaMinus T⟩
  apply (rMinusEquivStatedOmega K m b c).injective
  have hsymm : (rMinusEquivStatedOmega K m b c).toEquiv
      ((rMinusEquivStatedOmega K m b c).toEquiv.symm T) = T :=
    Equiv.apply_symm_apply _ T
  rw [show (rMinusEquivStatedOmega K m b c) ((rMinusEquivStatedOmega K m b c).symm T) = T
    from hsymm]
  unfold rMinusEquivStatedOmega
  rw [MulEquiv.trans_apply]
  symm
  rw [MulEquiv.symm_apply_eq (e := TableBOrth.projMkEquiv _)]
  rw [TableBOrth.projMkEquiv_apply]
  have hmem : Matrix.ProjGenLinGroup.mk h.1 ∈
      PGLModel.omegaModel (ComponentType.quadMinus (m + 1) b c) :=
    Subgroup.mem_map_of_mem _ h.2
  have hp1 : (StatedAPI.mapMkEquivStatedProj
      (LargeEvenOmega (LargeEvenQMinus (m + 1 - 1) b c))).symm
      (LargeEvenProjMk (LargeEvenOmega (LargeEvenQMinus (m + 1 - 1) b c)) h) =
      ⟨Matrix.ProjGenLinGroup.mk h.1, hmem⟩ := by
    ext
    exact StatedAPI.coe_mapMkEquivStatedProj_symm_mk _ h
  have hω' : (omegaModelMinusEquiv (m + 1) b c).symm
      (T : StatedProj (StatedOmega (StatedQuadMinus (m + 1) K b c))) =
      ⟨Matrix.ProjGenLinGroup.mk h.1, hmem⟩ := by
    apply Subtype.ext
    rw [coe_omegaModelMinusEquiv_symm_mk]
  have hω : omegaModelMinusEquiv (m + 1) b c
      ⟨Matrix.ProjGenLinGroup.mk h.1, hmem⟩ =
      (T : StatedProj (StatedOmega (StatedQuadMinus (m + 1) K b c))) := by
    rw [← hω', MulEquiv.apply_symm_apply]
  rw [omegaMinusProjEquiv_mk h]
  exact hω

private theorem torusImage_isMinusDiag {K : Type} [Field K] [Finite K] [CharP K 2]
    {m p : ℕ} [NeZero p] {b c : K} {ζ : Kˣ} (hζ : ζ ^ p = 1)
    (f : Fin m → Multiplicative (ZMod p)) :
    IsMinusDiag p
      (⟨(glReindex K (Equiv.sumAssoc (Fin (m + 1 - 1)) (Fin (m + 1 - 1)) (Fin 2))).symm
          (omMinusTorus (K := K) (m := m) (p := p) (b := b) (c := c) hζ f).1,
        reindex_mem_omegaMinus
          (omMinusTorus (K := K) (m := m) (p := p) (b := b) (c := c) hζ f)⟩ :
        LargeEvenOmega (LargeEvenQMinus (m + 1 - 1) b c)) := by
  set t : Fin m → Kˣ := fun i => TableBSymp.zmodPowHom hζ (f i)
  let d : LargeEvenMinusIdx (m + 1 - 1) → K :=
    Sum.elim (Sum.elim (fun i => (t i : K)) (fun i => ((t i)⁻¹ : K))) (fun _ => 1)
  have ht : ∀ i, t i ^ p = 1 := by
    intro i
    rw [show t i = TableBSymp.zmodPowHom hζ (f i) from rfl, TableBSymp.zmodPowHom_apply,
      ← pow_mul, mul_comm, pow_mul, hζ, one_pow]
  refine ⟨d, ?_, ?_, ?_⟩
  · intro x
    dsimp only [d]
    rcases x with x | j
    · rcases x with i | i
      · have h := congrArg (fun u : Kˣ => (u : K)) (ht i)
        simpa only [Sum.elim_inl, Units.val_pow_eq_pow_val, Units.val_one] using h
      · have h := congrArg (fun u : Kˣ => (u : K)) (ht i)
        rw [Sum.elim_inl, Sum.elim_inr, inv_pow, ← Units.val_pow_eq_pow_val, h]
        simp
    · fin_cases j <;> simp [Sum.elim_inr]
  · intro j
    rfl
  · exact coe_glReindex_symm_omMinusTorusGL hζ f

private theorem phi_apply_eq_pow {K : Type} [Field K] [Finite K] [CharP K 2]
    {m p k : ℕ} {b c : K}
    {φ : MulAut (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c)))}
    (hφ : LargeEvenGraphAut (LargeEvenProjMk (LargeEvenOmega (LargeEvenQMinus m b c)))
      (fun h h' : LargeEvenOmega (LargeEvenQMinus m b c) =>
        ((h' : GL (LargeEvenMinusIdx m) K) :
            Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K) *
          LargeEvenFrobBlock m b c k =
        LargeEvenFrobBlock m b c k *
          (((h : GL (LargeEvenMinusIdx m) K) :
            Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K).map (· ^ 2 ^ k)))
      φ)
    {h : LargeEvenOmega (LargeEvenQMinus m b c)} (hh : IsMinusDiag p h) :
    φ (LargeEvenProjMk (LargeEvenOmega (LargeEvenQMinus m b c)) h) =
      (LargeEvenProjMk (LargeEvenOmega (LargeEvenQMinus m b c)) h) ^ 2 ^ k := by
  obtain ⟨d, -, hd1, hmat⟩ := hh
  let h' : LargeEvenOmega (LargeEvenQMinus m b c) := h ^ 2 ^ k
  have hmat' : (((h' : GL (LargeEvenMinusIdx m) K)) :
      Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K) =
      Matrix.diagonal (fun x => d x ^ 2 ^ k) := by
    have h1 : (h' : GL (LargeEvenMinusIdx m) K) = (h : GL (LargeEvenMinusIdx m) K) ^ 2 ^ k :=
      Subgroup.coe_pow (LargeEvenOmega (LargeEvenQMinus m b c)) h (2 ^ k)
    rw [h1, Units.val_pow_eq_pow_val, hmat, Matrix.diagonal_pow]
    rfl
  have hmap : (((h : GL (LargeEvenMinusIdx m) K)) :
      Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K).map (· ^ 2 ^ k) =
      Matrix.diagonal (fun x => d x ^ 2 ^ k) := by
    rw [hmat, Matrix.diagonal_map (by simp)]
  have hrel : ((h' : GL (LargeEvenMinusIdx m) K) :
        Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K) *
        LargeEvenFrobBlock m b c k =
      LargeEvenFrobBlock m b c k *
        (((h : GL (LargeEvenMinusIdx m) K) :
          Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K).map (· ^ 2 ^ k)) := by
    rw [hmat', hmap]
    exact frobBlock_commute_diagonal hd1 k
  calc φ (LargeEvenProjMk (LargeEvenOmega (LargeEvenQMinus m b c)) h)
      = LargeEvenProjMk (LargeEvenOmega (LargeEvenQMinus m b c)) h' := hφ h h' hrel
    _ = LargeEvenProjMk (LargeEvenOmega (LargeEvenQMinus m b c)) (h ^ 2 ^ k) := rfl
    _ = (LargeEvenProjMk (LargeEvenOmega (LargeEvenQMinus m b c)) h) ^ 2 ^ k := by
        rw [map_pow]

private theorem exists_phi_of_mem_closure {K : Type} [Field K] [Finite K] [CharP K 2]
    {m : ℕ} {b c : K}
    {g : MulAut (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c)))}
    (hm : 3 ≤ m) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hg : g ∈ Subgroup.closure (LargeEvenPhiQ m b c
      (LargeEvenProjMk (LargeEvenOmega (LargeEvenQMinus m b c))))) :
    ∃ k : ℕ, LargeEvenGraphAut (LargeEvenProjMk (LargeEvenOmega (LargeEvenQMinus m b c)))
      (fun h h' : LargeEvenOmega (LargeEvenQMinus m b c) =>
        ((h' : GL (LargeEvenMinusIdx m) K) :
            Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K) *
          LargeEvenFrobBlock m b c k =
        LargeEvenFrobBlock m b c k *
          (((h : GL (LargeEvenMinusIdx m) K) :
            Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K).map (· ^ 2 ^ k)))
      g := by
  classical
  set τ := AutOm.frobAut (n := m + 1) (b := b) (c := c) (Nat.succ_le_succ hm) hirr
  have hτg : MulAut.congr (RecipeFieldOmega.minusEquiv (n := m + 1) (b := b) (c := c)
      (Nat.succ_le_succ hm)) g ∈ Subgroup.zpowers τ :=
    RecipeFieldOmega.congr_minusEquiv_of_mem_closure (n := m + 1) (Nat.succ_le_succ hm) hirr hg
  have hz' : MulAut.congr (RecipeFieldOmega.minusEquiv (n := m + 1) (b := b) (c := c)
      (Nat.succ_le_succ hm)) g ∈ (Finset.range (orderOf τ)).image (fun k => τ ^ k) :=
    (mem_zpowers_iff_mem_range_orderOf (x := τ)).mp hτg
  obtain ⟨k, -, hk⟩ := Finset.mem_image.mp hz'
  refine ⟨k, ?_⟩
  have hg_eq : g = (MulAut.congr (RecipeFieldOmega.minusEquiv (n := m + 1) (b := b) (c := c)
      (Nat.succ_le_succ hm))).symm (τ ^ k) := by
    rw [hk, MulEquiv.symm_apply_apply]
  rw [hg_eq]
  exact RecipeFieldOmega.graphAut_frobAut_pow (n := m + 1) (Nat.succ_le_succ hm) hirr k

private theorem action_of_mem_closure {K : Type} [Field K] [Finite K] [CharP K 2]
    {m p : ℕ} [NeZero p] {b c : K} {ζ : Kˣ} (hζ : ζ ^ p = 1)
    (hm : 3 ≤ m) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {g : MulAut (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c)))}
    (hg : g ∈ Subgroup.closure (LargeEvenPhiQ m b c
      (LargeEvenProjMk (LargeEvenOmega (LargeEvenQMinus m b c))))) :
    ∃ k : ℕ, ∀ v ∈ torusImage K m p hζ, g v = v ^ 2 ^ k := by
  obtain ⟨k, hgraph⟩ := exists_phi_of_mem_closure hm hirr hg
  refine ⟨k, fun v hv => ?_⟩
  obtain ⟨T, hT, rfl⟩ := hv
  obtain ⟨f, rfl⟩ := MonoidHom.mem_range.mp hT
  let h : LargeEvenOmega (LargeEvenQMinus (m + 1 - 1) b c) :=
    ⟨(glReindex K (Equiv.sumAssoc (Fin (m + 1 - 1)) (Fin (m + 1 - 1)) (Fin 2))).symm
        (omMinusTorus (K := K) (m := m) (p := p) (b := b) (c := c) hζ f).1,
      reindex_mem_omegaMinus
        (omMinusTorus (K := K) (m := m) (p := p) (b := b) (c := c) hζ f)⟩
  have hv_eq : (rMinusEquivStatedOmega K m b c).symm
      (omMinusTorus (K := K) (m := m) (p := p) (b := b) (c := c) hζ f) =
      LargeEvenProjMk (LargeEvenOmega (LargeEvenQMinus (m + 1 - 1) b c)) h :=
    rMinusEquivStatedOmega_symm_apply m b c
      (omMinusTorus (K := K) (m := m) (p := p) (b := b) (c := c) hζ f)
  have hdiag : IsMinusDiag p h := torusImage_isMinusDiag hζ f
  rw [hv_eq]
  exact phi_apply_eq_pow hgraph hdiag

private theorem pow_p_eq_one_of_mem_torusImage {K : Type} [Field K] [Finite K] [CharP K 2]
    {m p : ℕ} [NeZero p] {b c : K} {ζ : Kˣ} (hζ : ζ ^ p = 1)
    {v : LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c))}
    (hv : v ∈ torusImage K m p hζ) : v ^ p = 1 := by
  obtain ⟨T, hT, rfl⟩ := hv
  obtain ⟨f, rfl⟩ := MonoidHom.mem_range.mp hT
  let h : LargeEvenOmega (LargeEvenQMinus (m + 1 - 1) b c) :=
    ⟨(glReindex K (Equiv.sumAssoc (Fin (m + 1 - 1)) (Fin (m + 1 - 1)) (Fin 2))).symm
        (omMinusTorus (K := K) (m := m) (p := p) (b := b) (c := c) hζ f).1,
      reindex_mem_omegaMinus
        (omMinusTorus (K := K) (m := m) (p := p) (b := b) (c := c) hζ f)⟩
  have hv_eq : (rMinusEquivStatedOmega K m b c).symm
      (omMinusTorus (K := K) (m := m) (p := p) (b := b) (c := c) hζ f) =
      LargeEvenProjMk (LargeEvenOmega (LargeEvenQMinus (m + 1 - 1) b c)) h :=
    rMinusEquivStatedOmega_symm_apply m b c
      (omMinusTorus (K := K) (m := m) (p := p) (b := b) (c := c) hζ f)
  have hdiag : IsMinusDiag p h := torusImage_isMinusDiag hζ f
  rw [hv_eq, ← map_pow, pow_eq_one_of_isMinusDiag hdiag, map_one]

private theorem orderOf_two_dvd_of_dvd_mul {p n j e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpn : p ∣ 2 ^ n - 1) (hdiv : 2 * n ∣ p ^ e * j) :
    orderOf (2 : ZMod p) ∣ j := by
  have : Fact p.Prime := ⟨hp⟩
  have h20 : (2 : ZMod p) ≠ 0 := by
    have h : ((2 : ℕ) : ZMod p) ≠ 0 := by
      intro h
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
        ((ZMod.natCast_eq_zero_iff 2 p).mp h))
    simpa using h
  have h2n : (2 : ZMod p) ^ n = 1 := by
    show ((2 : ℕ) : ZMod p) ^ n = 1
    rw [← Nat.cast_pow, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff]
    exact ((Nat.modEq_iff_dvd' (Nat.one_le_two_pow)).mpr hpn).symm
  have hdn : orderOf (2 : ZMod p) ∣ n := orderOf_dvd_iff_pow_eq_one.mpr h2n
  have hdp : orderOf (2 : ZMod p) ∣ p - 1 := ZMod.orderOf_dvd_card_sub_one h20
  have hcop' : Nat.Coprime p (orderOf (2 : ZMod p)) := by
    rw [hp.coprime_iff_not_dvd]
    intro hpd
    have hpd1 : p ∣ p - 1 := dvd_trans hpd hdp
    have hp1 : 1 ≤ p - 1 := by have := hp.two_le; omega
    have hle : p ≤ p - 1 := Nat.le_of_dvd hp1 hpd1
    omega
  have hcop : Nat.Coprime (orderOf (2 : ZMod p)) p := hcop'.symm
  have hnd : orderOf (2 : ZMod p) ∣ p ^ e * j :=
    dvd_trans hdn (dvd_trans (dvd_mul_left n 2) hdiv)
  exact (hcop.pow_right e).dvd_of_dvd_mul_left hnd

private theorem pow_two_pow_sub_one_dvd {p : ℕ} [Fact p.Prime] {s j : ℕ}
    (hdj : orderOf (2 : ZMod p) ∣ s * j) : p ∣ 2 ^ (s * j) - 1 := by
  have hpow : (2 : ZMod p) ^ (s * j) = 1 := orderOf_dvd_iff_pow_eq_one.mp hdj
  have hnat : ((2 ^ (s * j) : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
    rw [Nat.cast_pow, Nat.cast_one]
    exact hpow
  have hmod : 2 ^ (s * j) ≡ 1 [MOD p] :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mp hnat
  exact (Nat.modEq_iff_dvd' Nat.one_le_two_pow).mp hmod.symm

private theorem pow_apply_eq_self {K : Type} [Field K] [Finite K] [CharP K 2]
    {m p : ℕ} [NeZero p] [Fact p.Prime] {b c : K} {ζ : Kˣ} (hζ : ζ ^ p = 1)
    (hm : 3 ≤ m) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {g : MulAut (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c)))}
    (hg : g ∈ Subgroup.closure (LargeEvenPhiQ m b c
      (LargeEvenProjMk (LargeEvenOmega (LargeEvenQMinus m b c)))))
    {j : ℕ} (hdj : orderOf (2 : ZMod p) ∣ j)
    {v : LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c))}
    (hv : v ∈ torusImage K m p hζ) : (g ^ j) v = v := by
  let V : Set (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c))) :=
    torusImage K m p hζ
  have hvV : v ∈ V := hv
  obtain ⟨s, hs⟩ := action_of_mem_closure hζ hm hirr hg
  have hVpow : ∀ v ∈ V, ∀ t : ℕ, v ^ t ∈ V := by
    rintro v ⟨T, hT, rfl⟩ t
    exact ⟨T ^ t, Subgroup.pow_mem _ hT t, by rw [map_pow]⟩
  have hiter : ∀ j : ℕ, ∀ v ∈ V, (g ^ j) v = v ^ (2 ^ s) ^ j := by
    intro j
    induction j with
    | zero => intro v hv; simp
    | succ j ih =>
      intro v hv
      rw [pow_succ, MulAut.mul_apply]
      have hv' : g v ∈ V := by
        rw [hs v hv]
        exact hVpow v hv (2 ^ s)
      rw [ih (g v) hv', hs v hv, ← pow_mul, pow_succ']
  have hvpow : v ^ p = 1 := pow_p_eq_one_of_mem_torusImage hζ hvV
  have hmod : p ∣ 2 ^ (s * j) - 1 :=
    pow_two_pow_sub_one_dvd (dvd_mul_of_dvd_right hdj s)
  obtain ⟨t, ht⟩ := hmod
  have h1 : 1 ≤ 2 ^ (s * j) := Nat.one_le_two_pow
  have hexp : 2 ^ (s * j) = 1 + p * t := by omega
  rw [hiter j v hvV, show (2 ^ s) ^ j = 2 ^ (s * j) from (pow_mul (2 : ℕ) s j).symm, hexp,
    pow_add, pow_mul, hvpow]
  simp

private theorem omegaMinus_hA {K : Type} [Field K] [Finite K] [CharP K 2] {m n p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card K = 2 ^ n) (hm : 3 ≤ m)
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hn1 : 1 ≤ n)
    (hpn : p ∣ 2 ^ n - 1) {ζ : Kˣ} (hζ : ζ ^ p = 1) :
    ∀ a : MulAut (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c))),
      (∃ k : ℕ, a ^ p ^ k = 1) →
      ∃ (ρ₁ : LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c)))
        (φ : MulAut (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c)))),
        a = MulAut.conj ρ₁ * φ ∧ ∀ v ∈ torusImage (b := b) (c := c) K m p hζ, φ v = v := by
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  intro a ha
  obtain ⟨k, hk⟩ := ha
  obtain ⟨u, hu, g, hg, haeq⟩ :=
    RawAutOmega.exists_inner_mul_field_omegaMinus (n := m + 1) (Nat.succ_le_succ hm) hirr
      (f := n) hK a
  have hn0 : 2 * n ≠ 0 := by omega
  obtain ⟨ρ, j, e, hdiv, haj⟩ :=
    CFSG.exists_eq_conj_mul_pow_of_eq_mul (G := LargeEvenProj (LargeEvenOmega
      (LargeEvenQMinus m b c))) (p := p) (n := 2 * n) (k := k) hp hn0 hu hk haeq
  have hdj : orderOf (2 : ZMod p) ∣ j :=
    orderOf_two_dvd_of_dvd_mul hp hp2 hpn hdiv
  exact ⟨ρ, g ^ j, haj, fun v hv => pow_apply_eq_self hζ hm hirr hg hdj hv⟩

private theorem omegaMinus_hfix {K : Type} [Field K] [Finite K] [CharP K 2] {m n p : ℕ}
    [NeZero m] (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = 2 ^ n) (hm : 3 ≤ m)
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hn1 : 1 ≤ n) (hpn : p ∣ 2 ^ n - 1)
    {ζ : Kˣ} (hζ : ζ ^ p = 1) (hζo : orderOf ζ = p) :
    ∀ E' : Subgroup (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c))),
      IsElemAbelian p E' → p ^ m ≤ Nat.card E' →
      ∀ a : MulAut (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c))),
        (∃ k : ℕ, a ^ p ^ k = 1) →
        ∃ ρ : LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c)),
          ∀ x ∈ E', ((MulAut.conj ρ)⁻¹ * a) x = x := by
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  intro E' hE' hcardE a ha
  exact CoverPToral.forall_fix_of_toral (torusImage (b := b) (c := c) K m p hζ)
    (fun E' hE' hc => CoverPToral.exists_mulAut_mapsTo_of_mulEquiv
      (rMinusEquivStatedOmega K m b c)
      (fun E hE hc' => exists_mulEquiv_eq_map_omMinusTorus hp2 hirr hζ hζo hE hc') hE' hc)
    (omegaMinus_hA hp hp2 hK hm hirr hn1 hpn hζ) hE' hcardE ha

theorem ggCoverPTableB_omegaMinus {K : Type} [Field K] [Finite K] {r n p : ℕ}
    (hK : Nat.card K = 2 ^ n) (hr : 4 ≤ r) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hp : p.Prime) (hpn : p ∣ 2 ^ n - 1) :
    GGCoverPTableB p (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (r - 1) b c)))
      (LargeEvenInnSet (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (r - 1) b c)))) := by
  let m := r - 1
  change GGCoverPTableB p (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c)))
    (LargeEvenInnSet (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c))))
  have hn1 : 1 ≤ n := CFSG.SeitzReduction.one_le_of_nontrivial_of_natCard_eq_two_pow hK
  have hp2 : p ≠ 2 := ne_two_of_dvd_two_pow_sub_one' hn1 hpn
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K 2 := charP_two_of_card hK
  have : NeZero p := ⟨hp.ne_zero⟩
  have hm : 3 ≤ m := by omega
  have hpq : p ∣ Nat.card K - 1 := by rw [hK]; exact hpn
  obtain ⟨ζ, hζo⟩ : ∃ ζ : Kˣ, orderOf ζ = p :=
    exists_prime_orderOf_dvd_card' p (by rw [Nat.card_units]; exact hpq)
  have hζ : ζ ^ p = 1 := by rw [← hζo]; exact pow_orderOf_eq_one ζ
  have : NeZero m := ⟨by omega⟩
  have hZ : Subgroup.center (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c))) = ⊥ :=
    TableBOrth.center_omegaMinus_eq_bot hp hp2 hpq hm hirr
  have hI : ∀ φ ∈ LargeEvenInnSet (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c))),
      φ ∈ (MulAut.conj : LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c)) →*
        MulAut _).range :=
    fun φ hφ => hφ
  have hcard : ∀ {M : Type} [Group M] [Finite M] {L' E : Subgroup M}
      {θ : L' ⧸ Subgroup.center L' ≃* LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c))}
      {hE : E ≤ Subgroup.normalizer (L' : Set M)},
      GGTableBPosition p L' E
        (LargeEvenInnSet (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c)))) θ hE →
        p ^ m ≤ Nat.card (ggLAutImage L' θ E) := by
    intro M _ _ L' E θ hE hP
    exact pow_le_card_ggLAutImage hP hp
      (TableBSymp.ggTorusLift_omegaMinus hp hp2 hpq hm b c)
  have hfix := omegaMinus_hfix hp hp2 hK hm hirr hn1 hpn hζ hζo
  exact CoverPToral.ggCoverPTableB_of_forall_fix (r := m) hZ hI hcard hfix

theorem largeEvenLabelAll_coverP_omegaMinus {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (ht : lab.tag = .twD) (h4 : 4 ≤ lab.rank) (hpn : p ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab fun R _ I _ => GGCoverPTableB p R I := by
  refine largeEvenLabelAll_omegaMinus ht h4 fun K _ _ _ hK b c hirr => ?_
  exact ggCoverPTableB_omegaMinus (n := lab.n) hK h4 hirr hp hpn

end CoverPOmMinus

end CFSG.StandardType

end
