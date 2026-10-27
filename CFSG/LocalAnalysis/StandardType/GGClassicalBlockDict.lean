module

public import CFSG.LocalAnalysis.StandardType.GGClassicalBlockDefs
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Eigenspace.Zero
public import Mathlib.RingTheory.Adjoin.PowerBasis
public import TauCeti.LinearAlgebra.Eigenspace.Semisimple
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockDecomp
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockDegreeParity
public import TauCeti.LinearAlgebra.End.FiniteOrder
public import TauCeti.LinearAlgebra.Dimension.DirectSum
public import TauCeti.FieldTheory.GaloisGroups.Stabilizer
public import TauCeti.InformationTheory.Coding.Semilinear.Basic
public import Mathlib.RingTheory.Artinian.Ring

public section

namespace CFSG.StandardType.ClassicalBlocks

open CFSG CFSG.StandardType CFSG.StandardType.ClassicalPosition Matrix

private theorem ggJSf2a_finrank_biSup_eq_sum {K M ι : Type*} [Field K] [AddCommGroup M]
    [Module K M] [FiniteDimensional K M] [DecidableEq ι] {S : ι → Submodule K M}
    (hS : iSupIndep S) (s : Finset ι) :
    Module.finrank K (⨆ i ∈ s, S i : Submodule K M) = ∑ i ∈ s, Module.finrank K (S i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hdis : Disjoint (S a) (⨆ i ∈ s, S i) := hS.disjoint_biSup (by simpa using ha)
    have h := Submodule.finrank_sup_add_finrank_inf_eq (S a) (⨆ i ∈ s, S i)
    rw [hdis.eq_bot, finrank_bot, add_zero] at h
    rw [Finset.iSup_insert, Finset.sum_insert ha, ← ih]
    exact h

theorem eigDim_eq_sum_eigDimOn {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    {b : Matrix ι ι K} {P : Finset (Matrix ι ι K)}
    (hP : ∀ ε ∈ P, IsIdempotentElem ε ∧ Commute b ε)
    (horth : ∀ ε ∈ P, ∀ ε' ∈ P, ε ≠ ε' → ε * ε' = 0) (hsum : ∑ ε ∈ P, ε = 1)
    (l : AlgebraicClosure K) :
    eigDim b l = ∑ ε ∈ P, eigDimOn b ε l := by
  classical
  let k := AlgebraicClosure K
  let φ : K →+* k := algebraMap K k
  let T : Module.End k (ι → k) := Matrix.toLin' (b.map φ)
  let E : Submodule k (ι → k) := Module.End.eigenspace T l
  let Pπ : Matrix ι ι K → Module.End k (ι → k) := fun ε => Matrix.toLin' (ε.map φ)
  let S : Matrix ι ι K → Submodule k (ι → k) :=
    fun ε => if ε ∈ P then E ⊓ LinearMap.range (Pπ ε) else ⊥
  have hidem : ∀ ε ∈ P, Pπ ε * Pπ ε = Pπ ε := by
    intro ε hε
    have hεε : ε * ε = ε := (hP ε hε).1.eq
    show Matrix.toLin' (ε.map φ) * Matrix.toLin' (ε.map φ) = Matrix.toLin' (ε.map φ)
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, ← Matrix.map_mul, hεε]
  have horthπ : ∀ ε ∈ P, ∀ ε' ∈ P, ε ≠ ε' → Pπ ε * Pπ ε' = 0 := by
    intro ε hε ε' hε' hne
    have h0 : ε * ε' = 0 := horth ε hε ε' hε' hne
    show Matrix.toLin' (ε.map φ) * Matrix.toLin' (ε'.map φ) = 0
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, ← Matrix.map_mul, h0]
    simp
  have hcomm : ∀ ε ∈ P, T * Pπ ε = Pπ ε * T := by
    intro ε hε
    have hb : (b.map φ) * (ε.map φ) = (ε.map φ) * (b.map φ) := by
      rw [← Matrix.map_mul, (hP ε hε).2.eq, Matrix.map_mul]
    show Matrix.toLin' (b.map φ) * Matrix.toLin' (ε.map φ) =
      Matrix.toLin' (ε.map φ) * Matrix.toLin' (b.map φ)
    rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← Matrix.toLin'_mul,
      ← Matrix.toLin'_mul, hb]
  have hsumP : ∑ ε ∈ P, Pπ ε = 1 := by
    have hmap : ∑ ε ∈ P, ε.map φ = 1 := by
      have h2 := map_sum (RingHom.mapMatrix φ) (fun ε : Matrix ι ι K => ε) P
      rw [hsum, map_one] at h2
      simpa only [RingHom.mapMatrix_apply] using h2.symm
    have h := map_sum (Matrix.toLin') (fun ε : Matrix ι ι K => ε.map φ) P
    rw [hmap, Matrix.toLin'_one] at h
    change (∑ ε ∈ P, Matrix.toLin' (ε.map φ)) = (1 : Module.End k (ι → k))
    exact h.symm
  have hS : iSupIndep S := by
    rw [iSupIndep_iff_finset_sum_eq_imp_eq]
    intro s v w hv hw j hj
    by_cases hjP : j ∈ P
    · have hvj : Pπ j (v j) = v j := by
        have hmem : v j ∈ LinearMap.range (Pπ j) := by
          have h := (hv j hj).1
          rw [show S j = E ⊓ LinearMap.range (Pπ j) from if_pos hjP] at h
          exact h.2
        obtain ⟨u, hu⟩ := LinearMap.mem_range.mp hmem
        rw [← hu, ← Module.End.mul_apply, hidem j hjP]
      have hwj : Pπ j (w j) = w j := by
        have hmem : w j ∈ LinearMap.range (Pπ j) := by
          have h := (hv j hj).2
          rw [show S j = E ⊓ LinearMap.range (Pπ j) from if_pos hjP] at h
          exact h.2
        obtain ⟨u, hu⟩ := LinearMap.mem_range.mp hmem
        rw [← hu, ← Module.End.mul_apply, hidem j hjP]
      have h1 : Pπ j (∑ i ∈ s, v i) = v j := by
        rw [map_sum, Finset.sum_eq_single j]
        · exact hvj
        · intro i hi hij
          by_cases hiP : i ∈ P
          · have hmem : v i ∈ LinearMap.range (Pπ i) := by
              have h := (hv i hi).1
              rw [show S i = E ⊓ LinearMap.range (Pπ i) from if_pos hiP] at h
              exact h.2
            obtain ⟨u, hu⟩ := LinearMap.mem_range.mp hmem
            rw [← hu, ← Module.End.mul_apply, horthπ j hjP i hiP (Ne.symm hij)]
            simp
          · have h0 : v i = 0 := by
              have h := (hv i hi).1
              rw [show S i = ⊥ from if_neg hiP] at h
              simpa using h
            rw [h0, map_zero]
        · intro hjnot
          exact absurd hj hjnot
      have h2 : Pπ j (∑ i ∈ s, w i) = w j := by
        rw [map_sum, Finset.sum_eq_single j]
        · exact hwj
        · intro i hi hij
          by_cases hiP : i ∈ P
          · have hmem : w i ∈ LinearMap.range (Pπ i) := by
              have h := (hv i hi).2
              rw [show S i = E ⊓ LinearMap.range (Pπ i) from if_pos hiP] at h
              exact h.2
            obtain ⟨u, hu⟩ := LinearMap.mem_range.mp hmem
            rw [← hu, ← Module.End.mul_apply, horthπ j hjP i hiP (Ne.symm hij)]
            simp
          · have h0 : w i = 0 := by
              have h := (hv i hi).2
              rw [show S i = ⊥ from if_neg hiP] at h
              simpa using h
            rw [h0, map_zero]
        · intro hjnot
          exact absurd hj hjnot
      rw [hw] at h1
      rw [h1] at h2
      exact h2
    · have hv0 : v j = 0 := by
        have h := (hv j hj).1
        rw [show S j = ⊥ from if_neg hjP] at h
        simpa using h
      have hw0 : w j = 0 := by
        have h := (hv j hj).2
        rw [show S j = ⊥ from if_neg hjP] at h
        simpa using h
      rw [hv0, hw0]
  have hS_eq : (⨆ ε ∈ P, E ⊓ LinearMap.range (Pπ ε)) = ⨆ ε ∈ P, S ε := by
    apply le_antisymm
    · apply iSup_le; intro ε; apply iSup_le; intro hε
      rw [show E ⊓ LinearMap.range (Pπ ε) = S ε from (if_pos hε).symm]
      exact le_iSup_of_le ε (le_iSup_of_le hε le_rfl)
    · apply iSup_le; intro ε; apply iSup_le; intro hε
      rw [show S ε = E ⊓ LinearMap.range (Pπ ε) from if_pos hε]
      exact le_iSup_of_le ε (le_iSup_of_le hε le_rfl)
  have hsup : E = ⨆ ε ∈ P, E ⊓ LinearMap.range (Pπ ε) := by
    apply le_antisymm
    · intro v hv
      have hmem : ∀ ε, ε ∈ P → Pπ ε v ∈ E ⊓ LinearMap.range (Pπ ε) := by
        intro ε hε
        refine ⟨?_, ⟨v, rfl⟩⟩
        refine Module.End.mem_eigenspace_iff.mpr ?_
        have hv' : T v = l • v := Module.End.mem_eigenspace_iff.mp hv
        calc T (Pπ ε v) = (T * Pπ ε) v := (Module.End.mul_apply T (Pπ ε) v).symm
          _ = (Pπ ε * T) v := by rw [hcomm ε hε]
          _ = Pπ ε (T v) := Module.End.mul_apply (Pπ ε) T v
          _ = Pπ ε (l • v) := by rw [hv']
          _ = l • Pπ ε v := (Pπ ε).map_smul l v
      have hvsum : v = ∑ ε ∈ P, Pπ ε v := by
        have h := congrArg (fun f : Module.End k (ι → k) => f v) hsumP
        simpa [LinearMap.sum_apply] using h.symm
      rw [hvsum]
      exact Submodule.sum_mem _ (fun ε hε =>
        Submodule.mem_iSup_of_mem ε (Submodule.mem_iSup_of_mem hε (hmem ε hε)))
    · exact iSup_le (fun ε => iSup_le (fun _ => inf_le_left))
  have hsum_eq : (∑ ε ∈ P, Module.finrank k (S ε)) = ∑ ε ∈ P, eigDimOn b ε l := by
    apply Finset.sum_congr rfl
    intro ε hε
    rw [show S ε = E ⊓ LinearMap.range (Pπ ε) from if_pos hε]
    rfl
  have hfin := ggJSf2a_finrank_biSup_eq_sum (S := S) hS P
  calc eigDim b l = Module.finrank k E := rfl
    _ = Module.finrank k (⨆ ε ∈ P, E ⊓ LinearMap.range (Pπ ε) : Submodule k (ι → k)) :=
        congrArg (fun X : Submodule k (ι → k) => Module.finrank k X) hsup
    _ = Module.finrank k (⨆ ε ∈ P, S ε : Submodule k (ι → k)) :=
        congrArg (fun X : Submodule k (ι → k) => Module.finrank k X) hS_eq
    _ = ∑ ε ∈ P, Module.finrank k (S ε) := hfin
    _ = ∑ ε ∈ P, eigDimOn b ε l := hsum_eq

private theorem ggJSf2a_scalar_action {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    {b : GL ι K} {a : Matrix ι ι K}
    (ha : a ∈ Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) (l : AlgebraicClosure K) :
    ∃ c : AlgebraicClosure K, ∀ v : ι → AlgebraicClosure K,
      v ∈ Module.End.eigenspace
          (Matrix.toLin' (((b : Matrix ι ι K)).map (algebraMap K (AlgebraicClosure K)))) l →
        Matrix.toLin' (a.map (algebraMap K (AlgebraicClosure K))) v = c • v := by
  classical
  let k := AlgebraicClosure K
  let φ : K →+* k := algebraMap K k
  let T : Module.End k (ι → k) := Matrix.toLin' (((b : Matrix ι ι K)).map φ)
  let E : Submodule k (ι → k) := Module.End.eigenspace T l
  have key : ∀ x ∈ Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K))),
      ∃ c : k, ∀ v, v ∈ E → Matrix.toLin' (x.map φ) v = c • v := by
    intro x hx
    refine Algebra.adjoin_induction (p := fun x _ => ∃ c : k, ∀ v, v ∈ E →
        Matrix.toLin' (x.map φ) v = c • v) ?_ ?_ ?_ ?_ hx
    · rintro x ⟨s, hs, rfl⟩
      rw [Set.mem_singleton_iff] at hs
      subst s
      exact ⟨l, fun v hv => Module.End.mem_eigenspace_iff.mp hv⟩
    · intro r
      refine ⟨φ r, fun v hv => ?_⟩
      have hx1 : (algebraMap K (Matrix ι ι K) r).map φ = φ r • (1 : Matrix ι ι k) := by
        rw [Algebra.algebraMap_eq_smul_one,
          Matrix.map_smul' φ r (1 : Matrix ι ι K) (fun a b => map_mul φ a b),
          Matrix.map_one φ (map_zero φ) (map_one φ)]
      rw [hx1, map_smul, Matrix.toLin'_one]
      rfl
    · intro x y hx hy hpx hpy
      obtain ⟨c, hc⟩ := hpx
      obtain ⟨d, hd⟩ := hpy
      refine ⟨c + d, fun v hv => ?_⟩
      rw [Matrix.map_add φ (map_add φ) x y, map_add, LinearMap.add_apply, hc v hv, hd v hv,
        add_smul]
    · intro x y hx hy hpx hpy
      obtain ⟨c, hc⟩ := hpx
      obtain ⟨d, hd⟩ := hpy
      refine ⟨d * c, fun v hv => ?_⟩
      rw [Matrix.map_mul, Matrix.toLin'_mul, LinearMap.comp_apply, hd v hv, map_smul,
        hc v hv, ← smul_smul]
  exact key a ha

theorem eigDimOn_eq_zero_or_of_mul_eq_zero {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    {b : GL ι K} {e e' : Matrix ι ι K}
    (he : IsPrimIdemIn (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) e)
    (he' : IsPrimIdemIn (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) e')
    (hee' : e * e' = 0) (l : AlgebraicClosure K) :
    eigDimOn (b : Matrix ι ι K) e l = 0 ∨ eigDimOn (b : Matrix ι ι K) e' l = 0 := by
  classical
  let k := AlgebraicClosure K
  let φ : K →+* k := algebraMap K k
  let T : Module.End k (ι → k) := Matrix.toLin' (((b : Matrix ι ι K)).map φ)
  let πe : Module.End k (ι → k) := Matrix.toLin' (e.map φ)
  let πe' : Module.End k (ι → k) := Matrix.toLin' (e'.map φ)
  have hidem : πe * πe = πe := by
    show Matrix.toLin' (e.map φ) * Matrix.toLin' (e.map φ) = Matrix.toLin' (e.map φ)
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, ← Matrix.map_mul, he.2.1.eq]
  have hidem' : πe' * πe' = πe' := by
    show Matrix.toLin' (e'.map φ) * Matrix.toLin' (e'.map φ) = Matrix.toLin' (e'.map φ)
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, ← Matrix.map_mul, he'.2.1.eq]
  have hzero : πe * πe' = 0 := by
    show Matrix.toLin' (e.map φ) * Matrix.toLin' (e'.map φ) = 0
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, ← Matrix.map_mul, hee']
    simp
  by_contra h
  push Not at h
  obtain ⟨hne, hne'⟩ := h
  have hVne : Module.End.eigenspace T l ⊓ LinearMap.range πe ≠ ⊥ := by
    intro hbot
    exact hne (by
      change Module.finrank k
        (Module.End.eigenspace T l ⊓ LinearMap.range πe : Submodule k (ι → k)) = 0
      rw [hbot, finrank_bot])
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp hVne
  have hvE : v ∈ Module.End.eigenspace T l := hv.1
  have hvR : v ∈ LinearMap.range πe := hv.2
  have hvfix : πe v = v := by
    obtain ⟨u, hu⟩ := LinearMap.mem_range.mp hvR
    rw [← hu, ← Module.End.mul_apply, hidem]
  obtain ⟨c, hc⟩ := ggJSf2a_scalar_action he.1 l
  have hc1 : c = 1 := by
    have h1 : πe v = c • v := hc v hvE
    rw [hvfix] at h1
    have h2 : (c - 1) • v = 0 := by rw [sub_smul, one_smul, ← h1, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero_iff_left hv0).mp h2)
  have hVne' : Module.End.eigenspace T l ⊓ LinearMap.range πe' ≠ ⊥ := by
    intro hbot
    exact hne' (by
      change Module.finrank k
        (Module.End.eigenspace T l ⊓ LinearMap.range πe' : Submodule k (ι → k)) = 0
      rw [hbot, finrank_bot])
  obtain ⟨v', hv', hv0'⟩ := (Submodule.ne_bot_iff _).mp hVne'
  have hv'E : v' ∈ Module.End.eigenspace T l := hv'.1
  have hv'R : v' ∈ LinearMap.range πe' := hv'.2
  have hv'fix : πe' v' = v' := by
    obtain ⟨u, hu⟩ := LinearMap.mem_range.mp hv'R
    rw [← hu, ← Module.End.mul_apply, hidem']
  obtain ⟨c', hc'⟩ := ggJSf2a_scalar_action he'.1 l
  have hc'1 : c' = 1 := by
    have h1 : πe' v' = c' • v' := hc' v' hv'E
    rw [hv'fix] at h1
    have h2 : (c' - 1) • v' = 0 := by rw [sub_smul, one_smul, ← h1, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero_iff_left hv0').mp h2)
  have hc'v : πe' v = v := by rw [hc' v hvE, hc'1, one_smul]
  have hcontra : v = 0 := by
    have h0 : (πe * πe') v = 0 := by rw [hzero]; rfl
    rw [Module.End.mul_apply, hc'v, hvfix] at h0
    exact h0
  exact hv0 hcontra

private theorem ggJSf2a_rank_eq_finrank_range_toLin' {F : Type*} [Field F] {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] (M : Matrix m n F) :
    M.rank = Module.finrank F (LinearMap.range (Matrix.toLin' M)) := by
  rw [Matrix.rank_eq_finrank_range_toLin M (Pi.basisFun F m) (Pi.basisFun F n),
    Matrix.toLin_eq_toLin']

private theorem ggJSf2a_rank_fromBlocks_one_zero {F : Type*} [Field F] {r s : ℕ} :
    (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) F) 0 0
      (0 : Matrix (Fin s) (Fin s) F)).rank = r := by
  classical
  have h : (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) F) 0 0
      (0 : Matrix (Fin s) (Fin s) F)) =
      diagonal (Sum.elim (fun _ : Fin r => (1 : F)) (fun _ : Fin s => (0 : F))) := by
    rw [← Matrix.fromBlocks_diagonal, Matrix.diagonal_one, Matrix.diagonal_zero]
  rw [h, Matrix.rank_diagonal, Fintype.card_subtype, Finset.card_filter, Fintype.sum_sum_type]
  simp

private theorem ggJSf2a_rank_map_eq {F E : Type*} [Field F] [Field E] {m : Type*} [Fintype m]
    [DecidableEq m] (f : F →+* E) (M : Matrix m m F) : (M.map f).rank = M.rank := by
  classical
  obtain ⟨V, U, e, hV, hU, h⟩ := Matrix.exists_rank_normal_form M
  have hVf : IsUnit (V.map f).det := (isUnit_iff_isUnit_det _).mp (hV.map f.mapMatrix)
  have hUf : IsUnit (U.map f).det := (isUnit_iff_isUnit_det _).mp (hU.map f.mapMatrix)
  have hE : (M.map f).rank = ((V.map f) * (M.map f) * (U.map f)).rank := by
    rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ hUf,
      Matrix.rank_mul_eq_right_of_isUnit_det _ _ hVf]
  have h1 : (V * M * U).map f = ((fromBlocks (1 : Matrix (Fin M.rank) (Fin M.rank) F) 0 0
      (0 : Matrix (Fin (Fintype.card m - M.rank)) (Fin (Fintype.card m - M.rank)) F)).submatrix
        e e).map f := by rw [h]
  simp only [Matrix.map_mul, ← Matrix.submatrix_map, Matrix.fromBlocks_map,
    Matrix.map_one _ (map_zero f) (map_one f), Matrix.map_zero _ (map_zero f)] at h1
  rw [hE, h1, Matrix.rank_submatrix, ggJSf2a_rank_fromBlocks_one_zero]

private theorem ggJSf2a_finrank_range_map {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (e : Matrix ι ι K) :
    Module.finrank (AlgebraicClosure K)
        (LinearMap.range (Matrix.toLin' (e.map (algebraMap K (AlgebraicClosure K))))) =
      Module.finrank K (LinearMap.range (Matrix.toLin' e)) := by
  rw [← ggJSf2a_rank_eq_finrank_range_toLin' (e.map (algebraMap K (AlgebraicClosure K))),
    ← ggJSf2a_rank_eq_finrank_range_toLin' e]
  exact ggJSf2a_rank_map_eq (algebraMap K (AlgebraicClosure K)) e

private theorem ggJSf2a_commute_T {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (b : GL ι K) {a : Matrix ι ι K}
    (ha : a ∈ Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) :
    Matrix.toLin' (a.map (algebraMap K (AlgebraicClosure K))) *
      Matrix.toLin' (((b : Matrix ι ι K)).map (algebraMap K (AlgebraicClosure K))) =
    Matrix.toLin' (((b : Matrix ι ι K)).map (algebraMap K (AlgebraicClosure K))) *
      Matrix.toLin' (a.map (algebraMap K (AlgebraicClosure K))) := by
  have ha' : a ∈ Algebra.adjoin K ({(b : Matrix ι ι K)} : Set (Matrix ι ι K)) := by
    simpa only [Set.image_singleton] using ha
  have hcomm : Commute (b : Matrix ι ι K) a := Algebra.commute_of_mem_adjoin_self ha'
  have hb : (b : Matrix ι ι K) * a = a * (b : Matrix ι ι K) := hcomm.eq
  rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, ← Matrix.toLin'_mul,
    ← Matrix.map_mul, ← Matrix.map_mul, hb]

private theorem ggJSf2a_mapsTo_eigenspace {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (b : GL ι K) {a : Matrix ι ι K}
    (ha : a ∈ Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) (l : AlgebraicClosure K)
    {v : ι → AlgebraicClosure K}
    (hv : v ∈ Module.End.eigenspace
      (Matrix.toLin' (((b : Matrix ι ι K)).map (algebraMap K (AlgebraicClosure K)))) l) :
    Matrix.toLin' (a.map (algebraMap K (AlgebraicClosure K))) v ∈
      Module.End.eigenspace
        (Matrix.toLin' (((b : Matrix ι ι K)).map (algebraMap K (AlgebraicClosure K)))) l := by
  refine Module.End.mem_eigenspace_iff.mpr ?_
  have hv' : Matrix.toLin' (((b : Matrix ι ι K)).map (algebraMap K (AlgebraicClosure K))) v
      = l • v := Module.End.mem_eigenspace_iff.mp hv
  have hc := ggJSf2a_commute_T b ha
  calc Matrix.toLin' (((b : Matrix ι ι K)).map (algebraMap K (AlgebraicClosure K)))
        (Matrix.toLin' (a.map (algebraMap K (AlgebraicClosure K))) v)
      = (Matrix.toLin' (((b : Matrix ι ι K)).map (algebraMap K (AlgebraicClosure K))) *
          Matrix.toLin' (a.map (algebraMap K (AlgebraicClosure K)))) v :=
        (Module.End.mul_apply _ _ _).symm
    _ = (Matrix.toLin' (a.map (algebraMap K (AlgebraicClosure K))) *
          Matrix.toLin' (((b : Matrix ι ι K)).map (algebraMap K (AlgebraicClosure K)))) v := by
        rw [← hc]
    _ = Matrix.toLin' (a.map (algebraMap K (AlgebraicClosure K)))
          (Matrix.toLin' (((b : Matrix ι ι K)).map (algebraMap K (AlgebraicClosure K))) v) :=
        Module.End.mul_apply _ _ _
    _ = Matrix.toLin' (a.map (algebraMap K (AlgebraicClosure K))) (l • v) := by rw [hv']
    _ = l • Matrix.toLin' (a.map (algebraMap K (AlgebraicClosure K))) v :=
        (Matrix.toLin' (a.map (algebraMap K (AlgebraicClosure K)))).map_smul l v

private theorem ggJSf2a_sub_one_mul_kill {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (b : GL ι K) {e : Matrix ι ι K}
    (he : e ∈ Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K))))
    {v : ι → AlgebraicClosure K}
    (hv : v ∈ Module.End.eigenspace
      (Matrix.toLin' (((b : Matrix ι ι K)).map (algebraMap K (AlgebraicClosure K)))) 1) :
    Matrix.toLin' ((((b : Matrix ι ι K) - 1) * e).map
        (algebraMap K (AlgebraicClosure K))) v = 0 := by
  have hmem := ggJSf2a_mapsTo_eigenspace b he 1 hv
  have hkill : ∀ w ∈ Module.End.eigenspace
      (Matrix.toLin' (((b : Matrix ι ι K)).map (algebraMap K (AlgebraicClosure K)))) 1,
      Matrix.toLin' ((((b : Matrix ι ι K) - 1)).map
        (algebraMap K (AlgebraicClosure K))) w = 0 := by
    intro w hw
    have hw' : Matrix.toLin' (((b : Matrix ι ι K)).map (algebraMap K (AlgebraicClosure K))) w
        = (1 : AlgebraicClosure K) • w := Module.End.mem_eigenspace_iff.mp hw
    rw [Matrix.map_sub (algebraMap K (AlgebraicClosure K))
        (map_sub (algebraMap K (AlgebraicClosure K))),
      Matrix.map_one (algebraMap K (AlgebraicClosure K)) (map_zero _) (map_one _),
      map_sub (Matrix.toLin'), Matrix.toLin'_one, LinearMap.sub_apply, hw', one_smul]
    simp
  calc Matrix.toLin' ((((b : Matrix ι ι K) - 1) * e).map
        (algebraMap K (AlgebraicClosure K))) v
      = Matrix.toLin' ((((b : Matrix ι ι K) - 1)).map
          (algebraMap K (AlgebraicClosure K)))
          (Matrix.toLin' (e.map (algebraMap K (AlgebraicClosure K))) v) := by
        rw [Matrix.map_mul, Matrix.toLin'_mul, LinearMap.comp_apply]
    _ = 0 := hkill _ hmem

private theorem ggJSf2a_exists_inv {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [Finite K]
    [CharP K 2] {b : GL ι K} (hodd : Odd (orderOf b)) {e : Matrix ι ι K}
    (he : IsPrimIdemIn (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) e)
    {x : Matrix ι ι K}
    (hx : x ∈ Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) (hxe : x * e ≠ 0) :
    ∃ y ∈ Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K))), x * y = e := by
  classical
  let A := Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))
  have hcomm : ∀ s ∈ ({b} : Set (GL ι K)), ∀ s' ∈ ({b} : Set (GL ι K)), Commute s s' := by
    intro s hs s' hs'
    rw [Set.mem_singleton_iff] at hs hs'
    subst hs
    subst hs'
    exact Commute.refl _
  have hodd' : ∀ s ∈ ({b} : Set (GL ι K)), Odd (orderOf s) := by
    intro s hs
    rw [Set.mem_singleton_iff] at hs
    subst hs
    exact hodd
  obtain ⟨K', fieldK', algK', finiteK', π, hπsurj, hπker, _hπdeg⟩ :=
    exists_blockField (S := ({b} : Set (GL ι K))) hcomm hodd' he
  letI : Field K' := fieldK'
  letI : Algebra K K' := algK'
  letI : Finite K' := finiteK'
  let eA : A := ⟨e, he.1⟩
  let xA : A := ⟨x, hx⟩
  have heidem : e * e = e := he.2.1.eq
  have hπe_idem : π eA * π eA = π eA := by
    rw [← map_mul]
    exact congrArg π (Subtype.ext heidem)
  have hπe_ne : π eA ≠ 0 := by
    intro h
    have h0 : e * e = 0 := (hπker eA).mp h
    exact he.2.2.1 (by rw [← heidem, h0])
  have hπe : π eA = 1 := by
    have h : π eA * (π eA - 1) = 0 := by rw [mul_sub, mul_one, hπe_idem, sub_self]
    rcases mul_eq_zero.mp h with h1 | h1
    · exact absurd h1 hπe_ne
    · exact sub_eq_zero.mp h1
  have hπx_ne : π xA ≠ 0 := by
    intro h
    exact hxe ((hπker xA).mp h)
  obtain ⟨yA, hyA⟩ := hπsurj ((π xA)⁻¹)
  have hcomp : π (xA * yA - eA) = 0 := by
    rw [map_sub, map_mul, hyA, hπe, mul_inv_cancel₀ hπx_ne, sub_self]
  have h0 : (((xA * yA - eA) : A) : Matrix ι ι K) * e = 0 := (hπker _).mp hcomp
  have hxy : x * ((yA : Matrix ι ι K) * e) = e := by
    have h : (x * (yA : Matrix ι ι K) - e) * e = 0 := by
      simpa [xA, eA] using h0
    rw [sub_mul, mul_assoc, heidem] at h
    exact sub_eq_zero.mp h
  exact ⟨(yA : Matrix ι ι K) * e, A.mul_mem yA.2 he.1, hxy⟩

theorem eigDimOn_one_of_isPrimIdemIn {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Finite K] [CharP K 2] {b : GL ι K} (hodd : Odd (orderOf b)) {e : Matrix ι ι K}
    (he : IsPrimIdemIn (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) e) :
    ((b : Matrix ι ι K) * e = e →
      eigDimOn (b : Matrix ι ι K) e 1 = Module.finrank K (LinearMap.range (Matrix.toLin' e))) ∧
      ((b : Matrix ι ι K) * e ≠ e → eigDimOn (b : Matrix ι ι K) e 1 = 0) := by
  classical
  let k := AlgebraicClosure K
  let φ : K →+* k := algebraMap K k
  let T : Module.End k (ι → k) := Matrix.toLin' (((b : Matrix ι ι K)).map φ)
  let πe : Module.End k (ι → k) := Matrix.toLin' (e.map φ)
  let E : Submodule k (ι → k) := Module.End.eigenspace T 1
  have hidem : πe * πe = πe := by
    show Matrix.toLin' (e.map φ) * Matrix.toLin' (e.map φ) = Matrix.toLin' (e.map φ)
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, ← Matrix.map_mul, he.2.1.eq]
  constructor
  · intro hbe
    have hTe : T * πe = πe := by
      have h1 : (((b : Matrix ι ι K)).map φ) * (e.map φ) = e.map φ := by
        rw [← Matrix.map_mul, hbe]
      show Matrix.toLin' (((b : Matrix ι ι K)).map φ) * Matrix.toLin' (e.map φ)
        = Matrix.toLin' (e.map φ)
      rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, h1]
    have hle : LinearMap.range πe ≤ E := by
      rintro v ⟨w, rfl⟩
      refine Module.End.mem_eigenspace_iff.mpr ?_
      rw [← Module.End.mul_apply, hTe, one_smul]
    have hinf : E ⊓ LinearMap.range πe = LinearMap.range πe := inf_eq_right.mpr hle
    change Module.finrank k (E ⊓ LinearMap.range πe : Submodule k (ι → k)) =
      Module.finrank K (LinearMap.range (Matrix.toLin' e))
    rw [hinf]
    exact ggJSf2a_finrank_range_map e
  · intro hbe
    have hbA : (b : Matrix ι ι K) ∈ Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K))) :=
      Algebra.subset_adjoin (by simp)
    have h1A : (1 : Matrix ι ι K) ∈ Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K))) :=
      Subalgebra.one_mem _
    have hxA : (((b : Matrix ι ι K) - 1) * e) ∈
        Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K))) :=
      Subalgebra.mul_mem _ (Subalgebra.sub_mem _ hbA h1A) he.1
    have hxe : (((b : Matrix ι ι K) - 1) * e) * e ≠ 0 := by
      intro h0
      apply hbe
      have h1 : ((b : Matrix ι ι K) - 1) * e = 0 := by
        calc ((b : Matrix ι ι K) - 1) * e
            = (((b : Matrix ι ι K) - 1) * e) * e := by rw [mul_assoc, he.2.1.eq]
          _ = 0 := h0
      have h2 : (b : Matrix ι ι K) * e - e = 0 := by
        simpa [sub_mul] using h1
      exact sub_eq_zero.mp h2
    obtain ⟨y, hy, hxy⟩ := ggJSf2a_exists_inv hodd he hxA hxe
    change Module.finrank k (E ⊓ LinearMap.range πe : Submodule k (ι → k)) = 0
    rw [Submodule.finrank_eq_zero]
    by_contra hV
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp hV
    have hvE : v ∈ E := hv.1
    have hvR : v ∈ LinearMap.range πe := hv.2
    have hvfix : πe v = v := by
      obtain ⟨u, hu⟩ := LinearMap.mem_range.mp hvR
      rw [← hu, ← Module.End.mul_apply, hidem]
    have hyE : Matrix.toLin' (y.map φ) v ∈ E :=
      ggJSf2a_mapsTo_eigenspace b hy 1 hvE
    have hkill := ggJSf2a_sub_one_mul_kill b he.1 hyE
    have hcomp : πe v = Matrix.toLin' ((((b : Matrix ι ι K) - 1) * e).map φ)
        (Matrix.toLin' (y.map φ) v) := by
      change Matrix.toLin' (e.map φ) v =
        Matrix.toLin' ((((b : Matrix ι ι K) - 1) * e).map φ) (Matrix.toLin' (y.map φ) v)
      have hmul : Matrix.toLin' (e.map φ) =
          (Matrix.toLin' ((((b : Matrix ι ι K) - 1) * e).map φ)).comp
            (Matrix.toLin' (y.map φ)) := by
        rw [← Matrix.toLin'_mul, ← Matrix.map_mul, hxy]
      rw [hmul, LinearMap.comp_apply]
    rw [hvfix] at hcomp
    exact hv0 (by rw [hcomp, hkill])

private lemma ggJSf2b_commute {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    {b : GL ι K} {e : Matrix ι ι K}
    (he : IsPrimIdemIn (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) e) :
    (b : Matrix ι ι K) * e = e * (b : Matrix ι ι K) := by
  let A : Subalgebra K (Matrix ι ι K) :=
    Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))
  have hcommP : (Units.val '' ({b} : Set (GL ι K)) : Set (Matrix ι ι K)).Pairwise Commute := by
    rintro x ⟨s, hs, rfl⟩ y ⟨t, ht, rfl⟩ _
    rw [Set.mem_singleton_iff] at hs ht
    subst hs; subst ht
    exact Commute.refl _
  letI : CommRing A := by
    change CommRing (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K))))
    exact Algebra.adjoinCommRingOfComm K hcommP
  have hbA : (b : Matrix ι ι K) ∈ A := Algebra.subset_adjoin (by simp [A])
  have hmem : e ∈ A := by simpa [A] using he.1
  have h := mul_comm (⟨(b : Matrix ι ι K), hbA⟩ : A) (⟨e, hmem⟩ : A)
  exact congrArg Subtype.val h

private lemma ggJSf2b_rootMultiplicity_map_of_map_eq {K : Type*} [Field K] (σ : K ≃+* K)
    {p : Polynomial K} (hp : p.map (σ : K →+* K) = p) (a : K) :
    p.rootMultiplicity (σ a) = p.rootMultiplicity a := by
  have h := Polynomial.eq_rootMultiplicity_map (p := p) (f := (σ : K →+* K)) σ.injective a
  rw [hp] at h
  exact h.symm

private lemma ggJSf2b_finrank_eigenspace_eq_of_charpoly_map_eq {K : Type*} [Field K] [IsAlgClosed K]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (σ : K ≃+* K) (C : Matrix ι ι K)
    (hfix : C.map (σ : K →+* K) = C)
    (hsemi : Module.End.IsSemisimple (Matrix.toLin' C)) (a : K) :
    Module.finrank K (Module.End.eigenspace (Matrix.toLin' C) (σ a)) =
      Module.finrank K (Module.End.eigenspace (Matrix.toLin' C) a) := by
  have hchar : ((Matrix.toLin' C).charpoly).map (σ : K →+* K) = (Matrix.toLin' C).charpoly := by
    have h1 := Matrix.charpoly_map C (σ : K →+* K)
    rw [hfix] at h1
    simpa only [Matrix.charpoly_toLin'] using h1.symm
  have h1 : Module.finrank K (Module.End.eigenspace (Matrix.toLin' C) a) =
      (Matrix.toLin' C).charpoly.rootMultiplicity a := by
    rw [← Module.End.IsFinitelySemisimple.maxGenEigenspace_eq_eigenspace
      (Module.End.IsSemisimple.isFinitelySemisimple hsemi) a]
    exact LinearMap.finrank_maxGenEigenspace_eq (Matrix.toLin' C) a
  have h2 : Module.finrank K (Module.End.eigenspace (Matrix.toLin' C) (σ a)) =
      (Matrix.toLin' C).charpoly.rootMultiplicity (σ a) := by
    rw [← Module.End.IsFinitelySemisimple.maxGenEigenspace_eq_eigenspace
      (Module.End.IsSemisimple.isFinitelySemisimple hsemi) (σ a)]
    exact LinearMap.finrank_maxGenEigenspace_eq (Matrix.toLin' C) (σ a)
  rw [h2, h1]
  exact ggJSf2b_rootMultiplicity_map_of_map_eq σ hchar a

private theorem ggJSf2b_rank_eq_finrank_range_toLin' {F : Type*} [Field F] {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] (M : Matrix m n F) :
    M.rank = Module.finrank F (LinearMap.range (Matrix.toLin' M)) := by
  rw [Matrix.rank_eq_finrank_range_toLin M (Pi.basisFun F m) (Pi.basisFun F n),
    Matrix.toLin_eq_toLin']

private theorem ggJSf2b_rank_fromBlocks_one_zero {F : Type*} [Field F] {r s : ℕ} :
    (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) F) 0 0
      (0 : Matrix (Fin s) (Fin s) F)).rank = r := by
  classical
  have h : (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) F) 0 0
      (0 : Matrix (Fin s) (Fin s) F)) =
      diagonal (Sum.elim (fun _ : Fin r => (1 : F)) (fun _ : Fin s => (0 : F))) := by
    rw [← Matrix.fromBlocks_diagonal, Matrix.diagonal_one, Matrix.diagonal_zero]
  rw [h, Matrix.rank_diagonal, Fintype.card_subtype, Finset.card_filter, Fintype.sum_sum_type]
  simp

private theorem ggJSf2b_rank_map_eq {F E : Type*} [Field F] [Field E] {m : Type*} [Fintype m]
    [DecidableEq m] (f : F →+* E) (M : Matrix m m F) : (M.map f).rank = M.rank := by
  classical
  obtain ⟨V, U, e, hV, hU, h⟩ := Matrix.exists_rank_normal_form M
  have hVf : IsUnit (V.map f).det := (isUnit_iff_isUnit_det _).mp (hV.map f.mapMatrix)
  have hUf : IsUnit (U.map f).det := (isUnit_iff_isUnit_det _).mp (hU.map f.mapMatrix)
  have hE : (M.map f).rank = ((V.map f) * (M.map f) * (U.map f)).rank := by
    rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ hUf,
      Matrix.rank_mul_eq_right_of_isUnit_det _ _ hVf]
  have h1 : (V * M * U).map f = ((fromBlocks (1 : Matrix (Fin M.rank) (Fin M.rank) F) 0 0
      (0 : Matrix (Fin (Fintype.card m - M.rank)) (Fin (Fintype.card m - M.rank)) F)).submatrix
        e e).map f := by rw [h]
  simp only [Matrix.map_mul, ← Matrix.submatrix_map, Matrix.fromBlocks_map,
    Matrix.map_one _ (map_zero f) (map_one f), Matrix.map_zero _ (map_zero f)] at h1
  rw [hE, h1, Matrix.rank_submatrix, ggJSf2b_rank_fromBlocks_one_zero]

private theorem ggJSf2b_finrank_range_map {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (e : Matrix ι ι K) :
    Module.finrank (AlgebraicClosure K)
        (LinearMap.range (Matrix.toLin' (e.map (algebraMap K (AlgebraicClosure K))))) =
      Module.finrank K (LinearMap.range (Matrix.toLin' e)) := by
  rw [← ggJSf2b_rank_eq_finrank_range_toLin' (e.map (algebraMap K (AlgebraicClosure K))),
    ← ggJSf2b_rank_eq_finrank_range_toLin' e]
  exact ggJSf2b_rank_map_eq (algebraMap K (AlgebraicClosure K)) e

private theorem ggJSf2b_finrank_biSup_eq_sum {K M ι : Type*} [Field K] [AddCommGroup M]
    [Module K M] [FiniteDimensional K M] [DecidableEq ι] {S : ι → Submodule K M}
    (hS : iSupIndep S) (s : Finset ι) :
    Module.finrank K (⨆ i ∈ s, S i : Submodule K M) = ∑ i ∈ s, Module.finrank K (S i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hdis : Disjoint (S a) (⨆ i ∈ s, S i) := hS.disjoint_biSup (by simpa using ha)
    have h := Submodule.finrank_sup_add_finrank_inf_eq (S a) (⨆ i ∈ s, S i)
    rw [hdis.eq_bot, finrank_bot, add_zero] at h
    rw [Finset.iSup_insert, Finset.sum_insert ha, ← ih]
    exact h

private lemma ggJSf2b_exists_blockMinpoly {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Finite K] [CharP K 2] {b : GL ι K} (hodd : Odd (orderOf b)) {e : Matrix ι ι K}
    (he : IsPrimIdemIn (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) e) :
    ∃ g : Polynomial K,
      Irreducible g ∧
      g.natDegree = blockDegree (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) e ∧
      (Polynomial.aeval (b : Matrix ι ι K) g) * e = 0 ∧
      g ∣ Polynomial.X ^ orderOf b - 1 := by
  classical
  let A : Subalgebra K (Matrix ι ι K) :=
    Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))
  obtain ⟨E, hEfield, hEalg, hEfin, π, hπsurj, hπker, hπdeg⟩ :=
    exists_blockField (S := ({b} : Set (GL ι K)))
      (by
        intro s hs s' hs'
        rw [Set.mem_singleton_iff] at hs hs'
        subst hs; subst hs'
        exact Commute.refl _)
      (by
        intro s hs
        rw [Set.mem_singleton_iff] at hs
        subst hs
        exact hodd)
      he
  letI : Field E := hEfield
  letI : Algebra K E := hEalg
  letI : Finite E := hEfin
  have hbA : (b : Matrix ι ι K) ∈ A := Algebra.subset_adjoin (by simp [A])
  let bA : A := ⟨(b : Matrix ι ι K), hbA⟩
  let β : E := π bA
  let g : Polynomial K := minpoly K β
  have hβint : IsIntegral K β := IsIntegral.of_finite (R := K) (B := E) β
  have hAtop : Algebra.adjoin K ({bA} : Set A) = ⊤ := by
    apply le_antisymm le_top
    intro a _
    have hval : (Algebra.adjoin K ({bA} : Set A)).map (Subalgebra.val A) = A := by
      rw [AlgHom.map_adjoin]
      have hset : (Subalgebra.val A) '' ({bA} : Set A) =
          Units.val '' ({b} : Set (GL ι K)) := by
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩
          rw [show y = bA from hy]
          exact ⟨b, rfl, rfl⟩
        · rintro ⟨s, hs, hx⟩
          rw [Set.mem_singleton_iff] at hs
          subst hs
          exact ⟨bA, rfl, hx⟩
      rw [hset]
    have hmem : (a : Matrix ι ι K) ∈
        (Algebra.adjoin K ({bA} : Set A)).map (Subalgebra.val A) := by
      rw [hval]
      exact a.2
    obtain ⟨s, hs, hsv⟩ := Subalgebra.mem_map.mp hmem
    exact (Subtype.ext hsv) ▸ hs
  have hEtop : Algebra.adjoin K ({β} : Set E) = ⊤ := by
    have htop : (⊤ : Subalgebra K A).map π = ⊤ := by
      rw [Algebra.map_top, (AlgHom.range_eq_top π).mpr hπsurj]
    have h2 : (Algebra.adjoin K ({bA} : Set A)).map π = ⊤ := by rw [hAtop, htop]
    rw [AlgHom.map_adjoin] at h2
    simpa [β] using h2
  have hfin : Module.finrank K E = (minpoly K β).natDegree := by
    have h1 : (PowerBasis.ofAdjoinEqTop hβint hEtop).dim = (minpoly K β).natDegree :=
      PowerBasis.ofAdjoinEqTop_dim hβint hEtop
    have h2 : Module.finrank K E = (PowerBasis.ofAdjoinEqTop hβint hEtop).dim :=
      PowerBasis.finrank (PowerBasis.ofAdjoinEqTop hβint hEtop)
    rw [h2, h1]
  refine ⟨g, minpoly.irreducible hβint, ?_, ?_, ?_⟩
  · exact hfin.symm.trans hπdeg
  · have h1 : Polynomial.aeval β g = 0 := minpoly.aeval K β
    have h2 : π (Polynomial.aeval bA g) = 0 := by
      rw [← Polynomial.aeval_algHom_apply π bA g]
      simpa [β] using h1
    have h3 : ((Polynomial.aeval bA g : A) : Matrix ι ι K) * e = 0 := (hπker _).mp h2
    have h4 : ((Polynomial.aeval bA g : A) : Matrix ι ι K) =
        Polynomial.aeval (b : Matrix ι ι K) g := by
      simpa using (Polynomial.aeval_algHom_apply (Subalgebra.val A) bA g).symm
    rwa [h4] at h3
  · have hbn : bA ^ orderOf b = 1 := by
      apply Subtype.ext
      change (b : Matrix ι ι K) ^ orderOf b = 1
      rw [← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one]
    have hβn : β ^ orderOf b = 1 := by
      rw [show β = π bA from rfl, ← map_pow, hbn, map_one]
    refine minpoly.dvd K β ?_
    rw [map_sub, map_pow, Polynomial.aeval_X, map_one, hβn, sub_self]

private lemma ggJSf2b_aeval_map {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (b : Matrix ι ι K) (p : Polynomial K) :
    Polynomial.aeval (b.map (algebraMap K (AlgebraicClosure K)))
        (p.map (algebraMap K (AlgebraicClosure K))) =
      (Polynomial.aeval b p).map (algebraMap K (AlgebraicClosure K)) := by
  let f : Matrix ι ι K →ₐ[K] Matrix ι ι (AlgebraicClosure K) :=
    AlgHom.mapMatrix (Algebra.ofId K (AlgebraicClosure K))
  have hf : f b = b.map (algebraMap K (AlgebraicClosure K)) := AlgHom.mapMatrix_apply ..
  have h1 : f (Polynomial.aeval b p) = (Polynomial.aeval b p).map
      (algebraMap K (AlgebraicClosure K)) := AlgHom.mapMatrix_apply ..
  rw [← hf, Polynomial.aeval_map_algebraMap (AlgebraicClosure K) (f b) p,
    Polynomial.aeval_algHom_apply f b p, h1]

private theorem ggJSf2b_eigenspace_mul {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (B E : Module.End k V) (hE : E * E = E) (hc : B * E = E * B) {l : k} (hl : l ≠ 0) :
    Module.End.eigenspace (B * E) l = Module.End.eigenspace B l ⊓ LinearMap.range E := by
  ext v
  simp only [Module.End.mem_eigenspace_iff, Submodule.mem_inf, LinearMap.mem_range,
    Module.End.mul_apply]
  constructor
  · intro hv
    have hkey : l • E v = l • v := by
      calc l • E v = E (l • v) := (E.map_smul l v).symm
        _ = E (B (E v)) := by rw [← hv]
        _ = (E * B * E) v := by simp only [Module.End.mul_apply]
        _ = (B * E) v := by
              congr 1
              rw [← hc, mul_assoc, hE]
        _ = l • v := hv
    have hEv : E v = v := by
      have h1 : l⁻¹ • (l • E v) = l⁻¹ • (l • v) := congrArg (fun x => l⁻¹ • x) hkey
      simpa [smul_smul, inv_mul_cancel₀ hl] using h1
    have hv' : B v = l • v := by rw [hEv] at hv; exact hv
    exact ⟨hv', ⟨v, hEv⟩⟩
  · rintro ⟨hvB, ⟨w, hw⟩⟩
    have hEv : E v = v := by rw [← hw, ← Module.End.mul_apply, hE]
    rw [hEv, hvB]

private lemma ggJSf2b_eigDimOn_eq {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (b e : Matrix ι ι K) (hbe : b * e = e * b) (hEidem : e * e = e)
    (l : AlgebraicClosure K) (hl : l ≠ 0) :
    eigDimOn b e l = Module.finrank (AlgebraicClosure K)
      (Module.End.eigenspace
        (Matrix.toLin' ((b.map (algebraMap K (AlgebraicClosure K))) *
          (e.map (algebraMap K (AlgebraicClosure K))))) l) := by
  let φ : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
  have hE' : Matrix.toLin' (e.map φ) * Matrix.toLin' (e.map φ) = Matrix.toLin' (e.map φ) := by
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, ← Matrix.map_mul, hEidem]
  have hc' : Matrix.toLin' (b.map φ) * Matrix.toLin' (e.map φ) =
      Matrix.toLin' (e.map φ) * Matrix.toLin' (b.map φ) := by
    rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← Matrix.toLin'_mul,
      ← Matrix.toLin'_mul, ← Matrix.map_mul, ← Matrix.map_mul, hbe]
  have h := ggJSf2b_eigenspace_mul (B := Matrix.toLin' (b.map φ))
    (E := Matrix.toLin' (e.map φ)) hE' hc' hl
  rw [eigDimOn, ← h, Module.End.mul_eq_comp, Matrix.toLin'_mul]

private lemma ggJSf2b_roots_card {K : Type*} [Field K] [Finite K] [CharP K 2]
    [DecidableEq (AlgebraicClosure K)] {n : ℕ} (hn : (n : K) ≠ 0) {g : Polynomial K}
    (hg_dvd : g ∣ Polynomial.X ^ n - 1) :
    (g.map (algebraMap K (AlgebraicClosure K))).roots.toFinset.card = g.natDegree := by
  classical
  have hg_sep : g.Separable :=
    Polynomial.Separable.of_dvd (Polynomial.X_pow_sub_one_separable_iff.mpr hn) hg_dvd
  have hsep : (g.map (algebraMap K (AlgebraicClosure K))).Separable := hg_sep.map
  have hnodup : (g.map (algebraMap K (AlgebraicClosure K))).roots.Nodup :=
    Polynomial.nodup_roots hsep
  rw [Multiset.toFinset_card_of_nodup hnodup,
    ← Polynomial.Splits.natDegree_eq_card_roots
      (IsAlgClosed.splits (g.map (algebraMap K (AlgebraicClosure K))))]
  exact Polynomial.natDegree_map_eq_of_injective
    (algebraMap K (AlgebraicClosure K)).injective g

private lemma ggJSf2b_zero_not_root {K : Type*} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hn0 : n ≠ 0) {g : Polynomial K} (hg_dvd : g ∣ Polynomial.X ^ n - 1) :
    ¬ (g.map (algebraMap K (AlgebraicClosure K))).IsRoot 0 := by
  intro h0
  have h0' : g.IsRoot 0 := by
    rw [Polynomial.IsRoot.def] at h0 ⊢
    rw [show (0 : AlgebraicClosure K) = algebraMap K (AlgebraicClosure K) 0 from
      (map_zero _).symm, Polynomial.eval_map_apply] at h0
    exact (algebraMap K (AlgebraicClosure K)).injective h0
  have hcoeff : g.coeff 0 = 0 := by
    rw [Polynomial.IsRoot.def] at h0'
    rw [Polynomial.coeff_zero_eq_eval_zero]
    exact h0'
  have hX : Polynomial.X ∣ g := Polynomial.X_dvd_iff.mpr hcoeff
  have hX2 : Polynomial.X ∣ (Polynomial.X ^ n - 1 : Polynomial K) := hX.trans hg_dvd
  have hc := Polynomial.X_dvd_iff.mp hX2
  simp [Polynomial.coeff_X_pow, Polynomial.coeff_one, Ne.symm hn0] at hc

private lemma ggJSf2b_isSemisimple_idem {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (E : Module.End k V) (hE : E * E = E) : E.IsSemisimple := by
  refine TauCeti.isSemisimple_of_iSup_eigenspace_eq_top ?_
  rw [eq_top_iff]
  intro v _
  have hEidem : IsIdempotentElem E := hE
  have hcompl : IsCompl (LinearMap.range E) (LinearMap.ker E) :=
    LinearMap.IsIdempotentElem.isCompl hEidem
  have hv : v ∈ LinearMap.range E ⊔ LinearMap.ker E := by rw [hcompl.sup_eq_top]; trivial
  rw [Submodule.mem_sup] at hv
  obtain ⟨a, ha, b, hb, hab⟩ := hv
  have ha' : a ∈ E.eigenspace 1 := by
    rw [Module.End.mem_eigenspace_iff, one_smul]
    exact (LinearMap.IsIdempotentElem.mem_range_iff hEidem).mp ha
  have hb' : b ∈ E.eigenspace 0 := by
    rw [Module.End.mem_eigenspace_iff, zero_smul]
    exact hb
  rw [← hab]
  exact Submodule.add_mem _
    (Submodule.mem_iSup_of_mem 1 ha') (Submodule.mem_iSup_of_mem 0 hb')

private lemma ggJSf2b_isSemisimple_C {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Finite K] [CharP K 2] {b : GL ι K} (hodd : Odd (orderOf b)) {e : Matrix ι ι K}
    (hbe : (b : Matrix ι ι K) * e = e * (b : Matrix ι ι K)) (hEidem : e * e = e) :
    Module.End.IsSemisimple
      (Matrix.toLin' ((b : Matrix ι ι K).map (algebraMap K (AlgebraicClosure K)) *
        (e.map (algebraMap K (AlgebraicClosure K))))) := by
  let φ := algebraMap K (AlgebraicClosure K)
  have hBpow : ((b : Matrix ι ι K).map φ) ^ orderOf b = 1 := by
    rw [← Matrix.map_pow, ← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one,
      Matrix.map_one φ (map_zero _) (map_one _)]
  have htoLin_pow : ∀ n, (Matrix.toLin' ((b : Matrix ι ι K).map φ)) ^ n =
      Matrix.toLin' (((b : Matrix ι ι K).map φ) ^ n) := fun n => by
    simpa using map_pow (Matrix.toLinAlgEquiv' (R := AlgebraicClosure K) (m := ι))
      (((b : Matrix ι ι K).map φ)) n
  have hBsemi : Module.End.IsSemisimple (Matrix.toLin' ((b : Matrix ι ι K).map φ)) :=
    TauCeti.End.isSemisimple_of_pow_eq_one
      (by
        intro h
        exact hodd.not_two_dvd_nat
          ((CharP.cast_eq_zero_iff (AlgebraicClosure K) 2 (orderOf b)).mp h))
      (by rw [htoLin_pow, hBpow, Matrix.toLin'_one, Module.End.one_eq_id])
  have hEsemi : Module.End.IsSemisimple (Matrix.toLin' (e.map φ)) :=
    ggJSf2b_isSemisimple_idem _
      (by rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, ← Matrix.map_mul, hEidem])
  have hcomm : Matrix.toLin' ((b : Matrix ι ι K).map φ) * Matrix.toLin' (e.map φ) =
      Matrix.toLin' (e.map φ) * Matrix.toLin' ((b : Matrix ι ι K).map φ) := by
    rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← Matrix.toLin'_mul,
      ← Matrix.toLin'_mul, ← Matrix.map_mul, ← Matrix.map_mul, hbe]
  rw [Matrix.toLin'_mul, ← Module.End.mul_eq_comp]
  exact Module.End.IsSemisimple.mul_of_commute hcomm hBsemi hEsemi

private lemma ggJSf2b_toLin_eq {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (M : Matrix ι ι K) :
    Matrix.toLin' M = Matrix.toLinAlgEquiv' (R := K) M := by
  refine LinearMap.ext (fun v => ?_)
  rw [Matrix.toLin'_apply, Matrix.toLinAlgEquiv'_apply]

private lemma ggJSf2b_aeval_toLin {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (B : Matrix ι ι K) (p : Polynomial K) :
    Matrix.toLin' (Polynomial.aeval B p) = Polynomial.aeval (Matrix.toLin' B) p := by
  have h : Matrix.toLinAlgEquiv' (R := K) (Polynomial.aeval B p) =
      Polynomial.aeval (Matrix.toLinAlgEquiv' (R := K) B) p :=
    (Polynomial.aeval_algHom_apply (Matrix.toLinAlgEquiv' (R := K)) B p).symm
  simpa [ggJSf2b_toLin_eq] using h

private lemma ggJSf2b_eigenspace_mul_apply {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (B E : Module.End k V) (hE : E * E = E) (hc : B * E = E * B) {l : k} (hl : l ≠ 0)
    {v : V} (hv : B (E v) = l • v) : E v = v ∧ B v = l • v := by
  have hkey : l • E v = l • v := by
    have h1 : E (B (E v)) = l • E v := (congrArg E hv).trans (E.map_smul l v)
    have h2 : E (B (E v)) = l • v := by
      calc E (B (E v)) = (E * B * E) v := by simp only [Module.End.mul_apply]
        _ = (B * E) v := by congr 1; rw [← hc, mul_assoc, hE]
        _ = l • v := hv
    rw [← h1, h2]
  have hEv : E v = v := by
    have h1 : l⁻¹ • (l • E v) = l⁻¹ • (l • v) := congrArg (fun x => l⁻¹ • x) hkey
    simpa [smul_smul, inv_mul_cancel₀ hl] using h1
  have hv' : B v = l • v := by rw [hEv] at hv; exact hv
  exact ⟨hEv, hv'⟩

private lemma ggJSf2b_off_R {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Finite K] [CharP K 2] {b : GL ι K} (hodd : Odd (orderOf b)) {e : Matrix ι ι K}
    (hbe : (b : Matrix ι ι K) * e = e * (b : Matrix ι ι K)) (hEidem : e * e = e)
    {g : Polynomial K} (hg_dvd : g ∣ Polynomial.X ^ orderOf b - 1)
    (h_ann : Polynomial.aeval (b : Matrix ι ι K) g * e = 0)
    {R : Finset (AlgebraicClosure K)}
    (hmemR : ∀ l, l ∈ R ↔ Polynomial.aeval l
      (g.map (algebraMap K (AlgebraicClosure K))) = 0) :
    ∀ l ∉ R, eigDimOn (b : Matrix ι ι K) e l = 0 := by
  classical
  let k := AlgebraicClosure K
  let φ : K →+* k := algebraMap K k
  let B : Matrix ι ι k := (b : Matrix ι ι K).map φ
  let E : Matrix ι ι k := e.map φ
  let C : Matrix ι ι k := B * E
  have hn : (orderOf b : K) ≠ 0 := by
    intro h
    exact hodd.not_two_dvd_nat ((CharP.cast_eq_zero_iff K 2 (orderOf b)).mp h)
  have hE' : Matrix.toLin' E * Matrix.toLin' E = Matrix.toLin' E := by
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, ← Matrix.map_mul, hEidem]
  have hc' : Matrix.toLin' B * Matrix.toLin' E = Matrix.toLin' E * Matrix.toLin' B := by
    rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← Matrix.toLin'_mul,
      ← Matrix.toLin'_mul, ← Matrix.map_mul, ← Matrix.map_mul, hbe]
  have hker0 : Module.End.eigenspace (Matrix.toLin' B) (0 : k) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    rw [Module.End.mem_eigenspace_iff, zero_smul] at hv
    have hBpow : B ^ orderOf b = 1 := by
      rw [show B = (b : Matrix ι ι K).map φ from rfl, ← Matrix.map_pow,
        ← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one,
        Matrix.map_one φ (map_zero _) (map_one _)]
    have hpow : (Matrix.toLin' B) ^ orderOf b = 1 := by
      rw [ggJSf2b_toLin_eq B, ← map_pow, hBpow, map_one]
    have h2 : v = ((Matrix.toLin' B) ^ (orderOf b - 1)) ((Matrix.toLin' B) v) := by
      rw [← Module.End.mul_apply, ← pow_succ, Nat.sub_add_cancel (orderOf_pos b), hpow,
        Module.End.one_apply]
    rw [hv, LinearMap.map_zero] at h2
    exact h2
  intro l hl
  by_cases hl0 : l = 0
  · subst hl0
    rw [eigDimOn, Submodule.finrank_eq_zero, Submodule.eq_bot_iff]
    intro v hv
    rw [Submodule.mem_inf, hker0] at hv
    simpa using hv.1
  · rw [ggJSf2b_eigDimOn_eq (b : Matrix ι ι K) e hbe hEidem l hl0]
    rw [Submodule.finrank_eq_zero, Submodule.eq_bot_iff]
    intro v hv
    rw [Module.End.mem_eigenspace_iff] at hv
    have hvBE : Matrix.toLin' B (Matrix.toLin' E v) = l • v := by
      have h := hv
      rw [Matrix.toLin'_mul, LinearMap.comp_apply] at h
      exact h
    obtain ⟨hEv, hvB⟩ := ggJSf2b_eigenspace_mul_apply (B := Matrix.toLin' B)
      (E := Matrix.toLin' E) hE' hc' hl0 hvBE
    have hannM : (Polynomial.aeval B (g.map φ)) * E = 0 := by
      rw [ggJSf2b_aeval_map (b : Matrix ι ι K) g, ← Matrix.map_mul, h_ann]
      exact Matrix.map_zero φ (map_zero _)
    have hann : Polynomial.aeval (Matrix.toLin' B) (g.map φ) v = 0 := by
      have h1 := congrArg (fun M : Matrix ι ι k => (Matrix.toLin' M) v) hannM
      have h2 : (Matrix.toLin' ((Polynomial.aeval B (g.map φ)) * E)) v =
          (Polynomial.aeval (Matrix.toLin' B) (g.map φ)) (Matrix.toLin' E v) := by
        rw [Matrix.toLin'_mul, LinearMap.comp_apply, ggJSf2b_aeval_toLin]
      rw [h2, hEv] at h1
      simpa using h1
    have hsmul : (g.map φ).eval l • v = 0 := by
      rw [← Module.End.aeval_apply_of_mem_apply_eq_smul (f := Matrix.toLin' B)
        (x := v) (μ := l) hvB (p := g.map φ)]
      exact hann
    by_cases heval0 : (g.map φ).eval l = 0
    · exact absurd ((hmemR l).mpr (by
        change Polynomial.eval l (Polynomial.map (algebraMap K (AlgebraicClosure K)) g) = 0
        exact heval0)) hl
    · exact (smul_eq_zero.mp hsmul).resolve_left heval0

private lemma ggJSf2b_sum_eigDimOn {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Finite K] [CharP K 2] {b : GL ι K} (hodd : Odd (orderOf b)) {e : Matrix ι ι K}
    (hbe : (b : Matrix ι ι K) * e = e * (b : Matrix ι ι K)) (hEidem : e * e = e)
    {g : Polynomial K} (hg_dvd : g ∣ Polynomial.X ^ orderOf b - 1)
    (h_ann : Polynomial.aeval (b : Matrix ι ι K) g * e = 0)
    (R : Finset (AlgebraicClosure K))
    (hmemR : ∀ l, l ∈ R ↔
      Polynomial.aeval l (g.map (algebraMap K (AlgebraicClosure K))) = 0)
    (h0R : (0 : AlgebraicClosure K) ∉ R) :
    Module.finrank K (LinearMap.range (Matrix.toLin' e)) =
      ∑ l ∈ R, eigDimOn (b : Matrix ι ι K) e l := by
  classical
  let k := AlgebraicClosure K
  let φ : K →+* k := algebraMap K k
  let Bm : Matrix ι ι k := (b : Matrix ι ι K).map φ
  let Em : Matrix ι ι k := e.map φ
  let B : Module.End k (ι → k) := Matrix.toLin' Bm
  let E : Module.End k (ι → k) := Matrix.toLin' Em
  let C : Module.End k (ι → k) := Matrix.toLin' (Bm * Em)
  have hCBE : C = B * E := by
    change Matrix.toLin' (Bm * Em) = B * E
    rw [Module.End.mul_eq_comp, Matrix.toLin'_mul]
  have hsemi : Module.End.IsSemisimple C := by
    simpa only [C, Bm, Em, φ] using ggJSf2b_isSemisimple_C hodd hbe hEidem
  have hsup : (⨆ l : k, C.eigenspace l) = ⊤ :=
    Module.End.IsSemisimple.iSup_eigenspace_eq_top hsemi
  have hind : iSupIndep C.eigenspace := Module.End.eigenspaces_iSupIndep C
  let b' : Matrix ι ι k := ((b⁻¹ : GL ι K) : Matrix ι ι K).map φ
  have hBm_mul : Bm * b' = 1 := by
    dsimp only [Bm, b', φ]
    rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hBm_mul' : b' * Bm = 1 := by
    dsimp only [Bm, b', φ]
    rw [← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hBB' : B * Matrix.toLin' b' = 1 := by
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hBm_mul, Matrix.toLin'_one,
      Module.End.one_eq_id]
  have hB'B : Matrix.toLin' b' * B = 1 := by
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hBm_mul', Matrix.toLin'_one,
      Module.End.one_eq_id]
  have hinj : Function.Injective B := by
    apply Function.LeftInverse.injective (g := Matrix.toLin' b')
    intro v
    have h := congrArg (fun f : Module.End k (ι → k) => f v) hB'B
    simpa [Module.End.mul_apply] using h
  have hzero : C.eigenspace 0 = LinearMap.ker E := by
    rw [hCBE]
    ext v
    rw [Module.End.mem_eigenspace_iff, zero_smul, LinearMap.mem_ker]
    constructor
    · intro hv
      have hv' : B (E v) = 0 := by simpa [Module.End.mul_apply] using hv
      exact hinj (by simpa using hv')
    · intro hv
      simp [Module.End.mul_apply, hv]
  have hEigL : ∀ l ∉ insert 0 R, C.eigenspace l = ⊥ := by
    intro l hl
    have hlR : l ∉ R := fun h => hl (Finset.mem_insert.mpr (Or.inr h))
    have hl0 : l ≠ 0 := fun h => hl (h ▸ Finset.mem_insert_self 0 R)
    have hoff := ggJSf2b_off_R hodd hbe hEidem hg_dvd h_ann hmemR l hlR
    have heq : eigDimOn (b : Matrix ι ι K) e l = Module.finrank k (C.eigenspace l) := by
      simpa only [C, Bm, Em, φ] using
        ggJSf2b_eigDimOn_eq (b : Matrix ι ι K) e hbe hEidem l hl0
    rw [heq] at hoff
    exact (Submodule.finrank_eq_zero).mp hoff
  have hV : (⨆ l ∈ insert 0 R, C.eigenspace l) = ⊤ := by
    rw [eq_top_iff, ← hsup]
    apply iSup_le
    intro l
    by_cases hl : l ∈ insert 0 R
    · exact le_iSup₂ (f := fun i (_ : i ∈ insert 0 R) => C.eigenspace i) l hl
    · rw [hEigL l hl]
      exact bot_le
  have htop : Module.finrank k (⊤ : Submodule k (ι → k)) =
      ∑ l ∈ insert 0 R, Module.finrank k (C.eigenspace l) := by
    rw [← hV]
    exact ggJSf2b_finrank_biSup_eq_sum hind (insert 0 R)
  have hsum_top : Module.finrank k (ι → k) =
      Module.finrank k (LinearMap.ker E) +
        ∑ l ∈ R, Module.finrank k (C.eigenspace l) := by
    rw [finrank_top k (ι → k)] at htop
    rw [Finset.sum_insert h0R, hzero] at htop
    exact htop
  have hrn := LinearMap.finrank_range_add_finrank_ker E
  have hrange : Module.finrank k (LinearMap.range E) =
      ∑ l ∈ R, Module.finrank k (C.eigenspace l) := by
    omega
  have hsum_eq : (∑ l ∈ R, Module.finrank k (C.eigenspace l)) =
      ∑ l ∈ R, eigDimOn (b : Matrix ι ι K) e l := by
    apply Finset.sum_congr rfl
    intro l hl
    have hl0 : l ≠ 0 := fun h => h0R (h ▸ hl)
    have heq : eigDimOn (b : Matrix ι ι K) e l = Module.finrank k (C.eigenspace l) := by
      simpa only [C, Bm, Em, φ] using
        ggJSf2b_eigDimOn_eq (b : Matrix ι ι K) e hbe hEidem l hl0
    exact heq.symm
  have hErange : LinearMap.range E = LinearMap.range (Matrix.toLin' (e.map φ)) := by
    simp only [E, Em, φ]
  have hfinal : Module.finrank k (LinearMap.range E) =
      ∑ l ∈ R, eigDimOn (b : Matrix ι ι K) e l := by
    rw [← hsum_eq]
    exact hrange
  rw [← ggJSf2b_finrank_range_map e, ← hErange]
  exact hfinal

private lemma ggJSf2b_eigDimOn_eq_of_roots {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Finite K] [CharP K 2] {b : GL ι K} (hodd : Odd (orderOf b)) {e : Matrix ι ι K}
    (hbe : (b : Matrix ι ι K) * e = e * (b : Matrix ι ι K)) (hEidem : e * e = e)
    {g : Polynomial K} (hg : Irreducible g)
    {l l' : AlgebraicClosure K}
    (hl : (g.map (algebraMap K (AlgebraicClosure K))).IsRoot l)
    (hl' : (g.map (algebraMap K (AlgebraicClosure K))).IsRoot l')
    (hl0 : l ≠ 0) (hl0' : l' ≠ 0) :
    eigDimOn (b : Matrix ι ι K) e l = eigDimOn (b : Matrix ι ι K) e l' := by
  classical
  let k := AlgebraicClosure K
  let φ : K →+* k := algebraMap K k
  let C : Matrix ι ι k := (b : Matrix ι ι K).map φ * e.map φ
  have hg_ne : g ≠ 0 := hg.ne_zero
  have haeval_l : Polynomial.aeval l g = 0 := by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map]
    exact hl
  have haeval_l' : Polynomial.aeval l' g = 0 := by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map]
    exact hl'
  have hroot_l : l ∈ g.rootSet k :=
    (Polynomial.mem_rootSet).mpr ⟨hg_ne, haeval_l⟩
  have hroot_l' : l' ∈ g.rootSet k :=
    (Polynomial.mem_rootSet).mpr ⟨hg_ne, haeval_l'⟩
  haveI : MulAction.IsPretransitive (k ≃ₐ[K] k) (g.rootSet k) :=
    TauCeti.isPretransitive_rootSet_of_irreducible (F := K) (M := k) hg
  obtain ⟨σ, hσ⟩ := MulAction.IsPretransitive.exists_smul_eq
    (M := k ≃ₐ[K] k) (α := g.rootSet k) ⟨l, hroot_l⟩ ⟨l', hroot_l'⟩
  have hσl : σ l = l' := by
    simpa using congrArg Subtype.val hσ
  have hfix : C.map (σ : k →+* k) = C := by
    dsimp only [C, φ]
    rw [Matrix.map_mul, Matrix.map_map, Matrix.map_map]
    congr 2 <;> ext x <;> exact σ.commutes x
  have hsemi : Module.End.IsSemisimple (Matrix.toLin' C) := by
    simpa only [C, φ] using ggJSf2b_isSemisimple_C hodd hbe hEidem
  have hchar := ggJSf2b_finrank_eigenspace_eq_of_charpoly_map_eq
    (σ : k ≃+* k) C hfix hsemi l
  have hσl' : (σ : k ≃+* k) l = l' := hσl
  rw [hσl'] at hchar
  rw [ggJSf2b_eigDimOn_eq (b : Matrix ι ι K) e hbe hEidem l hl0,
    ggJSf2b_eigDimOn_eq (b : Matrix ι ι K) e hbe hEidem l' hl0']
  simpa only [C, φ] using hchar.symm

theorem exists_blockRoots_of_isPrimIdemIn {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Finite K] [CharP K 2] {b : GL ι K} (hodd : Odd (orderOf b)) {e : Matrix ι ι K}
    (he : IsPrimIdemIn (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) e) :
    ∃ (R : Finset (AlgebraicClosure K)) (m : ℕ),
      R.card = blockDegree (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) e ∧
      R.card * m = Module.finrank K (LinearMap.range (Matrix.toLin' e)) ∧
      (∀ l ∈ R, eigDimOn (b : Matrix ι ι K) e l = m) ∧
        ∀ l ∉ R, eigDimOn (b : Matrix ι ι K) e l = 0 := by
  classical
  let A : Subalgebra K (Matrix ι ι K) :=
    Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))
  obtain ⟨g, hg_irred, hg_deg, h_ann, hg_dvd⟩ := ggJSf2b_exists_blockMinpoly hodd he
  let φ : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
  let R : Finset (AlgebraicClosure K) := (g.map φ).roots.toFinset
  have hbe : (b : Matrix ι ι K) * e = e * (b : Matrix ι ι K) := ggJSf2b_commute he
  have hEidem : e * e = e := he.2.1
  have hg_ne : g ≠ 0 := hg_irred.ne_zero
  have hφ_inj : Function.Injective φ := (algebraMap K (AlgebraicClosure K)).injective
  have hmap_ne : g.map φ ≠ 0 := (Polynomial.map_ne_zero_iff hφ_inj).mpr hg_ne
  have hmemR : ∀ l, l ∈ R ↔ Polynomial.aeval l (g.map φ) = 0 := by
    intro l
    have hae : Polynomial.aeval l (g.map φ) = Polynomial.eval l (g.map φ) := by
      rw [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id]
    rw [show R = (g.map φ).roots.toFinset from rfl, Multiset.mem_toFinset,
      Polynomial.mem_roots hmap_ne, Polynomial.IsRoot.def, hae]
  have hn : (orderOf b : K) ≠ 0 := by
    intro h
    exact hodd.not_two_dvd_nat ((CharP.cast_eq_zero_iff K 2 (orderOf b)).mp h)
  have hRcard : R.card = blockDegree A e := by
    rw [show R = (g.map φ).roots.toFinset from rfl, ggJSf2b_roots_card hn hg_dvd]
    exact hg_deg
  have h0R : (0 : AlgebraicClosure K) ∉ R := by
    intro h0
    have h0' : (0 : AlgebraicClosure K) ∈ (g.map φ).roots := by
      simpa only [R, Multiset.mem_toFinset] using h0
    have hroot : (g.map φ).IsRoot 0 := (Polynomial.mem_roots hmap_ne).mp h0'
    exact ggJSf2b_zero_not_root (orderOf_pos b).ne' hg_dvd hroot
  have hoff : ∀ l ∉ R, eigDimOn (b : Matrix ι ι K) e l = 0 :=
    ggJSf2b_off_R hodd hbe hEidem hg_dvd h_ann hmemR
  have hsum := ggJSf2b_sum_eigDimOn hodd hbe hEidem hg_dvd h_ann R hmemR h0R
  have hRpos : 0 < R.card := by
    rw [hRcard, ← hg_deg]
    exact hg_irred.natDegree_pos
  have hRne : R.Nonempty := Finset.card_pos.mp hRpos
  obtain ⟨l₀, hl₀⟩ := hRne.exists_mem
  have hroot_of_mem : ∀ {l : AlgebraicClosure K}, l ∈ R →
      (g.map φ).IsRoot l ∧ l ≠ 0 := by
    intro l hl
    refine ⟨(Polynomial.mem_roots hmap_ne).mp ?_, fun h => h0R (h ▸ hl)⟩
    simpa only [R, Multiset.mem_toFinset] using hl
  let m : ℕ := eigDimOn (b : Matrix ι ι K) e l₀
  refine ⟨R, m, hRcard, ?_, ?_, hoff⟩
  · have hsum_eq : (∑ l ∈ R, eigDimOn (b : Matrix ι ι K) e l) = R.card * m := by
      rw [show (∑ l ∈ R, eigDimOn (b : Matrix ι ι K) e l) =
          ∑ _l ∈ R, m from
        Finset.sum_congr rfl (fun l hl =>
          ggJSf2b_eigDimOn_eq_of_roots hodd hbe hEidem hg_irred
            (hroot_of_mem hl).1 (hroot_of_mem hl₀).1 (hroot_of_mem hl).2
              (hroot_of_mem hl₀).2)]
      rw [Finset.sum_const, nsmul_eq_mul]
      simp
    rw [hsum, ← hsum_eq]
  · intro l hl
    exact ggJSf2b_eigDimOn_eq_of_roots hodd hbe hEidem hg_irred
      (hroot_of_mem hl).1 (hroot_of_mem hl₀).1 (hroot_of_mem hl).2
        (hroot_of_mem hl₀).2

end CFSG.StandardType.ClassicalBlocks
