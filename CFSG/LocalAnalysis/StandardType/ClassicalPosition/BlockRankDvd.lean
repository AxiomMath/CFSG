module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockDegreeParity
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.GeoDualPair
public import Mathlib.LinearAlgebra.Matrix.Rank

public section

namespace CFSG.StandardType.ClassicalPosition

private lemma brd_rank_fromBlocks_one_zero (F : Type) [Field F] (r s : ℕ) :
    (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) F) 0 0
      (0 : Matrix (Fin s) (Fin s) F)).rank = r := by
  classical
  have h : (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) F) 0 0
      (0 : Matrix (Fin s) (Fin s) F)) =
      Matrix.diagonal (Sum.elim (fun _ : Fin r => (1 : F)) (fun _ : Fin s => (0 : F))) := by
    rw [← Matrix.fromBlocks_diagonal, Matrix.diagonal_one, Matrix.diagonal_zero]
  rw [h, Matrix.rank_diagonal, Fintype.card_subtype, Finset.card_filter, Fintype.sum_sum_type]
  simp

private lemma brd_rank_map_ringHom {F E : Type} [Field F] [Field E] (φ : F →+* E) {m : Type}
    [Fintype m] [DecidableEq m] (M : Matrix m m F) : (M.map φ).rank = M.rank := by
  classical
  obtain ⟨V, U, e, hV, hU, h⟩ := Matrix.exists_rank_normal_form M
  have hVf : IsUnit (V.map φ).det := (Matrix.isUnit_iff_isUnit_det _).mp (hV.map φ.mapMatrix)
  have hUf : IsUnit (U.map φ).det := (Matrix.isUnit_iff_isUnit_det _).mp (hU.map φ.mapMatrix)
  have hE : (M.map φ).rank = ((V.map φ) * (M.map φ) * (U.map φ)).rank := by
    rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ hUf,
      Matrix.rank_mul_eq_right_of_isUnit_det _ _ hVf]
  have h1 : (V * M * U).map φ =
      ((Matrix.fromBlocks (1 : Matrix (Fin M.rank) (Fin M.rank) F) 0 0
        (0 : Matrix (Fin (Fintype.card m - M.rank)) (Fin (Fintype.card m - M.rank)) F)).submatrix
          e e).map φ := by rw [h]
  simp only [Matrix.map_mul, ← Matrix.submatrix_map, Matrix.fromBlocks_map,
    Matrix.map_one _ (map_zero φ) (map_one φ), Matrix.map_zero _ (map_zero φ)] at h1
  rw [hE, h1, Matrix.rank_submatrix, brd_rank_fromBlocks_one_zero]

private lemma brd_rank_formAdj {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] (σ : F →+* F)
    {G : Matrix ι ι F} (hG : IsUnit G.det) (M : Matrix ι ι F) :
    Matrix.rank (formAdj σ G M) = Matrix.rank M := by
  have hX : (G⁻¹ * Matrix.transpose (M.map σ)).rank = M.rank := by
    rw [Matrix.rank_mul_eq_right_of_isUnit_det G⁻¹ (Matrix.transpose (M.map σ))
      (Matrix.isUnit_nonsing_inv_det G hG), Matrix.rank_transpose, brd_rank_map_ringHom σ M]
  unfold formAdj
  rw [Matrix.rank_mul_eq_left_of_isUnit_det G (G⁻¹ * Matrix.transpose (M.map σ)) hG, hX]

private lemma brd_adjoin_comm {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {S : Set (GL ι F)} (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') :
    ∀ a ∈ Algebra.adjoin F (Units.val '' S), ∀ b ∈ Algebra.adjoin F (Units.val '' S),
      Commute a b := by
  intro a ha b hb
  have hgen : (Units.val '' S : Set (Matrix ι ι F)) ⊆
      (Subalgebra.centralizer F (Units.val '' S) : Set (Matrix ι ι F)) := by
    rintro x ⟨s, hs, rfl⟩
    refine (Subalgebra.mem_centralizer_iff F).mpr ?_
    intro y hy
    rcases hy with ⟨s', hs', rfl⟩
    have h := congrArg (fun u : GL ι F => (u : Matrix ι ι F)) (hS s' hs' s hs).eq
    simpa [Units.val_mul] using h
  have hA : Algebra.adjoin F (Units.val '' S) ≤ Subalgebra.centralizer F (Units.val '' S) :=
    Algebra.adjoin_le hgen
  have ha' : a ∈ Subalgebra.centralizer F (Units.val '' S) := hA ha
  have hgen2 : (Units.val '' S : Set (Matrix ι ι F)) ⊆
      (Subalgebra.centralizer F ({a} : Set (Matrix ι ι F)) : Set (Matrix ι ι F)) := by
    rintro x ⟨s, hs, rfl⟩
    refine (Subalgebra.mem_centralizer_iff F).mpr ?_
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    have h := (Subalgebra.mem_centralizer_iff F).mp ha' (s : Matrix ι ι F) ⟨s, hs, rfl⟩
    exact h.symm
  have hA2 : Algebra.adjoin F (Units.val '' S) ≤
      Subalgebra.centralizer F ({a} : Set (Matrix ι ι F)) := Algebra.adjoin_le hgen2
  have hb' : b ∈ Subalgebra.centralizer F ({a} : Set (Matrix ι ι F)) := hA2 hb
  exact (Subalgebra.mem_centralizer_iff F).mp hb' a (Set.mem_singleton a)

private lemma brd_commute_adjoin {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {S : Set (GL ι F)} {g : GL ι F}
    (hg : ∀ s ∈ S, (g : Matrix ι ι F) * (s : Matrix ι ι F) =
      (s : Matrix ι ι F) * (g : Matrix ι ι F)) :
    ∀ a ∈ Algebra.adjoin F (Units.val '' S),
      (g : Matrix ι ι F) * a = a * (g : Matrix ι ι F) := by
  intro a ha
  refine Algebra.adjoin_induction
    (p := fun x _ => (g : Matrix ι ι F) * x = x * (g : Matrix ι ι F)) ?_ ?_ ?_ ?_ ha
  · rintro x ⟨s, hs, rfl⟩
    exact hg s hs
  · intro r
    rw [Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.smul_mul, mul_one, one_mul]
  · intro x y _ _ hx hy
    rw [mul_add, add_mul, hx, hy]
  · intro x y _ _ hx hy
    rw [← mul_assoc, hx, mul_assoc, hy, ← mul_assoc]

private lemma brd_neg_eq_self {ι F : Type}   [Ring F] [CharP F 2]
    (M : Matrix ι ι F) : -M = M := by
  ext i j
  rw [Matrix.neg_apply, CharTwo.neg_eq]

private lemma brd_formAdj_neg {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] (σ : F →+* F)
    (G a : Matrix ι ι F) : formAdj σ G (-a) = -formAdj σ G a := by
  have h : formAdj σ G (-a) + formAdj σ G a = 0 := by
    rw [← Geo.formAdj_add, neg_add_cancel]
    unfold formAdj
    rw [Matrix.map_zero σ (map_zero σ), Matrix.transpose_zero, Matrix.mul_zero, Matrix.zero_mul]
  exact eq_neg_of_add_eq_zero_left h

private lemma brd_formAdj_sub {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] (σ : F →+* F)
    (G a b : Matrix ι ι F) : formAdj σ G (a - b) = formAdj σ G a - formAdj σ G b := by
  rw [sub_eq_add_neg, Geo.formAdj_add, brd_formAdj_neg, sub_eq_add_neg]

private lemma brd_core {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] [Finite F] [CharP F 2]
    {S : Set (GL ι F)} (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hodd : ∀ s ∈ S, Odd (orderOf s)) {e : Matrix ι ι F}
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e) {g : GL ι F}
    (hgm : ∀ a ∈ Algebra.adjoin F (Units.val '' S),
      (g : Matrix ι ι F) * a = a * (g : Matrix ι ι F)) :
    blockDegree (Algebra.adjoin F (Units.val '' S)) e ∣
      Matrix.rank ((g : Matrix ι ι F) * e - e) := by
  classical
  let A : Subalgebra F (Matrix ι ι F) := Algebra.adjoin F (Units.val '' S)
  let V := ι → F
  let gM : Matrix ι ι F := (g : Matrix ι ι F)
  let T : Matrix ι ι F := gM * e - e
  have hTmul : T * e = T := by
    show (gM * e - e) * e = gM * e - e
    rw [Matrix.sub_mul, Matrix.mul_assoc, he.2.1.eq]
  have hsmulT : e * T = T := by
    show e * (gM * e - e) = gM * e - e
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, ← hgm e he.1, Matrix.mul_assoc, he.2.1.eq]
  have hcommT : ∀ a ∈ A, T * a = a * T := by
    intro a ha
    have hea : e * a = a * e := (brd_adjoin_comm hS e he.1 a ha).eq
    have hga : gM * a = a * gM := hgm a ha
    have h1 : gM * e * a = a * (gM * e) := by
      rw [Matrix.mul_assoc, hea, ← Matrix.mul_assoc, hga, Matrix.mul_assoc]
    show (gM * e - e) * a = a * (gM * e - e)
    rw [Matrix.sub_mul, Matrix.mul_sub, h1, hea]
  obtain ⟨K, hKfield, hKalg, hKfin, π, hπsurj, hπker, hπdeg⟩ := exists_blockField hS hodd he
  letI : Field K := hKfield
  letI : Algebra F K := hKalg
  letI : Finite K := hKfin
  have hcommP : (Units.val '' S : Set (Matrix ι ι F)).Pairwise Commute := by
    rintro a ⟨s, hs, rfl⟩ b ⟨s', hs', rfl⟩ _
    have h := hS s hs s' hs'
    show (s : Matrix ι ι F) * (s' : Matrix ι ι F) = (s' : Matrix ι ι F) * (s : Matrix ι ι F)
    rw [← Units.val_mul, ← Units.val_mul, h]
  letI : CommRing A := Algebra.adjoinCommRingOfComm F hcommP
  let I : Ideal A := RingHom.ker π.toRingHom
  let L : Submodule A V :=
    { carrier := Set.range T.mulVec
      zero_mem' := ⟨0, by simp [Matrix.mulVec]⟩
      add_mem' := by
        rintro x y ⟨u, rfl⟩ ⟨v, rfl⟩
        exact ⟨u + v, by rw [Matrix.mulVec_add]⟩
      smul_mem' := by
        rintro a x ⟨u, rfl⟩
        refine ⟨a • u, ?_⟩
        change T.mulVec ((a : Matrix ι ι F).mulVec u) = a • T.mulVec u
        rw [Matrix.mulVec_mulVec, hcommT a a.2, ← Matrix.mulVec_mulVec]
        rfl }
  have hTe' : T.mulVecLin = e.mulVecLin.comp T.mulVecLin := by
    conv_lhs => rw [← hsmulT]
    exact Matrix.mulVecLin_mul e T
  have hrange : LinearMap.range T.mulVecLin ≤ LinearMap.range e.mulVecLin := by
    rw [hTe']
    exact LinearMap.range_comp_le_range _ _
  have hLleW : ∀ x : V, x ∈ L → x ∈ LinearMap.range e.mulVecLin := by
    intro x hx
    obtain ⟨u, rfl⟩ := hx
    exact hrange (LinearMap.mem_range_self T.mulVecLin u)
  have hLrank : Module.finrank F L = Matrix.rank T := rfl
  let gmap : A →ₐ[F] Module.End F L := Algebra.lsmul (R := F) (A := A) (B := F) (M := L)
  have hker : ∀ a ∈ I, gmap a = 0 := by
    intro a ha
    have hae : (a : Matrix ι ι F) * e = 0 := (hπker a).mp ha
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    rw [show (gmap a) x = a • x from
      Algebra.lsmul_apply (R := F) (A := A) (B := F) (M := L) a x]
    change a • (x : V) = 0
    obtain ⟨y, hy⟩ := hLleW (x : V) x.2
    have hx : (x : V) = e.mulVec y := by
      rw [Matrix.mulVecLin_apply] at hy
      exact hy.symm
    rw [hx]
    rw [show a • e.mulVec y = ((a : Matrix ι ι F) * e).mulVec y from by
      rw [show a • e.mulVec y = (a : Matrix ι ι F).mulVec (e.mulVec y) from rfl,
        Matrix.mulVec_mulVec]]
    rw [hae, Matrix.zero_mulVec]
  let ρ' : A ⧸ I →ₐ[F] Module.End F L := Ideal.Quotient.liftₐ I gmap hker
  let e' : A ⧸ I →ₐ[F] K := Ideal.Quotient.liftₐ I π (fun a ha => ha)
  have hsurj' : Function.Surjective e' := by
    intro k
    obtain ⟨a, ha⟩ := hπsurj k
    exact ⟨Ideal.Quotient.mk I a, by change π a = k; exact ha⟩
  have hinj' : Function.Injective e' := by
    intro x y hxy
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    change π a = π b at hxy
    rw [Ideal.Quotient.eq]
    change π (a - b) = 0
    rw [map_sub, hxy, sub_self]
  let ee := AlgEquiv.ofBijective e' ⟨hinj', hsurj'⟩
  let ρ : K →ₐ[F] Module.End F L := ρ'.comp ee.symm.toAlgHom
  letI : Module K L := Module.compHom L ρ.toRingHom
  haveI hST : IsScalarTower F K L := by
    refine ⟨fun r k x => ?_⟩
    show ρ (r • k) x = r • (ρ k x)
    rw [Algebra.smul_def, map_mul, AlgHom.commutes]
    exact (Module.End.apply_isScalarTower.smul_assoc r (ρ k) x)
  have hfm : Module.finrank F K * Module.finrank K L = Module.finrank F L :=
    Module.finrank_mul_finrank F K L
  rw [← hπdeg, ← hLrank]
  exact ⟨Module.finrank K L, hfm.symm⟩

theorem blockDegree_dvd_rank_sub_one_of_glFixing {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    [Finite F] [CharP F 2] {S : Set (GL ι F)} (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hodd : ∀ s ∈ S, Odd (orderOf s)) {e : Matrix ι ι F}
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e) {g : GL ι F}
    (hgS : g ∈ Subgroup.centralizer S) (hge : g ∈ glFixing (1 - e)) :
    blockDegree (Algebra.adjoin F (Units.val '' S)) e ∣ Matrix.rank ((g : Matrix ι ι F) - 1) := by
  have hg : ∀ s ∈ S, (g : Matrix ι ι F) * (s : Matrix ι ι F) =
      (s : Matrix ι ι F) * (g : Matrix ι ι F) := by
    intro s hs
    have h := congrArg (fun u : GL ι F => (u : Matrix ι ι F))
      (Subgroup.mem_centralizer_iff.mp hgS s hs)
    simpa [Units.val_mul] using h.symm
  have hgm := brd_commute_adjoin hg
  have hdecomp : (g : Matrix ι ι F) - 1 = (g : Matrix ι ι F) * e - e := by
    have h : (g : Matrix ι ι F) * (1 - e) = 1 - e := hge
    rw [Matrix.mul_sub, Matrix.mul_one] at h
    calc (g : Matrix ι ι F) - 1
        = ((g : Matrix ι ι F) - (g : Matrix ι ι F) * e) +
            ((g : Matrix ι ι F) * e - 1) := by abel
      _ = (1 - e) + ((g : Matrix ι ι F) * e - 1) := by rw [h]
      _ = (g : Matrix ι ι F) * e - e := by abel
  rw [hdecomp]
  exact brd_core hS hodd he hgm

theorem two_mul_blockDegree_dvd_rank_sub_one_of_formAdj_ne {ι F : Type} [Fintype ι]
    [DecidableEq ι] [Field F] [Finite F] [CharP F 2] (σ : F →+* F) (hσ : ∀ x, σ (σ x) = x)
    {G : Matrix ι ι F} (hG : IsUnit G.det) (hGh : Matrix.transpose (G.map σ) = G)
    {S : Set (GL ι F)}
    (hSU : ∀ s ∈ S, Matrix.transpose ((s : Matrix ι ι F).map σ) * G * (s : Matrix ι ι F) = G)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix ι ι F} (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e)
    (hpair : formAdj σ G e ≠ e) {g : GL ι F} (hgS : g ∈ Subgroup.centralizer S)
    (hgiso : Matrix.transpose ((g : Matrix ι ι F).map σ) * G * (g : Matrix ι ι F) = G)
    (hge : g ∈ glFixing (1 - (e + formAdj σ G e))) :
    2 * blockDegree (Algebra.adjoin F (Units.val '' S)) e ∣
      Matrix.rank ((g : Matrix ι ι F) - 1) := by
  let A : Subalgebra F (Matrix ι ι F) := Algebra.adjoin F (Units.val '' S)
  let gM : Matrix ι ι F := (g : Matrix ι ι F)
  let gInv : Matrix ι ι F := ((g⁻¹ : GL ι F) : Matrix ι ι F)
  let e' : Matrix ι ι F := formAdj σ G e
  let Te : Matrix ι ι F := gM * e - e
  let Ts : Matrix ι ι F := gM * e' - e'
  have hg : ∀ s ∈ S, gM * (s : Matrix ι ι F) = (s : Matrix ι ι F) * gM := by
    intro s hs
    have h := congrArg (fun u : GL ι F => (u : Matrix ι ι F))
      (Subgroup.mem_centralizer_iff.mp hgS s hs)
    simpa [Units.val_mul, gM] using h.symm
  have hgm : ∀ a ∈ A, gM * a = a * gM := brd_commute_adjoin hg
  have hgInv_mem : g⁻¹ ∈ Subgroup.centralizer S := (Subgroup.centralizer S).inv_mem hgS
  have hg_inv : ∀ s ∈ S, gInv * (s : Matrix ι ι F) = (s : Matrix ι ι F) * gInv := by
    intro s hs
    have h := congrArg (fun u : GL ι F => (u : Matrix ι ι F))
      (Subgroup.mem_centralizer_iff.mp hgInv_mem s hs)
    simpa [Units.val_mul, gInv] using h.symm
  have hgm_inv : ∀ a ∈ A, gInv * a = a * gInv := brd_commute_adjoin hg_inv
  have he'A : e' ∈ A := Geo.formAdj_mem_adjoin σ hG hSU he.1
  have horth : e * e' = 0 ∧ e' * e = 0 :=
    Geo.mul_formAdj_eq_zero_of_dualPair σ hσ hG hGh hSU hS he hpair
  have he'_idem : e' * e' = e' := by
    show formAdj σ G e * formAdj σ G e = formAdj σ G e
    rw [← Geo.formAdj_mul σ hG, he.2.1.eq]
  have hcore : blockDegree A e ∣ Matrix.rank Te := brd_core hS hodd he hgm
  have hform : formAdj σ G Ts = e * gInv - e := by
    show formAdj σ G (gM * e' - e') = e * gInv - e
    rw [brd_formAdj_sub, Geo.formAdj_mul σ hG, Geo.formAdj_formAdj σ hσ hG hGh e,
      Geo.formAdj_eq_inv_of_isometry σ hG g hgiso]
  have hrel : e * gInv - e = gInv * Te := by
    have hcomm : e * gInv = gInv * e :=
      (hgm_inv e he.1).symm
    have hmul : gInv * Te = e - gInv * e := by
      dsimp only [Te, gInv, gM]
      rw [Matrix.mul_sub, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mul]
    rw [hmul, hcomm]
    exact (brd_neg_eq_self (gInv * e - e)).symm.trans (neg_sub (gInv * e) e)
  have hgInvDet : IsUnit (gInv.det) :=
    (Matrix.isUnit_iff_isUnit_det _).mp (g⁻¹).isUnit
  have hrankTs : Matrix.rank Ts = Matrix.rank Te := by
    have h1 : Matrix.rank Ts = Matrix.rank (formAdj σ G Ts) :=
      (brd_rank_formAdj σ hG Ts).symm
    rw [hform, hrel] at h1
    rw [h1, Matrix.rank_mul_eq_right_of_isUnit_det gInv Te hgInvDet]
  have hTe_e : Te * e = Te := by
    show (gM * e - e) * e = gM * e - e
    rw [Matrix.sub_mul, Matrix.mul_assoc, he.2.1.eq]
  have hTs_e : Ts * e = 0 := by
    show (gM * e' - e') * e = 0
    rw [Matrix.sub_mul, Matrix.mul_assoc, horth.2, Matrix.mul_zero, sub_zero]
  have hTe_e' : Te * e' = 0 := by
    show (gM * e - e) * e' = 0
    rw [Matrix.sub_mul, Matrix.mul_assoc, horth.1, Matrix.mul_zero, sub_zero]
  have hTs_e' : Ts * e' = Ts := by
    show (gM * e' - e') * e' = gM * e' - e'
    rw [Matrix.sub_mul, Matrix.mul_assoc, he'_idem]
  have hTe : Te = e * Te := by
    show gM * e - e = e * (gM * e - e)
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, ← hgm e he.1, Matrix.mul_assoc, he.2.1.eq]
  have hTs : Ts = e' * Ts := by
    show gM * e' - e' = e' * (gM * e' - e')
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, ← hgm e' he'A, Matrix.mul_assoc, he'_idem]
  have hWe : LinearMap.range Te.mulVecLin ≤ LinearMap.range e.mulVecLin := by
    have h : Te.mulVecLin = e.mulVecLin.comp Te.mulVecLin := by
      conv_lhs => rw [hTe]
      exact Matrix.mulVecLin_mul e Te
    rw [h]
    exact LinearMap.range_comp_le_range _ _
  have hWs : LinearMap.range Ts.mulVecLin ≤ LinearMap.range e'.mulVecLin := by
    have h : Ts.mulVecLin = e'.mulVecLin.comp Ts.mulVecLin := by
      conv_lhs => rw [hTs]
      exact Matrix.mulVecLin_mul e' Ts
    rw [h]
    exact LinearMap.range_comp_le_range _ _
  have hbot : LinearMap.range e.mulVecLin ⊓ LinearMap.range e'.mulVecLin = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro z ⟨hz1, hz2⟩
    obtain ⟨x, hx⟩ := hz1
    obtain ⟨y, hy⟩ := hz2
    rw [Matrix.mulVecLin_apply] at hx hy
    have hz_e : e.mulVec z = 0 := by
      calc e.mulVec z = e.mulVec (e'.mulVec y) := by rw [hy.symm]
        _ = (e * e').mulVec y := by rw [Matrix.mulVec_mulVec]
        _ = 0 := by rw [horth.1, Matrix.zero_mulVec]
    have hz_self : e.mulVec z = z := by
      calc e.mulVec z = e.mulVec (e.mulVec x) := by rw [hx.symm]
        _ = (e * e).mulVec x := by rw [Matrix.mulVec_mulVec]
        _ = e.mulVec x := by rw [he.2.1.eq]
        _ = z := hx
    rwa [hz_self] at hz_e
  have hbotT : LinearMap.range Te.mulVecLin ⊓ LinearMap.range Ts.mulVecLin = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro z ⟨hz1, hz2⟩
    have hz : z ∈ LinearMap.range e.mulVecLin ⊓ LinearMap.range e'.mulVecLin :=
      ⟨hWe hz1, hWs hz2⟩
    rwa [hbot, Submodule.mem_bot] at hz
  have hsum_e : (Te + Ts) * e = Te := by
    rw [Matrix.add_mul, hTe_e, hTs_e, add_zero]
  have hsum_e' : (Te + Ts) * e' = Ts := by
    rw [Matrix.add_mul, hTe_e', hTs_e', zero_add]
  have hsup : LinearMap.range (Te + Ts).mulVecLin =
      LinearMap.range Te.mulVecLin ⊔ LinearMap.range Ts.mulVecLin := by
    refine le_antisymm ?_ ?_
    · rw [Matrix.mulVecLin_add]
      exact LinearMap.range_add_le Te.mulVecLin Ts.mulVecLin
    · apply sup_le
      · rintro y ⟨x, rfl⟩
        refine LinearMap.mem_range.mpr ⟨e.mulVec x, ?_⟩
        change (Te + Ts).mulVec (e.mulVec x) = Te.mulVec x
        rw [Matrix.mulVec_mulVec, hsum_e]
      · rintro y ⟨x, rfl⟩
        refine LinearMap.mem_range.mpr ⟨e'.mulVec x, ?_⟩
        change (Te + Ts).mulVec (e'.mulVec x) = Ts.mulVec x
        rw [Matrix.mulVec_mulVec, hsum_e']
  have hrank_add : Matrix.rank (Te + Ts) = Matrix.rank Te + Matrix.rank Ts := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq
      (LinearMap.range Te.mulVecLin) (LinearMap.range Ts.mulVecLin)
    rw [hbotT, ← hsup, finrank_bot, add_zero] at h
    exact h
  have hdecomp : gM - 1 = Te + Ts := by
    have h : gM * (1 - (e + e')) = 1 - (e + e') := hge
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_add] at h
    show gM - 1 = (gM * e - e) + (gM * e' - e')
    calc gM - 1
        = (gM - (gM * e + gM * e')) + ((gM * e + gM * e') - 1) := by abel
      _ = (1 - (e + e')) + ((gM * e + gM * e') - 1) := by rw [h]
      _ = (gM * e - e) + (gM * e' - e') := by abel
  have hrank : Matrix.rank (gM - 1) = 2 * Matrix.rank Te := by
    rw [hdecomp, hrank_add, hrankTs]
    ring
  rw [hrank]
  exact Nat.mul_dvd_mul_left 2 hcore

end CFSG.StandardType.ClassicalPosition
