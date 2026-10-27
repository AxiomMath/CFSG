module

public import CFSG.LocalAnalysis.StandardType.GGQ2NbrD5Frame
public import CFSG.LocalAnalysis.StandardType.GGQ2NbrD5Forced
public import CFSG.LocalAnalysis.StandardType.GGQTwoDFourLeafNorm
public import CFSG.LocalAnalysis.StandardType.GGQTwoFinishGen

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module CFSG.StandardType.GGQ2NbrD5

private lemma ggQ2NbG_D5_det :
    ((CartanMatrix.D 5).map (Int.cast : ℤ → ZMod 3)).det ≠ 0 := by
  have hmat : (CartanMatrix.D 5).map (Int.cast : ℤ → ZMod 3) =
      !![2, 2, 0, 0, 0;
         2, 2, 2, 0, 0;
         0, 2, 2, 2, 2;
         0, 0, 2, 2, 0;
         0, 0, 2, 0, 2] := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [hmat]
  have hBA : (!![1, 1, 1, 2, 2;
                 1, 2, 2, 1, 1;
                 1, 2, 0, 0, 0;
                 2, 1, 0, 2, 0;
                 2, 1, 0, 0, 2] : Matrix (Fin 5) (Fin 5) (ZMod 3)) *
             (!![2, 2, 0, 0, 0;
                2, 2, 2, 0, 0;
                0, 2, 2, 2, 2;
                0, 0, 2, 2, 0;
                0, 0, 2, 0, 2] : Matrix (Fin 5) (Fin 5) (ZMod 3)) = 1 := by
    decide
  exact Matrix.det_ne_zero_of_left_inverse hBA

private lemma ggQ2NbG_D4_det :
    ((CartanMatrix.D 4).map (Int.cast : ℤ → ZMod 3)).det ≠ 0 := by
  have hmat : (CartanMatrix.D 4).map (Int.cast : ℤ → ZMod 3) =
      !![2, 2, 0, 0; 2, 2, 2, 2; 0, 2, 2, 0; 0, 2, 0, 2] := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [hmat]
  decide

private lemma ggQ2NbG_det_cartan {ι : Type} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι ℤ) (e : Fin 5 ≃ ι)
    (hecart : ∀ i j, C (e i) (e j) = CartanMatrix.D 5 i j) :
    ((C.det : ℤ) : ZMod 3) ≠ 0 := by
  have hmap : C.map (Int.castRingHom (ZMod 3)) =
      ((CartanMatrix.D 5).map (Int.castRingHom (ZMod 3))).submatrix
        (⇑e.symm) (⇑e.symm) := by
    ext i j
    have h := congrArg (fun z : ℤ => (z : ZMod 3)) (hecart (e.symm i) (e.symm j))
    simpa only [Matrix.map_apply, Matrix.submatrix_apply, Equiv.apply_symm_apply,
      Int.coe_castRingHom] using h
  have hdet : (C.map (Int.castRingHom (ZMod 3))).det =
      ((CartanMatrix.D 5).map (Int.castRingHom (ZMod 3))).det := by
    rw [hmap, Matrix.det_submatrix_equiv_self]
  have h1 : ((C.det : ℤ) : ZMod 3) = (C.map (Int.castRingHom (ZMod 3))).det := by
    simpa using RingHom.map_det (Int.castRingHom (ZMod 3)) C
  rw [h1, hdet]
  exact ggQ2NbG_D5_det

private lemma ggQ2NbG_coxeter_of_D5 {ι : Type} (N : CoxeterMatrix ι) (C : Matrix ι ι ℤ)
    (hC : GGIntCartan N C) (e : Fin 5 ≃ ι)
    (he : ∀ i j, C (e i) (e j) = CartanMatrix.D 5 i j) :
    N = (ggCoxeterMatrixD 5).reindex e := by
  ext a b
  obtain ⟨i, rfl⟩ := e.surjective a
  obtain ⟨j, rfl⟩ := e.surjective b
  rw [CoxeterMatrix.reindex_apply, e.symm_apply_apply, e.symm_apply_apply,
    ggCoxeterMatrixD_apply]
  by_cases hij : i = j
  · subst hij
    simp
  · rw [if_neg hij]
    have h1 := he i j
    have h2 := he j i
    have hne : e i ≠ e j := fun h => hij (e.injective h)
    have h3 := hC.2 (e i) (e j) hne
    have hD : CartanMatrix.D 5 i j = 0 ∨ CartanMatrix.D 5 i j = -1 := by
      revert hij
      fin_cases i <;> fin_cases j <;> decide
    have hDji : CartanMatrix.D 5 j i = 0 ∨ CartanMatrix.D 5 j i = -1 := by
      revert hij
      fin_cases i <;> fin_cases j <;> decide
    rcases h3 with ⟨hm, hc, -⟩ | ⟨hm, hc, -⟩ | ⟨hm, hp, -⟩ | ⟨hm, hp, -⟩
    · rw [hm, if_pos (by rw [← h1, hc])]
    · rw [hm, if_neg (by rw [← h1, hc]; norm_num)]
    · exfalso
      rw [h1, h2] at hp
      rcases hD with h | h <;> rcases hDji with h' | h' <;> rw [h, h'] at hp <;>
        norm_num at hp
    · exfalso
      rw [h1, h2] at hp
      rcases hD with h | h <;> rcases hDji with h' | h' <;> rw [h, h'] at hp <;>
        norm_num at hp

private lemma ggQ2NbG_perm_one (γ : Equiv.Perm (Fin 4))
    (hγ : ∀ i j, CartanMatrix.D 4 (γ i) (γ j) = CartanMatrix.D 4 i j) (_h0 : γ 0 = 0) :
    γ 1 = 1 := by
  have hrel : ∀ i j, (1 : ZMod 3) * (CartanMatrix.D 4 i j : ZMod 3) =
      1 * (CartanMatrix.D 4 (γ i) (γ j) : ZMod 3) := by
    intro i j
    rw [hγ i j]
  exact (ggQ2g_scaledD4 γ (fun _ => 1) (fun _ => one_ne_zero) hrel).2

private lemma ggQ2NbG_perm_eq (γ : Equiv.Perm (Fin 4))
    (hγ : ∀ i j, CartanMatrix.D 4 (γ i) (γ j) = CartanMatrix.D 4 i j)
    (h0 : γ 0 = 0) (hne : γ ≠ 1) : γ = Equiv.swap 2 3 := by
  have h1 : γ 1 = 1 := ggQ2NbG_perm_one γ hγ h0
  have key3 : ∀ v : Fin 4, v ≠ 0 → v ≠ 1 → v ≠ 2 → v = 3 := by decide
  have key2 : ∀ v : Fin 4, v ≠ 0 → v ≠ 1 → v ≠ 3 → v = 2 := by decide
  have h2ne : γ 2 ≠ 2 := by
    intro h
    apply hne
    refine Equiv.ext fun i => ?_
    fin_cases i
    · show γ 0 = (1 : Equiv.Perm (Fin 4)) 0
      rw [h0]
      rfl
    · show γ 1 = (1 : Equiv.Perm (Fin 4)) 1
      rw [h1]
      rfl
    · show γ 2 = (1 : Equiv.Perm (Fin 4)) 2
      rw [h]
      rfl
    · show γ 3 = (1 : Equiv.Perm (Fin 4)) 3
      have h3 : γ 3 = 3 := by
        apply key3
        · intro hh
          exact absurd (γ.injective (show γ 3 = γ 0 by rw [h0]; exact hh)) (by decide)
        · intro hh
          exact absurd (γ.injective (show γ 3 = γ 1 by rw [h1]; exact hh)) (by decide)
        · intro hh
          exact absurd (γ.injective (show γ 3 = γ 2 by rw [h]; exact hh)) (by decide)
      rw [h3]
      rfl
  have h2 : γ 2 = 3 := by
    apply key3
    · intro h
      exact absurd (γ.injective (show γ 2 = γ 0 by rw [h0]; exact h)) (by decide)
    · intro h
      exact absurd (γ.injective (show γ 2 = γ 1 by rw [h1]; exact h)) (by decide)
    · exact h2ne
  have h3 : γ 3 = 2 := by
    apply key2
    · intro h
      exact absurd (γ.injective (show γ 3 = γ 0 by rw [h0]; exact h)) (by decide)
    · intro h
      exact absurd (γ.injective (show γ 3 = γ 1 by rw [h1]; exact h)) (by decide)
    · intro h
      exact absurd (γ.injective (show γ 3 = γ 2 by rw [h2]; exact h)) (by decide)
  refine Equiv.ext fun i => ?_
  fin_cases i
  · show γ 0 = Equiv.swap 2 3 0
    rw [h0]
    exact (Equiv.swap_apply_of_ne_of_ne (a := 2) (b := 3) (x := 0)
      (by decide) (by decide)).symm
  · show γ 1 = Equiv.swap 2 3 1
    rw [h1]
    exact (Equiv.swap_apply_of_ne_of_ne (a := 2) (b := 3) (x := 1)
      (by decide) (by decide)).symm
  · show γ 2 = Equiv.swap 2 3 2
    rw [h2]
    exact (Equiv.swap_apply_left 2 3).symm
  · show γ 3 = Equiv.swap 2 3 3
    rw [h3]
    exact (Equiv.swap_apply_right 2 3).symm

private lemma ggQ2NbG_swap_four {ι : Type} [DecidableEq ι] (e : Fin 5 ≃ ι) (j : Fin 4) :
    e (Equiv.swap 2 3 j).succ = Equiv.swap (e 3) (e 4) (e j.succ) := by
  fin_cases j <;>
    simp [Equiv.swap_apply_def, e.injective.eq_iff]

theorem ggQ2NbrD5Gamma_holds (hLB : GGLBalanceInput)
    (hP : GGStdSubPrimeInput) (h5 : GGQTwoCentralizerInput) : GGQ2NbrD5GammaInput := by
  intro G _ _ p B Bs x L D J hS hp hI1 hpp y K hnb hF u hu φ hφ hφu
  subst hp
  classical
  obtain ⟨M, e, hecart, he0, hb, hlin, hspan, hJ3, hZ, hAJ, -, hSC⟩ := hF
  have hH : GGCorFiveTwentyHyp 3 B Bs x L D J := hS.1
  have hAJS : ggAutomizer J Bs ≠ ⊥ := ggQ2_ajOfSetting hP h5 hS
  have hK1 : GGQTwoK1 3 B Bs x D J := ggQ2_K1_of_I1 hLB hP hH hI1
  have hG0K : K ≤ ggG0 3 B x L D J := le_ggG0_of_ggNbr hnb
  have hG0L : L ≤ ggG0 3 B x L D J := le_ggG0_left _ _ _ _ _ _
  have hG0LK : L ⊔ K ≤ ggG0 3 B x L D J := sup_le hG0L hG0K
  have : Finite M.V := Finite.of_equiv (Additive ↥Bs) M.model.toEquiv
  have : FiniteDimensional (ZMod 3) M.V := Module.Finite.of_finite
  have hbas : M.toLin.Basis := by
    refine ⟨hlin, ?_⟩
    have h := (linearIndependent_iff_card_eq_finrank_span (R := ZMod 3)
      (b := M.coroot)).mp hlin
    rw [Set.finrank, hspan, finrank_top] at h
    exact h
  have hind : LinearIndependent (ZMod 3) (fun i : {k // k ≠ M.a} => M.coroot i) :=
    hlin.comp (fun i : {k // k ≠ M.a} => (i : M.ι)) Subtype.val_injective
  have hnd : ((M.cartan.det : ℤ) : ZMod 3) ≠ 0 := ggQ2NbG_det_cartan M.cartan e hecart
  let fsub : Fin 4 → {k // k ≠ M.a} := fun i =>
    ⟨e i.succ, by
      rw [he0]
      exact e.injective.ne (Fin.succ_ne_zero i)⟩
  have hf_bij : Function.Bijective fsub := by
    constructor
    · intro a b hab
      have h1 : e a.succ = e b.succ := congrArg Subtype.val hab
      exact Fin.succ_injective 4 (e.injective h1)
    · rintro ⟨i, hi⟩
      obtain ⟨t, rfl⟩ := e.surjective i
      have ht : t ≠ 0 := by
        intro h
        exact hi (by rw [h]; exact he0.symm)
      obtain ⟨j, hj⟩ := Fin.exists_succ_eq_of_ne_zero ht
      exact ⟨j, Subtype.ext (by show e j.succ = e t; rw [hj])⟩
  let f : Fin 4 ≃ {k // k ≠ M.a} := Equiv.ofBijective fsub hf_bij
  have hf : ∀ i j, M.cartan (f i) (f j) = CartanMatrix.D 4 i j := by
    intro i j
    have h1 : M.cartan (f i) (f j) = CartanMatrix.D 5 i.succ j.succ :=
      hecart i.succ j.succ
    rw [h1, ggQ2xa_D_succ_succ (k := 2) (by norm_num)]
  have hdet : ((M.cartan.submatrix (fun i : {k // k ≠ M.a} => (i : M.ι))
      (fun i : {k // k ≠ M.a} => (i : M.ι))).det : ZMod 3) ≠ 0 := by
    have hC : M.cartan.submatrix (fun i : {k // k ≠ M.a} => (i : M.ι))
        (fun i : {k // k ≠ M.a} => (i : M.ι)) =
        (CartanMatrix.D 4).submatrix (⇑f.symm) (⇑f.symm) := by
      ext i j
      have h := hf (f.symm i) (f.symm j)
      simpa only [Matrix.submatrix_apply, Equiv.apply_symm_apply] using h
    have hmap : (M.cartan.submatrix (fun i : {k // k ≠ M.a} => (i : M.ι))
        (fun i : {k // k ≠ M.a} => (i : M.ι))).map (Int.castRingHom (ZMod 3)) =
        ((CartanMatrix.D 4).map (Int.castRingHom (ZMod 3))).submatrix
          (⇑f.symm) (⇑f.symm) := by
      rw [hC]
      rfl
    have h1 : ((M.cartan.submatrix (fun i : {k // k ≠ M.a} => (i : M.ι))
        (fun i : {k // k ≠ M.a} => (i : M.ι))).det : ZMod 3) =
        ((M.cartan.submatrix (fun i : {k // k ≠ M.a} => (i : M.ι))
        (fun i : {k // k ≠ M.a} => (i : M.ι))).map (Int.castRingHom (ZMod 3))).det := by
      simpa using RingHom.map_det (Int.castRingHom (ZMod 3))
        (M.cartan.submatrix (fun i : {k // k ≠ M.a} => (i : M.ι))
          (fun i : {k // k ≠ M.a} => (i : M.ι)))
    rw [h1, hmap, Matrix.det_submatrix_equiv_self]
    exact ggQ2NbG_D4_det
  have hdet' : (Matrix.of fun i j : {k // k ≠ M.a} => (M.cartan i j : ZMod 3)).det ≠ 0 := by
    have hmap : (Matrix.of fun i j : {k // k ≠ M.a} => (M.cartan i j : ZMod 3)) =
        (Int.castRingHom (ZMod 3)).mapMatrix
          (M.cartan.submatrix (fun i : {k // k ≠ M.a} => (i : M.ι))
            (fun i : {k // k ≠ M.a} => (i : M.ι))) := rfl
    rw [hmap, ← RingHom.map_det]
    exact hdet
  have hDxy : D = Subgroup.closure ({y, x} : Set G) := by
    rw [hnb.2.1, Set.pair_comm]
  have finK : (∃ w' ∈ M.parabL {k | k ≠ M.a}, ∀ v ∈ Submodule.span (ZMod 3) {M.xV, M.yV},
      w' (ggLin (p := 3) M.model φ v) ∈ Submodule.span (ZMod 3) {M.xV, M.yV}) →
      φ ∈ ggAutomizer (Subgroup.normalizer (ggG0 3 B x L D J : Set G)) Bs := by
    intro h
    obtain ⟨ψ, hψ, hD⟩ := ggQ2xa_bridge M hDxy (le_of_eq M.parabL_L) h
    exact ggQ2_finish_of_le hLB hP hS hAJS hK1 hnb hG0K hφ hψ hD
  have finW : (∃ w' ∈ M.toLin.weyl, ∀ v ∈ Submodule.span (ZMod 3) {M.xV, M.yV},
      w' (ggLin (p := 3) M.model φ v) ∈ Submodule.span (ZMod 3) {M.xV, M.yV}) →
      φ ∈ ggAutomizer (Subgroup.normalizer (ggG0 3 B x L D J : Set G)) Bs := by
    intro h
    have hH' : M.parabL Set.univ ≤
        (ggAutomizer (L ⊔ K) Bs).map (ggLin (p := 3) M.model) := by
      have h1 := M.weyl_le
      rwa [sup_eq_right.mpr le_sup_right] at h1
    obtain ⟨ψ, hψ, hD⟩ := ggQ2xa_bridge (S := Set.univ) M hDxy hH' h
    exact ggQ2_finish_of_le hLB hP hS hAJS hK1 hnb hG0LK hφ hψ hD
  have hφx : φ ⟨y, M.hx⟩ ∈ Subgroup.zpowers (⟨y, M.hx⟩ : ↥Bs) :=
    ggQ2xa_x_stable M.hx hu hφu
  have hφxV : ggLin (p := 3) M.model φ M.xV ∈ Submodule.span (ZMod 3) {M.xV} := by
    have h1 : ggLin (p := 3) M.model φ M.xV = M.model (Additive.ofMul (φ ⟨y, M.hx⟩)) := by
      rw [GGQTwoAmbModel.xV, ggLin_apply_ofMul]
    rw [h1]
    exact ggQ2xa_model_mem_span M (φ ⟨y, M.hx⟩) ⟨y, M.hx⟩ hφx
  have hfix1 : ∀ v, (∀ g ∈ M.toLin.parab {k | k ≠ M.a}, g v = v) ↔
      v ∈ Submodule.span (ZMod 3) {M.xV} := M.fixed_lin
  have hxα : ∀ j : {k // k ≠ M.a}, M.root j M.xV = 0 :=
    ggQ2g_alpha_fixed rfl M.toLin M.a M.xV hfix1
  have hy1 : y ≠ 1 := hnb.1.2.2.1
  have hx0 : M.xV ≠ 0 := by
    intro h
    have h0 : Additive.ofMul (⟨y, M.hx⟩ : ↥Bs) = 0 :=
      M.model.injective (by rw [map_zero]; exact h)
    have h1 : (⟨y, M.hx⟩ : ↥Bs) = 1 := Additive.ofMul.injective (by simpa using h0)
    exact hy1 (Subtype.ext_iff.mp h1)
  have hker0 : ∀ κ : {k // k ≠ M.a} → ZMod 3,
      (∀ i : {k // k ≠ M.a}, ∑ j : {k // k ≠ M.a}, (M.cartan i j : ZMod 3) * κ j = 0) →
        κ = 0 := by
    intro κ hκ
    refine Matrix.eq_zero_of_mulVec_eq_zero hdet' (funext fun i => ?_)
    simpa [Matrix.mulVec, dotProduct] using hκ i
  have hxs : M.xV ∉
      Submodule.span (ZMod 3) (Set.range fun i : {k // k ≠ M.a} => M.coroot i) := by
    intro hmem
    obtain ⟨κ, hκ⟩ := (Submodule.mem_span_range_iff_exists_fun (R := ZMod 3)).mp hmem
    have hκk : ∀ i : {k // k ≠ M.a},
        ∑ j : {k // k ≠ M.a}, (M.cartan i j : ZMod 3) * κ j = 0 := by
      intro i
      have h := hxα i
      rw [← hκ, map_sum] at h
      simpa only [map_smul, smul_eq_mul, M.pairing, mul_comm] using h
    apply hx0
    rw [← hκ, hker0 κ hκk]
    simp
  have hcardΛ : Fintype.card {k // k ≠ M.a} = Fintype.card M.ι - 1 := Set.card_ne_eq M.a
  have hcardι : 0 < Fintype.card M.ι := Fintype.card_pos_iff.mpr ⟨M.a⟩
  have hdimeq : Module.finrank (ZMod 3) M.V = Fintype.card {k // k ≠ M.a} + 1 := by
    have hb2 : Fintype.card M.ι = Module.finrank (ZMod 3) M.V := hbas.2
    rw [← hb2, hcardΛ]
    omega
  have hV : Submodule.span (ZMod 3)
      (insert M.xV (Set.range fun i : {k // k ≠ M.a} => M.coroot i)) = ⊤ := by
    have hspan' := (hind.option hxs).span_eq_top_of_card_eq_finrank'
      (by rw [Fintype.card_option, hdimeq])
    rw [Option.range_eq] at hspan'
    exact hspan'
  obtain ⟨π, c, hc0, hπ, w, hw, hT⟩ :=
    ggQ2_tbwNormNbrAmb_of_dFourLeaf hLB hP h5 hS rfl hI1 hnb M hind f hf hφ hφxV
  have hScaled : M.toLin.ScaledAut M.a π (fun _ => 1) := by
    simp only [GGQ2Lin.ScaledAut, GGQTwoAmbModel.toLin]
    refine ⟨fun _ => one_ne_zero, fun i j => ?_⟩
    simp only [one_mul]
    exact congrArg (fun z : ℤ => (z : ZMod 3)) (hπ i j).symm
  have hT1 : ∀ i : {k // k ≠ M.a},
      ggLin (p := 3) M.model φ (M.coroot i) = c • (1 : ZMod 3) • w (M.coroot (π i)) := by
    intro i
    simpa using hT i
  let t : {k // k ≠ M.a} := ⟨e 1, by
    rw [he0]
    exact e.injective.ne (by decide)⟩
  by_cases hπb : π ⟨M.b, M.a_ne_b.symm⟩ = ⟨M.b, M.a_ne_b.symm⟩
  ·
    have hxa : M.root M.a M.xV ≠ 0 := by
      intro h0
      apply hx0
      have hall : ∀ i : M.ι, M.root i M.xV = 0 := by
        intro i
        by_cases hi : i = M.a
        · rw [hi]
          exact h0
        · exact hxα ⟨i, hi⟩
      have hspanι : Submodule.span (ZMod 3) (Set.range M.coroot) = ⊤ := hspan
      have hmem : M.xV ∈ Submodule.span (ZMod 3) (Set.range M.coroot) := by
        rw [hspanι]
        exact Submodule.mem_top
      obtain ⟨κ, hκ⟩ := (Submodule.mem_span_range_iff_exists_fun (R := ZMod 3)).mp hmem
      have hκk : ∀ i : M.ι, ∑ j : M.ι, (M.cartan i j : ZMod 3) * κ j = 0 := by
        intro i
        have h := hall i
        rw [← hκ, map_sum] at h
        simpa only [map_smul, smul_eq_mul, M.pairing, mul_comm] using h
      have hdetι : (Matrix.of fun i j : M.ι => (M.cartan i j : ZMod 3)).det ≠ 0 := by
        have hmap : (Matrix.of fun i j : M.ι => (M.cartan i j : ZMod 3)) =
            (Int.castRingHom (ZMod 3)).mapMatrix M.cartan := rfl
        rw [hmap, ← RingHom.map_det]
        exact hnd
      have hκ0 : κ = 0 := Matrix.eq_zero_of_mulVec_eq_zero hdetι
        (funext fun i => by simpa [Matrix.mulVec, dotProduct] using hκk i)
      rw [← hκ, hκ0]
      simp
    obtain ⟨t', ht⟩ : ∃ t' : ZMod 3, t' = M.root M.a M.yV * (M.root M.a M.xV)⁻¹ := ⟨_, rfl⟩
    have hyα' : ∀ j : {k // k ≠ M.b}, M.root j (M.yV - t' • M.xV) = 0 := by
      rintro ⟨j, hjb⟩
      rw [map_sub, map_smul, smul_eq_mul]
      by_cases hja : j = M.a
      · subst hja
        show M.root M.a M.yV - t' * M.root M.a M.xV = 0
        rw [ht, mul_assoc, inv_mul_cancel₀ hxa, mul_one, sub_self]
      · have h1 : M.root j M.yV = 0 := M.root_yV rfl j hja hjb
        have h2 : M.root j M.xV = 0 := hxα ⟨j, hja⟩
        show M.root j M.yV - t' * M.root j M.xV = 0
        rw [h1, h2]
        ring
    obtain ⟨w', hw', hstab⟩ :=
      ggQ2_lemmaA M.toLin M.xV (M.yV - t' • M.xV) hxα hyα' hV hdet hScaled hπb hw hT1 hφxV
    have hspan_eq : Submodule.span (ZMod 3) {M.xV, M.yV - t' • M.xV} =
        Submodule.span (ZMod 3) {M.xV, M.yV} := by
      have hx1 : M.xV ∈ Submodule.span (ZMod 3) ({M.xV, M.yV} : Set M.V) :=
        Submodule.subset_span (by simp)
      have hy1' : M.yV ∈ Submodule.span (ZMod 3) ({M.xV, M.yV} : Set M.V) :=
        Submodule.subset_span (by simp)
      have hx2 : M.xV ∈ Submodule.span (ZMod 3) ({M.xV, M.yV - t' • M.xV} : Set M.V) :=
        Submodule.subset_span (by simp)
      have hy2 : M.yV - t' • M.xV ∈
          Submodule.span (ZMod 3) ({M.xV, M.yV - t' • M.xV} : Set M.V) :=
        Submodule.subset_span (by simp)
      apply le_antisymm
      · rw [Submodule.span_le]
        rintro v hv
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
        rcases hv with rfl | rfl
        · exact hx1
        · exact Submodule.sub_mem _ hy1' (Submodule.smul_mem _ _ hx1)
      · rw [Submodule.span_le]
        rintro v hv
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
        rcases hv with rfl | rfl
        · exact hx2
        · have hmem : (M.yV - t' • M.xV) + t' • M.xV ∈
              Submodule.span (ZMod 3) ({M.xV, M.yV - t' • M.xV} : Set M.V) :=
            Submodule.add_mem _ hy2 (Submodule.smul_mem _ _ hx2)
          rwa [sub_add_cancel] at hmem
    refine finK ⟨w', hw', fun v hv => ?_⟩
    rw [← hspan_eq] at hv ⊢
    exact hstab v hv
  · by_cases hsm : M.toLin.ScalarModW M.a π (fun _ => 1)
    ·
      obtain ⟨w', hw', ε, hε⟩ := ggQ2_scalarStable M.toLin M.xV hxα hV hsm hw hT1 hφxV
      have hstab : ∀ v ∈ Submodule.span (ZMod 3) {M.xV, M.yV},
          w' (ggLin (p := 3) M.model φ v) ∈ Submodule.span (ZMod 3) {M.xV, M.yV} := by
        intro v hv
        obtain ⟨s', hs⟩ := hε v
        have hs' : w' (ggLin (p := 3) M.model φ v) = ε • v + s' • M.xV := hs
        rw [hs']
        have hx : M.xV ∈ Submodule.span (ZMod 3) ({M.xV, M.yV} : Set M.V) :=
          Submodule.subset_span (by simp)
        exact Submodule.add_mem _ (Submodule.smul_mem _ ε hv) (Submodule.smul_mem _ s' hx)
      exact finK ⟨w', hw', hstab⟩
    · by_cases hπt : π t = t
      ·
        have hcox' : M.toLin.coxeter = (ggCoxeterMatrixD 5).reindex e :=
          ggQ2NbG_coxeter_of_D5 M.coxeter M.cartan M.isCartan e hecart
        let γ : Equiv.Perm (Fin 4) := (f.trans π).trans f.symm
        have hγ : ∀ i j, CartanMatrix.D 4 (γ i) (γ j) = CartanMatrix.D 4 i j := by
          intro i j
          rw [← hf (γ i) (γ j), ← hf i j]
          rw [show f (γ i) = π (f i) from Equiv.apply_symm_apply f (π (f i)),
            show f (γ j) = π (f j) from Equiv.apply_symm_apply f (π (f j))]
          exact hπ (f i) (f j)
        have h0 : γ 0 = 0 := by
          change f.symm (π (f 0)) = 0
          have hft : f 0 = t := Subtype.ext rfl
          rw [hft, hπt, ← hft]
          exact Equiv.symm_apply_apply f 0
        have hne : γ ≠ 1 := by
          intro h1
          apply hπb
          have hγb : γ (f.symm ⟨M.b, M.a_ne_b.symm⟩) = f.symm ⟨M.b, M.a_ne_b.symm⟩ := by
            rw [h1]; rfl
          have h2 : f (γ (f.symm ⟨M.b, M.a_ne_b.symm⟩)) =
              π (f (f.symm ⟨M.b, M.a_ne_b.symm⟩)) :=
            Equiv.apply_symm_apply f (π (f (f.symm ⟨M.b, M.a_ne_b.symm⟩)))
          rw [hγb, Equiv.apply_symm_apply] at h2
          exact h2.symm
        have hγswap : γ = Equiv.swap 2 3 := ggQ2NbG_perm_eq γ hγ h0 hne
        have hπapply : ∀ i : {k // k ≠ M.a}, ((π i : {k // k ≠ M.a}) : M.ι) =
            Equiv.swap (e 3) (e 4) (i : M.ι) := by
          intro i
          obtain ⟨j, rfl⟩ := f.surjective i
          have h1 : (π (f j) : {k // k ≠ M.a}) = f (γ j) :=
            (Equiv.apply_symm_apply f (π (f j))).symm
          rw [h1, hγswap]
          exact ggQ2NbG_swap_four e j
        let T : M.V →ₗ[ZMod 3] M.V :=
          (ggLin (p := 3) M.model φ : M.V ≃ₗ[ZMod 3] M.V).toLinearMap
        have hTswap : ∀ i : M.ι, i ≠ M.a →
            T (M.coroot i) = c • (1 : ZMod 3) • w (M.coroot (Equiv.swap (e 3) (e 4) i)) := by
          intro i hi
          have h1 := hT ⟨i, hi⟩
          rw [show ((π ⟨i, hi⟩ : {k // k ≠ M.a}) : M.ι) = Equiv.swap (e 3) (e 4) i
            from hπapply ⟨i, hi⟩] at h1
          simpa [T] using h1
        obtain ⟨w', hw'weyl, hstab⟩ :=
          ggQ2g_swap_stable (p := 3) (by decide) M.toLin hbas (m := 5) (by omega) e hcox'
            he0 M.xV hfix1 hV hw hTswap hφxV
        exact finW ⟨w', hw'weyl, fun v hv => hstab M.yV v hv⟩
      ·
        have hπ1' : ∀ i : {k // k ≠ M.a}, (i : M.ι) = e 1 →
            ((π i : {k // k ≠ M.a}) : M.ι) ≠ e 1 := by
          intro i hi hcontra
          apply hπt
          have hit : i = t := Subtype.ext hi
          calc π t = π i := by rw [hit]
            _ = t := Subtype.ext hcontra
        have hTF : lup10fa_TwistFacts := lup10fa_twistFacts_of_check
        obtain ⟨κ, hκ1, hκs, hκx⟩ := lup10ab_coord M e hecart he0 hbas
        obtain ⟨w', hw'K, b0, γ, lam, c', hadm, hb0, hform⟩ :=
          lup10ab_twist_form M e hecart he0 hV hbas hy1 κ hκ1 (hκx hy1) hφxV π
            (fun _ => 1) c w hScaled hw hT1 hπb hπ1'
        obtain ⟨r', hr', hlin⟩ :=
          ggQ2Nbr_forced_reflection hLB hP h5 hS hI1 hnb M e hecart he0 hV hbas hJ3 hZ hAJ
            hSC hTF κ hκ1 hκs (hκx hy1) hφ w' hw'K b0 γ lam c' hadm hb0 hform
        obtain ⟨ψ, hψ, hD⟩ :=
          lup10d_absorb_swapped hS rfl hnb M e hecart he0 hV hbas hTF hφ hφxV π
            (fun _ => 1) c w hScaled hw hT1 hπb hπ1' r' hr' hlin
        exact ggQ2_finish_of_le hLB hP hS hAJS hK1 hnb le_rfl hφ hψ hD

end CFSG.StandardType

end
