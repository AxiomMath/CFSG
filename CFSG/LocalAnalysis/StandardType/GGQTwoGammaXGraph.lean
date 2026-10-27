module

public import CFSG.LocalAnalysis.StandardType.GGQTwoGammaXGraphE7
public import CFSG.LocalAnalysis.StandardType.GGQTwoGammaXGraphD5
public import CFSG.LocalAnalysis.StandardType.GGQTwoGammaXHolds
public import CFSG.LocalAnalysis.StandardType.GGQTwoGraphClassify
public import CFSG.LocalAnalysis.StandardType.GGQTwoGraphSwap
public import CFSG.LocalAnalysis.StandardType.GGQTwoGraphFinish
public import CFSG.LocalAnalysis.StandardType.GGQTwoK1OfI1

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module

private lemma ggQ2gx_D_fork_nbr {m : ℕ} (hm : 4 ≤ m) {i : Fin m}
    (hi : i.val = m - 2 ∨ i.val = m - 1) :
    CartanMatrix.D m i ⟨m - 3, by omega⟩ ≠ 0 := by
  rcases hi with hi | hi
  · rw [CartanMatrix.D, Matrix.of_apply, hi]
    simp only [Fin.val_mk]
    split_ifs <;> omega
  · rw [CartanMatrix.D, Matrix.of_apply, hi]
    simp only [Fin.val_mk]
    split_ifs <;> omega

private lemma ggQ2gx_D_fork_nbr_eq {m : ℕ} (hm : 4 ≤ m) {i j : Fin m}
    (hi : i.val = m - 2 ∨ i.val = m - 1) (hij : i ≠ j)
    (h : CartanMatrix.D m i j ≠ 0) : j.val = m - 3 := by
  rw [CartanMatrix.D, Matrix.of_apply] at h
  simp only [hij, if_false] at h
  rcases hi with hi | hi
  · rw [hi] at h
    split_ifs at h <;> omega
  · rw [hi] at h
    split_ifs at h <;> omega

theorem ggQ2g_second_leaf {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p) {k : ℕ} (hk : 2 ≤ k)
    (f : Fin (2 * k) ≃ {i // i ≠ D.a})
    (hf : ∀ i j, D.cartan (f i) (f j) = CartanMatrix.D (2 * k) i j) :
    ∃ c : D.ι, c ≠ D.a ∧ ∃! d, d ≠ c ∧ D.cartan c d ≠ 0 := by
  classical
  have hm : 4 ≤ 2 * k := by omega
  obtain ⟨d₀, ⟨_, _⟩, huniq⟩ := D.a_leaf
  have hex : ∃ j : Fin (2 * k),
      (j.val = 2 * k - 2 ∨ j.val = 2 * k - 1) ∧ (f j : D.ι) ≠ d₀ := by
    by_cases h : (f (⟨2 * k - 2, by omega⟩ : Fin (2 * k)) : D.ι) = d₀
    · refine ⟨⟨2 * k - 1, by omega⟩, Or.inr rfl, ?_⟩
      intro hh
      have hfj : f (⟨2 * k - 1, by omega⟩ : Fin (2 * k)) =
          f (⟨2 * k - 2, by omega⟩ : Fin (2 * k)) := Subtype.ext (hh.trans h.symm)
      have hv := congrArg Fin.val (f.injective hfj)
      simp only [Fin.val_mk] at hv
      omega
    · exact ⟨⟨2 * k - 2, by omega⟩, Or.inl rfl, h⟩
  obtain ⟨j, hj, hjne⟩ := hex
  refine ⟨f j, (f j).2, ?_⟩
  refine ⟨f ⟨2 * k - 3, by omega⟩, ⟨?_, ?_⟩, ?_⟩
  · intro hh
    have hv := congrArg Fin.val (f.injective (Subtype.ext hh))
    simp only [Fin.val_mk] at hv
    rcases hj with hj | hj <;> omega
  · rw [hf j ⟨2 * k - 3, by omega⟩]
    exact ggQ2gx_D_fork_nbr hm hj
  · intro d hd
    obtain ⟨hdc, hdnbr⟩ := hd
    by_cases hda : d = D.a
    · subst hda
      have hac : D.cartan D.a (f j : D.ι) ≠ 0 := by
        intro hzero
        exact hdnbr (D.isCartan.eq_zero_symm (a := (f j : D.ι)) (b := D.a)
          (f j).2 hzero)
      exact absurd (huniq (f j) ⟨(f j).2, hac⟩) hjne
    · let i : Fin (2 * k) := f.symm ⟨d, hda⟩
      have hfi : (f i : D.ι) = d := by
        dsimp [i]
        exact congrArg Subtype.val (f.apply_symm_apply ⟨d, hda⟩)
      have hD : CartanMatrix.D (2 * k) j i ≠ 0 := by
        intro hzero
        apply hdnbr
        rw [← hfi, hf j i]
        exact hzero
      have hji : j ≠ i := by
        intro hEq
        apply hdc
        calc d = (f i : D.ι) := hfi.symm
          _ = (f j : D.ι) := by rw [hEq]
      have hEq : i.val = 2 * k - 3 := ggQ2gx_D_fork_nbr_eq hm hj hji hD
      calc d = (f i : D.ι) := hfi.symm
        _ = (f ⟨2 * k - 3, by omega⟩ : D.ι) := by
          rw [show i = (⟨2 * k - 3, by omega⟩ : Fin (2 * k)) from Fin.ext hEq]

private lemma ggQ2gx_D_succ_succ {k : ℕ} (hk : 2 ≤ k) (i j : Fin (2 * k)) :
    CartanMatrix.D (2 * k + 1) i.succ j.succ = CartanMatrix.D (2 * k) i j := by
  simp only [CartanMatrix.D, Matrix.of_apply]
  rw [if_congr (show i.succ = j.succ ↔ i = j from
    ⟨fun h => Fin.succ_injective (2 * k) h, fun h => by rw [h]⟩) rfl ?_]
  rw [if_neg (by omega : ¬ 2 * k + 1 ≤ 2), if_neg (by omega : ¬ 2 * k ≤ 2)]
  have hsi : (i.succ : Fin (2 * k + 1)).val = i.val + 1 := rfl
  have hsj : (j.succ : Fin (2 * k + 1)).val = j.val + 1 := rfl
  have h1 : (i.succ.val + 1 = j.succ.val ∧ j.succ.val + 2 < 2 * k + 1) ↔
      (i.val + 1 = j.val ∧ j.val + 2 < 2 * k) := by
    rw [hsi, hsj]
    constructor <;> intro h <;> omega
  have h2 : (j.succ.val + 1 = i.succ.val ∧ i.succ.val + 2 < 2 * k + 1) ↔
      (j.val + 1 = i.val ∧ i.val + 2 < 2 * k) := by
    rw [hsi, hsj]
    constructor <;> intro h <;> omega
  have h3 : (i.succ.val + 3 = 2 * k + 1 ∧
      (j.succ.val + 2 = 2 * k + 1 ∨ j.succ.val + 1 = 2 * k + 1)) ↔
      (i.val + 3 = 2 * k ∧ (j.val + 2 = 2 * k ∨ j.val + 1 = 2 * k)) := by
    rw [hsi, hsj]
    constructor <;> intro h <;> omega
  have h4 : (j.succ.val + 3 = 2 * k + 1 ∧
      (i.succ.val + 2 = 2 * k + 1 ∨ i.succ.val + 1 = 2 * k + 1)) ↔
      (j.val + 3 = 2 * k ∧ (i.val + 2 = 2 * k ∨ i.val + 1 = 2 * k)) := by
    rw [hsi, hsj]
    constructor <;> intro h <;> omega
  rw [if_congr h1 rfl (if_congr h2 rfl (if_congr h3 rfl (if_congr h4 rfl rfl)))]

private lemma ggQ2gx_fin4_perm (π : Equiv.Perm (Fin 4)) (h0 : π 0 = 0) (h1 : π 1 = 1) :
    π = 1 ∨ π = Equiv.swap (2 : Fin 4) 3 := by
  revert π
  decide +kernel

theorem ggQ2_gammaXGraph_holds (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (h5 : GGQTwoCentralizerInput) (hD5 : GGQ2GammaXGraphD5Input) (hE7 : GGQ2GammaXGraphE7Input) :
    GGQ2GammaXGraphInput := by
  intro G _ _ p B Bs x L D J hS hp hI1 hxL _ y K hnb M hD2k hV φ hφ hφxV π μ c w hSc hw hT hπb _
  haveI : Fact p.Prime := ⟨hS.1.1.tableB_facts.1⟩
  subst hp
  classical
  have hH : GGCorFiveTwentyHyp 3 B Bs x L D J := hS.1
  have hAJS : ggAutomizer J Bs ≠ ⊥ := ggQ2_ajOfSetting hP h5 hS
  have hK1 : GGQTwoK1 3 B Bs x D J := ggQ2_K1_of_I1 hLB hP hH hI1
  obtain ⟨k, hk, f, hf⟩ := hD2k
  obtain ⟨c₀, hc₀a, hc₀l⟩ := ggQ2g_second_leaf M.toLin hk f hf
  rcases ggQ2g_classify M.toLin M.a c₀ hc₀a hc₀l hk f hf with
    ⟨e, hecart, hcox, he0, -⟩ | ⟨rfl, e, hecart, he0, -⟩
  · let e' : Fin (2 * k + 1) ≃ M.ι := e
    have hecart' : ∀ i j : Fin (2 * k + 1),
        M.cartan (e' i) (e' j) = CartanMatrix.D (2 * k + 1) i j := hecart
    have hcox' : M.toLin.coxeter = (ggCoxeterMatrixD (2 * k + 1)).reindex e' := hcox
    have he0' : M.a = e' ⟨0, by omega⟩ := he0
    let σf : Fin (2 * k) → {i : M.ι // i ≠ M.a} := fun i =>
      ⟨e' i.succ, by
        rw [he0']
        intro h
        exact Fin.succ_ne_zero i (e'.injective h)⟩
    have hσf_bij : Function.Bijective σf := by
      constructor
      · intro a b hab
        have h1 : e' a.succ = e' b.succ := congrArg Subtype.val hab
        exact Fin.succ_injective (2 * k) (e'.injective h1)
      · rintro ⟨i, hi⟩
        obtain ⟨t, rfl⟩ := e'.surjective i
        have ht : t ≠ 0 := by
          intro h
          exact hi (by rw [h]; exact he0'.symm)
        obtain ⟨j, hj⟩ := Fin.exists_succ_eq_of_ne_zero ht
        have hσfj : (σf j : M.ι) = e' j.succ := rfl
        exact ⟨j, Subtype.ext (by rw [hσfj, hj])⟩
    let σ : Fin (2 * k) ≃ {i : M.ι // i ≠ M.a} := Equiv.ofBijective σf hσf_bij
    have hσ : ∀ i j, M.cartan (σ i) (σ j) = CartanMatrix.D (2 * k) i j := by
      intro i j
      have h1 := hecart' i.succ j.succ
      change M.cartan (e' i.succ) (e' j.succ) = CartanMatrix.D (2 * k) i j
      rw [h1, ggQ2gx_D_succ_succ hk i j]
    obtain ⟨π', μ', hμ'0, hrel, hπσ, hμσ⟩ := ggQ2g_transport M.toLin M.a σ hσ hSc
    have hπσv : ∀ i, ((π (σ i) : {k // k ≠ M.a}) : M.ι) =
        ((σ (π' i) : {k // k ≠ M.a}) : M.ι) := fun i => congrArg Subtype.val (hπσ i)
    have hπ'ne : π' ≠ 1 := by
      intro h1
      apply hπb
      have hi : σ (σ.symm (⟨M.b, M.a_ne_b.symm⟩ : {i // i ≠ M.a})) =
          ⟨M.b, M.a_ne_b.symm⟩ := σ.apply_symm_apply _
      calc π ⟨M.b, M.a_ne_b.symm⟩
          = π (σ (σ.symm ⟨M.b, M.a_ne_b.symm⟩)) := by rw [hi]
        _ = σ (π' (σ.symm ⟨M.b, M.a_ne_b.symm⟩)) := hπσ _
        _ = σ (σ.symm ⟨M.b, M.a_ne_b.symm⟩) := by rw [h1, Equiv.Perm.one_apply]
        _ = ⟨M.b, M.a_ne_b.symm⟩ := hi
    have finishD (hμc : ∀ i, μ' i = μ' ⟨0, by omega⟩)
        (hπ' : π' = Equiv.swap (⟨2 * k - 2, by omega⟩ : Fin (2 * k))
          ⟨2 * k - 1, by omega⟩) :
        φ ∈ ggAutomizer (Subgroup.normalizer (ggG0 3 B x L D J : Set G)) Bs := by
      let μ₀ : ZMod 3 := μ' ⟨0, by omega⟩
      let T : M.V →ₗ[ZMod 3] M.V :=
        (ggLin (p := 3) M.model φ : M.V ≃ₗ[ZMod 3] M.V).toLinearMap
      have hT' : ∀ i : M.ι, i ≠ M.a →
          T (M.coroot i) = c • μ₀ • w (M.coroot (Equiv.swap
            (e' ⟨2 * k + 1 - 2, by omega⟩) (e' ⟨2 * k + 1 - 1, by omega⟩) i)) := by
        intro i hi
        let j : Fin (2 * k) := σ.symm ⟨i, hi⟩
        have hj : (σ j : M.ι) = i := congrArg Subtype.val (σ.apply_symm_apply ⟨i, hi⟩)
        have h1 := hT (σ j)
        rw [hj] at h1
        simp only [hπσv j, hπ'] at h1
        have hσj : (σ (Equiv.swap (⟨2 * k - 2, by omega⟩ : Fin (2 * k))
            ⟨2 * k - 1, by omega⟩ j) : M.ι) =
            Equiv.swap (e' ⟨2 * k + 1 - 2, by omega⟩)
              (e' ⟨2 * k + 1 - 1, by omega⟩) i := by
          have hsa : (⟨2 * k + 1 - 2, by omega⟩ : Fin (2 * k + 1)) =
              (⟨2 * k - 2, by omega⟩ : Fin (2 * k)).succ := by
            apply Fin.ext
            simp only [Fin.val_succ]
            omega
          have hsb : (⟨2 * k + 1 - 1, by omega⟩ : Fin (2 * k + 1)) =
              (⟨2 * k - 1, by omega⟩ : Fin (2 * k)).succ := by
            apply Fin.ext
            simp only [Fin.val_succ]
            omega
          rw [hsa, hsb]
          have hσa : (σ (Equiv.swap (⟨2 * k - 2, by omega⟩ : Fin (2 * k))
              ⟨2 * k - 1, by omega⟩ j) : M.ι) =
              e' ((Equiv.swap (⟨2 * k - 2, by omega⟩ : Fin (2 * k))
                ⟨2 * k - 1, by omega⟩ j).succ) := rfl
          rw [hσa]
          rw [← Function.Injective.swap_apply (Fin.succ_injective (2 * k))
            (⟨2 * k - 2, by omega⟩) (⟨2 * k - 1, by omega⟩) j]
          rw [← show e' j.succ = i from hj]
          exact (Function.Injective.swap_apply e'.injective
            (⟨2 * k - 2, by omega⟩ : Fin (2 * k)).succ
            (⟨2 * k - 1, by omega⟩ : Fin (2 * k)).succ j.succ).symm
        rw [hσj] at h1
        change ((ggLin (p := 3) M.model φ : M.V ≃ₗ[ZMod 3] M.V).toLinearMap
            (M.coroot i)) = c • μ' ⟨0, by omega⟩ • w (M.coroot (Equiv.swap
              (e' ⟨2 * k + 1 - 2, by omega⟩) (e' ⟨2 * k + 1 - 1, by omega⟩) i))
        rw [show μ' ⟨0, by omega⟩ = μ (σ j) from (hμc j).symm.trans (hμσ j).symm]
        exact h1
      have hM : M.cartan = (CartanMatrix.D (2 * k + 1)).submatrix e'.symm e'.symm := by
        ext i j
        simp only [Matrix.submatrix_apply]
        rw [← hecart' (e'.symm i) (e'.symm j)]
        simp
      have hdet : ((M.cartan.det : ℤ) : ZMod 3) ≠ 0 := by
        rw [hM, Matrix.det_submatrix_equiv_self, CartanMatrix.D_det (by omega)]
        have h4 : (((4 : ℤ) : ZMod 3)) = (((1 : ℤ) : ZMod 3)) := by
          rw [ZMod.intCast_eq_intCast_iff']
          norm_num
        rw [h4]
        exact one_ne_zero
      have hbas : M.toLin.Basis := ggQ2g_basis M.toLin M.a M.xV hdet hV
      have hfix1 := (ggQ2_fixed_lin M).1
      obtain ⟨w', hw'weyl, hstab⟩ :=
        ggQ2g_swap_stable (p := 3) (by decide) M.toLin hbas (m := 2 * k + 1) (by omega)
          e' hcox' he0' M.xV hfix1 hV hw hT' hφxV
      exact ggQ2_finish_of_weyl hLB hP hS hAJS hK1 hnb M hφ
        ⟨w', hw'weyl, fun v hv => hstab M.yV v hv⟩
    by_cases hk3 : 3 ≤ k
    · obtain ⟨hμc, hπc⟩ := ggQ2g_scaledD (2 * k) (by omega) π' μ' hμ'0 hrel
      exact finishD hμc (hπc.resolve_left hπ'ne)
    · have hk2 : k = 2 := by omega
      subst hk2
      obtain ⟨hμc, hπ1⟩ := ggQ2g_scaledD4 π' μ' hμ'0 hrel
      by_cases hπ0 : π' 0 = 0
      · have hperm := ggQ2gx_fin4_perm π' hπ0 hπ1
        have hπ' : π' = Equiv.swap (⟨2, by omega⟩ : Fin 4) ⟨3, by omega⟩ := by
          rcases hperm with h | h
          · exact absurd h hπ'ne
          · rw [h]
            rfl
        exact finishD hμc hπ'
      · have hmove : ∀ i : {i : M.ι // i ≠ M.a}, (i : M.ι) = e' 1 →
            ((π i : {i : M.ι // i ≠ M.a}) : M.ι) ≠ e' 1 := by
          rintro ⟨i, hi⟩ hie
          let j : Fin 4 := σ.symm ⟨i, hi⟩
          have hj : (σ j : M.ι) = i := congrArg Subtype.val (σ.apply_symm_apply ⟨i, hi⟩)
          have hjs : j = 0 := by
            apply Fin.succ_injective 4
            apply e'.injective
            have h1 : e' j.succ = i := hj
            have h2 : i = e' ((0 : Fin 4).succ) := hie
            exact h1.trans h2
          intro hcontra
          have hπi : π ⟨i, hi⟩ = σ (π' j) := by
            have h := hπσ j
            have hσj : σ j = ⟨i, hi⟩ := σ.apply_symm_apply ⟨i, hi⟩
            calc π ⟨i, hi⟩ = π (σ j) := congrArg π hσj.symm
              _ = σ (π' j) := h
          have h1 : (σ (π' j) : M.ι) = e' 1 := by
            rw [← hπi]
            exact hcontra
          have h2 : e' ((π' j).succ) = e' 1 := h1
          have h4 : π' j = 0 := by
            apply Fin.succ_injective 4
            apply e'.injective
            rw [h2]
            rfl
          exact hπ0 (by rwa [hjs] at h4)
        exact hD5 hS rfl hI1 hxL hnb M (e' : Fin 5 ≃ M.ι) hecart' he0' hV φ hφ hφxV π μ c w hSc
          hw hT hπb hmove
  · let e' : Fin 7 ≃ M.ι := e
    have hecart' : ∀ i j, M.cartan (e' i) (e' j) = CartanMatrix.E 7 i j := hecart
    have he0' : M.a = e' 0 := he0
    exact hE7 hS rfl hI1 hxL hnb M e' hecart' he0' hV φ hφ hφxV π μ c w hSc hw hT hπb

theorem ggQ2_gammaXGraph_of_D5 (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (h5 : GGQTwoCentralizerInput) (hD5 : GGQ2GammaXGraphD5Input) : GGQ2GammaXGraphInput :=
  ggQ2_gammaXGraph_holds hLB hP h5 hD5 (ggQ2_gammaXGraphE7_holds hLB hP h5)

theorem ggQ2_gammaXGraph_of_inputs (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (h5 : GGQTwoCentralizerInput) : GGQ2GammaXGraphInput :=
  ggQ2_gammaXGraph_of_D5 hLB hP h5 (ggQ2_gammaXGraphD5_holds hLB hP h5)

end CFSG.StandardType

end
