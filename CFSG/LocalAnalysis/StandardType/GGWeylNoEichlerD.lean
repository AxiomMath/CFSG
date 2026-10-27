module

public import CFSG.LocalAnalysis.StandardType.GGWeylNoEichlerBCDAux
public import CFSG.LocalAnalysis.StandardType.GGQTwoDWeyl

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma ggBCDE_D_zero_one {n : ℕ} (hn : 4 ≤ n) {a0 b0 : Fin n}
    (ha0 : (a0 : ℕ) = 0) (hb0 : (b0 : ℕ) = 1) : CartanMatrix.D n a0 b0 ≠ 0 := by
  rw [CartanMatrix.D]
  simp only [Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> omega

private lemma ggBCDE_D_zero_other {n : ℕ} (hn : 4 ≤ n) {a0 c : Fin n}
    (ha0 : (a0 : ℕ) = 0) (hc0 : (c : ℕ) ≠ 0) (hc1 : (c : ℕ) ≠ 1) :
    CartanMatrix.D n a0 c = 0 := by
  rw [CartanMatrix.D]
  simp only [Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> omega

private lemma ggBCDE_sum_ggDSimple (p m : ℕ) (i : Fin m) (hi : (i : ℕ) + 1 < m)
    (g : Fin m → ZMod p) :
    ∑ l : Fin m, ggDSimple p m i l * g l = g i - g ⟨(i : ℕ) + 1, hi⟩ := by
  have hpoint : ∀ l : Fin m, ggDSimple p m i l =
      (if (l : ℕ) = (i : ℕ) then (1 : ZMod p) else 0) +
      (if (l : ℕ) = (i : ℕ) + 1 then (-1 : ZMod p) else 0) := by
    intro l
    rw [ggDSimple, if_pos hi]
    by_cases h1 : (l : ℕ) = (i : ℕ)
    · have h2 : ¬ (l : ℕ) = (i : ℕ) + 1 := by omega
      simp [h1]
    · by_cases h2 : (l : ℕ) = (i : ℕ) + 1
      simp [h2]
      · simp [h1, h2]
  calc ∑ l : Fin m, ggDSimple p m i l * g l
      = ∑ l : Fin m, ((if (l : ℕ) = (i : ℕ) then (1 : ZMod p) else 0) * g l +
              (if (l : ℕ) = (i : ℕ) + 1 then (-1 : ZMod p) else 0) * g l) := by
          apply Finset.sum_congr rfl
          intro l _
          rw [hpoint l]
          ring
    _ = (∑ l : Fin m, (if (l : ℕ) = (i : ℕ) then (1 : ZMod p) else 0) * g l) +
        (∑ l : Fin m, (if (l : ℕ) = (i : ℕ) + 1 then (-1 : ZMod p) else 0) * g l) := by
          rw [Finset.sum_add_distrib]
    _ = 1 * g i + (-1) * g ⟨(i : ℕ) + 1, hi⟩ := by
          rw [ggBCDE_sum_nat_indicator (k := (i : ℕ)) (hk := i.isLt),
            ggBCDE_sum_nat_indicator (k := (i : ℕ) + 1) (hk := hi)]
    _ = g i - g ⟨(i : ℕ) + 1, hi⟩ := by ring

private lemma ggBCDE_sum_ggDSimple_fork (p m : ℕ) (hm : 2 ≤ m) (i : Fin m)
    (hi : ¬ (i : ℕ) + 1 < m) (g : Fin m → ZMod p) :
    ∑ l : Fin m, ggDSimple p m i l * g l =
      g ⟨m - 2, by omega⟩ + g ⟨m - 1, by omega⟩ := by
  have hpoint : ∀ l : Fin m, ggDSimple p m i l =
      (if (l : ℕ) = m - 2 then (1 : ZMod p) else 0) +
      (if (l : ℕ) = m - 1 then (1 : ZMod p) else 0) := by
    intro l
    rw [ggDSimple, if_neg hi]
    by_cases h2 : (l : ℕ) + 2 = m
    · have h : (l : ℕ) = m - 2 := by omega
      rw [if_pos (Or.inl h2), h]
      have hlt : ¬ (m - 2 : ℕ) = m - 1 := by omega
      simp [hlt]
    · by_cases h1 : (l : ℕ) + 1 = m
      · have h : (l : ℕ) = m - 1 := by omega
        rw [if_pos (Or.inr h1), h]
        have hlt : ¬ (m - 1 : ℕ) = m - 2 := by omega
        simp [hlt]
      · have hc : ¬ ((l : ℕ) + 2 = m ∨ (l : ℕ) + 1 = m) := by omega
        rw [if_neg hc]
        have hlt2 : ¬ (l : ℕ) = m - 2 := by omega
        have hlt1 : ¬ (l : ℕ) = m - 1 := by omega
        simp [hlt2, hlt1]
  calc ∑ l : Fin m, ggDSimple p m i l * g l
      = ∑ l : Fin m, ((if (l : ℕ) = m - 2 then (1 : ZMod p) else 0) * g l +
              (if (l : ℕ) = m - 1 then (1 : ZMod p) else 0) * g l) := by
          apply Finset.sum_congr rfl
          intro l _
          rw [hpoint l]
          ring
    _ = (∑ l : Fin m, (if (l : ℕ) = m - 2 then (1 : ZMod p) else 0) * g l) +
        (∑ l : Fin m, (if (l : ℕ) = m - 1 then (1 : ZMod p) else 0) * g l) := by
          rw [Finset.sum_add_distrib]
    _ = 1 * g ⟨m - 2, by omega⟩ + 1 * g ⟨m - 1, by omega⟩ := by
          rw [ggBCDE_sum_nat_indicator (k := m - 2) (hk := by omega),
            ggBCDE_sum_nat_indicator (k := m - 1) (hk := by omega)]
    _ = g ⟨m - 2, by omega⟩ + g ⟨m - 1, by omega⟩ := by ring

private lemma ggBCDE_chain_rel {n : ℕ} (i : Fin n) (hi : (i : ℕ) + 1 < n) :
    ggDSimple 3 n i =
      (Pi.single i (1 : ZMod 3) - Pi.single ⟨(i : ℕ) + 1, hi⟩ 1 : GGBCV n) := by
  funext j
  rw [ggDSimple, if_pos hi]
  simp only [Pi.sub_apply]
  by_cases h1 : (j : ℕ) = (i : ℕ)
  · have hj : j = i := Fin.ext h1
    subst j
    have hne : (Pi.single (⟨(i : ℕ) + 1, hi⟩ : Fin n) (1 : ZMod 3) : GGBCV n) i = 0 := by
      rw [Pi.single_eq_of_ne (show i ≠ (⟨(i : ℕ) + 1, hi⟩ : Fin n) from by
        intro h
        have := congrArg Fin.val h
        dsimp only at this
        omega)]
    rw [if_pos h1, Pi.single_eq_same, hne]
    ring
  · have hPi : (Pi.single i (1 : ZMod 3) : GGBCV n) j = 0 := by
      rw [Pi.single_eq_of_ne (show j ≠ i from fun h => h1 (congrArg Fin.val h))]
    by_cases h2 : (j : ℕ) = (i : ℕ) + 1
    · have hj : j = ⟨(i : ℕ) + 1, hi⟩ := Fin.ext h2
      subst j
      rw [if_neg h1, if_pos h2, Pi.single_eq_same, hPi]
      ring_nf
    · have hPi2 : (Pi.single (⟨(i : ℕ) + 1, hi⟩ : Fin n) (1 : ZMod 3) : GGBCV n) j = 0 := by
        rw [Pi.single_eq_of_ne (show j ≠ (⟨(i : ℕ) + 1, hi⟩ : Fin n) from by
          intro h
          have := congrArg Fin.val h
          dsimp only at this
          omega)]
      rw [if_neg h1, if_neg h2, hPi, hPi2]
      ring

private lemma ggBCDE_fork_rel {n : ℕ} (hn : 2 ≤ n) :
    ggDSimple 3 n ⟨n - 1, by omega⟩ =
      (Pi.single ⟨n - 2, by omega⟩ (1 : ZMod 3) +
        Pi.single ⟨n - 1, by omega⟩ 1 : GGBCV n) := by
  funext j
  have hlast : ¬ ((⟨n - 1, by omega⟩ : Fin n) : ℕ) + 1 < n := by
    dsimp only
    omega
  rw [ggDSimple, if_neg hlast]
  simp only [Pi.add_apply]
  by_cases h2 : (j : ℕ) + 2 = n
  · rw [if_pos (Or.inl h2)]
    have hj : j = ⟨n - 2, by omega⟩ := Fin.ext (by dsimp only; omega)
    rw [hj]
    have hne : (⟨n - 2, by omega⟩ : Fin n) ≠ ⟨n - 1, by omega⟩ := by
      intro h
      have := congrArg Fin.val h
      dsimp only at this
      omega
    rw [Pi.single_eq_same, Pi.single_eq_of_ne hne]
    ring
  · by_cases h1 : (j : ℕ) + 1 = n
    · rw [if_pos (Or.inr h1)]
      have hj : j = ⟨n - 1, by omega⟩ := Fin.ext (by dsimp only; omega)
      rw [hj]
      have hne : (⟨n - 1, by omega⟩ : Fin n) ≠ ⟨n - 2, by omega⟩ := by
        intro h
        have := congrArg Fin.val h
        dsimp only at this
        omega
      rw [Pi.single_eq_same, Pi.single_eq_of_ne hne]
      ring
    · have hc : ¬ ((j : ℕ) + 2 = n ∨ (j : ℕ) + 1 = n) := by omega
      rw [if_neg hc]
      have h1' : j ≠ ⟨n - 2, by omega⟩ := by
        intro h
        have := congrArg Fin.val h
        dsimp only at this
        omega
      have h2' : j ≠ ⟨n - 1, by omega⟩ := by
        intro h
        have := congrArg Fin.val h
        dsimp only at this
        omega
      rw [Pi.single_eq_of_ne h1', Pi.single_eq_of_ne h2']
      ring

private lemma ggBCDE_wt_ggDSimple {n : ℕ} (hn : 4 ≤ n) (i : Fin n) :
    ggBCWt (ggDSimple 3 n i) = 2 := by
  by_cases hi : (i : ℕ) + 1 < n
  · rw [ggBCDE_chain_rel i hi]
    exact ggQ2x_wt_sub_single i ⟨(i : ℕ) + 1, hi⟩ (by
      intro h
      have := congrArg Fin.val h
      dsimp only at this
      omega)
  · have hi_eq : i = ⟨n - 1, by omega⟩ := Fin.ext (by
      dsimp only
      omega)
    rw [hi_eq, ggBCDE_fork_rel (n := n) (by omega)]
    exact ggQ2x_wt_single_add_single ⟨n - 2, by omega⟩ ⟨n - 1, by omega⟩ (by
      intro h
      have := congrArg Fin.val h
      dsimp only at this
      omega) 1 1 one_ne_zero one_ne_zero

private lemma ggBCDE_root_inj_D {n : ℕ} (hn : 2 ≤ n)
    (x : GGBCV n) (hx : ∀ i, ∑ j, ggDSimple 3 n i j * x j = 0) : x = 0 := by
  let last : Fin n := ⟨n - 1, by omega⟩
  have hchain : ∀ (j : Fin n) (hj : (j : ℕ) + 1 < n),
      x j = x ⟨(j : ℕ) + 1, hj⟩ := by
    intro j hj
    have h := hx j
    rw [ggBCDE_sum_ggDSimple 3 n j hj] at h
    exact sub_eq_zero.mp h
  have hfork : x ⟨n - 2, by omega⟩ + x last = 0 := by
    have h := hx last
    have hlast : ¬ ((last : Fin n) : ℕ) + 1 < n := by
      simp only [last]
      omega
    have hlast' : last = ⟨n - 1, by omega⟩ := rfl
    rw [hlast', ggBCDE_sum_ggDSimple_fork 3 n hn ⟨n - 1, by omega⟩ hlast x] at h
    simpa [last] using h
  have hall : ∀ j : Fin n, x j = x last := by
    have hdesc : ∀ m : ℕ, ∀ j : Fin n, n - 1 - (j : ℕ) = m → x j = x last := by
      intro m
      induction m using Nat.strong_induction_on with
      | _ m ih =>
        intro j hm
        by_cases hj : (j : ℕ) = n - 1
        · rw [show j = last from Fin.ext hj]
        · have hjlt : (j : ℕ) + 1 < n := by omega
          rw [hchain j hjlt]
          exact ih (n - 1 - ((j : ℕ) + 1)) (by omega) ⟨(j : ℕ) + 1, hjlt⟩ rfl
    intro j
    exact hdesc (n - 1 - (j : ℕ)) j rfl
  have hlast0 : x last = 0 := by
    have h1 : x ⟨n - 2, by omega⟩ = x last := hall ⟨n - 2, by omega⟩
    rw [h1] at hfork
    have h2 : (2 : ZMod 3) * x last = 0 := by
      simpa [two_mul] using hfork
    exact (mul_eq_zero.mp h2).resolve_left (by decide)
  funext j
  rw [hall j, hlast0]
  rfl

private theorem ggBCDE_rho_D {n : ℕ} (hn : 5 ≤ n) :
    GGWeylNoEichlerRho (CartanMatrix.D n) := by
  classical
  intro U instACG instMod h α hb hspan hα g hg hgne
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hm4 : 4 ≤ n := by omega
  have hn2 : 2 ≤ n := by omega
  have hfr : Module.finrank (ZMod 3) U = n := by
    have h1 := finrank_span_eq_card hb
    rw [hspan, finrank_top, Fintype.card_fin] at h1
    exact h1
  let D' : GGQ2Lin 3 :=
    { ι := Fin n
      coxeter := ggCoxeterMatrixD n
      cartan := CartanMatrix.D n
      V := U
      coroot := h
      root := α
      a := ⟨0, by omega⟩
      b := ⟨1, by omega⟩
      a_ne_b := by
        intro hh
        have := congrArg Fin.val hh
        simp at this
      a_leaf := by
        refine ⟨⟨1, by omega⟩, ⟨?_, ?_⟩, ?_⟩
        · intro hh
          have := congrArg Fin.val hh
          simp at this
        · exact ggBCDE_D_zero_one (n := n) (by omega) rfl rfl
        · intro y hy
          obtain ⟨hyne, hyC⟩ := hy
          have hyval : (y : ℕ) = 0 ∨ (y : ℕ) = 1 := by
            by_cases h0 : (y : ℕ) = 0
            · exact Or.inl h0
            · by_cases h1 : (y : ℕ) = 1
              · exact Or.inr h1
              · exfalso
                exact hyC (ggBCDE_D_zero_other (n := n) (by omega) rfl h0 h1)
          rcases hyval with h0 | h1
          · exact (hyne (Fin.ext h0)).elim
          · exact Fin.ext h1
      isWeyl := Or.inl ⟨n, Equiv.refl _, by omega,
        Or.inr (Or.inr ⟨by omega, (ggBCDE_reindex_refl (ggCoxeterMatrixD n)).symm⟩)⟩
      isCartan := ggIntCartan_D n
      pairing := fun i j => by simpa using hα i j }
  have hbas : D'.Basis := by
    change LinearIndependent (ZMod 3) h ∧ Fintype.card (Fin n) = Module.finrank (ZMod 3) U
    exact ⟨hb, by simp [hfr]⟩
  have hgen : Set.range D'.simpleRefl =
      {t : U ≃ₗ[ZMod 3] U | ∃ j, ∀ v, t v = v - α j v • h j} := by
    ext t
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k, fun v => by rw [GGQ2Lin.simpleRefl, Module.reflection_apply]⟩
    · rintro ⟨j, hj⟩
      refine ⟨j, ?_⟩
      ext v
      rw [hj v, GGQ2Lin.simpleRefl, Module.reflection_apply]
  have hWclos : D'.weyl = Subgroup.closure (Set.range D'.simpleRefl) := by
    rw [GGQ2Lin.weyl, GGQ2Lin.parab, Set.image_univ]
  have hweylEq : D'.weyl = ggQ2WeylOf h α := by
    rw [hWclos, hgen]
    rfl
  have hg' : g ∈ D'.weyl := by
    rw [hweylEq]
    exact hg
  have hB : D'.coxeter = (ggCoxeterMatrixD n).reindex (Equiv.refl (Fin n)) :=
    (ggBCDE_reindex_refl (ggCoxeterMatrixD n)).symm
  obtain ⟨τ, hτ, hroot⟩ :=
    ggQ2_D_coordinates (p := 3) (by decide) D' hbas hm4 (Equiv.refl (Fin n)) hB
  have hroot' : ∀ i v, D'.root i v = ∑ j, ggDSimple 3 n i j * τ v j := by
    intro i v
    simpa using hroot i v
  have hmapWc : (D'.weyl).map (ggLinConj τ).toMonoidHom = ggQ2_DW_Wc 3 n hm4 :=
    ggQ2_DW_linWeylMap D' hm4 (Equiv.refl (Fin n)) τ hτ hroot
  have hDle : ggBCReflGp (ggDRoots n) ≤ (D'.weyl).map (ggLinConj τ).toMonoidHom :=
    ggQ2_DW_Droots_le_map D' hbas (by omega) (Equiv.refl (Fin n)) hB τ hτ hroot
      D'.weyl le_rfl
  have hWc_le_D : ggQ2_DW_Wc 3 n hm4 ≤ ggBCReflGp (ggDRoots n) := by
    rw [ggQ2_DW_Wc, Subgroup.closure_le]
    rintro t ⟨i, rfl⟩
    rw [ggQ2_DW_r_eq_bc hm4 i]
    exact Subgroup.subset_closure
      ⟨ggDSimple 3 n i, by simpa [ggDRoots] using ggBCDE_wt_ggDSimple (by omega) i,
        by rw [ggQ2_DW_simple_norm hm4 i]; decide, rfl⟩
  have hmapD : (D'.weyl).map (ggLinConj τ).toMonoidHom = ggBCReflGp (ggDRoots n) := by
    apply le_antisymm
    · rw [hmapWc]
      exact hWc_le_D
    · exact hDle
  have hmemD : ggLinConj τ g ∈ ggBCReflGp (ggDRoots n) := by
    have h := Subgroup.mem_map_of_mem (ggLinConj τ).toMonoidHom hg'
    rwa [hmapD] at h
  have hDsub : ggDRoots n ⊆ ggBCRoots n := by
    intro v hv
    simp only [ggDRoots, Set.mem_setOf_eq] at hv
    simp only [ggBCRoots, Set.mem_setOf_eq]
    omega
  obtain ⟨σ, ε', hε', hsingle⟩ := ggBCReflGp_monomial (S := ggDRoots n) hDsub hmemD
  have hne : ¬ GGEichler g :=
    ggBCDE_no_eichler_of_monomial τ g ((ggLinConj τ).toMonoidHom) (fun _ _ => rfl)
      ⟨σ, ε', hε', hsingle⟩
  have hinj : ∀ w : U, (∀ i, α i w = 0) → w = 0 := by
    intro w hw
    have hzero : τ w = 0 := by
      apply ggBCDE_root_inj_D hn2 (τ w)
      intro i
      rw [← hroot' i w]
      simpa using hw i
    exact τ.injective (by rw [hzero, map_zero])
  by_contra hcon
  push Not at hcon
  have hN : ∀ v, g (g v) + g v + v = 0 := fun v => hinj _ (fun i => hcon v i)
  exact hne ⟨hgne, hN⟩

theorem ggWeylNoEichlerRho_D {n : ℕ} (hn : 5 ≤ n) : GGWeylNoEichlerRho (CartanMatrix.D n) :=
  ggBCDE_rho_D hn

end CFSG.StandardType

end
