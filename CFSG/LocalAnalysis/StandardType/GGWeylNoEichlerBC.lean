module

public import CFSG.LocalAnalysis.StandardType.GGWeylNoEichlerBCDAux
public import CFSG.LocalAnalysis.StandardType.GGQTwoBCCoord
public import CFSG.LocalAnalysis.StandardType.GGQTwoTransport
public import CFSG.LocalAnalysis.StandardType.GGQTwoBCZ1

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma ggBCDE_B_apply {n : ℕ} (i j : Fin n) :
    (CoxeterMatrix.B n) i j =
      (if i = j then 1
        else if ((i : ℕ) = n - 1 ∧ (j : ℕ) = n - 2) ∨
          ((j : ℕ) = n - 1 ∧ (i : ℕ) = n - 2) then 4
        else if ((j : ℕ) + 1 = (i : ℕ)) ∨ ((i : ℕ) + 1 = (j : ℕ)) then 3 else 2) := by
  rw [CoxeterMatrix.B]
  simp only [Matrix.of_apply]

private lemma ggBCDE_B_zero_one {n : ℕ} (hn : 3 ≤ n) {a0 b0 : Fin n}
    (ha0 : (a0 : ℕ) = 0) (hb0 : (b0 : ℕ) = 1) : (CoxeterMatrix.B n) a0 b0 = 3 := by
  rw [ggBCDE_B_apply]
  simp only [Fin.ext_iff]
  split_ifs <;> omega

private lemma ggBCDE_B_zero_other {n : ℕ} (hn : 3 ≤ n) {a0 c : Fin n}
    (ha0 : (a0 : ℕ) = 0) (hc0 : (c : ℕ) ≠ 0) (hc1 : (c : ℕ) ≠ 1) :
    (CoxeterMatrix.B n) a0 c = 2 := by
  rw [ggBCDE_B_apply]
  simp only [Fin.ext_iff]
  split_ifs <;> omega

private lemma ggBCDE_sum_ggBCRootFun_chain (n : ℕ) (ε : ZMod 3) (i : Fin n)
    (hi : (i : ℕ) + 1 < n) (x : GGBCV n) :
    ∑ j, ggBCRootFun n ε i j * x j = x i - x ⟨(i : ℕ) + 1, hi⟩ := by
  have hpoint : ∀ l : Fin n, ggBCRootFun n ε i l =
      (if (l : ℕ) = (i : ℕ) then (1 : ZMod 3) else 0) +
      (if (l : ℕ) = (i : ℕ) + 1 then (-1 : ZMod 3) else 0) := by
    intro l
    rw [ggBCRootFun, if_pos hi]
    by_cases h1 : (l : ℕ) = (i : ℕ)
    · have h2 : ¬ (l : ℕ) = (i : ℕ) + 1 := by omega
      simp [h1]
    · by_cases h2 : (l : ℕ) = (i : ℕ) + 1
      · simp [h2]
        rfl
      · simp [h1, h2]
  calc ∑ l : Fin n, ggBCRootFun n ε i l * x l
      = ∑ l : Fin n, ((if (l : ℕ) = (i : ℕ) then (1 : ZMod 3) else 0) * x l +
              (if (l : ℕ) = (i : ℕ) + 1 then (-1 : ZMod 3) else 0) * x l) := by
          apply Finset.sum_congr rfl
          intro l _
          rw [hpoint l]
          ring
    _ = (∑ l : Fin n, (if (l : ℕ) = (i : ℕ) then (1 : ZMod 3) else 0) * x l) +
        (∑ l : Fin n, (if (l : ℕ) = (i : ℕ) + 1 then (-1 : ZMod 3) else 0) * x l) := by
          rw [Finset.sum_add_distrib]
    _ = 1 * x i + (-1) * x ⟨(i : ℕ) + 1, hi⟩ := by
          rw [ggBCDE_sum_nat_indicator (k := (i : ℕ)) (hk := i.isLt),
            ggBCDE_sum_nat_indicator (k := (i : ℕ) + 1) (hk := hi)]
    _ = x i - x ⟨(i : ℕ) + 1, hi⟩ := by ring

private lemma ggBCDE_sum_ggBCRootFun_last (n : ℕ) (hn : 1 ≤ n) (ε : ZMod 3)
    (x : GGBCV n) :
    ∑ j, ggBCRootFun n ε ⟨n - 1, by omega⟩ j * x j =
      (2 / ε) * x ⟨n - 1, by omega⟩ := by
  have hlast : ¬ ((⟨n - 1, by omega⟩ : Fin n) : ℕ) + 1 < n := by
    dsimp only
    omega
  have hval : ((⟨n - 1, by omega⟩ : Fin n) : ℕ) + 1 = n := by
    dsimp only
    omega
  rw [Finset.sum_eq_single (⟨n - 1, by omega⟩ : Fin n)]
  · simp [ggBCRootFun, hval]
  · intro b _ hb
    have hbne : (b : ℕ) ≠ n - 1 := fun h => hb (Fin.ext h)
    have hcond : ¬ ((b : ℕ) + 1 = n) := by omega
    simp [ggBCRootFun, hlast, hcond]
  · intro h
    exact absurd (Finset.mem_univ _) h

private lemma ggBCDE_root_inj_BC {n : ℕ} (hn : 1 ≤ n) (ε : ZMod 3) (hε : ε ≠ 0)
    (x : GGBCV n) (hx : ∀ i, ∑ j, ggBCRootFun n ε i j * x j = 0) : x = 0 := by
  have h2ε : (2 / ε : ZMod 3) ≠ 0 := by
    intro h
    have h2 : (2 : ZMod 3) = 0 := by
      have := congrArg (fun z => z * ε) h
      rwa [div_mul_cancel₀ _ hε, zero_mul] at this
    exact (by decide : (2 : ZMod 3) ≠ 0) h2
  let last : Fin n := ⟨n - 1, by omega⟩
  have hlast0 : x last = 0 := by
    have h := hx last
    have hlast : last = ⟨n - 1, by omega⟩ := rfl
    rw [hlast, ggBCDE_sum_ggBCRootFun_last n hn ε x] at h
    exact (mul_eq_zero.mp h).resolve_left h2ε
  have hstep : ∀ (j : Fin n) (hj : (j : ℕ) + 1 < n),
      x j = x ⟨(j : ℕ) + 1, hj⟩ := by
    intro j hj
    have h := hx j
    rw [ggBCDE_sum_ggBCRootFun_chain n ε j hj] at h
    exact sub_eq_zero.mp h
  have hall : ∀ j : Fin n, x j = x last := by
    have hdesc : ∀ m : ℕ, ∀ j : Fin n, n - 1 - (j : ℕ) = m → x j = x last := by
      intro m
      induction m using Nat.strong_induction_on with
      | _ m ih =>
        intro j hm
        by_cases hj : (j : ℕ) = n - 1
        · rw [show j = last from Fin.ext hj]
        · have hjlt : (j : ℕ) + 1 < n := by omega
          rw [hstep j hjlt]
          exact ih (n - 1 - ((j : ℕ) + 1)) (by omega) ⟨(j : ℕ) + 1, hjlt⟩ rfl
    intro j
    exact hdesc (n - 1 - (j : ℕ)) j rfl
  funext j
  rw [hall j, hlast0]
  rfl

private lemma ggBCDE_coroot_chain {n : ℕ} (i : Fin n) (hi : (i : ℕ) + 1 < n) (ε : ZMod 3) :
    ggBCCoroot n ε i =
      ((Pi.single i (1 : ZMod 3) : Fin n → ZMod 3) -
        (Pi.single ⟨(i : ℕ) + 1, hi⟩ (1 : ZMod 3) : Fin n → ZMod 3)) := by
  funext j
  by_cases h1 : j = i
  · subst h1
    have hne : j ≠ ⟨(j : ℕ) + 1, hi⟩ := by
      intro h
      have := Fin.ext_iff.mp h
      dsimp only at this
      omega
    simp [ggBCCoroot, hi, hne]
  · by_cases h2 : j = ⟨(i : ℕ) + 1, hi⟩
    · subst h2
      have hne' : i ≠ ⟨(i : ℕ) + 1, hi⟩ := by
        intro h
        have := Fin.ext_iff.mp h
        dsimp only at this
        omega
      simp [ggBCCoroot, hi, h1]
      rfl
    · have hj1 : (j : ℕ) ≠ i := fun h => h1 (Fin.ext h)
      have hj2 : (j : ℕ) ≠ (i : ℕ) + 1 := fun h => h2 (Fin.ext h)
      simp [ggBCCoroot, hi, h1, h2, hj1, hj2]

private lemma ggBCDE_coroot_last {n : ℕ} (i : Fin n) (hi : ¬ (i : ℕ) + 1 < n)
    (ε : ZMod 3) : ggBCCoroot n ε i = (Pi.single i ε : GGBCV n) := by
  funext j
  rw [ggBCCoroot, if_neg hi]
  by_cases hj : (j : ℕ) + 1 = n
  · rw [if_pos hj]
    have hji : j = i := Fin.ext (by omega)
    subst j
    rw [Pi.single_eq_same]
  · rw [if_neg hj]
    rw [Pi.single_eq_of_ne]
    intro hh
    exact hj (by rw [hh]; omega)

private lemma ggBCDE_dot_single {n : ℕ} (a : Fin n) (x : ZMod 3) (v : GGBCV n) :
    (Pi.single a x : GGBCV n) ⬝ᵥ v = x * v a := by
  simp only [dotProduct]
  rw [Finset.sum_eq_single a]
  · simp [Pi.single_eq_same]
  · intro b _ hb
    rw [Pi.single_eq_of_ne hb]
    simp
  · intro h
    exact absurd (Finset.mem_univ _) h

private lemma ggBCDE_norm_sub_single {n : ℕ} (a b : Fin n) (hab : a ≠ b) :
    ((Pi.single a (1 : ZMod 3) - Pi.single b (1 : ZMod 3) : GGBCV n) ⬝ᵥ
      (Pi.single a 1 - Pi.single b 1)) = 2 := by
  rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, ggBCDE_dot_single,
    ggBCDE_dot_single, ggBCDE_dot_single, ggBCDE_dot_single,
    Pi.single_eq_same, Pi.single_eq_of_ne hab, Pi.single_eq_of_ne (Ne.symm hab),
    Pi.single_eq_same]
  norm_num

private lemma ggBCDE_norm_smul_single {n : ℕ} (a : Fin n) (ε : ZMod 3)
    (hε : ε = 1 ∨ ε = -1) :
    (Pi.single a ε : GGBCV n) ⬝ᵥ Pi.single a ε = 1 := by
  rw [ggBCDE_dot_single, Pi.single_eq_same]
  rcases hε with rfl | rfl <;> norm_num

private lemma ggBCDE_wt_single_ne {n : ℕ} (a : Fin n) {x : ZMod 3} (hx : x ≠ 0) :
    ggBCWt (Pi.single a x : GGBCV n) = 1 := by
  unfold ggBCWt
  have hset : Finset.univ.filter (fun j => (Pi.single a x : GGBCV n) j ≠ 0) = {a} := by
    ext j
    rw [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨-, h⟩
      by_contra hji
      exact h (Pi.single_eq_of_ne (M := fun _ => ZMod 3) hji x)
    · rintro rfl
      exact ⟨Finset.mem_univ _, by simpa using hx⟩
  rw [hset, Finset.card_singleton]

private lemma ggBCDE_two_ne_zero : (2 : ZMod 3) ≠ 0 := by decide

private lemma ggBCDE_one_ne_zero : (1 : ZMod 3) ≠ 0 := by decide

private lemma ggBCDE_two_div_two : (2 / 2 : ZMod 3) = 1 :=
  div_self ggBCDE_two_ne_zero

private lemma ggBCDE_inv_eq (ε : ZMod 3) (hε : ε = 1 ∨ ε = -1) : ε⁻¹ = ε := by
  apply inv_eq_of_mul_eq_one_right
  rcases hε with rfl | rfl <;> norm_num

private lemma ggBCDE_two_div_eq (ε : ZMod 3) (hε : ε = 1 ∨ ε = -1) :
    (2 / ε : ZMod 3) = 2 * ε := by
  rw [div_eq_mul_inv, ggBCDE_inv_eq ε hε]

private lemma ggBCDE_neg_one_ne_zero : (-1 : ZMod 3) ≠ 0 := by norm_num

private lemma ggBCDE_sum_ggBCRootFun_last' {n : ℕ} (hn : 1 ≤ n) (ε : ZMod 3)
    (i : Fin n) (hi : ¬ (i : ℕ) + 1 < n) (x : GGBCV n) :
    ∑ j, ggBCRootFun n ε i j * x j = (2 / ε) * x i := by
  have hieq : i = ⟨n - 1, by omega⟩ := Fin.ext (by
    dsimp only
    omega)
  rw [hieq]
  exact ggBCDE_sum_ggBCRootFun_last n hn ε x

private lemma ggBCDE_coroot_mem_roots {n : ℕ} (i : Fin n) {ε : ZMod 3} (hε : ε ≠ 0) :
    ggBCCoroot n ε i ∈ ggBCRoots n := by
  by_cases hi : (i : ℕ) + 1 < n
  · rw [ggBCDE_coroot_chain i hi ε]
    have hwt : ggBCWt
        (Pi.single i (1 : ZMod 3) - Pi.single ⟨(i : ℕ) + 1, hi⟩ 1 : GGBCV n) = 2 :=
      ggQ2x_wt_sub_single i ⟨(i : ℕ) + 1, hi⟩ (by
        intro h
        have := congrArg Fin.val h
        dsimp only at this
        omega)
    rw [ggBCRoots, Set.mem_setOf_eq, hwt]
    omega
  · rw [ggBCDE_coroot_last i hi ε]
    have hwt : ggBCWt (Pi.single i ε : GGBCV n) = 1 := ggBCDE_wt_single_ne i hε
    rw [ggBCRoots, Set.mem_setOf_eq, hwt]
    omega

private theorem ggBCDE_rho_BC {n : ℕ} (hn : 3 ≤ n)
    (C : Matrix (Fin n) (Fin n) ℤ) (hC : GGIntCartan (CoxeterMatrix.B n) C) :
    GGWeylNoEichlerRho C := by
  classical
  intro U instACG instMod h α hb hspan hα g hg hgne
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hn1 : 1 ≤ n := by omega
  have hfr : Module.finrank (ZMod 3) U = n := by
    have h1 := finrank_span_eq_card hb
    rw [hspan, finrank_top, Fintype.card_fin] at h1
    exact h1
  let D' : GGQ2Lin 3 :=
    { ι := Fin n
      coxeter := CoxeterMatrix.B n
      cartan := C
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
        · have hB3 : (CoxeterMatrix.B n) (⟨0, by omega⟩ : Fin n) (⟨1, by omega⟩ : Fin n) = 3 :=
            ggBCDE_B_zero_one (n := n) (by omega) rfl rfl
          rcases hC.2 (⟨0, by omega⟩ : Fin n) (⟨1, by omega⟩ : Fin n) (by
              intro hh
              have := congrArg Fin.val hh
              simp at this) with
            ⟨hm, h1, -⟩ | ⟨hm, h1, -⟩ | ⟨hm, -, -, -⟩ | ⟨hm, -, -, -⟩
          · rw [hB3] at hm
            omega
          · rw [h1]
            decide
          · rw [hB3] at hm
            omega
          · rw [hB3] at hm
            omega
        · intro y hy
          obtain ⟨hyne, hyC⟩ := hy
          have hBne2 : (CoxeterMatrix.B n) (⟨0, by omega⟩ : Fin n) y ≠ 2 := by
            intro hm2
            rcases hC.2 (⟨0, by omega⟩ : Fin n) y hyne.symm with
              ⟨hm, h1, -⟩ | ⟨hm, h1, -⟩ | ⟨hm, -, -, -⟩ | ⟨hm, -, -, -⟩
            · exact hyC h1
            · rw [hm2] at hm
              omega
            · rw [hm2] at hm
              omega
            · rw [hm2] at hm
              omega
          have hyval : (y : ℕ) = 0 ∨ (y : ℕ) = 1 := by
            by_contra hcon
            push Not at hcon
            exact hBne2 (ggBCDE_B_zero_other (n := n) (by omega) rfl hcon.1 hcon.2)
          apply Fin.ext
          rcases hyval with h0 | h1
          · exact (hyne (Fin.ext h0)).elim
          · exact h1
      isWeyl := Or.inl ⟨n, Equiv.refl _, by omega,
        Or.inr (Or.inl ⟨by omega, (ggBCDE_reindex_refl (CoxeterMatrix.B n)).symm⟩)⟩
      isCartan := hC
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
  have hB : D'.coxeter = (CoxeterMatrix.B n).reindex (Equiv.refl (Fin n)) :=
    (ggBCDE_reindex_refl (CoxeterMatrix.B n)).symm
  obtain ⟨τ, ε, hε, hcor, hroot⟩ :=
    ggQ2_BC_coordinates D' hbas hn (Equiv.refl (Fin n)) hB
  have hroot' : ∀ i v, D'.root i v = ∑ j, ggBCRootFun n ε i j * τ v j := by
    intro i v
    simpa using hroot i v
  have hcor_clean : ∀ i, τ (D'.coroot i) = ggBCCoroot n ε i := by
    intro i
    simpa using hcor i
  have hc : ∀ i, (ggBCCoroot n ε i) ⬝ᵥ (ggBCCoroot n ε i) ≠ 0 := by
    intro i
    by_cases hi : (i : ℕ) + 1 < n
    · rw [ggBCDE_coroot_chain i hi ε,
        ggBCDE_norm_sub_single i ⟨(i : ℕ) + 1, hi⟩ (by
          intro h
          have := congrArg Fin.val h
          dsimp only at this
          omega)]
      exact ggBCDE_two_ne_zero
    · rw [ggBCDE_coroot_last i hi ε, ggBCDE_norm_smul_single i ε hε]
      exact ggBCDE_one_ne_zero
  have hsimple : ∀ i : Fin n,
      ggLinConj τ (D'.simpleRefl i) = ggBCRefl (ggBCCoroot n ε i) (hc i) := by
    intro i
    ext w
    have hw : w = τ (τ.symm w) := by rw [LinearEquiv.apply_symm_apply]
    rw [hw, ggLinConj_apply]
    simp only [LinearEquiv.symm_apply_apply]
    have hsr : D'.simpleRefl i (τ.symm w) =
        τ.symm w - D'.root i (τ.symm w) • D'.coroot i := by
      rw [show D'.simpleRefl i = Module.reflection (D'.root_coroot_self i) from rfl,
        Module.reflection_apply]
    rw [hsr, map_sub, map_smul, hcor_clean i, hroot' i (τ.symm w)]
    rw [show ggBCRefl (ggBCCoroot n ε i) (hc i) (τ (τ.symm w)) =
        τ (τ.symm w) -
          (((2 / ((ggBCCoroot n ε i) ⬝ᵥ (ggBCCoroot n ε i))) •
            ggBCDot (ggBCCoroot n ε i)) (τ (τ.symm w))) •
          ggBCCoroot n ε i from Module.reflection_apply _ _]
    rw [LinearMap.smul_apply, ggQ2x_ggBCDot_apply, smul_eq_mul]
    have hcoef : (∑ j, ggBCRootFun n ε i j * (τ (τ.symm w)) j) =
        (2 / ((ggBCCoroot n ε i) ⬝ᵥ (ggBCCoroot n ε i))) *
          ((ggBCCoroot n ε i) ⬝ᵥ (τ (τ.symm w))) := by
      by_cases hi : (i : ℕ) + 1 < n
      · have hdot : (Pi.single i (1 : ZMod 3) - Pi.single ⟨(i : ℕ) + 1, hi⟩ 1 : GGBCV n) ⬝ᵥ
            (τ (τ.symm w)) =
            (τ (τ.symm w)) i - (τ (τ.symm w)) ⟨(i : ℕ) + 1, hi⟩ := by
          rw [sub_dotProduct, ggBCDE_dot_single, ggBCDE_dot_single]
          ring
        rw [ggBCDE_sum_ggBCRootFun_chain n ε i hi, ggBCDE_coroot_chain i hi ε, hdot,
          ggBCDE_norm_sub_single i ⟨(i : ℕ) + 1, hi⟩ (by
            intro h
            have := congrArg Fin.val h
            dsimp only at this
            omega),
          ggBCDE_two_div_two]
        ring
      · have hdot : (Pi.single i ε : GGBCV n) ⬝ᵥ (τ (τ.symm w)) =
            ε * (τ (τ.symm w)) i := by
          rw [ggBCDE_dot_single]
        rw [ggBCDE_sum_ggBCRootFun_last' hn1 ε i hi, ggBCDE_coroot_last i hi ε,
          hdot, ggBCDE_norm_smul_single i ε hε, ggBCDE_two_div_eq ε hε]
        ring
    rw [hcoef]
  have hε0 : ε ≠ 0 := by
    rcases hε with h | h
    · rw [h]
      exact ggBCDE_one_ne_zero
    · rw [h]
      exact ggBCDE_neg_one_ne_zero
  have hgenmem : ∀ i : Fin n, ggLinConj τ (D'.simpleRefl i) ∈ ggBCW n := by
    intro i
    rw [hsimple i]
    exact Subgroup.subset_closure
      ⟨ggBCCoroot n ε i, ggBCDE_coroot_mem_roots i hε0, hc i, rfl⟩
  have hmap_le : Subgroup.map (ggLinConj τ).toMonoidHom D'.weyl ≤ ggBCW n := by
    rw [hWclos, MonoidHom.map_closure, Subgroup.closure_le]
    rintro t ⟨s, ⟨i, -, rfl⟩, rfl⟩
    exact hgenmem i
  have hmemBC : ggLinConj τ g ∈ ggBCReflGp (ggBCRoots n) := by
    have h := Subgroup.mem_map_of_mem (ggLinConj τ).toMonoidHom hg'
    have h' : ggLinConj τ g ∈ ggBCW n := hmap_le h
    simpa [ggBCW, ggBCReflGp] using h'
  obtain ⟨σ, ε', hε', hsingle⟩ :=
    ggBCReflGp_monomial (S := ggBCRoots n) (fun _ hx => hx) hmemBC
  have hne : ¬ GGEichler g :=
    ggBCDE_no_eichler_of_monomial τ g ((ggLinConj τ).toMonoidHom) (fun _ _ => rfl)
      ⟨σ, ε', hε', hsingle⟩
  have hinj : ∀ w : U, (∀ i, α i w = 0) → w = 0 := by
    intro w hw
    have hzero : τ w = 0 := by
      apply ggBCDE_root_inj_BC hn1 ε hε0 (τ w)
      intro i
      rw [← hroot' i w]
      simpa using hw i
    exact τ.injective (by rw [hzero, map_zero])
  by_contra hcon
  push Not at hcon
  have hN : ∀ v, g (g v) + g v + v = 0 := fun v => hinj _ (fun i => hcon v i)
  exact hne ⟨hgne, hN⟩

theorem ggWeylNoEichlerRho_B {n : ℕ} (hn : 5 ≤ n) : GGWeylNoEichlerRho (CartanMatrix.B n) :=
  ggBCDE_rho_BC (n := n) (by omega) (CartanMatrix.B n) (ggIntCartan_B n)

theorem ggWeylNoEichlerRho_C {n : ℕ} (hn : 5 ≤ n) : GGWeylNoEichlerRho (CartanMatrix.C n) :=
  ggBCDE_rho_BC (n := n) (by omega) (CartanMatrix.C n) (ggIntCartan_C n)

end CFSG.StandardType

end
