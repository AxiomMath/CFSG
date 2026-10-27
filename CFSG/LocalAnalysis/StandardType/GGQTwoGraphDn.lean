module

public import CFSG.LocalAnalysis.StandardType.GGQTwoGammaXGraphLinDefs
import CFSG.LocalAnalysis.StandardType.GGWAutModelNorm
import CFSG.LocalAnalysis.StandardType.GGQTwoDWeyl
import CFSG.LocalAnalysis.StandardType.GGQTwoDCoord

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma ggQ2gd_D_zero_one {n : ℕ} (hn : 4 ≤ n) {a0 b0 : Fin n}
    (ha0 : (a0 : ℕ) = 0) (hb0 : (b0 : ℕ) = 1) : CartanMatrix.D n a0 b0 ≠ 0 := by
  rw [CartanMatrix.D]
  simp only [Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> omega

private lemma ggQ2gd_D_zero_other {n : ℕ} (hn : 4 ≤ n) {a0 c : Fin n}
    (ha0 : (a0 : ℕ) = 0) (hc0 : (c : ℕ) ≠ 0) (hc1 : (c : ℕ) ≠ 1) :
    CartanMatrix.D n a0 c = 0 := by
  rw [CartanMatrix.D]
  simp only [Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> omega

private lemma ggQ2gd_reindex_refl {ι : Type*} (M : CoxeterMatrix ι) :
    M.reindex (Equiv.refl ι) = M :=
  CoxeterMatrix.ext (Matrix.ext fun _ _ => rfl)

private lemma ggQ2gd_linConj_symm_apply {p : ℕ} [Fact p.Prime] {V V' : Type} [AddCommGroup V]
    [Module (ZMod p) V] [AddCommGroup V'] [Module (ZMod p) V']
    (τ : V ≃ₗ[ZMod p] V') (g : V ≃ₗ[ZMod p] V) :
    ggLinConj τ.symm (ggLinConj τ g) = g := by
  ext v
  simp [ggLinConj_apply]

private lemma ggQ2gd_conj_bcRefl {n : ℕ} {U : Type} [AddCommGroup U] [Module (ZMod 3) U]
    (τ : U ≃ₗ[ZMod 3] GGBCV n) (z : GGBCV n) (hz : z ⬝ᵥ z ≠ 0)
    (h : ((ggBCDot z).comp τ.toLinearMap) (τ.symm z) = 2) :
    ggLinConj τ.symm (ggBCRefl z hz) = Module.reflection h := by
  have hzz : z ⬝ᵥ z = 2 := by
    simpa [LinearMap.comp_apply, ggQ2_DW_dot_apply] using h
  ext v
  rw [ggLinConj_apply, ggQ2_DW_bc_apply', Module.reflection_apply]
  change τ.symm (τ v + (z ⬝ᵥ (τ v) * (z ⬝ᵥ z)) • z) =
    v - (ggBCDot z) (τ v) • τ.symm z
  rw [map_add, map_smul, LinearEquiv.symm_apply_apply, hzz, ggQ2_DW_dot_apply]
  have h2 : ∀ x : ZMod 3, x * 2 = -x := by decide
  rw [h2, neg_smul, sub_eq_add_neg]

private theorem ggQ2gd_model {n : ℕ} (hn : 5 ≤ n) {U : Type} [AddCommGroup U]
    [Module (ZMod 3) U] (h : Fin n → U) (hli : LinearIndependent (ZMod 3) h)
    (hsp : Submodule.span (ZMod 3) (Set.range h) = ⊤)
    (α : Fin n → Module.Dual (ZMod 3) U)
    (hα : ∀ i j, α i (h j) = ((CartanMatrix.D n i j : ℤ) : ZMod 3)) :
    ∃ τ : U ≃ₗ[ZMod 3] GGBCV n,
      (∀ i, τ (h i) = ggDSimple 3 n i) ∧
      (∀ i v, α i v = ∑ j, ggDSimple 3 n i j * τ v j) ∧
      (ggQ2WeylOf h α).map (ggLinConj τ).toMonoidHom = ggQ2_DW_Wc 3 n (by omega) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hm4 : 4 ≤ n := by omega
  have hfr : Module.finrank (ZMod 3) U = n := by
    have h1 := finrank_span_eq_card hli
    rw [hsp, finrank_top, Fintype.card_fin] at h1
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
        · exact ggQ2gd_D_zero_one (n := n) (by omega) rfl rfl
        · intro y hy
          obtain ⟨hyne, hyC⟩ := hy
          have hyval : (y : ℕ) = 0 ∨ (y : ℕ) = 1 := by
            by_cases h0 : (y : ℕ) = 0
            · exact Or.inl h0
            · by_cases h1 : (y : ℕ) = 1
              · exact Or.inr h1
              · exfalso
                exact hyC (ggQ2gd_D_zero_other (n := n) (by omega) rfl h0 h1)
          rcases hyval with h0 | h1
          · exact (hyne (Fin.ext h0)).elim
          · exact Fin.ext h1
      isWeyl := Or.inl ⟨n, Equiv.refl _, by omega,
        Or.inr (Or.inr ⟨by omega, (ggQ2gd_reindex_refl (ggCoxeterMatrixD n)).symm⟩)⟩
      isCartan := ggIntCartan_D n
      pairing := fun i j => by simpa using hα i j }
  have hbas : D'.Basis := by
    change LinearIndependent (ZMod 3) h ∧ Fintype.card (Fin n) = Module.finrank (ZMod 3) U
    exact ⟨hli, by simp [hfr]⟩
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
  have hB : D'.coxeter = (ggCoxeterMatrixD n).reindex (Equiv.refl (Fin n)) :=
    (ggQ2gd_reindex_refl (ggCoxeterMatrixD n)).symm
  obtain ⟨τ, hτ, hroot⟩ :=
    ggQ2_D_coordinates (p := 3) (by decide) D' hbas (by omega) (Equiv.refl (Fin n)) hB
  have hmapWc : (D'.weyl).map (ggLinConj τ).toMonoidHom = ggQ2_DW_Wc 3 n (by omega) :=
    ggQ2_DW_linWeylMap D' (by omega) (Equiv.refl (Fin n)) τ hτ hroot
  exact ⟨τ, hτ, hroot, hweylEq ▸ hmapWc⟩

private lemma ggQ2gd_root_refl_mem {n : ℕ} (hn : 5 ≤ n) {U : Type} [AddCommGroup U]
    [Module (ZMod 3) U] {h : Fin n → U} {α : Fin n → Module.Dual (ZMod 3) U}
    (τ : U ≃ₗ[ZMod 3] GGBCV n)
    (hmap : (ggQ2WeylOf h α).map (ggLinConj τ).toMonoidHom = ggQ2_DW_Wc 3 n (by omega))
    {z : GGBCV n} (hz : z ∈ ggDRoots n) (hz0 : z ⬝ᵥ z ≠ 0) :
    ggLinConj τ.symm (ggBCRefl z hz0) ∈ ggQ2WeylOf h α := by
  have h4 : 4 ≤ n := by omega
  have hmem : ggBCRefl z hz0 ∈ ggQ2_DW_Wc 3 n h4 :=
    ggQ2_DW_Droot_refl_mem_Wc n h4 hz hz0
  rw [← hmap] at hmem
  obtain ⟨u, hu, hueq⟩ := Subgroup.mem_map.mp hmem
  change ggLinConj τ u = ggBCRefl z hz0 at hueq
  rw [show ggLinConj τ.symm (ggBCRefl z hz0) = u by
    rw [← hueq, ggQ2gd_linConj_symm_apply]]
  exact hu


private lemma ggQ2gd_single_dot {n : ℕ} (a : Fin n) (y : GGBCV n) :
    (Pi.single a (1 : ZMod 3) : GGBCV n) ⬝ᵥ y = y a := by
  rw [dotProduct, Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    rw [Pi.single_eq_of_ne hb]
    simp
  · intro ha
    exact absurd (Finset.mem_univ a) ha

private lemma ggQ2gd_lt {n : ℕ} (i : Fin (n - 1)) : (i : ℕ) < n :=
  lt_of_lt_of_le i.isLt (Nat.sub_le n 1)

private lemma ggQ2gd_succ_lt {n : ℕ} (i : Fin (n - 1)) : (i : ℕ) + 1 < n := by
  have h1 : (i : ℕ) + 1 ≤ n - 1 := Nat.succ_le_of_lt i.isLt
  have h2 : n - 1 ≤ n := Nat.sub_le n 1
  omega

private noncomputable def ggQ2gd_z {n : ℕ} (δ : GGBCV n) (i : Fin (n - 1)) : GGBCV n :=
  Pi.single ⟨(i : ℕ), ggQ2gd_lt i⟩ (1 : ZMod 3) -
    (δ ⟨(i : ℕ), ggQ2gd_lt i⟩ * δ ⟨(i : ℕ) + 1, ggQ2gd_succ_lt i⟩) •
      Pi.single ⟨(i : ℕ) + 1, ggQ2gd_succ_lt i⟩ (1 : ZMod 3)

private lemma ggQ2gd_z_apply {n : ℕ} (δ : GGBCV n) (i : Fin (n - 1))
    (k : Fin n) :
    ggQ2gd_z δ i k =
      (if (k : ℕ) = (i : ℕ) then (1 : ZMod 3) else 0) -
        (δ ⟨(i : ℕ), ggQ2gd_lt i⟩ * δ ⟨(i : ℕ) + 1, ggQ2gd_succ_lt i⟩) *
          (if (k : ℕ) = (i : ℕ) + 1 then (1 : ZMod 3) else 0) := by
  simp only [ggQ2gd_z, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
    Fin.ext_iff]

private lemma ggQ2gd_z_self {n : ℕ} (δ : GGBCV n) (i : Fin (n - 1)) :
    ggQ2gd_z δ i ⟨(i : ℕ), ggQ2gd_lt i⟩ = 1 := by
  rw [ggQ2gd_z_apply]
  simp

private lemma ggQ2gd_z_succ {n : ℕ} (δ : GGBCV n) (i : Fin (n - 1)) :
    ggQ2gd_z δ i ⟨(i : ℕ) + 1, ggQ2gd_succ_lt i⟩ =
      -(δ ⟨(i : ℕ), ggQ2gd_lt i⟩ * δ ⟨(i : ℕ) + 1, ggQ2gd_succ_lt i⟩) := by
  rw [ggQ2gd_z_apply]
  simp

private lemma ggQ2gd_z_other {n : ℕ} (δ : GGBCV n) (i : Fin (n - 1))
    (k : Fin n) (h1 : (k : ℕ) ≠ (i : ℕ)) (h2 : (k : ℕ) ≠ (i : ℕ) + 1) :
    ggQ2gd_z δ i k = 0 := by
  rw [ggQ2gd_z_apply]
  simp [h1, h2]

private lemma ggQ2gd_z_dot {n : ℕ} (δ : GGBCV n) (i : Fin (n - 1))
    (x : GGBCV n) :
    ggQ2gd_z δ i ⬝ᵥ x =
      x ⟨(i : ℕ), ggQ2gd_lt i⟩ -
        (δ ⟨(i : ℕ), ggQ2gd_lt i⟩ * δ ⟨(i : ℕ) + 1, ggQ2gd_succ_lt i⟩) *
          x ⟨(i : ℕ) + 1, ggQ2gd_succ_lt i⟩ := by
  rw [ggQ2gd_z, sub_dotProduct, smul_dotProduct, ggQ2gd_single_dot, ggQ2gd_single_dot,
    smul_eq_mul]

private lemma ggQ2gd_z_dot_delta {n : ℕ} (δ : GGBCV n)
    (hδ : ∀ k, δ k ≠ 0) (i : Fin (n - 1)) : ggQ2gd_z δ i ⬝ᵥ δ = 0 := by
  rw [ggQ2gd_z_dot]
  have h1 : δ ⟨(i : ℕ), ggQ2gd_lt i⟩ ≠ 0 := hδ _
  have h2 : δ ⟨(i : ℕ) + 1, ggQ2gd_succ_lt i⟩ ≠ 0 := hδ _
  have hsq2 : δ ⟨(i : ℕ) + 1, ggQ2gd_succ_lt i⟩ * δ ⟨(i : ℕ) + 1, ggQ2gd_succ_lt i⟩ = 1 :=
    ggQ2_DW_sq _ h2
  rw [show δ ⟨(i : ℕ), ggQ2gd_lt i⟩ - (δ ⟨(i : ℕ), ggQ2gd_lt i⟩ * δ ⟨(i : ℕ) + 1, ggQ2gd_succ_lt i⟩) *
      δ ⟨(i : ℕ) + 1, ggQ2gd_succ_lt i⟩ =
      δ ⟨(i : ℕ), ggQ2gd_lt i⟩ * (1 - δ ⟨(i : ℕ) + 1, ggQ2gd_succ_lt i⟩ *
        δ ⟨(i : ℕ) + 1, ggQ2gd_succ_lt i⟩) by ring, hsq2, sub_self, mul_zero]

private lemma ggQ2gd_z_wt {n : ℕ} (δ : GGBCV n) (hδ : ∀ k, δ k ≠ 0)
    (i : Fin (n - 1)) : ggBCWt (ggQ2gd_z δ i) = 2 := by
  have h1 : δ ⟨(i : ℕ), ggQ2gd_lt i⟩ ≠ 0 := hδ _
  have h2 : δ ⟨(i : ℕ) + 1, ggQ2gd_succ_lt i⟩ ≠ 0 := hδ _
  have hprod : δ ⟨(i : ℕ), ggQ2gd_lt i⟩ * δ ⟨(i : ℕ) + 1, ggQ2gd_succ_lt i⟩ ≠ 0 :=
    mul_ne_zero h1 h2
  have hi : (⟨(i : ℕ), ggQ2gd_lt i⟩ : Fin n) ≠ ⟨(i : ℕ) + 1, ggQ2gd_succ_lt i⟩ := by
    intro hh
    have := congrArg Fin.val hh
    simp at this
  unfold ggBCWt
  have hfilter : (Finset.univ.filter fun k => ggQ2gd_z δ i k ≠ 0) =
      ({⟨(i : ℕ), ggQ2gd_lt i⟩, ⟨(i : ℕ) + 1, ggQ2gd_succ_lt i⟩} : Finset (Fin n)) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro hk
      by_contra h
      push Not at h
      obtain ⟨hk1, hk2⟩ := h
      apply hk
      exact ggQ2gd_z_other δ i k (fun hh => hk1 (Fin.ext hh))
        (fun hh => hk2 (Fin.ext hh))
    · rintro (rfl | rfl)
      · rw [ggQ2gd_z_self]
        exact one_ne_zero
      · rw [ggQ2gd_z_succ]
        exact neg_ne_zero.mpr hprod
  rw [hfilter, Finset.card_pair hi]

private lemma ggQ2gd_z_dot_self {n : ℕ} (δ : GGBCV n)
    (hδ : ∀ k, δ k ≠ 0) (i : Fin (n - 1)) : ggQ2gd_z δ i ⬝ᵥ ggQ2gd_z δ i = 2 := by
  rw [ggQ2_DW_A_dot_self_eq_wt, ggQ2gd_z_wt δ hδ i]
  rfl

private lemma ggQ2gd_z_dot_succ {n : ℕ} (δ : GGBCV n) (i : Fin (n - 1))
    (hi : (i : ℕ) + 1 < n - 1) :
    ggQ2gd_z δ i ⬝ᵥ ggQ2gd_z δ ⟨(i : ℕ) + 1, hi⟩ =
      -(δ ⟨(i : ℕ), lt_of_lt_of_le i.isLt (Nat.sub_le n 1)⟩ *
        δ ⟨(i : ℕ) + 1, lt_of_lt_of_le hi (Nat.sub_le n 1)⟩) := by
  rw [ggQ2gd_z_dot]
  have h1 : ggQ2gd_z δ ⟨(i : ℕ) + 1, hi⟩
      ⟨(i : ℕ), lt_of_lt_of_le i.isLt (Nat.sub_le n 1)⟩ = 0 := by
    refine ggQ2gd_z_other δ ⟨(i : ℕ) + 1, hi⟩ _ ?_ ?_
    · simp
    · simp
      omega
  have h2 : ggQ2gd_z δ ⟨(i : ℕ) + 1, hi⟩
      ⟨(i : ℕ) + 1, lt_of_lt_of_le hi (Nat.sub_le n 1)⟩ = 1 :=
    ggQ2gd_z_self δ ⟨(i : ℕ) + 1, hi⟩
  rw [h1, h2]
  ring

private lemma ggQ2gd_z_kernel {n : ℕ} (hn : 3 ≤ n) (δ : GGBCV n)
    (hδ : ∀ k, δ k ≠ 0) {x : GGBCV n}
    (hx : ∀ i : Fin (n - 1), ggQ2gd_z δ i ⬝ᵥ x = 0) :
    x ∈ Submodule.span (ZMod 3) {δ} := by
  have hstep : ∀ (t : ℕ) (ht : t < n - 1),
      x ⟨t, ggQ2gd_lt ⟨t, ht⟩⟩ =
        δ ⟨t, ggQ2gd_lt ⟨t, ht⟩⟩ * δ ⟨t + 1, ggQ2gd_succ_lt ⟨t, ht⟩⟩ *
          x ⟨t + 1, ggQ2gd_succ_lt ⟨t, ht⟩⟩ := by
    intro t ht
    have h := hx ⟨t, ht⟩
    rw [ggQ2gd_z_dot] at h
    exact sub_eq_zero.mp h
  have hmain : ∀ (t : ℕ) (ht : t < n),
      x ⟨t, ht⟩ = δ ⟨0, by omega⟩ * x ⟨0, by omega⟩ * δ ⟨t, ht⟩ := by
    intro t
    induction t with
    | zero =>
        intro ht
        have hsq : δ (⟨0, by omega⟩ : Fin n) * δ (⟨0, by omega⟩ : Fin n) = 1 :=
          ggQ2_DW_sq _ (hδ _)
        rw [show δ ⟨0, by omega⟩ * x ⟨0, by omega⟩ * δ ⟨0, ht⟩ =
          x ⟨0, by omega⟩ * (δ ⟨0, by omega⟩ * δ ⟨0, by omega⟩) by ring, hsq, mul_one]
    | succ t ih =>
        intro ht
        have ht' : t < n := Nat.lt_of_succ_lt ht
        have hlt : t < n - 1 := Nat.lt_pred_iff.mpr ht
        have hrec : x ⟨t, ggQ2gd_lt ⟨t, hlt⟩⟩ =
            δ ⟨t, ggQ2gd_lt ⟨t, hlt⟩⟩ * δ ⟨t + 1, ggQ2gd_succ_lt ⟨t, hlt⟩⟩ *
              x ⟨t + 1, ggQ2gd_succ_lt ⟨t, hlt⟩⟩ := hstep t hlt
        have ihv : x ⟨t, ht'⟩ = δ ⟨0, by omega⟩ * x ⟨0, by omega⟩ * δ ⟨t, ht'⟩ :=
          ih ht'
        have ha : δ ⟨t, ggQ2gd_lt ⟨t, hlt⟩⟩ * δ ⟨t + 1, ggQ2gd_succ_lt ⟨t, hlt⟩⟩ *
            (δ ⟨t, ggQ2gd_lt ⟨t, hlt⟩⟩ * δ ⟨t + 1, ggQ2gd_succ_lt ⟨t, hlt⟩⟩) = 1 := by
          rw [show δ ⟨t, ggQ2gd_lt ⟨t, hlt⟩⟩ * δ ⟨t + 1, ggQ2gd_succ_lt ⟨t, hlt⟩⟩ *
              (δ ⟨t, ggQ2gd_lt ⟨t, hlt⟩⟩ * δ ⟨t + 1, ggQ2gd_succ_lt ⟨t, hlt⟩⟩) =
              (δ ⟨t, ggQ2gd_lt ⟨t, hlt⟩⟩ * δ ⟨t, ggQ2gd_lt ⟨t, hlt⟩⟩) *
                (δ ⟨t + 1, ggQ2gd_succ_lt ⟨t, hlt⟩⟩ *
                  δ ⟨t + 1, ggQ2gd_succ_lt ⟨t, hlt⟩⟩) by ring,
            ggQ2_DW_sq _ (hδ _), ggQ2_DW_sq _ (hδ _), one_mul]
        have hrec' : x ⟨t + 1, ht⟩ =
            δ ⟨t, ggQ2gd_lt ⟨t, hlt⟩⟩ * δ ⟨t + 1, ggQ2gd_succ_lt ⟨t, hlt⟩⟩ *
              x ⟨t, ht'⟩ := by
          calc x ⟨t + 1, ht⟩ =
              (δ ⟨t, ggQ2gd_lt ⟨t, hlt⟩⟩ * δ ⟨t + 1, ggQ2gd_succ_lt ⟨t, hlt⟩⟩) *
                ((δ ⟨t, ggQ2gd_lt ⟨t, hlt⟩⟩ * δ ⟨t + 1, ggQ2gd_succ_lt ⟨t, hlt⟩⟩) *
                  x ⟨t + 1, ggQ2gd_succ_lt ⟨t, hlt⟩⟩) := by
                rw [← mul_assoc, ha, one_mul]
            _ = (δ ⟨t, ggQ2gd_lt ⟨t, hlt⟩⟩ * δ ⟨t + 1, ggQ2gd_succ_lt ⟨t, hlt⟩⟩) *
                  x ⟨t, ggQ2gd_lt ⟨t, hlt⟩⟩ := by
                rw [← hrec]
            _ = (δ ⟨t, ggQ2gd_lt ⟨t, hlt⟩⟩ * δ ⟨t + 1, ggQ2gd_succ_lt ⟨t, hlt⟩⟩) *
                  x ⟨t, ht'⟩ := by rfl
        rw [hrec', ihv]
        have hsq : δ ⟨t, ggQ2gd_lt ⟨t, hlt⟩⟩ * δ ⟨t, ggQ2gd_lt ⟨t, hlt⟩⟩ = 1 :=
          ggQ2_DW_sq _ (hδ _)
        rw [show δ ⟨t, ggQ2gd_lt ⟨t, hlt⟩⟩ * δ ⟨t + 1, ggQ2gd_succ_lt ⟨t, hlt⟩⟩ *
            (δ ⟨0, by omega⟩ * x ⟨0, by omega⟩ * δ ⟨t, ht'⟩) =
            (δ ⟨0, by omega⟩ * x ⟨0, by omega⟩) *
              (δ ⟨t, ggQ2gd_lt ⟨t, hlt⟩⟩ * δ ⟨t, ggQ2gd_lt ⟨t, hlt⟩⟩) *
              δ ⟨t + 1, ggQ2gd_succ_lt ⟨t, hlt⟩⟩ by ring, hsq, mul_one]
  refine Submodule.mem_span_singleton.mpr ⟨δ ⟨0, by omega⟩ * x ⟨0, by omega⟩, ?_⟩
  funext k
  rw [Pi.smul_apply, smul_eq_mul]
  exact (hmain k.val k.isLt).symm

private lemma ggQ2gd_z_linearIndependent {n : ℕ} (δ : GGBCV n) :
    LinearIndependent (ZMod 3) (fun i : Fin (n - 1) => ggQ2gd_z δ i) := by
  rw [Fintype.linearIndependent_iff]
  intro c hsum
  by_contra hc
  push Not at hc
  obtain ⟨i0, hi0⟩ := hc
  let S : Finset (Fin (n - 1)) := Finset.univ.filter (fun i => c i ≠ 0)
  have hSne : S.Nonempty := ⟨i0, by simp [S, hi0]⟩
  let m := S.min' hSne
  have hmS : m ∈ S := Finset.min'_mem S hSne
  have hcm : c m ≠ 0 := (Finset.mem_filter.mp hmS).2
  have hmin : ∀ j, c j ≠ 0 → m ≤ j := by
    intro j hj
    exact Finset.min'_le S j (by simp [S, hj])
  have hcoord : (∑ j : Fin (n - 1), c j • ggQ2gd_z δ j) ⟨(m : ℕ), ggQ2gd_lt m⟩ = 0 := by
    rw [hsum]
    rfl
  rw [Finset.sum_apply] at hcoord
  simp only [Pi.smul_apply, smul_eq_mul] at hcoord
  have hsingle : (∑ j : Fin (n - 1),
      c j * ggQ2gd_z δ j ⟨(m : ℕ), ggQ2gd_lt m⟩) = c m := by
    rw [Finset.sum_eq_single m]
    · rw [ggQ2gd_z_apply]
      simp
    · intro j _ hjm
      by_cases hcj : c j = 0
      · simp [hcj]
      · have hmj : m < j := lt_of_le_of_ne (hmin j hcj) (Ne.symm hjm)
        have hval : (m : ℕ) < (j : ℕ) := hmj
        rw [ggQ2gd_z_apply]
        rw [if_neg (by omega : ¬ ((m : ℕ) = (j : ℕ))),
          if_neg (by omega : ¬ ((m : ℕ) = (j : ℕ) + 1))]
        ring
    · intro h
      exact absurd (Finset.mem_univ m) h
  rw [hsingle] at hcoord
  exact hcm hcoord

private lemma ggQ2gd_fin_univ_of_step {m : ℕ} (S : Set (Fin m)) (hne : S.Nonempty)
    (hstep : ∀ (t : ℕ) (ht : t + 1 < m),
      ((⟨t, by omega⟩ : Fin m) ∈ S ↔ (⟨t + 1, ht⟩ : Fin m) ∈ S)) :
    S = Set.univ := by
  obtain ⟨k, hk⟩ := hne
  have hklt : (k : ℕ) < m := k.isLt
  have hzero : ((⟨0, by omega⟩ : Fin m)) ∈ S := by
    have hdown : ∀ t : ℕ, t ≤ (k : ℕ) →
        ((⟨(k : ℕ) - t, by omega⟩ : Fin m)) ∈ S := by
      intro t
      induction t with
      | zero => intro _; simpa using hk
      | succ t ih =>
          intro ht
          have hle : t ≤ (k : ℕ) := by omega
          have hprev : ((⟨(k : ℕ) - t, by omega⟩ : Fin m)) ∈ S := ih hle
          have hlt : (k : ℕ) - (t + 1) + 1 < m := by omega
          have hstep' : ((⟨(k : ℕ) - (t + 1), by omega⟩ : Fin m) ∈ S ↔
              (⟨(k : ℕ) - (t + 1) + 1, hlt⟩ : Fin m) ∈ S) :=
            hstep ((k : ℕ) - (t + 1)) hlt
          have heq : (⟨(k : ℕ) - (t + 1) + 1, hlt⟩ : Fin m) =
              (⟨(k : ℕ) - t, by omega⟩ : Fin m) := by
            apply Fin.ext
            simp
            omega
          rw [heq] at hstep'
          exact hstep'.mpr hprev
    have hfin : ((⟨(k : ℕ) - (k : ℕ), by omega⟩ : Fin m)) ∈ S := hdown (k : ℕ) le_rfl
    have heq0 : ((⟨(k : ℕ) - (k : ℕ), by omega⟩ : Fin m)) = (⟨0, by omega⟩ : Fin m) := by
      apply Fin.ext
      simp
    rw [heq0] at hfin
    exact hfin
  have hup : ∀ (t : ℕ) (ht : t < m), ((⟨t, ht⟩ : Fin m)) ∈ S := by
    intro t
    induction t with
    | zero => intro ht; simpa using hzero
    | succ t ih =>
        intro ht
        have ht' : t < m := by omega
        have hs : ((⟨t, ht'⟩ : Fin m)) ∈ S := ih ht'
        have hstep' := hstep t ht
        exact hstep'.mp hs
  ext j
  simp only [Set.mem_univ, iff_true]
  exact hup j.val j.isLt


private theorem ggQ2gd_caseA {n : ℕ} (hn : 5 ≤ n) {U : Type} [AddCommGroup U]
    [Module (ZMod 3) U] {h : Fin n → U} {α : Fin n → Module.Dual (ZMod 3) U}
    (τ : U ≃ₗ[ZMod 3] GGBCV n)
    (hmap : (ggQ2WeylOf h α).map (ggLinConj τ).toMonoidHom = ggQ2_DW_Wc 3 n (by omega))
    (hfinU : Module.finrank (ZMod 3) U = n)
    (d : U) (δ : GGBCV n) (hδeq : τ d = δ) (hδ : ∀ k, δ k ≠ 0) :
    GGQ2KillFamily h α d := by
  classical
  let c : Fin (n - 1) → U := fun i => τ.symm (ggQ2gd_z δ i)
  let f : Fin (n - 1) → Module.Dual (ZMod 3) U :=
    fun i => (ggBCDot (ggQ2gd_z δ i)).comp τ.toLinearMap
  have hfc : ∀ i, f i (c i) = 2 := by
    intro i
    change ggBCDot (ggQ2gd_z δ i) (τ (τ.symm (ggQ2gd_z δ i))) = 2
    rw [LinearEquiv.apply_symm_apply, ggQ2_DW_dot_apply]
    exact ggQ2gd_z_dot_self δ hδ i
  have hzmem : ∀ i, ggQ2gd_z δ i ∈ ggDRoots n := by
    intro i
    exact ggQ2gd_z_wt δ hδ i
  have hznorm : ∀ i, ggQ2gd_z δ i ⬝ᵥ ggQ2gd_z δ i ≠ 0 := by
    intro i
    rw [ggQ2gd_z_dot_self δ hδ i]
    decide
  have hrefl : ∀ i, Module.reflection (hfc i) ∈ ggQ2WeylOf h α := by
    intro i
    rw [← ggQ2gd_conj_bcRefl τ (ggQ2gd_z δ i) (hznorm i) (hfc i)]
    exact ggQ2gd_root_refl_mem hn τ hmap (hzmem i) (hznorm i)
  have hfd : ∀ i, f i d = 0 := by
    intro i
    change ggBCDot (ggQ2gd_z δ i) (τ d) = 0
    rw [hδeq, ggQ2_DW_dot_apply]
    exact ggQ2gd_z_dot_delta δ hδ i
  have hconn : ∀ S : Set (Fin (n - 1)), S.Nonempty →
      (∀ i j, (f i (c j) ≠ 0 ∨ f j (c i) ≠ 0) → (i ∈ S ↔ j ∈ S)) → S = Set.univ := by
    intro S hS hclosed
    refine ggQ2gd_fin_univ_of_step S hS ?_
    intro t ht
    have hadj : f ⟨t, by omega⟩ (c ⟨t + 1, ht⟩) ≠ 0 := by
      change ggBCDot (ggQ2gd_z δ ⟨t, by omega⟩)
        (τ (τ.symm (ggQ2gd_z δ ⟨t + 1, ht⟩))) ≠ 0
      rw [LinearEquiv.apply_symm_apply, ggQ2_DW_dot_apply,
        ggQ2gd_z_dot_succ δ ⟨t, by omega⟩ ht]
      exact neg_ne_zero.mpr (mul_ne_zero (hδ _) (hδ _))
    exact hclosed _ _ (Or.inl hadj)
  have hkernel : ∀ u : U, (∀ i, f i u = 0) → u ∈ Submodule.span (ZMod 3) {d} := by
    intro u hu
    have hx : ∀ i, ggQ2gd_z δ i ⬝ᵥ τ u = 0 := by
      intro i
      have hi := hu i
      change ggBCDot (ggQ2gd_z δ i) (τ u) = 0 at hi
      rwa [ggQ2_DW_dot_apply] at hi
    obtain ⟨lam, hlam⟩ :=
      Submodule.mem_span_singleton.mp (ggQ2gd_z_kernel (by omega : 3 ≤ n) δ hδ hx)
    rw [Submodule.mem_span_singleton]
    refine ⟨lam, ?_⟩
    have hu' : τ.symm (τ u) = u := LinearEquiv.symm_apply_apply τ u
    rw [← hu', ← hlam, map_smul]
    congr 1
    rw [← hδeq, LinearEquiv.symm_apply_apply]
  let z : Fin (n - 1) → GGBCV n := fun i => ggQ2gd_z δ i
  set φ : GGBCV n →ₗ[ZMod 3] ZMod 3 := ggQ2_DW_dotLin 3 n δ with hφdef
  set Az : Submodule (ZMod 3) (GGBCV n) := Submodule.span (ZMod 3) (Set.range z) with hAzdef
  have hfinAz : Module.finrank (ZMod 3) Az = n - 1 := by
    dsimp only [Az, z]
    rw [finrank_span_eq_card (ggQ2gd_z_linearIndependent δ), Fintype.card_fin]
  have hker_le : Az ≤ φ.ker := by
    rw [hAzdef, Submodule.span_le]
    rintro - ⟨i, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, hφdef, ggQ2_DW_dotLin_apply]
    rw [show (∑ j : Fin n, δ j * z i j) = δ ⬝ᵥ z i from rfl, dotProduct_comm]
    simpa [dotProduct] using ggQ2gd_z_dot_delta δ hδ i
  have hφne : φ ≠ 0 := by
    intro h0
    have hval : φ (Pi.single (⟨0, by omega⟩ : Fin n) (1 : ZMod 3)) = 0 := by
      rw [h0]
      rfl
    rw [hφdef, ggQ2_DW_dotLin_apply] at hval
    have hsum : (∑ j : Fin n,
        δ j * (Pi.single (⟨0, by omega⟩ : Fin n) (1 : ZMod 3) : GGBCV n) j) =
        δ ⟨0, by omega⟩ := by
      rw [Finset.sum_eq_single (⟨0, by omega⟩ : Fin n)]
      · simp
      · intro b _ hb
        rw [Pi.single_eq_of_ne hb]
        simp
      · intro hmem
        exact absurd (Finset.mem_univ _) hmem
    rw [hsum] at hval
    exact hδ _ hval
  have hrange : φ.range = ⊤ := Module.Dual.range_eq_top_of_ne_zero hφne
  have hfinV : Module.finrank (ZMod 3) (GGBCV n) = n := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have hfinKer : Module.finrank (ZMod 3) φ.ker = n - 1 := by
    have h := LinearMap.finrank_range_add_finrank_ker φ
    rw [hrange, finrank_top, Module.finrank_self, hfinV] at h
    omega
  have hAz : Az = φ.ker :=
    Submodule.eq_of_le_of_finrank_eq hker_le (by rw [hfinAz, hfinKer])
  have hφδ : φ δ = (n : ZMod 3) := by
    rw [hφdef, ggQ2_DW_dotLin_apply]
    have hone : ∀ j : Fin n, δ j * δ j = (1 : ZMod 3) := fun j => ggQ2_DW_sq _ (hδ j)
    simp only [hone]
    simp
  have hτδ : (τ.symm : GGBCV n ≃ₗ[ZMod 3] U).toLinearMap δ = d := by
    rw [← hδeq]
    simp
  have hBmap : (Submodule.span (ZMod 3) {δ}).map
      (τ.symm : GGBCV n ≃ₗ[ZMod 3] U).toLinearMap =
      Submodule.span (ZMod 3) {d} := by
    rw [Submodule.map_span, Set.image_singleton, hτδ]
  have hAmap : Az.map (τ.symm : GGBCV n ≃ₗ[ZMod 3] U).toLinearMap =
      Submodule.span (ZMod 3) (Set.range c) := by
    rw [hAzdef, Submodule.map_span]
    congr 1
    ext x
    constructor
    · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨z i, ⟨i, rfl⟩, rfl⟩
  have hdisj : Submodule.span (ZMod 3) (Set.range c) ⊔
      Submodule.span (ZMod 3) {d} = ⊤ ∨
      (d ∈ Submodule.span (ZMod 3) (Set.range c) ∧
        Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range c)) + 1 =
          Module.finrank (ZMod 3) U) := by
    by_cases hn3 : (n : ZMod 3) = 0
    · right
      have hδAz : δ ∈ Az := by
        rw [hAz, LinearMap.mem_ker]
        rw [hφδ, hn3]
      have hdA : d ∈ Submodule.span (ZMod 3) (Set.range c) := by
        rw [← hAmap]
        refine Submodule.mem_map.mpr ⟨δ, hδAz, ?_⟩
        rw [← hδeq]
        exact τ.symm_apply_apply d
      have hfinA : Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range c)) = n - 1 := by
        rw [← hAmap, LinearEquiv.finrank_map_eq, hfinAz]
      exact ⟨hdA, by omega⟩
    · left
      have hφδne : φ δ ≠ 0 := by
        rw [hφδ]
        exact hn3
      have hδnotin : δ ∉ Az := by
        intro hmem
        have hzero : φ δ = 0 := by
          rw [hAz, LinearMap.mem_ker] at hmem
          exact hmem
        exact hφδne hzero
      have hsupz : Az ⊔ Submodule.span (ZMod 3) {δ} = ⊤ := by
        rw [eq_top_iff]
        intro x _
        rw [Submodule.mem_sup]
        refine ⟨x - (φ x / φ δ) • δ, ?_,
          (φ x / φ δ) • δ, Submodule.smul_mem _ _ (Submodule.subset_span rfl), ?_⟩
        · rw [hAz, LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul,
            div_mul_cancel₀ (φ x) hφδne]
          exact sub_self _
        · exact sub_add_cancel x ((φ x / φ δ) • δ)
      have hsup : Submodule.span (ZMod 3) (Set.range c) ⊔
          Submodule.span (ZMod 3) {d} = ⊤ := by
        have h := congrArg (Submodule.map (τ.symm : GGBCV n ≃ₗ[ZMod 3] U).toLinearMap) hsupz
        rw [Submodule.map_sup, hAmap, hBmap, Submodule.map_top,
          LinearMap.range_eq_top.mpr (LinearEquiv.surjective τ.symm)] at h
        exact h
      exact hsup
  exact ⟨Fin (n - 1), ⟨⟨0, by omega⟩⟩, c, f, hfc, hrefl, hfd, hconn, hkernel, hdisj⟩



private abbrev ggQ2gd_last (n : ℕ) (hn : 1 ≤ n) : Fin n := ⟨n - 1, by omega⟩

private noncomputable def ggQ2gd_negCoord {n : ℕ} (a : Fin n) : GGBCV n ≃ₗ[ZMod 3] GGBCV n :=
  ggBCRefl (Pi.single a (1 : ZMod 3)) (by
    rw [ggQ2gd_single_dot, Pi.single_eq_same]
    exact one_ne_zero)

private lemma ggQ2gd_negCoord_apply {n : ℕ} (a : Fin n) (v : GGBCV n) (k : Fin n) :
    ggQ2gd_negCoord a v k = if k = a then -v k else v k := by
  rw [ggQ2gd_negCoord, ggQ2_DW_bc_apply']
  have hcv : (Pi.single a (1 : ZMod 3) : GGBCV n) ⬝ᵥ v = v a := ggQ2gd_single_dot a v
  have hcc : (Pi.single a (1 : ZMod 3) : GGBCV n) ⬝ᵥ
      (Pi.single a (1 : ZMod 3) : GGBCV n) = 1 := by
    rw [ggQ2gd_single_dot]
    simp
  rw [hcv, hcc]
  by_cases h : k = a
  · subst h
    simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
    exact (by decide : ∀ x : ZMod 3, x + x = -x) (v k)
  · rw [if_neg h]
    simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne h, smul_eq_mul, mul_zero,
      add_zero]

private noncomputable def ggQ2gd_negLast {n : ℕ} (hn : 1 ≤ n) : GGBCV n ≃ₗ[ZMod 3] GGBCV n :=
  ggQ2gd_negCoord (ggQ2gd_last n hn)

private lemma ggQ2gd_negLast_apply {n : ℕ} (hn : 1 ≤ n) (v : GGBCV n) (k : Fin n) :
    ggQ2gd_negLast hn v k = if k = ggQ2gd_last n hn then -v k else v k := by
  rw [ggQ2gd_negLast, ggQ2gd_negCoord_apply]

private lemma ggQ2gd_negLast_apply_apply {n : ℕ} (hn : 1 ≤ n) (v : GGBCV n) :
    ggQ2gd_negLast hn (ggQ2gd_negLast hn v) = v := by
  funext k
  rw [ggQ2gd_negLast_apply, ggQ2gd_negLast_apply]
  by_cases h : k = ggQ2gd_last n hn <;> simp [h]

private lemma ggQ2gd_negLast_simple {n : ℕ} (hn : 2 ≤ n) (j : Fin n) :
    ggQ2gd_negLast (by omega : 1 ≤ n) (ggDSimple 3 n j) =
      ggDSimple 3 n (Equiv.swap (⟨n - 2, by omega⟩ : Fin n) (ggQ2gd_last n (by omega)) j) := by
  funext k
  rw [ggQ2gd_negLast_apply]
  have hk := k.isLt
  have hj := j.isLt
  by_cases h2 : (j : ℕ) = n - 2
  · have hjeq : j = ⟨n - 2, by omega⟩ := Fin.ext h2
    rw [hjeq, Equiv.swap_apply_left]
    simp only [ggDSimple, Fin.ext_iff]
    split_ifs <;> simp_all <;> omega
  · by_cases h1 : (j : ℕ) = n - 1
    · have hjeq : j = ggQ2gd_last n (by omega) := Fin.ext h1
      rw [hjeq, Equiv.swap_apply_right]
      simp only [ggDSimple, Fin.ext_iff]
      split_ifs <;> simp_all <;> omega
    · rw [Equiv.swap_apply_of_ne_of_ne (fun hh => h2 (by simpa using congrArg Fin.val hh))
        (fun hh => h1 (by simpa using congrArg Fin.val hh))]
      simp only [ggDSimple, Fin.ext_iff]
      split_ifs <;> simp_all <;> omega

private lemma ggQ2gd_pair_flip_eq {n : ℕ} (hn : 1 ≤ n) (i : Fin n)
    (hi : i ≠ ggQ2gd_last n hn) :
    ggQ2gd_negCoord i * ggQ2gd_negCoord (ggQ2gd_last n hn) =
      ggBCRefl ((Pi.single i (1 : ZMod 3) : GGBCV n) + Pi.single (ggQ2gd_last n hn) 1)
        (by rw [ggQ2_DW_add_norm i (ggQ2gd_last n hn) hi]; decide) *
      ggBCRefl ((Pi.single i (1 : ZMod 3) : GGBCV n) - Pi.single (ggQ2gd_last n hn) 1)
        (by rw [ggQ2_DW_sub_norm i (ggQ2gd_last n hn) hi]; decide) := by
  ext v k
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply,
    ggQ2_DW_bc_apply', ggQ2_DW_bc_apply', ggQ2gd_negCoord_apply, ggQ2gd_negCoord_apply]
  have hdadd : ((Pi.single i (1 : ZMod 3) : GGBCV n) + Pi.single (ggQ2gd_last n hn) 1) ⬝ᵥ
      ((Pi.single i (1 : ZMod 3) : GGBCV n) + Pi.single (ggQ2gd_last n hn) 1) = 2 :=
    ggQ2_DW_add_norm i (ggQ2gd_last n hn) hi
  have hdsub : ((Pi.single i (1 : ZMod 3) : GGBCV n) - Pi.single (ggQ2gd_last n hn) 1) ⬝ᵥ
      ((Pi.single i (1 : ZMod 3) : GGBCV n) - Pi.single (ggQ2gd_last n hn) 1) = 2 :=
    ggQ2_DW_sub_norm i (ggQ2gd_last n hn) hi
  have hdotadd : ∀ w : GGBCV n,
      ((Pi.single i (1 : ZMod 3) : GGBCV n) + Pi.single (ggQ2gd_last n hn) 1) ⬝ᵥ w =
        w i + w (ggQ2gd_last n hn) := by
    intro w
    rw [add_dotProduct, ggQ2gd_single_dot, ggQ2gd_single_dot]
  have hdotsub : ∀ w : GGBCV n,
      ((Pi.single i (1 : ZMod 3) : GGBCV n) - Pi.single (ggQ2gd_last n hn) 1) ⬝ᵥ w =
        w i - w (ggQ2gd_last n hn) := by
    intro w
    rw [sub_dotProduct, ggQ2gd_single_dot, ggQ2gd_single_dot]
  rw [hdotadd, hdotsub, hdadd, hdsub]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hia : k = i
  · have hib : ¬ k = ggQ2gd_last n hn := fun h => hi (hia.symm.trans h)
    simp [hia, hi, Ne.symm hi]
    generalize v i = x
    generalize v (ggQ2gd_last n hn) = y
    decide +revert
  · by_cases hib : k = ggQ2gd_last n hn
    · have hia' : ¬ k = i := fun h => hi (h.symm.trans hib)
      simp [hib, hi, Ne.symm hi]
      generalize v i = x
      generalize v (ggQ2gd_last n hn) = y
      decide +revert
    · simp [hia, hib, hi, Ne.symm hi]

private lemma ggQ2gd_pair_flip_apply {n : ℕ} (hn : 1 ≤ n) (i : Fin n)
    (hi : i ≠ ggQ2gd_last n hn) (x : GGBCV n) (hxi : x i = 0) :
    ggBCRefl ((Pi.single i (1 : ZMod 3) : GGBCV n) + Pi.single (ggQ2gd_last n hn) 1)
        (by rw [ggQ2_DW_add_norm i (ggQ2gd_last n hn) hi]; decide)
      (ggBCRefl ((Pi.single i (1 : ZMod 3) : GGBCV n) - Pi.single (ggQ2gd_last n hn) 1)
        (by rw [ggQ2_DW_sub_norm i (ggQ2gd_last n hn) hi]; decide) x) =
      ggQ2gd_negLast hn x := by
  rw [← LinearEquiv.mul_apply, ← ggQ2gd_pair_flip_eq hn i hi, LinearEquiv.mul_apply]
  funext k
  rw [ggQ2gd_negCoord_apply, ggQ2gd_negCoord_apply, ggQ2gd_negLast_apply]
  by_cases hk : k = ggQ2gd_last n hn
  · subst hk
    simp [Ne.symm hi]
  · rw [if_neg hk]
    by_cases hki : k = i
    · subst hki
      simp [hxi]
    · simp [hki]


private lemma ggQ2gd_tau_s {n : ℕ} (hn : 5 ≤ n) {U : Type} [AddCommGroup U]
    [Module (ZMod 3) U] {h : Fin n → U}
    (hsp : Submodule.span (ZMod 3) (Set.range h) = ⊤)
    (τ : U ≃ₗ[ZMod 3] GGBCV n) (hτ : ∀ i, τ (h i) = ggDSimple 3 n i)
    (s : U ≃ₗ[ZMod 3] U)
    (hsfork : ∀ j, s (h j) =
      h (Equiv.swap (⟨n - 2, by omega⟩ : Fin n) ⟨n - 1, by omega⟩ j))
    (v : U) :
    τ (s v) = ggQ2gd_negLast (by omega : 1 ≤ n) (τ v) := by
  have hcomp : (τ : U →ₗ[ZMod 3] GGBCV n) ∘ₗ (s : U →ₗ[ZMod 3] U) =
      (ggQ2gd_negLast (by omega : 1 ≤ n) :
        GGBCV n ≃ₗ[ZMod 3] GGBCV n).toLinearMap ∘ₗ (τ : U →ₗ[ZMod 3] GGBCV n) := by
    apply LinearMap.ext_on_range hsp
    intro j
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hsfork j, hτ, hτ]
    exact (ggQ2gd_negLast_simple (by omega : 2 ≤ n) j).symm
  exact congrArg (fun f => f v) hcomp

private lemma ggQ2gd_s_s {n : ℕ} (hn : 5 ≤ n) {U : Type} [AddCommGroup U]
    [Module (ZMod 3) U] {h : Fin n → U}
    (hsp : Submodule.span (ZMod 3) (Set.range h) = ⊤)
    (τ : U ≃ₗ[ZMod 3] GGBCV n) (hτ : ∀ i, τ (h i) = ggDSimple 3 n i)
    (s : U ≃ₗ[ZMod 3] U)
    (hsfork : ∀ j, s (h j) =
      h (Equiv.swap (⟨n - 2, by omega⟩ : Fin n) ⟨n - 1, by omega⟩ j))
    (v : U) : s (s v) = v := by
  apply τ.injective
  rw [ggQ2gd_tau_s hn hsp τ hτ s hsfork (s v),
    ggQ2gd_tau_s hn hsp τ hτ s hsfork v, ggQ2gd_negLast_apply_apply]

private theorem ggQ2gd_caseB {n : ℕ} (hn : 5 ≤ n) {U : Type} [AddCommGroup U]
    [Module (ZMod 3) U] {h : Fin n → U} {α : Fin n → Module.Dual (ZMod 3) U}
    (hli : LinearIndependent (ZMod 3) h)
    (hsp : Submodule.span (ZMod 3) (Set.range h) = ⊤)
    (hα : ∀ i j, α i (h j) = ((CartanMatrix.D n i j : ℤ) : ZMod 3))
    (τ : U ≃ₗ[ZMod 3] GGBCV n) (hτ : ∀ i, τ (h i) = ggDSimple 3 n i)
    (hmap : (ggQ2WeylOf h α).map (ggLinConj τ).toMonoidHom = ggQ2_DW_Wc 3 n (by omega))
    (d : U) (δ : GGBCV n) (hδeq : τ d = δ)
    (hδ0 : ∃ i, δ i = 0) :
    GGQ2LineCrit h α d := by
  classical
  intro T hT
  obtain ⟨s, -, -, hsfork, hcases⟩ :=
    ggQ2WeylNormD_fork hn h hli hsp α hα T hT
  have hu₁ : ∃ u₁ ∈ ggQ2WeylOf h α, u₁ d = s d := by
    obtain ⟨i, hzi⟩ := hδ0
    by_cases hil : i = ggQ2gd_last n (by omega : 1 ≤ n)
    · refine ⟨1, one_mem _, ?_⟩
      have hsdeq : s d = d := by
        apply τ.injective
        rw [ggQ2gd_tau_s hn hsp τ hτ s hsfork d, hδeq]
        funext k
        rw [ggQ2gd_negLast_apply]
        by_cases hk : k = ggQ2gd_last n (by omega : 1 ≤ n)
        · rw [if_pos hk]
          have hki : k = i := hk.trans hil.symm
          rw [hki, hzi, neg_zero]
        · rw [if_neg hk]
      rw [hsdeq]
      rfl
    · have hi' : i ≠ ggQ2gd_last n (by omega : 1 ≤ n) := hil
      have hsub_norm : ((Pi.single i (1 : ZMod 3) : GGBCV n) -
          Pi.single (ggQ2gd_last n (by omega : 1 ≤ n)) 1) ⬝ᵥ
          ((Pi.single i (1 : ZMod 3) : GGBCV n) -
            Pi.single (ggQ2gd_last n (by omega : 1 ≤ n)) 1) ≠ 0 := by
        rw [ggQ2_DW_sub_norm i (ggQ2gd_last n (by omega : 1 ≤ n)) hi']
        decide
      have hadd_norm : ((Pi.single i (1 : ZMod 3) : GGBCV n) +
          Pi.single (ggQ2gd_last n (by omega : 1 ≤ n)) 1) ⬝ᵥ
          ((Pi.single i (1 : ZMod 3) : GGBCV n) +
            Pi.single (ggQ2gd_last n (by omega : 1 ≤ n)) 1) ≠ 0 := by
        rw [ggQ2_DW_add_norm i (ggQ2gd_last n (by omega : 1 ≤ n)) hi']
        decide
      have hsub_root : ((Pi.single i (1 : ZMod 3) : GGBCV n) -
          Pi.single (ggQ2gd_last n (by omega : 1 ≤ n)) 1) ∈ ggDRoots n :=
        ggQ2_DW_Wt_sub_single i (ggQ2gd_last n (by omega : 1 ≤ n)) hi'
      have hadd_root : ((Pi.single i (1 : ZMod 3) : GGBCV n) +
          Pi.single (ggQ2gd_last n (by omega : 1 ≤ n)) 1) ∈ ggDRoots n :=
        ggQ2_DW_Wt_add_single i (ggQ2gd_last n (by omega : 1 ≤ n)) hi'
      let A : GGBCV n ≃ₗ[ZMod 3] GGBCV n :=
        ggBCRefl ((Pi.single i (1 : ZMod 3) : GGBCV n) +
          Pi.single (ggQ2gd_last n (by omega : 1 ≤ n)) 1) hadd_norm
      let B : GGBCV n ≃ₗ[ZMod 3] GGBCV n :=
        ggBCRefl ((Pi.single i (1 : ZMod 3) : GGBCV n) -
          Pi.single (ggQ2gd_last n (by omega : 1 ≤ n)) 1) hsub_norm
      have hA : ggLinConj τ.symm A ∈ ggQ2WeylOf h α :=
        ggQ2gd_root_refl_mem hn τ hmap hadd_root hadd_norm
      have hB : ggLinConj τ.symm B ∈ ggQ2WeylOf h α :=
        ggQ2gd_root_refl_mem hn τ hmap hsub_root hsub_norm
      have hmul : ggLinConj τ.symm (A * B) =
          ggLinConj τ.symm A * ggLinConj τ.symm B := map_mul _ _ _
      refine ⟨ggLinConj τ.symm (A * B), ?_, ?_⟩
      · rw [hmul]
        exact (ggQ2WeylOf h α).mul_mem hA hB
      apply τ.injective
      have hτu : τ (ggLinConj τ.symm (A * B) d) = ggQ2gd_negLast (by omega : 1 ≤ n) δ := by
        rw [ggLinConj_apply]
        change τ (τ.symm ((A * B) (τ d))) = ggQ2gd_negLast (by omega : 1 ≤ n) δ
        rw [LinearEquiv.apply_symm_apply, LinearEquiv.mul_apply, hδeq]
        exact ggQ2gd_pair_flip_apply (by omega : 1 ≤ n) i hil δ hzi
      rw [hτu, ggQ2gd_tau_s hn hsp τ hτ s hsfork d, hδeq]
  obtain ⟨u₁, hu₁W, hu₁d⟩ := hu₁
  have hss : s (s d) = d := ggQ2gd_s_s hn hsp τ hτ s hsfork d
  have hspan : ∀ c : ZMod 3, c • d ∈ Submodule.span (ZMod 3) {d} := fun c =>
    Submodule.smul_mem _ _ (Submodule.subset_span rfl)
  have hwd : ∀ w : U ≃ₗ[ZMod 3] U, w (w⁻¹ d) = d := by
    intro w
    rw [← LinearEquiv.mul_apply, mul_inv_cancel]
    rfl
  rcases hcases with ⟨w, hw, hTw | hTw⟩ | ⟨w, hw, hTw | hTw⟩
  · refine ⟨w⁻¹, (ggQ2WeylOf h α).inv_mem hw, ?_⟩
    rw [hTw, hwd]
    simp
  · refine ⟨w⁻¹, (ggQ2WeylOf h α).inv_mem hw, ?_⟩
    rw [hTw, hwd]
    simp
  · refine ⟨w⁻¹ * u₁, (ggQ2WeylOf h α).mul_mem ((ggQ2WeylOf h α).inv_mem hw) hu₁W, ?_⟩
    rw [hTw]
    have hw1 : w ((w⁻¹ * u₁) d) = u₁ d := by
      rw [← LinearEquiv.mul_apply, ← mul_assoc, mul_inv_cancel]
      rfl
    rw [hw1, hu₁d, hss]
    simp
  · refine ⟨w⁻¹ * u₁, (ggQ2WeylOf h α).mul_mem ((ggQ2WeylOf h α).inv_mem hw) hu₁W, ?_⟩
    rw [hTw]
    have hw1 : w ((w⁻¹ * u₁) d) = u₁ d := by
      rw [← LinearEquiv.mul_apply, ← mul_assoc, mul_inv_cancel]
      rfl
    rw [hw1, hu₁d, hss]
    simp


theorem ggQ2GraphAbsCore_D {n : ℕ} (hn : 5 ≤ n) : GGQ2GraphAbsCore n (CartanMatrix.D n) := by
  classical
  intro U instACG instMod h hli hsp α hα d hd
  have hfinU : Module.finrank (ZMod 3) U = n := by
    have h1 := finrank_span_eq_card hli
    rw [hsp, finrank_top, Fintype.card_fin] at h1
    exact h1
  obtain ⟨τ, hτ, hroot, hmap⟩ := ggQ2gd_model hn h hli hsp α hα
  set δ : GGBCV n := τ d with hδdef
  by_cases hδ0 : ∃ i, δ i = 0
  · exact Or.inr (ggQ2gd_caseB hn hli hsp hα τ hτ hmap d δ hδdef.symm hδ0)
  · push Not at hδ0
    exact Or.inl (ggQ2gd_caseA hn τ hmap hfinU d δ hδdef.symm hδ0)

end CFSG.StandardType

end
