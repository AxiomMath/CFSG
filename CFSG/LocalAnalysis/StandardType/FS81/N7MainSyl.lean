module

public import CFSG.LocalAnalysis.StandardType.FS81.N7MainMono
public import CFSG.LocalAnalysis.StandardType.FS81.N7MainE6

public section

namespace CFSG.StandardType.FrameRoute.FS81

open scoped Matrix Pointwise

private def nmh_F2 {X : Type} [Group X] [Finite X] (S : N7MSetup X) (A₀ : Finset (Fin 8)) :
    Set X :=
  {x | ∃ B : Finset (Fin 8), B ⊆ A₀ ∧ Even B.card ∧ S.ρ x = nmSgn B}

private def nmh_C {X : Type} [Group X] [Finite X] (S : N7MSetup X) (A₀ : Finset (Fin 8)) :
    Subgroup X :=
  Subgroup.centralizer (nmh_F2 S A₀)

private theorem nmh_diagonal_commute {σ : Equiv.Perm (Fin 8)} {s : Fin 8 → ZMod 3}
    (hs : IsSign s) {d : Fin 8 → ZMod 3}
    (h : spMat σ s * Matrix.diagonal d = Matrix.diagonal d * spMat σ s) :
    ∀ j, d (σ j) = d j := by
  intro j
  have hsj : s j ≠ 0 := by rcases hs j with h | h <;> rw [h] <;> decide
  have hc := congrFun (congrFun h (σ j)) j
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, spMat_apply] at hc
  simp only [if_true] at hc
  rw [mul_comm (d (σ j)) (s j)] at hc
  exact (mul_left_cancel₀ hsj hc).symm

theorem nm_perm_fixes_A0 {σ : Equiv.Perm (Fin 8)} {s : Fin 8 → ZMod 3}
    (hs : IsSign s) {A₀ : Finset (Fin 8)} (hA6 : A₀.card = 6)
    (hcomm : ∀ i m : Fin 8, i ∈ A₀ → m ∈ A₀ → i ≠ m →
      spMat σ s * nmSgn ({i, m} : Finset (Fin 8)) =
        nmSgn ({i, m} : Finset (Fin 8)) * spMat σ s) :
    ∀ i ∈ A₀, σ i = i := by
  intro i hi
  by_contra hne
  have hcard : ({σ i} : Finset (Fin 8)).card < (A₀.erase i).card := by
    rw [Finset.card_singleton, Finset.card_erase_of_mem hi, hA6]
    decide
  obtain ⟨m, hm_erase, hm_ne⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  have hmA : m ∈ A₀ := Finset.mem_of_mem_erase hm_erase
  have hmi : m ≠ i := Finset.ne_of_mem_erase hm_erase
  have hmσ : m ≠ σ i := by simpa using hm_ne
  have hcomm' : spMat σ s * Matrix.diagonal (fun l : Fin 8 =>
        if l ∈ ({i, m} : Finset (Fin 8)) then (-1 : ZMod 3) else 1) =
      Matrix.diagonal (fun l : Fin 8 =>
        if l ∈ ({i, m} : Finset (Fin 8)) then (-1 : ZMod 3) else 1) * spMat σ s :=
    hcomm i m hi hmA hmi.symm
  have hd := nmh_diagonal_commute hs hcomm'
  have hdi : (fun l : Fin 8 =>
      if l ∈ ({i, m} : Finset (Fin 8)) then (-1 : ZMod 3) else 1) i = -1 := by simp
  have hnotmem : σ i ∉ ({i, m} : Finset (Fin 8)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hne, fun h => hmσ h.symm⟩
  have hdσ : (fun l : Fin 8 =>
      if l ∈ ({i, m} : Finset (Fin 8)) then (-1 : ZMod 3) else 1) (σ i) = 1 := by
    simp [hnotmem]
  have hcontra : (1 : ZMod 3) = -1 := hdσ.symm.trans ((hd i).trans hdi)
  exact absurd hcontra (by decide)

theorem nm_perm_eq_one_of_fixes {σ : Equiv.Perm (Fin 8)} {A₀ : Finset (Fin 8)}
    (hA0 : 0 ∉ A₀) (hA6 : A₀.card = 6) (hσ0 : σ 0 = 0)
    (hσA : ∀ i ∈ A₀, σ i = i) : σ = 1 := by
  set T : Finset (Fin 8) := insert 0 A₀ with hTdef
  have hTcard : T.card = 7 := by
    rw [hTdef, Finset.card_insert_of_notMem hA0, hA6]
  have hTfix : ∀ i ∈ T, σ i = i := by
    intro i hi
    rw [hTdef] at hi
    rcases Finset.mem_insert.mp hi with rfl | hiA
    · exact hσ0
    · exact hσA i hiA
  have hcompl : (Finset.univ \ T).card = 1 := by
    rw [Finset.card_sdiff, Finset.card_univ, Fintype.card_fin, Finset.inter_univ, hTcard]
  obtain ⟨k, hk⟩ := Finset.card_eq_one.mp hcompl
  have hmemT : σ k ∈ T ↔ σ k ≠ k := by
    constructor
    · intro h hk_eq
      have : σ k ∈ Finset.univ \ T := by
        rw [hk]
        exact Finset.mem_singleton.mpr hk_eq
      exact (Finset.mem_sdiff.mp this).2 h
    · intro hne
      by_contra hnot
      have : σ k ∈ Finset.univ \ T := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hnot⟩
      rw [hk, Finset.mem_singleton] at this
      exact hne this
  have hkfix : σ k = k := by
    by_contra hne
    have hkT : σ k ∈ T := hmemT.mpr hne
    have h := hTfix (σ k) hkT
    exact hne (σ.injective h.symm).symm
  refine Equiv.ext fun j => ?_
  by_cases hj : j ∈ T
  · exact hTfix j hj
  · have : j ∈ Finset.univ \ T := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hj⟩
    rw [hk, Finset.mem_singleton] at this
    rw [this, hkfix]
    rfl

private theorem nmh_F_max {X : Type} [Group X] [Finite X] (S : N7MSetup X)
    (hY : ∀ x : X, (∀ a, a ∈ S.Fgrp ↔ x * a * x⁻¹ ∈ S.Fgrp) → S.ρ x ∈ evenAll0 7)
    {A₀ : Finset (Fin 8)} (hA0 : 0 ∉ A₀) (hA6 : A₀.card = 6)
    (Q : Subgroup X) (hQp : IsPGroup 2 Q) (hQC : Q ≤ nmh_C S A₀) (hFQ : S.Fgrp ≤ Q) :
    Q ≤ S.Fgrp := by
  by_contra hle
  let F' : Subgroup Q := S.Fgrp.subgroupOf Q
  have hF'_lt_top : F' < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h
    exact hle (by
      intro q hq
      have : (⟨q, hq⟩ : Q) ∈ F' := by rw [h]; exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp this)
  haveI : Group.IsNilpotent Q := IsPGroup.isNilpotent hQp
  have hnc : NormalizerCondition Q := normalizerCondition_of_isNilpotent
  obtain ⟨-, n, hn, hnnot⟩ := SetLike.lt_iff_le_and_exists.mp (hnc F' hF'_lt_top)
  have hn1_notin : (n : X) ∉ S.Fgrp := fun h => hnnot (Subgroup.mem_subgroupOf.mpr h)
  have hnormX : (n : X) ∈ Subgroup.normalizer S.Fgrp := by
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      have h1 : (⟨a, hFQ ha⟩ : Q) ∈ F' := Subgroup.mem_subgroupOf.mpr ha
      have h2 : n * (⟨a, hFQ ha⟩ : Q) * n⁻¹ ∈ F' :=
        (Subgroup.mem_normalizer_iff.mp hn (⟨a, hFQ ha⟩ : Q)).mp h1
      exact Subgroup.mem_subgroupOf.mp h2
    · intro ha
      have haQ : a ∈ Q := by
        have heq : (n : X)⁻¹ * ((n : X) * a * (n : X)⁻¹) * (n : X) = a := by group
        rw [← heq]
        exact Q.mul_mem (Q.mul_mem (Q.inv_mem n.2) (hFQ ha)) n.2
      have h1 : n * (⟨a, haQ⟩ : Q) * n⁻¹ ∈ F' := by
        rw [Subgroup.mem_subgroupOf]
        show (n : X) * a * (n : X)⁻¹ ∈ S.Fgrp
        exact ha
      exact Subgroup.mem_subgroupOf.mp
        ((Subgroup.mem_normalizer_iff.mp hn (⟨a, haQ⟩ : Q)).mpr h1)
  obtain ⟨σ, s, hs, ⟨hσ0, hps⟩, hρn⟩ := hY (n : X) hnormX
  have hnC : (n : X) ∈ nmh_C S A₀ := hQC n.2
  have hcomm : ∀ i m : Fin 8, i ∈ A₀ → m ∈ A₀ → i ≠ m →
      spMat σ s * nmSgn ({i, m} : Finset (Fin 8)) =
        nmSgn ({i, m} : Finset (Fin 8)) * spMat σ s := by
    intro i m hi hm him
    have hpair : ({i, m} : Finset (Fin 8)) ⊆ A₀ := by
      intro l hl
      rcases Finset.mem_insert.mp hl with rfl | hl'
      · exact hi
      · rw [Finset.mem_singleton.mp hl']; exact hm
    have heven : Even ({i, m} : Finset (Fin 8)).card := by
      rw [Finset.card_pair him]; exact even_two
    obtain ⟨x, hx⟩ := S.exists_of_mem_nmF (nmSgn_mem_nmF heven)
    have hxF2 : x ∈ nmh_F2 S A₀ := ⟨{i, m}, hpair, heven, hx⟩
    have hcx : x * (n : X) = (n : X) * x :=
      (Subgroup.mem_centralizer_iff.mp hnC) x hxF2
    have hmat : S.ρ x * S.ρ (n : X) = S.ρ (n : X) * S.ρ x := by
      have := congrArg S.ρ hcx
      rwa [map_mul, map_mul] at this
    rw [hx, hρn] at hmat
    exact hmat.symm
  have hfixA : ∀ i ∈ A₀, σ i = i := nm_perm_fixes_A0 hs hA6 hcomm
  have hσeq : σ = 1 := nm_perm_eq_one_of_fixes hA0 hA6 hσ0 hfixA
  have hρn_nmF : S.ρ (n : X) ∈ nmF := by
    rw [hρn, hσeq]
    exact ⟨1, s, hs, ⟨rfl, hps⟩, rfl⟩
  exact hn1_notin ((S.mem_Fgrp (n : X)).mpr hρn_nmF)

theorem nm_det_one_of_centralizer {X : Type} [Group X] [Finite X] (S : N7MSetup X)
    (hY : ∀ x : X, (∀ a, a ∈ S.Fgrp ↔ x * a * x⁻¹ ∈ S.Fgrp) → S.ρ x ∈ evenAll0 7)
    {A₀ : Finset (Fin 8)} (hA0 : 0 ∉ A₀) (hA6 : A₀.card = 6) {v : X} (hv : v * v = 1)
    (hc : ∀ x : X, (∃ B : Finset (Fin 8), B ⊆ A₀ ∧ Even B.card ∧ S.ρ x = nmSgn B) →
      v * x = x * v) :
    (S.ρ v).det = 1 := by
  classical
  have hvC : v ∈ nmh_C S A₀ := by
    rw [nmh_C, Subgroup.mem_centralizer_iff]
    intro x hx
    exact (hc x hx).symm
  have hF_le_C : S.Fgrp ≤ nmh_C S A₀ := by
    intro f hf
    rw [nmh_C, Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨B, -, hBeven, hBx⟩ := hx
    have hxnmF : S.ρ x ∈ nmF := hBx ▸ nmSgn_mem_nmF hBeven
    exact S.ρ_inj (by rw [map_mul, map_mul, nmF_comm hxnmF hf])
  have hmax : ∀ Q : Subgroup X, IsPGroup 2 Q → Q ≤ nmh_C S A₀ → S.Fgrp ≤ Q → Q ≤ S.Fgrp :=
    fun Q hQp hQC hFQ => nmh_F_max S hY hA0 hA6 Q hQp hQC hFQ
  have hSFp : IsPGroup 2 S.Fgrp := by
    intro f
    refine ⟨1, ?_⟩
    show f ^ (2 ^ 1) = 1
    rw [pow_one, pow_two]
    exact Subtype.ext (S.ρ_inj (by
      show S.ρ (f.1 * f.1) = S.ρ 1
      rw [map_mul, map_one]
      exact nmF_sq f.2))
  let C' := ↥(nmh_C S A₀)
  set F' : Subgroup C' := S.Fgrp.subgroupOf (nmh_C S A₀) with hF'def
  have hF'p : IsPGroup 2 F' := by
    rw [hF'def]
    exact hSFp.comap_subtype (K := nmh_C S A₀)
  have hF'max : ∀ (R : Subgroup C'), IsPGroup 2 R → F' ≤ R → R = F' := by
    intro R hRp hFR
    have hRmap : IsPGroup 2 (R.map (nmh_C S A₀).subtype) := hRp.map _
    have hRmap_le : R.map (nmh_C S A₀).subtype ≤ nmh_C S A₀ := Subgroup.map_subtype_le R
    have hF'map : F'.map (nmh_C S A₀).subtype = S.Fgrp := by
      rw [hF'def]
      exact Subgroup.map_subgroupOf_eq_of_le hF_le_C
    have hFRmap : S.Fgrp ≤ R.map (nmh_C S A₀).subtype := by
      rw [← hF'map]
      exact Subgroup.map_mono hFR
    have hle := nmh_F_max S hY hA0 hA6 (R.map (nmh_C S A₀).subtype) hRmap hRmap_le hFRmap
    have hmaple : R.map (nmh_C S A₀).subtype ≤ F'.map (nmh_C S A₀).subtype := by
      rw [hF'map]; exact hle
    exact le_antisymm
      ((Subgroup.map_le_map_iff_of_injective (nmh_C S A₀).subtype_injective).mp hmaple) hFR
  set F'syl : Sylow 2 C' :=
    { toSubgroup := F'
      isPGroup' := hF'p
      is_maximal' := fun {R} hRp hFR => hF'max R hRp hFR } with hF'syldef
  let vC : C' := ⟨v, hvC⟩
  have hvCp : IsPGroup 2 (Subgroup.zpowers vC) := by
    refine IsPGroup.of_card_dvd_pow (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_iff_pow_eq_one.mpr (Subtype.ext (by rw [pow_two]; exact hv))
  obtain ⟨P, hPle⟩ := IsPGroup.exists_le_sylow hvCp
  obtain ⟨c, hc_eq⟩ := MulAction.exists_smul_eq C' P F'syl
  have hvP : vC ∈ P := hPle (Subgroup.mem_zpowers vC)
  have hconj : c * vC * c⁻¹ ∈ F' := by
    have hmem : MulAut.conj c • vC ∈ ((c • P : Sylow 2 C') : Subgroup C') := by
      rw [Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul vC (MulAut.conj c) (P : Subgroup C') hvP
    have hc_eq' : ((c • P : Sylow 2 C') : Subgroup C') = F' := by
      have := congrArg (fun S : Sylow 2 C' => (S : Subgroup C')) hc_eq
      simpa only [hF'syldef] using this
    rw [hc_eq'] at hmem
    simpa [MulAut.conj_apply] using hmem
  have hmemF : S.ρ (c.1 * v * c.1⁻¹) ∈ nmF := by
    have hsub : ((c * vC * c⁻¹ : C') : X) ∈ S.Fgrp := Subgroup.mem_subgroupOf.mp hconj
    exact (S.mem_Fgrp _).mp hsub
  obtain ⟨B, hBeven, hB⟩ := exists_nmSgn_of_mem_nmF hmemF
  have hdetB : (S.ρ (c.1 * v * c.1⁻¹)).det = 1 := by
    rw [hB, nmSgn, Matrix.det_diagonal, Finset.prod_ite, Finset.filter_mem_eq_inter,
      Finset.univ_inter, Finset.prod_const, Finset.prod_const_one, mul_one]
    exact Even.neg_one_pow hBeven
  have hAAinv : S.ρ c.1 * S.ρ (c.1⁻¹) = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  have hdet_eq : (S.ρ (c.1 * v * c.1⁻¹)).det = (S.ρ v).det := by
    rw [map_mul, map_mul]
    rw [Matrix.det_mul_right_comm (S.ρ c.1) (S.ρ v) (S.ρ (c.1⁻¹)), hAAinv, Matrix.one_mul]
  calc (S.ρ v).det = (S.ρ (c.1 * v * c.1⁻¹)).det := hdet_eq.symm
    _ = 1 := hdetB

end CFSG.StandardType.FrameRoute.FS81

end
