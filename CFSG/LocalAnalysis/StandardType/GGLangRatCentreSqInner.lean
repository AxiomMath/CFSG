module

public import CFSG.LocalAnalysis.StandardType.GGLangRatCentreStmts
public import Certificates.Certificate13659

import CFSG.HardMathSupport.Timmesfeld.RootAut.Main
import CFSG.LieType.Chevalley.WeylRoots
import CFSG.LocalAnalysis.StandardType.GGLangOrbitTwo

public section

namespace CFSG.StandardType.LangRat

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.RootAut
open scoped TensorProduct

private def langRatCI_closure {τ : Tag} (Ψ : Set (Fin τ.rank → ℤ)) : Subgroup (WeylGroup τ) :=
  Subgroup.closure {s : WeylGroup τ | ∃ γ ∈ Ψ, s = rootReflection γ}

private theorem langRatCI_map_add_zsmul {τ : Tag}
    {Ψ : Set (Fin τ.rank → ℤ)} {g : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ} (hg : IsIsometry Ψ g)
    {x y : Fin τ.rank → ℤ} (hx : x ∈ Ψ) (hy : y ∈ Ψ) (c : ℤ) (h : x + c • y ∈ Ψ) :
    g (x + c • y) = g x + c • g y := by
  have hs : ∀ w ∈ ({x, y} : Finset (Fin τ.rank → ℤ)), w ∈ Ψ := by
    intro w hw
    rcases Finset.mem_insert.1 hw with rfl | hw
    · exact hx
    · exact Finset.mem_singleton.1 hw ▸ hy
  have hsum : x + c • y = ∑ w ∈ ({x, y} : Finset (Fin τ.rank → ℤ)),
      ((if w = x then (1 : ℤ) else 0) + (if w = y then c else 0)) • w := by
    by_cases hxy : x = y
    · subst hxy
      simp [add_smul, one_smul]
    · have hyx : y ≠ x := Ne.symm hxy
      rw [Finset.sum_insert (by simp [hxy]), Finset.sum_singleton]
      simp [hxy, hyx, add_smul, one_smul]
  rw [apply_eq_sum_of_iform hg.iform_eq hs h hsum]
  by_cases hxy : x = y
  · subst hxy
    simp [add_smul, one_smul]
  · have hyx : y ≠ x := Ne.symm hxy
    rw [Finset.sum_insert (by simp [hxy]), Finset.sum_singleton]
    simp [hxy, hyx, add_smul, one_smul]

private theorem langRatCI_map_sub_zsmul {τ : Tag}
    {Ψ : Set (Fin τ.rank → ℤ)} {g : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ} (hg : IsIsometry Ψ g)
    {x y : Fin τ.rank → ℤ} (hx : x ∈ Ψ) (hy : y ∈ Ψ) (c : ℤ) (h : x - c • y ∈ Ψ) :
    g (x - c • y) = g x - c • g y := by
  have h' : x + (-c) • y ∈ Ψ := by simpa only [sub_eq_add_neg, neg_smul] using h
  have hlin := langRatCI_map_add_zsmul hg hx hy (-c) h'
  simpa only [sub_eq_add_neg, neg_smul] using hlin

private theorem langRatCI_map_rootReflection {τ : Tag}
    {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ)
    {g : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ} (hg : IsIsometry Ψ g)
    {β : Fin τ.rank → ℤ} (hβ : β ∈ Ψ) {z : Fin τ.rank → ℤ} (hz : z ∈ Ψ) :
    g (rootReflection β • z) = rootReflection (g β) • g z := by
  have hβr : IsRoot τ β := hΨ.isRoot β hβ
  have hgβ : g β ∈ Ψ := hg.bijOn.mapsTo hβ
  have hgβr : IsRoot τ (g β) := hΨ.isRoot (g β) hgβ
  have hmem : rootReflection β • z ∈ Ψ := hΨ.reflection_mem z hz β hβ
  rw [rootReflection_smul hβr z, rootReflection_smul hgβr (g z)]
  rw [corootPair_isometry hg hβ hz]
  exact langRatCI_map_sub_zsmul hg hz hβ (corootPair β z)
    (by rwa [rootReflection_smul hβr z] at hmem)

private theorem langRatCI_exists_conj {τ : Tag}
    {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ)
    {g : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ} (hg : IsIsometry Ψ g)
    {a : WeylGroup τ} (ha : a ∈ componentWeylGroup Ψ) :
    ∃ y ∈ langRatCI_closure Ψ, ∀ z ∈ Ψ, g (a • z) = y • g z := by
  classical
  induction ha using Subgroup.closure_induction with
  | mem s hs =>
    obtain ⟨β, hβ, rfl⟩ := hs
    exact ⟨rootReflection (g β),
      Subgroup.subset_closure ⟨g β, hg.bijOn.mapsTo (simpleRoots_subset hβ), rfl⟩,
      fun z hz => langRatCI_map_rootReflection hΨ hg (simpleRoots_subset hβ) hz⟩
  | one => exact ⟨1, one_mem _, fun z hz => by simp⟩
  | mul a b ha hb iha ihb =>
    obtain ⟨ya, hya, hya'⟩ := iha
    obtain ⟨yb, hyb, hyb'⟩ := ihb
    refine ⟨ya * yb, mul_mem hya hyb, fun z hz => ?_⟩
    rw [mul_smul, hya' _ (smul_mem_of_mem_componentWeylGroup hΨ hb z hz), hyb' z hz, mul_smul]
  | inv a ha iha =>
    obtain ⟨ya, hya, hya'⟩ := iha
    refine ⟨ya⁻¹, inv_mem hya, fun z hz => ?_⟩
    have hz' : a⁻¹ • z ∈ Ψ := smul_mem_of_mem_componentWeylGroup hΨ (inv_mem ha) z hz
    have h1 := hya' (a⁻¹ • z) hz'
    rw [smul_inv_smul] at h1
    have h2 := congrArg (fun v => ya⁻¹ • v) h1
    simp only [inv_smul_smul] at h2
    exact h2.symm

private theorem langRatCI_twistInner_sq {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)}
    {σ : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ} (hbij : Set.BijOn σ Ψ Ψ)
    (h : twistInner Ψ σ) : twistInner Ψ (σ^[2]) := by
  obtain ⟨a, ha, hσ⟩ := h
  refine ⟨a * a, mul_mem ha ha, fun γ hγ => ?_⟩
  have hγ' : σ γ ∈ Ψ := hbij.mapsTo hγ
  change σ (σ γ) = (a * a) • γ
  rw [hσ (σ γ) hγ', hσ γ hγ, mul_smul]

private theorem langRatCI_symmetrizer_self {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8)
    (j : Fin τ.rank) : τ.symmetrizer j j = 1 := by
  rcases hτ with rfl | rfl <;> revert j <;> decide

private theorem langRatCI_iform_self_eq_two {τ : Tag}
    (hτ : τ = .E7 ∨ τ = .E8) {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) :
    iform β β = 2 := by
  obtain ⟨w, j, rfl⟩ := isRoot_iff_exists_smul_single.1 hβ
  rw [iform_smul, iform_single_single, langRatCI_symmetrizer_self hτ j]
  ring

private theorem langRatCI_corootPair_eq_iform {τ : Tag}
    {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (h2 : iform β β = 2)
    (γ : Fin τ.rank → ℤ) : corootPair β γ = iform β γ := by
  have h := corootPair_mul hβ γ
  rw [h2] at h
  omega

private theorem langRatCI_cartanA_neg_one_iff {n : ℕ} (i j : Fin n) :
    CartanMatrix.A n i j = -1 ↔ i.val + 1 = j.val ∨ j.val + 1 = i.val := by
  rw [CartanMatrix.A, Matrix.of_apply]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    exact ⟨fun h => absurd h (by norm_num), fun h => by
      rcases h with h | h <;> omega⟩
  · rw [if_neg hij]
    by_cases h : i.val + 1 = j.val ∨ j.val + 1 = i.val
    · rw [if_pos h]
      exact ⟨fun _ => h, fun _ => rfl⟩
    · rw [if_neg h]
      exact ⟨fun hh => absurd hh (by norm_num), fun hh => absurd hh h⟩

private theorem langRatCI_permA_apply0 {n : ℕ} (hn : 2 ≤ n) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ i j, CartanMatrix.A n (σ i) (σ j) = CartanMatrix.A n i j) :
    σ ⟨0, by omega⟩ = ⟨0, by omega⟩ ∨ σ ⟨0, by omega⟩ = ⟨n - 1, by omega⟩ := by
  have hneigh : ∀ k : Fin n,
      (CartanMatrix.A n (σ ⟨0, by omega⟩) k = -1 ↔ k = σ ⟨1, by omega⟩) := by
    intro k
    constructor
    · intro hk
      obtain ⟨j, rfl⟩ := σ.surjective k
      have h0 : CartanMatrix.A n (⟨0, by omega⟩ : Fin n) j = -1 :=
        (hσ ⟨0, by omega⟩ j).symm.trans hk
      have hj : j = ⟨1, by omega⟩ := by
        have h := (langRatCI_cartanA_neg_one_iff (⟨0, by omega⟩ : Fin n) j).1 h0
        rcases h with h | h
        · exact Fin.ext (by simp only [Fin.val_mk] at h ⊢; omega)
        · simp only [Fin.val_mk] at h; omega
      rw [hj]
    · intro hk
      rw [hk]
      exact (hσ ⟨0, by omega⟩ ⟨1, by omega⟩).trans
        ((langRatCI_cartanA_neg_one_iff (⟨0, by omega⟩ : Fin n) (⟨1, by omega⟩ : Fin n)).2
          (Or.inl (by simp)))
  by_cases h0 : σ ⟨0, by omega⟩ = ⟨0, by omega⟩
  · exact Or.inl h0
  · right
    by_contra hlast
    have hval0 : (σ ⟨0, by omega⟩).val ≠ 0 := fun h => h0 (Fin.ext h)
    have hvaln : (σ ⟨0, by omega⟩).val ≠ n - 1 := fun h => hlast (Fin.ext h)
    have hpos : 0 < (σ ⟨0, by omega⟩).val := by
      have := (σ ⟨0, by omega⟩).isLt
      omega
    have hlt : (σ ⟨0, by omega⟩).val < n - 1 := by
      have := (σ ⟨0, by omega⟩).isLt
      omega
    have ha : CartanMatrix.A n (σ ⟨0, by omega⟩)
        (⟨(σ ⟨0, by omega⟩).val - 1, by omega⟩ : Fin n) = -1 :=
      (langRatCI_cartanA_neg_one_iff _ _).2 (Or.inr (by simp only [Fin.val_mk]; omega))
    have hb : CartanMatrix.A n (σ ⟨0, by omega⟩)
        (⟨(σ ⟨0, by omega⟩).val + 1, by omega⟩ : Fin n) = -1 :=
      (langRatCI_cartanA_neg_one_iff _ _).2 (Or.inl (by simp only [Fin.val_mk]))
    have haeq := (hneigh _).1 ha
    have hbeq := (hneigh _).1 hb
    have hfin : (⟨(σ ⟨0, by omega⟩).val - 1, by omega⟩ : Fin n) =
        ⟨(σ ⟨0, by omega⟩).val + 1, by omega⟩ := haeq.trans hbeq.symm
    have := congrArg Fin.val hfin
    simp only [Fin.val_mk] at this
    omega

private theorem langRatCI_permA_eq_one_of_apply0 {n : ℕ} (hn : 2 ≤ n) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ i j, CartanMatrix.A n (σ i) (σ j) = CartanMatrix.A n i j)
    (h0 : σ ⟨0, by omega⟩ = ⟨0, by omega⟩) : σ = 1 := by
  ext i
  have key : ∀ m (hm : m < n), (σ ⟨m, hm⟩).val = m := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro hm
      rcases Nat.eq_zero_or_pos m with rfl | hpos
      · have := congrArg Fin.val h0
        simpa using this
      · have hm1 : m - 1 < n := by omega
        have hprev : (σ ⟨m - 1, hm1⟩).val = m - 1 := ih (m - 1) (by omega) hm1
        have hA : CartanMatrix.A n (σ ⟨m - 1, hm1⟩) (σ ⟨m, hm⟩) = -1 := by
          rw [hσ]
          exact (langRatCI_cartanA_neg_one_iff (⟨m - 1, hm1⟩ : Fin n) (⟨m, hm⟩ : Fin n)).2
            (Or.inl (by simp only [Fin.val_mk]; omega))
        have hdisj := (langRatCI_cartanA_neg_one_iff (σ ⟨m - 1, hm1⟩) (σ ⟨m, hm⟩)).1 hA
        rcases hdisj with h | h
        · omega
        · have hle : 2 ≤ m := by omega
          have hm2 : m - 2 < n := by omega
          have hval : (σ ⟨m, hm⟩).val = (σ ⟨m - 2, hm2⟩).val := by
            have := ih (m - 2) (by omega) hm2
            omega
          have heq : (⟨m, hm⟩ : Fin n) = ⟨m - 2, hm2⟩ := σ.injective (Fin.ext hval)
          have := congrArg Fin.val heq
          simp only [Fin.val_mk] at this
          omega
  simpa using key i.val i.isLt

private theorem langRatCI_permA_eq_rev_of_apply0 {n : ℕ} (hn : 2 ≤ n) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ i j, CartanMatrix.A n (σ i) (σ j) = CartanMatrix.A n i j)
    (h0 : σ ⟨0, by omega⟩ = ⟨n - 1, by omega⟩) : σ * σ = 1 := by
  have key : ∀ m (hm : m < n), (σ ⟨m, hm⟩).val = n - 1 - m := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro hm
      rcases Nat.eq_zero_or_pos m with rfl | hpos
      · have := congrArg Fin.val h0
        simp only [Fin.val_mk] at this
        omega
      · have hm1 : m - 1 < n := by omega
        have hprev : (σ ⟨m - 1, hm1⟩).val = n - 1 - (m - 1) := ih (m - 1) (by omega) hm1
        have hA : CartanMatrix.A n (σ ⟨m - 1, hm1⟩) (σ ⟨m, hm⟩) = -1 := by
          rw [hσ]
          exact (langRatCI_cartanA_neg_one_iff (⟨m - 1, hm1⟩ : Fin n) (⟨m, hm⟩ : Fin n)).2
            (Or.inl (by simp only [Fin.val_mk]; omega))
        have hdisj := (langRatCI_cartanA_neg_one_iff (σ ⟨m - 1, hm1⟩) (σ ⟨m, hm⟩)).1 hA
        rcases hdisj with h | h
        · have hle : 2 ≤ m := by
            have := (σ ⟨m, hm⟩).isLt
            omega
          have hm2 : m - 2 < n := by omega
          have hval : (σ ⟨m, hm⟩).val = (σ ⟨m - 2, hm2⟩).val := by
            have := ih (m - 2) (by omega) hm2
            omega
          have heq : (⟨m, hm⟩ : Fin n) = ⟨m - 2, hm2⟩ := σ.injective (Fin.ext hval)
          have := congrArg Fin.val heq
          simp only [Fin.val_mk] at this
          omega
        · omega
  ext i
  have h1 : (σ (σ i)).val = i.val := by
    have hi : (σ i).val = n - 1 - i.val := key i.val i.isLt
    have h2 : (σ (σ i)).val = n - 1 - (σ i).val := key (σ i).val (σ i).isLt
    omega
  simpa using h1

private theorem langRatCI_permA_mul_self {n : ℕ} (σ : Equiv.Perm (Fin n))
    (hσ : ∀ i j, CartanMatrix.A n (σ i) (σ j) = CartanMatrix.A n i j) : σ * σ = 1 := by
  by_cases hn : n < 2
  · haveI : Subsingleton (Fin n) := ⟨fun a b => Fin.ext (by omega)⟩
    haveI : Subsingleton (Equiv.Perm (Fin n)) :=
      ⟨fun a b => Equiv.ext fun i => Subsingleton.elim _ _⟩
    exact Subsingleton.elim _ _
  · push Not at hn
    rcases langRatCI_permA_apply0 hn σ hσ with h0 | h0
    · rw [langRatCI_permA_eq_one_of_apply0 hn σ hσ h0, mul_one]
    · exact langRatCI_permA_eq_rev_of_apply0 hn σ hσ h0

private theorem langRatCI_det_dvd_of_cartanD {τ : Tag}
    {Ψ : Set (Fin τ.rank → ℤ)} {n : ℕ} (hn : 2 ≤ n) (e : simpleRoots Ψ ≃ Fin n)
    (he : ∀ β γ : simpleRoots Ψ, iform (β : Fin τ.rank → ℤ) γ = CartanMatrix.D n (e β) (e γ)) :
    (Matrix.of fun α β : ↥(simpleRoots Ψ) => iform (α : Fin τ.rank → ℤ) β).det ∣ 4 := by
  have hmat : (Matrix.of fun α β : ↥(simpleRoots Ψ) => iform (α : Fin τ.rank → ℤ) β) =
      (CartanMatrix.D n).submatrix e e := by
    ext α β
    exact he α β
  rw [hmat, Matrix.det_submatrix_equiv_self, CartanMatrix.D_det hn]

theorem langRatCI_twistInner_of_sepB {τ : Tag}
    {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ)
    {σ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ)} (hbij : Set.BijOn σ Ψ Ψ)
    (hform : ∀ γ ∈ Ψ, ∀ δ ∈ Ψ, iform (σ γ) (σ δ) = iform γ δ)
    (hneg : ∀ γ ∈ Ψ, σ (-γ) = -σ γ)
    {t : TauCeti.DynkinType} (e : simpleRoots Ψ ≃ Fin t.rank)
    (he' : ∀ β γ : simpleRoots Ψ, corootPair (β : Fin τ.rank → ℤ) γ =
      t.cartanMatrix (e β) (e γ))
    (hsep : sepB t.cartanMatrix (2 * t.rank) = true) : twistInner Ψ σ := by
  classical
  have hf : IsIsometry Ψ σ := ⟨hbij, hform, hneg⟩
  obtain ⟨w, hw, hpos⟩ := exists_mem_componentWeylGroup_posRoots hΨ hf
  have hf' : IsIsometry Ψ fun γ => σ (w • γ) := hf.comp_smul hΨ hw
  suffices hfix : ∀ β ∈ simpleRoots Ψ, σ (w • β) = β by
    obtain ⟨u, hu, hσu⟩ := exists_smul_eq_of_isIsometry hΨ hf hw hfix
    exact ⟨u, componentWeylGroup_le Ψ hu, hσu⟩
  set π : simpleRoots Ψ → simpleRoots Ψ := fun β =>
    ⟨σ (w • (β : Fin τ.rank → ℤ)), hf'.apply_mem_simpleRoots hΨ hpos β.2⟩ with hπ
  have hπinj : Function.Injective π := by
    intro β γ h
    have h' : σ (w • (β : Fin τ.rank → ℤ)) = σ (w • (γ : Fin τ.rank → ℤ)) :=
      congrArg Subtype.val h
    exact Subtype.ext (hf'.bijOn.injOn (simpleRoots_subset β.2) (simpleRoots_subset γ.2) h')
  set πe : simpleRoots Ψ ≃ simpleRoots Ψ :=
    Equiv.ofBijective π (Finite.injective_iff_bijective.1 hπinj) with hπe
  set σ' : Equiv.Perm (Fin t.rank) := (e.symm.trans πe).trans e with hσ'
  have hσ'M : ∀ i j, t.cartanMatrix (σ' i) (σ' j) = t.cartanMatrix i j := by
    intro i j
    have hi := simpleRoots_subset (e.symm i).2
    have hj := simpleRoots_subset (e.symm j).2
    calc t.cartanMatrix (σ' i) (σ' j)
        = t.cartanMatrix (e (π (e.symm i))) (e (π (e.symm j))) := rfl
      _ = corootPair (π (e.symm i) : Fin τ.rank → ℤ) (π (e.symm j)) := (he' _ _).symm
      _ = corootPair (e.symm i : Fin τ.rank → ℤ) (e.symm j) := corootPair_isometry hf' hi hj
      _ = t.cartanMatrix (e (e.symm i)) (e (e.symm j)) := he' _ _
      _ = t.cartanMatrix i j := by rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have h1 : σ' = 1 := eq_one_of_sepB hsep hσ'M
  intro β hβ
  have h2 := congrArg (fun g : Equiv.Perm (Fin t.rank) => g (e ⟨β, hβ⟩)) h1
  simp only [hσ', Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.Perm.one_apply] at h2
  have h3 := congrArg Subtype.val (e.injective h2)
  simpa [hπe, hπ] using h3

private theorem langRatCI_twistInner_sq_of_diagram_invol {τ : Tag}
    {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ)
    {σ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ)} (hbij : Set.BijOn σ Ψ Ψ)
    (hform : ∀ γ ∈ Ψ, ∀ δ ∈ Ψ, iform (σ γ) (σ δ) = iform γ δ)
    (hneg : ∀ γ ∈ Ψ, σ (-γ) = -σ γ)
    {t : TauCeti.DynkinType} (e : simpleRoots Ψ ≃ Fin t.rank)
    (he' : ∀ β γ : simpleRoots Ψ, corootPair (β : Fin τ.rank → ℤ) γ =
      t.cartanMatrix (e β) (e γ))
    (hinvol : ∀ π : Equiv.Perm (Fin t.rank),
      (∀ i j, t.cartanMatrix (π i) (π j) = t.cartanMatrix i j) → π * π = 1) :
    twistInner Ψ (σ^[2]) := by
  classical
  have hf : IsIsometry Ψ σ := ⟨hbij, hform, hneg⟩
  obtain ⟨w, hw, hpos⟩ := exists_mem_componentWeylGroup_posRoots hΨ hf
  set g : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ := fun γ => σ (w • γ) with hgdef
  have hg : IsIsometry Ψ g := hf.comp_smul hΨ hw
  set π : simpleRoots Ψ → simpleRoots Ψ := fun β =>
    ⟨g (β : Fin τ.rank → ℤ), hg.apply_mem_simpleRoots hΨ hpos β.2⟩ with hπ
  have hπinj : Function.Injective π := by
    intro β γ h
    have h' : g (β : Fin τ.rank → ℤ) = g (γ : Fin τ.rank → ℤ) := congrArg Subtype.val h
    exact Subtype.ext (hg.bijOn.injOn (simpleRoots_subset β.2) (simpleRoots_subset γ.2) h')
  set πe : simpleRoots Ψ ≃ simpleRoots Ψ :=
    Equiv.ofBijective π (Finite.injective_iff_bijective.1 hπinj) with hπe
  set σ' : Equiv.Perm (Fin t.rank) := (e.symm.trans πe).trans e with hσ'
  have hσ'M : ∀ i j, t.cartanMatrix (σ' i) (σ' j) = t.cartanMatrix i j := by
    intro i j
    have hi := simpleRoots_subset (e.symm i).2
    have hj := simpleRoots_subset (e.symm j).2
    calc t.cartanMatrix (σ' i) (σ' j)
        = t.cartanMatrix (e (π (e.symm i))) (e (π (e.symm j))) := rfl
      _ = corootPair (π (e.symm i) : Fin τ.rank → ℤ) (π (e.symm j)) := (he' _ _).symm
      _ = corootPair (e.symm i : Fin τ.rank → ℤ) (e.symm j) := corootPair_isometry hg hi hj
      _ = t.cartanMatrix (e (e.symm i)) (e (e.symm j)) := he' _ _
      _ = t.cartanMatrix i j := by rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have hsq : σ' * σ' = 1 := hinvol σ' hσ'M
  have hπ2 : ∀ β : simpleRoots Ψ, π (π β) = β := by
    intro β
    have h := congrArg (fun q : Equiv.Perm (Fin t.rank) => q (e β)) hsq
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply] at h
    have hgen : ∀ γ : simpleRoots Ψ, σ' (e γ) = e (π γ) := by
      intro γ
      rw [hσ']
      simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
      rw [hπe]
      rfl
    rw [hgen β, hgen (π β)] at h
    exact e.injective h
  have hg2fix : ∀ β ∈ simpleRoots Ψ, g (g β) = β := by
    intro β hβ
    have := hπ2 ⟨β, hβ⟩
    simpa [hπ, hgdef] using congrArg Subtype.val this
  have hg2 : IsIsometry Ψ fun γ => g (g γ) := by
    refine ⟨hg.bijOn.comp hg.bijOn, fun γ hγ δ hδ => ?_, fun γ hγ => ?_⟩
    · rw [hg.iform_eq _ (hg.bijOn.mapsTo hγ) _ (hg.bijOn.mapsTo hδ), hg.iform_eq γ hγ δ hδ]
    · rw [hg.neg γ hγ]
      exact hg.neg (g γ) (hg.bijOn.mapsTo hγ)
  obtain ⟨u, hu, hu'⟩ := exists_smul_eq_of_isIsometry hΨ hg2 (w := 1) (one_mem _)
    (fun β hβ => by simpa using hg2fix β hβ)
  obtain ⟨y, hy, hy'⟩ := langRatCI_exists_conj hΨ hg (inv_mem hw)
  refine ⟨y * u * w⁻¹, ?_, ?_⟩
  · exact mul_mem (mul_mem hy (componentWeylGroup_le Ψ hu))
      (componentWeylGroup_le Ψ (inv_mem hw))
  · intro γ hγ
    have hγ' : w⁻¹ • γ ∈ Ψ := smul_mem_of_mem_componentWeylGroup hΨ (inv_mem hw) γ hγ
    have hgz : g (w⁻¹ • γ) ∈ Ψ := hg.bijOn.mapsTo hγ'
    have hσeq : ∀ δ, σ δ = g (w⁻¹ • δ) := fun δ => by
      rw [hgdef]
      show σ δ = σ (w • (w⁻¹ • δ))
      rw [smul_inv_smul]
    calc σ (σ γ) = g (w⁻¹ • σ γ) := hσeq (σ γ)
      _ = g (w⁻¹ • g (w⁻¹ • γ)) := by rw [hσeq γ]
      _ = y • g (g (w⁻¹ • γ)) := hy' _ hgz
      _ = y • (u • (w⁻¹ • γ)) := by rw [hu' _ hγ']
      _ = (y * u * w⁻¹) • γ := by rw [mul_smul, mul_smul]

theorem langRatSqInnerOrDet_holds :
    LangRatSqInnerOrDet := by
  intro τ hτ Ψ hΨ σ hbij hform hneg
  rcases Ψ.eq_empty_or_nonempty with rfl | hne
  · exact Or.inl ⟨1, one_mem _, fun γ hγ => absurd hγ (Set.notMem_empty γ)⟩
  obtain ⟨t, ⟨ht, e, he⟩, -⟩ :=
    (CFSG.HardMathSupport.Timmesfeld.Proving.isFiniteType_simpleRoots_corootPair
      hΨ).existsUnique_dynkinType
        (CFSG.HardMathSupport.Timmesfeld.Proving.diagramGraph_simpleRoots_connected hΨ hne)
  have he' : ∀ β γ : simpleRoots Ψ, corootPair (β : Fin τ.rank → ℤ) γ =
      t.cartanMatrix (e β) (e γ) := fun β γ => by
    simpa only [Matrix.of_apply] using he β γ
  have hcard : (simpleRoots Ψ).card = t.rank := by
    rw [← Fintype.card_coe, Fintype.card_congr e, Fintype.card_fin]
  have hrank : compRank Ψ = t.rank := by rw [compRank_eq_card hΨ, hcard]
  have hr8 : t.rank ≤ 8 := hrank ▸ (compRank_le Ψ).trans (rank_le_eight τ)
  have hiform_he : ∀ β γ : simpleRoots Ψ, iform (β : Fin τ.rank → ℤ) γ =
      t.cartanMatrix (e β) (e γ) := by
    intro β γ
    rw [← langRatCI_corootPair_eq_iform (simpleRoots_isRoot β.2)
      (langRatCI_iform_self_eq_two hτ (simpleRoots_isRoot β.2))]
    exact he' β γ
  rcases mem_rigidTypes_or_mem_countTypes ht hr8 with hmem | hmem
  · have hok : rigidOK t = true :=
      List.all_eq_true.1 Certificates.certificate13659.1 t hmem
    have hinner := langRatCI_twistInner_of_sepB hΨ hbij hform hneg e he' hok
    exact Or.inl (langRatCI_twistInner_sq hbij hinner)
  · simp only [countTypes, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl (langRatCI_twistInner_sq_of_diagram_invol hΨ hbij hform hneg e he'
        (fun π hπ => langRatCI_permA_mul_self π (by
          intro i j
          have h := hπ i j
          rwa [TauCeti.DynkinType.cartanMatrix_A] at h)))
    · exact Or.inl (langRatCI_twistInner_sq_of_diagram_invol hΨ hbij hform hneg e he'
        (fun π hπ => langRatCI_permA_mul_self π (by
          intro i j
          have h := hπ i j
          rwa [TauCeti.DynkinType.cartanMatrix_A] at h)))
    · exact Or.inl (langRatCI_twistInner_sq_of_diagram_invol hΨ hbij hform hneg e he'
        (fun π hπ => langRatCI_permA_mul_self π (by
          intro i j
          have h := hπ i j
          rwa [TauCeti.DynkinType.cartanMatrix_A] at h)))
    · exact Or.inl (langRatCI_twistInner_sq_of_diagram_invol hΨ hbij hform hneg e he'
        (fun π hπ => langRatCI_permA_mul_self π (by
          intro i j
          have h := hπ i j
          rwa [TauCeti.DynkinType.cartanMatrix_A] at h)))
    · exact Or.inl (langRatCI_twistInner_sq_of_diagram_invol hΨ hbij hform hneg e he'
        (fun π hπ => langRatCI_permA_mul_self π (by
          intro i j
          have h := hπ i j
          rwa [TauCeti.DynkinType.cartanMatrix_A] at h)))
    · exact Or.inl (langRatCI_twistInner_sq_of_diagram_invol hΨ hbij hform hneg e he'
        (fun π hπ => langRatCI_permA_mul_self π (by
          intro i j
          have h := hπ i j
          rwa [TauCeti.DynkinType.cartanMatrix_A] at h)))
    · exact Or.inl (langRatCI_twistInner_sq_of_diagram_invol hΨ hbij hform hneg e he'
        (fun π hπ => langRatCI_permA_mul_self π (by
          intro i j
          have h := hπ i j
          rwa [TauCeti.DynkinType.cartanMatrix_A] at h)))
    · exact Or.inr (langRatCI_det_dvd_of_cartanD (τ := τ) (Ψ := Ψ) (n := 4) (by norm_num) e
        (fun β γ => by
          have h := hiform_he β γ
          rwa [TauCeti.DynkinType.cartanMatrix_D] at h))
    · exact Or.inr (langRatCI_det_dvd_of_cartanD (τ := τ) (Ψ := Ψ) (n := 5) (by norm_num) e
        (fun β γ => by
          have h := hiform_he β γ
          rwa [TauCeti.DynkinType.cartanMatrix_D] at h))
    · exact Or.inr (langRatCI_det_dvd_of_cartanD (τ := τ) (Ψ := Ψ) (n := 6) (by norm_num) e
        (fun β γ => by
          have h := hiform_he β γ
          rwa [TauCeti.DynkinType.cartanMatrix_D] at h))
    · exact Or.inr (langRatCI_det_dvd_of_cartanD (τ := τ) (Ψ := Ψ) (n := 7) (by norm_num) e
        (fun β γ => by
          have h := hiform_he β γ
          rwa [TauCeti.DynkinType.cartanMatrix_D] at h))
    · exact Or.inr (langRatCI_det_dvd_of_cartanD (τ := τ) (Ψ := Ψ) (n := 8) (by norm_num) e
        (fun β γ => by
          have h := hiform_he β γ
          rwa [TauCeti.DynkinType.cartanMatrix_D] at h))
    · exact Or.inl (langRatCI_twistInner_sq_of_diagram_invol hΨ hbij hform hneg e he'
        (fun π hπ => by
          have hπ' : ∀ i j, Tag.E6.cartan (π i) (π j) = Tag.E6.cartan i j := by
            intro i j
            have h := hπ i j
            rw [TauCeti.DynkinType.cartanMatrix_E6, ← cartanE_eq] at h
            exact h
          exact perm_mul_self_eq_one_of_cartan (Or.inr (Or.inl rfl)) π hπ'))

end CFSG.StandardType.LangRat
