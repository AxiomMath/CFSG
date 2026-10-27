module

public import CFSG.RankThree.GF2n.Stroth80.Sp6NoEmb.Cube
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bRepInd

public section

namespace CFSG.RankThree.GF2n.Stroth80.Sp6NoEmb

open Module
open scoped MatrixGroups TensorProduct
open CFSG.Semidihedral.Principal CFSG.QuasithinUnique.Setup.X7b Representation
open CFSG.QuasithinUnique.Setup.SL2Modules (frobTensor frobTensor_isIrreducible
  frobTensor_classification frobTensor_nonisomorphic finrank_frobTensor)

variable {K : Type} [Field K] [Fintype K] [CharP K 2] {n : ℕ}

@[expose] def labels (n : ℕ) : Finset (Fin 3 → Finset ℕ) :=
  Fintype.piFinset fun _ => (Finset.range n).powerset

theorem mem_labels {J : Fin 3 → Finset ℕ} : J ∈ labels n ↔ IsLabel n J := by
  simp only [labels, Fintype.mem_piFinset, Finset.mem_powerset, Finset.subset_iff,
    Finset.mem_range, IsLabel]

@[expose] def slLabels (n : ℕ) : Finset (Finset ℕ) :=
  (Finset.range n).powerset

theorem mem_slLabels {J : Finset ℕ} : J ∈ slLabels n ↔ ∀ i ∈ J, i < n := by
  simp only [slLabels, Finset.mem_powerset, Finset.subset_iff, Finset.mem_range]

variable {V W : Type} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

@[expose] noncomputable def pat (ρ : Representation K (Cube K) V) (J : Fin 3 → Finset ℕ) : ℕ :=
  repMultiplicity ρ (cubeRep K J)

@[expose] noncomputable def slPat (σ : Representation K SL(2, K) V) (J : Finset ℕ) : ℕ :=
  repMultiplicity σ (frobTensor K K J)

theorem pat_congr {ρ : Representation K (Cube K) V} {ρ' : Representation K (Cube K) W}
    (e : ρ.Equiv ρ') (J : Fin 3 → Finset ℕ) : pat ρ J = pat ρ' J :=
  repMultiplicity_congr_left e _

theorem slPat_congr {σ : Representation K SL(2, K) V} {σ' : Representation K SL(2, K) W}
    (e : σ.Equiv σ') (J : Finset ℕ) : slPat σ J = slPat σ' J :=
  repMultiplicity_congr_left e _

theorem pat_of_subsingleton [Subsingleton V] (ρ : Representation K (Cube K) V)
    (J : Fin 3 → Finset ℕ) : pat ρ J = 0 := by
  have : Subsingleton ρ.asModule := inferInstanceAs (Subsingleton V)
  rw [pat, repMultiplicity, compositionMultiplicity_of_subsingleton]

theorem slPat_of_subsingleton [Subsingleton V] (σ : Representation K SL(2, K) V) (J : Finset ℕ) :
    slPat σ J = 0 := by
  have : Subsingleton σ.asModule := inferInstanceAs (Subsingleton V)
  rw [slPat, repMultiplicity, compositionMultiplicity_of_subsingleton]

theorem pat_of_equiv (hK : Fintype.card K = 2 ^ n) {ρ : Representation K (Cube K) V}
    (hρ : ρ.IsIrreducible) {J₀ : Fin 3 → Finset ℕ} (hJ₀ : IsLabel n J₀) (e : ρ.Equiv (cubeRep K J₀))
    {J : Fin 3 → Finset ℕ} (hJ : IsLabel n J) : pat ρ J = if J = J₀ then 1 else 0 := by
  rw [pat, repMultiplicity_of_isIrreducible hρ]
  by_cases h : J = J₀
  · subst h
    rw [if_pos ⟨e⟩, if_pos rfl]
  · rw [if_neg h, if_neg]
    rintro ⟨e'⟩
    exact h (cubeRep_injective hK hJ₀ hJ (e.symm.trans e')).symm

theorem slPat_of_equiv (hK : Fintype.card K = 2 ^ n) {σ : Representation K SL(2, K) V}
    (hσ : σ.IsIrreducible) {J₀ : Finset ℕ} (hJ₀ : ∀ i ∈ J₀, i < n)
    (e : σ.Equiv (frobTensor K K J₀)) {J : Finset ℕ} (hJ : ∀ i ∈ J, i < n) :
    slPat σ J = if J = J₀ then 1 else 0 := by
  rw [slPat, repMultiplicity_of_isIrreducible hσ]
  by_cases h : J = J₀
  · subst h
    rw [if_pos ⟨e⟩, if_pos rfl]
  · rw [if_neg h, if_neg]
    rintro ⟨e'⟩
    exact h (frobTensor_nonisomorphic hK hJ₀ hJ (e.symm.trans e')).symm

theorem slPat_frobTensor (hK : Fintype.card K = 2 ^ n) {J₀ J : Finset ℕ} (hJ₀ : ∀ i ∈ J₀, i < n)
    (hJ : ∀ i ∈ J, i < n) : slPat (frobTensor K K J₀) J = if J = J₀ then 1 else 0 :=
  slPat_of_equiv hK (frobTensor_isIrreducible hK hJ₀) hJ₀ (Representation.Equiv.refl _) hJ

theorem sum_pat (hK : Fintype.card K = 2 ^ n)
    (φ : ∀ {V : Type} [AddCommGroup V] [Module K V] [Module.Finite K V],
      Representation K (Cube K) V → ℕ)
    (h0 : ∀ {V : Type} [AddCommGroup V] [Module K V] [Module.Finite K V]
      (ρ : Representation K (Cube K) V), Subsingleton V → φ ρ = 0)
    (hiso : ∀ {V W : Type} [AddCommGroup V] [Module K V] [Module.Finite K V] [AddCommGroup W]
      [Module K W] [Module.Finite K W] (ρ : Representation K (Cube K) V)
      (σ : Representation K (Cube K) W), ρ.Equiv σ → φ ρ = φ σ)
    (hadd : ∀ {V : Type} [AddCommGroup V] [Module K V] [Module.Finite K V]
      (ρ : Representation K (Cube K) V) (W : Subrepresentation ρ),
      φ ρ = φ W.toRepresentation + φ W.quotient)
    [Module.Finite K V] (ρ : Representation K (Cube K) V) :
    φ ρ = ∑ J ∈ labels n, pat ρ J * φ (cubeRep K J) := by
  have key := rep_induction (k := K) (G := Cube K)
    (fun {V} _ _ _ ρ => φ ρ = ∑ J ∈ labels n, pat ρ J * φ (cubeRep K J))
    (fun {V} _ _ _ ρ hsub => by
      haveI := hsub
      rw [h0 ρ hsub]
      symm
      exact Finset.sum_eq_zero fun J _ => by rw [pat_of_subsingleton, zero_mul])
    (fun {V} _ _ _ ρ hρ => by
      obtain ⟨J₀, hJ₀, ⟨e⟩⟩ := cube_classification hK ρ hρ
      rw [Finset.sum_eq_single_of_mem J₀ (mem_labels.mpr hJ₀)]
      · rw [pat_of_equiv hK hρ hJ₀ e hJ₀, if_pos rfl, one_mul]
        exact hiso ρ _ e
      · intro J hJ hne
        rw [pat_of_equiv hK hρ hJ₀ e (mem_labels.mp hJ), if_neg hne, zero_mul])
    (fun {V} _ _ _ ρ W hW1 hW2 => by
      rw [hadd ρ W, hW1, hW2, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun J _ => ?_
      rw [pat, pat, pat, repMultiplicity_sub_quot ρ W, add_mul])
  exact key _ ρ rfl

theorem finrank_eq_sum_pat (hK : Fintype.card K = 2 ^ n) [Module.Finite K V]
    (ρ : Representation K (Cube K) V) :
    finrank K V = ∑ J ∈ labels n, pat ρ J * 2 ^ ((J 0).card + (J 1).card + (J 2).card) := by
  have h := sum_pat hK (fun {V} _ _ _ _ => finrank K V)
    (fun {V} _ _ _ _ hsub => by haveI := hsub; exact finrank_zero_of_subsingleton)
    (fun {V W} _ _ _ _ _ _ _ _ e => e.toLinearEquiv.finrank_eq)
    (fun {V} _ _ _ _ W => by rw [add_comm]; exact (Submodule.finrank_quotient_add_finrank _).symm)
    ρ
  rw [h]
  exact Finset.sum_congr rfl fun J _ => by rw [finrank_cubeRep]

theorem subsingleton_of_pat_eq_zero (hK : Fintype.card K = 2 ^ n) [Module.Finite K V]
    (ρ : Representation K (Cube K) V) (h : ∀ J, IsLabel n J → pat ρ J = 0) : Subsingleton V := by
  have h1 := finrank_eq_sum_pat hK ρ
  rw [Finset.sum_eq_zero fun J hJ => by rw [h J (mem_labels.mp hJ), zero_mul]] at h1
  exact Module.finrank_zero_iff.mp h1

theorem pat_sub_le [Module.Finite K V] (ρ : Representation K (Cube K) V) (W : Subrepresentation ρ)
    (J : Fin 3 → Finset ℕ) : pat W.toRepresentation J ≤ pat ρ J := by
  rw [pat, pat, repMultiplicity_sub_quot ρ W]
  exact Nat.le_add_right _ _

theorem pat_quot_le [Module.Finite K V] (ρ : Representation K (Cube K) V) (W : Subrepresentation ρ)
    (J : Fin 3 → Finset ℕ) : pat W.quotient J ≤ pat ρ J := by
  rw [pat, pat, repMultiplicity_sub_quot ρ W]
  exact Nat.le_add_left _ _

@[expose] def imageSub {ρ : Representation K (Cube K) V} {ρ' : Representation K (Cube K) W}
    (f : ρ.IntertwiningMap ρ') : Subrepresentation ρ' where
  toSubmodule := LinearMap.range f.toLinearMap
  apply_mem_toSubmodule g := by
    rintro _ ⟨v, rfl⟩
    exact ⟨ρ g v, LinearMap.congr_fun (f.isIntertwining' g) v⟩

@[expose] noncomputable def equivImageSub {ρ : Representation K (Cube K) V}
    {ρ' : Representation K (Cube K) W} (f : ρ.IntertwiningMap ρ') (hf : Function.Injective f) :
    ρ.Equiv (imageSub f).toRepresentation :=
  Representation.Equiv.mk (LinearEquiv.ofInjective f.toLinearMap hf) fun g => by
    ext v
    exact LinearMap.congr_fun (f.isIntertwining' g) v

theorem pat_le_of_injective [Module.Finite K W] {ρ : Representation K (Cube K) V}
    {ρ' : Representation K (Cube K) W} (f : ρ.IntertwiningMap ρ') (hf : Function.Injective f)
    (J : Fin 3 → Finset ℕ) : pat ρ J ≤ pat ρ' J := by
  rw [pat_congr (equivImageSub f hf) J]
  exact pat_sub_le ρ' (imageSub f) J

@[expose] def kerSub {ρ : Representation K (Cube K) V} {ρ' : Representation K (Cube K) W}
    (f : ρ.IntertwiningMap ρ') : Subrepresentation ρ where
  toSubmodule := LinearMap.ker f.toLinearMap
  apply_mem_toSubmodule g v hv := by
    rw [LinearMap.mem_ker] at hv ⊢
    rw [show f.toLinearMap (ρ g v) = ρ' g (f.toLinearMap v) from
      LinearMap.congr_fun (f.isIntertwining' g) v, hv, map_zero]

@[expose] noncomputable def equivQuotKer {ρ : Representation K (Cube K) V}
    {ρ' : Representation K (Cube K) W} (f : ρ.IntertwiningMap ρ') (hf : Function.Surjective f) :
    (kerSub f).quotient.Equiv ρ' :=
  Representation.Equiv.mk (f.toLinearMap.quotKerEquivOfSurjective hf) fun g => by
    ext v
    exact LinearMap.congr_fun (f.isIntertwining' g) v

theorem pat_le_of_surjective [Module.Finite K V] {ρ : Representation K (Cube K) V}
    {ρ' : Representation K (Cube K) W} (f : ρ.IntertwiningMap ρ') (hf : Function.Surjective f)
    (J : Fin 3 → Finset ℕ) : pat ρ' J ≤ pat ρ J := by
  rw [← pat_congr (equivQuotKer f hf) J]
  exact pat_quot_le ρ (kerSub f) J

end CFSG.RankThree.GF2n.Stroth80.Sp6NoEmb
