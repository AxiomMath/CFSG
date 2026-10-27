module

public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalStd

public section

namespace CFSG.StandardType

namespace GGOppRad

open Matrix CFSG.LieType.BorelTits

section Adapted

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

structure IsAdapted (F : ℕ → Submodule K V) (k : ℕ) (s : Set V) : Prop where
  li : LinearIndepOn K id s
  sub : s ⊆ F k
  span : (F k : Set V) ⊆ Submodule.span K s

theorem IsAdapted.span_eq {F : ℕ → Submodule K V} {k : ℕ} {s : Set V} (hs : IsAdapted F k s) :
    Submodule.span K s = F k :=
  le_antisymm (Submodule.span_le.mpr hs.sub) fun _ hx => hs.span hx

theorem exists_isAdapted_succ {F : ℕ → Submodule K V} (hF : Monotone F) {k : ℕ} {s : Set V}
    (hs : IsAdapted F k s) : ∃ b, s ⊆ b ∧ IsAdapted F (k + 1) b := by
  obtain ⟨b, hbt, hsb, htb, hli⟩ :=
    exists_linearIndepOn_id_extension hs.li (hs.sub.trans (hF (Nat.le_succ k)))
  exact ⟨b, hsb, hli, hbt, htb⟩

theorem isAdapted_zero {F : ℕ → Submodule K V} (h0 : F 0 = ⊥) : IsAdapted F 0 (∅ : Set V) :=
  ⟨linearIndepOn_empty K id, Set.empty_subset _, by rw [h0]; simp⟩

@[expose] noncomputable def adaptedChain {F : ℕ → Submodule K V} (hF : Monotone F)
    (h0 : F 0 = ⊥) : (k : ℕ) → {s : Set V // IsAdapted F k s}
  | 0 => ⟨∅, isAdapted_zero h0⟩
  | k + 1 => ⟨Classical.choose (exists_isAdapted_succ hF (adaptedChain hF h0 k).2),
      (Classical.choose_spec (exists_isAdapted_succ hF (adaptedChain hF h0 k).2)).2⟩

theorem adaptedChain_sub_succ {F : ℕ → Submodule K V} (hF : Monotone F) (h0 : F 0 = ⊥)
    (k : ℕ) : (adaptedChain hF h0 k).1 ⊆ (adaptedChain hF h0 (k + 1)).1 :=
  (Classical.choose_spec (exists_isAdapted_succ hF (adaptedChain hF h0 k).2)).1

theorem adaptedChain_mono {F : ℕ → Submodule K V} (hF : Monotone F) (h0 : F 0 = ⊥) :
    Monotone fun k => (adaptedChain hF h0 k).1 :=
  monotone_nat_of_le_succ (adaptedChain_sub_succ hF h0)

end Adapted

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [Field K]

theorem exists_eq_flagMap_stdFlag {F : ℕ → Submodule K (ι → K)} (hF : Monotone F)
    (h0 : F 0 = ⊥) (htop : ∃ m, F m = ⊤) :
    ∃ (g : Matrix.SpecialLinearGroup ι K) (ℓ : ι → ℕ), F = flagMap slRep g (stdFlag ℓ) := by
  classical
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨a₀⟩⟩
  · exact ⟨1, fun _ => 0, funext fun _ => Subsingleton.elim _ _⟩
  obtain ⟨M, hM⟩ := htop
  set s : ℕ → Set (ι → K) := fun k => (adaptedChain hF h0 k).1 with hs_def
  have hsA : ∀ k, IsAdapted F k (s k) := fun k => (adaptedChain hF h0 k).2
  have hsmono : Monotone s := adaptedChain_mono hF h0
  have hli : LinearIndependent K ((↑) : s M → ι → K) := (hsA M).li
  have hsp : ⊤ ≤ Submodule.span K (Set.range ((↑) : s M → ι → K)) := by
    rw [Subtype.range_coe, (hsA M).span_eq, hM]
  let bas : Module.Basis (s M) K (ι → K) := Module.Basis.mk hli hsp
  let e : ι ≃ s M := (Pi.basisFun K ι).indexEquiv bas
  let w : ι → ι → K := fun a => (e a : ι → K)
  have hex : ∀ a, ∃ k, w a ∈ s (k + 1) := fun a => ⟨M, hsmono (Nat.le_succ M) (e a).2⟩
  let ℓ : ι → ℕ := fun a => Nat.find (hex a)
  have hℓ : ∀ a k, w a ∈ s k ↔ ℓ a < k := by
    intro a k
    constructor
    · intro h
      cases k with
      | zero =>
        change w a ∈ (∅ : Set (ι → K)) at h
        exact absurd h (Set.notMem_empty _)
      | succ k => exact Nat.lt_succ_of_le (Nat.find_min' (hex a) h)
    · intro h
      exact hsmono (Nat.succ_le_of_lt h) (Nat.find_spec (hex a))
  have hFk : ∀ k, F k = Submodule.span K (Set.range fun a : {a // ℓ a < k} => w a) := by
    intro k
    apply le_antisymm
    · rcases le_total k M with hkM | hMk
      · rw [← (hsA k).span_eq]
        refine Submodule.span_mono fun x hx => ?_
        have hxB : x ∈ s M := hsmono hkM hx
        refine ⟨⟨e.symm ⟨x, hxB⟩, (hℓ _ k).mp ?_⟩, ?_⟩
        · simpa [w] using hx
        · simp [w]
      · calc F k ≤ F M := by rw [hM]; exact le_top
          _ = Submodule.span K (s M) := (hsA M).span_eq.symm
          _ ≤ _ := by
            refine Submodule.span_mono fun x hx => ?_
            refine ⟨⟨e.symm ⟨x, hx⟩, ?_⟩, by simp [w]⟩
            have : ℓ (e.symm ⟨x, hx⟩) < M := (hℓ _ M).mp (by simpa [w] using hx)
            omega
    · rw [Submodule.span_le]
      rintro _ ⟨a, rfl⟩
      exact (hsA k).sub ((hℓ a k).mpr a.2)
  let Mw : Matrix ι ι K := Matrix.of fun c a => w a c
  have hunit : IsUnit Mw := by
    rw [← Matrix.linearIndependent_cols_iff_isUnit]
    have hc : Mw.col = fun a => (bas (e a) : ι → K) := by
      funext a
      ext c
      simp [Mw, w, bas, Module.Basis.mk_apply]
    rw [hc]
    exact bas.linearIndependent.comp e e.injective
  have hdet : Mw.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det Mw).mp hunit).ne_zero
  let d : ι → K := fun a => if a = a₀ then Mw.det⁻¹ else 1
  have hd : ∀ a, d a ≠ 0 := fun a => by
    by_cases h : a = a₀ <;> simp [d, h, hdet]
  let M' : Matrix ι ι K := Mw * Matrix.diagonal d
  have hdet' : M'.det = 1 := by
    simp [M', Matrix.det_mul, Matrix.det_diagonal, d, Finset.prod_ite_eq', hdet]
  let g : Matrix.SpecialLinearGroup ι K := ⟨M', hdet'⟩
  have hg : ∀ a, slRep g (Pi.single a 1) = d a • w a := by
    intro a
    rw [slRep_apply]
    ext c
    change (M' *ᵥ Pi.single a 1) c = _
    rw [mulVec_single_one, col_apply]
    simp [M', Matrix.mul_diagonal, Mw, mul_comm]
  refine ⟨g, ℓ, funext fun k => ?_⟩
  rw [hFk k]
  change _ = (stdFlag ℓ k).map (slRep g)
  rw [stdFlag_eq_span, Submodule.map_span, ← Set.range_comp]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    have hwa : w a = (d a)⁻¹ • slRep g (Pi.single a 1) := by
      rw [hg, smul_smul, inv_mul_cancel₀ (hd a), one_smul]
    change w a ∈ _
    rw [hwa]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    rw [Function.comp_apply, hg]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

end GGOppRad

end CFSG.StandardType
