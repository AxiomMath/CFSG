module

public import CFSG.Sporadic.HN.Local.ClassCount

public section

namespace CFSG.Sporadic.Ly.Omega

open MulAction

section Tree

variable {G X : Type*} [Group G] [MulAction G X]

theorem tree_mem_orbit (H : Subgroup G) (p : X) (key : ℕ → X) (par : ℕ → ℕ) (n : ℕ)
    (h0 : key 0 = p) (hs : ∀ i, 0 < i → i < n → par i < i ∧ ∃ s ∈ H, key i = s • key (par i)) :
    ∀ i < n, key i ∈ orbit H p := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · rw [h0]
      exact mem_orbit_self p
    · obtain ⟨hp, s, hsH, hk⟩ := hs i hpos hi
      obtain ⟨g, hg⟩ := ih (par i) hp (lt_trans hp hi)
      refine ⟨⟨s, hsH⟩ * g, ?_⟩
      change (⟨s, hsH⟩ * g : H) • p = key i
      rw [hk, mul_smul]
      change (⟨s, hsH⟩ : H) • (g • p) = s • key (par i)
      rw [show g • p = key (par i) from hg]
      rfl

theorem tree_card_le [Finite X] (H : Subgroup G) (p : X) (key : ℕ → X) (par : ℕ → ℕ) (n : ℕ)
    (h0 : key 0 = p) (hs : ∀ i, 0 < i → i < n → par i < i ∧ ∃ s ∈ H, key i = s • key (par i))
    (hinj : ∀ i < n, ∀ j < n, key i = key j → i = j) :
    n ≤ Nat.card (orbit H p) := by
  classical
  have hsub : (((Finset.range n).image key : Finset X) : Set X) ⊆ orbit H p := by
    intro x hx
    simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact tree_mem_orbit H p key par n h0 hs i hi
  have hcard : ((Finset.range n).image key).card = n := by
    rw [Finset.card_image_of_injOn (fun i hi j hj e => hinj i (Finset.mem_range.1 hi) j
      (Finset.mem_range.1 hj) e), Finset.card_range]
  rw [Nat.card_coe_set_eq]
  calc n = ((Finset.range n).image key).card := hcard.symm
    _ = (((Finset.range n).image key : Finset X) : Set X).ncard := (Set.ncard_coe_finset _).symm
    _ ≤ (orbit H p).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)

end Tree

section Fiber

variable {H X Z : Type*} [Group H] [MulAction H X] [MulAction H Z]

theorem mul_card_le_card_orbit [Finite X] (Y : X → Z) (hY : ∀ (h : H) (x : X), Y (h • x) = h • Y x)
    (p : X) (A : Set Z) (hA : A ⊆ orbit H (Y p)) (B : Set X)
    (hB : B ⊆ orbit (stabilizer H (Y p)) p) :
    A.ncard * B.ncard ≤ Nat.card (orbit H p) := by
  classical
  have hz : ∀ z : A, ∃ h : H, h • Y p = z.1 := fun z => (hA z.2)
  choose hh hhz using hz
  have hYB : ∀ b : B, Y b.1 = Y p := by
    intro b
    obtain ⟨k, hk⟩ := hB b.2
    rw [← hk]
    change Y ((k : H) • p) = Y p
    rw [hY]
    exact k.2
  let f : A × B → orbit H p := fun q => ⟨hh q.1 • q.2.1, by
    obtain ⟨k, hk⟩ := hB q.2.2
    refine ⟨hh q.1 * (k : H), ?_⟩
    change (hh q.1 * (k : H)) • p = hh q.1 • q.2.1
    rw [mul_smul]
    congr 1⟩
  have hf : Function.Injective f := by
    rintro ⟨z, b⟩ ⟨z', b'⟩ e
    have e1 : hh z • b.1 = hh z' • b'.1 := congrArg Subtype.val e
    have e2 : hh z • Y b.1 = hh z' • Y b'.1 := by rw [← hY, ← hY, e1]
    rw [hYB, hYB, hhz, hhz] at e2
    have hzz : z = z' := Subtype.ext e2
    subst hzz
    have hbb : b = b' := Subtype.ext (smul_left_cancel _ e1)
    rw [hbb]
  have := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_prod, Nat.card_coe_set_eq, Nat.card_coe_set_eq] at this

end Fiber

section Squeeze

variable {J X : Type*} [Group J] [Finite J] [MulAction J X]

theorem squeeze (E : X) (H : Subgroup J) (hH : H ≤ stabilizer J E) {N h₀ : ℕ}
    (hJ : Nat.card J = N * h₀) (hh : h₀ ≤ Nat.card H) (h0 : 0 < h₀) {ι : Type*} [Fintype ι]
    [DecidableEq X] (O : ι → Finset X) (hO : ∀ i, (O i : Set X) ⊆ orbit J E)
    (hd : Pairwise fun i j => Disjoint (O i) (O j)) (hsum : N ≤ ∑ i, (O i).card) :
    stabilizer J E = H ∧ Nat.card H = h₀ ∧ Nat.card (orbit J E) = N ∧ ∑ i, (O i).card = N ∧
      ((Finset.univ.biUnion O : Finset X) : Set X) = orbit J E := by
  have hos : Nat.card (orbit J E) * Nat.card (stabilizer J E) = Nat.card J := by
    rw [Nat.card_coe_set_eq, ← MulAction.index_stabilizer, mul_comm, Subgroup.card_mul_index]
  have hHS : Nat.card H ≤ Nat.card (stabilizer J E) := Subgroup.card_le_of_le hH
  have hU : (Finset.univ.biUnion O).card = ∑ i, (O i).card :=
    Finset.card_biUnion fun i _ j _ hij => hd hij
  have hUsub : ((Finset.univ.biUnion O : Finset X) : Set X) ⊆ orbit J E := by
    intro x hx
    simp only [Finset.coe_biUnion, Finset.coe_univ, Set.mem_univ, Set.iUnion_true,
      Set.mem_iUnion, Finset.mem_coe] at hx
    obtain ⟨i, hi⟩ := hx
    exact hO i hi
  have hfin : (orbit J E).Finite := Set.finite_range _
  have hle : (Finset.univ.biUnion O).card ≤ Nat.card (orbit J E) := by
    rw [← Set.ncard_coe_finset, ← Nat.card_coe_set_eq]
    exact Set.ncard_le_ncard hUsub hfin
  have horb : Nat.card (orbit J E) ≤ N := by
    by_contra hc
    push Not at hc
    have : N * h₀ < Nat.card (orbit J E) * Nat.card (stabilizer J E) :=
      Nat.mul_lt_mul_of_lt_of_le hc (hh.trans hHS) Nat.card_pos
    omega
  have hN : Nat.card (orbit J E) = N := le_antisymm horb (hsum.trans (hU ▸ hle))
  have hNpos : 0 < N := by
    rcases Nat.eq_zero_or_pos N with e | e
    · rw [e, zero_mul] at hJ
      exact absurd hJ Nat.card_pos.ne'
    · exact e
  have hS : Nat.card (stabilizer J E) = h₀ := by
    rw [hN, hJ] at hos
    exact Nat.eq_of_mul_eq_mul_left hNpos hos
  have hHc : Nat.card H = h₀ := le_antisymm (hS ▸ hHS) hh
  refine ⟨(Subgroup.eq_of_le_of_card_ge hH (by rw [hS, hHc])).symm, hHc, hN, ?_, ?_⟩
  · exact le_antisymm (hU ▸ hle.trans hN.le) hsum
  · apply Set.eq_of_subset_of_ncard_le hUsub _ hfin
    rw [Set.ncard_coe_finset, ← Nat.card_coe_set_eq, hN, hU]
    exact hsum

end Squeeze

section Fix

variable {H X : Type*} [Group H] [Finite H] [MulAction H X]

theorem card_fix_orbit (p : X) (t : H) :
    Nat.card {y : orbit H p // t • y = y} * Nat.card (stabilizer H p) =
      Nat.card (Subgroup.centralizer {t}) *
        Nat.card {h : H // h ∈ stabilizer H p ∧ IsConj t h} := by
  have : Finite (orbit H p) := Set.finite_coe_iff.2 (Set.finite_range _)
  have hst : stabilizer H (⟨p, mem_orbit_self p⟩ : orbit H p) = stabilizer H p := by
    ext h
    simp only [mem_stabilizer_iff]
    constructor
    · intro e
      exact congrArg Subtype.val e
    · intro e
      exact Subtype.ext e
  have := CFSG.Sporadic.HN.Local.card_centralizer_mul_card_inter
    (X := orbit H p) (⟨p, mem_orbit_self p⟩ : orbit H p) t
  rw [hst] at this
  exact this.symm

end Fix

section Beta

open Matrix

variable {n k : ℕ} {K : Type*} [Field K]

theorem beta_conj (F h E' : Matrix (Fin n) (Fin n) K) (U : Matrix (Fin n) (Fin k) K)
    (r : Matrix (Fin k) (Fin k) K) (hF : hᵀ * F * h = F) (hU : h * U = U * r)
    (hh : IsUnit h.det) (hr : IsUnit r.det) :
    Uᵀ * (h * E' * h⁻¹)ᵀ * F * U = (r⁻¹)ᵀ * (Uᵀ * E'ᵀ * F * U) * r⁻¹ := by
  have e1 : h⁻¹ * (h * U) = U := by
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul h hh, Matrix.one_mul]
  have e2 : U * r * r⁻¹ = U := by
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv r hr, Matrix.mul_one]
  have hU' : h⁻¹ * U = U * r⁻¹ := by
    calc h⁻¹ * U = h⁻¹ * (U * r * r⁻¹) := by rw [e2]
      _ = h⁻¹ * (U * r) * r⁻¹ := by rw [Matrix.mul_assoc h⁻¹ (U * r) r⁻¹]
      _ = h⁻¹ * (h * U) * r⁻¹ := by rw [hU]
      _ = U * r⁻¹ := by rw [e1]
  have e3 : hᵀ * F * h * h⁻¹ = hᵀ * F := by
    rw [Matrix.mul_assoc (hᵀ * F) h h⁻¹, Matrix.mul_nonsing_inv h hh, Matrix.mul_one]
  have hF' : hᵀ * F = F * h⁻¹ := by
    rw [← e3, hF]
  have hUT : Uᵀ * (h⁻¹)ᵀ = (r⁻¹)ᵀ * Uᵀ := by
    rw [← Matrix.transpose_mul, hU', Matrix.transpose_mul]
  calc Uᵀ * (h * E' * h⁻¹)ᵀ * F * U
      = Uᵀ * (h⁻¹)ᵀ * E'ᵀ * (hᵀ * F) * U := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = (r⁻¹)ᵀ * Uᵀ * E'ᵀ * (F * h⁻¹) * U := by rw [hUT, hF']
    _ = (r⁻¹)ᵀ * Uᵀ * E'ᵀ * F * (h⁻¹ * U) := by simp only [Matrix.mul_assoc]
    _ = (r⁻¹)ᵀ * (Uᵀ * E'ᵀ * F * U) * r⁻¹ := by
        rw [hU']
        simp only [Matrix.mul_assoc]

end Beta

end CFSG.Sporadic.Ly.Omega

end
