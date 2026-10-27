module

public import CFSG.RankThree.PartOne.KFCL.SpPerm

public section

namespace CFSG.RankThree.PartOne.KFCL.Sp

open Matrix CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.LieType.Universal.Symplectic.SpExtras
  CFSG.Assembly.LowTwoRank CFSG.LieType.Steinberg.Sp
open CFSG.LieType.Steinberg (sl2Upper sl2Lower)
open scoped MatrixGroups

variable {K : Type} [Field K] {n : ℕ}

theorem commute_iff_entries {t g : StatedSp n K} (ht : ∀ a b, a ≠ b → mat n K t a b = 0) :
    Commute t g ↔ ∀ a b, mat n K t a a * mat n K g a b = mat n K g a b * mat n K t b b := by
  have key1 : ∀ a b, mat n K (t * g) a b = mat n K t a a * mat n K g a b := by
    intro a b
    rw [map_mul, Matrix.mul_apply, Finset.sum_eq_single a]
    · intro c _ hc
      rw [ht a c (Ne.symm hc), zero_mul]
    · simp
  have key2 : ∀ a b, mat n K (g * t) a b = mat n K g a b * mat n K t b b := by
    intro a b
    rw [map_mul, Matrix.mul_apply, Finset.sum_eq_single b]
    · intro c _ hc
      rw [ht c b hc, mul_zero]
    · simp
  constructor
  · intro h a b
    have := congrFun (congrFun (congrArg (mat n K) h.eq) a) b
    rwa [key1, key2] at this
  · intro h
    show t * g = g * t
    apply mat_injective
    ext a b
    rw [key1, key2]
    exact h a b

theorem eq_one_of_sq_eq_one {x : K} {p : ℕ} (hp : Odd p) (hx : x ^ p = 1) (hx2 : x ^ 2 = 1) : x = 1 := by
  have h := pow_gcd_eq_one.2 ⟨hx, hx2⟩
  have : Nat.gcd p 2 = 1 := Nat.coprime_two_right.2 hp
  rwa [this, pow_one] at h

theorem h01 : (0 : Fin 3) ≠ 1 := by decide

variable (K) in
@[expose] noncomputable def Sl : Subgroup (StatedSp 3 K) := (longBlock K 3 0).range

variable (K) in
@[expose] noncomputable def Ss : Subgroup (StatedSp 3 K) := (shortBlock K (n := 3) h01).range

theorem mat_elt_positiveLong_apply : mat 3 K (elt (.positiveLong 0) 1) (Sum.inl 0) (Sum.inr 0) = 1 := by
  rw [mat_elt]
  simp [E]

theorem mat_elt_difference_apply :
    mat 3 K (elt (.difference 0 1 h01) 1) (Sum.inl 0) (Sum.inl 1) = 1 := by
  rw [mat_elt]
  simp [E]

theorem elt_positiveLong_mem_Sl : elt (.positiveLong 0) (1 : K) ∈ Sl K :=
  ⟨sl2Upper 1, longBlock_sl2Upper 0 1⟩

theorem elt_difference_mem_Ss : elt (.difference 0 1 h01) (1 : K) ∈ Ss K :=
  ⟨sl2Upper 1, shortBlock_sl2Upper h01 1⟩

theorem Sl_entries {g : StatedSp 3 K} (hg : g ∈ Sl K) {a b : Fin 3 ⊕ Fin 3} (h : mat 3 K g a b ≠ 0) :
    a = b ∨ (a ∈ coords 0 ∧ b ∈ coords 0) := by
  rw [Sl, range_longBlock] at hg
  by_contra hcon
  push Not at hcon
  have := hg a b (fun hh => hcon.2 hh.1 hh.2)
  rw [this] at h
  exact h (Matrix.one_apply_ne hcon.1)

theorem Ss_entries {g : StatedSp 3 K} (hg : g ∈ Ss K) {a b : Fin 3 ⊕ Fin 3} (h : mat 3 K g a b ≠ 0) :
    a = b ∨ ((a = Sum.inl 0 ∨ a = Sum.inl 1) ∧ (b = Sum.inl 0 ∨ b = Sum.inl 1)) ∨
      ((a = Sum.inr 0 ∨ a = Sum.inr 1) ∧ (b = Sum.inr 0 ∨ b = Sum.inr 1)) := by
  obtain ⟨A, rfl⟩ := hg
  rw [mat_shortBlock] at h
  rcases a with x | x <;> rcases b with y | y
  · simp only [Matrix.fromBlocks_apply₁₁] at h
    by_cases hxy : (x = 0 ∨ x = 1) ∧ (y = 0 ∨ y = 1)
    · right; left
      simpa using hxy
    · rw [blockMat_apply_of_not h01 _ (by simpa using hxy)] at h
      left
      by_contra hne
      exact h (Matrix.one_apply_ne (fun hxy => hne (by rw [hxy])))
  · simp [Matrix.fromBlocks_apply₁₂] at h
  · simp [Matrix.fromBlocks_apply₂₁] at h
  · simp only [Matrix.fromBlocks_apply₂₂, Matrix.transpose_apply] at h
    by_cases hxy : (y = 0 ∨ y = 1) ∧ (x = 0 ∨ x = 1)
    · right; right
      simpa [and_comm] using hxy
    · rw [blockMat_apply_of_not h01 _ (by simpa using hxy)] at h
      left
      by_contra hne
      have : y ≠ x := fun hyx => hne (by rw [hyx])
      exact h (Matrix.one_apply_ne (fun hh => this hh))

variable {p : ℕ}

theorem mem_centralizer_Sl_iff (hp : Odd p) {t : StatedSp 3 K} (ht : t ∈ spTorus p 3 K) :
    t ∈ Subgroup.centralizer (Sl K : Set (StatedSp 3 K)) ↔ mat 3 K t (Sum.inl 0) (Sum.inl 0) = 1 := by
  have hdiag : ∀ a b, a ≠ b → mat 3 K t a b = 0 := fun a b hab => spTorus_apply_ne ht hab
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro h
    have hc := h _ elt_positiveLong_mem_Sl
    have h2 := (commute_iff_entries hdiag).1 (show Commute t (elt (.positiveLong 0) (1 : K)) from hc.symm)
      (Sum.inl 0) (Sum.inr 0)
    rw [mat_elt_positiveLong_apply, mul_one, one_mul] at h2
    have h3 : mat 3 K t (Sum.inl 0) (Sum.inl 0) ^ 2 = 1 := by
      have := spTorus_par ht (Sum.inl 0)
      rw [par_inl] at this
      rw [← h2] at this
      have h0 : mat 3 K t (Sum.inl 0) (Sum.inl 0) ≠ 0 := by
        intro h0
        have := spTorus_pow ht (Sum.inl 0)
        rw [h0, zero_pow (by intro hp0; simp [hp0] at hp)] at this
        exact zero_ne_one this
      field_simp at this
      linear_combination this
    exact eq_one_of_sq_eq_one hp (spTorus_pow ht _) h3
  · intro h1 g hg
    have hc : Commute t g := (commute_iff_entries hdiag).2 (fun a b => by
      by_cases hab : mat 3 K g a b = 0
      · rw [hab, mul_zero, zero_mul]
      · rcases Sl_entries hg hab with rfl | ⟨ha, hb⟩
        · exact mul_comm _ _
        · have hinr : mat 3 K t (Sum.inr 0) (Sum.inr 0) = 1 := by
            rw [show (Sum.inr 0 : Fin 3 ⊕ Fin 3) = par (Sum.inl 0) from rfl, spTorus_par ht, h1, inv_one]
          have e : ∀ c ∈ coords (0 : Fin 3), mat 3 K t c c = 1 := by
            intro c hc
            rcases mem_coords.1 hc with rfl | rfl
            · exact h1
            · exact hinr
          rw [e a ha, e b hb]
          exact mul_comm _ _)
    exact hc.symm.eq

theorem mem_centralizer_Ss_iff {t : StatedSp 3 K} (ht : t ∈ spTorus p 3 K) :
    t ∈ Subgroup.centralizer (Ss K : Set (StatedSp 3 K)) ↔
      mat 3 K t (Sum.inl 0) (Sum.inl 0) = mat 3 K t (Sum.inl 1) (Sum.inl 1) := by
  have hdiag : ∀ a b, a ≠ b → mat 3 K t a b = 0 := fun a b hab => spTorus_apply_ne ht hab
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro h
    have hc := h _ elt_difference_mem_Ss
    have h2 := (commute_iff_entries hdiag).1 (show Commute t (elt (.difference 0 1 h01) (1 : K)) from hc.symm)
      (Sum.inl 0) (Sum.inl 1)
    rw [mat_elt_difference_apply, mul_one, one_mul] at h2
    exact h2
  · intro h1 g hg
    have hc : Commute t g := (commute_iff_entries hdiag).2 (fun a b => by
      by_cases hab : mat 3 K g a b = 0
      · rw [hab, mul_zero, zero_mul]
      · have hinr : mat 3 K t (Sum.inr 0) (Sum.inr 0) = mat 3 K t (Sum.inr 1) (Sum.inr 1) := by
          rw [show (Sum.inr 0 : Fin 3 ⊕ Fin 3) = par (Sum.inl 0) from rfl,
            show (Sum.inr 1 : Fin 3 ⊕ Fin 3) = par (Sum.inl 1) from rfl, spTorus_par ht, spTorus_par ht, h1]
        rcases Ss_entries hg hab with rfl | ⟨ha, hb⟩ | ⟨ha, hb⟩
        · exact mul_comm _ _
        · have e : ∀ c : Fin 3 ⊕ Fin 3, (c = Sum.inl 0 ∨ c = Sum.inl 1) →
              mat 3 K t c c = mat 3 K t (Sum.inl 0) (Sum.inl 0) := by
            rintro c (rfl | rfl)
            · rfl
            · exact h1.symm
          rw [e a ha, e b hb]
          exact mul_comm _ _
        · have e : ∀ c : Fin 3 ⊕ Fin 3, (c = Sum.inr 0 ∨ c = Sum.inr 1) →
              mat 3 K t c c = mat 3 K t (Sum.inr 0) (Sum.inr 0) := by
            rintro c (rfl | rfl)
            · rfl
            · exact hinr.symm
          rw [e a ha, e b hb]
          exact mul_comm _ _)
    exact hc.symm.eq

end CFSG.RankThree.PartOne.KFCL.Sp
