module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCAPairConj
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.SpModel
public import CFSG.Open.StatedAPI
public import CFSG.Open.StatedDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open Matrix

variable {K : Type*} [Field K] {n : ℕ}

private def s16c13bcA_rot (p : Fin n) : (Fin n ⊕ Fin n → K) →ₗ[K] (Fin n ⊕ Fin n → K) where
  toFun x := fun i => if i = Sum.inl p then -x (Sum.inr p)
    else if i = Sum.inr p then x (Sum.inl p) - x (Sum.inr p) else x i
  map_add' x y := by
    funext i
    simp only [Pi.add_apply]
    split_ifs <;> ring
  map_smul' c x := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

private theorem s16c13bcA_rot_form (p : Fin n) (x y : Fin n ⊕ Fin n → K) :
    symB (s16c13bcA_rot p x) (s16c13bcA_rot p y) = symB x y := by
  rw [symB_eq, symB_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : i = p
  · subst hi
    simp [s16c13bcA_rot]
    ring
  · simp [s16c13bcA_rot, hi]

private theorem s16c13bcA_rot_cube (p : Fin n) (x : Fin n ⊕ Fin n → K) :
    s16c13bcA_rot p (s16c13bcA_rot p (s16c13bcA_rot p x)) = x := by
  funext i
  by_cases h1 : i = Sum.inl p
  · subst h1; simp [s16c13bcA_rot]
  · by_cases h2 : i = Sum.inr p
    · subst h2; simp [s16c13bcA_rot]; ring
    · simp [s16c13bcA_rot, h1, h2]

private theorem s16c13bcA_symB_eq_dot (u v : Fin n ⊕ Fin n → K) :
    symB u v = u ⬝ᵥ ((Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ v) := by
  rw [symB_eq]
  simp [dotProduct, Fintype.sum_sum_type, Matrix.mulVec, Matrix.fromBlocks, Matrix.one_apply,
    sub_eq_add_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib]

private theorem s16c13bcA_form_to_matrix (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)
    (h : ∀ x y, symB (M *ᵥ x) (M *ᵥ y) = symB x y) :
    Mᵀ * (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * M =
      Matrix.fromBlocks 0 1 (-1) 0 := by
  rw [Matrix.ext_iff_mulVec]
  intro v
  funext i
  have key : ∀ x : Fin n ⊕ Fin n → K,
      x ⬝ᵥ ((Mᵀ * (Matrix.fromBlocks 0 1 (-1) 0 : Matrix _ _ K) * M) *ᵥ v) =
      x ⬝ᵥ ((Matrix.fromBlocks 0 1 (-1) 0 : Matrix _ _ K) *ᵥ v) := by
    intro x
    have hx := h x v
    rw [s16c13bcA_symB_eq_dot, s16c13bcA_symB_eq_dot] at hx
    rw [← hx]
    simp only [← Matrix.mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
  simpa using key (Pi.single i 1)

private theorem s16c13bcA_exists_rot (p : Fin n) :
    ∃ g ∈ spGroup n K, (∀ x, (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ x =
      s16c13bcA_rot p x) := by
  obtain ⟨g, hg, hgM⟩ := exists_spGroup_of_form
    (LinearMap.toMatrix' (s16c13bcA_rot p : _ →ₗ[K] _)) (by
      intro x y
      rw [LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec, s16c13bcA_rot_form])
  exact ⟨g, hg, fun x => by rw [hgM, LinearMap.toMatrix'_mulVec]⟩

private theorem s16c13bcA_rot_eq_self {p : Fin n} {x : Fin n ⊕ Fin n → K}
    (h1 : x (Sum.inl p) = 0) (h2 : x (Sum.inr p) = 0) : s16c13bcA_rot p x = x := by
  funext i
  by_cases hi1 : i = Sum.inl p
  · subst hi1; simp [s16c13bcA_rot, h1, h2]
  · by_cases hi2 : i = Sum.inr p
    · subst hi2; simp [s16c13bcA_rot, h1, h2]
    · simp [s16c13bcA_rot, hi1, hi2]

private theorem s16c13bcA_rot_inl (p : Fin n) (x : Fin n ⊕ Fin n → K) :
    s16c13bcA_rot p x (Sum.inl p) = -x (Sum.inr p) := by
  simp [s16c13bcA_rot]

private theorem s16c13bcA_rot_inr (p : Fin n) (x : Fin n ⊕ Fin n → K) :
    s16c13bcA_rot p x (Sum.inr p) = x (Sum.inl p) - x (Sum.inr p) := by
  simp [s16c13bcA_rot]

private theorem s16c13bcA_rot_apply_of_ne (p : Fin n) (x : Fin n ⊕ Fin n → K)
    {i : Fin n ⊕ Fin n} (h1 : i ≠ Sum.inl p) (h2 : i ≠ Sum.inr p) :
    s16c13bcA_rot p x i = x i := by
  simp [s16c13bcA_rot, h1, h2]

private theorem s16c13bcA_single_eq_zero {a b : Fin n ⊕ Fin n} (h : a ≠ b) :
    (Pi.single a (1 : K) : Fin n ⊕ Fin n → K) b = 0 :=
  Pi.single_eq_of_ne' h 1

private theorem s16c13bcA_rot_comm {p q : Fin n} (hpq : p ≠ q) (x : Fin n ⊕ Fin n → K) :
    s16c13bcA_rot p (s16c13bcA_rot q x) = s16c13bcA_rot q (s16c13bcA_rot p x) := by
  have hp1 : (Sum.inl p : Fin n ⊕ Fin n) ≠ Sum.inl q := fun h => hpq (Sum.inl.inj h)
  have hp2 : (Sum.inl p : Fin n ⊕ Fin n) ≠ Sum.inr q := by simp
  have hp3 : (Sum.inr p : Fin n ⊕ Fin n) ≠ Sum.inl q := by simp
  have hp4 : (Sum.inr p : Fin n ⊕ Fin n) ≠ Sum.inr q := fun h => hpq (Sum.inr.inj h)
  have hq1 : (Sum.inl q : Fin n ⊕ Fin n) ≠ Sum.inl p := fun h => hpq (Sum.inl.inj h).symm
  have hq2 : (Sum.inl q : Fin n ⊕ Fin n) ≠ Sum.inr p := by simp
  have hq3 : (Sum.inr q : Fin n ⊕ Fin n) ≠ Sum.inl p := by simp
  have hq4 : (Sum.inr q : Fin n ⊕ Fin n) ≠ Sum.inr p := fun h => hpq (Sum.inr.inj h).symm
  funext i
  by_cases hip1 : i = Sum.inl p
  · subst hip1
    rw [s16c13bcA_rot_inl, s16c13bcA_rot_apply_of_ne q x hp3 hp4,
      s16c13bcA_rot_apply_of_ne q (s16c13bcA_rot p x) hp1 hp2, s16c13bcA_rot_inl]
  · by_cases hip2 : i = Sum.inr p
    · subst hip2
      rw [s16c13bcA_rot_inr, s16c13bcA_rot_apply_of_ne q x hp1 hp2,
        s16c13bcA_rot_apply_of_ne q x hp3 hp4,
        s16c13bcA_rot_apply_of_ne q (s16c13bcA_rot p x) hp3 hp4, s16c13bcA_rot_inr]
    · by_cases hiq1 : i = Sum.inl q
      · subst hiq1
        rw [s16c13bcA_rot_apply_of_ne p (s16c13bcA_rot q x) hq1 hq2,
          s16c13bcA_rot_inl, s16c13bcA_rot_inl, s16c13bcA_rot_apply_of_ne p x hq3 hq4]
      · by_cases hiq2 : i = Sum.inr q
        · subst hiq2
          rw [s16c13bcA_rot_apply_of_ne p (s16c13bcA_rot q x) hq3 hq4,
            s16c13bcA_rot_inr, s16c13bcA_rot_inr, s16c13bcA_rot_apply_of_ne p x hq1 hq2,
            s16c13bcA_rot_apply_of_ne p x hq3 hq4]
        · rw [s16c13bcA_rot_apply_of_ne p (s16c13bcA_rot q x) hip1 hip2,
            s16c13bcA_rot_apply_of_ne q x hiq1 hiq2,
            s16c13bcA_rot_apply_of_ne q (s16c13bcA_rot p x) hiq1 hiq2,
            s16c13bcA_rot_apply_of_ne p x hip1 hip2]

theorem s16c13bcA_pairFixed_statedSp {K : Type} [Field K] {n : ℕ} (hn : 3 ≤ n) :
    s16c13bcA_PairFixed (CFSG.Open.StatedSp n K) (Fin n ⊕ Fin n → K) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let r : Fin n := ⟨0, by omega⟩
  let p : Fin n := ⟨1, by omega⟩
  let q : Fin n := ⟨2, by omega⟩
  have hrp : r ≠ p := by simp [r, p, Fin.ext_iff]
  have hrq : r ≠ q := by simp [r, q, Fin.ext_iff]
  have hpq : p ≠ q := by simp [p, q, Fin.ext_iff]
  have hsp : spGroup n K ≤ CFSG.Open.StatedSp n K := by
    intro A hA
    rw [CFSG.Open.StatedAPI.mem_statedSp_iff]
    exact s16c13bcA_form_to_matrix (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)
      (mem_spGroup.mp hA)
  set e : Fin n ⊕ Fin n → K := Pi.single (Sum.inl r) 1 with he
  set e' : Fin n ⊕ Fin n → K := Pi.single (Sum.inl q) 1 with he'
  obtain ⟨g₁, hg₁, hg₁x⟩ := s16c13bcA_exists_rot (K := K) p
  obtain ⟨g₂, hg₂, hg₂x⟩ := s16c13bcA_exists_rot (K := K) q
  have hg₁3 : g₁ ^ 3 = 1 := by
    apply Units.ext
    simp only [pow_succ, pow_zero, one_mul, Units.val_mul, Units.val_one]
    rw [Matrix.ext_iff_mulVec]
    intro x
    simp [← Matrix.mulVec_mulVec, hg₁x, s16c13bcA_rot_cube]
  have hg₂3 : g₂ ^ 3 = 1 := by
    apply Units.ext
    simp only [pow_succ, pow_zero, one_mul, Units.val_mul, Units.val_one]
    rw [Matrix.ext_iff_mulVec]
    intro x
    simp [← Matrix.mulVec_mulVec, hg₂x, s16c13bcA_rot_cube]
  have hg₁1 : g₁ ≠ 1 := by
    intro h
    have hc := congrFun (hg₁x (Pi.single (Sum.inr p) 1)) (Sum.inl p)
    rw [h] at hc
    simp [s16c13bcA_rot] at hc
  have hg₂1 : g₂ ≠ 1 := by
    intro h
    have hc := congrFun (hg₂x (Pi.single (Sum.inr q) 1)) (Sum.inl q)
    rw [h] at hc
    simp [s16c13bcA_rot] at hc
  have hg₁ord : orderOf g₁ = 3 := orderOf_eq_prime hg₁3 hg₁1
  have hg₂ord : orderOf g₂ = 3 := orderOf_eq_prime hg₂3 hg₂1
  have hcomm_mat : (g₁ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *
      (g₂ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
      (g₂ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *
      (g₁ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) := by
    rw [Matrix.ext_iff_mulVec]
    intro x
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hg₁x, hg₂x, hg₂x, hg₁x]
    exact s16c13bcA_rot_comm hpq x
  have hcomm : g₁ * g₂ = g₂ * g₁ := by
    apply Units.ext
    simpa only [Units.val_mul] using hcomm_mat
  have he_inl : e (Sum.inl p) = 0 := by
    rw [he]; exact s16c13bcA_single_eq_zero (fun h => hrp (Sum.inl.inj h))
  have he_inr : e (Sum.inr p) = 0 := by
    rw [he]; exact s16c13bcA_single_eq_zero (by simp)
  have he_qinl : e (Sum.inl q) = 0 := by
    rw [he]; exact s16c13bcA_single_eq_zero (fun h => hrq (Sum.inl.inj h))
  have he_qinr : e (Sum.inr q) = 0 := by
    rw [he]; exact s16c13bcA_single_eq_zero (by simp)
  have he'_inl : e' (Sum.inl p) = 0 := by
    rw [he']; exact s16c13bcA_single_eq_zero (fun h => hpq (Sum.inl.inj h).symm)
  have he'_inr : e' (Sum.inr p) = 0 := by
    rw [he']; exact s16c13bcA_single_eq_zero (by simp)
  have hg₁e : (g₁ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ e = e := by
    rw [hg₁x]; exact s16c13bcA_rot_eq_self he_inl he_inr
  have hg₁e' : (g₁ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ e' = e' := by
    rw [hg₁x]; exact s16c13bcA_rot_eq_self he'_inl he'_inr
  have hg₂e : (g₂ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ e = e := by
    rw [hg₂x]; exact s16c13bcA_rot_eq_self he_qinl he_qinr
  have hrot_e'q : s16c13bcA_rot q e' = Pi.single (Sum.inr q) 1 := by
    funext i
    by_cases hi1 : i = Sum.inl q
    · subst hi1; simp [s16c13bcA_rot, he']
    · by_cases hi2 : i = Sum.inr q
      · subst hi2; simp [s16c13bcA_rot, he']
      · simp [s16c13bcA_rot, he', hi1, hi2]
  have hg₂e' : (g₂ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ e' =
      Pi.single (Sum.inr q) 1 := by
    rw [hg₂x]; exact hrot_e'q
  have hne : (g₂ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ e' ≠ e' := by
    rw [hg₂e']
    intro h
    have hc := congrFun h (Sum.inl q)
    simp [he'] at hc
  have hnot : (⟨g₂, hsp hg₂⟩ : ↥(CFSG.Open.StatedSp n K)) ∉
      Subgroup.zpowers (⟨g₁, hsp hg₁⟩ : ↥(CFSG.Open.StatedSp n K)) := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    have hk' : g₁ ^ k = g₂ := by
      have := congrArg (Subtype.val) hk
      simpa using this
    have hmem2 : g₂ ∈ Subgroup.zpowers g₁ := Subgroup.mem_zpowers_iff.2 ⟨k, hk'⟩
    exact hne (smul_eq_self_of_mem_zpowers hmem2 hg₁e')
  have he_pair : ∃ G₁ G₂ : ↥(CFSG.Open.StatedSp n K),
      orderOf G₁ = 3 ∧ orderOf G₂ = 3 ∧ G₁ * G₂ = G₂ * G₁ ∧
      G₂ ∉ Subgroup.zpowers G₁ ∧ G₁ • e = e ∧ G₂ • e = e :=
    ⟨⟨g₁, hsp hg₁⟩, ⟨g₂, hsp hg₂⟩,
      by rw [Subgroup.orderOf_mk]; exact hg₁ord,
      by rw [Subgroup.orderOf_mk]; exact hg₂ord,
      Subtype.ext hcomm,
      hnot,
      hg₁e,
      hg₂e⟩
  intro w
  by_cases hw : w = 0
  · subst hw
    obtain ⟨G₁, G₂, h1, h2, hc, hn, -, -⟩ := he_pair
    exact ⟨G₁, G₂, h1, h2, hc, hn, smul_zero G₁, smul_zero G₂⟩
  · have he0 : e ≠ 0 := by
      intro h
      have hc := congrFun h (Sum.inl r)
      simp [he] at hc
    obtain ⟨C, hC, hCe⟩ := exists_spGroup_mulVec_eq he0 hw
    exact s16c13bcA_pairFixed_of_orbit (Γ := ↥(CFSG.Open.StatedSp n K))
      (e := e) (v := w) (c := ⟨C, hsp hC⟩) hCe he_pair

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
