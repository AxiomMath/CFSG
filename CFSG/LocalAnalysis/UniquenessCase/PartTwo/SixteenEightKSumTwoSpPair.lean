module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCAAux
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCAPairConj
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.SpModel
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open Matrix

variable {K : Type} [Field K] {m : ℕ}

private def s16k_e (i : Fin m) : Fin m ⊕ Fin m → K := Pi.single (Sum.inl i) 1

private def s16k_f (i : Fin m) : Fin m ⊕ Fin m → K := Pi.single (Sum.inr i) 1

private theorem s16k_symB_eq_dot (u v : Fin m ⊕ Fin m → K) :
    symB u v = u ⬝ᵥ ((Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ v) := by
  rw [symB_eq]
  simp [dotProduct, Fintype.sum_sum_type, Matrix.mulVec, Matrix.fromBlocks, Matrix.one_apply,
    sub_eq_add_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib]

private theorem s16k_form_to_matrix (M : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)
    (h : ∀ x y, symB (M *ᵥ x) (M *ᵥ y) = symB x y) :
    Mᵀ * (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) * M =
      Matrix.fromBlocks 0 1 (-1) 0 := by
  rw [Matrix.ext_iff_mulVec]
  intro v
  funext i
  have key : ∀ x : Fin m ⊕ Fin m → K,
      x ⬝ᵥ ((Mᵀ * (Matrix.fromBlocks 0 1 (-1) 0 : Matrix _ _ K) * M) *ᵥ v) =
      x ⬝ᵥ ((Matrix.fromBlocks 0 1 (-1) 0 : Matrix _ _ K) *ᵥ v) := by
    intro x
    have hx := h x v
    rw [s16k_symB_eq_dot, s16k_symB_eq_dot] at hx
    rw [← hx]
    simp only [← Matrix.mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
  simpa using key (Pi.single i 1)

private theorem s16k_spGroup_le_statedSp (m : ℕ) (K : Type) [Field K] :
    spGroup m K ≤ StatedSp m K := by
  intro A hA
  rw [CFSG.Open.StatedAPI.mem_statedSp_iff]
  exact s16k_form_to_matrix (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) (mem_spGroup.mp hA)

private theorem s16k_e_ne_zero (i : Fin m) : s16k_e (K := K) i ≠ 0 := by
  intro h
  have hc := congrFun h (Sum.inl i)
  simp [s16k_e] at hc

private theorem s16k_e_ne_f (i : Fin m) : s16k_e (K := K) i ≠ s16k_f (K := K) i := by
  intro h
  have hc := congrFun h (Sum.inl i)
  simp [s16k_e, s16k_f] at hc

private theorem s16k_symB_e (i : Fin m) (u : Fin m ⊕ Fin m → K) :
    symB u (s16k_e (K := K) i) = -u (Sum.inr i) := by
  rw [symB_eq]
  refine (Finset.sum_eq_single i ?_ ?_).trans ?_
  · intro j _ hj
    rw [s16k_e, Pi.single_eq_of_ne' (by simp : (Sum.inl i : Fin m ⊕ Fin m) ≠ Sum.inr j) 1,
      Pi.single_eq_of_ne' (fun h => hj (Sum.inl.inj h).symm) 1]
    ring
  · intro h; exact absurd (Finset.mem_univ i) h
  · simp [s16k_e]

private theorem s16k_symB_f (i : Fin m) (u : Fin m ⊕ Fin m → K) :
    symB u (s16k_f (K := K) i) = u (Sum.inl i) := by
  rw [symB_eq]
  refine (Finset.sum_eq_single i ?_ ?_).trans ?_
  · intro j _ hj
    rw [s16k_f, Pi.single_eq_of_ne' (by simp : (Sum.inr i : Fin m ⊕ Fin m) ≠ Sum.inl j) 1,
      Pi.single_eq_of_ne' (fun h => hj (Sum.inr.inj h).symm) 1]
    ring
  · intro h; exact absurd (Finset.mem_univ i) h
  · simp [s16k_f]

private theorem s16k_symB_e_left (i : Fin m) (w : Fin m ⊕ Fin m → K) :
    symB (s16k_e (K := K) i) w = w (Sum.inr i) := by
  rw [symB_comm, s16k_symB_e, neg_neg]

private theorem s16k_symB_f_left (i : Fin m) (w : Fin m ⊕ Fin m → K) :
    symB (s16k_f (K := K) i) w = -w (Sum.inl i) := by
  rw [symB_comm, s16k_symB_f]

private def s16k_rot (p : Fin m) : (Fin m ⊕ Fin m → K) →ₗ[K] (Fin m ⊕ Fin m → K) where
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

private theorem s16k_rot_form (p : Fin m) (x y : Fin m ⊕ Fin m → K) :
    symB (s16k_rot p x) (s16k_rot p y) = symB x y := by
  rw [symB_eq, symB_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : i = p
  · subst hi
    simp [s16k_rot]
    ring
  · simp [s16k_rot, hi]

private theorem s16k_rot_cube (p : Fin m) (x : Fin m ⊕ Fin m → K) :
    s16k_rot p (s16k_rot p (s16k_rot p x)) = x := by
  funext i
  by_cases h1 : i = Sum.inl p
  · subst h1; simp [s16k_rot]
  · by_cases h2 : i = Sum.inr p
    · subst h2; simp [s16k_rot]; ring
    · simp [s16k_rot, h1, h2]

private theorem s16k_exists_rot (p : Fin m) :
    ∃ g ∈ spGroup m K,
      ∀ x, (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x = s16k_rot p x := by
  obtain ⟨g, hg, hgM⟩ := exists_spGroup_of_form
    (LinearMap.toMatrix' (s16k_rot p : _ →ₗ[K] _)) (by
      intro x y
      rw [LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec, s16k_rot_form])
  exact ⟨g, hg, fun x => by rw [hgM, LinearMap.toMatrix'_mulVec]⟩

private theorem s16k_rot_inl (p : Fin m) (x : Fin m ⊕ Fin m → K) :
    s16k_rot p x (Sum.inl p) = -x (Sum.inr p) := by simp [s16k_rot]

private theorem s16k_rot_inr (p : Fin m) (x : Fin m ⊕ Fin m → K) :
    s16k_rot p x (Sum.inr p) = x (Sum.inl p) - x (Sum.inr p) := by simp [s16k_rot]

private theorem s16k_rot_apply_of_ne (p : Fin m) (x : Fin m ⊕ Fin m → K)
    {i : Fin m ⊕ Fin m} (h1 : i ≠ Sum.inl p) (h2 : i ≠ Sum.inr p) :
    s16k_rot p x i = x i := by simp [s16k_rot, h1, h2]

private theorem s16k_rot_eq_self {p : Fin m} {x : Fin m ⊕ Fin m → K}
    (h1 : x (Sum.inl p) = 0) (h2 : x (Sum.inr p) = 0) : s16k_rot p x = x := by
  funext i
  by_cases hi1 : i = Sum.inl p
  · subst hi1; simp [s16k_rot, h1, h2]
  · by_cases hi2 : i = Sum.inr p
    · subst hi2; simp [s16k_rot, h1, h2]
    · simp [s16k_rot, hi1, hi2]

private theorem s16k_rot_e (p : Fin m) : s16k_rot p (s16k_e (K := K) p) = s16k_f (K := K) p := by
  funext j
  by_cases h1 : j = Sum.inl p
  · subst h1; simp [s16k_rot, s16k_e, s16k_f]
  · by_cases h2 : j = Sum.inr p
    · subst h2; simp [s16k_rot, s16k_e, s16k_f]
    · simp [s16k_rot, s16k_e, s16k_f, h1, h2]

private theorem s16k_rot_comm {p q : Fin m} (hpq : p ≠ q) (x : Fin m ⊕ Fin m → K) :
    s16k_rot p (s16k_rot q x) = s16k_rot q (s16k_rot p x) := by
  have hp1 : (Sum.inl p : Fin m ⊕ Fin m) ≠ Sum.inl q := fun h => hpq (Sum.inl.inj h)
  have hp2 : (Sum.inl p : Fin m ⊕ Fin m) ≠ Sum.inr q := by simp
  have hp3 : (Sum.inr p : Fin m ⊕ Fin m) ≠ Sum.inl q := by simp
  have hp4 : (Sum.inr p : Fin m ⊕ Fin m) ≠ Sum.inr q := fun h => hpq (Sum.inr.inj h)
  have hq1 : (Sum.inl q : Fin m ⊕ Fin m) ≠ Sum.inl p := fun h => hpq (Sum.inl.inj h).symm
  have hq2 : (Sum.inl q : Fin m ⊕ Fin m) ≠ Sum.inr p := by simp
  have hq3 : (Sum.inr q : Fin m ⊕ Fin m) ≠ Sum.inl p := by simp
  have hq4 : (Sum.inr q : Fin m ⊕ Fin m) ≠ Sum.inr p := fun h => hpq (Sum.inr.inj h).symm
  funext i
  by_cases hip1 : i = Sum.inl p
  · subst hip1
    rw [s16k_rot_inl, s16k_rot_apply_of_ne q x hp3 hp4,
      s16k_rot_apply_of_ne q (s16k_rot p x) hp1 hp2, s16k_rot_inl]
  · by_cases hip2 : i = Sum.inr p
    · subst hip2
      rw [s16k_rot_inr, s16k_rot_apply_of_ne q x hp1 hp2,
        s16k_rot_apply_of_ne q x hp3 hp4,
        s16k_rot_apply_of_ne q (s16k_rot p x) hp3 hp4, s16k_rot_inr]
    · by_cases hiq1 : i = Sum.inl q
      · subst hiq1
        rw [s16k_rot_apply_of_ne p (s16k_rot q x) hq1 hq2,
          s16k_rot_inl, s16k_rot_inl, s16k_rot_apply_of_ne p x hq3 hq4]
      · by_cases hiq2 : i = Sum.inr q
        · subst hiq2
          rw [s16k_rot_apply_of_ne p (s16k_rot q x) hq3 hq4,
            s16k_rot_inr, s16k_rot_inr, s16k_rot_apply_of_ne p x hq1 hq2,
            s16k_rot_apply_of_ne p x hq3 hq4]
        · rw [s16k_rot_apply_of_ne p (s16k_rot q x) hip1 hip2,
            s16k_rot_apply_of_ne q x hiq1 hiq2,
            s16k_rot_apply_of_ne q (s16k_rot p x) hiq1 hiq2,
            s16k_rot_apply_of_ne p x hip1 hip2]

private theorem s16k_rot_orderOf {p : Fin m} {g : GL (Fin m ⊕ Fin m) K}
    (hgx : ∀ x, (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x = s16k_rot p x) :
    orderOf g = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hg3 : g ^ 3 = 1 := by
    apply Units.ext
    simp only [pow_succ, pow_zero, one_mul, Units.val_mul, Units.val_one]
    rw [Matrix.ext_iff_mulVec]
    intro x
    simp [← Matrix.mulVec_mulVec, hgx, s16k_rot_cube]
  have hg1 : g ≠ 1 := by
    intro h
    have hc := congrFun (hgx (Pi.single (Sum.inr p) 1)) (Sum.inl p)
    rw [h] at hc
    simp [s16k_rot] at hc
  exact orderOf_eq_prime hg3 hg1

private theorem s16k_natAct_one {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (Γ : Subgroup (GL ι K)) (a : Multiplicative (ι → K)) : natAct Γ 1 a = a := by
  simp [natAct]

private theorem s16k_natAct_mul {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (Γ : Subgroup (GL ι K)) (x y : ↥Γ) (a : Multiplicative (ι → K)) :
    natAct Γ (x * y) a = natAct Γ x (natAct Γ y a) := by
  simp [natAct, Units.val_mul, Matrix.mulVec_mulVec]

private theorem s16k_natAct_inv {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (Γ : Subgroup (GL ι K)) (x : ↥Γ) (a : Multiplicative (ι → K))
    (h : natAct Γ x a = a) : natAct Γ x⁻¹ a = a := by
  rw [← h, ← s16k_natAct_mul, inv_mul_cancel, s16k_natAct_one]
  exact h.symm

private theorem s16k_natAct_eq_ofAdd_smul {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] (Γ : Subgroup (GL ι K)) (x : ↥Γ) (a : Multiplicative (ι → K)) :
    natAct Γ x a = Multiplicative.ofAdd (x • Multiplicative.toAdd a) := rfl

private theorem s16k_exists_symB_ne_zero_of_W {i₀ : Fin m} {u : Fin m ⊕ Fin m → K}
    (hu₀ : u (Sum.inl i₀) = 0) (hu₁ : u (Sum.inr i₀) = 0) (hu : u ≠ 0) :
    ∃ p : Fin m ⊕ Fin m → K,
      p (Sum.inl i₀) = 0 ∧ p (Sum.inr i₀) = 0 ∧ symB u p ≠ 0 := by
  obtain ⟨p, hp⟩ := exists_symB_ne_zero hu
  refine ⟨p - p (Sum.inl i₀) • s16k_e (K := K) i₀ - p (Sum.inr i₀) • s16k_f (K := K) i₀,
    ?_, ?_, ?_⟩
  · simp [s16k_e, s16k_f, Pi.single_apply, Pi.sub_apply, Pi.smul_apply]
  · simp [s16k_e, s16k_f, Pi.single_apply, Pi.sub_apply, Pi.smul_apply]
  · rw [symB_sub_right, symB_sub_right, symB_smul_right, symB_smul_right,
      s16k_symB_e, s16k_symB_f, hu₁, hu₀]
    simpa using hp

private theorem s16k_transvection_of_W {i₀ : Fin m} {w : Fin m ⊕ Fin m → K}
    (hw₀ : w (Sum.inl i₀) = 0) (hw₁ : w (Sum.inr i₀) = 0) (c : K) :
    ∃ g ∈ spGroup m K,
      (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ s16k_e (K := K) i₀ =
        s16k_e (K := K) i₀ ∧
      (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ s16k_f (K := K) i₀ =
        s16k_f (K := K) i₀ ∧
      ∀ x, (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x = x + (c * symB x w) • w := by
  obtain ⟨g, hg, hgx⟩ := exists_transvection (K := K) (n := m) w c
  refine ⟨g, hg, ?_, ?_, hgx⟩
  · rw [hgx, s16k_symB_e_left, hw₁, mul_zero, zero_smul, add_zero]
  · rw [hgx, s16k_symB_f_left, hw₀, neg_zero, mul_zero, zero_smul, add_zero]

private theorem s16k_exists_move_of_symB_ne {i₀ : Fin m} {u v : Fin m ⊕ Fin m → K}
    (hu₀ : u (Sum.inl i₀) = 0) (hu₁ : u (Sum.inr i₀) = 0)
    (hv₀ : v (Sum.inl i₀) = 0) (hv₁ : v (Sum.inr i₀) = 0) (huv : symB u v ≠ 0) :
    ∃ g ∈ spGroup m K,
      (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u = v ∧
      (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ s16k_e (K := K) i₀ =
        s16k_e (K := K) i₀ ∧
      (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ s16k_f (K := K) i₀ =
        s16k_f (K := K) i₀ := by
  have hw₀ : (u - v) (Sum.inl i₀) = 0 := by simp [Pi.sub_apply, hu₀, hv₀]
  have hw₁ : (u - v) (Sum.inr i₀) = 0 := by simp [Pi.sub_apply, hu₁, hv₁]
  obtain ⟨g, hg, hge, hgf, hgx⟩ := s16k_transvection_of_W (i₀ := i₀) hw₀ hw₁ (symB u v)⁻¹
  refine ⟨g, hg, ?_, hge, hgf⟩
  rw [hgx, symB_sub_right, symB_self, zero_sub, mul_neg, inv_mul_cancel₀ huv]
  simp

private theorem s16k_exists_spGroup_mulVec_eq_of_W {i₀ : Fin m} {u v : Fin m ⊕ Fin m → K}
    (hu₀ : u (Sum.inl i₀) = 0) (hu₁ : u (Sum.inr i₀) = 0) (hu : u ≠ 0)
    (hv₀ : v (Sum.inl i₀) = 0) (hv₁ : v (Sum.inr i₀) = 0) (hv : v ≠ 0) :
    ∃ g ∈ spGroup m K,
      (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u = v ∧
      (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ s16k_e (K := K) i₀ =
        s16k_e (K := K) i₀ ∧
      (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ s16k_f (K := K) i₀ =
        s16k_f (K := K) i₀ := by
  by_cases huv : symB u v = 0
  · obtain ⟨p, hp₀, hp₁, hpu⟩ := s16k_exists_symB_ne_zero_of_W hu₀ hu₁ hu
    obtain ⟨q, hq₀, hq₁, hqv⟩ := s16k_exists_symB_ne_zero_of_W hv₀ hv₁ hv
    have hqv' : symB q v ≠ 0 := by rw [symB_comm]; exact neg_ne_zero.mpr hqv
    have key : ∃ z : Fin m ⊕ Fin m → K, z (Sum.inl i₀) = 0 ∧ z (Sum.inr i₀) = 0 ∧
        symB u z ≠ 0 ∧ symB z v ≠ 0 := by
      by_cases h1 : symB u q = 0
      · by_cases h2 : symB p v = 0
        · refine ⟨p + q, ?_, ?_, ?_, ?_⟩
          · simp [Pi.add_apply, hp₀, hq₀]
          · simp [Pi.add_apply, hp₁, hq₁]
          · rw [symB_add_right, h1, add_zero]; exact hpu
          · rw [symB_add_left, h2, zero_add]; exact hqv'
        · exact ⟨p, hp₀, hp₁, hpu, h2⟩
      · exact ⟨q, hq₀, hq₁, h1, hqv'⟩
    obtain ⟨z, hz₀, hz₁, hzu, hzv⟩ := key
    obtain ⟨g₁, hg₁, hg₁z, hg₁e, hg₁f⟩ :=
      s16k_exists_move_of_symB_ne hu₀ hu₁ hz₀ hz₁ hzu
    obtain ⟨g₂, hg₂, hg₂v, hg₂e, hg₂f⟩ :=
      s16k_exists_move_of_symB_ne hz₀ hz₁ hv₀ hv₁ hzv
    refine ⟨g₂ * g₁, (spGroup m K).mul_mem hg₂ hg₁, ?_, ?_, ?_⟩
    · rw [Units.val_mul, ← Matrix.mulVec_mulVec, hg₁z, hg₂v]
    · rw [Units.val_mul, ← Matrix.mulVec_mulVec, hg₁e, hg₂e]
    · rw [Units.val_mul, ← Matrix.mulVec_mulVec, hg₁f, hg₂f]
  · exact s16k_exists_move_of_symB_ne hu₀ hu₁ hv₀ hv₁ huv

private theorem s16k_close {K : Type} [Field K] [Finite K] {m : ℕ}
    (a b : Multiplicative (Fin m ⊕ Fin m → K))
    {av bv : Fin m ⊕ Fin m → K}
    (hav : av = Multiplicative.toAdd a) (hbv : bv = Multiplicative.toAdd b)
    {R₁ R₂ : ↥(StatedSp m K)} (hR₁3 : orderOf R₁ = 3) (hR₂3 : orderOf R₂ = 3)
    (hRcomm : R₁ * R₂ = R₂ * R₁) (hRnot : R₂ ∉ Subgroup.zpowers R₁)
    {k : ↥(StatedSp m K)} {w e₀ : Fin m ⊕ Fin m → K}
    (hkav : k • av = e₀) (hkbv : k • bv = w)
    (hR₁e₀ : R₁ • e₀ = e₀) (hR₂e₀ : R₂ • e₀ = e₀)
    (hR₁w : R₁ • w = w) (hR₂w : R₂ • w = w) :
    ∃ B : Subgroup ↥(StatedSp m K), IsPGroup 3 B ∧ ¬ IsCyclic ↥B ∧ ∀ g ∈ B,
      natAct (StatedSp m K) g a = a ∧ natAct (StatedSp m K) g b = b := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite ↥(StatedSp m K) := by infer_instance
  obtain ⟨hT₁3', hT₂3', hTcomm', hTnot'⟩ :=
    s16c13bcA_pair_conj hR₁3 hR₂3 hRcomm hRnot k⁻¹
  set T₁ : ↥(StatedSp m K) := k⁻¹ * R₁ * k with hT₁
  set T₂ : ↥(StatedSp m K) := k⁻¹ * R₂ * k with hT₂
  have hT₁3 : orderOf T₁ = 3 := by simpa only [hT₁, inv_inv] using hT₁3'
  have hT₂3 : orderOf T₂ = 3 := by simpa only [hT₂, inv_inv] using hT₂3'
  have hTcomm : T₁ * T₂ = T₂ * T₁ := by simpa only [hT₁, hT₂, inv_inv] using hTcomm'
  have hTnot : T₂ ∉ Subgroup.zpowers T₁ := by
    simpa only [hT₁, hT₂, inv_inv] using hTnot'
  have hT₁av : T₁ • av = av := by
    rw [hT₁, mul_smul, mul_smul, hkav, hR₁e₀]
    rw [← hkav, ← mul_smul, inv_mul_cancel, one_smul]
  have hT₂av : T₂ • av = av := by
    rw [hT₂, mul_smul, mul_smul, hkav, hR₂e₀]
    rw [← hkav, ← mul_smul, inv_mul_cancel, one_smul]
  have hT₁bv : T₁ • bv = bv := by
    rw [hT₁, mul_smul, mul_smul, hkbv, hR₁w]
    rw [← hkbv, ← mul_smul, inv_mul_cancel, one_smul]
  have hT₂bv : T₂ • bv = bv := by
    rw [hT₂, mul_smul, mul_smul, hkbv, hR₂w]
    rw [← hkbv, ← mul_smul, inv_mul_cancel, one_smul]
  have hT₁a : natAct (StatedSp m K) T₁ a = a := by
    rw [s16k_natAct_eq_ofAdd_smul, ← hav, hT₁av, hav, ofAdd_toAdd]
  have hT₂a : natAct (StatedSp m K) T₂ a = a := by
    rw [s16k_natAct_eq_ofAdd_smul, ← hav, hT₂av, hav, ofAdd_toAdd]
  have hT₁b : natAct (StatedSp m K) T₁ b = b := by
    rw [s16k_natAct_eq_ofAdd_smul, ← hbv, hT₁bv, hbv, ofAdd_toAdd]
  have hT₂b : natAct (StatedSp m K) T₂ b = b := by
    rw [s16k_natAct_eq_ofAdd_smul, ← hbv, hT₂bv, hbv, ofAdd_toAdd]
  let Hfix : Subgroup ↥(StatedSp m K) :=
    { carrier := {x | natAct (StatedSp m K) x a = a ∧ natAct (StatedSp m K) x b = b}
      one_mem' := ⟨s16k_natAct_one _ _, s16k_natAct_one _ _⟩
      mul_mem' := fun hx hy =>
        ⟨by rw [s16k_natAct_mul, hy.1, hx.1], by rw [s16k_natAct_mul, hy.2, hx.2]⟩
      inv_mem' := fun hx =>
        ⟨s16k_natAct_inv _ _ _ hx.1, s16k_natAct_inv _ _ _ hx.2⟩ }
  have hle : Subgroup.closure ({T₁, T₂} : Set ↥(StatedSp m K)) ≤ Hfix := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | hx
    · exact ⟨hT₁a, hT₁b⟩
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact ⟨hT₂a, hT₂b⟩
  refine ⟨Subgroup.closure ({T₁, T₂} : Set ↥(StatedSp m K)),
    (s16c13bcA_pair_group Nat.prime_three hT₁3 hT₂3 hTcomm hTnot).1,
    (s16c13bcA_pair_group Nat.prime_three hT₁3 hT₂3 hTcomm hTnot).2, ?_⟩
  intro g hg
  exact hle hg

theorem s16k_sp_pair_fix {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) {m : ℕ}
    (hm : 4 ≤ m) (a b : Multiplicative (Fin m ⊕ Fin m → K)) (hab : a ≠ 1 ∨ b ≠ 1) :
    ∃ B : Subgroup ↥(StatedSp m K), IsPGroup 3 B ∧ ¬ IsCyclic ↥B ∧ ∀ g ∈ B,
      natAct (StatedSp m K) g a = a ∧ natAct (StatedSp m K) g b = b := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsp : spGroup m K ≤ StatedSp m K := s16k_spGroup_le_statedSp m K
  let i₀ : Fin m := ⟨0, by omega⟩
  let i₁ : Fin m := ⟨1, by omega⟩
  let i₂ : Fin m := ⟨2, by omega⟩
  let i₃ : Fin m := ⟨3, by omega⟩
  set e₀ : Fin m ⊕ Fin m → K := s16k_e (K := K) i₀ with he₀
  set f₀ : Fin m ⊕ Fin m → K := s16k_f (K := K) i₀ with hf₀
  set e₃ : Fin m ⊕ Fin m → K := s16k_e (K := K) i₃ with he₃
  obtain ⟨r₁, hr₁, hr₁x⟩ := s16k_exists_rot (K := K) i₁
  obtain ⟨r₂, hr₂, hr₂x⟩ := s16k_exists_rot (K := K) i₂
  let R₁ : ↥(StatedSp m K) := ⟨r₁, hsp hr₁⟩
  let R₂ : ↥(StatedSp m K) := ⟨r₂, hsp hr₂⟩
  have hR₁3 : orderOf R₁ = 3 := by
    rw [Subgroup.orderOf_mk]; exact s16k_rot_orderOf hr₁x
  have hR₂3 : orderOf R₂ = 3 := by
    rw [Subgroup.orderOf_mk]; exact s16k_rot_orderOf hr₂x
  have hRcomm_mat : (r₁ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) * r₂ = r₂ * r₁ := by
    rw [Matrix.ext_iff_mulVec]
    intro x
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hr₁x, hr₂x, hr₂x, hr₁x]
    exact s16k_rot_comm (by simp [i₁, i₂, Fin.ext_iff]) x
  have hRcomm : R₁ * R₂ = R₂ * R₁ := by
    apply Subtype.ext
    apply Units.ext
    show (r₁ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) * r₂ = r₂ * r₁
    exact hRcomm_mat
  have hRnot : R₂ ∉ Subgroup.zpowers R₁ := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    have hk' : r₁ ^ k = r₂ := by
      have := congrArg (Subtype.val) hk
      simpa using this
    have hmem2 : r₂ ∈ Subgroup.zpowers r₁ := Subgroup.mem_zpowers_iff.2 ⟨k, hk'⟩
    have hfix₁ : r₁ • s16k_e (K := K) i₂ = s16k_e (K := K) i₂ := by
      change (r₁ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ s16k_e (K := K) i₂ =
        s16k_e (K := K) i₂
      rw [hr₁x]
      exact s16k_rot_eq_self (by simp [s16k_e, i₁, i₂, Fin.ext_iff])
        (by simp [s16k_e, i₂])
    have hfix₂ : r₂ • s16k_e (K := K) i₂ = s16k_e (K := K) i₂ :=
      smul_eq_self_of_mem_zpowers hmem2 hfix₁
    have hmove : r₂ • s16k_e (K := K) i₂ = s16k_f (K := K) i₂ := by
      change (r₂ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ s16k_e (K := K) i₂ =
        s16k_f (K := K) i₂
      rw [hr₂x]; exact s16k_rot_e i₂
    rw [hmove] at hfix₂
    exact s16k_e_ne_f i₂ hfix₂.symm
  have hR₁e₀ : R₁ • e₀ = e₀ := by
    change (r₁ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ e₀ = e₀
    rw [he₀, hr₁x]
    exact s16k_rot_eq_self (by simp [s16k_e, i₀, i₁, Fin.ext_iff])
      (by simp [s16k_e, i₀, i₁, Fin.ext_iff])
  have hR₂e₀ : R₂ • e₀ = e₀ := by
    change (r₂ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ e₀ = e₀
    rw [he₀, hr₂x]
    exact s16k_rot_eq_self (by simp [s16k_e, i₀, i₂, Fin.ext_iff])
      (by simp [s16k_e, i₀, i₂, Fin.ext_iff])
  have hR₁f₀ : R₁ • f₀ = f₀ := by
    change (r₁ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ f₀ = f₀
    rw [hf₀, hr₁x]
    exact s16k_rot_eq_self (by simp [s16k_f, i₀, i₁, Fin.ext_iff])
      (by simp [s16k_f, i₀, i₁, Fin.ext_iff])
  have hR₂f₀ : R₂ • f₀ = f₀ := by
    change (r₂ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ f₀ = f₀
    rw [hf₀, hr₂x]
    exact s16k_rot_eq_self (by simp [s16k_f, i₀, i₂, Fin.ext_iff])
      (by simp [s16k_f, i₀, i₂, Fin.ext_iff])
  have hR₁e₃ : R₁ • e₃ = e₃ := by
    change (r₁ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ e₃ = e₃
    rw [he₃, hr₁x]
    exact s16k_rot_eq_self (by simp [s16k_e, i₁, i₃, Fin.ext_iff])
      (by simp [s16k_e, i₁, i₃, Fin.ext_iff])
  have hR₂e₃ : R₂ • e₃ = e₃ := by
    change (r₂ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ e₃ = e₃
    rw [he₃, hr₂x]
    exact s16k_rot_eq_self (by simp [s16k_e, i₂, i₃, Fin.ext_iff])
      (by simp [s16k_e, i₂, i₃, Fin.ext_iff])
  have hmain : ∀ (a b : Multiplicative (Fin m ⊕ Fin m → K)), a ≠ 1 →
      ∃ B : Subgroup ↥(StatedSp m K), IsPGroup 3 B ∧ ¬ IsCyclic ↥B ∧ ∀ g ∈ B,
        natAct (StatedSp m K) g a = a ∧ natAct (StatedSp m K) g b = b := by
    intro a b ha
    set av : Fin m ⊕ Fin m → K := Multiplicative.toAdd a with hav
    set bv : Fin m ⊕ Fin m → K := Multiplicative.toAdd b with hbv
    have ha0 : av ≠ 0 := by
      intro h
      rw [hav] at h
      exact ha (toAdd_eq_zero.mp h)
    obtain ⟨gA, hgA, hgAav⟩ := exists_spGroup_mulVec_eq (K := K) (n := m) ha0 (s16k_e_ne_zero i₀)
    let g : ↥(StatedSp m K) := ⟨gA, hsp hgA⟩
    have hgav : g • av = e₀ := by
      change (gA : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ av = e₀
      exact hgAav
    set bp : Fin m ⊕ Fin m → K := g • bv with hbp
    set c : K := bp (Sum.inl i₀) with hc
    set d : K := bp (Sum.inr i₀) with hd
    set y : Fin m ⊕ Fin m → K := bp - c • e₀ - d • f₀ with hy
    have hbp_decomp : bp = c • e₀ + d • f₀ + y := by rw [hy]; abel
    have hy_inl : y (Sum.inl i₀) = 0 := by
      rw [hy]
      simp [hc, hd, he₀, hf₀, s16k_e, s16k_f, Pi.single_apply, Pi.sub_apply, Pi.smul_apply]
    have hy_inr : y (Sum.inr i₀) = 0 := by
      rw [hy]
      simp [hc, hd, he₀, hf₀, s16k_e, s16k_f, Pi.single_apply, Pi.sub_apply, Pi.smul_apply]
    by_cases hy0 : y = 0
    · have hbp_eq : bp = c • e₀ + d • f₀ := by rw [hbp_decomp, hy0, add_zero]
      have hR₁w : R₁ • bp = bp := by
        rw [hbp_eq, smul_add, smul_comm R₁ c e₀, smul_comm R₁ d f₀, hR₁e₀, hR₁f₀]
      have hR₂w : R₂ • bp = bp := by
        rw [hbp_eq, smul_add, smul_comm R₂ c e₀, smul_comm R₂ d f₀, hR₂e₀, hR₂f₀]
      exact s16k_close a b hav hbv hR₁3 hR₂3 hRcomm hRnot (k := g) (w := bp) (e₀ := e₀)
        hgav hbp.symm hR₁e₀ hR₂e₀ hR₁w hR₂w
    · have he₃_inl : e₃ (Sum.inl i₀) = 0 := by
        simp [he₃, s16k_e, i₀, i₃, Fin.ext_iff]
      have he₃_inr : e₃ (Sum.inr i₀) = 0 := by
        simp [he₃, s16k_e, i₀, i₃, Fin.ext_iff]
      obtain ⟨hA, hhA, hhy, hhe₀, hhf₀⟩ :=
        s16k_exists_spGroup_mulVec_eq_of_W hy_inl hy_inr hy0 he₃_inl he₃_inr (s16k_e_ne_zero i₃)
      let h : ↥(StatedSp m K) := ⟨hA, hsp hhA⟩
      have hhh_e₀ : h • e₀ = e₀ := hhe₀
      have hhh_f₀ : h • f₀ = f₀ := hhf₀
      have hhh_y : h • y = e₃ := hhy
      set w : Fin m ⊕ Fin m → K := h • bp with hw
      have hw_eq : w = c • e₀ + d • f₀ + e₃ := by
        rw [hw, hbp_decomp, smul_add, smul_add, smul_comm h c e₀, smul_comm h d f₀,
          hhh_e₀, hhh_f₀, hhh_y]
      have hR₁w : R₁ • w = w := by
        rw [hw_eq, smul_add, smul_add, smul_comm R₁ c e₀, smul_comm R₁ d f₀, hR₁e₀, hR₁f₀,
          hR₁e₃]
      have hR₂w : R₂ • w = w := by
        rw [hw_eq, smul_add, smul_add, smul_comm R₂ c e₀, smul_comm R₂ d f₀, hR₂e₀, hR₂f₀,
          hR₂e₃]
      have hkgav : (h * g) • av = e₀ := by
        rw [mul_smul, hgav, hhh_e₀]
      have hkgbv : (h * g) • bv = w := by
        rw [mul_smul, ← hbp, hw]
      exact s16k_close a b hav hbv hR₁3 hR₂3 hRcomm hRnot (k := h * g) (w := w) (e₀ := e₀)
        hkgav hkgbv hR₁e₀ hR₂e₀ hR₁w hR₂w
  rcases hab with ha | hb
  · exact hmain a b ha
  · obtain ⟨B, hBp, hBc, hBfix⟩ := hmain b a hb
    exact ⟨B, hBp, hBc, fun g hg => ⟨(hBfix g hg).2, (hBfix g hg).1⟩⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
