module

public import CFSG.Quasithin.AppendixH.H9.ModelBasic
public import CFSG.Quasithin.AppendixH.H9.ConjTransport
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagData
import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open

variable {n : ℕ}

@[expose] def ez (m : ℕ) : Fin (m + 1) → ZMod 2 := Pi.single 0 1

@[expose] def ezl (m : ℕ) : Fin (m + 1) → ZMod 2 := Pi.single (Fin.last m) 1

@[expose] def revGL (n : ℕ) : GL (Fin n) (ZMod 2) where
  val := Matrix.of fun i j => if j = Fin.rev i then 1 else 0
  inv := Matrix.of fun i j => if j = Fin.rev i then 1 else 0
  val_inv := by
    ext i k
    simp only [Matrix.mul_apply, Matrix.one_apply, Matrix.of_apply]
    rw [Finset.sum_eq_single (Fin.rev i)]
    · simp [Fin.rev_rev, eq_comm]
    · intro j _ hj; simp [hj]
    · simp
  inv_val := by
    ext i k
    simp only [Matrix.mul_apply, Matrix.one_apply, Matrix.of_apply]
    rw [Finset.sum_eq_single (Fin.rev i)]
    · simp [Fin.rev_rev, eq_comm]
    · intro j _ hj; simp [hj]
    · simp

@[expose] def utriGL (n : ℕ) : Subgroup (GL (Fin n) (ZMod 2)) :=
  (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.unitriangular n (ZMod 2)).map
    (Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin n) (ZMod 2) →* GL (Fin n) (ZMod 2))

@[expose] noncomputable def T0 (n : ℕ) : Subgroup (MulAut (PairN n)) :=
  (utriGL n).map (pairActN n) ⊔ Subgroup.zpowers (pairActN n (revGL n) * swapN n)

theorem mem_utriGL_iff {A : GL (Fin n) (ZMod 2)} :
    A ∈ utriGL n ↔ (∀ i j : Fin n, j < i → (A : Matrix (Fin n) (Fin n) (ZMod 2)) i j = 0) ∧
      ∀ i : Fin n, (A : Matrix (Fin n) (Fin n) (ZMod 2)) i i = 1 := by
  constructor
  · rintro ⟨B, hB, rfl⟩
    exact hB
  · rintro ⟨h1, h2⟩
    have hdet : (A : Matrix (Fin n) (Fin n) (ZMod 2)).det = 1 := by
      rw [Matrix.det_of_isUpperTriangular (fun i j hij => h1 i j hij)]
      exact Finset.prod_eq_one fun i _ => h2 i
    exact ⟨⟨A, hdet⟩, ⟨h1, h2⟩, Units.ext rfl⟩

theorem card_utriGL (n : ℕ) : Nat.card (utriGL n) = 2 ^ (n * (n - 1) / 2) := by
  unfold utriGL
  rw [Subgroup.card_map_of_injective Matrix.SpecialLinearGroup.toGL_injective,
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_unitriangular, Nat.card_zmod]

theorem padicValNat_card_GL_two (n : ℕ) :
    padicValNat 2 (Nat.card (GL (Fin n) (ZMod 2))) = n * (n - 1) / 2 := by
  rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_GL_eq, Nat.card_zmod]
  have hprod : ¬ 2 ∣ ∏ j ∈ Finset.Icc 1 n, (2 ^ j - 1) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.prod_Icc_one_eq _ hn]
      simpa using CFSG.LocalAnalysis.ComponentInitial.LinearFlag.not_dvd_prod_pow_sub_one
        Nat.prime_two (dvd_refl 2) (by norm_num) n
  have hne : ∏ j ∈ Finset.Icc 1 n, (2 ^ j - 1) ≠ 0 := fun h => hprod (h ▸ dvd_zero 2)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [padicValNat.mul (by positivity) hne, padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd hprod, add_zero]

theorem isSylowIn_utriGL (n : ℕ) : IsSylowIn 2 (utriGL n) (⊤ : Subgroup (GL (Fin n) (ZMod 2))) := by
  refine isSylowIn_of_card_eq le_top ?_
  rw [card_utriGL, Subgroup.card_top, Nat.factorization_def _ Nat.prime_two,
    padicValNat_card_GL_two]

theorem revGL_mul_self (n : ℕ) : revGL n * revGL n = 1 :=
  Units.ext (revGL n).val_inv

private theorem revGL_val_apply (n : ℕ) (i j : Fin n) :
    ((revGL n : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) i j =
      if j = Fin.rev i then 1 else 0 := rfl

private theorem revGL_inv (n : ℕ) : (revGL n)⁻¹ = revGL n :=
  inv_eq_of_mul_eq_one_right (revGL_mul_self n)

private theorem revGL_transpose (n : ℕ) :
    ((revGL n : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ =
      ((revGL n : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) := by
  ext i j
  rw [Matrix.transpose_apply, revGL_val_apply, revGL_val_apply]
  have : (i = Fin.rev j) ↔ (j = Fin.rev i) := by
    constructor <;> intro h <;> simp [h]
  simp only [this]

theorem dualGLn_revGL (n : ℕ) : dualGLn n (revGL n) = revGL n :=
  Units.ext (by rw [dualGLn_val, revGL_inv, revGL_transpose])

theorem revGL_mulVec_ez (m : ℕ) :
    ((revGL (m + 1) : GL (Fin (m + 1)) (ZMod 2)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)) *ᵥ ez m =
      ezl m := by
  ext i
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single (0 : Fin (m + 1))]
  · have h : (0 : Fin (m + 1)) = Fin.rev i ↔ i = Fin.last m := by
      rw [Fin.ext_iff, Fin.ext_iff, Fin.val_rev, Fin.val_last, Fin.val_zero]
      have := i.isLt
      omega
    simp [revGL_val_apply, ez, ezl, Pi.single_apply, h]
  · intro j _ hj
    simp [ez, Pi.single_apply, hj]
  · simp

private theorem revGL_mulVec_ezl (m : ℕ) :
    ((revGL (m + 1) : GL (Fin (m + 1)) (ZMod 2)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)) *ᵥ ezl m =
      ez m := by
  ext i
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single (Fin.last m)]
  · have h : Fin.last m = Fin.rev i ↔ i = 0 := by
      rw [Fin.ext_iff, Fin.ext_iff, Fin.val_rev, Fin.val_last, Fin.val_zero]
      have := i.isLt
      omega
    simp [revGL_val_apply, ez, ezl, Pi.single_apply, h]
  · intro j _ hj
    simp [ezl, Pi.single_apply, hj]
  · simp

theorem revGL_mul_dualGLn_mul_revGL_mem_utriGL {A : GL (Fin n) (ZMod 2)} (hA : A ∈ utriGL n) :
    revGL n * dualGLn n A * revGL n ∈ utriGL n := by
  have hmul : ∀ (X : Matrix (Fin n) (Fin n) (ZMod 2)) (i j : Fin n),
      (((revGL n : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) * X *
        ((revGL n : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))) i j =
        X (Fin.rev i) (Fin.rev j) := by
    intro X i j
    simp only [Matrix.mul_apply, revGL_val_apply, mul_ite, mul_one, mul_zero, ite_mul, one_mul,
      zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [Finset.sum_eq_single (Fin.rev j)]
    · simp
    · intro k _ hk
      have : j ≠ Fin.rev k := fun h => hk (by rw [h, Fin.rev_rev])
      simp [this]
    · simp
  obtain ⟨h1, h2⟩ := mem_utriGL_iff.1 ((utriGL n).inv_mem hA)
  rw [mem_utriGL_iff]
  refine ⟨fun i j hji => ?_, fun i => ?_⟩
  · rw [Units.val_mul, Units.val_mul, hmul, dualGLn_val, Matrix.transpose_apply]
    exact h1 _ _ (Fin.rev_lt_rev.2 hji)
  · rw [Units.val_mul, Units.val_mul, hmul, dualGLn_val, Matrix.transpose_apply]
    exact h2 _

private theorem outerGen_mem_T0 (n : ℕ) : pairActN n (revGL n) * swapN n ∈ T0 n :=
  Subgroup.mem_sup_right (Subgroup.mem_zpowers _)

private theorem pairActN_mem_T0 {n : ℕ} {A : GL (Fin n) (ZMod 2)} (hA : A ∈ utriGL n) :
    pairActN n A ∈ T0 n :=
  Subgroup.mem_sup_left (Subgroup.mem_map_of_mem _ hA)

private theorem outerGen_mul_self (n : ℕ) :
    (pairActN n (revGL n) * swapN n) * (pairActN n (revGL n) * swapN n) = 1 := by
  calc (pairActN n (revGL n) * swapN n) * (pairActN n (revGL n) * swapN n)
      = pairActN n (revGL n) * (swapN n * pairActN n (revGL n)) * swapN n := by
        simp only [mul_assoc]
    _ = pairActN n (revGL n * dualGLn n (revGL n)) * (swapN n * swapN n) := by
        rw [swapN_mul_pairActN, map_mul]
        simp only [mul_assoc]
    _ = 1 := by rw [swapN_mul_self, dualGLn_revGL, revGL_mul_self, map_one, mul_one]

private theorem outerGen_mul_pairActN (n : ℕ) (B : GL (Fin n) (ZMod 2)) :
    (pairActN n (revGL n) * swapN n) * pairActN n B =
      pairActN n (revGL n * dualGLn n B * revGL n) * (pairActN n (revGL n) * swapN n) := by
  have h : revGL n * dualGLn n B * revGL n * revGL n = revGL n * dualGLn n B := by
    rw [mul_assoc (revGL n * dualGLn n B), revGL_mul_self, mul_one]
  calc (pairActN n (revGL n) * swapN n) * pairActN n B
      = pairActN n (revGL n * dualGLn n B) * swapN n := by
        rw [mul_assoc, swapN_mul_pairActN, ← mul_assoc, ← map_mul]
    _ = pairActN n (revGL n * dualGLn n B * revGL n * revGL n) * swapN n := by rw [h]
    _ = _ := by
        rw [map_mul (pairActN n) (revGL n * dualGLn n B * revGL n) (revGL n)]
        simp only [mul_assoc]

private theorem mem_T0_iff_aux {s : MulAut (PairN n)} :
    s ∈ T0 n ↔ (∃ A ∈ utriGL n, s = pairActN n A) ∨
      ∃ A ∈ utriGL n, s = pairActN n A * (pairActN n (revGL n) * swapN n) := by
  set t₀ : MulAut (PairN n) := pairActN n (revGL n) * swapN n with ht₀
  have hdu : ∀ B ∈ utriGL n, revGL n * dualGLn n B * revGL n ∈ utriGL n :=
    fun B hB => revGL_mul_dualGLn_mul_revGL_mem_utriGL hB
  have hmulB : ∀ B : GL (Fin n) (ZMod 2),
      t₀ * pairActN n B = pairActN n (revGL n * dualGLn n B * revGL n) * t₀ :=
    fun B => outerGen_mul_pairActN n B
  have hsq : t₀ * t₀ = 1 := outerGen_mul_self n
  have hinv : t₀⁻¹ = t₀ := inv_eq_of_mul_eq_one_right hsq
  let S : Subgroup (MulAut (PairN n)) :=
    { carrier := {s | (∃ A ∈ utriGL n, s = pairActN n A) ∨
        ∃ A ∈ utriGL n, s = pairActN n A * t₀}
      one_mem' := Or.inl ⟨1, (utriGL n).one_mem, (map_one _).symm⟩
      mul_mem' := by
        rintro a b (⟨A, hA, rfl⟩ | ⟨A, hA, rfl⟩) (⟨B, hB, rfl⟩ | ⟨B, hB, rfl⟩)
        · exact Or.inl ⟨A * B, (utriGL n).mul_mem hA hB, (map_mul _ _ _).symm⟩
        · refine Or.inr ⟨A * B, (utriGL n).mul_mem hA hB, ?_⟩
          rw [map_mul, mul_assoc]
        · refine Or.inr ⟨A * (revGL n * dualGLn n B * revGL n),
            (utriGL n).mul_mem hA (hdu B hB), ?_⟩
          rw [mul_assoc, hmulB, map_mul (pairActN n) A (revGL n * dualGLn n B * revGL n)]
          exact (mul_assoc _ _ _).symm
        · refine Or.inl ⟨A * (revGL n * dualGLn n B * revGL n),
            (utriGL n).mul_mem hA (hdu B hB), ?_⟩
          calc pairActN n A * t₀ * (pairActN n B * t₀)
              = pairActN n A * (t₀ * pairActN n B) * t₀ := by simp only [mul_assoc]
            _ = pairActN n A * (pairActN n (revGL n * dualGLn n B * revGL n) * t₀) * t₀ := by
                rw [hmulB]
            _ = pairActN n A * pairActN n (revGL n * dualGLn n B * revGL n) * (t₀ * t₀) := by
                simp only [mul_assoc]
            _ = _ := by rw [hsq, mul_one, ← map_mul]
      inv_mem' := by
        rintro a (⟨A, hA, rfl⟩ | ⟨A, hA, rfl⟩)
        · exact Or.inl ⟨A⁻¹, (utriGL n).inv_mem hA, (map_inv _ _).symm⟩
        · refine Or.inr ⟨revGL n * dualGLn n A⁻¹ * revGL n,
            hdu _ ((utriGL n).inv_mem hA), ?_⟩
          rw [mul_inv_rev, hinv, ← map_inv, hmulB] }
  have hT0 : T0 n = S := by
    refine le_antisymm (sup_le ?_ ?_) ?_
    · rintro _ ⟨A, hA, rfl⟩
      exact Or.inl ⟨A, hA, rfl⟩
    · refine Subgroup.zpowers_le.2 (Or.inr ⟨1, (utriGL n).one_mem, ?_⟩)
      rw [map_one, one_mul]
    · rintro s (⟨A, hA, rfl⟩ | ⟨A, hA, rfl⟩)
      · exact pairActN_mem_T0 hA
      · exact (T0 n).mul_mem (pairActN_mem_T0 hA) (outerGen_mem_T0 n)
  rw [hT0]
  exact Iff.rfl

theorem T0_le_Mg (n : ℕ) : T0 n ≤ Mg n :=
  sup_le ((Subgroup.map_le_range (pairActN n) _).trans Lg_le_Mg)
    (Subgroup.zpowers_le.2 (outer_mem_Mg _))

theorem T0_inf_Lg (hn : 0 < n) : T0 n ⊓ Lg n = (utriGL n).map (pairActN n) := by
  ext s
  constructor
  · rintro ⟨hs, hsL⟩
    rcases mem_T0_iff_aux.1 hs with ⟨A, hA, rfl⟩ | ⟨A, hA, rfl⟩
    · exact Subgroup.mem_map_of_mem _ hA
    · refine absurd ?_ (outer_not_mem_Lg hn (A * revGL n))
      rw [map_mul, mul_assoc]
      exact hsL
  · intro hs
    refine ⟨Subgroup.mem_sup_left hs, ?_⟩
    obtain ⟨A, -, rfl⟩ := hs
    exact pairActN_mem_Lg A

theorem T0_inf_stabSub_V1n (hn : 0 < n) : T0 n ⊓ stabSub (V1n n) = (utriGL n).map (pairActN n) := by
  rw [← T0_inf_Lg hn]
  ext s
  constructor
  · rintro ⟨hs, hs'⟩
    exact ⟨hs, (Mg_inf_stabSub_V1n hn).le ⟨T0_le_Mg n hs, hs'⟩⟩
  · rintro ⟨hs, hsL⟩
    exact ⟨hs, Lg_le_stabSub_V1n hsL⟩

theorem mem_T0_iff {s : MulAut (PairN n)} :
    s ∈ T0 n ↔ (∃ A ∈ utriGL n, s = pairActN n A) ∨
      ∃ A ∈ utriGL n, s = pairActN n A * (pairActN n (revGL n) * swapN n) :=
  mem_T0_iff_aux

theorem card_T0 (hn : 0 < n) : Nat.card (T0 n) = 2 * 2 ^ (n * (n - 1) / 2) := by
  have ht₀ := outerGen_mem_T0 n
  have h1 : pairActN n (revGL n) * swapN n ∉ Lg n := by
    have := outer_not_mem_Lg hn (revGL n)
    exact this
  have hidx : ((T0 n ⊓ Lg n).subgroupOf (T0 n)).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨_, ht₀⟩, ?_⟩
    rintro ⟨b, hb⟩
    rcases mem_T0_iff_aux.1 hb with ⟨A, hA, rfl⟩ | ⟨A, hA, rfl⟩
    · have h1' : pairActN n A * (pairActN n (revGL n) * swapN n) ∉ Lg n := by
        rw [← mul_assoc, ← map_mul]
        exact outer_not_mem_Lg hn _
      exact Or.inr ⟨⟨hb, pairActN_mem_Lg A⟩, fun h => h1' h.2⟩
    · have h1' : pairActN n A * (pairActN n (revGL n) * swapN n) ∉ Lg n := by
        rw [← mul_assoc, ← map_mul]
        exact outer_not_mem_Lg hn _
      have h2 : pairActN n A * (pairActN n (revGL n) * swapN n) *
          (pairActN n (revGL n) * swapN n) ∈ Lg n := by
        rw [mul_assoc, outerGen_mul_self, mul_one]
        exact pairActN_mem_Lg A
      exact Or.inl ⟨⟨(T0 n).mul_mem hb ht₀, h2⟩, fun h => h1' h.2⟩
  have h1 := Subgroup.card_mul_index ((T0 n ⊓ Lg n).subgroupOf (T0 n))
  rw [hidx, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : T0 n ⊓ Lg n ≤ T0 n)).toEquiv,
    T0_inf_Lg hn, Subgroup.card_map_of_injective pairActN_injective, card_utriGL] at h1
  rw [← h1, mul_comm]

theorem isSylowIn_T0 (hn : 0 < n) : IsSylowIn 2 (T0 n) (Mg n) := by
  refine isSylowIn_of_card_eq (T0_le_Mg n) ?_
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [card_T0 hn, card_Mg hn, Nat.factorization_def _ Nat.prime_two,
    padicValNat.mul (by norm_num) Nat.card_pos.ne', padicValNat_card_GL_two, padicValNat_self,
    pow_add, pow_one]

private theorem exists_mem_conj_eq_of_isSylowIn {G : Type*} [Group G] [Finite G]
    {P Q H : Subgroup G} (hP : IsSylowIn 2 P H) (hQ : IsSylowIn 2 Q H) :
    ∃ g ∈ H, Q = P.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H hP.toSylow hQ.toSylow
  refine ⟨g, g.2, ?_⟩
  have hE : (hQ.toSylow : Subgroup H) = (hP.toSylow : Subgroup H).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul]
    ext x
    simp only [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, Subgroup.mem_map, MulAut.smul_def,
      MulAut.conj_apply, MulEquiv.coe_toMonoidHom]
    constructor
    · intro h
      exact ⟨g⁻¹ * x * g, by simpa using h, by group⟩
    · rintro ⟨y, hy, rfl⟩
      simpa [mul_assoc] using hy
  rw [IsSylowIn.coe_toSylow, IsSylowIn.coe_toSylow] at hE
  ext x
  constructor
  · intro hx
    have hxH : x ∈ H := hQ.le hx
    have h3 : (⟨x, hxH⟩ : H) ∈ (P.subgroupOf H).map (MulAut.conj g).toMonoidHom := by
      rw [← hE]
      exact hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 h3
    refine ⟨(y : G), hy, ?_⟩
    have := congrArg Subtype.val hyx
    simpa [MulAut.conj_apply] using this
  · rintro ⟨y, hy, rfl⟩
    have hyH : y ∈ H := hP.le hy
    have h4 : MulAut.conj g ⟨y, hyH⟩ ∈ (Q.subgroupOf H) := by
      rw [hE]
      exact Subgroup.mem_map_of_mem _ hy
    simpa [MulAut.conj_apply, Subgroup.mem_subgroupOf] using h4

theorem exists_Lg_conj_T0 (hn : 0 < n) {T : Subgroup (MulAut (PairN n))} (hT : IsSylowIn 2 T (Mg n)) :
    ∃ l ∈ Lg n, T = conjAut l (T0 n) := by
  obtain ⟨g, hgM, hTg⟩ := exists_mem_conj_eq_of_isSylowIn (isSylowIn_T0 hn) hT
  rcases mem_Mg_iff.1 hgM with hgL | ⟨A, rfl⟩
  · exact ⟨g, hgL, hTg⟩
  · refine ⟨pairActN n (A * revGL n), pairActN_mem_Lg _, ?_⟩
    have hg : pairActN n A * swapN n =
        pairActN n (A * revGL n) * (pairActN n (revGL n) * swapN n) := by
      rw [map_mul, mul_assoc, ← mul_assoc (pairActN n (revGL n)), ← map_mul, revGL_mul_self,
        map_one, one_mul]
    have key : conjAut (pairActN n (A * revGL n) * (pairActN n (revGL n) * swapN n)) (T0 n) =
        conjAut (pairActN n (A * revGL n)) (T0 n) :=
      (conjAut_mul _ _ _).trans (congrArg _ (conjAut_eq_self_of_mem (outerGen_mem_T0 n)))
    refine hTg.trans ?_
    rw [hg]
    exact key

private theorem utriGL_mulVec_ez (m : ℕ) {A : GL (Fin (m + 1)) (ZMod 2)} (hA : A ∈ utriGL (m + 1)) :
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)) *ᵥ ez m = ez m := by
  obtain ⟨h1, h2⟩ := mem_utriGL_iff.1 hA
  ext i
  rw [ez, Matrix.mulVec_single_one, Matrix.col_apply]
  by_cases hi : i = 0
  · subst hi
    simp [h2 0]
  · have : (0 : Fin (m + 1)) < i := Fin.pos_iff_ne_zero.2 hi
    simp [h1 i 0 this, Pi.single_apply, hi]

private theorem utriGL_dual_mulVec_ezl (m : ℕ) {A : GL (Fin (m + 1)) (ZMod 2)}
    (hA : A ∈ utriGL (m + 1)) :
    ((dualGLn (m + 1) A : GL (Fin (m + 1)) (ZMod 2)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)) *ᵥ
      ezl m = ezl m := by
  obtain ⟨h1, h2⟩ := mem_utriGL_iff.1 ((utriGL (m + 1)).inv_mem hA)
  ext i
  rw [dualGLn_val, ezl, Matrix.mulVec_single_one, Matrix.col_apply, Matrix.transpose_apply]
  by_cases hi : i = Fin.last m
  · subst hi
    simp [h2 (Fin.last m)]
  · have : i < Fin.last m := Fin.lt_last_iff_ne_last.2 hi
    simp [h1 (Fin.last m) i this, Pi.single_apply, hi]

private noncomputable def tvGL {n : ℕ} {i j : Fin n} (hij : i < j) : GL (Fin n) (ZMod 2) :=
  Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection hij.ne (1 : ZMod 2))

private theorem tvGL_val {n : ℕ} {i j : Fin n} (hij : i < j) :
    ((tvGL hij : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) =
      1 + Matrix.single i j (1 : ZMod 2) := rfl

private theorem tvGL_mem_utriGL {n : ℕ} {i j : Fin n} (hij : i < j) : tvGL hij ∈ utriGL n := by
  rw [mem_utriGL_iff, tvGL_val]
  refine ⟨fun a b hba => ?_, fun a => ?_⟩
  · rw [Matrix.add_apply, Matrix.one_apply_ne hba.ne', Matrix.single_apply_of_ne, zero_add]
    rintro ⟨rfl, rfl⟩
    exact absurd hij (not_lt.2 hba.le)
  · rw [Matrix.add_apply, Matrix.one_apply_eq, Matrix.single_apply_of_ne, add_zero]
    rintro ⟨rfl, rfl⟩
    exact hij.ne rfl

private theorem tvGL_mulVec {n : ℕ} {i j : Fin n} (hij : i < j) (v : Fin n → ZMod 2) (k : Fin n) :
    ((tvGL hij : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v) k = v k + if k = i then v j else 0 := by
  rw [tvGL_val, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec_eq]
  simp [Pi.single_apply]

private theorem dualGLn_tvGL_mulVec {n : ℕ} {i j : Fin n} (hij : i < j) (v : Fin n → ZMod 2)
    (k : Fin n) :
    (((dualGLn n (tvGL hij) : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v) k =
      v k + if k = j then v i else 0 := by
  have hsq : tvGL hij * tvGL hij = 1 := by
    refine Units.ext ?_
    rw [Units.val_mul, tvGL_val, Units.val_one]
    have h := Matrix.transvection_mul_transvection_same i j hij.ne (1 : ZMod 2) 1
    rw [show (1 : ZMod 2) + 1 = 0 from by decide, Matrix.transvection_zero] at h
    exact h
  rw [dualGLn_val, inv_eq_of_mul_eq_one_right hsq, tvGL_val, Matrix.transpose_add,
    Matrix.transpose_one, Matrix.transpose_single, Matrix.add_mulVec, Matrix.one_mulVec,
    Matrix.single_mulVec_eq]
  simp [Pi.single_apply]

private theorem eq_zero_or_ez {m : ℕ} {v : Fin (m + 1) → ZMod 2} (h : ∀ j, j ≠ 0 → v j = 0) :
    v = 0 ∨ v = ez m := by
  have h01 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases h01 (v 0) with h0 | h0
  · left
    ext j
    by_cases hj : j = 0
    · subst hj
      simpa using h0
    · simpa using h j hj
  · right
    ext j
    by_cases hj : j = 0
    · subst hj
      simp [ez, h0]
    · simp [ez, Pi.single_apply, hj, h j hj]

private theorem eq_zero_or_ezl {m : ℕ} {v : Fin (m + 1) → ZMod 2}
    (h : ∀ j, j ≠ Fin.last m → v j = 0) : v = 0 ∨ v = ezl m := by
  have h01 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases h01 (v (Fin.last m)) with h0 | h0
  · left
    ext j
    by_cases hj : j = Fin.last m
    · subst hj
      simpa using h0
    · simpa using h j hj
  · right
    ext j
    by_cases hj : j = Fin.last m
    · subst hj
      simp [ezl, h0]
    · simp [ezl, Pi.single_apply, hj, h j hj]

private theorem fixed_by_utri_fst {m : ℕ} {a b : Fin (m + 1) → ZMod 2}
    (hfix : ∀ A ∈ utriGL (m + 1), pairActN (m + 1) A (pairVec a b) = pairVec a b) :
    ∀ j, j ≠ 0 → a j = 0 := by
  intro j hj
  have hij : (0 : Fin (m + 1)) < j := Fin.pos_iff_ne_zero.2 hj
  have h := hfix _ (tvGL_mem_utriGL hij)
  rw [pairActN_pairVec] at h
  have h2 := congrFun (pairVec_inj.1 h).1 0
  rw [tvGL_mulVec hij a 0] at h2
  simpa using h2

private theorem fixed_by_utri_snd {m : ℕ} {a b : Fin (m + 1) → ZMod 2}
    (hfix : ∀ A ∈ utriGL (m + 1), pairActN (m + 1) A (pairVec a b) = pairVec a b) :
    ∀ i, i ≠ Fin.last m → b i = 0 := by
  intro i hi
  have hij : i < Fin.last m := Fin.lt_last_iff_ne_last.2 hi
  have h := hfix _ (tvGL_mem_utriGL hij)
  rw [pairActN_pairVec] at h
  have h2 := congrFun (pairVec_inj.1 h).2 (Fin.last m)
  rw [dualGLn_tvGL_mulVec hij b (Fin.last m)] at h2
  simpa using h2

theorem mem_fixV_T0_iff (m : ℕ) (hm : 1 ≤ m) (x : PairN (m + 1)) :
    x ∈ fixV (T0 (m + 1)) ↔ x = 1 ∨ x = pairVec (ez m) (ezl m) := by
  constructor
  · intro hx
    obtain ⟨a, b, rfl⟩ := pairVec_surj x
    have hfix : ∀ s ∈ T0 (m + 1), s (pairVec a b) = pairVec a b := hx
    have hU : ∀ A ∈ utriGL (m + 1), pairActN (m + 1) A (pairVec a b) = pairVec a b :=
      fun A hA => hfix _ (pairActN_mem_T0 hA)
    have ha := eq_zero_or_ez (fixed_by_utri_fst hU)
    have hb := eq_zero_or_ezl (fixed_by_utri_snd hU)
    have ht := hfix _ (outerGen_mem_T0 (m + 1))
    rw [MulAut.mul_apply, swapN_pairVec, pairActN_pairVec, dualGLn_revGL] at ht
    have hJb := (pairVec_inj.1 ht).1
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · left
      rw [pairVec_one]
    · rw [revGL_mulVec_ezl] at hJb
      have := congrFun hJb 0
      simp [ez] at this
    · rw [Matrix.mulVec_zero] at hJb
      have := congrFun hJb 0
      simp [ez] at this
    · right
      rfl
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · have key : ∀ s ∈ T0 (m + 1), s (pairVec (ez m) (ezl m)) = pairVec (ez m) (ezl m) := by
        intro s hs
        rcases mem_T0_iff.1 hs with ⟨A, hA, rfl⟩ | ⟨A, hA, rfl⟩
        · rw [pairActN_pairVec, utriGL_mulVec_ez m hA, utriGL_dual_mulVec_ezl m hA]
        · rw [MulAut.mul_apply, MulAut.mul_apply, swapN_pairVec, pairActN_pairVec, dualGLn_revGL,
            revGL_mulVec_ezl, revGL_mulVec_ez, pairActN_pairVec, utriGL_mulVec_ez m hA,
            utriGL_dual_mulVec_ezl m hA]
      exact key

private theorem mem_zpowers_iff_of_sq_eq_one {G : Type*} [Group G] {x y : G} (hx : x ^ 2 = 1) :
    y ∈ Subgroup.zpowers x ↔ y = 1 ∨ y = x := by
  constructor
  · intro hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    have h2 : x ^ (2 : ℤ) = 1 := by rw [zpow_two, ← pow_two]; exact hx
    have hk : x ^ k = x ^ (k % 2) := by
      conv_lhs => rw [← Int.emod_add_mul_ediv k 2]
      rw [zpow_add, zpow_mul, h2, one_zpow, mul_one]
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · left
      rw [hk, h, zpow_zero]
    · right
      rw [hk, h, zpow_one]
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _

theorem fixV_T0_inf_stabSub_inf_V1n (m : ℕ) :
    fixV (T0 (m + 1) ⊓ stabSub (V1n (m + 1))) ⊓ V1n (m + 1) = Subgroup.zpowers (pairVec (ez m) 0) := by
  have hU : T0 (m + 1) ⊓ stabSub (V1n (m + 1)) = (utriGL (m + 1)).map (pairActN (m + 1)) :=
    T0_inf_stabSub_V1n (Nat.succ_pos m)
  have hsq : (pairVec (ez m) 0 : PairN (m + 1)) ^ 2 = 1 := pairN_sq _
  ext y
  refine Iff.trans ?_ (mem_zpowers_iff_of_sq_eq_one hsq).symm
  constructor
  · intro hy'
    obtain ⟨hy, hy1⟩ := Subgroup.mem_inf.1 hy'
    obtain ⟨a, b, rfl⟩ := pairVec_surj y
    have hb : b = 0 := ofAdd_eq_one.1 (mem_V1n.1 hy1)
    subst hb
    have hfix : ∀ s ∈ T0 (m + 1) ⊓ stabSub (V1n (m + 1)), s (pairVec a 0) = pairVec a 0 := hy
    have hfix' : ∀ A ∈ utriGL (m + 1), pairActN (m + 1) A (pairVec a 0) = pairVec a 0 := by
      intro A hA
      refine hfix _ ?_
      rw [hU]
      exact Subgroup.mem_map_of_mem _ hA
    rcases eq_zero_or_ez (fixed_by_utri_fst hfix') with rfl | rfl
    · left
      rw [pairVec_one]
    · right
      rfl
  · rintro (rfl | rfl)
    · exact Subgroup.mem_inf.2 ⟨Subgroup.one_mem _, Subgroup.one_mem _⟩
    · refine Subgroup.mem_inf.2 ⟨?_, pairVec_mem_V1n _⟩
      have key : ∀ s ∈ T0 (m + 1) ⊓ stabSub (V1n (m + 1)),
          s (pairVec (ez m) 0) = pairVec (ez m) 0 := by
        intro s hs
        rw [hU] at hs
        obtain ⟨A, hA, rfl⟩ := hs
        rw [pairActN_pairVec, utriGL_mulVec_ez m hA, Matrix.mulVec_zero]
      exact key

theorem exists_T0_inf_Lg_apply_V2 (m : ℕ) {b b' : Fin (m + 1) → ZMod 2} (hb : b 0 = 1) (hb' : b' 0 = 1) :
    ∃ u ∈ T0 (m + 1) ⊓ Lg (m + 1), u (pairVec (ez m) 0) = pairVec (ez m) 0 ∧
      u (pairVec 0 b) = pairVec 0 b' := by
  have key : ∀ x y : ZMod 2, x + (x + y) = y := by decide
  have key2 : ∀ x : ZMod 2, x + x = 0 := by decide
  set w : Fin (m + 1) → ZMod 2 := b + b' with hw
  have hw0 : w 0 = 0 := by
    simp only [hw, Pi.add_apply, hb, hb']
    decide
  set N : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2) :=
    Matrix.of fun i j => if j = 0 then w i else 0 with hN
  have hNN : N * N = 0 := by
    ext i k
    simp only [hN, Matrix.mul_apply, Matrix.of_apply, Matrix.zero_apply]
    rw [Finset.sum_eq_single 0]
    · by_cases hk : k = 0 <;> simp [hk, hw0]
    · intro j _ hj
      simp [hj]
    · simp
  have hNN2 : N + N = 0 := by
    ext i j
    simp only [Matrix.add_apply, Matrix.zero_apply]
    exact key2 _
  have hCC : (1 + N) * (1 + N) = 1 := by
    have : (1 + N) * (1 + N) = 1 + (N + N) + N * N := by noncomm_ring
    rw [this, hNN, hNN2, add_zero, add_zero]
  let Cg : GL (Fin (m + 1)) (ZMod 2) := ⟨1 + N, 1 + N, hCC, hCC⟩
  have hAval : ((dualGLn (m + 1) Cg : GL (Fin (m + 1)) (ZMod 2)) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)) = (1 + N)ᵀ := by
    rw [dualGLn_val]
    rfl
  have hAU : dualGLn (m + 1) Cg ∈ utriGL (m + 1) := by
    rw [mem_utriGL_iff]
    refine ⟨fun i j hji => ?_, fun i => ?_⟩
    · have hi0 : i ≠ 0 := fun h => by
        subst h
        exact absurd hji (Fin.not_lt_zero j)
      rw [hAval, Matrix.transpose_apply, Matrix.add_apply, Matrix.one_apply_ne hji.ne]
      simp [hN, hi0]
    · rw [hAval, Matrix.transpose_apply, Matrix.add_apply, Matrix.one_apply_eq]
      by_cases hi : i = 0
      · subst hi
        simp [hN, hw0]
      · simp [hN, hi]
  refine ⟨pairActN (m + 1) (dualGLn (m + 1) Cg),
    ⟨Subgroup.mem_sup_left (Subgroup.mem_map_of_mem _ hAU), pairActN_mem_Lg _⟩, ?_, ?_⟩
  · rw [pairActN_pairVec, utriGL_mulVec_ez m hAU, Matrix.mulVec_zero]
  · rw [pairActN_pairVec, dualGLn_dualGLn, Matrix.mulVec_zero]
    congr 1
    ext i
    have hCb : ((Cg : GL (Fin (m + 1)) (ZMod 2)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)) *ᵥ b =
        b + N *ᵥ b := by
      show (1 + N) *ᵥ b = b + N *ᵥ b
      rw [Matrix.add_mulVec, Matrix.one_mulVec]
    have hNb : N *ᵥ b = w * fun _ => b 0 := by
      ext k
      simp only [hN, Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.mul_apply]
      rw [Finset.sum_eq_single 0]
      · simp
      · intro j _ hj
        simp [hj]
      · simp
    rw [hCb, hNb]
    simp only [Pi.add_apply, Pi.mul_apply, hb, mul_one, hw]
    exact key _ _

theorem T0_outer_not_fix (m : ℕ) (hm : 1 ≤ m) {s : MulAut (PairN (m + 1))} (hs : s ∈ T0 (m + 1))
    (hsL : s ∉ Lg (m + 1)) {b : Fin (m + 1) → ZMod 2} (hb : b 0 = 1) :
    s (pairVec (ez m) b) ≠ pairVec (ez m) b := by
  rcases mem_T0_iff.1 hs with ⟨A, hA, rfl⟩ | ⟨A, hA, rfl⟩
  · exact absurd (pairActN_mem_Lg A) hsL
  · intro h
    rw [MulAut.mul_apply, MulAut.mul_apply, swapN_pairVec, pairActN_pairVec, dualGLn_revGL,
      revGL_mulVec_ez, pairActN_pairVec, utriGL_dual_mulVec_ezl m hA] at h
    have h2 := congrFun (pairVec_inj.1 h).2 0
    have hlast : (0 : Fin (m + 1)) ≠ Fin.last m := by
      intro h0
      have := congrArg Fin.val h0
      simp only [Fin.val_zero, Fin.val_last] at this
      omega
    simp [ezl, Pi.single_apply, hlast, hb] at h2

end CFSG.ASVolI.ChH
