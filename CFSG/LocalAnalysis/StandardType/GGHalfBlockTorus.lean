module

public import CFSG.LocalAnalysis.StandardType.GGTypeAFarPerm
public import CFSG.LocalAnalysis.StandardType.GGTypeAEndNodeBlock

public section

namespace CFSG.StandardType.GGHalf

open CFSG.LieType.Universal.SpecialLinear Matrix

abbrev F2 : Type := GaloisField 2 1

theorem gf2_two : (2 : F2) = 0 :=
  two_eq_zero_of_card (GaloisField.card 2 1 (by omega)) le_rfl

@[expose] noncomputable def slLower2Hom (m : ℕ) :
    SpecialLinearGroup (Fin (m + 1)) F2 →* SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 :=
  (slLowerBlockHom (m + 1 + 1) F2).comp (slLowerBlockHom (m + 1) F2)

@[expose] noncomputable def slUpper2Hom (m : ℕ) :
    SpecialLinearGroup (Fin (m + 1)) F2 →* SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 :=
  (slUpperBlockHom (m + 1 + 1) F2).comp (slUpperBlockHom (m + 1) F2)

@[expose] noncomputable def omegaBlock (n : ℕ) (k : Fin n) : SpecialLinearGroup (Fin (n + 1)) F2 :=
  weylRep n F2 k *
    SpecialLinearGroup.transvection (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne 1

@[expose] noncomputable def halfTorus (n : ℕ) : Subgroup (SpecialLinearGroup (Fin (n + 1)) F2) :=
  Subgroup.closure {t | ∃ k : Fin n, k.val % 2 = 0 ∧ t = omegaBlock n k}

@[expose] noncomputable def halfTorusK (n : ℕ) :
    Subgroup (SpecialLinearGroup (Fin (n + 1)) F2) :=
  Subgroup.closure {t | ∃ k : Fin n,
    (k.val + 1 = n ∨ (k.val % 2 = 0 ∧ k.val + 2 < n)) ∧ t = omegaBlock n k}

@[expose] noncomputable def slOn (N : ℕ) (S : Set (Fin N)) :
    Subgroup (SpecialLinearGroup (Fin N) F2) :=
  Subgroup.closure {t | ∃ (a b : Fin N) (hab : a ≠ b) (c : F2), a ∈ S ∧ b ∈ S ∧
    t = SpecialLinearGroup.transvection hab c}

@[expose] def sigmaPerm (m : ℕ) : Equiv.Perm (Fin (m + 1 + 1 + 1)) :=
  Equiv.swap 0 2 * Equiv.swap 1 3

@[expose] def tauPerm (m : ℕ) : Equiv.Perm (Fin (m + 1 + 1 + 1)) :=
  Equiv.swap (Fin.last (m + 1)).castSucc 0 * Equiv.swap (Fin.last (m + 1 + 1)) 1

@[expose] noncomputable def supp {n : ℕ} (t : SpecialLinearGroup (Fin (n + 1)) F2) : ℕ :=
  Matrix.rank ((t : Matrix (Fin (n + 1)) (Fin (n + 1)) F2) - 1)

private theorem one_add_one_f2 : (1 : F2) + 1 = 0 := by
  linear_combination gf2_two

private theorem transvection_congr {N : ℕ} {i j i' j' : Fin N} (hij : i ≠ j) (hij' : i' ≠ j')
    (hi : i = i') (hj : j = j') (c : F2) :
    SpecialLinearGroup.transvection hij c = SpecialLinearGroup.transvection hij' c := by
  cases hi; cases hj
  exact Subtype.ext rfl

private theorem transvection_self_mul {N : ℕ} {i j : Fin N} (hij : i ≠ j) :
    SpecialLinearGroup.transvection hij (1 : F2) * SpecialLinearGroup.transvection hij 1 = 1 := by
  rw [← SpecialLinearGroup.transvection_add, one_add_one_f2]
  exact SpecialLinearGroup.transvection_coeff_zero hij

private theorem transvection_commute {N : ℕ} {a b e f : Fin N}
    (hab : a ≠ b) (hef : e ≠ f) (hbe : b ≠ e) (haf : a ≠ f) (c d : F2) :
    SpecialLinearGroup.transvection hab c * SpecialLinearGroup.transvection hef d =
      SpecialLinearGroup.transvection hef d * SpecialLinearGroup.transvection hab c := by
  refine Subtype.ext ?_
  change (1 + Matrix.single a b c : Matrix (Fin N) (Fin N) F2) *
        (1 + Matrix.single e f d) =
      (1 + Matrix.single e f d) * (1 + Matrix.single a b c)
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.one_mul, Matrix.mul_one,
    Matrix.single_mul_single_of_ne _ _ _ _ hbe,
    Matrix.single_mul_single_of_ne _ _ _ _ haf.symm, add_zero]
  abel

private theorem mul_comm_mul {G : Type*} [Group G] {a b c d : G}
    (hac : a * c = c * a) (had : a * d = d * a) (hbc : b * c = c * b) (hbd : b * d = d * b) :
    (a * b) * (c * d) = (c * d) * (a * b) := by
  calc (a * b) * (c * d) = a * (b * (c * d)) := by group
    _ = a * ((b * c) * d) := by group
    _ = a * ((c * b) * d) := by rw [hbc]
    _ = (a * c) * (b * d) := by group
    _ = (c * a) * (b * d) := by rw [hac]
    _ = (c * a) * (d * b) := by rw [hbd]
    _ = c * (a * (d * b)) := by group
    _ = c * ((a * d) * b) := by group
    _ = c * ((d * a) * b) := by rw [had]
    _ = (c * d) * (a * b) := by group

private theorem weylRep_eq_xyx (n : ℕ) (k : Fin n) :
    weylRep n F2 k =
      SpecialLinearGroup.transvection (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne 1 *
      SpecialLinearGroup.transvection
        ((show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne).symm 1 *
      SpecialLinearGroup.transvection (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne 1 := by
  rw [← slPerm_swap_castSucc_succ gf2_two k]
  exact slPerm_swap_eq_transvections gf2_two
    (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne

private theorem omegaBlock_eq_xy (n : ℕ) (k : Fin n) :
    omegaBlock n k =
      SpecialLinearGroup.transvection (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne 1 *
      SpecialLinearGroup.transvection
        ((show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne).symm 1 := by
  rw [omegaBlock, weylRep_eq_xyx]
  set x : SpecialLinearGroup (Fin (n + 1)) F2 :=
    SpecialLinearGroup.transvection (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne 1
  set y : SpecialLinearGroup (Fin (n + 1)) F2 :=
    SpecialLinearGroup.transvection
      ((show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne).symm 1
  have hxx : x * x = 1 := by
    rw [show x = SpecialLinearGroup.transvection
        (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne 1 from rfl]
    exact transvection_self_mul _
  calc (x * y * x) * x = x * y * (x * x) := by group
    _ = x * y := by rw [hxx, mul_one]

private theorem weylRep_conj_x (n : ℕ) (k : Fin n) :
    weylRep n F2 k *
      SpecialLinearGroup.transvection (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne 1 *
      weylRep n F2 k =
      SpecialLinearGroup.transvection
        ((show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne).symm 1 := by
  have hcoe := coe_weylRep_of_two n gf2_two k
  have hε : ∀ s : Fin (n + 1), (1 : Fin (n + 1) → F2) s * (1 : Fin (n + 1) → F2) s = 1 := by
    intro s; simp
  have h := conj_transvection_of_coe_eq_signedPerm (g := weylRep n F2 k)
    (π := Equiv.swap k.castSucc k.succ) (ε := (1 : Fin (n + 1) → F2)) hcoe hε
    (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne (1 : F2)
  have hinv : (weylRep n F2 k)⁻¹ = weylRep n F2 k :=
    inv_eq_of_mul_eq_one_right (weylRep_mul_self n gf2_two k)
  rw [hinv] at h
  simp only [Pi.one_apply, mul_one] at h
  rw [h]
  exact transvection_congr _ _ (Equiv.swap_apply_left _ _) (Equiv.swap_apply_right _ _) 1

private theorem even_add_two_le_of_lt {a b : ℕ} (ha : a % 2 = 0) (hb : b % 2 = 0) (h : a < b) :
    a + 2 ≤ b := by omega

private theorem weylRep_conj_y (n : ℕ) (k : Fin n) :
    weylRep n F2 k *
      SpecialLinearGroup.transvection
        ((show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne).symm 1 *
      weylRep n F2 k =
      SpecialLinearGroup.transvection (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne 1 := by
  have hs : weylRep n F2 k * weylRep n F2 k = 1 := weylRep_mul_self n gf2_two k
  have h := weylRep_conj_x n k
  calc weylRep n F2 k *
        SpecialLinearGroup.transvection
          ((show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne).symm 1 *
        weylRep n F2 k
      = weylRep n F2 k *
          (weylRep n F2 k * SpecialLinearGroup.transvection
            (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne 1 * weylRep n F2 k) *
          weylRep n F2 k := by rw [← h]
    _ = SpecialLinearGroup.transvection
          (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne 1 := by
        rw [show weylRep n F2 k *
              (weylRep n F2 k * SpecialLinearGroup.transvection
                (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne 1 * weylRep n F2 k) *
              weylRep n F2 k
            = (weylRep n F2 k * weylRep n F2 k) * SpecialLinearGroup.transvection
                (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne 1 *
                (weylRep n F2 k * weylRep n F2 k) from by group,
            hs, one_mul, mul_one]

private theorem halfTorusK_index_sep {n : ℕ} {k k' : Fin n}
    (hk : k.val + 1 = n ∨ (k.val % 2 = 0 ∧ k.val + 2 < n))
    (hk' : k'.val + 1 = n ∨ (k'.val % 2 = 0 ∧ k'.val + 2 < n))
    (hne : k ≠ k') : k.val + 2 ≤ k'.val ∨ k'.val + 2 ≤ k.val := by
  rcases hk with hk | ⟨hke, hkg⟩
  · rcases hk' with hk' | ⟨hk'e, hk'g⟩
    · exact absurd (Fin.ext (by omega)) hne
    · right; omega
  · rcases hk' with hk' | ⟨hk'e, hk'g⟩
    · left; omega
    · rcases lt_or_gt_of_ne (fun h => hne (Fin.ext h)) with h | h
      · left; omega
      · right; omega

theorem omegaBlock_pow_three (n : ℕ) (k : Fin n) : omegaBlock n k ^ 3 = 1 := by
  rw [omegaBlock_eq_xy]
  set x : SpecialLinearGroup (Fin (n + 1)) F2 :=
    SpecialLinearGroup.transvection (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne 1
  set y : SpecialLinearGroup (Fin (n + 1)) F2 :=
    SpecialLinearGroup.transvection
      ((show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne).symm 1
  have hxyx : x * y * x = slPerm gf2_two (Equiv.swap k.castSucc k.succ) := by
    rw [show x * y * x = weylRep n F2 k from (weylRep_eq_xyx n k).symm]
    exact (slPerm_swap_castSucc_succ gf2_two k).symm
  have hyxy : y * x * y = x * y * x := by
    rw [← slPerm_swap_eq_transvections gf2_two
          (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne.symm,
        hxyx]
    exact (congrArg (slPerm gf2_two) (Equiv.swap_comm k.castSucc k.succ)).symm
  calc (x * y) ^ 3 = (x * y) * (x * y) * (x * y) := by rw [pow_succ, pow_succ, pow_one]
    _ = (x * y * x) * (y * x * y) := by group
    _ = (x * y * x) * (x * y * x) := by rw [hyxy]
    _ = 1 := by
      rw [hxyx, ← map_mul, Equiv.swap_mul_self, map_one]

theorem omegaBlock_ne_one (n : ℕ) (k : Fin n) : omegaBlock n k ≠ 1 := by
  have hij : k.castSucc ≠ k.succ := (Fin.castSucc_lt_succ).ne
  intro h
  have hv : (omegaBlock n k) • (Pi.single k.succ (1 : F2) : Fin (n + 1) → F2) =
      Pi.single k.succ 1 := by
    rw [h, one_smul]
  rw [omegaBlock_eq_xy, mul_smul,
    SpecialLinearGroup.transvection_smul_single_fst, SpecialLinearGroup.transvection_smul_single_snd,
    one_smul] at hv
  have h2 := congrFun hv k.castSucc
  simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hij, zero_add] at h2
  exact one_ne_zero h2

theorem omegaBlock_comm {n : ℕ} {k k' : Fin n} (hkk : k.val + 2 ≤ k'.val) :
    omegaBlock n k * omegaBlock n k' = omegaBlock n k' * omegaBlock n k := by
  rw [omegaBlock_eq_xy (n := n) (k := k), omegaBlock_eq_xy (n := n) (k := k')]
  have val_inj : ∀ {a b : Fin n}, a = b → a.val = b.val := fun h => congrArg Fin.val h
  have hij : k.castSucc ≠ k.succ := (Fin.castSucc_lt_succ).ne
  have hi'j' : k'.castSucc ≠ k'.succ := (Fin.castSucc_lt_succ).ne
  have hji' : k.succ ≠ k'.castSucc := by
    intro h; have := congrArg Fin.val h; simp only [Fin.val_succ, Fin.val_castSucc] at this; omega
  have hij' : k.castSucc ≠ k'.succ := by
    intro h; have := congrArg Fin.val h; simp only [Fin.val_succ, Fin.val_castSucc] at this; omega
  have hii' : k.castSucc ≠ k'.castSucc := by
    intro h; have := congrArg Fin.val h; simp only [Fin.val_castSucc] at this; omega
  have hjj' : k.succ ≠ k'.succ := by
    intro h; have := congrArg Fin.val h; simp only [Fin.val_succ] at this; omega
  exact mul_comm_mul
    (transvection_commute hij hi'j' hji' hij' 1 1)
    (transvection_commute hij hi'j'.symm hjj' hii' 1 1)
    (transvection_commute hij.symm hi'j' hii' hjj' 1 1)
    (transvection_commute hij.symm hi'j'.symm hij' hji' 1 1)

theorem weylRep_mul_omegaBlock_mul_weylRep (n : ℕ) (k : Fin n) :
    weylRep n F2 k * omegaBlock n k * weylRep n F2 k = (omegaBlock n k)⁻¹ := by
  rw [omegaBlock_eq_xy]
  have hsx : weylRep n F2 k * SpecialLinearGroup.transvection
        (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne 1 * weylRep n F2 k =
      SpecialLinearGroup.transvection
        ((show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne).symm 1 := weylRep_conj_x n k
  have hsy : weylRep n F2 k * SpecialLinearGroup.transvection
        ((show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne).symm 1 * weylRep n F2 k =
      SpecialLinearGroup.transvection
        (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne 1 := weylRep_conj_y n k
  have hx2 : SpecialLinearGroup.transvection
        (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne (1 : F2) *
      SpecialLinearGroup.transvection
        (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne 1 = 1 :=
    transvection_self_mul _
  have hy2 : SpecialLinearGroup.transvection
        ((show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne).symm (1 : F2) *
      SpecialLinearGroup.transvection
        ((show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne).symm 1 = 1 :=
    transvection_self_mul _
  have hxinv : (SpecialLinearGroup.transvection
        (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne (1 : F2))⁻¹ =
      SpecialLinearGroup.transvection
        (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne 1 :=
    inv_eq_of_mul_eq_one_right hx2
  have hyinv : (SpecialLinearGroup.transvection
        ((show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne).symm (1 : F2))⁻¹ =
      SpecialLinearGroup.transvection
        ((show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne).symm 1 :=
    inv_eq_of_mul_eq_one_right hy2
  have hs : weylRep n F2 k * weylRep n F2 k = 1 := weylRep_mul_self n gf2_two k
  have hsinv : (weylRep n F2 k)⁻¹ = weylRep n F2 k := inv_eq_of_mul_eq_one_right hs
  rw [_root_.mul_inv_rev, hxinv, hyinv]
  calc weylRep n F2 k *
        (SpecialLinearGroup.transvection
          (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne 1 *
         SpecialLinearGroup.transvection
          ((show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne).symm 1) *
        weylRep n F2 k
      = weylRep n F2 k *
          (SpecialLinearGroup.transvection
            (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne 1 *
           SpecialLinearGroup.transvection
            ((show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne).symm 1) *
        (weylRep n F2 k)⁻¹ := by rw [hsinv]
    _ = (weylRep n F2 k * SpecialLinearGroup.transvection
            (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne 1 * (weylRep n F2 k)⁻¹) *
          (weylRep n F2 k * SpecialLinearGroup.transvection
            ((show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne).symm 1 *
            (weylRep n F2 k)⁻¹) := by group
    _ = (weylRep n F2 k * SpecialLinearGroup.transvection
            (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne 1 * weylRep n F2 k) *
          (weylRep n F2 k * SpecialLinearGroup.transvection
            ((show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne).symm 1 *
            weylRep n F2 k) := by rw [hsinv]
    _ = SpecialLinearGroup.transvection
          ((show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne).symm 1 *
        SpecialLinearGroup.transvection
          (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne 1 := by rw [hsx, hsy]

theorem halfTorus_comm {n : ℕ} {a b : SpecialLinearGroup (Fin (n + 1)) F2}
    (ha : a ∈ halfTorus n) (hb : b ∈ halfTorus n) : a * b = b * a := by
  have hgen : ({t : SpecialLinearGroup (Fin (n + 1)) F2 |
      ∃ k : Fin n, k.val % 2 = 0 ∧ t = omegaBlock n k}).Pairwise Commute := by
    intro x hx y hy _
    obtain ⟨k, hk, rfl⟩ := hx
    obtain ⟨k', hk', rfl⟩ := hy
    rw [commute_iff_eq]
    by_cases h : k = k'
    · subst h; rfl
    · rcases lt_or_gt_of_ne h with hlt | hgt
      · exact omegaBlock_comm (even_add_two_le_of_lt hk hk' hlt)
      · exact (omegaBlock_comm (k := k') (k' := k) (even_add_two_le_of_lt hk' hk hgt)).symm
  haveI : IsMulCommutative (halfTorus n) := Subgroup.isMulCommutative_closure hgen
  exact setLike_mul_comm ha hb

theorem halfTorus_pow_three {n : ℕ} {a : SpecialLinearGroup (Fin (n + 1)) F2}
    (ha : a ∈ halfTorus n) : a ^ 3 = 1 := by
  refine Subgroup.closure_induction (p := fun x _ => x ^ 3 = 1) ?_ ?_ ?_ ?_ ha
  · intro x hx
    obtain ⟨k, hk, rfl⟩ := hx
    exact omegaBlock_pow_three n k
  · exact one_pow 3
  · intro x y hx hy ihx ihy
    rw [Commute.mul_pow ((commute_iff_eq x y).mpr (halfTorus_comm hx hy)), ihx, ihy, one_mul]
  · intro x hx ihx
    rw [inv_pow, ihx, inv_one]

theorem halfTorusK_comm {n : ℕ} {a b : SpecialLinearGroup (Fin (n + 1)) F2}
    (ha : a ∈ halfTorusK n) (hb : b ∈ halfTorusK n) : a * b = b * a := by
  have hgen : ({t : SpecialLinearGroup (Fin (n + 1)) F2 |
      ∃ k : Fin n, (k.val + 1 = n ∨ (k.val % 2 = 0 ∧ k.val + 2 < n)) ∧
        t = omegaBlock n k}).Pairwise Commute := by
    intro x hx y hy _
    obtain ⟨k, hk, rfl⟩ := hx
    obtain ⟨k', hk', rfl⟩ := hy
    rw [commute_iff_eq]
    by_cases h : k = k'
    · subst h; rfl
    · rcases halfTorusK_index_sep hk hk' h with hle | hle
      · exact omegaBlock_comm hle
      · exact (omegaBlock_comm hle).symm
  haveI : IsMulCommutative (halfTorusK n) := Subgroup.isMulCommutative_closure hgen
  exact setLike_mul_comm ha hb

theorem halfTorusK_pow_three {n : ℕ} {a : SpecialLinearGroup (Fin (n + 1)) F2}
    (ha : a ∈ halfTorusK n) : a ^ 3 = 1 := by
  refine Subgroup.closure_induction (p := fun x _ => x ^ 3 = 1) ?_ ?_ ?_ ?_ ha
  · intro x hx
    obtain ⟨k, hk, rfl⟩ := hx
    exact omegaBlock_pow_three n k
  · exact one_pow 3
  · intro x y hx hy ihx ihy
    rw [Commute.mul_pow ((commute_iff_eq x y).mpr (halfTorusK_comm hx hy)), ihx, ihy, one_mul]
  · intro x hx ihx
    rw [inv_pow, ihx, inv_one]

private theorem two_mul_lt_of_lt_div {n i : ℕ} (h : i < (n + 1) / 2) : 2 * i < n := by omega

private noncomputable def cIdx (n : ℕ) (i : Fin ((n + 1) / 2)) : Fin n :=
  ⟨2 * i.val, two_mul_lt_of_lt_div i.isLt⟩

private theorem cIdx_val (n : ℕ) (i : Fin ((n + 1) / 2)) : (cIdx n i).val = 2 * i.val := rfl

private theorem cIdx_even (n : ℕ) (i : Fin ((n + 1) / 2)) : (cIdx n i).val % 2 = 0 := by
  rw [cIdx_val]; omega

private noncomputable def cG (n : ℕ) (i : Fin ((n + 1) / 2)) :
    SpecialLinearGroup (Fin (n + 1)) F2 := omegaBlock n (cIdx n i)

private theorem cG_mem (n : ℕ) (i : Fin ((n + 1) / 2)) : cG n i ∈ halfTorus n :=
  Subgroup.subset_closure ⟨cIdx n i, cIdx_even n i, rfl⟩

private theorem cG_pow_mem (n : ℕ) (i : Fin ((n + 1) / 2)) (k : ℕ) :
    (cG n i) ^ k ∈ halfTorus n := Subgroup.pow_mem _ (cG_mem n i) k

private noncomputable def zmodPowHom3 {G : Type*} [Group G] (g : G) (hg : g ^ 3 = 1) :
    Multiplicative (ZMod 3) →* G where
  toFun a := g ^ (Multiplicative.toAdd a).val
  map_one' := by simp
  map_mul' a b := by
    rw [toAdd_mul, ZMod.val_add, ← pow_add]
    conv_rhs => rw [← Nat.mod_add_div ((Multiplicative.toAdd a).val +
      (Multiplicative.toAdd b).val) 3, pow_add, pow_mul, hg, one_pow, mul_one]

private theorem zmodPowHom3_injective {G : Type*} [Group G] {g : G}
    (hgo : orderOf g = 3) (hg : g ^ 3 = 1) : Function.Injective (zmodPowHom3 g hg) := by
  intro x y h
  have h1 : g ^ (Multiplicative.toAdd x).val = g ^ (Multiplicative.toAdd y).val := h
  rw [pow_eq_pow_iff_modEq, hgo] at h1
  have h2 := (ZMod.natCast_eq_natCast_iff _ _ _).2 h1
  rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at h2
  exact Multiplicative.toAdd.injective h2

private noncomputable def cCoord (n : ℕ) (i : Fin ((n + 1) / 2)) :
    Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin (n + 1)) F2 :=
  zmodPowHom3 (cG n i) (omegaBlock_pow_three n (cIdx n i))

private theorem cCoord_apply (n : ℕ) (i : Fin ((n + 1) / 2))
    (a : Multiplicative (ZMod 3)) :
    cCoord n i a = (cG n i) ^ (Multiplicative.toAdd a).val := rfl

private theorem cCoord_commute (n : ℕ) :
    Pairwise fun i j : Fin ((n + 1) / 2) =>
      ∀ x y : Multiplicative (ZMod 3), Commute (cCoord n i x) (cCoord n j y) := by
  intro i j _ x y
  rw [cCoord_apply, cCoord_apply]
  exact (commute_iff_eq _ _).mpr
    (halfTorus_comm (cG_pow_mem n i (Multiplicative.toAdd x).val)
      (cG_pow_mem n j (Multiplicative.toAdd y).val))

private noncomputable def cPhi (n : ℕ) :
    (Fin ((n + 1) / 2) → Multiplicative (ZMod 3)) →*
      SpecialLinearGroup (Fin (n + 1)) F2 :=
  MonoidHom.noncommPiCoprod (cCoord n) (cCoord_commute n)

private theorem cPhi_range (n : ℕ) : (cPhi n).range = halfTorus n := by
  apply le_antisymm
  · rw [cPhi, MonoidHom.noncommPiCoprod_range]
    refine iSup_le fun i => ?_
    rintro _ ⟨a, rfl⟩
    rw [cCoord_apply]
    exact cG_pow_mem n i (Multiplicative.toAdd a).val
  · rw [halfTorus, Subgroup.closure_le]
    rintro t ⟨k, hk, rfl⟩
    rw [cPhi, MonoidHom.noncommPiCoprod_range]
    let i : Fin ((n + 1) / 2) := ⟨k.val / 2, by omega⟩
    have hik : cIdx n i = k := by
      apply Fin.ext
      rw [cIdx_val]
      show 2 * (k.val / 2) = k.val
      omega
    refine Subgroup.mem_iSup_of_mem i ?_
    refine ⟨Multiplicative.ofAdd (1 : ZMod 3), ?_⟩
    haveI : Fact (1 < 3) := ⟨by norm_num⟩
    rw [cCoord_apply, show omegaBlock n k = cG n i by rw [cG, hik], toAdd_ofAdd]
    change cG n i ^ (1 : ZMod 3).val = cG n i
    rw [ZMod.val_one 3, pow_one]

private noncomputable def cSep (n : ℕ) (i : Fin ((n + 1) / 2)) :
    SpecialLinearGroup (Fin (n + 1)) F2 :=
  SpecialLinearGroup.transvection
    (show (cIdx n i).castSucc < (cIdx n i).succ from Fin.castSucc_lt_succ).ne 1

private theorem transvection_commute_omegaBlock {n : ℕ} {k k' : Fin n}
    (hkk : k.val + 2 ≤ k'.val) :
    SpecialLinearGroup.transvection
        (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne 1 * omegaBlock n k' =
      omegaBlock n k' * SpecialLinearGroup.transvection
        (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne 1 := by
  rw [omegaBlock_eq_xy (n := n) (k := k')]
  have hij : k.castSucc ≠ k.succ := (Fin.castSucc_lt_succ).ne
  have hi'j' : k'.castSucc ≠ k'.succ := (Fin.castSucc_lt_succ).ne
  have hji' : k.succ ≠ k'.castSucc := by
    intro h; have := congrArg Fin.val h; simp only [Fin.val_succ, Fin.val_castSucc] at this; omega
  have hij' : k.castSucc ≠ k'.succ := by
    intro h; have := congrArg Fin.val h; simp only [Fin.val_succ, Fin.val_castSucc] at this; omega
  have hii' : k.castSucc ≠ k'.castSucc := by
    intro h; have := congrArg Fin.val h; simp only [Fin.val_castSucc] at this; omega
  have hjj' : k.succ ≠ k'.succ := by
    intro h; have := congrArg Fin.val h; simp only [Fin.val_succ] at this; omega
  have hxx : SpecialLinearGroup.transvection hij (1 : F2) *
        SpecialLinearGroup.transvection hi'j' (1 : F2) =
      SpecialLinearGroup.transvection hi'j' (1 : F2) * SpecialLinearGroup.transvection hij (1 : F2) :=
    transvection_commute hij hi'j' hji' hij' 1 1
  have hxy : SpecialLinearGroup.transvection hij (1 : F2) *
        SpecialLinearGroup.transvection hi'j'.symm (1 : F2) =
      SpecialLinearGroup.transvection hi'j'.symm (1 : F2) * SpecialLinearGroup.transvection hij (1 : F2) :=
    transvection_commute hij hi'j'.symm hjj' hii' 1 1
  calc SpecialLinearGroup.transvection hij (1 : F2) *
        (SpecialLinearGroup.transvection hi'j' (1 : F2) * SpecialLinearGroup.transvection hi'j'.symm (1 : F2))
      = (SpecialLinearGroup.transvection hij (1 : F2) * SpecialLinearGroup.transvection hi'j' (1 : F2)) *
          SpecialLinearGroup.transvection hi'j'.symm (1 : F2) := by group
    _ = (SpecialLinearGroup.transvection hi'j' (1 : F2) * SpecialLinearGroup.transvection hij (1 : F2)) *
          SpecialLinearGroup.transvection hi'j'.symm (1 : F2) := by rw [hxx]
    _ = SpecialLinearGroup.transvection hi'j' (1 : F2) *
          (SpecialLinearGroup.transvection hij (1 : F2) * SpecialLinearGroup.transvection hi'j'.symm (1 : F2)) := by
          group
    _ = SpecialLinearGroup.transvection hi'j' (1 : F2) *
          (SpecialLinearGroup.transvection hi'j'.symm (1 : F2) * SpecialLinearGroup.transvection hij (1 : F2)) := by
          rw [hxy]
    _ = (SpecialLinearGroup.transvection hi'j' (1 : F2) * SpecialLinearGroup.transvection hi'j'.symm (1 : F2)) *
          SpecialLinearGroup.transvection hij (1 : F2) := by group

private theorem omegaBlock_commute_transvection {n : ℕ} {k k' : Fin n}
    (hkk : k.val + 2 ≤ k'.val) :
    omegaBlock n k * SpecialLinearGroup.transvection
        (show k'.castSucc < k'.succ from Fin.castSucc_lt_succ).ne 1 =
      SpecialLinearGroup.transvection
        (show k'.castSucc < k'.succ from Fin.castSucc_lt_succ).ne 1 * omegaBlock n k := by
  rw [omegaBlock_eq_xy (n := n) (k := k)]
  have hij : k.castSucc ≠ k.succ := (Fin.castSucc_lt_succ).ne
  have hi'j' : k'.castSucc ≠ k'.succ := (Fin.castSucc_lt_succ).ne
  have hji' : k.succ ≠ k'.castSucc := by
    intro h; have := congrArg Fin.val h; simp only [Fin.val_succ, Fin.val_castSucc] at this; omega
  have hij' : k.castSucc ≠ k'.succ := by
    intro h; have := congrArg Fin.val h; simp only [Fin.val_succ, Fin.val_castSucc] at this; omega
  have hii' : k.castSucc ≠ k'.castSucc := by
    intro h; have := congrArg Fin.val h; simp only [Fin.val_castSucc] at this; omega
  have hjj' : k.succ ≠ k'.succ := by
    intro h; have := congrArg Fin.val h; simp only [Fin.val_succ] at this; omega
  have hxx : SpecialLinearGroup.transvection hij (1 : F2) *
        SpecialLinearGroup.transvection hi'j' (1 : F2) =
      SpecialLinearGroup.transvection hi'j' (1 : F2) * SpecialLinearGroup.transvection hij (1 : F2) :=
    transvection_commute hij hi'j' hji' hij' 1 1
  have hyy : SpecialLinearGroup.transvection hij.symm (1 : F2) *
        SpecialLinearGroup.transvection hi'j' (1 : F2) =
      SpecialLinearGroup.transvection hi'j' (1 : F2) * SpecialLinearGroup.transvection hij.symm (1 : F2) :=
    transvection_commute hij.symm hi'j' hii' hjj' 1 1
  calc (SpecialLinearGroup.transvection hij (1 : F2) * SpecialLinearGroup.transvection hij.symm (1 : F2)) *
        SpecialLinearGroup.transvection hi'j' (1 : F2)
      = SpecialLinearGroup.transvection hij (1 : F2) *
          (SpecialLinearGroup.transvection hij.symm (1 : F2) * SpecialLinearGroup.transvection hi'j' (1 : F2)) := by
          group
    _ = SpecialLinearGroup.transvection hij (1 : F2) *
          (SpecialLinearGroup.transvection hi'j' (1 : F2) * SpecialLinearGroup.transvection hij.symm (1 : F2)) := by
          rw [hyy]
    _ = (SpecialLinearGroup.transvection hij (1 : F2) * SpecialLinearGroup.transvection hi'j' (1 : F2)) *
          SpecialLinearGroup.transvection hij.symm (1 : F2) := by group
    _ = (SpecialLinearGroup.transvection hi'j' (1 : F2) * SpecialLinearGroup.transvection hij (1 : F2)) *
          SpecialLinearGroup.transvection hij.symm (1 : F2) := by rw [hxx]
    _ = SpecialLinearGroup.transvection hi'j' (1 : F2) *
          (SpecialLinearGroup.transvection hij (1 : F2) * SpecialLinearGroup.transvection hij.symm (1 : F2)) := by
          group

private theorem cSep_commute_cG {n : ℕ} {i j : Fin ((n + 1) / 2)} (hij : i ≠ j) :
    cSep n i * cG n j = cG n j * cSep n i := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact transvection_commute_omegaBlock (k := cIdx n i) (k' := cIdx n j)
      (by rw [cIdx_val, cIdx_val]; omega)
  · exact (omegaBlock_commute_transvection (k := cIdx n j) (k' := cIdx n i)
      (by rw [cIdx_val, cIdx_val]; omega)).symm

private theorem cSep_commute_pow {n : ℕ} {i j : Fin ((n + 1) / 2)} (hij : i ≠ j) (k : ℕ) :
    cSep n i * (cG n j) ^ k = (cG n j) ^ k * cSep n i := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc cSep n i * (cG n j) ^ (k + 1) = (cSep n i * (cG n j) ^ k) * cG n j := by
          rw [pow_succ]; group
      _ = ((cG n j) ^ k * cSep n i) * cG n j := by rw [ih]
      _ = (cG n j) ^ k * (cSep n i * cG n j) := by group
      _ = (cG n j) ^ k * (cG n j * cSep n i) := by rw [cSep_commute_cG hij]
      _ = ((cG n j) ^ k * cG n j) * cSep n i := by group
      _ = (cG n j) ^ (k + 1) * cSep n i := by rw [pow_succ]

private theorem transvection_braid {N : ℕ} {i j : Fin N} (hij : i ≠ j) :
    SpecialLinearGroup.transvection hij (1 : F2) *
        SpecialLinearGroup.transvection hij.symm (1 : F2) *
        SpecialLinearGroup.transvection hij (1 : F2) =
      SpecialLinearGroup.transvection hij.symm (1 : F2) *
        SpecialLinearGroup.transvection hij (1 : F2) *
        SpecialLinearGroup.transvection hij.symm (1 : F2) := by
  have h1 := slPerm_swap_eq_transvections gf2_two hij
  have h2 := slPerm_swap_eq_transvections gf2_two hij.symm
  rw [← h1, ← h2]
  exact congrArg (slPerm gf2_two) (Equiv.swap_comm i j)

private theorem xy_sq_of_braid {G : Type*} [Group G] {x y : G}
    (hbraid : x * y * x = y * x * y) (hy2 : y * y = 1) : (x * y) ^ 2 = y * x := by
  rw [pow_two]
  calc (x * y) * (x * y) = (x * y * x) * y := by group
    _ = (y * x * y) * y := by rw [hbraid]
    _ = y * x * (y * y) := by group
    _ = y * x := by rw [hy2, mul_one]

private theorem xy_eq_one_of_mul {G : Type*} [Group G] {x y : G} (hstep : y * x * y = y) :
    x * y = 1 := by
  have h2 : y * (x * y) = y := by
    calc y * (x * y) = y * x * y := by group
      _ = y := hstep
  exact mul_left_cancel (by rw [h2, mul_one])

private theorem xy_eq_one_of_commute_left {G : Type*} [Group G] {x y : G}
    (hbraid : x * y * x = y * x * y) (hx2 : x * x = 1) (hc : Commute (x * y) x) :
    x * y = 1 := by
  apply xy_eq_one_of_mul
  calc y * x * y = x * y * x := hbraid.symm
    _ = x * (x * y) := hc.eq
    _ = (x * x) * y := by group
    _ = y := by rw [hx2, one_mul]

private theorem xy_eq_one_of_commute_right {G : Type*} [Group G] {x y : G}
    (hbraid : x * y * x = y * x * y) (hx2 : x * x = 1) (hc : Commute (y * x) x) :
    x * y = 1 := by
  apply xy_eq_one_of_mul
  calc y * x * y = x * y * x := hbraid.symm
    _ = x * (y * x) := by group
    _ = (y * x) * x := hc.eq.symm
    _ = y := by rw [mul_assoc, hx2, mul_one]

private theorem transvection_not_commute_omegaBlock (n : ℕ) (k : Fin n) :
    ¬ Commute (omegaBlock n k)
      (SpecialLinearGroup.transvection (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne 1) := by
  intro hc
  rw [omegaBlock_eq_xy] at hc
  exact omegaBlock_ne_one n k (by
    rw [omegaBlock_eq_xy]
    exact xy_eq_one_of_commute_left (transvection_braid _) (transvection_self_mul _) hc)

private theorem transvection_not_commute_omegaBlock_sq (n : ℕ) (k : Fin n) :
    ¬ Commute ((omegaBlock n k) ^ 2)
      (SpecialLinearGroup.transvection (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne 1) := by
  intro hc
  rw [omegaBlock_eq_xy, xy_sq_of_braid (transvection_braid _) (transvection_self_mul _)] at hc
  exact omegaBlock_ne_one n k (by
    rw [omegaBlock_eq_xy]
    exact xy_eq_one_of_commute_right (transvection_braid _) (transvection_self_mul _) hc)

private theorem cPhi_iSupIndep (n : ℕ) :
    iSupIndep fun i : Fin ((n + 1) / 2) => (cCoord n i).range := by
  rw [iSupIndep_def]
  intro i
  rw [Subgroup.disjoint_def]
  intro x hx hx'
  obtain ⟨a, rfl⟩ := hx
  have hle : (⨆ (j : Fin ((n + 1) / 2)) (_ : j ≠ i), (cCoord n j).range) ≤
      Subgroup.centralizer ({cSep n i} : Set (SpecialLinearGroup (Fin (n + 1)) F2)) := by
    refine iSup₂_le fun j hj => ?_
    rintro _ ⟨b, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, cCoord_apply]
    exact (cSep_commute_pow (n := n) (i := i) (j := j) hj.symm
      (Multiplicative.toAdd b).val).symm
  have hc : cCoord n i a * cSep n i = cSep n i * cCoord n i a :=
    Subgroup.mem_centralizer_singleton_iff.mp (hle hx')
  rw [cCoord_apply] at hc
  have hlt : (Multiplicative.toAdd a).val < 3 := ZMod.val_lt _
  have hcases : (Multiplicative.toAdd a).val = 0 ∨ (Multiplicative.toAdd a).val = 1 ∨
      (Multiplicative.toAdd a).val = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · rw [cCoord_apply, h0, pow_zero]
  · rw [h1, pow_one] at hc
    exact (transvection_not_commute_omegaBlock n (cIdx n i) hc).elim
  · rw [h2] at hc
    exact (transvection_not_commute_omegaBlock_sq n (cIdx n i) hc).elim

private theorem cPhi_injective (n : ℕ) : Function.Injective (cPhi n) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [cPhi]
  refine MonoidHom.injective_noncommPiCoprod_of_iSupIndep
    (ϕ := cCoord n) (hcomm := cCoord_commute n) (cPhi_iSupIndep n) ?_
  intro i
  exact zmodPowHom3_injective
    (orderOf_eq_prime (omegaBlock_pow_three n (cIdx n i)) (omegaBlock_ne_one n (cIdx n i)))
    (omegaBlock_pow_three n (cIdx n i))

theorem card_halfTorus (n : ℕ) : Nat.card (halfTorus n) = 3 ^ ((n + 1) / 2) := by
  have hinj : Function.Injective (cPhi n) := cPhi_injective n
  have hrange : (cPhi n).range = halfTorus n := cPhi_range n
  have e : (Fin ((n + 1) / 2) → Multiplicative (ZMod 3)) ≃ (cPhi n).range :=
    Equiv.ofBijective
      (fun c => (⟨cPhi n c, MonoidHom.mem_range.mpr ⟨c, rfl⟩⟩ : (cPhi n).range))
      ⟨fun a b h => hinj (Subtype.ext_iff.mp h),
       fun y => by
         obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp y.2
         exact ⟨c, Subtype.ext hc⟩⟩
  rw [← hrange, (Nat.card_congr e).symm, Nat.card_eq_fintype_card, Fintype.card_fun,
    Fintype.card_multiplicative, ZMod.card, Fintype.card_fin]

end CFSG.StandardType.GGHalf

end
