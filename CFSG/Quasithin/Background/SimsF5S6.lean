module

public import CFSG.Quasithin.Background.SimsF5Stab
public import CFSG.Quasithin.Background.SimsF5Lin
public import CFSG.Permutation.SymmetricCoxeter

public section

namespace CFSG.Quasithin.SimsF5

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

noncomputable section

open Matrix

@[expose] def s6Mat : Fin 5 → Matrix (Fin 6) (Fin 6) (ZMod 3) :=
  ![!![0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0; 0, 0, 0, 0, 2, 0; 0, 0, 0, 2, 0, 0;
      0, 0, 0, 0, 0, 1],
    !![0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 0, 0; 0, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0;
      0, 0, 0, 0, 0, 1],
    !![0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0; 0, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0;
      0, 0, 0, 0, 0, 1],
    !![2, 0, 2, 1, 2, 0; 0, 2, 2, 1, 2, 0; 2, 2, 0, 1, 2, 0; 1, 1, 1, 0, 1, 0; 2, 2, 2, 1, 0, 0;
      0, 0, 0, 0, 0, 1],
    !![2, 0, 0, 0, 0, 0; 0, 2, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0;
      0, 0, 0, 0, 0, 1]]

theorem s6Mat_mul_self (i : Fin 5) : s6Mat i * s6Mat i = 1 := by
  revert i; decide +kernel

private theorem s6Mat_braid : ∀ i j : Fin 5, i.val + 1 = j.val →
    s6Mat i * s6Mat j * s6Mat i = s6Mat j * s6Mat i * s6Mat j := by
  decide +kernel

private theorem s6Mat_comm :
    ∀ i j : Fin 5, i.val + 2 ≤ j.val → s6Mat i * s6Mat j = s6Mat j * s6Mat i := by
  decide +kernel

@[expose] def s6Unit (i : Fin 5) : GL6 := ⟨s6Mat i, s6Mat i, s6Mat_mul_self i, s6Mat_mul_self i⟩

@[expose] def s6Gen (i : ℕ) : GL6 := if h : i < 5 then s6Unit ⟨i, h⟩ else 1

theorem s6Gen_of_lt {i : ℕ} (hi : i < 5) : s6Gen i = s6Unit ⟨i, hi⟩ := dif_pos hi

private theorem s6Gen_val {i : ℕ} (hi : i < 5) :
    ((s6Gen i : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) = s6Mat ⟨i, hi⟩ := by
  rw [s6Gen_of_lt hi]; rfl

theorem isCoxeterA_s6Gen : CFSG.Permutation.SymmetricCoxeter.IsCoxeterA 5 s6Gen where
  sq i hi := by
    apply Units.ext
    rw [Units.val_mul, s6Gen_val hi, Units.val_one]
    exact s6Mat_mul_self ⟨i, hi⟩
  braid i hi := by
    apply Units.ext
    simp only [Units.val_mul]
    rw [s6Gen_val (by omega), s6Gen_val hi]
    exact s6Mat_braid ⟨i, by omega⟩ ⟨i + 1, hi⟩ rfl
  comm i j hij hj := by
    apply Units.ext
    simp only [Units.val_mul]
    rw [s6Gen_val (by omega), s6Gen_val hj]
    exact s6Mat_comm ⟨i, by omega⟩ ⟨j, hj⟩ hij

theorem s6_mem_DDot_iff {g : GL6} : g ∈ DDot ↔ g ∈ GDot ∧ g * fDot = fDot * g := by
  rw [DDot, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]

@[expose] def s6W : Fin 5 → V6 :=
  ![![0, 0, 0, 1, 1, 0], ![0, 0, 1, 0, 2, 0], ![0, 0, 0, 2, 1, 0], ![1, 1, 1, 2, 1, 0],
    ![1, 1, 0, 0, 0, 0]]

private theorem qV_s6W (i : Fin 5) : qV (s6W i) = -1 := by
  revert i; decide

private theorem qV_s6_d : qV (x1 - x2) = -1 := by decide

private theorem qV_s6W_ne_zero (i : Fin 5) : qV (s6W i) ≠ 0 := by
  rw [qV_s6W]; decide

private theorem inv_neg_one_zmod3 : ((-1 : ZMod 3))⁻¹ = -1 :=
  inv_eq_of_mul_eq_one_right (by decide)

private theorem reflM_of_qV_neg_one {z : V6} (hz : qV z = -1) :
    reflM z = 1 + Matrix.vecMulVec z (wv z) := by
  unfold reflM
  rw [hz, inv_neg_one_zmod3, neg_smul, one_smul, sub_neg_eq_add]

private theorem s6Mat_eq_prod : ∀ i : Fin 5, s6Mat i =
    (1 + Matrix.vecMulVec (s6W i) (wv (s6W i))) *
      (1 + Matrix.vecMulVec (x1 - x2) (wv (x1 - x2))) := by
  decide +kernel

private theorem s6Unit_eq_refl (i : Fin 5) :
    s6Unit i = refl6 (s6W i) (qV_s6W_ne_zero i) * refl6 (x1 - x2) qV_x1_sub_x2_ne_zero := by
  apply Units.ext
  rw [Units.val_mul, refl6_val, refl6_val, reflM_of_qV_neg_one (qV_s6W i),
    reflM_of_qV_neg_one qV_s6_d]
  exact s6Mat_eq_prod i

theorem s6Unit_mem_MDot (i : Fin 5) : s6Unit i ∈ MDot := by
  have h := (prod_refl_mem_MDot_iff [⟨s6W i, qV_s6W_ne_zero i⟩,
    ⟨x1 - x2, qV_x1_sub_x2_ne_zero⟩]).2 ⟨⟨1, rfl⟩, ?_⟩
  · rw [s6Unit_eq_refl]
    simpa [reflOf] using h
  · simp [List.countP_cons, qV_s6W, qV_s6_d]

private theorem s6Mat_mulVec_x6 : ∀ i : Fin 5, s6Mat i *ᵥ x6 = x6 := by
  decide +kernel

private theorem s6Mat_comm_fMat : ∀ i : Fin 5, s6Mat i * fMat = fMat * s6Mat i := by
  decide +kernel

theorem s6Unit_mem_DDot (i : Fin 5) : s6Unit i ∈ DDot :=
  s6_mem_DDot_iff.2 ⟨mem_GDot_iff.2 ⟨s6Unit_mem_MDot i, s6Mat_mulVec_x6 i⟩,
    Units.ext (s6Mat_comm_fMat i)⟩

theorem s6Gen_mem_DDot (i : ℕ) (hi : i < 5) : s6Gen i ∈ DDot := by
  rw [s6Gen_of_lt hi]; exact s6Unit_mem_DDot _

@[expose] def s6Hom : Equiv.Perm (Fin 6) →* GL6 :=
  (CFSG.Permutation.SymmetricCoxeter.exists_hom_perm 5 s6Gen isCoxeterA_s6Gen).choose

theorem s6Hom_adjSwap {i : ℕ} (hi : i < 5) :
    s6Hom (CFSG.Permutation.SymmetricCoxeter.adjSwap 5 i) = s6Gen i :=
  (CFSG.Permutation.SymmetricCoxeter.exists_hom_perm 5 s6Gen isCoxeterA_s6Gen).choose_spec i hi

private theorem s6Mat_zero_mul_one_ne : s6Mat 0 * s6Mat 1 ≠ 1 := by
  decide +kernel

private theorem isSwap_adjSwap_five {i : ℕ} (hi : i < 5) :
    (CFSG.Permutation.SymmetricCoxeter.adjSwap 5 i).IsSwap :=
  ⟨⟨i, by omega⟩, ⟨i + 1, by omega⟩, fun h => by simpa using congrArg Fin.val h,
    CFSG.Permutation.SymmetricCoxeter.adjSwap_of_lt hi⟩

theorem s6Hom_injective : Function.Injective s6Hom := by
  rw [← MonoidHom.ker_eq_bot_iff]
  by_contra hne
  haveI : Nontrivial s6Hom.ker := (Subgroup.nontrivial_iff_ne_bot _).2 hne
  have hA : alternatingGroup (Fin 6) ≤ s6Hom.ker :=
    Equiv.Perm.alternatingGroup_le_of_normal (α := Fin 6) (by simp) this
  have hmem := hA (Equiv.Perm.mul_mem_alternatingGroup_of_isSwap (isSwap_adjSwap_five (i := 0)
    (by omega)) (isSwap_adjSwap_five (i := 1) (by omega)))
  rw [MonoidHom.mem_ker, map_mul, s6Hom_adjSwap (by omega), s6Hom_adjSwap (by omega)] at hmem
  apply s6Mat_zero_mul_one_ne
  have h := congrArg (fun g : GL6 => (g : Matrix (Fin 6) (Fin 6) (ZMod 3))) hmem
  simpa [Units.val_mul, s6Gen_val] using h

theorem s6Hom_range_le : s6Hom.range ≤ DDot := by
  rw [MonoidHom.range_eq_map, ← CFSG.Permutation.SymmetricCoxeter.closure_adjSwap 5,
    MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨_, ⟨i, hi, rfl⟩, rfl⟩
  rw [s6Hom_adjSwap hi]
  exact s6Gen_mem_DDot i hi

private theorem s6_exists_orth : ∀ b : V6, b 5 = 0 → qV b = -1 → ∀ t : ZMod 3, t ≠ 0 →
    ∃ u : V6, u 5 = 0 ∧ bil u b = 0 ∧ qV u = t := by
  decide +kernel

private theorem s6_exists_GDot_mulVec {a b : V6} (ha5 : a 5 = 0) (hb5 : b 5 = 0) (ha : qV a = -1)
    (hb : qV b = -1) :
    ∃ g ∈ GDot, (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ a = b := by
  by_cases hab : a = b
  · exact ⟨1, GDot.one_mem, by rw [hab, Units.val_one, Matrix.one_mulVec]⟩
  have hsum : qV (a - b) + qV (a + b) = -1 := by
    rw [qV_sub, qV_add, ha, hb]
    generalize bil a b = t
    revert t; decide
  have h_sub : bil a (a - b) = qV (a - b) := by
    rw [bil_sub_right, bil_self, qV_sub, ha, hb]; ring
  have h_add : bil a (a + b) = qV (a + b) := by
    rw [bil_add_right, bil_self, qV_add, ha, hb]; ring
  have hb0 : qV b ≠ 0 := by rw [hb]; decide
  have hd5 : (a - b) 5 = 0 := by simp [ha5, hb5]
  have hs5 : (a + b) 5 = 0 := by simp [ha5, hb5]
  by_cases hd0 : qV (a - b) = 0
  · have hs : qV (a + b) = -1 := by
      rw [hd0, zero_add] at hsum; exact hsum
    have hs0 : qV (a + b) ≠ 0 := by rw [hs]; decide
    refine ⟨refl6 b hb0 * refl6 (a + b) hs0, ?_, ?_⟩
    · refine mem_GDot_iff.2 ⟨refl6_mul_refl6_mem_MDot b (a + b) hb0 hs0 (hb.trans hs.symm), ?_⟩
      rw [Units.val_mul, ← Matrix.mulVec_mulVec, refl6_mulVec_x6_of_last _ hs0 hs5,
        refl6_mulVec_x6_of_last b hb0 hb5]
    · rw [Units.val_mul, ← Matrix.mulVec_mulVec, refl6_mulVec (a + b) a hs0, h_add,
        inv_mul_cancel₀ hs0, one_smul, sub_add_cancel_left, Matrix.mulVec_neg,
        refl6_mulVec_self b hb0, neg_neg]
  · obtain ⟨u, hu5, hub, hqu⟩ := s6_exists_orth b hb5 hb _ hd0
    have hu0 : qV u ≠ 0 := by rw [hqu]; exact hd0
    refine ⟨refl6 u hu0 * refl6 (a - b) hd0, ?_, ?_⟩
    · refine mem_GDot_iff.2 ⟨refl6_mul_refl6_mem_MDot u (a - b) hu0 hd0 hqu, ?_⟩
      rw [Units.val_mul, ← Matrix.mulVec_mulVec, refl6_mulVec_x6_of_last _ hd0 hd5,
        refl6_mulVec_x6_of_last u hu0 hu5]
    · rw [Units.val_mul, ← Matrix.mulVec_mulVec, refl6_mulVec (a - b) a hd0, h_sub,
        inv_mul_cancel₀ hd0, one_smul, sub_sub_cancel, refl6_mulVec, bil_comm b u, hub, mul_zero,
        zero_smul, sub_zero]

private theorem s6_orbit_eq :
    MulAction.orbit ↥GDot (x1 - x2) = {v : V6 | v 5 = 0 ∧ qV v = -1} := by
  ext v
  constructor
  · rintro ⟨g, rfl⟩
    have hg : (g : GL6) ∈ MDot := g.2.1
    have h6 := (mem_GDot_iff.1 g.2).2
    refine ⟨?_, ?_⟩
    · have h1 := bil_mulVec_of_mem_OVq (MDot_le_OVq hg) (x1 - x2) x6
      rw [h6, bil_x6, bil_x6] at h1
      exact h1.trans (by decide)
    · show qV ((g : GL6) • (x1 - x2)) = -1
      rw [qV_smul_of_mem_MDot hg, qV_s6_d]
  · rintro ⟨hv5, hv⟩
    obtain ⟨g, hg, hgv⟩ := s6_exists_GDot_mulVec (a := x1 - x2) (b := v) (by decide) hv5
      qV_s6_d hv
    exact ⟨⟨g, hg⟩, hgv⟩

private theorem card_s6X : Nat.card {v : V6 // v 5 = 0 ∧ qV v = -1} = 72 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

private def s6StabEquiv : MulAction.stabilizer ↥GDot (x1 - x2) ≃ ↥CGDot12 where
  toFun g := ⟨g.1.1, g.1.2, g.2⟩
  invFun g := ⟨⟨g.1, g.2.1⟩, g.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem s6_card_GDot : Nat.card ↥GDot = 72 * Nat.card ↥CGDot12 := by
  rw [← Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup ↥GDot (x1 - x2)), Nat.card_prod,
    Nat.card_congr s6StabEquiv, s6_orbit_eq]
  exact congrArg (· * _) card_s6X

theorem card_CGDot12 : Nat.card ↥CGDot12 = 360 := by
  have h := s6_card_GDot
  rw [card_GDot] at h
  omega

private theorem s6_fMat_mulVec_d : fMat *ᵥ (x1 - x2) = -(x1 - x2) := by
  decide +kernel

private theorem s6_eigen : ∀ e : V6, fMat *ᵥ e = -e → e 5 = 0 → qV e = -1 →
    e = x1 - x2 ∨ e = -(x1 - x2) := by
  decide +kernel

theorem s6_DDot_mulVec {g : GL6} (hg : g ∈ DDot) :
    (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ (x1 - x2) = x1 - x2 ∨
      (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ (x1 - x2) = -(x1 - x2) := by
  obtain ⟨hgG, hgf⟩ := s6_mem_DDot_iff.1 hg
  have hgf' : (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) * fMat = fMat * (g : Matrix _ _ _) :=
    congrArg Units.val hgf
  obtain ⟨hgM, hg6⟩ := mem_GDot_iff.1 hgG
  have hgO : g ∈ OVq := MDot_le_OVq hgM
  refine s6_eigen _ ?_ ?_ ?_
  · rw [Matrix.mulVec_mulVec, ← hgf', ← Matrix.mulVec_mulVec, s6_fMat_mulVec_d,
      Matrix.mulVec_neg]
  · have h1 := bil_mulVec_of_mem_OVq hgO (x1 - x2) x6
    rw [hg6, bil_x6, bil_x6] at h1
    exact h1.trans (by decide)
  · rw [qV_mulVec_of_mem_OVq hgO, qV_s6_d]

private theorem s6_zDot_mulVec_d :
    ((zDot : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ (x1 - x2) = -(x1 - x2) := by
  decide +kernel

private theorem s6_zDot_comm_fDot : zDot * fDot = fDot * zDot :=
  Units.ext (by decide +kernel)

theorem s6_zDot_mem_DDot : zDot ∈ DDot :=
  s6_mem_DDot_iff.2 ⟨zDot_mem_GDot, s6_zDot_comm_fDot⟩

private theorem s6_comm_refl6 {g : GL6} (hg : g ∈ OVq) (z : V6) (hz : qV z ≠ 0)
    (hgz : (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ z = z) :
    g * refl6 z hz = refl6 z hz * g := by
  have h := conj_refl6 hg z hz
  have h2 : refl6 ((g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ z)
      (by rw [qV_mulVec_of_mem_OVq hg]; exact hz) = refl6 z hz := by
    apply Units.ext
    rw [refl6_val, refl6_val, hgz]
  rw [h2] at h
  exact mul_inv_eq_iff_eq_mul.1 h

theorem s6_CGDot12_le_DDot : CGDot12 ≤ DDot := by
  intro g hg
  refine s6_mem_DDot_iff.2 ⟨hg.1, ?_⟩
  have hgO : g ∈ OVq := MDot_le_OVq (mem_GDot_iff.1 hg.1).1
  have h6 := (mem_GDot_iff.1 hg.1).2
  have h12 : (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ (x1 - x2) = x1 - x2 := hg.2
  have hA := s6_comm_refl6 hgO (x1 - x2) qV_x1_sub_x2_ne_zero h12
  have hB := s6_comm_refl6 hgO x6 qV_x6_ne_zero h6
  rw [fDot_eq_refl6_mul]
  calc g * (refl6 (x1 - x2) qV_x1_sub_x2_ne_zero * refl6 x6 qV_x6_ne_zero)
      = (g * refl6 (x1 - x2) qV_x1_sub_x2_ne_zero) * refl6 x6 qV_x6_ne_zero :=
        (mul_assoc _ _ _).symm
    _ = (refl6 (x1 - x2) qV_x1_sub_x2_ne_zero * g) * refl6 x6 qV_x6_ne_zero := by rw [hA]
    _ = refl6 (x1 - x2) qV_x1_sub_x2_ne_zero * (g * refl6 x6 qV_x6_ne_zero) := mul_assoc _ _ _
    _ = refl6 (x1 - x2) qV_x1_sub_x2_ne_zero * (refl6 x6 qV_x6_ne_zero * g) := by rw [hB]
    _ = (refl6 (x1 - x2) qV_x1_sub_x2_ne_zero * refl6 x6 qV_x6_ne_zero) * g :=
        (mul_assoc _ _ _).symm

theorem s6_index_CGDot12_subgroupOf_DDot : (CGDot12.subgroupOf DDot).index = 2 := by
  rw [Subgroup.index_eq_two_iff]
  refine ⟨⟨zDot, s6_zDot_mem_DDot⟩, fun b => ?_⟩
  have hd : x1 - x2 ≠ -(x1 - x2) := by decide
  have e1 : (b : GL6) ∈ CGDot12 ↔
      ((b : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ (x1 - x2) = x1 - x2 :=
    ⟨fun h => h.2, fun h => ⟨b.2.1, h⟩⟩
  have e2 : (b : GL6) * zDot ∈ CGDot12 ↔
      ((b : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ (x1 - x2) = -(x1 - x2) := by
    constructor
    · intro h
      have h' : (((b : GL6) * zDot : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ (x1 - x2) =
          x1 - x2 := h.2
      rw [Units.val_mul, ← Matrix.mulVec_mulVec, s6_zDot_mulVec_d, Matrix.mulVec_neg] at h'
      exact neg_eq_iff_eq_neg.1 h'
    · intro h
      refine ⟨GDot.mul_mem b.2.1 zDot_mem_GDot, ?_⟩
      show (((b : GL6) * zDot : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ (x1 - x2) = x1 - x2
      rw [Units.val_mul, ← Matrix.mulVec_mulVec, s6_zDot_mulVec_d, Matrix.mulVec_neg, h, neg_neg]
  show Xor' ((b : GL6) * zDot ∈ CGDot12) ((b : GL6) ∈ CGDot12)
  rw [e1, e2]
  rcases s6_DDot_mulVec b.2 with h | h
  · exact Or.inr ⟨h, fun h' => hd (h.symm.trans h')⟩
  · exact Or.inl ⟨h, fun h' => hd (h'.symm.trans h)⟩

theorem card_DDot : Nat.card ↥DDot = 720 := by
  have h := Subgroup.card_mul_index (CGDot12.subgroupOf DDot)
  rw [s6_index_CGDot12_subgroupOf_DDot,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe s6_CGDot12_le_DDot).toEquiv, card_CGDot12] at h
  omega

theorem DDot_eq : DDot = CGDot12 ⊔ Subgroup.zpowers zDot := by
  apply le_antisymm
  · intro g hg
    rcases s6_DDot_mulVec hg with h | h
    · exact Subgroup.mem_sup_left ⟨hg.1, h⟩
    · have hgz : g * zDot ∈ CGDot12 := by
        refine ⟨GDot.mul_mem hg.1 zDot_mem_GDot, ?_⟩
        show ((g * zDot : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ (x1 - x2) = x1 - x2
        rw [Units.val_mul, ← Matrix.mulVec_mulVec, s6_zDot_mulVec_d, Matrix.mulVec_neg, h, neg_neg]
      have := Subgroup.mul_mem_sup hgz (Subgroup.inv_mem _ (Subgroup.mem_zpowers zDot))
      rwa [mul_inv_cancel_right] at this
  · exact sup_le s6_CGDot12_le_DDot ((Subgroup.zpowers_le).2 s6_zDot_mem_DDot)

theorem s6Hom_range_eq : s6Hom.range = DDot := by
  apply Subgroup.eq_of_le_of_card_ge s6Hom_range_le
  rw [card_DDot, ← Nat.card_congr (MonoidHom.ofInjective s6Hom_injective).toEquiv,
    Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  rfl

@[expose] def DDotEquivS6 : ↥DDot ≃* Equiv.Perm (Fin 6) :=
  (MulEquiv.subgroupCongr s6Hom_range_eq.symm).trans (MonoidHom.ofInjective s6Hom_injective).symm

theorem s6_CGDot12_eq_map_alternatingGroup :
    CGDot12 = (alternatingGroup (Fin 6)).map s6Hom := by
  have h1 : (CGDot12.comap s6Hom).index = 2 := by
    rw [Subgroup.index_comap, s6Hom_range_eq]
    exact s6_index_CGDot12_subgroupOf_DDot
  rw [← Equiv.Perm.eq_alternatingGroup_of_index_eq_two h1, Subgroup.map_comap_eq,
    s6Hom_range_eq]
  exact (inf_eq_right.2 s6_CGDot12_le_DDot).symm

theorem s6_commutator_CGDot12 : ⁅CGDot12, CGDot12⁆ = CGDot12 := by
  rw [s6_CGDot12_eq_map_alternatingGroup, ← Subgroup.map_commutator,
    commutator_alternatingGroup_eq_self (by simp)]

@[expose] def s6C : Subgroup GL6 :=
  OVq ⊓ MulAction.stabilizer GL6 x6 ⊓ MulAction.stabilizer GL6 (x1 - x2)

theorem s6C_le_OVq : s6C ≤ OVq := fun _ hg => hg.1.1

theorem CGDot12_le_s6C : CGDot12 ≤ s6C := fun _ hg =>
  ⟨⟨MDot_le_OVq hg.1.1, hg.1.2⟩, hg.2⟩

theorem commutator_s6C_le : ⁅s6C, s6C⁆ ≤ CGDot12 := by
  have h1 : ⁅s6C, s6C⁆ ≤ MDot := Subgroup.commutator_mono s6C_le_OVq s6C_le_OVq
  intro g hg
  have hgC : g ∈ s6C := commutator_le_self' _ hg
  exact ⟨⟨h1 hg, hgC.1.2⟩, hgC.2⟩

theorem commutator_s6C : ⁅s6C, s6C⁆ = CGDot12 := by
  apply le_antisymm commutator_s6C_le
  calc CGDot12 = ⁅CGDot12, CGDot12⁆ := s6_commutator_CGDot12.symm
    _ ≤ ⁅s6C, s6C⁆ := Subgroup.commutator_mono CGDot12_le_s6C CGDot12_le_s6C

private def s6E : Matrix (Fin 6) (Fin 4) (ZMod 3) :=
  !![1, 0, 0, 0; 1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1; 0, 0, 0, 0]

private def s6M : Matrix (Fin 4) (Fin 6) (ZMod 3) :=
  !![2, 2, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0]

private theorem s6M_mul_E : s6M * s6E = 1 := by decide +kernel

private theorem s6E_col : ∀ (j : Fin 4) (k : Fin 6), bvec j k = s6E k j := by decide +kernel

private theorem s6E_bidx : ∀ i k : Fin 4, s6E (bidx i) k = if i = k then 1 else 0 := by
  decide +kernel

private theorem s6_blk4_apply (g : GL6) (i j : Fin 4) :
    blk4 g i j = ((g : Matrix (Fin 6) (Fin 6) (ZMod 3)) * s6E) (bidx i) j := by
  have h : bvec j = fun l => s6E l j := funext fun l => s6E_col j l
  show ((g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ bvec j) (bidx i) = _
  rw [h, Matrix.mul_apply]
  rfl

private theorem s6_blk4_of_mul_E {g : GL6} {B : Matrix (Fin 4) (Fin 4) (ZMod 3)}
    (h : (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) * s6E = s6E * B) : blk4 g = B := by
  ext i j
  rw [s6_blk4_apply, h, Matrix.mul_apply]
  simp only [s6E_bidx, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

private theorem s6_decomp : ∀ y : V6, y 1 = y 0 → y 5 = 0 →
    y = s6E *ᵥ (fun i => y (bidx i)) := by
  decide +kernel

private theorem s6_bil_d : ∀ y : V6, bil y (x1 - x2) = 2 * (y 0 - y 1) := by
  decide +kernel

private theorem s6_E_prop : ∀ c : Fin 4 → ZMod 3,
    (s6E *ᵥ c) 5 = 0 ∧ (s6E *ᵥ c) 1 = (s6E *ᵥ c) 0 := by
  decide +kernel

private theorem s6_apply_E {g : GL6} (hg : g ∈ s6C) (c : Fin 4 → ZMod 3) :
    (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ (s6E *ᵥ c) = s6E *ᵥ (blk4 g *ᵥ c) := by
  have hO : g ∈ OVq := hg.1.1
  have h6 : (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ x6 = x6 := hg.1.2
  have h12 : (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ (x1 - x2) = x1 - x2 := hg.2
  obtain ⟨hw5, hw10⟩ := s6_E_prop c
  have hy5 : ((g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ (s6E *ᵥ c)) 5 = 0 := by
    have h1 := bil_mulVec_of_mem_OVq hO (s6E *ᵥ c) x6
    rw [h6, bil_x6, bil_x6, hw5] at h1
    exact h1
  have hy10 : ((g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ (s6E *ᵥ c)) 1 =
      ((g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ (s6E *ᵥ c)) 0 := by
    have h1 := bil_mulVec_of_mem_OVq hO (s6E *ᵥ c) (x1 - x2)
    rw [h12, s6_bil_d, s6_bil_d, hw10, sub_self, mul_zero] at h1
    have h2 := (by decide : ∀ t : ZMod 3, 2 * t = 0 → t = 0) _ h1
    exact (sub_eq_zero.1 h2).symm
  have hcoord : (fun i => ((g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ (s6E *ᵥ c)) (bidx i)) =
      blk4 g *ᵥ c := by
    funext i
    rw [Matrix.mulVec_mulVec]
    simp only [Matrix.mulVec, dotProduct, s6_blk4_apply]
  rw [← hcoord]
  exact s6_decomp _ hy10 hy5

private theorem s6_bvec_bidx : ∀ i j : Fin 4, bvec j (bidx i) = if i = j then 1 else 0 := by
  decide +kernel

private theorem s6_blk4_one : blk4 1 = 1 := by
  ext i j
  simp only [blk4, Matrix.of_apply, Units.val_one, Matrix.one_mulVec, Matrix.one_apply,
    s6_bvec_bidx]

private theorem s6_blk4_mul {g h : GL6} (hh : h ∈ s6C) : blk4 (g * h) = blk4 g * blk4 h :=
  blk4_mul g h (preserves_V4minus h hh.1.1 hh.1.2 hh.2)

private def s6BlkHom : ↥s6C →* GL (Fin 4) (ZMod 3) where
  toFun g := ⟨blk4 g.1, blk4 g.1⁻¹,
    by rw [← s6_blk4_mul (s6C.inv_mem g.2), mul_inv_cancel, s6_blk4_one],
    by rw [← s6_blk4_mul g.2, inv_mul_cancel, s6_blk4_one]⟩
  map_one' := Units.ext s6_blk4_one
  map_mul' g h := Units.ext (s6_blk4_mul h.2)

private theorem s6_qV4m_eq : ∀ c : Fin 4 → ZMod 3, qV4m c = qV (s6E *ᵥ c) := by
  decide +kernel

private theorem s6BlkHom_mem (g : ↥s6C) :
    s6BlkHom g ∈ CFSG.MatrixModel.isometryCore qV4m := by
  refine Subgroup.subset_closure fun c => ?_
  show qV4m (blk4 g.1 *ᵥ c) = qV4m c
  rw [s6_qV4m_eq (blk4 g.1 *ᵥ c), ← s6_apply_E g.2, qV_mulVec_of_mem_OVq g.2.1.1,
    ← s6_qV4m_eq]

private def s6Gmat (A : Matrix (Fin 4) (Fin 4) (ZMod 3)) : Matrix (Fin 6) (Fin 6) (ZMod 3) :=
  1 + s6E * (A - 1) * s6M

private theorem s6M_mul_E_mul (Z : Matrix (Fin 4) (Fin 6) (ZMod 3)) : s6M * (s6E * Z) = Z := by
  rw [← Matrix.mul_assoc, s6M_mul_E, Matrix.one_mul]

private theorem s6Gmat_one : s6Gmat 1 = 1 := by
  simp [s6Gmat]

private theorem s6Gmat_mul (A B : Matrix (Fin 4) (Fin 4) (ZMod 3)) :
    s6Gmat A * s6Gmat B = s6Gmat (A * B) := by
  have hAB : (A - 1) + (B - 1) + (A - 1) * (B - 1) = A * B - 1 := by noncomm_ring
  unfold s6Gmat
  rw [← hAB]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc,
    s6M_mul_E_mul]
  abel

private theorem s6M_mul_Gmat (A : Matrix (Fin 4) (Fin 4) (ZMod 3)) :
    s6M * s6Gmat A = A * s6M := by
  unfold s6Gmat
  simp only [Matrix.mul_add, Matrix.mul_one, Matrix.mul_assoc, s6M_mul_E_mul, Matrix.sub_mul,
    Matrix.one_mul]
  abel

private theorem s6Gmat_mul_E (A : Matrix (Fin 4) (Fin 4) (ZMod 3)) :
    s6Gmat A * s6E = s6E * A := by
  unfold s6Gmat
  simp only [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, s6M_mul_E, Matrix.mul_one,
    Matrix.mul_sub]
  abel

private theorem s6Gmat_mulVec (A : Matrix (Fin 4) (Fin 4) (ZMod 3)) (v : V6) :
    s6Gmat A *ᵥ v = v + s6E *ᵥ ((A - 1) *ᵥ (s6M *ᵥ v)) := by
  unfold s6Gmat
  rw [Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

private def s6Ext (U : GL (Fin 4) (ZMod 3)) : GL6 :=
  ⟨s6Gmat U, s6Gmat ((U⁻¹ : GL (Fin 4) (ZMod 3)) : Matrix (Fin 4) (Fin 4) (ZMod 3)),
    by rw [s6Gmat_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, s6Gmat_one],
    by rw [s6Gmat_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, s6Gmat_one]⟩

private theorem s6M_mulVec_x6 : s6M *ᵥ x6 = 0 := by decide +kernel

private theorem s6M_mulVec_d : s6M *ᵥ (x1 - x2) = 0 := by decide +kernel

private theorem s6_qV_decomp : ∀ v : V6,
    qV v = qV4m (s6M *ᵥ v) - (2 * (v 0 - v 1)) ^ 2 - v 5 ^ 2 := by
  decide +kernel

private theorem s6Ext_mem {U : GL (Fin 4) (ZMod 3)}
    (hU : ∀ c, qV4m ((U : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ c) = qV4m c) : s6Ext U ∈ s6C := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · refine mem_OVq_iff_forall.2 fun v => ?_
    show qV (s6Gmat U *ᵥ v) = qV v
    have h1 : s6M *ᵥ (s6Gmat U *ᵥ v) = (U : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ (s6M *ᵥ v) := by
      rw [Matrix.mulVec_mulVec, s6M_mul_Gmat, ← Matrix.mulVec_mulVec]
    obtain ⟨h5, h10⟩ := s6_E_prop ((↑U - 1 : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ (s6M *ᵥ v))
    have h2 : (s6Gmat U *ᵥ v) 0 - (s6Gmat U *ᵥ v) 1 = v 0 - v 1 := by
      rw [s6Gmat_mulVec]
      simp only [Pi.add_apply, h10]
      ring
    have h3 : (s6Gmat U *ᵥ v) 5 = v 5 := by
      rw [s6Gmat_mulVec]
      simp only [Pi.add_apply, h5, add_zero]
    rw [s6_qV_decomp (s6Gmat U *ᵥ v), s6_qV_decomp v, h1, h2, h3, hU]
  · show ((s6Gmat U : Matrix (Fin 6) (Fin 6) (ZMod 3))) *ᵥ x6 = x6
    rw [s6Gmat_mulVec, s6M_mulVec_x6, Matrix.mulVec_zero, Matrix.mulVec_zero, add_zero]
  · show ((s6Gmat U : Matrix (Fin 6) (Fin 6) (ZMod 3))) *ᵥ (x1 - x2) = x1 - x2
    rw [s6Gmat_mulVec, s6M_mulVec_d, Matrix.mulVec_zero, Matrix.mulVec_zero, add_zero]

private theorem s6_blk4_ext (U : GL (Fin 4) (ZMod 3)) : blk4 (s6Ext U) = U :=
  s6_blk4_of_mul_E (s6Gmat_mul_E U)

private theorem s6_isometry_of_mem {A : GL (Fin 4) (ZMod 3)}
    (hA : A ∈ CFSG.MatrixModel.isometryCore qV4m) :
    ∀ c, qV4m ((A : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ c) = qV4m c := by
  unfold CFSG.MatrixModel.isometryCore at hA
  induction hA using Subgroup.closure_induction with
  | mem x hx => exact fun v => hx v
  | one => intro v; simp
  | mul x y _ _ hx hy =>
    intro v
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hx, hy]
  | inv x _ hx =>
    intro v
    have h1 : (x : Matrix (Fin 4) (Fin 4) (ZMod 3)) *
        ((x⁻¹ : GL (Fin 4) (ZMod 3)) : Matrix (Fin 4) (Fin 4) (ZMod 3)) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have h := hx (((x⁻¹ : GL (Fin 4) (ZMod 3)) : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ v)
    rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec] at h
    exact h.symm

private theorem s6BlkHom_range : s6BlkHom.range = CFSG.MatrixModel.isometryCore qV4m := by
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    exact s6BlkHom_mem g
  · intro U hU
    exact ⟨⟨s6Ext U, s6Ext_mem (s6_isometry_of_mem hU)⟩, Units.ext (s6_blk4_ext U)⟩

theorem blk4_injOn_CGDot12 : ∀ g ∈ CGDot12, ∀ h ∈ CGDot12, blk4 g = blk4 h → g = h :=
  fun g hg h hh hb => blk4_inj g h (MDot_le_OVq hg.1.1) (MDot_le_OVq hh.1.1) hg.1.2 hh.1.2 hg.2
    hh.2 hb

theorem blk4_image (B : Matrix (Fin 4) (Fin 4) (ZMod 3)) :
    (∃ g ∈ CGDot12, blk4 g = B) ↔
      ∃ u ∈ CFSG.Open.StatedOmega qV4m, (u : Matrix (Fin 4) (Fin 4) (ZMod 3)) = B := by
  have hmap1 : Subgroup.map s6C.subtype ⁅(⊤ : Subgroup ↥s6C), (⊤ : Subgroup ↥s6C)⁆ =
      CGDot12 := by
    rw [← commutator_s6C]
    exact Subgroup.map_subtype_commutator s6C
  have hmap2 : Subgroup.map s6BlkHom ⁅(⊤ : Subgroup ↥s6C), (⊤ : Subgroup ↥s6C)⁆ =
      CFSG.Open.StatedOmega qV4m := by
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, s6BlkHom_range]
    rfl
  constructor
  · rintro ⟨g, hg, rfl⟩
    rw [← hmap1] at hg
    obtain ⟨x, hx, rfl⟩ := hg
    refine ⟨s6BlkHom x, ?_, rfl⟩
    rw [← hmap2]
    exact ⟨x, hx, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    rw [← hmap2] at hu
    obtain ⟨x, hx, rfl⟩ := hu
    refine ⟨x.1, ?_, rfl⟩
    rw [← hmap1]
    exact ⟨x, hx, rfl⟩

end

end CFSG.Quasithin.SimsF5
