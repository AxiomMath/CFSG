module

public import CFSG.Quasithin.Recognition.CertG2TwoRelA
public import CFSG.Quasithin.Recognition.CertG2TwoRelB
public import CFSG.Quasithin.Recognition.CertG2TwoChk
public import CFSG.Quasithin.Recognition.CertDerived
public import CFSG.Quasithin.Recognition.CertU33Psu
public import CFSG.Quasithin.Recognition.CertU33Simple

public section

namespace CFSG.Quasithin

open scoped commutatorElement
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Ree CFSG.CosetTable

theorem g2_invol_check : ∀ t < 4,
    constCheck Tag.G2 2 (g2W (g2LetterStr t) ++ g2W (g2LetterStr t)) [] = true := by
  intro t ht
  interval_cases t
  exacts [g2_invol_check_0, g2_invol_check_1, g2_invol_check_2, g2_invol_check_3]

theorem g2_rel_check_aux : ∀ i < 15,
    constCheck Tag.G2 2 (g2PW (u33PresRels.getD i [])) [] = true := by
  intro i hi
  interval_cases i
  exacts [g2_rel_check_0, g2_rel_check_1, g2_rel_check_2, g2_rel_check_3, g2_rel_check_4,
    g2_rel_check_5, g2_rel_check_6, g2_rel_check_7, g2_rel_check_8, g2_rel_check_9,
    g2_rel_check_10, g2_rel_check_11, g2_rel_check_12, g2_rel_check_13, g2_rel_check_14]

theorem g2_comm_check_aux
    : ∀ j < 5, constCheck Tag.G2 2 (g2GenWord j)
    (g2Comm (g2W (g2CommG.getD j "")) (g2W (g2CommH.getD j ""))) = true := by
  intro j hj
  interval_cases j
  exacts [g2_comm_check_0, g2_comm_check_1, g2_comm_check_2, g2_comm_check_3, g2_comm_check_4]

theorem g2_conjb_check_aux : ∀ j < 5,
    constCheck Tag.G2 2
      (g2W (g2LetterStr 1) ++ g2GenWord j ++ g2Inv (g2W (g2LetterStr 1)))
      (g2PW (u33Word (g2ConjStrings.getD (5 * 1 + j) ""))) = true := by
  intro j hj
  interval_cases j
  exacts [g2_conjb_check_0, g2_conjb_check_1, g2_conjb_check_2, g2_conjb_check_3,
    g2_conjb_check_4]

theorem g2_root_positions :
    Tag.G2.rootCertificate.root 0 = Pi.single ⟨0, by decide⟩ 1 ∧
    Tag.G2.rootCertificate.root 1 = Pi.single ⟨1, by decide⟩ 1 ∧
    Tag.G2.rootCertificate.root 2 = -Pi.single ⟨0, by decide⟩ 1 ∧
    Tag.G2.rootCertificate.root 5 = -Pi.single ⟨1, by decide⟩ 1 := by
  decide

section Main

variable {k : Type} [Field k]

theorem constPinned_mem_adjointGroup
    (w : List (ℕ × ℤ)) :
    (constPinned Tag.G2 k w : ModGL Tag.G2 k) ∈ adjointGroup Tag.G2 k := by
  unfold constPinned
  refine Subgroup.list_prod_mem _ fun g hg => ?_
  obtain ⟨f, -, rfl⟩ := List.mem_map.1 hg
  exact pinnedX_mem_adjointGroup _ _

theorem constPinned_single (f : ℕ × ℤ) :
    constPinned Tag.G2 k [f] =
      pinnedX Tag.G2 k (Tag.G2.rootCertificate.root f.1) (f.2 : k) := by
  rw [constPinned_cons, constPinned_nil, mul_one]

theorem constPinned_inv'
    (w : List (ℕ × ℤ)) :
    (constPinned Tag.G2 k w)⁻¹ = constPinned Tag.G2 k (g2Inv w) := by
  induction w with
  | nil => simp [g2Inv, constPinned_nil]
  | cons f w ih =>
    have e : g2Inv (f :: w) = g2Inv w ++ [(f.1, -f.2)] := by simp [g2Inv]
    rw [e, constPinned_append, constPinned_cons, mul_inv_rev, ih, constPinned_single]
    congr 1
    rw [pinnedX_neg]
    simp

@[expose] noncomputable def g2Img
    (i : Fin 5) : ModGL Tag.G2 k := constPinned Tag.G2 k (g2GenWord i)

theorem lift_g2PW
    (w : List (Fin 5 × Bool)) :
    FreeGroup.lift (g2Img (k := k)) (FreeGroup.mk w) = constPinned Tag.G2 k (g2PW w) := by
  rw [FreeGroup.lift_mk]
  induction w with
  | nil => simp [g2PW, constPinned_nil]
  | cons x w ih =>
    simp only [g2PW, List.flatMap_cons, List.map_cons, List.prod_cons] at ih ⊢
    rw [ih, constPinned_append]
    congr 1
    obtain ⟨i, b⟩ := x
    cases b
    · simp only [g2PL, g2Img, Bool.false_eq_true, ↓reduceIte, Bool.cond_false]
      exact constPinned_inv' _
    · simp [g2PL, g2Img]

theorem g2_rel_one
    (h2 : (2 : k) = 0) {w : List (Fin 5 × Bool)} (hw : w ∈ u33PresRels) :
    constPinned Tag.G2 k (g2PW w) = 1 := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hw
  have h := g2_rel_check_aux i (by simpa [u33PresRels] using hi)
  rw [List.getD_eq_getElem _ _ hi] at h
  rw [constPinned_eq_of_constCheck h k (by simpa using h2), constPinned_nil]

noncomputable def g2Hom
    (h2 : (2 : k) = 0) : PG 5 u33PresRels →* ModGL Tag.G2 k :=
  PresentedGroup.toGroup (f := g2Img (k := k)) (by
    intro r hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    rw [lift_g2PW]
    exact g2_rel_one h2 hw)

theorem g2Hom_of
    (h2 : (2 : k) = 0) (i : Fin 5) :
    g2Hom h2 (PresentedGroup.of i) = g2Img i := by
  rw [g2Hom, PresentedGroup.toGroup.of]

theorem g2Hom_mk
    (h2 : (2 : k) = 0) (w : List (Fin 5 × Bool)) :
    g2Hom h2 (PresentedGroup.mk _ (FreeGroup.mk w)) = constPinned Tag.G2 k (g2PW w) :=
  lift_g2PW w

theorem range_g2Hom
    (h2 : (2 : k) = 0) :
    (g2Hom h2).range = Subgroup.closure (Set.range (g2Img (k := k))) := by
  rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of
    {r : FreeGroup (Fin 5) | r ∈ u33PresRels.map FreeGroup.mk}, MonoidHom.map_closure,
    ← Set.range_comp]
  congr 2

theorem constPinned_g2PW_mem_range
    (h2 : (2 : k) = 0) (w : List (Fin 5 × Bool)) :
    constPinned Tag.G2 k (g2PW w) ∈ (g2Hom h2).range :=
  ⟨PresentedGroup.mk _ (FreeGroup.mk w), g2Hom_mk h2 w⟩

end Main

section Letters

variable {k : Type} [Field k]

@[expose] noncomputable def g2L
    (t : ℕ) : ModGL Tag.G2 k := constPinned Tag.G2 k (g2W (g2LetterStr t))

theorem g2L_mem_adjointGroup
    (t : ℕ) : (g2L t : ModGL Tag.G2 k) ∈ adjointGroup Tag.G2 k :=
  constPinned_mem_adjointGroup _

theorem g2L_mul_self
    (h2 : (2 : k) = 0) {t : ℕ} (ht : t < 4) :
    (g2L t : ModGL Tag.G2 k) * g2L t = 1 := by
  have h := constPinned_eq_of_constCheck (g2_invol_check t ht) k (by simpa using h2)
  rw [constPinned_append, constPinned_nil] at h
  exact h

theorem g2L_inv (t : ℕ) :
    (g2L t : ModGL Tag.G2 k)⁻¹ = constPinned Tag.G2 k (g2Inv (g2W (g2LetterStr t))) :=
  constPinned_inv' _

theorem g2L_one_conj
    (h2 : (2 : k) = 0) {j : ℕ} (hj : j < 5) :
    (g2L 1 : ModGL Tag.G2 k) * constPinned Tag.G2 k (g2GenWord j) * (g2L 1)⁻¹ =
      constPinned Tag.G2 k (g2PW (u33Word (g2ConjStrings.getD (5 * 1 + j) ""))) := by
  have h := constPinned_eq_of_constCheck (g2_conjb_check_aux j hj) k (by simpa using h2)
  rw [constPinned_append, constPinned_append, ← g2L_inv] at h
  exact h

theorem g2Img_eq_comm
    (h2 : (2 : k) = 0) {j : ℕ} (hj : j < 5) :
    constPinned Tag.G2 k (g2GenWord j) =
      ⁅constPinned Tag.G2 k (g2W (g2CommG.getD j "")),
        constPinned Tag.G2 k (g2W (g2CommH.getD j ""))⁆ := by
  have h := constPinned_eq_of_constCheck (g2_comm_check_aux j hj) k (by simpa using h2)
  simp only [g2Comm, constPinned_append, ← constPinned_inv'] at h
  rw [h, commutatorElement_def]

theorem g2_gen_two_ne_one
    : constPinned Tag.G2 k (g2GenWord 2) ≠ 1 := by
  have e : g2GenWord 2 = [(0, 1)] := by decide +kernel
  intro h
  rw [e, constPinned_single] at h
  have h1 : pinnedX Tag.G2 k (Tag.G2.rootCertificate.root 0) 1 =
      pinnedX Tag.G2 k (Tag.G2.rootCertificate.root 0) 0 := by
    rw [pinnedX_zero]
    simpa using h
  exact one_ne_zero (pinnedX_injective Tag.G2 k _ h1)

theorem g2Hom_injective
    (h2 : (2 : k) = 0) : Function.Injective (g2Hom h2) := by
  have := isSimpleGroup_u33Pres
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (g2Hom h2).ker with h | h
  · exact h
  · exfalso
    have hmem : (PresentedGroup.of (2 : Fin 5) : PG 5 u33PresRels) ∈ (g2Hom h2).ker := by
      rw [h]
      trivial
    have h1 : g2Hom h2 (PresentedGroup.of (2 : Fin 5)) = 1 := hmem
    rw [g2Hom_of] at h1
    exact g2_gen_two_ne_one (k := k) h1

theorem eq_zero_or_eq_one_of_card_two [Finite k] (hk : Nat.card k = 2) (c : k) :
    c = 0 ∨ c = 1 := by
  obtain ⟨y, -, huniq⟩ := (Nat.card_eq_two_iff' (0 : k)).1 hk
  by_cases hc : c = 0
  · exact Or.inl hc
  · exact Or.inr ((huniq c hc).trans (huniq 1 one_ne_zero).symm)

theorem two_eq_zero_of_card_two [Finite k] (hk : Nat.card k = 2) : (2 : k) = 0 := by
  have h := card_nsmul_eq_zero' (G := k) (x := (1 : k))
  rwa [hk, nsmul_eq_mul, mul_one, Nat.cast_ofNat] at h

theorem g2L_zero
    : (g2L 0 : ModGL Tag.G2 k) = xUnit Tag.G2 k ⟨0, by decide⟩ 1 := by
  obtain ⟨h0, -⟩ := g2_root_positions
  have e : g2W (g2LetterStr 0) = [(0, 1)] := by decide +kernel
  show constPinned Tag.G2 k (g2W (g2LetterStr 0)) = _
  rw [e, constPinned_single]
  simp only [h0, Int.cast_one]
  rw [pinnedX_single]

theorem g2L_one
    : (g2L 1 : ModGL Tag.G2 k) = xUnit Tag.G2 k ⟨1, by decide⟩ 1 := by
  obtain ⟨-, h1, -⟩ := g2_root_positions
  have e : g2W (g2LetterStr 1) = [(1, 1)] := by decide +kernel
  show constPinned Tag.G2 k (g2W (g2LetterStr 1)) = _
  rw [e, constPinned_single]
  simp only [h1, Int.cast_one]
  rw [pinnedX_single]

theorem g2L_two
    : (g2L 2 : ModGL Tag.G2 k) = yUnit Tag.G2 k ⟨0, by decide⟩ 1 := by
  obtain ⟨-, -, h2, -⟩ := g2_root_positions
  have e : g2W (g2LetterStr 2) = [(2, 1)] := by decide +kernel
  show constPinned Tag.G2 k (g2W (g2LetterStr 2)) = _
  rw [e, constPinned_single]
  simp only [h2, Int.cast_one]
  rw [pinnedX_neg_single]

theorem g2L_three
    : (g2L 3 : ModGL Tag.G2 k) = yUnit Tag.G2 k ⟨1, by decide⟩ 1 := by
  obtain ⟨-, -, -, h5⟩ := g2_root_positions
  have e : g2W (g2LetterStr 3) = [(5, 1)] := by decide +kernel
  show constPinned Tag.G2 k (g2W (g2LetterStr 3)) = _
  rw [e, constPinned_single]
  simp only [h5, Int.cast_one]
  rw [pinnedX_neg_single]

theorem adjointGroup_G2_eq
    (hk2 : ∀ c : k, c = 0 ∨ c = 1) :
    adjointGroup Tag.G2 k =
      Subgroup.closure (insert 1 (Set.range fun t : Fin 4 => (g2L (t : ℕ) : ModGL Tag.G2 k))) := by
  have hi2 : ∀ i : Fin Tag.G2.rank, i = ⟨0, by decide⟩ ∨ i = ⟨1, by decide⟩ := by
    rintro ⟨i, hi⟩
    have hi' : i < 2 := hi
    interval_cases i
    · exact Or.inl rfl
    · exact Or.inr rfl
  apply le_antisymm
  · refine (Subgroup.closure_le _).2 ?_
    rintro g ⟨i, c, hg | hg⟩
    · have hg' : g = xUnit Tag.G2 k i c := Units.ext hg
      rw [SetLike.mem_coe, hg']
      rcases hk2 c with rfl | rfl
      · rw [xUnit_zero]
        exact Subgroup.one_mem _
      · rcases hi2 i with rfl | rfl
        · rw [← g2L_zero]
          exact Subgroup.subset_closure (Set.mem_insert_of_mem _ ⟨0, rfl⟩)
        · rw [← g2L_one]
          exact Subgroup.subset_closure (Set.mem_insert_of_mem _ ⟨1, rfl⟩)
    · have hg' : g = yUnit Tag.G2 k i c := Units.ext hg
      rw [SetLike.mem_coe, hg']
      rcases hk2 c with rfl | rfl
      · rw [CFSG.LieType.Chevalley.yUnit_zero]
        exact Subgroup.one_mem _
      · rcases hi2 i with rfl | rfl
        · rw [← g2L_two]
          exact Subgroup.subset_closure (Set.mem_insert_of_mem _ ⟨2, rfl⟩)
        · rw [← g2L_three]
          exact Subgroup.subset_closure (Set.mem_insert_of_mem _ ⟨3, rfl⟩)
  · refine (Subgroup.closure_le _).2 ?_
    rintro g (rfl | ⟨t, rfl⟩)
    · exact Subgroup.one_mem _
    · exact g2L_mem_adjointGroup _

end Letters

section Derived

variable {k : Type} [Field k]

theorem mem_range_g2Hom_of_eq
    (h2 : (2 : k) = 0) {g : ModGL Tag.G2 k} {w : List (Fin 5 × Bool)}
    (h : g = constPinned Tag.G2 k (g2PW w)) : g ∈ (g2Hom h2).range := by
  rw [h]
  exact constPinned_g2PW_mem_range h2 w

theorem g2Img_mem_range
    (h2 : (2 : k) = 0) (j : Fin 5) : g2Img j ∈ (g2Hom h2).range :=
  ⟨PresentedGroup.of j, g2Hom_of h2 j⟩

theorem g2L_zero_eq_img
    : (g2L 0 : ModGL Tag.G2 k) = g2Img 2 := by
  have e : g2GenWord 2 = g2W (g2LetterStr 0) := by decide +kernel
  show constPinned Tag.G2 k (g2W (g2LetterStr 0)) = constPinned Tag.G2 k (g2GenWord 2)
  rw [e]

theorem g2L_two_mem_range
    (h2 : (2 : k) = 0) : (g2L 2 : ModGL Tag.G2 k) ∈ (g2Hom h2).range :=
  mem_range_g2Hom_of_eq h2 (constPinned_eq_of_constCheck g2_cword_check k (by simpa using h2))

theorem g2L_one_mul_three
    : (g2L 1 : ModGL Tag.G2 k) * g2L 3 = g2Img 4 := by
  have e : g2GenWord 4 = g2W (g2LetterStr 1) ++ g2W (g2LetterStr 3) := by decide +kernel
  show _ = constPinned Tag.G2 k (g2GenWord 4)
  rw [e, constPinned_append]
  rfl

theorem g2L_three_eq
    (h2 : (2 : k) = 0) : (g2L 3 : ModGL Tag.G2 k) = g2L 1 * g2Img 4 := by
  rw [← g2L_one_mul_three, ← mul_assoc, g2L_mul_self h2 (by norm_num), one_mul]

theorem g2L_one_mem_normalizer
    (h2 : (2 : k) = 0) :
    (g2L 1 : ModGL Tag.G2 k) ∈ Subgroup.normalizer ((g2Hom h2).range : Set (ModGL Tag.G2 k)) := by
  rw [range_g2Hom]
  refine mem_normalizer_of_involution (g2L_mul_self h2 (by norm_num)) ?_
  rintro _ ⟨j, rfl⟩
  rw [← range_g2Hom h2]
  exact mem_range_g2Hom_of_eq h2 (g2L_one_conj h2 j.2)

theorem g2L_mem_normalizer
    (h2 : (2 : k) = 0) {t : ℕ} (ht : t < 4) :
    (g2L t : ModGL Tag.G2 k) ∈ Subgroup.normalizer ((g2Hom h2).range : Set (ModGL Tag.G2 k)) := by
  interval_cases t
  · rw [g2L_zero_eq_img]
    exact Subgroup.le_normalizer (g2Img_mem_range h2 2)
  · exact g2L_one_mem_normalizer h2
  · exact Subgroup.le_normalizer (g2L_two_mem_range h2)
  · rw [g2L_three_eq h2]
    exact Subgroup.mul_mem _ (g2L_one_mem_normalizer h2)
      (Subgroup.le_normalizer (g2Img_mem_range h2 4))

theorem commutator_mem_of_left {G : Type*} [Group G] {R : Subgroup G} {x y : G} (hx : x ∈ R)
    (hy : y ∈ Subgroup.normalizer (R : Set G)) : ⁅x, y⁆ ∈ R := by
  have h : y * x⁻¹ * y⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.1 hy x⁻¹).1 (R.inv_mem hx)
  have e : ⁅x, y⁆ = x * (y * x⁻¹ * y⁻¹) := by
    simp only [commutatorElement_def]; group
  rw [e]
  exact R.mul_mem hx h

theorem commutator_mem_of_right {G : Type*} [Group G] {R : Subgroup G} {x y : G}
    (hx : x ∈ Subgroup.normalizer (R : Set G)) (hy : y ∈ R) : ⁅x, y⁆ ∈ R := by
  have h : x * y * x⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.1 hx y).1 hy
  have e : ⁅x, y⁆ = (x * y * x⁻¹) * y⁻¹ := commutatorElement_def x y
  rw [e]
  exact R.mul_mem h (R.inv_mem hy)

theorem commutator_eq_sq_of_involutions {G : Type*} [Group G] {x y : G} (hx : x * x = 1)
    (hy : y * y = 1) : ⁅x, y⁆ = (x * y) * (x * y) := by
  have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  simp only [commutatorElement_def, hx', hy', mul_assoc]

theorem g2L_comm_mem_range
    (h2 : (2 : k) = 0) {t t' : ℕ} (ht : t < 4) (ht' : t' < 4) :
    ⁅(g2L t : ModGL Tag.G2 k), g2L t'⁆ ∈ (g2Hom h2).range := by
  have hN := fun {s : ℕ} (hs : s < 4) => g2L_mem_normalizer h2 (k := k) hs
  have h0 : (g2L 0 : ModGL Tag.G2 k) ∈ (g2Hom h2).range := by
    rw [g2L_zero_eq_img]; exact g2Img_mem_range h2 2
  have h2' := g2L_two_mem_range h2
  have hbd : (g2L 1 : ModGL Tag.G2 k) * g2L 3 ∈ (g2Hom h2).range := by
    rw [g2L_one_mul_three]; exact g2Img_mem_range h2 4
  have hdb : (g2L 3 : ModGL Tag.G2 k) * g2L 1 ∈ (g2Hom h2).range := by
    have := (g2Hom h2).range.inv_mem hbd
    have e : ((g2L 1 : ModGL Tag.G2 k) * g2L 3)⁻¹ = g2L 3 * g2L 1 := by
      rw [mul_inv_rev, inv_eq_of_mul_eq_one_right (g2L_mul_self h2 (by norm_num)),
        inv_eq_of_mul_eq_one_right (g2L_mul_self h2 (by norm_num))]
    rwa [e] at this
  interval_cases t <;> interval_cases t'
  · exact commutator_mem_of_left h0 (hN (by norm_num))
  · exact commutator_mem_of_left h0 (hN (by norm_num))
  · exact commutator_mem_of_left h0 (hN (by norm_num))
  · exact commutator_mem_of_left h0 (hN (by norm_num))
  · exact commutator_mem_of_right (hN (by norm_num)) h0
  · rw [commutatorElement_self]; exact Subgroup.one_mem _
  · exact commutator_mem_of_right (hN (by norm_num)) h2'
  · rw [commutator_eq_sq_of_involutions (g2L_mul_self h2 (by norm_num))
      (g2L_mul_self h2 (by norm_num))]
    exact Subgroup.mul_mem _ hbd hbd
  · exact commutator_mem_of_left h2' (hN (by norm_num))
  · exact commutator_mem_of_left h2' (hN (by norm_num))
  · exact commutator_mem_of_left h2' (hN (by norm_num))
  · exact commutator_mem_of_left h2' (hN (by norm_num))
  · exact commutator_mem_of_right (hN (by norm_num)) h0
  · rw [commutator_eq_sq_of_involutions (g2L_mul_self h2 (by norm_num))
      (g2L_mul_self h2 (by norm_num))]
    exact Subgroup.mul_mem _ hdb hdb
  · exact commutator_mem_of_right (hN (by norm_num)) h2'
  · rw [commutatorElement_self]; exact Subgroup.one_mem _

theorem g2_derived_eq_range
    (h2 : (2 : k) = 0) (hk2 : ∀ c : k, c = 0 ∨ c = 1) :
    ⁅adjointGroup Tag.G2 k, adjointGroup Tag.G2 k⁆ = (g2Hom h2).range := by
  apply le_antisymm
  · rw [adjointGroup_G2_eq hk2, range_g2Hom]
    refine commutator_closure_le_of_involutions ?_ ?_ ?_
    · rintro s (rfl | ⟨t, rfl⟩)
      · exact mul_one 1
      · exact g2L_mul_self h2 t.2
    · rintro s (rfl | ⟨t, rfl⟩) u ⟨j, rfl⟩
      · rw [one_mul, inv_one, mul_one]
        exact Subgroup.subset_closure (Set.mem_range_self j)
      · rw [← range_g2Hom h2]
        have hN := Subgroup.mem_normalizer_iff.1 (g2L_mem_normalizer h2 t.2)
        exact (hN (g2Img j)).1 (g2Img_mem_range h2 j)
    · rintro s hs s' hs'
      rw [← range_g2Hom h2]
      rcases hs with rfl | ⟨t, rfl⟩
      · simp
      rcases hs' with rfl | ⟨t', rfl⟩
      · simp
      exact g2L_comm_mem_range h2 t.2 t'.2
  · rw [range_g2Hom]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe]
    have h : g2Img j = ⁅constPinned Tag.G2 k (g2W (g2CommG.getD j "")),
        constPinned Tag.G2 k (g2W (g2CommH.getD j ""))⁆ := g2Img_eq_comm h2 j.2
    rw [h]
    exact Subgroup.commutator_mem_commutator (constPinned_mem_adjointGroup _)
      (constPinned_mem_adjointGroup _)

theorem g2_derived_mulEquiv_PSU3
    (k : Type) [Field k] [Finite k] (hk : Nat.card k = 2) :
    Nonempty (↥⁅adjointGroup Tag.G2 k, adjointGroup Tag.G2 k⁆ ≃* CFSG.Open.PSU3 3 1) := by
  have h2 := two_eq_zero_of_card_two hk
  have hder := g2_derived_eq_range h2 (eq_zero_or_eq_one_of_card_two hk)
  obtain ⟨e⟩ := u33Pres_mulEquiv_PSU3
  exact ⟨((MonoidHom.ofInjective (g2Hom_injective h2)).trans
    (MulEquiv.subgroupCongr hder.symm)).symm.trans e⟩

end Derived

end CFSG.Quasithin
