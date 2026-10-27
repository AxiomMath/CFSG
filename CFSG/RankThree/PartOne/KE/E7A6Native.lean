module

public import CFSG.RankThree.PartOne.KE.E7A6NativeModule
public import CFSG.RankThree.PartOne.KE.E7A2Native

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix
open CFSG.RankThree.E6 (chainRoot)
open scoped commutatorElement Pointwise MatrixGroups


variable {K : Type} [Field K]

theorem e7a6TorusElt_mul (a b c d e f a' b' c' d' e' f' : Kˣ) :
    e7a6TorusElt a b c d e f * e7a6TorusElt a' b' c' d' e' f' =
      e7a6TorusElt (a * a') (b * b') (c * c') (d * d') (e * e') (f * f') := by
  simp only [e7a6TorusElt, torusElt_mul]
  rw [Commute.mul_mul_mul_comm (Commute.mul_right (Commute.mul_right (Commute.mul_right (Commute.mul_right (torusElt_mul_comm (e7Index 6) (e7Index 0) f a' : Commute _ _) (torusElt_mul_comm (e7Index 6) (e7Index 2) f b')) (torusElt_mul_comm (e7Index 6) (e7Index 3) f c')) (torusElt_mul_comm (e7Index 6) (e7Index 4) f d')) (torusElt_mul_comm (e7Index 6) (e7Index 5) f e'))]
  rw [Commute.mul_mul_mul_comm (Commute.mul_right (Commute.mul_right (Commute.mul_right (torusElt_mul_comm (e7Index 5) (e7Index 0) e a' : Commute _ _) (torusElt_mul_comm (e7Index 5) (e7Index 2) e b')) (torusElt_mul_comm (e7Index 5) (e7Index 3) e c')) (torusElt_mul_comm (e7Index 5) (e7Index 4) e d'))]
  rw [Commute.mul_mul_mul_comm (Commute.mul_right (Commute.mul_right (torusElt_mul_comm (e7Index 4) (e7Index 0) d a' : Commute _ _) (torusElt_mul_comm (e7Index 4) (e7Index 2) d b')) (torusElt_mul_comm (e7Index 4) (e7Index 3) d c'))]
  rw [Commute.mul_mul_mul_comm (Commute.mul_right (torusElt_mul_comm (e7Index 3) (e7Index 0) c a' : Commute _ _) (torusElt_mul_comm (e7Index 3) (e7Index 2) c b'))]
  rw [Commute.mul_mul_mul_comm (torusElt_mul_comm (e7Index 2) (e7Index 0) b a' : Commute _ _)]

theorem e7a6TorusElt_one : e7a6TorusElt (1 : Kˣ) 1 1 1 1 1 = (1 : ModGL Tag.E7 K) := by
  simp only [e7a6TorusElt, torusElt_one, mul_one]

theorem e7a6TorusElt_inv (a b c d e f : Kˣ) :
    (e7a6TorusElt a b c d e f : ModGL Tag.E7 K)⁻¹ = e7a6TorusElt a⁻¹ b⁻¹ c⁻¹ d⁻¹ e⁻¹ f⁻¹ := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [e7a6TorusElt_mul, mul_inv_cancel, mul_inv_cancel, mul_inv_cancel, mul_inv_cancel, mul_inv_cancel, mul_inv_cancel, e7a6TorusElt_one]

theorem mem_subsystemTorus_e7a6 {g : ModGL Tag.E7 K} :
    g ∈ subsystemTorus Tag.E7 K e7a6support ↔ ∃ a b c d e f : Kˣ, g = e7a6TorusElt a b c d e f := by
  constructor
  · intro hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨i, hi, t, rfl⟩ := hx
      rcases (mem_e7a6support i).1 hi with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨t, 1, 1, 1, 1, 1, by simp only [e7a6TorusElt, torusElt_one, mul_one, one_mul]⟩
      · exact ⟨1, t, 1, 1, 1, 1, by simp only [e7a6TorusElt, torusElt_one, mul_one, one_mul]⟩
      · exact ⟨1, 1, t, 1, 1, 1, by simp only [e7a6TorusElt, torusElt_one, mul_one, one_mul]⟩
      · exact ⟨1, 1, 1, t, 1, 1, by simp only [e7a6TorusElt, torusElt_one, mul_one, one_mul]⟩
      · exact ⟨1, 1, 1, 1, t, 1, by simp only [e7a6TorusElt, torusElt_one, mul_one, one_mul]⟩
      · exact ⟨1, 1, 1, 1, 1, t, by simp only [e7a6TorusElt, torusElt_one, mul_one, one_mul]⟩
    | one => exact ⟨1, 1, 1, 1, 1, 1, e7a6TorusElt_one.symm⟩
    | mul x y _ _ hx hy =>
      obtain ⟨a, b, c, d, e, f, rfl⟩ := hx
      obtain ⟨a', b', c', d', e', f', rfl⟩ := hy
      exact ⟨_, _, _, _, _, _, e7a6TorusElt_mul a b c d e f a' b' c' d' e' f'⟩
    | inv x _ hx =>
      obtain ⟨a, b, c, d, e, f, rfl⟩ := hx
      exact ⟨_, _, _, _, _, _, e7a6TorusElt_inv a b c d e f⟩
  · rintro ⟨a, b, c, d, e, f, rfl⟩
    exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (torusElt_mem_subsystemTorus mem_e7a6support_0 a)
      (torusElt_mem_subsystemTorus mem_e7a6support_2 b))
      (torusElt_mem_subsystemTorus mem_e7a6support_3 c))
      (torusElt_mem_subsystemTorus mem_e7a6support_4 d))
      (torusElt_mem_subsystemTorus mem_e7a6support_5 e))
      (torusElt_mem_subsystemTorus mem_e7a6support_6 f)

theorem e7a6Weight_height : ∀ i j : Fin 7,
    (height (e7a6Weight j) < height (e7a6Weight i) ↔ i < j) ∧
      (height (e7a6Weight i) = height (e7a6Weight j) ↔ i = j) := by
  decide +kernel

theorem e7a6Label_precedes_iff (i j : Fin 7) : (e7a6Label i).Precedes (e7a6Label j) ↔ i < j := by
  simp only [Label.Precedes, Label.weight]
  constructor
  · rintro (h | ⟨h, h'⟩)
    · exact ((e7a6Weight_height i j).1).1 h
    · obtain rfl := ((e7a6Weight_height i j).2).1 h
      exact absurd h' (lt_irrefl _)
  · intro h
    exact Or.inl (((e7a6Weight_height i j).1).2 h)

theorem e7Index_mem_e7a6support_iff (i : Fin 7) :
    e7Index i ∈ e7a6support ↔ (i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) :=
  mem_e7a6support (e7Index i)

theorem e7a6Weight_outside : ∀ k : Fin 7, ∀ i : Fin 7, ¬(i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) →
    e7a6Weight k (e7Index i) = e7a6Weight 0 (e7Index i) := by
  decide +kernel

theorem exists_e7a6Weight_of_e7RootVec : ∀ m : Fin 126,
    (∀ i : Fin 7, ¬(i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) →
      e7RootVec m (e7Index i) = e7a6Weight 0 (e7Index i)) →
      ∃ k, e7a6Weight k = e7RootVec m := by
  decide +kernel

theorem exists_e7a6Weight_smul {w : WeylGroup Tag.E7}
    (hw : w ∈ parabolicWeylGroup Tag.E7 e7a6support) (k : Fin 7) :
    ∃ k', e7a6Weight k' = w • e7a6Weight k := by
  obtain ⟨m, hm⟩ := isRoot_iff_exists_e7RootVec.1 (IsRoot.smul (isRoot_e7a6Weight k) w)
  obtain ⟨k', hk'⟩ := exists_e7a6Weight_of_e7RootVec m (fun i hi => by
    have hi' : e7Index i ∉ e7a6support := fun h => hi ((e7Index_mem_e7a6support_iff i).1 h)
    rw [hm, smul_apply_of_mem_parabolicWeylGroup hw _ hi', e7a6Weight_outside k i hi])
  exact ⟨k', hk'.trans hm⟩

theorem smul_e7a6Weight_eq_of_not_lt {w : WeylGroup Tag.E7}
    (hw : w ∈ parabolicWeylGroup Tag.E7 e7a6support)
    (hprec : ∀ j j', e7a6Weight j' = w • e7a6Weight j → ¬j < j') (j : Fin 7) :
    w • e7a6Weight j = e7a6Weight j := by
  by_contra hj
  classical
  set M : Finset (Fin 7) := Finset.univ.filter fun k => w • e7a6Weight k ≠ e7a6Weight k
  have hM : M.Nonempty := ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
  obtain ⟨k, hkM, hmin⟩ := M.exists_min_image id hM
  have hk : w • e7a6Weight k ≠ e7a6Weight k := (Finset.mem_filter.mp hkM).2
  obtain ⟨k', hk'⟩ := exists_e7a6Weight_smul hw k
  have hne : k' ≠ k := fun h => hk (by rw [← hk', h])
  have hlt : k' < k := lt_of_le_of_ne (not_lt.1 (hprec k k' hk')) hne
  have hk'M : k' ∈ M := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun h => hne ?_⟩
    apply e7a6Weight_injective
    apply smul_left_cancel w
    rw [h]
    exact hk'
  exact absurd (hmin k' hk'M) (not_le.mpr hlt)


theorem single_eq_e7a6Weight_sub :
    (Pi.single (e7Index 0) 1 : Fin Tag.E7.rank → ℤ) = e7a6Weight 0 - e7a6Weight 1 ∧
    (Pi.single (e7Index 2) 1 : Fin Tag.E7.rank → ℤ) = e7a6Weight 1 - e7a6Weight 2 ∧
    (Pi.single (e7Index 3) 1 : Fin Tag.E7.rank → ℤ) = e7a6Weight 2 - e7a6Weight 3 ∧
    (Pi.single (e7Index 4) 1 : Fin Tag.E7.rank → ℤ) = e7a6Weight 3 - e7a6Weight 4 ∧
    (Pi.single (e7Index 5) 1 : Fin Tag.E7.rank → ℤ) = e7a6Weight 4 - e7a6Weight 5 ∧
    (Pi.single (e7Index 6) 1 : Fin Tag.E7.rank → ℤ) = e7a6Weight 5 - e7a6Weight 6 := by
  decide +kernel

theorem eq_one_of_smul_e7a6Weight {w : WeylGroup Tag.E7}
    (hw : w ∈ parabolicWeylGroup Tag.E7 e7a6support) (h : ∀ k, w • e7a6Weight k = e7a6Weight k) :
    w = 1 := by
  obtain ⟨e0, e2, e3, e4, e5, e6⟩ := single_eq_e7a6Weight_sub
  refine eq_one_of_forall_height_pos fun i => ?_
  by_cases hi : i ∈ e7a6support
  · have hfix : w • (Pi.single i 1 : Fin Tag.E7.rank → ℤ) = Pi.single i 1 := by
      rcases (mem_e7a6support i).1 hi with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [e0, smul_sub, h, h]
      · rw [e2, smul_sub, h, h]
      · rw [e3, smul_sub, h, h]
      · rw [e4, smul_sub, h, h]
      · rw [e5, smul_sub, h, h]
      · rw [e6, smul_sub, h, h]
    rw [hfix, height_single]
    exact one_pos
  · have hroot := IsRoot.smul (isRoot_single Tag.E7 i) w
    have hcoord : (w • (Pi.single i 1 : Fin Tag.E7.rank → ℤ)) i = 1 := by
      rw [smul_apply_of_mem_parabolicWeylGroup hw _ hi, Pi.single_eq_same]
    refine (IsRoot.height_pos_iff hroot).2 ?_
    rcases hroot.nonneg_or_nonpos with hs | hs
    · exact hs
    · have := hs i
      omega

theorem borel_apply_e7a6Vec_eq_zero {c : ModGL Tag.E7 K} (hc : c ∈ borelGroup Tag.E7 K)
    {j j' : Fin 7} (h : j < j') :
    (c : Module.End K (RootModule Tag.E7 K)) (e7a6Vec K j) (e7a6Label j') = 0 :=
  (triangular_borel_structure.{0, 0} Tag.E7 K).2.2.2.2.2.2.2.2.2.1 c hc (e7a6Label j')
    (e7a6Label j) ((e7a6Label_precedes_iff j j').2 h)


@[expose] def e7a6PosRoot : Fin 21 → Fin Tag.E7.rank → ℤ :=
  ![chainRoot e7a6chain 5 6,
    chainRoot e7a6chain 4 5,
    chainRoot e7a6chain 4 6,
    chainRoot e7a6chain 3 4,
    chainRoot e7a6chain 3 5,
    chainRoot e7a6chain 3 6,
    chainRoot e7a6chain 2 3,
    chainRoot e7a6chain 2 4,
    chainRoot e7a6chain 2 5,
    chainRoot e7a6chain 2 6,
    chainRoot e7a6chain 1 2,
    chainRoot e7a6chain 1 3,
    chainRoot e7a6chain 1 4,
    chainRoot e7a6chain 1 5,
    chainRoot e7a6chain 1 6,
    chainRoot e7a6chain 0 1,
    chainRoot e7a6chain 0 2,
    chainRoot e7a6chain 0 3,
    chainRoot e7a6chain 0 4,
    chainRoot e7a6chain 0 5,
    chainRoot e7a6chain 0 6]

theorem e7a6PosRoot_injective : Function.Injective e7a6PosRoot := by
  intro k k' h
  revert k k'
  decide +kernel

theorem e7a6chainRoot_height_pos : ∀ k l : Fin 7, k ≠ l →
    (0 < height (chainRoot e7a6chain k l) ↔ k < l) := by
  decide +kernel

theorem exists_e7a6PosRoot :
    ∀ k l : Fin 7, k < l → ∃ m, e7a6PosRoot m = chainRoot e7a6chain k l := by
  decide +kernel

theorem range_e7a6PosRoot : Set.range e7a6PosRoot = parabolicPosRoots Tag.E7 e7a6support := by
  ext β
  constructor
  · rintro ⟨m, rfl⟩
    have h : ∀ m : Fin 21, ∃ k l : Fin 7, k < l ∧ e7a6PosRoot m = chainRoot e7a6chain k l := by
      decide +kernel
    obtain ⟨k, l, hkl, hm⟩ := h m
    rw [hm]
    have hmem := e7a6chainRoot_mem_parabolicRoots hkl.ne
    exact ⟨hmem, hmem.1, (e7a6chainRoot_height_pos k l hkl.ne).2 hkl⟩
  · rintro ⟨hβ, -, hpos⟩
    obtain ⟨k, l, hkl, rfl⟩ := exists_e7a6chainRoot_of_mem hβ
    exact exists_e7a6PosRoot k l ((e7a6chainRoot_height_pos k l hkl).1 hpos)

@[expose] def e7a6PosRow : Fin 21 → Fin 7 := ![5, 4, 4, 3, 3, 3, 2, 2, 2, 2, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0]

@[expose] def e7a6PosCol : Fin 21 → Fin 7 := ![6, 5, 6, 4, 5, 6, 3, 4, 5, 6, 2, 3, 4, 5, 6, 1, 2, 3, 4, 5, 6]

theorem e7a6PosRoot_eq (m : Fin 21) :
    e7a6PosRoot m = chainRoot e7a6chain (e7a6PosRow m) (e7a6PosCol m) := by
  fin_cases m <;> rfl

theorem e7a6PosRow_lt_col : ∀ m : Fin 21, e7a6PosRow m < e7a6PosCol m := by decide

theorem e7a6_one_add_mul_one_add {A S : Matrix (Fin 7) (Fin 7) K} (h : A * S = 0) :
    (1 + A) * (1 + S) = 1 + (A + S) := by
  rw [add_mul, mul_add, mul_add, one_mul, one_mul, mul_one, h, add_zero]
  abel

theorem e7a6_single_mul_eq_zero {p q : Fin 7} (a : K) {S : Matrix (Fin 7) (Fin 7) K}
    (h : ∀ j, S q j = 0) : (single p q a : Matrix (Fin 7) (Fin 7) K) * S = 0 := by
  ext r s
  by_cases hr : r = p
  · subst hr
    rw [single_mul_apply_same, h, mul_zero, Matrix.zero_apply]
  · rw [single_mul_apply_of_ne _ _ _ _ _ hr, Matrix.zero_apply]

theorem prod_e7a6Pos (x : Fin 21 → K) :
    (List.ofFn fun m => (1 + single (e7a6PosRow m) (e7a6PosCol m) (x m) :
      Matrix (Fin 7) (Fin 7) K)).prod =
      1 + (single 5 6 (x 0) + (single 4 5 (x 1) + (single 4 6 (x 2) + (single 3 4 (x 3) + (single 3 5 (x 4) + (single 3 6 (x 5) + (single 2 3 (x 6) + (single 2 4 (x 7) + (single 2 5 (x 8) + (single 2 6 (x 9) + (single 1 2 (x 10) + (single 1 3 (x 11) + (single 1 4 (x 12) + (single 1 5 (x 13) + (single 1 6 (x 14) + (single 0 1 (x 15) + (single 0 2 (x 16) + (single 0 3 (x 17) + (single 0 4 (x 18) + (single 0 5 (x 19) + single 0 6 (x 20))))))))))))))))))))) := by
  simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one]
  change ((1 + single 5 6 (x 0)) * ((1 + single 4 5 (x 1)) * ((1 + single 4 6 (x 2)) * ((1 + single 3 4 (x 3)) * ((1 + single 3 5 (x 4)) * ((1 + single 3 6 (x 5)) * ((1 + single 2 3 (x 6)) * ((1 + single 2 4 (x 7)) * ((1 + single 2 5 (x 8)) * ((1 + single 2 6 (x 9)) * ((1 + single 1 2 (x 10)) * ((1 + single 1 3 (x 11)) * ((1 + single 1 4 (x 12)) * ((1 + single 1 5 (x 13)) * ((1 + single 1 6 (x 14)) * ((1 + single 0 1 (x 15)) * ((1 + single 0 2 (x 16)) * ((1 + single 0 3 (x 17)) * ((1 + single 0 4 (x 18)) * ((1 + single 0 5 (x 19)) * (1 + single 0 6 (x 20)))))))))))))))))))))) = _
  rw [e7a6_one_add_mul_one_add (e7a6_single_mul_eq_zero _ fun j => by simp), e7a6_one_add_mul_one_add (e7a6_single_mul_eq_zero _ fun j => by simp), e7a6_one_add_mul_one_add (e7a6_single_mul_eq_zero _ fun j => by simp), e7a6_one_add_mul_one_add (e7a6_single_mul_eq_zero _ fun j => by simp), e7a6_one_add_mul_one_add (e7a6_single_mul_eq_zero _ fun j => by simp), e7a6_one_add_mul_one_add (e7a6_single_mul_eq_zero _ fun j => by simp), e7a6_one_add_mul_one_add (e7a6_single_mul_eq_zero _ fun j => by simp), e7a6_one_add_mul_one_add (e7a6_single_mul_eq_zero _ fun j => by simp), e7a6_one_add_mul_one_add (e7a6_single_mul_eq_zero _ fun j => by simp), e7a6_one_add_mul_one_add (e7a6_single_mul_eq_zero _ fun j => by simp), e7a6_one_add_mul_one_add (e7a6_single_mul_eq_zero _ fun j => by simp), e7a6_one_add_mul_one_add (e7a6_single_mul_eq_zero _ fun j => by simp), e7a6_one_add_mul_one_add (e7a6_single_mul_eq_zero _ fun j => by simp), e7a6_one_add_mul_one_add (e7a6_single_mul_eq_zero _ fun j => by simp), e7a6_one_add_mul_one_add (e7a6_single_mul_eq_zero _ fun j => by simp), e7a6_one_add_mul_one_add (e7a6_single_mul_eq_zero _ fun j => by simp), e7a6_one_add_mul_one_add (e7a6_single_mul_eq_zero _ fun j => by simp), e7a6_one_add_mul_one_add (e7a6_single_mul_eq_zero _ fun j => by simp), e7a6_one_add_mul_one_add (e7a6_single_mul_eq_zero _ fun j => by simp), e7a6_one_add_mul_one_add (e7a6_single_mul_eq_zero _ fun j => by simp)]

theorem e7a6Mat_list_prod (l : List (ModGL Tag.E7 K))
    (hl : ∀ g ∈ l, g ∈ subsystemGroup Tag.E7 K e7a6support) :
    e7a6Mat l.prod = (l.map e7a6Mat).prod := by
  induction l with
  | nil => rw [List.prod_nil, List.map_nil, List.prod_nil, e7a6Mat_one]
  | cons g l ih =>
    rw [List.prod_cons, List.map_cons, List.prod_cons,
      e7a6Mat_mul (hl g List.mem_cons_self) (Subgroup.list_prod_mem _ fun h hh => hl h
        (List.mem_cons_of_mem g hh)), ih fun h hh => hl h (List.mem_cons_of_mem g hh)]

theorem e7a6PosRoot_mem (m : Fin 21) :
    e7a6PosRoot m ∈ parabolicRoots Tag.E7 e7a6support :=
  (show e7a6PosRoot m ∈ parabolicPosRoots Tag.E7 e7a6support from
    range_e7a6PosRoot ▸ ⟨m, rfl⟩).1


theorem eq_one_of_e7a6Mat_mul_eq_one {t u : ModGL Tag.E7 K}
    (ht : t ∈ subsystemTorus Tag.E7 K e7a6support)
    (hu : u ∈ parabolicLeviUnipotent Tag.E7 K e7a6support) (h : e7a6Mat (t * u) = 1) :
    t = 1 ∧ u = 1 := by
  obtain ⟨a, b, c, d, e, f, rfl⟩ := mem_subsystemTorus_e7a6.1 ht
  obtain ⟨x, -, rfl⟩ := (bijOn_prod_pinnedX_parabolicPosRoots (K := K) e7a6PosRoot
    e7a6PosRoot_injective range_e7a6PosRoot).surjOn hu
  choose ε hε hfam using e7a6RootFamily_all (K := K)
  have hrc : ∀ m, e7a6PosRow m ≠ e7a6PosCol m := fun m => (e7a6PosRow_lt_col m).ne
  set y : Fin 21 → K := fun m => (ε (e7a6PosRow m) (e7a6PosCol m) (hrc m) : K) * x m with hy
  have hlist : ∀ g ∈ List.ofFn fun m => pinnedX Tag.E7 K (e7a6PosRoot m) (x m),
      g ∈ subsystemGroup Tag.E7 K e7a6support := by
    intro g hg
    obtain ⟨m, rfl⟩ := List.mem_ofFn.1 hg
    exact pinnedX_mem_e7a6Group (e7a6PosRoot_mem m) _
  have hu' : e7a6Mat (List.ofFn fun m => pinnedX Tag.E7 K (e7a6PosRoot m) (x m)).prod =
      1 + (single 5 6 (y 0) + (single 4 5 (y 1) + (single 4 6 (y 2) + (single 3 4 (y 3) + (single 3 5 (y 4) + (single 3 6 (y 5) + (single 2 3 (y 6) + (single 2 4 (y 7) + (single 2 5 (y 8) + (single 2 6 (y 9) + (single 1 2 (y 10) + (single 1 3 (y 11) + (single 1 4 (y 12) + (single 1 5 (y 13) + (single 1 6 (y 14) + (single 0 1 (y 15) + (single 0 2 (y 16) + (single 0 3 (y 17) + (single 0 4 (y 18) + (single 0 5 (y 19) + single 0 6 (y 20))))))))))))))))))))) := by
    rw [e7a6Mat_list_prod _ hlist, List.map_ofFn, ← prod_e7a6Pos y]
    refine congrArg List.prod (congrArg List.ofFn (funext fun m => ?_))
    rw [Function.comp_apply, e7a6PosRoot_eq, hfam]
  rw [e7a6Mat_mul (e7a6TorusElt_mem a b c d e f) (Subgroup.list_prod_mem _ hlist),
    e7a6Mat_e7a6TorusElt, hu'] at h
  have hE : ∀ p q, (Matrix.diagonal ![(a : K), ((a⁻¹ * b : Kˣ) : K), ((b⁻¹ * c : Kˣ) : K), ((c⁻¹ * d : Kˣ) : K),
      ((d⁻¹ * e : Kˣ) : K), ((e⁻¹ * f : Kˣ) : K), ((f⁻¹ : Kˣ) : K)] *
      (1 + (single 5 6 (y 0) + (single 4 5 (y 1) + (single 4 6 (y 2) + (single 3 4 (y 3) + (single 3 5 (y 4) + (single 3 6 (y 5) + (single 2 3 (y 6) + (single 2 4 (y 7) + (single 2 5 (y 8) + (single 2 6 (y 9) + (single 1 2 (y 10) + (single 1 3 (y 11) + (single 1 4 (y 12) + (single 1 5 (y 13) + (single 1 6 (y 14) + (single 0 1 (y 15) + (single 0 2 (y 16) + (single 0 3 (y 17) + (single 0 4 (y 18) + (single 0 5 (y 19) + single 0 6 (y 20)))))))))))))))))))))) : Matrix (Fin 7) (Fin 7) K) p q =
        (1 : Matrix (Fin 7) (Fin 7) K) p q := fun p q => by rw [h]
  have d0 := hE 0 0
  have d1 := hE 1 1
  have d2 := hE 2 2
  have d3 := hE 3 3
  have d4 := hE 4 4
  have d5 := hE 5 5
  simp [Matrix.diagonal_mul, Matrix.add_apply] at d0 d1 d2 d3 d4 d5
  have ha : a = 1 := Units.ext (by simpa using d0)
  subst ha
  have hb : b = 1 := Units.ext (by simpa using d1)
  subst hb
  have hc : c = 1 := Units.ext (by simpa using d2)
  subst hc
  have hd : d = 1 := Units.ext (by simpa using d3)
  subst hd
  have he : e = 1 := Units.ext (by simpa using d4)
  subst he
  have hf : f = 1 := Units.ext (by simpa using d5)
  subst hf
  have o0 := hE 5 6
  have o1 := hE 4 5
  have o2 := hE 4 6
  have o3 := hE 3 4
  have o4 := hE 3 5
  have o5 := hE 3 6
  have o6 := hE 2 3
  have o7 := hE 2 4
  have o8 := hE 2 5
  have o9 := hE 2 6
  have o10 := hE 1 2
  have o11 := hE 1 3
  have o12 := hE 1 4
  have o13 := hE 1 5
  have o14 := hE 1 6
  have o15 := hE 0 1
  have o16 := hE 0 2
  have o17 := hE 0 3
  have o18 := hE 0 4
  have o19 := hE 0 5
  have o20 := hE 0 6
  simp [Matrix.diagonal_mul, Matrix.add_apply] at o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 o11 o12 o13 o14 o15 o16 o17 o18 o19 o20
  have hy0 : ∀ m, y m = 0 := by
    intro m
    fin_cases m
    exacts [o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13, o14, o15, o16, o17, o18, o19, o20]
  have hx0 : x = 0 := by
    funext m
    have h0 := hy0 m
    rw [hy] at h0
    rcases hε (e7a6PosRow m) (e7a6PosCol m) (hrc m) with h1 | h1 <;>
      (simp only [h1] at h0; simpa using h0)
  subst hx0
  refine ⟨e7a6TorusElt_one, ?_⟩
  simp only [Pi.zero_apply, pinnedX_zero, List.ofFn_const, List.prod_replicate, one_pow]

theorem e7a6Rep_injective : Function.Injective (e7a6Rep K) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hmat : e7a6Mat (g : ModGL Tag.E7 K) = 1 := congrArg Subtype.val hg
  have hfixv : ∀ k, ((g : ModGL Tag.E7 K) : Module.End K (RootModule Tag.E7 K)) (e7a6Vec K k) =
      e7a6Vec K k := by
    intro k
    rw [apply_e7a6Vec g.2, hmat]
    simp only [Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
  have hfix : ∀ m ∈ e7a6Module K,
      ((g : ModGL Tag.E7 K) : Module.End K (RootModule Tag.E7 K)) m = m := by
    intro m hm
    have e := eq_sum_of_mem_e7a6Module hm
    calc ((g : ModGL Tag.E7 K) : Module.End K (RootModule Tag.E7 K)) m =
        ((g : ModGL Tag.E7 K) : Module.End K (RootModule Tag.E7 K))
          (∑ k, m (e7a6Label k) • e7a6Vec K k) := by rw [← e]
      _ = ∑ k, m (e7a6Label k) • e7a6Vec K k := by
          rw [map_sum]
          exact Finset.sum_congr rfl fun k _ => by rw [map_smul, hfixv]
      _ = m := e.symm
  have hgS : (g : ModGL Tag.E7 K) ∈
      (subsystemGroup Tag.E7 K e7a6support : Set (ModGL Tag.E7 K)) := g.2
  rw [(subsystem_root_group_bruhat (τ := Tag.E7) (K := K) (A := e7a6support)).2.2.1] at hgS
  simp only [Set.mem_iUnion] at hgS
  obtain ⟨w, hw, hgw⟩ := hgS
  obtain ⟨_, ⟨b, hb, _, rfl, rfl⟩, v, hv, hgbv⟩ := hgw
  beta_reduce at hgbv
  have hbB : b ∈ borelGroup Tag.E7 K := subsystemBorel_le_borelGroup hb
  have hvU : v ∈ posUnipotent Tag.E7 K :=
    rootSpan_le_posUnipotent (fun _ h => inversionSet_pos h) hv
  have hvB : v ∈ borelGroup Tag.E7 K := Subgroup.mem_sup_right hvU
  have hvS : v ∈ subsystemGroup Tag.E7 K e7a6support :=
    parabolicLeviUnipotent_le_subsystemGroup (τ := Tag.E7) (K := K) (A := e7a6support)
      (rootSpan_mono (inversionSet_subset_parabolicPosRoots hw) hv)
  have hn : ∀ j, (canonicalRep (coxeterSystem Tag.E7) K w : Module.End K (RootModule Tag.E7 K))
      (e7a6Vec K j) = ((b⁻¹ * v⁻¹ : ModGL Tag.E7 K) : Module.End K (RootModule Tag.E7 K))
        (e7a6Vec K j) := by
    intro j
    have hn' : canonicalRep (coxeterSystem Tag.E7) K w = b⁻¹ * (g : ModGL Tag.E7 K) * v⁻¹ := by
      rw [← hgbv]
      group
    rw [hn', Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply,
      hfix _ (mem_e7a6Module_of_mem (inv_mem hvS) (e7a6Vec_mem j)), Units.val_mul,
      Module.End.mul_apply]
  have hprec : ∀ j j', e7a6Weight j' = w • e7a6Weight j → ¬j < j' := by
    intro j j' hj' hlt
    obtain ⟨ε, hε, hne⟩ := canonicalRep_rootVec_of_isRoot (K := K) w (isRoot_e7a6Weight j)
    have h0 := borel_apply_e7a6Vec_eq_zero (mul_mem (inv_mem hbB) (inv_mem hvB)) hlt
    rw [← hn j, ← rootVec_e7a6Weight, hne, ← hj', rootVec_e7a6Weight, Finsupp.smul_apply,
      e7a6Vec_apply, ite_eq_left rfl, smul_eq_mul, mul_one] at h0
    exact hε h0
  have hw1 : w = 1 := eq_one_of_smul_e7a6Weight hw (smul_e7a6Weight_eq_of_not_lt hw hprec)
  subst hw1
  have hv1 : v = 1 := by
    rw [inversionSet_one, show rootSpan Tag.E7 K (∅ : Set (Fin Tag.E7.rank → ℤ)) = ⊥ by
      simp [rootSpan]] at hv
    exact hv
  rw [canonicalRep_one, hv1, mul_one, mul_one] at hgbv
  have hb' : b ∈ (subsystemTorus Tag.E7 K e7a6support : Set (ModGL Tag.E7 K)) *
      (parabolicLeviUnipotent Tag.E7 K e7a6support : Set (ModGL Tag.E7 K)) :=
    (Set.ext_iff.mp (coe_subsystemBorel (τ := Tag.E7) (K := K) (A := e7a6support)) b).mp hb
  obtain ⟨t, ht, u, hu, rfl⟩ := hb'
  beta_reduce at hgbv
  have h1 := eq_one_of_e7a6Mat_mul_eq_one ht hu (by rw [hgbv]; exact hmat)
  refine Subtype.ext ?_
  rw [Subgroup.coe_one, ← hgbv, h1.1, h1.2, mul_one]


theorem e7a6Rep_bijective : Function.Bijective (e7a6Rep K) :=
  ⟨e7a6Rep_injective, e7a6Rep_surjective⟩

end CFSG.RankThree.PartOne.KE
