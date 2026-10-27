module

public import CFSG.Quasithin.Recognition.Stroth.MoufangLittleGen

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Quasithin CFSG.GH74.BNPair CFSG.GH74.GLS.SP

open scoped Pointwise commutatorElement

variable {V : Type} [Fintype V] {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
  {n : ℕ} {D : Type} [Group D] [MulAction D V] [FaithfulSMul D V] [GraphAction D Γ]

@[expose] def rootD (t : ZMod (2 * n) → V) (i : ℤ) : Subgroup D :=
  if 0 < i then aptRoot D Γ n t i else aptRoot D Γ n t ((n : ℤ) - i)

@[expose] def rootL (t : ZMod (2 * n) → V) (i : ℤ) : Subgroup ↥(littleGroup D Γ n) :=
  (rootD (D := D) (Γ := Γ) (n := n) t i).subgroupOf (littleGroup D Γ n)

variable {t : ZMod (2 * n) → V}

theorem rootD_le_littleGroup (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n) (i : ℤ) :
    rootD (D := D) (Γ := Γ) (n := n) t i ≤ littleGroup D Γ n := by
  unfold rootD
  split_ifs
  · exact aptRoot_le_littleGroup ht (by omega) i
  · exact aptRoot_le_littleGroup ht (by omega) ((n : ℤ) - i)

theorem rootL_map_subtype (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n) (i : ℤ) :
    (rootL (D := D) (Γ := Γ) (n := n) t i).map (littleGroup D Γ n).subtype =
      rootD (D := D) (Γ := Γ) (n := n) t i :=
  Subgroup.map_subgroupOf_eq_of_le (rootD_le_littleGroup ht hn i)

theorem rootL_ne_bot (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n)
    (hP : CFSG.Geometry.GeneralizedPolygons.IsGeneralizedPolygon Γ n)
    (hT : CFSG.Geometry.GeneralizedPolygons.IsThick Γ) (hM : MoufangCondition D Γ n)
    {i : ℤ} (hi : IsRoot n i) : rootL (D := D) (Γ := Γ) (n := n) t i ≠ ⊥ := by
  intro hbot
  have hmap := rootL_map_subtype (D := D) (Γ := Γ) (n := n) (t := t) ht hn i
  have hbot' : rootD (D := D) (Γ := Γ) (n := n) t i = ⊥ := by
    rw [← hmap, hbot, Subgroup.map_bot]
  have hpos : 0 < i ∨ i < 0 := by
    rcases lt_or_gt_of_ne hi.1 with h | h
    · exact Or.inr h
    · exact Or.inl h
  rcases hpos with h | h
  · rw [rootD, if_pos h] at hbot'
    exact aptRoot_ne_bot ht hn hP hT hM i hbot'
  · rw [rootD, if_neg (by omega)] at hbot'
    exact aptRoot_ne_bot ht hn hP hT hM ((n : ℤ) - i) hbot'

theorem rootD_map_conj_of_fix {g : D} (hg : ∀ k : ℤ, g • apt t k = apt t k) (i : ℤ) :
    (rootD (D := D) (Γ := Γ) (n := n) t i).map (MulAut.conj g).toMonoidHom =
      rootD (D := D) (Γ := Γ) (n := n) t i := by
  have hfun : (fun j : ZMod (2 * n) => g • t j) = t := by
    funext j
    obtain ⟨k, rfl⟩ := ZMod.intCast_surjective j
    exact hg k
  unfold rootD
  split_ifs
  · rw [aptRoot_map_conj, hfun]
  · rw [aptRoot_map_conj, hfun]

theorem rootL_invariant (B N : Subgroup ↥(littleGroup D Γ n))
    (hfix : ∀ h ∈ B ⊓ N, ∀ k : ℤ,
      ((h : ↥(littleGroup D Γ n)) : D) • apt t k = apt t k)
    {i : ℤ} (_hi : IsRoot n i) {h : ↥(littleGroup D Γ n)} (hh : h ∈ B ⊓ N)
    {x : ↥(littleGroup D Γ n)}
    (hx : x ∈ rootL (D := D) (Γ := Γ) (n := n) t i) :
    h * x * h⁻¹ ∈ rootL (D := D) (Γ := Γ) (n := n) t i := by
  rw [rootL, Subgroup.mem_subgroupOf] at hx ⊢
  have hmap := rootD_map_conj_of_fix (D := D) (Γ := Γ) (n := n) (t := t)
    (g := (h : D)) (hfix h hh) i
  have hmem : (MulAut.conj (h : D)) (x : D) ∈
      (rootD (D := D) (Γ := Γ) (n := n) t i).map (MulAut.conj (h : D)).toMonoidHom :=
    ⟨x, hx, rfl⟩
  rw [hmap] at hmem
  simpa [MulAut.conj_apply, mul_assoc] using hmem

private theorem mem_iSup_rootL_iff (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n) (S : Set ℤ)
    {x : ↥(littleGroup D Γ n)} :
    x ∈ ⨆ k ∈ S, rootL (D := D) (Γ := Γ) (n := n) t k ↔
      (x : D) ∈ ⨆ k ∈ S, rootD (D := D) (Γ := Γ) (n := n) t k := by
  have hmap : (⨆ k ∈ S, rootL (D := D) (Γ := Γ) (n := n) t k).map
        (littleGroup D Γ n).subtype =
      ⨆ k ∈ S, rootD (D := D) (Γ := Γ) (n := n) t k := by
    simp_rw [Subgroup.map_iSup, rootL_map_subtype ht hn]
  constructor
  · intro hx
    have hx' : (x : D) ∈ (⨆ k ∈ S, rootL (D := D) (Γ := Γ) (n := n) t k).map
        (littleGroup D Γ n).subtype := ⟨x, hx, rfl⟩
    rwa [hmap] at hx'
  · intro hx
    have hx' : (x : D) ∈ (⨆ k ∈ S, rootL (D := D) (Γ := Γ) (n := n) t k).map
        (littleGroup D Γ n).subtype := by rwa [hmap]
    obtain ⟨y, hy, hyx⟩ := hx'
    have : y = x := Subtype.ext hyx
    rwa [this] at hy

theorem rootL_commutator_le (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n)
    (hP : CFSG.Geometry.GeneralizedPolygons.IsGeneralizedPolygon Γ n)
    (hT : CFSG.Geometry.GeneralizedPolygons.IsThick Γ) (hM : MoufangCondition D Γ n)
    {i j : ℤ} (hi : 1 ≤ i) (hij : i < j) (hjn : j < i + (n : ℤ)) :
    ⁅rootL (D := D) (Γ := Γ) (n := n) t i, rootL (D := D) (Γ := Γ) (n := n) t j⁆ ≤
      ⨆ k ∈ Set.Ioo i j, rootL (D := D) (Γ := Γ) (n := n) t k := by
  intro x hx
  have hP1 : ∀ u ∈ aptRoot D Γ n t i, ∀ v ∈ aptRoot D Γ n t j,
      u * v * u⁻¹ * v⁻¹ ∈ ⨆ k ∈ Set.Ioo i j, aptRoot D Γ n t k := by
    have h := (moufangTitsAxioms n) V Γ D hn hP hT hM t ht
    exact h.2.1 i j hij hjn
  have hxD : (x : D) ∈ ⁅rootD (D := D) (Γ := Γ) (n := n) t i,
      rootD (D := D) (Γ := Γ) (n := n) t j⁆ := by
    have hmap : (⁅rootL (D := D) (Γ := Γ) (n := n) t i,
        rootL (D := D) (Γ := Γ) (n := n) t j⁆).map (littleGroup D Γ n).subtype =
        ⁅rootD (D := D) (Γ := Γ) (n := n) t i,
          rootD (D := D) (Γ := Γ) (n := n) t j⁆ := by
      rw [Subgroup.map_commutator, rootL_map_subtype ht hn, rootL_map_subtype ht hn]
    rw [← hmap]
    exact ⟨x, hx, rfl⟩
  have hleD : ⁅rootD (D := D) (Γ := Γ) (n := n) t i,
      rootD (D := D) (Γ := Γ) (n := n) t j⁆ ≤
      ⨆ k ∈ Set.Ioo i j, rootD (D := D) (Γ := Γ) (n := n) t k := by
    have hsup : (⨆ k ∈ Set.Ioo i j, rootD (D := D) (Γ := Γ) (n := n) t k) =
        ⨆ k ∈ Set.Ioo i j, aptRoot D Γ n t k := by
      exact biSup_congr fun k hk => by
        rw [rootD, if_pos (by have := Set.mem_Ioo.1 hk; omega)]
    rw [hsup]
    refine Subgroup.commutator_le.2 fun u hu v hv => ?_
    rw [rootD, if_pos (by omega)] at hu
    rw [rootD, if_pos (by omega)] at hv
    rw [commutatorElement_def]
    exact hP1 u hu v hv
  exact (mem_iSup_rootL_iff ht hn (Set.Ioo i j)).mpr (hleD hxD)

@[expose] noncomputable def rootU (t : ZMod (2 * n) → V) :
    Subgroup ↥(littleGroup D Γ n) :=
  ⨆ k ∈ intList (1 : ℤ) (n : ℤ), rootL (D := D) (Γ := Γ) (n := n) t k

theorem rootU_coe (t : ZMod (2 * n) → V) (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n)
    (hP : CFSG.Geometry.GeneralizedPolygons.IsGeneralizedPolygon Γ n)
    (hT : CFSG.Geometry.GeneralizedPolygons.IsThick Γ) (hM : MoufangCondition D Γ n) :
    (rootU (D := D) (Γ := Γ) (n := n) t : Set ↥(littleGroup D Γ n)) =
      chainProd (rootL (D := D) (Γ := Γ) (n := n) t) (intList 1 n) := by
  have hC : OctComm (rootL (D := D) (Γ := Γ) (n := n) t) (n : ℤ) :=
    fun i j hi hij hjn =>
      Subgroup.commutator_le.mp (rootL_commutator_le ht hn hP hT hM hi hij (by omega))
  exact hC.carrier_eq (by omega) (by omega)

theorem rootL_le_rootU (t : ZMod (2 * n) → V) {k : ℤ} (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    rootL (D := D) (Γ := Γ) (n := n) t k ≤ rootU (D := D) (Γ := Γ) (n := n) t :=
  le_iSup₂_of_le k (mem_intList_iff.2 ⟨hk1, hkn⟩) le_rfl

theorem chainProd_rootL_subgroup (t : ZMod (2 * n) → V) (ht : IsPolygonApartment Γ n t)
    (hn : 3 ≤ n) (hP : CFSG.Geometry.GeneralizedPolygons.IsGeneralizedPolygon Γ n)
    (hT : CFSG.Geometry.GeneralizedPolygons.IsThick Γ) (hM : MoufangCondition D Γ n)
    {i j : ℤ} (hi : 1 ≤ i) (hij : i ≤ j) (hjn : j ≤ n) :
    ∃ V : Subgroup ↥(littleGroup D Γ n),
      (V : Set ↥(littleGroup D Γ n)) =
        chainProd (rootL (D := D) (Γ := Γ) (n := n) t) (intList i j) ∧
      V ≤ rootU t ∧
      (1 < i → ∀ x ∈ rootL (D := D) (Γ := Γ) (n := n) t (i - 1), ∀ v ∈ V,
        x * v * x⁻¹ ∈ V) ∧
      (j < n → ∀ x ∈ rootL (D := D) (Γ := Γ) (n := n) t (j + 1), ∀ v ∈ V,
        x * v * x⁻¹ ∈ V) := by
  have hC : OctComm (rootL (D := D) (Γ := Γ) (n := n) t) (n : ℤ) :=
    fun a b ha hab hbn =>
      (Subgroup.commutator_le.mp (rootL_commutator_le ht hn hP hT hM ha hab (by omega)))
  exact hC.exists_subgroup (U := rootU (D := D) (Γ := Γ) (n := n) t)
    (fun k hk1 hkn => rootL_le_rootU (D := D) (Γ := Γ) (n := n) t hk1 hkn) hi hjn

theorem chainProd_rootL_reverse (t : ZMod (2 * n) → V) (ht : IsPolygonApartment Γ n t)
    (hn : 3 ≤ n) (hP : CFSG.Geometry.GeneralizedPolygons.IsGeneralizedPolygon Γ n)
    (hT : CFSG.Geometry.GeneralizedPolygons.IsThick Γ) (hM : MoufangCondition D Γ n)
    {i j : ℤ} (hi : 1 ≤ i) (hij : i ≤ j) (hjn : j ≤ n) :
    chainProd (rootL (D := D) (Γ := Γ) (n := n) t) (intList i j) =
      chainProd (rootL (D := D) (Γ := Γ) (n := n) t) (intList i j).reverse := by
  have hC : OctComm (rootL (D := D) (Γ := Γ) (n := n) t) (n : ℤ) :=
    fun a b ha hab hbn =>
      (Subgroup.commutator_le.mp (rootL_commutator_le ht hn hP hT hM ha hab (by omega)))
  exact hC.reverse_eq hi hjn

theorem rootL_prod_unique (t : ZMod (2 * n) → V) (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n)
    (hP : CFSG.Geometry.GeneralizedPolygons.IsGeneralizedPolygon Γ n)
    (hT : CFSG.Geometry.GeneralizedPolygons.IsThick Γ) (hM : MoufangCondition D Γ n)
    {f g : ℤ → ↥(littleGroup D Γ n)}
    (hf : ∀ k ∈ intList 1 n, f k ∈ rootL (D := D) (Γ := Γ) (n := n) t k)
    (hg : ∀ k ∈ intList 1 n, g k ∈ rootL (D := D) (Γ := Γ) (n := n) t k)
    (heq : ((intList 1 n).map f).prod = ((intList 1 n).map g).prod) :
    ∀ k ∈ intList 1 n, f k = g k := by
  have hP2 := ((moufangTitsAxioms n) V Γ D hn hP hT hM t ht).2.2.1
  have hfD : ∀ k ∈ intList 1 n, (f k : D) ∈ aptRoot D Γ n t k := by
    intro k hk
    have h := hf k hk
    rw [rootL, Subgroup.mem_subgroupOf] at h
    rwa [rootD, if_pos (by have := mem_intList_iff.1 hk; omega)] at h
  have hgD : ∀ k ∈ intList 1 n, (g k : D) ∈ aptRoot D Γ n t k := by
    intro k hk
    have h := hg k hk
    rw [rootL, Subgroup.mem_subgroupOf] at h
    rwa [rootD, if_pos (by have := mem_intList_iff.1 hk; omega)] at h
  have heqD : ((intList 1 n).map (fun k => (f k : D))).prod =
      ((intList 1 n).map (fun k => (g k : D))).prod := by
    have h := congrArg (fun x : ↥(littleGroup D Γ n) => (x : D)) heq
    simp only [Subgroup.val_list_prod, List.map_map, Function.comp_def] at h
    exact h
  have hlist : intList (0 + 1) (0 + (n : ℤ)) = intList 1 n := by
    rw [show (0 : ℤ) + 1 = 1 by norm_num, show (0 : ℤ) + (n : ℤ) = (n : ℤ) by ring]
  have hfD' : ∀ l ∈ intList (0 + 1) (0 + (n : ℤ)), (f l : D) ∈ aptRoot D Γ n t l := by
    intro l hl
    rw [hlist] at hl
    exact hfD l hl
  have hgD' : ∀ l ∈ intList (0 + 1) (0 + (n : ℤ)), (g l : D) ∈ aptRoot D Γ n t l := by
    intro l hl
    rw [hlist] at hl
    exact hgD l hl
  have heqD' : ((intList (0 + 1) (0 + (n : ℤ))).map (fun l => (f l : D))).prod =
      ((intList (0 + 1) (0 + (n : ℤ))).map (fun l => (g l : D))).prod := by
    rw [hlist]
    exact heqD
  intro k hk
  have hk' : k ∈ intList (0 + 1) (0 + (n : ℤ)) := by
    rw [hlist]
    exact hk
  exact Subtype.ext (hP2 0 (fun l => (f l : D)) (fun l => (g l : D))
    hfD' hgD' heqD' k hk')

theorem map_subtype_conjBy
    (m : ↥(littleGroup D Γ n)) (A : Subgroup ↥(littleGroup D Γ n)) :
    (CFSG.GH74.BNPair.conjBy m A).map (littleGroup D Γ n).subtype =
      CFSG.GH74.BNPair.conjBy (m : D) (A.map (littleGroup D Γ n).subtype) := by
  unfold CFSG.GH74.BNPair.conjBy
  rw [Subgroup.map_map, Subgroup.map_map]
  have e : ((littleGroup D Γ n).subtype.comp (MulAut.conj m⁻¹).toMonoidHom) =
      ((MulAut.conj (m : D)⁻¹).toMonoidHom.comp (littleGroup D Γ n).subtype) := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rw [e]

theorem conjBy_subgroupOf (m : ↥(littleGroup D Γ n))
    {A B : Subgroup D} (hA : A ≤ littleGroup D Γ n) (hB : B ≤ littleGroup D Γ n)
    (h : CFSG.GH74.BNPair.conjBy (m : D) A = B) :
    CFSG.GH74.BNPair.conjBy m (A.subgroupOf (littleGroup D Γ n)) =
      B.subgroupOf (littleGroup D Γ n) := by
  apply Subgroup.map_injective (littleGroup D Γ n).subtype_injective
  rw [map_subtype_conjBy, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hA, h,
    Subgroup.map_subgroupOf_eq_of_le hB]

theorem conjBy_eq_self_of_mem_cartan (B N : Subgroup ↥(littleGroup D Γ n))
    (hfix : ∀ h ∈ B ⊓ N, ∀ k : ℤ,
      ((h : ↥(littleGroup D Γ n)) : D) • apt t k = apt t k)
    {i : ℤ} (hi : IsRoot n i) {h : ↥(littleGroup D Γ n)} (hh : h ∈ B ⊓ N) :
    CFSG.GH74.BNPair.conjBy h (rootL (D := D) (Γ := Γ) (n := n) t i) =
      rootL (D := D) (Γ := Γ) (n := n) t i := by
  ext x
  rw [CFSG.GH74.BNPair.mem_conjBy_iff]
  constructor
  · intro hx
    have := rootL_invariant B N hfix hi ((B ⊓ N).inv_mem hh) hx
    simpa [mul_assoc] using this
  · intro hx
    exact rootL_invariant B N hfix hi hh hx

theorem conjBy_eq_of_same_weyl (B N : Subgroup ↥(littleGroup D Γ n))
    [(cartan B N).Normal]
    (hfix : ∀ h ∈ B ⊓ N, ∀ k : ℤ,
      ((h : ↥(littleGroup D Γ n)) : D) • apt t k = apt t k)
    {m : ↥N} {m₁ : ↥(littleGroup D Γ n)} (hm₁N : m₁ ∈ N)
    (hmW : (m : WeylGroup B N) = (⟨m₁, hm₁N⟩ : N)) {f : ℤ → ℤ}
    (hconj : ∀ i : ℤ, IsRoot n i →
      CFSG.GH74.BNPair.conjBy m₁ (rootL (D := D) (Γ := Γ) (n := n) t i) =
        rootL (D := D) (Γ := Γ) (n := n) t (f i)) :
    ∀ i : ℤ, IsRoot n i →
      CFSG.GH74.BNPair.conjBy (m : ↥(littleGroup D Γ n))
        (rootL (D := D) (Γ := Γ) (n := n) t i) =
        rootL (D := D) (Γ := Γ) (n := n) t (f i) := by
  let m₁N : ↥N := ⟨m₁, hm₁N⟩
  have hker : ((m * m₁N⁻¹ : ↥N) : WeylGroup B N) = 1 := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hmW]
    exact mul_inv_cancel _
  have hmem : (((m * m₁N⁻¹ : ↥N) : ↥(littleGroup D Γ n)) ∈ B ⊓ N) := by
    have h := (QuotientGroup.eq_one_iff (m * m₁N⁻¹)).mp hker
    rwa [cartan, Subgroup.mem_subgroupOf] at h
  have hmul : (m : ↥(littleGroup D Γ n)) =
      ((m * m₁N⁻¹ : ↥N) : ↥(littleGroup D Γ n)) * m₁ := by
    simp [m₁N, mul_assoc]
  intro i hi
  rw [hmul, CFSG.GH74.BNPair.conjBy_mul,
    conjBy_eq_self_of_mem_cartan B N hfix hi hmem]
  exact hconj i hi

end CFSG.Quasithin.Stroth
