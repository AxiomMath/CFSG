module

public import CFSG.Quasithin.Vol2.Ch12Sec5L2G

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S125 S125St S125W Matrix

local notation "SL5" => Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)
local notation "MV" => Multiplicative (Fin 10 → ZMod 2)

namespace S125Ir

@[expose] def dOp (i j : Fin 5) : Matrix (Fin 10) (Fin 10) (ZMod 2) :=
  JonesParshall.wedgeMat (Matrix.transvection i j 1) + 1

@[expose] def rowOf : Fin 10 → Fin 5 := ![0, 0, 0, 0, 1, 1, 1, 2, 2, 3]

@[expose] def colOf : Fin 10 → Fin 5 := ![1, 2, 3, 4, 2, 3, 4, 3, 4, 4]

@[expose] def oth (k l : Fin 10) : Fin 5 :=
  if rowOf l = rowOf k ∨ rowOf l = colOf k then colOf l else rowOf l

@[expose] def step6 (k l : Fin 10) : Bool :=
  decide (1 ≤ k.val ∧ k.val ≤ 6 ∧ 1 ≤ l.val ∧ l.val ≤ 6 ∧ rowOf k ≠ rowOf l ∧ colOf k ≠ colOf l)

theorem dOp_mul_dOp : ∀ k l : Fin 10, step6 k l = true →
    dOp (rowOf l) (rowOf k) * dOp (colOf l) (colOf k) = Matrix.single l k 1 := by
  decide +kernel

@[expose] def topMask : Matrix (Fin 10) (Fin 10) (ZMod 2) :=
  Matrix.diagonal fun r => if 7 ≤ r.val then 1 else 0

theorem dOp_top : ∀ k l : Fin 10, 7 ≤ k.val → 7 ≤ l.val → k ≠ l →
    topMask * dOp (oth k l) (oth l k) = topMask * Matrix.single l k 1 := by
  decide +kernel

theorem dOp_top_apply {k l : Fin 10} (hk : 7 ≤ k.val) (hl : 7 ≤ l.val) (hkl : k ≠ l)
    (x : Fin 10 → ZMod 2) {r : Fin 10} (hr : 7 ≤ r.val) :
    (dOp (oth k l) (oth l k) *ᵥ x) r = (Pi.single l (x k) : Fin 10 → ZMod 2) r := by
  have h : ((topMask * dOp (oth k l) (oth l k)) *ᵥ x) r =
      ((topMask * Matrix.single l k (1 : ZMod 2)) *ᵥ x) r := by
    rw [dOp_top k l hk hl hkl]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, topMask, Matrix.mulVec_diagonal,
    Matrix.mulVec_diagonal, ite_eq_left hr, one_mul, one_mul] at h
  rw [h, Matrix.single_mulVec, one_mul]
  rfl

theorem step6_rows : ∀ k l : Fin 10, step6 k l = true →
    rowOf l ≠ rowOf k ∧ (rowOf l).val < 2 ∧ colOf l ≠ colOf k ∧ 2 ≤ (colOf k).val := by
  decide

theorem oth_props : ∀ k l : Fin 10, 7 ≤ k.val → 7 ≤ l.val → k ≠ l →
    oth k l ≠ oth l k ∧ 2 ≤ (oth l k).val := by
  decide

theorem exists_step6 : ∀ k : Fin 10, 1 ≤ k.val → k.val ≤ 6 → ∃ l : Fin 10, step6 k l = true := by
  decide

theorem reach6 : ∀ k l : Fin 10, 1 ≤ k.val → k.val ≤ 6 → 1 ≤ l.val → l.val ≤ 6 →
    k = l ∨ step6 k l = true ∨ (∃ m, step6 k m = true ∧ step6 m l = true) ∨
      ∃ m m', step6 k m = true ∧ step6 m m' = true ∧ step6 m' l = true := by
  decide

@[expose] def Inv2 (P : Subgroup MV) : Prop :=
  ∀ g : SL5, StabGam 2 g → ∀ x : Fin 10 → ZMod 2, Multiplicative.ofAdd x ∈ P →
    Multiplicative.ofAdd (JonesParshall.wedgeMat (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ x) ∈ P

theorem dOp_mem {P : Subgroup MV} (hP : Inv2 P) {i j : Fin 5} (hij : i ≠ j)
    (hs : j.val < 2 → i.val < 2) {x : Fin 10 → ZMod 2} (hx : Multiplicative.ofAdd x ∈ P) :
    Multiplicative.ofAdd (dOp i j *ᵥ x) ∈ P := by
  have hg : StabGam 2
      (⟨Matrix.transvection i j 1, Matrix.det_transvection_of_ne i j hij 1⟩ : SL5) := by
    intro r c hc hr
    change Matrix.transvection i j (1 : ZMod 2) r c = 0
    have hrc : r ≠ c := fun h => by rw [h] at hr; omega
    simp only [Matrix.transvection, Matrix.add_apply, Matrix.one_apply_ne hrc, zero_add,
      Matrix.single_apply]
    rw [ite_eq_right_iff]
    rintro ⟨rfl, rfl⟩
    have := hs hc
    omega
  have h1 := hP _ hg x hx
  rw [dOp, Matrix.add_mulVec, Matrix.one_mulVec, ofAdd_add]
  exact P.mul_mem h1 hx

theorem zmod2_eq_one {c : ZMod 2} (h : c ≠ 0) : c = 1 := by
  fin_cases c
  · exact absurd rfl h
  · rfl

theorem coordSub_le {P : Subgroup MV} {S : Finset (Fin 10)}
    (h : ∀ l ∈ S, Multiplicative.ofAdd (Pi.single l 1 : Fin 10 → ZMod 2) ∈ P) :
    coordSub S ≤ P := by
  intro z hz
  have hz' : Multiplicative.toAdd z = ∑ l ∈ S, Pi.single l (Multiplicative.toAdd z l) := by
    funext k
    rw [Finset.sum_apply]
    by_cases hk : k ∈ S
    · rw [Finset.sum_eq_single k (fun l _ hlk => Pi.single_eq_of_ne' hlk _)
        (fun h => absurd hk h), Pi.single_eq_same]
    · rw [hz k hk, Finset.sum_eq_zero fun l hl =>
        Pi.single_eq_of_ne' (fun (h : l = k) => hk (h ▸ hl)) _]
  rw [← ofAdd_toAdd z, hz', ofAdd_sum]
  refine P.prod_mem fun l hl => ?_
  by_cases h0 : Multiplicative.toAdd z l = 0
  · rw [h0, Pi.single_zero, ofAdd_zero]
    exact P.one_mem
  · rw [zmod2_eq_one h0]
    exact h l hl

theorem single_mem_coordSub {S : Finset (Fin 10)} {l : Fin 10} (hl : l ∈ S) :
    Multiplicative.ofAdd (Pi.single l 1 : Fin 10 → ZMod 2) ∈ coordSub S := by
  intro k hk
  rw [toAdd_ofAdd, Pi.single_eq_of_ne' (fun (h : l = k) => hk (h ▸ hl))]

theorem coordSub_ne {S S' : Finset (Fin 10)} {l : Fin 10} (hl : l ∈ S') (hl' : l ∉ S) :
    coordSub S ≠ coordSub S' := by
  intro h
  have h1 := single_mem_coordSub (S := S') hl
  rw [← h] at h1
  have := h1 l hl'
  rw [toAdd_ofAdd, Pi.single_eq_same] at this
  exact one_ne_zero this

theorem coordSub_mono {S S' : Finset (Fin 10)} (h : S ⊆ S') : coordSub S ≤ coordSub S' :=
  fun _ hx k hk => hx k fun hkS => hk (h hkS)

theorem coordSub_univ : coordSub Finset.univ = ⊤ :=
  eq_top_iff.2 fun _ _ k hk => absurd (Finset.mem_univ k) hk

theorem irr_bot {P : Subgroup MV} (hB : P ≤ coordSub {0}) : P = ⊥ ∨ P = coordSub {0} := by
  by_cases h : P = ⊥
  · exact Or.inl h
  · right
    refine le_antisymm hB (coordSub_le fun l hl => ?_)
    rw [Finset.mem_singleton] at hl
    subst hl
    obtain ⟨y, hy⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 h
    have hy0 : Multiplicative.toAdd (y : MV) ≠ 0 := fun h0 =>
      hy (Subtype.ext (by rw [Subgroup.coe_one, ← ofAdd_toAdd (y : MV), h0, ofAdd_zero]))
    have hk : Multiplicative.toAdd (y : MV) 0 ≠ 0 := by
      intro h0
      apply hy0
      funext k
      by_cases hk : k = 0
      · rw [hk, h0]
        rfl
      · exact hB y.2 k (by simpa using hk)
    have : (y : MV) = Multiplicative.ofAdd (Pi.single 0 1) := by
      apply Multiplicative.toAdd.injective
      funext k
      rw [toAdd_ofAdd]
      by_cases hk' : k = 0
      · rw [hk', Pi.single_eq_same, zmod2_eq_one hk]
      · rw [Pi.single_eq_of_ne hk', hB y.2 k (by simpa using hk')]
    rw [← this]
    exact y.2

theorem irr_mid {P : Subgroup MV} (hP : Inv2 P) (hA : coordSub {0} ≤ P)
    (hB : P ≤ coordSub {0, 1, 2, 3, 4, 5, 6}) :
    P = coordSub {0} ∨ P = coordSub {0, 1, 2, 3, 4, 5, 6} := by
  by_cases h : P ≤ coordSub {0}
  · exact Or.inl (le_antisymm h hA)
  · right
    refine le_antisymm hB ?_
    obtain ⟨y, hyP, hy⟩ := Set.not_subset.1 h
    obtain ⟨k, hk0, hk⟩ : ∃ k, k ∉ ({0} : Finset (Fin 10)) ∧ Multiplicative.toAdd y k ≠ 0 := by
      by_contra hc
      exact hy fun k hk => by
        by_contra h'
        exact hc ⟨k, hk, h'⟩
    have hk6 : k.val ≤ 6 := by
      by_contra hk6
      exact hk (hB hyP k (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        omega))
    have hk1 : 1 ≤ k.val := by
      rw [Finset.mem_singleton] at hk0
      have : k.val ≠ 0 := fun h => hk0 (Fin.ext h)
      omega
    have hstep : ∀ x : Fin 10 → ZMod 2, Multiplicative.ofAdd x ∈ P → ∀ k l : Fin 10,
        step6 k l = true → Multiplicative.ofAdd (Pi.single l (x k)) ∈ P := by
      intro x hx k l hkl
      obtain ⟨hr, hr2, hc, hc2⟩ := step6_rows k l hkl
      have h1 := dOp_mem hP hc (fun h => absurd h (by omega)) hx
      have h2 := dOp_mem hP hr (fun _ => hr2) h1
      rwa [Matrix.mulVec_mulVec, dOp_mul_dOp k l hkl, Matrix.single_mulVec, one_mul] at h2
    have hR : ∀ k l : Fin 10, Multiplicative.ofAdd (Pi.single k 1 : Fin 10 → ZMod 2) ∈ P →
        step6 k l = true → Multiplicative.ofAdd (Pi.single l 1 : Fin 10 → ZMod 2) ∈ P := by
      intro k l hk hkl
      have := hstep _ hk k l hkl
      rwa [Pi.single_eq_same] at this
    obtain ⟨l₀, hl₀⟩ := exists_step6 k hk1 hk6
    have h₀ : Multiplicative.ofAdd (Pi.single l₀ 1 : Fin 10 → ZMod 2) ∈ P := by
      have := hstep (Multiplicative.toAdd y) (by rwa [ofAdd_toAdd]) k l₀ hl₀
      rwa [zmod2_eq_one hk] at this
    have hl₀' := step6_rows k l₀ hl₀
    have hl₀6 : 1 ≤ l₀.val ∧ l₀.val ≤ 6 := by
      have := hl₀
      simp only [step6, decide_eq_true_eq] at this
      exact ⟨this.2.2.1, this.2.2.2.1⟩
    refine coordSub_le fun l hl => ?_
    by_cases hl0 : l = 0
    · rw [hl0]
      exact hA (single_mem_coordSub (Finset.mem_singleton_self 0))
    · have hl1 : 1 ≤ l.val := by
        have : l.val ≠ 0 := fun h => hl0 (Fin.ext h)
        omega
      have hl6 : l.val ≤ 6 := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hl
        rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      rcases reach6 l₀ l hl₀6.1 hl₀6.2 hl1 hl6 with h | h | ⟨m, h1, h2⟩ | ⟨m, m', h1, h2, h3⟩
      · rw [← h]
        exact h₀
      · exact hR _ _ h₀ h
      · exact hR _ _ (hR _ _ h₀ h1) h2
      · exact hR _ _ (hR _ _ (hR _ _ h₀ h1) h2) h3

theorem irr_top {P : Subgroup MV} (hP : Inv2 P) (hA : coordSub {0, 1, 2, 3, 4, 5, 6} ≤ P) :
    P = coordSub {0, 1, 2, 3, 4, 5, 6} ∨ P = ⊤ := by
  by_cases h : P ≤ coordSub {0, 1, 2, 3, 4, 5, 6}
  · exact Or.inl (le_antisymm h hA)
  · right
    have h7 : ∀ k : Fin 10, 7 ≤ k.val → k ∉ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 10)) := by
      intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    have hstep : ∀ x : Fin 10 → ZMod 2, Multiplicative.ofAdd x ∈ P → ∀ k l : Fin 10,
        7 ≤ k.val → 7 ≤ l.val → k ≠ l → Multiplicative.ofAdd (Pi.single l (x k)) ∈ P := by
      intro x hx k l hk hl hkl
      obtain ⟨hne, h2⟩ := oth_props k l hk hl hkl
      have h1 := dOp_mem hP hne (fun h => absurd h (by omega)) hx
      have hz : Multiplicative.ofAdd (dOp (oth k l) (oth l k) *ᵥ x - Pi.single l (x k)) ∈ P := by
        refine hA fun r hr => ?_
        have hr7 : 7 ≤ r.val := by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hr
          omega
        rw [toAdd_ofAdd, Pi.sub_apply, sub_eq_zero]
        exact dOp_top_apply hk hl hkl x hr7
      have e : Multiplicative.ofAdd (Pi.single l (x k)) =
          Multiplicative.ofAdd (dOp (oth k l) (oth l k) *ᵥ x) *
            (Multiplicative.ofAdd (dOp (oth k l) (oth l k) *ᵥ x - Pi.single l (x k)))⁻¹ := by
        apply Multiplicative.toAdd.injective
        simp only [toAdd_ofAdd, toAdd_mul, toAdd_inv]
        abel
      rw [e]
      exact P.mul_mem h1 (P.inv_mem hz)
    obtain ⟨y, hyP, hy⟩ := Set.not_subset.1 h
    obtain ⟨k, hk0, hk⟩ : ∃ k, k ∉ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 10)) ∧
        Multiplicative.toAdd y k ≠ 0 := by
      by_contra hc
      exact hy fun k hk => by
        by_contra h'
        exact hc ⟨k, hk, h'⟩
    have hk7 : 7 ≤ k.val := by
      by_contra hk7
      apply hk0
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    obtain ⟨l, hl7, hkl⟩ : ∃ l : Fin 10, 7 ≤ l.val ∧ k ≠ l := by
      by_cases hk8 : k = 8
      · exact ⟨9, by decide, by rw [hk8]; decide⟩
      · exact ⟨8, by decide, hk8⟩
    have hl : Multiplicative.ofAdd (Pi.single l 1 : Fin 10 → ZMod 2) ∈ P := by
      have := hstep (Multiplicative.toAdd y) (by rwa [ofAdd_toAdd]) k l hk7 hl7 hkl
      rwa [zmod2_eq_one hk] at this
    rw [eq_top_iff, ← coordSub_univ]
    refine coordSub_le fun m _ => ?_
    by_cases hm : m.val ≤ 6
    · refine hA (single_mem_coordSub ?_)
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    · by_cases hml : m = l
      · rw [hml]
        exact hl
      · have := hstep _ hl l m hl7 (by omega) (Ne.symm hml)
        rwa [Pi.single_eq_same] at this

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

@[expose] noncomputable def coordOf (F : Frame125 T L V) (W : Subgroup G) : Subgroup MV :=
  (W.subgroupOf V).map F.e.toMonoidHom

omit [Finite G] in
theorem mem_coordOf {F : Frame125 T L V} {W : Subgroup G} {y : MV} :
    y ∈ coordOf F W ↔ ((F.e.symm y : ↥V) : G) ∈ W := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    have hv' : (v : G) ∈ W := hv
    change ((F.e.symm (F.e v) : ↥V) : G) ∈ W
    rwa [MulEquiv.symm_apply_apply]
  · intro h
    exact ⟨F.e.symm y, Subgroup.mem_subgroupOf.2 h, MulEquiv.apply_symm_apply _ _⟩

omit [Finite G] in
theorem coordOf_sub (F : Frame125 T L V) (S : Finset (Fin 10)) :
    coordOf F (F.sub S) = coordSub S := by
  ext y
  rw [mem_coordOf, mem_sub_iff, MulEquiv.apply_symm_apply]
  rfl

omit [Finite G] in
theorem coordOf_V (F : Frame125 T L V) : coordOf F V = ⊤ :=
  eq_top_iff.2 fun y _ => mem_coordOf.2 (F.e.symm y).2

omit [Finite G] in
theorem coordOf_bot (F : Frame125 T L V) : coordOf F ⊥ = ⊥ := by
  ext y
  rw [mem_coordOf, Subgroup.mem_bot, Subgroup.mem_bot]
  constructor
  · intro h
    have h1 : F.e.symm y = 1 := Subtype.ext h
    rw [← F.e.apply_symm_apply y, h1, map_one]
  · intro h
    rw [h, map_one]
    rfl

omit [Finite G] in
theorem coordOf_le_iff (F : Frame125 T L V) {W W' : Subgroup G} (hW : W ≤ V) :
    coordOf F W ≤ coordOf F W' ↔ W ≤ W' := by
  constructor
  · intro h g hg
    have h1 : F.e ⟨g, hW hg⟩ ∈ coordOf F W' :=
      h (mem_coordOf.2 (by rw [MulEquiv.symm_apply_apply]; exact hg))
    rw [mem_coordOf, MulEquiv.symm_apply_apply] at h1
    exact h1
  · intro h y hy
    exact mem_coordOf.2 (h (mem_coordOf.1 hy))

omit [Finite G] in
theorem eq_of_coordOf_eq (F : Frame125 T L V) {W W' : Subgroup G} (hW : W ≤ V) (hW' : W' ≤ V)
    (h : coordOf F W = coordOf F W') : W = W' :=
  le_antisymm ((coordOf_le_iff F hW).1 h.le) ((coordOf_le_iff F hW').1 h.ge)

omit [Finite G] in
theorem inv2_coordOf (F : Frame125 T L V) {X W : Subgroup G} (hX : F.IsStab X 2)
    (hXW : X ≤ Subgroup.normalizer (W : Set G)) : Inv2 (coordOf F W) := by
  intro g hg x hx
  rw [mem_coordOf] at hx ⊢
  have hhX : ((F.γ.symm g : ↥(autOn L V)) : MulAut ↥V) ∈ autOn X V :=
    (hX.2 _).2 (by rw [MulEquiv.apply_symm_apply]; exact hg)
  obtain ⟨m, hm, hmX, hmh⟩ := mem_autOn_iff_exists.mp hhX
  have hw := (Subgroup.mem_normalizer_iff.1 (hXW hmX) _).1 hx
  have key : F.e.symm (Multiplicative.ofAdd (JonesParshall.wedgeMat
      (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ x)) =
      ((F.γ.symm g : ↥(autOn L V)) : MulAut ↥V) (F.e.symm (Multiplicative.ofAdd x)) := by
    apply F.e.injective
    rw [MulEquiv.apply_symm_apply, F.wedge, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply,
      toAdd_ofAdd, S125ZV.wedgeRep_apply]
  rw [key, ← hmh]
  exact hw

omit [Finite G] in
theorem le_normalizer_sub [Finite G] (F : Frame125 T L V) {X : Subgroup G} (hX : F.IsStab X 2)
    (hXV : X ≤ Subgroup.normalizer (V : Set G)) {S : Finset (Fin 10)}
    (hS : ∀ g : SL5, StabGam 2 g →
      CoordFix S (JonesParshall.wedgeMat (g : Matrix (Fin 5) (Fin 5) (ZMod 2)))) :
    X ≤ Subgroup.normalizer ((F.sub S : Subgroup G) : Set G) := by
  intro m hm
  have hmA : conjAct V ⟨m, hXV hm⟩ ∈ autOn X V :=
    mem_autOn_iff_exists.mpr ⟨m, hXV hm, hm, rfl⟩
  set h : ↥(autOn L V) := ⟨_, hX.1 hmA⟩
  have hfix := (mapsTo_sub_iff F S h).2 (hS _ ((hX.2 h).1 hmA))
  apply mem_normalizer_of_conj_le
  intro w hw
  exact hfix ⟨w, sub_le F S hw⟩ hw

theorem coordFix_V7 : ∀ g : SL5, StabGam 2 g →
    CoordFix {0, 1, 2, 3, 4, 5, 6} (JonesParshall.wedgeMat (g : Matrix (Fin 5) (Fin 5) (ZMod 2))) :=
  fun _ hg => coordFix_V7_of hg

theorem part1_irr (h1222 : Stmt12_2_2) (F : Frame125 T L V) (hH : Hyp125 G T L V) :
    IrrSection (mi T L F.V1) ⊥ F.V1 ∧ IrrSection (mi T L F.V1) F.V1 F.V7 ∧
      IrrSection (mi T L F.V1) F.V7 V := by
  have hf := S125Ex.Facts125.of h1222 hH
  have hst := isStab_V1 F hf.normalizes hf.T_le
  have hXV : mi T L F.V1 ≤ Subgroup.normalizer (V : Set G) :=
    inf_le_left.trans (sup_le hf.normalizes hf.T_le)
  have hX1 : mi T L F.V1 ≤ Subgroup.normalizer ((F.V1 : Subgroup G) : Set G) := inf_le_right
  have hX7 : mi T L F.V1 ≤ Subgroup.normalizer ((F.V7 : Subgroup G) : Set G) :=
    le_normalizer_sub F hst hXV coordFix_V7
  have hXb : mi T L F.V1 ≤ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := by
    intro m _
    rw [Subgroup.mem_normalizer_iff]
    intro w
    simp only [Subgroup.mem_bot]
    constructor
    · rintro rfl
      group
    · intro h
      have := congrArg (fun z => m⁻¹ * z * m) h
      simpa [mul_assoc] using this
  have h1V : F.V1 ≤ V := sub_le F _
  have h7V : F.V7 ≤ V := sub_le F _
  have c1 : coordOf F F.V1 = coordSub {0} := coordOf_sub F _
  have c7 : coordOf F F.V7 = coordSub {0, 1, 2, 3, 4, 5, 6} := coordOf_sub F _
  have h17 : F.V1 ≤ F.V7 := by
    rw [← coordOf_le_iff F h1V, c1, c7]
    exact coordSub_mono (by decide)
  refine ⟨⟨?_, hXb, hX1, fun W hW1 hW2 hXW => ?_⟩, ⟨?_, hX1, hX7, fun W hW1 hW2 hXW => ?_⟩,
    ⟨?_, hX7, hXV, fun W hW1 hW2 hXW => ?_⟩⟩
  · refine lt_of_le_of_ne bot_le fun h => ?_
    have := congrArg (coordOf F) h
    rw [coordOf_bot, c1] at this
    have h1 := single_mem_coordSub (S := {0}) (l := 0) (Finset.mem_singleton_self 0)
    rw [← this, Subgroup.mem_bot] at h1
    have h2 := congrArg (fun z : MV => Multiplicative.toAdd z 0) h1
    simp at h2
  · have hWV : W ≤ V := hW2.trans h1V
    have hc : coordOf F W ≤ coordSub {0} := by
      rw [← c1]
      exact (coordOf_le_iff F hWV).2 hW2
    rcases irr_bot hc with h | h
    · left
      exact eq_of_coordOf_eq F hWV bot_le (h.trans (coordOf_bot F).symm)
    · right
      exact eq_of_coordOf_eq F hWV h1V (h.trans c1.symm)
  · refine lt_of_le_of_ne h17 fun h => ?_
    have := congrArg (coordOf F) h
    rw [c1, c7] at this
    exact coordSub_ne (l := 1) (by decide) (by decide) this
  · have hWV : W ≤ V := hW2.trans h7V
    have hA : coordSub {0} ≤ coordOf F W := by
      rw [← c1]
      exact (coordOf_le_iff F h1V).2 hW1
    have hB : coordOf F W ≤ coordSub {0, 1, 2, 3, 4, 5, 6} := by
      rw [← c7]
      exact (coordOf_le_iff F hWV).2 hW2
    rcases irr_mid (inv2_coordOf F hst hXW) hA hB with h | h
    · left
      exact eq_of_coordOf_eq F hWV h1V (h.trans c1.symm)
    · right
      exact eq_of_coordOf_eq F hWV h7V (h.trans c7.symm)
  · refine lt_of_le_of_ne h7V fun h => ?_
    have := congrArg (coordOf F) h
    rw [c7, coordOf_V, ← coordSub_univ] at this
    exact coordSub_ne (l := 7) (Finset.mem_univ _) (by decide) this
  · have hA : coordSub {0, 1, 2, 3, 4, 5, 6} ≤ coordOf F W := by
      rw [← c7]
      exact (coordOf_le_iff F h7V).2 hW1
    rcases irr_top (inv2_coordOf F hst hXW) hA with h | h
    · left
      exact eq_of_coordOf_eq F hW2 h7V (h.trans c7.symm)
    · right
      exact eq_of_coordOf_eq F hW2 le_rfl (h.trans (coordOf_V F).symm)

end S125Ir

end CFSG.Quasithin.H13
