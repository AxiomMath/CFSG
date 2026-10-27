module

public import CFSG.Monster.B.GSide.HomotopyTyped
public import CFSG.Monster.B.TwoA.Amalgam.NativeChainFinal

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.GSide

open SimpleGraph CFSG.Monster.B.Recog CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Amalgam

section Generic

variable {V : Type*} {G : SimpleGraph V} {T : V → V → V → Prop}

theorem triLoop_eq_of_eq {x a b a' b' : V} (ha : a = a') (hb : b = b') (h₁ : G.Adj x a)
    (h₂ : G.Adj a b) (h₃ : G.Adj b x) (h₁' : G.Adj x a') (h₂' : G.Adj a' b')
    (h₃' : G.Adj b' x) : triLoop h₁ h₂ h₃ = triLoop h₁' h₂' h₃' := by
  subst ha hb
  rfl

theorem triLoop_map {V' : Type*} {G' : SimpleGraph V'} (f : G →g G') {x a b : V}
    (h₁ : G.Adj x a) (h₂ : G.Adj a b) (h₃ : G.Adj b x) :
    (triLoop h₁ h₂ h₃).map f = triLoop (f.map_adj h₁) (f.map_adj h₂) (f.map_adj h₃) := by
  simp [triLoop]

variable (G T) in
@[expose] def LocConst (x : V) : Prop :=
  ∀ (a b a' b' : V) (h₁ : G.Adj x a) (h₂ : G.Adj a b) (h₃ : G.Adj b x) (h₁' : G.Adj x a')
    (h₂' : G.Adj a' b') (h₃' : G.Adj b' x), ¬ T x a b → ¬ T x a' b' →
      HomotopicT T (triLoop h₁ h₂ h₃) (triLoop h₁' h₂' h₃')

variable (G T) in
@[expose] def EdgeConst (x a : V) : Prop :=
  ∀ (b b' : V) (h₁ : G.Adj x a) (h₂ : G.Adj a b) (h₃ : G.Adj b x) (h₂' : G.Adj a b')
    (h₃' : G.Adj b' x), ¬ T x a b → ¬ T x a b' →
      HomotopicT T (triLoop h₁ h₂ h₃) (triLoop h₁ h₂' h₃')

theorem LocConst.map (f : G ≃g G) (hf : ∀ a b c, T a b c ↔ T (f a) (f b) (f c)) {x : V}
    (h : LocConst G T x) {y : V} (hy : f x = y) : LocConst G T y := by
  subst hy
  intro a b a' b' h₁ h₂ h₃ h₁' h₂' h₃' hb hb'
  have e : ∀ u, f (f.symm u) = u := fun u => f.apply_symm_apply u
  have ex : f.symm (f x) = x := f.symm_apply_apply x
  have adj : ∀ {u w : V}, G.Adj u w → G.Adj (f.symm u) (f.symm w) := fun h =>
    f.symm.map_rel_iff.2 h
  have k₁ : G.Adj x (f.symm a) := ex ▸ adj h₁
  have k₂ : G.Adj (f.symm a) (f.symm b) := adj h₂
  have k₃ : G.Adj (f.symm b) x := ex ▸ adj h₃
  have k₁' : G.Adj x (f.symm a') := ex ▸ adj h₁'
  have k₂' : G.Adj (f.symm a') (f.symm b') := adj h₂'
  have k₃' : G.Adj (f.symm b') x := ex ▸ adj h₃'
  have kb : ¬ T x (f.symm a) (f.symm b) := fun ht => hb (by
    have := (hf _ _ _).1 ht
    rwa [e, e] at this)
  have kb' : ¬ T x (f.symm a') (f.symm b') := fun ht => hb' (by
    have := (hf _ _ _).1 ht
    rwa [e, e] at this)
  have H := (h _ _ _ _ k₁ k₂ k₃ k₁' k₂' k₃' kb kb').map f.toHom
    (fun a b c ht => (hf a b c).1 ht)
  rw [triLoop_map, triLoop_map] at H
  rw [triLoop_eq_of_eq (e a).symm (e b).symm h₁ h₂ h₃ _ _ _,
    triLoop_eq_of_eq (e a').symm (e b').symm h₁' h₂' h₃' _ _ _]
  exact H

theorem EdgeConst.map (f : G ≃g G) (hf : ∀ a b c, T a b c ↔ T (f a) (f b) (f c)) {x a : V}
    (h : EdgeConst G T x a) {y c : V} (hy : f x = y) (hc : f a = c) : EdgeConst G T y c := by
  subst hy hc
  intro b b' h₁ h₂ h₃ h₂' h₃' hb hb'
  have e : ∀ u, f (f.symm u) = u := fun u => f.apply_symm_apply u
  have ex : f.symm (f x) = x := f.symm_apply_apply x
  have ea : f.symm (f a) = a := f.symm_apply_apply a
  have adj : ∀ {u w : V}, G.Adj u w → G.Adj (f.symm u) (f.symm w) := fun h =>
    f.symm.map_rel_iff.2 h
  have k₁ : G.Adj x a := by simpa [ex, ea] using adj h₁
  have k₂ : G.Adj a (f.symm b) := ea ▸ adj h₂
  have k₃ : G.Adj (f.symm b) x := ex ▸ adj h₃
  have k₂' : G.Adj a (f.symm b') := ea ▸ adj h₂'
  have k₃' : G.Adj (f.symm b') x := ex ▸ adj h₃'
  have kb : ¬ T x a (f.symm b) := fun ht => hb (by
    have := (hf _ _ _).1 ht
    rwa [e] at this)
  have kb' : ¬ T x a (f.symm b') := fun ht => hb' (by
    have := (hf _ _ _).1 ht
    rwa [e] at this)
  have H := (h _ _ k₁ k₂ k₃ k₂' k₃' kb kb').map f.toHom (fun a b c ht => (hf a b c).1 ht)
  rw [triLoop_map, triLoop_map] at H
  rw [triLoop_eq_of_eq rfl (e b).symm h₁ h₂ h₃ _ _ _,
    triLoop_eq_of_eq rfl (e b').symm h₁ h₂' h₃' _ _ _]
  exact H

end Generic

@[expose] def IsType1782
    (x y z : CVert) : Prop := IsCTriangle x y z ∧ triType x y z = 1782

theorem triSymm_isType1782 :
    TriSymm IsType1782 := by
  rintro x y z ⟨hT, ht⟩
  obtain ⟨h1, -, h3, -, -⟩ := triType_perm hT
  exact ⟨⟨⟨hT.2.2, hT.1.symm, hT.2.1.symm⟩, h3.trans ht⟩, ⟨⟨hT.2.1, hT.1, hT.2.2.symm⟩,
    h1.trans ht⟩⟩

theorem isType1782_cvMul
    (s : Shat) {x y z : CVert} (h : IsType1782 x y z) :
    IsType1782 (cvMul x s) (cvMul y s) (cvMul z s) :=
  ⟨⟨(cgraph_adj_cvMul x y s).2 h.1.1, (cgraph_adj_cvMul x z s).2 h.1.2.1,
    (cgraph_adj_cvMul y z s).2 h.1.2.2⟩, (triType_cvMul x y z s).trans h.2⟩

theorem isType1782_cvMul_iff
    (s : Shat) (x y z : CVert) :
    IsType1782 x y z ↔ IsType1782 (cvMul x s) (cvMul y s) (cvMul z s) := by
  refine ⟨isType1782_cvMul s, fun h => ?_⟩
  have := isType1782_cvMul s⁻¹ h
  rwa [cvMul_inv_cancel, cvMul_inv_cancel, cvMul_inv_cancel] at this

theorem exists_not_isType1782
    {x y : CVert} (h : cgraph.Adj x y) :
    ∃ z, cgraph.Adj y z ∧ cgraph.Adj z x ∧ ¬ IsType1782 x y z := by
  obtain ⟨u, hu, -, h1⟩ := exists_triangle_types h
  refine ⟨u 1, (hu 1).2, (hu 1).1.symm, fun h' => ?_⟩
  rw [h'.2] at h1
  exact absurd h1 (by norm_num)

@[expose] def BT2C1 :
    Prop := EdgeConst cgraph IsType1782 cv0 cw0

@[expose] def BT2C2 :
    Prop :=
  ∀ {p q p' q' : CVert}, cgraph.Adj cv0 p → cgraph.Adj p q → cgraph.Adj q cv0 →
    ¬ IsType1782 cv0 p q → cgraph.Adj cv0 p' → cgraph.Adj p' q' → cgraph.Adj q' cv0 →
      ¬ IsType1782 cv0 p' q' →
        Relation.ReflTransGen (fun a c => ∃ b, cgraph.Adj cv0 a ∧ cgraph.Adj a b ∧
          cgraph.Adj b cv0 ∧ ¬ IsType1782 cv0 a b ∧ cgraph.Adj cv0 c ∧ cgraph.Adj c b ∧
          ¬ IsType1782 cv0 c b) p p'

theorem isType1782_cvIso_iff
    (s : Shat) (a b c : CVert) :
    IsType1782 a b c ↔ IsType1782 (cvIso s a) (cvIso s b) (cvIso s c) :=
  isType1782_cvMul_iff s a b c

theorem hloc_of_bt2
    (h1 : BT2C1) (h2 : BT2C2) (x : CVert) : LocConst cgraph IsType1782 x := by
  have hedge : ∀ p, cgraph.Adj cv0 p → EdgeConst cgraph IsType1782 cv0 p := by
    intro p hp
    obtain ⟨s, hsv, hsp⟩ := cvMul_edge_transitive cgraph_adj_cv0_cw0 hp
    exact EdgeConst.map (cvIso s) (isType1782_cvIso_iff s) h1 hsv hsp
  have hv : LocConst cgraph IsType1782 cv0 := by
    intro a b a' b' k₁ k₂ k₃ k₁' k₂' k₃' kb kb'
    exact homotopicT_triLoop_of_chain triSymm_isType1782
      (fun h₁ h₂ h₃ h₂' h₃' hb hb' => hedge _ h₁ _ _ h₁ h₂ h₃ h₂' h₃' hb hb') h2
      k₁ k₂ k₃ k₁' k₂' k₃' kb kb'
  obtain ⟨s, hs⟩ := cvMul_transitive cv0 x
  exact LocConst.map (cvIso s) (isType1782_cvIso_iff s) hv hs

theorem bt2_nil_or_triLoop
    (h1 : BT2C1) (h2 : BT2C2) {x a₁ a₂ : CVert} (ha₁ : cgraph.Adj x a₁)
    (ha₂ : cgraph.Adj a₁ a₂) (ha₃ : cgraph.Adj a₂ x) (ha : ¬ IsType1782 x a₁ a₂)
    (W : cgraph.Walk x x) :
    HomotopicT IsType1782 W .nil ∨ HomotopicT IsType1782 W (triLoop ha₁ ha₂ ha₃) :=
  homotopicT_nil_or_triLoop triSymm_isType1782 (fun _ _ h => exists_not_isType1782 h)
    (fun h₁ h₂ h₃ h₁' h₂' h₃' hb hb' => hloc_of_bt2 h1 h2 _ _ _ _ _ h₁ h₂ h₃ h₁' h₂' h₃' hb hb')
    native_cgraph_triangulable ha₁ ha₂ ha₃ ha W

theorem bt2_exists_fiber_subset_pair
    (h1 : BT2C1) (h2 : BT2C2) {W : Type*} {H : SimpleGraph W}
    {f : H →g cgraph} (hf : IsCovering f) (ht : LiftsTrianglesT IsType1782 f) (a : W) :
    ∃ a', ∀ b, H.Reachable a b → f b = f a → b = a ∨ b = a' :=
  exists_fiber_subset_pair triSymm_isType1782 (fun _ _ h => exists_not_isType1782 h)
    (fun h₁ h₂ h₃ h₁' h₂' h₃' hb hb' => hloc_of_bt2 h1 h2 _ _ _ _ _ h₁ h₂ h₃ h₁' h₂' h₃' hb hb')
    native_cgraph_triangulable hf ht a

theorem bt2_completion_ker_le_two
    (h1 : BT2C1) (h2 : BT2C2) {Y : Type*} [Group Y]
    (φv : vStab cv0 →* Y) (φe : cvSetStab {cv0, cw0} →* Y)
    (φt : cvSetStab {cv0, cw0, cu 0} →* Y)
    (hve : ∀ a (ha : a ∈ vStab cv0) (hb : a ∈ cvSetStab {cv0, cw0}), φv ⟨a, ha⟩ = φe ⟨a, hb⟩)
    (hvt : ∀ a (ha : a ∈ vStab cv0) (hb : a ∈ cvSetStab {cv0, cw0, cu 0}),
      φv ⟨a, ha⟩ = φt ⟨a, hb⟩)
    (het : ∀ a (ha : a ∈ cvSetStab {cv0, cw0}) (hb : a ∈ cvSetStab {cv0, cw0, cu 0}),
      φe ⟨a, ha⟩ = φt ⟨a, hb⟩) :
    (∀ a : cvSetStab {cv0, cw0, cu 0}, (φt a, (a : Shat)) ∈ homGraph φv ⊔ homGraph φe) ∧
      (homGraph φv ⊔ homGraph φe).map (MonoidHom.snd Y Shat) = ⊤ ∧
      ∃ n ∈ homGraph φv ⊔ homGraph φe, n.2 = 1 ∧
        ∀ k ∈ homGraph φv ⊔ homGraph φe, k.2 = 1 → k = 1 ∨ k = n := by
  let _ : MulAction Shat CVert := cvLeftAction
  have hvw := cgraph_adj_cv0_cw0
  have hne : cv0 ≠ cw0 := hvw.ne
  have hu := cgraph_adj_cu 0
  have hmem : ∀ s : Shat,
      (cvMul cv0 s = cw0 ∧ cvMul cw0 s = cv0 ∧ cvMul (cu 0) s = cu 0) ∨
      (cvMul cv0 s = cw0 ∧ cvMul cw0 s = cu 0 ∧ cvMul (cu 0) s = cv0) →
        s⁻¹ ∈ cvSetStab {cv0, cw0, cu 0} := by
    rintro s (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
    · refine (cvSetStab _).inv_mem (mem_cvSetStab_triple ⟨?_, ?_, ?_⟩ ?_)
      · rw [h1]; exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
      · rw [h2]; exact Set.mem_insert _ _
      · rw [h3]; exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)
      · rintro y (rfl | rfl | rfl)
        · exact ⟨cw0, Set.mem_insert_of_mem _ (Set.mem_insert _ _), h2⟩
        · exact ⟨cv0, Set.mem_insert _ _, h1⟩
        · exact ⟨cu 0, Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl), h3⟩
    · refine (cvSetStab _).inv_mem (mem_cvSetStab_triple ⟨?_, ?_, ?_⟩ ?_)
      · rw [h1]; exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
      · rw [h2]; exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)
      · rw [h3]; exact Set.mem_insert _ _
      · rintro y (rfl | rfl | rfl)
        · exact ⟨cu 0, Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl), h3⟩
        · exact ⟨cv0, Set.mem_insert _ _, h1⟩
        · exact ⟨cw0, Set.mem_insert_of_mem _ (Set.mem_insert _ _), h2⟩
  refine tits_completion_ker_le_two triSymm_isType1782 (fun _ _ h => exists_not_isType1782 h)
    (fun h₁ h₂ h₃ h₁' h₂' h₃' hb hb' => hloc_of_bt2 h1 h2 _ _ _ _ _ h₁ h₂ h₃ h₁' h₂' h₃' hb hb')
    cgraph_connected.preconnected native_cgraph_triangulable
    (fun g a b h => (cgraph_adj_cvMul a b g⁻¹).2 h) hvw (fun y hy => ?_) ?_ (vStab cv0)
    (cvSetStab {cv0, cw0}) (fun g => ?_) (fun g => ?_) (fun _ : Unit => cu 0)
    (fun _ => cvSetStab {cv0, cw0, cu 0}) (fun _ g hg => ?_) (fun _ => ?_) (fun _ => ?_)
    (fun g a b c h => isType1782_cvMul g⁻¹ h) (fun y₁ y₂ k₁ k₁₂ k₂ ht => ?_) φv φe
    (fun _ => φt) hve (fun _ => hvt) (fun _ => het) |>.imp (fun h a => h () a) id
  ·
    obtain ⟨s, h1, h2⟩ := cvMul_edge_transitive hvw hy
    refine ⟨s⁻¹, ?_, ?_⟩
    · show cvMul cv0 s⁻¹⁻¹ = cv0
      rw [inv_inv, h1]
    · show cvMul cw0 s⁻¹⁻¹ = y
      rw [inv_inv, h2]
  ·
    obtain ⟨s, h1, h2⟩ := cvMul_edge_transitive hvw hvw.symm
    refine ⟨s⁻¹, ?_, ?_⟩
    · show cvMul cv0 s⁻¹⁻¹ = cw0
      rw [inv_inv, h1]
    · show cvMul cw0 s⁻¹⁻¹ = cv0
      rw [inv_inv, h2]
  ·
    show cvMul cv0 g = cv0 ↔ cvMul cv0 g⁻¹ = cv0
    refine ⟨cvMul_inv_eq_of_cvMul_eq, fun h => ?_⟩
    have h' := cvMul_inv_eq_of_cvMul_eq h
    rwa [inv_inv] at h'
  ·
    rw [← Subgroup.inv_mem_iff, mem_cvSetStab_pair hne]
    rfl
  ·
    have h := ((mem_cvSetStab.1 ((cvSetStab _).inv_mem hg)) cv0).2 (Set.mem_insert _ _)
    rcases h with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  ·
    obtain ⟨s, h1, h2, h3⟩ := exists_swap_of_isCTriangle ⟨hvw, hu.1, hu.2⟩
    refine ⟨s⁻¹, hmem s (Or.inl ⟨h1, h2, h3⟩), ?_, ?_⟩
    · show cvMul cv0 s⁻¹⁻¹ = cw0
      rw [inv_inv, h1]
    · show cvMul cw0 s⁻¹⁻¹ = cv0
      rw [inv_inv, h2]
  ·
    obtain ⟨s, h1, h2, h3⟩ := exists_cycle_of_isCTriangle ⟨hvw, hu.1, hu.2⟩
    refine ⟨s⁻¹, hmem s (Or.inr ⟨h1, h2, h3⟩), ?_, ?_, ?_⟩
    · show cvMul cv0 s⁻¹⁻¹ = cw0
      rw [inv_inv, h1]
    · show cvMul cw0 s⁻¹⁻¹ = cu 0
      rw [inv_inv, h2]
    · show cvMul (cu 0) s⁻¹⁻¹ = cv0
      rw [inv_inv, h3]
  ·
    obtain ⟨j, s, hs1, hs2, hs3⟩ := exists_triangle_orbit hvw cgraph_adj_cu triType_cu k₁ k₁₂ k₂
    have hj : j = 0 := by
      by_contra hj
      have hj1 : j = 1 := by
        fin_cases j
        · exact absurd rfl hj
        · rfl
      subst hj1
      have e := triType_cvMul cv0 cw0 (cu 1) s
      rw [hs1, hs2, hs3, triType_cu.2] at e
      rw [show (y₂ : CVert) = y₂ from rfl] at e
      have := ht.2
      rw [e] at this
      exact absurd this (by norm_num)
    subst hj
    refine ⟨(), s⁻¹, ?_, ?_, ?_⟩
    · show cvMul cv0 s⁻¹⁻¹ = cv0
      rw [inv_inv, hs1]
    · show cvMul cw0 s⁻¹⁻¹ = y₁
      rw [inv_inv, hs2]
    · show cvMul (cu 0) s⁻¹⁻¹ = y₂
      rw [inv_inv, hs3]

end CFSG.Monster.B.GSide
