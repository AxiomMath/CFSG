module

public import CFSG.Monster.B.Geometry.ChamberModel
public import CFSG.Monster.B.Geometry.PlaneModel

public section

namespace CFSG.Monster.B.Geometry

open CoxeterSystem CFSG.LieType.Chevalley.CosetBuilding

variable {ι : Type*} {M : CoxeterMatrix ι} {W : Type*} [Group W] {cs : CoxeterSystem M W}

namespace ChamberSystem

variable {F : Type*}

open _root_.Classical in
@[expose] noncomputable def ofThree (i₁ i₂ i₃ : ι) (r₁ r₂ r₃ : F → F → Prop)
    (h₁ : Equivalence r₁) (h₂ : Equivalence r₂) (h₃ : Equivalence r₃) : ChamberSystem ι F where
  adj i := if i = i₁ then r₁ else if i = i₂ then r₂ else if i = i₃ then r₃ else Eq
  equivalence i := by
    split_ifs
    · exact h₁
    · exact h₂
    · exact h₃
    · exact ⟨fun _ => rfl, fun h => h.symm, fun h h' => h.trans h'⟩

variable {i₁ i₂ i₃ : ι} {r₁ r₂ r₃ : F → F → Prop} {h₁ : Equivalence r₁} {h₂ : Equivalence r₂}
  {h₃ : Equivalence r₃}

theorem ofThree_adj₁ : (ofThree i₁ i₂ i₃ r₁ r₂ r₃ h₁ h₂ h₃).adj i₁ = r₁ := by
  simp [ofThree]

theorem ofThree_adj₂ (h : i₂ ≠ i₁) : (ofThree i₁ i₂ i₃ r₁ r₂ r₃ h₁ h₂ h₃).adj i₂ = r₂ := by
  simp [ofThree, h]

theorem ofThree_adj₃ (h : i₃ ≠ i₁) (h' : i₃ ≠ i₂) :
    (ofThree i₁ i₂ i₃ r₁ r₂ r₃ h₁ h₂ h₃).adj i₃ = r₃ := by
  simp [ofThree, h, h']

end ChamberSystem

section Model

variable (k : Type*) [Field k] (Z : Type*) (a b z : ι)

@[expose] noncomputable def planeProduct : ChamberSystem ι (PlaneFlag k × Z) :=
  ChamberSystem.ofThree a b z (fun p q => p.1.line = q.1.line ∧ p.2 = q.2)
    (fun p q => p.1.pt = q.1.pt ∧ p.2 = q.2) (fun p q => p.1 = q.1)
    ⟨fun _ => ⟨rfl, rfl⟩, fun h => ⟨h.1.symm, h.2.symm⟩,
      fun h h' => ⟨h.1.trans h'.1, h.2.trans h'.2⟩⟩
    ⟨fun _ => ⟨rfl, rfl⟩, fun h => ⟨h.1.symm, h.2.symm⟩,
      fun h h' => ⟨h.1.trans h'.1, h.2.trans h'.2⟩⟩
    ⟨fun _ => rfl, fun h => h.symm, fun h h' => h.trans h'⟩

variable {k Z a b z}

theorem planeProduct_adj_a :
    (planeProduct k Z a b z).adj a = fun p q => p.1.line = q.1.line ∧ p.2 = q.2 :=
  ChamberSystem.ofThree_adj₁

theorem planeProduct_adj_b (hab : a ≠ b) :
    (planeProduct k Z a b z).adj b = fun p q => p.1.pt = q.1.pt ∧ p.2 = q.2 :=
  ChamberSystem.ofThree_adj₂ hab.symm

theorem planeProduct_adj_z (haz : a ≠ z) (hbz : b ≠ z) :
    (planeProduct k Z a b z).adj z = fun p q => p.1 = q.1 :=
  ChamberSystem.ofThree_adj₃ haz.symm hbz.symm

theorem prodCongr_mem_typeAut (hab : a ≠ b) (haz : a ≠ z) (hbz : b ≠ z)
    (hι : ∀ i, i = a ∨ i = b ∨ i = z) {G : Equiv.Perm (PlaneFlag k)} (hG : G ∈ planeTypeAut k)
    (σ : Equiv.Perm Z) : Equiv.prodCongr G σ ∈ (planeProduct k Z a b z).typeAut := by
  intro i p q
  rcases hι i with rfl | rfl | rfl
  · rw [planeProduct_adj_a]
    simp only [Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, σ.injective.eq_iff]
    rw [(hG p.1 q.1).2]
  · rw [planeProduct_adj_b hab]
    simp only [Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, σ.injective.eq_iff]
    rw [(hG p.1 q.1).1]
  · rw [planeProduct_adj_z haz hbz]
    simp only [Equiv.prodCongr_apply, Prod.map_fst, G.injective.eq_iff]

end Model

section Paths

variable {k : Type*} [Field k]

theorem pathLE_three (u v : PlaneFlag k) :
    PathLE PlaneFlag.SamePt PlaneFlag.SameLine 3 u v := by
  by_cases h : u.IsOpposite v
  · have hne : u.pt ≠ v.pt := fun e => h.2 (e ▸ u.pt_le_line)
    have hN := ProjPlane.finrank_sup_of_ne u.finrank_pt v.finrank_pt hne
    let w₁ : PlaneFlag k := ⟨u.pt, u.pt ⊔ v.pt, u.finrank_pt, hN, le_sup_left⟩
    let w₂ : PlaneFlag k := ⟨v.pt, u.pt ⊔ v.pt, v.finrank_pt, hN, le_sup_right⟩
    exact .step (b := w₁) (Or.inl (show u.pt = w₁.pt from rfl))
      (.step (b := w₂) (Or.inr (show w₁.line = w₂.line from rfl))
        (.step (b := v) (Or.inl (show w₂.pt = v.pt from rfl)) (.refl 0 v)))
  · exact (pathLE_of_not_isOpposite h).mono (by omega)

variable {Z : Type*} {a b z : ι} (hab : a ≠ b)
include hab

theorem exists_gallery_of_pathLE {n : ℕ} {u v : PlaneFlag k}
    (h : PathLE PlaneFlag.SamePt PlaneFlag.SameLine n u v) (t : Z) :
    ∃ γ : List (ι × (PlaneFlag k × Z)), (planeProduct k Z a b z).IsGallery (u, t) γ ∧
      galleryEnd (u, t) γ = (v, t) ∧ (∀ i ∈ galleryType γ, i ∈ ({a, b} : Set ι)) ∧
      γ.length ≤ n := by
  induction h with
  | refl n u => exact ⟨[], trivial, rfl, by simp, Nat.zero_le _⟩
  | @step n u w v huw _ ih =>
    obtain ⟨γ, h1, h2, h3, h4⟩ := ih
    rcases huw with huw | huw
    · refine ⟨(b, (w, t)) :: γ, ⟨?_, h1⟩, h2, ?_, by simp; omega⟩
      · rw [planeProduct_adj_b hab]
        exact ⟨huw, rfl⟩
      · intro i hi
        simp only [galleryType_cons, List.mem_cons] at hi
        rcases hi with rfl | hi
        · simp
        · exact h3 i hi
    · refine ⟨(a, (w, t)) :: γ, ⟨?_, h1⟩, h2, ?_, by simp; omega⟩
      · rw [planeProduct_adj_a]
        exact ⟨huw, rfl⟩
      · intro i hi
        simp only [galleryType_cons, List.mem_cons] at hi
        rcases hi with rfl | hi
        · simp
        · exact h3 i hi

end Paths

section Building

variable {C : Type*} {δ : C → C → W} {k : Type*} [Field k] {Z : Type*} {a b z : ι}
  {f : C → PlaneFlag k × Z} (hf : IsChamberModel cs δ (planeProduct k Z a b z) f)

include hf

theorem planeProduct_dist_a {x y : C} :
    δ x y = cs.simple a ↔ x ≠ y ∧ (f x).1.line = (f y).1.line ∧ (f x).2 = (f y).2 := by
  rw [hf.2, planeProduct_adj_a]

theorem planeProduct_dist_b (hab : a ≠ b) {x y : C} :
    δ x y = cs.simple b ↔ x ≠ y ∧ (f x).1.pt = (f y).1.pt ∧ (f x).2 = (f y).2 := by
  rw [hf.2, planeProduct_adj_b hab]

theorem planeProduct_dist_z (haz : a ≠ z) (hbz : b ≠ z) {x y : C} :
    δ x y = cs.simple z ↔ x ≠ y ∧ (f x).1 = (f y).1 := by
  rw [hf.2, planeProduct_adj_z haz hbz]

theorem mem_residue_ab_iff (hab : a ≠ b) {x y : C} :
    y ∈ residue cs δ {a, b} x ↔ (f y).2 = (f x).2 := by
  rw [hf.mem_residue_iff]
  constructor
  · rintro ⟨γ, hγ, hJ, hend⟩
    rw [← hend]
    clear hend
    induction γ generalizing x with
    | nil => rfl
    | cons p γ ih =>
      obtain ⟨h1, h2⟩ := hγ
      have hp : p.1 = a ∨ p.1 = b := by simpa using hJ p.1 (by simp)
      have hp2 : p.2.2 = (f x).2 := by
        rcases hp with hp | hp
        · rw [hp, planeProduct_adj_a] at h1
          exact h1.2.symm
        · rw [hp, planeProduct_adj_b hab] at h1
          exact h1.2.symm
      obtain ⟨x', hx'⟩ := hf.1.2 p.2
      have := ih (x := x') (by rw [hx']; exact h2) (fun i hi => hJ i (by simp [hi]))
      rw [galleryEnd_cons, ← hx', this, hx', hp2]
  · intro h
    obtain ⟨γ, h1, h2, h3, -⟩ := exists_gallery_of_pathLE (z := z) hab
      (pathLE_three (f x).1 (f y).1) (f x).2
    refine ⟨γ, h1, h3, ?_⟩
    rw [h2, ← h]

theorem isPlaneFlagResidue_of_planeProduct (hab : a ≠ b) (x : C) :
    IsPlaneFlagResidue cs δ k a b x := by
  refine ⟨fun y => (f y).1, Or.inr ⟨⟨fun _ _ => trivial, fun y hy y' hy' h => ?_, fun u _ => ?_⟩,
    fun y hy y' hy' => ?_⟩⟩
  · have h2 : (f y).2 = (f y').2 := by
      rw [(mem_residue_ab_iff hf hab).mp hy, (mem_residue_ab_iff hf hab).mp hy']
    exact hf.1.1 (Prod.ext h h2)
  · obtain ⟨y, hy⟩ := hf.1.2 (u, (f x).2)
    refine ⟨y, (mem_residue_ab_iff hf hab).mpr (by rw [hy]), ?_⟩
    simp only [hy]
  · have h2 : (f y).2 = (f y').2 := by
      rw [(mem_residue_ab_iff hf hab).mp hy, (mem_residue_ab_iff hf hab).mp hy']
    rw [planeProduct_dist_a hf, planeProduct_dist_b hf hab]
    exact ⟨⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, h2⟩⟩,
      ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, h2⟩⟩⟩

theorem isModelResidue_of_planeProduct (hab : a ≠ b) (x : C) :
    IsModelResidue cs δ PlaneFlag.SameLine PlaneFlag.SamePt a b x (fun y => (f y).1) := by
  refine ⟨⟨fun _ _ => trivial, fun y hy y' hy' h => ?_, fun u _ => ?_⟩, fun y hy y' hy' => ?_⟩
  · have h2 : (f y).2 = (f y').2 := by
      rw [(mem_residue_ab_iff hf hab).mp hy, (mem_residue_ab_iff hf hab).mp hy']
    exact hf.1.1 (Prod.ext h h2)
  · obtain ⟨y, hy⟩ := hf.1.2 (u, (f x).2)
    refine ⟨y, (mem_residue_ab_iff hf hab).mpr (by rw [hy]), ?_⟩
    simp only [hy]
  · have h2 : (f y).2 = (f y').2 := by
      rw [(mem_residue_ab_iff hf hab).mp hy, (mem_residue_ab_iff hf hab).mp hy']
    rw [planeProduct_dist_a hf, planeProduct_dist_b hf hab]
    exact ⟨⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, h2⟩⟩,
      ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, h2⟩⟩⟩

theorem mem_panel_z_iff (haz : a ≠ z) (hbz : b ≠ z) {x y : C} :
    y ∈ panel cs δ z x ↔ (f y).1 = (f x).1 := by
  rw [panel, hf.mem_residue_iff, ChamberSystem.mem_residue_singleton, planeProduct_adj_z haz hbz]
  exact eq_comm

end Building

section Coxeter

theorem simple_mul_simple_comm {i j : ι} (hM : M i j = 2) :
    cs.simple i * cs.simple j = cs.simple j * cs.simple i := by
  have h2 := cs.simple_mul_simple_pow i j
  rw [hM, pow_two] at h2
  have := eq_inv_of_mul_eq_one_left h2
  rw [this, mul_inv_rev, cs.inv_simple, cs.inv_simple]

theorem mul_simple_comm_of_mem_parabolic {J : Set ι} {k : ι} (hk : ∀ j ∈ J, M j k = 2) {x : W}
    (hx : x ∈ cs.parabolic J) : x * cs.simple k = cs.simple k * x := by
  have hle : cs.parabolic J ≤ Subgroup.centralizer {cs.simple k} := by
    rw [cs.parabolic_le_iff]
    intro j hj
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact simple_mul_simple_comm (hk j hj)
  have := hle hx
  rw [Subgroup.mem_centralizer_singleton_iff] at this
  exact this

theorem not_isRightDescent_of_mem_parabolic {J : Set ι} {k : ι} (hk : k ∉ J) {x : W}
    (hx : x ∈ cs.parabolic J) : ¬cs.IsRightDescent x k := by
  intro h
  rw [← cs.isLeftDescent_inv_iff] at h
  exact hk ((simple_mem_parabolic_iff cs).mp
    (cs.simple_mem_parabolic_of_isLeftDescent (inv_mem hx) h))

theorem length_mul_simple_of_mem_parabolic {J : Set ι} {k : ι} (hk : k ∉ J) {x : W}
    (hx : x ∈ cs.parabolic J) : cs.length (x * cs.simple k) = cs.length x + 1 := by
  rcases cs.length_mul_simple x k with h | h
  · exact h
  · exact absurd (by rw [cs.isRightDescent_iff]; omega) (not_isRightDescent_of_mem_parabolic hk hx)

variable [Finite W] {a b z : ι} (hab : a ≠ b) (haz : a ≠ z) (hbz : b ≠ z)
  (hι : ∀ i, i = a ∨ i = b ∨ i = z) (hMab : M a b = 3) (hMaz : M a z = 2) (hMbz : M b z = 2)
include hab haz hbz hι hMab hMaz hMbz

theorem longest_eq_product :
    longest cs Set.univ = longest cs {a, b} * cs.simple z ∧
      cs.length (longest cs Set.univ) = 4 := by
  have hfin := finite_parabolic_pair (cs := cs) (i := a) (j := b) (by omega)
  have hL := isLongest_longest (cs := cs) {a, b}
  have hLlen : cs.length (longest cs {a, b}) = 3 := by
    rw [length_longest_pair hab (by omega), hMab]
  have hz : z ∉ ({a, b} : Set ι) := by
    rintro (h | h)
    · exact haz h.symm
    · exact hbz (Set.mem_singleton_iff.mp h).symm
  have hcomm : ∀ x ∈ cs.parabolic {a, b}, x * cs.simple z = cs.simple z * x :=
    fun x hx => mul_simple_comm_of_mem_parabolic (fun j hj => by
      rcases hj with rfl | hj
      · exact hMaz
      · rw [Set.mem_singleton_iff.mp hj]; exact hMbz) hx
  have hv : cs.length (longest cs {a, b} * cs.simple z) = 4 := by
    rw [length_mul_simple_of_mem_parabolic hz hL.1, hLlen]
  have hlong : IsLongest cs Set.univ (longest cs {a, b} * cs.simple z) := by
    refine isLongest_of_forall_isLeftDescent (by rw [cs.parabolic_univ]; trivial) fun i _ => ?_
    have hdesc : ∀ j ∈ ({a, b} : Set ι), cs.IsLeftDescent (longest cs {a, b} * cs.simple z) j := by
      intro j hj
      have h1 := hL.length_mul_left (cs.simple_mem_parabolic hj)
      rw [cs.length_simple, hLlen] at h1
      have h2 : cs.simple j * longest cs {a, b} ∈ cs.parabolic {a, b} :=
        mul_mem (cs.simple_mem_parabolic hj) hL.1
      change cs.length (cs.simple j * (longest cs {a, b} * cs.simple z)) <
        cs.length (longest cs {a, b} * cs.simple z)
      rw [← mul_assoc, length_mul_simple_of_mem_parabolic hz h2, hv]
      omega
    rcases hι i with rfl | rfl | rfl
    · exact hdesc i (by simp)
    · exact hdesc i (by simp)
    · change cs.length (cs.simple i * (longest cs {a, b} * cs.simple i)) <
        cs.length (longest cs {a, b} * cs.simple i)
      have e : cs.simple i * (longest cs {a, b} * cs.simple i) = longest cs {a, b} := by
        rw [hcomm _ hL.1, ← mul_assoc, cs.simple_mul_simple_self, one_mul]
      rw [e, hv, hLlen]
      omega
  have := hlong.eq_longest
  exact ⟨this.symm, by rw [← this, hv]⟩

end Coxeter

theorem exists_perm_pair {Z : Type*} {p q p₁ q₁ : Z} (h : p ≠ q) (h₁ : p₁ ≠ q₁) :
    ∃ σ : Equiv.Perm Z, σ p = p₁ ∧ σ q = q₁ := by
  classical
  have hq' : Equiv.swap p p₁ q ≠ p₁ := fun e =>
    h ((Equiv.swap p p₁).injective (e.trans (Equiv.swap_apply_left p p₁).symm)).symm
  refine ⟨Equiv.swap (Equiv.swap p p₁ q) q₁ * Equiv.swap p p₁, ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne hq'.symm h₁]
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]

section Building3

variable [Finite W] {C : Type*} {δ : C → C → W} (hδ : IsWeylDistanceBuilding cs δ)
  {k : Type*} [Field k] {Z : Type*} {a b z : ι} (hab : a ≠ b) (haz : a ≠ z) (hbz : b ≠ z)
  (hι : ∀ i, i = a ∨ i = b ∨ i = z) (hMab : M a b = 3) (hMaz : M a z = 2) (hMbz : M b z = 2)
  {f : C → PlaneFlag k × Z} (hf : IsChamberModel cs δ (planeProduct k Z a b z) f)
include hδ hab haz hbz hι hMab hMaz hMbz hf

omit [Finite W] in
theorem rig₂_of_planeProduct : Rig₂ cs δ := by
  intro i j hij x y hy hxy g hg hgy hfix
  have hM2 : ∀ {i j : ι}, i ≠ j → (i, j) ≠ (a, b) → (i, j) ≠ (b, a) → M i j = 2 := by
    intro i j hij h1 h2
    rcases hι i with rfl | rfl | rfl <;> rcases hι j with rfl | rfl | rfl
    all_goals first
      | exact absurd rfl hij
      | exact absurd rfl h1
      | exact absurd rfl h2
      | assumption
      | (rwa [M.symmetric])
  by_cases h1 : (i, j) = (a, b)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h1
    exact (isPlaneFlagResidue_of_planeProduct hf hij x).fix hδ hij hMab hy hxy hg hgy hfix
  by_cases h2 : (i, j) = (b, a)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2
    exact (isPlaneFlagResidue_of_planeProduct hf hab x).swap.fix hδ hij
      (by rw [M.symmetric]; exact hMab) hy hxy hg hgy hfix
  exact fix_residue_of_commute hδ hij (hM2 hij h1 h2) hg hfix

theorem opposite_of_planeProduct {x y : C} (hxy : δ x y = longest cs Set.univ) :
    (f x).1.IsOpposite (f y).1 ∧ (f x).2 ≠ (f y).2 := by
  obtain ⟨-, hlen⟩ := longest_eq_product hab haz hbz hι hMab hMaz hMbz (cs := cs)
  have hfin := finite_parabolic_pair (cs := cs) (i := a) (j := b) (by omega)
  refine ⟨?_, fun h => ?_⟩
  · by_contra hno
    obtain ⟨γ, h1, h2, -, h4⟩ := exists_gallery_of_pathLE (z := z) hab
      (pathLE_of_not_isOpposite hno) (f x).2
    have hγ : (planeProduct k Z a b z).IsGallery (f x) (γ ++ [(z, f y)]) := by
      refine (ChamberSystem.isGallery_append _ _ _).mpr ⟨h1, ?_⟩
      rw [h2]
      refine ⟨?_, trivial⟩
      rw [planeProduct_adj_z haz hbz]
    have := hf.length_le hδ hγ (by rw [galleryEnd_append, h2]; rfl)
    rw [hxy, hlen, List.length_append, List.length_singleton] at this
    omega
  · have hmem : y ∈ residue cs δ {a, b} x := (mem_residue_ab_iff hf hab).mpr h.symm
    have h3 := (isLongest_longest (cs := cs) {a, b}).2 _ (mem_parabolic_of_mem_residue hδ
      (self_mem_residue _ x) hmem)
    rw [hxy, hlen, length_longest_pair hab (by omega), hMab] at h3
    omega

theorem planeProduct_transitive (c d c₁ d₁ : C) (hcd : δ c d = longest cs Set.univ)
    (hcd₁ : δ c₁ d₁ = longest cs Set.univ) :
    ∃ g ∈ typeAut cs δ, g c = c₁ ∧ g d = d₁ := by
  obtain ⟨ho, hz⟩ := opposite_of_planeProduct hδ hab haz hbz hι hMab hMaz hMbz hf hcd
  obtain ⟨ho₁, hz₁⟩ := opposite_of_planeProduct hδ hab haz hbz hι hMab hMaz hMbz hf hcd₁
  obtain ⟨A, hA1, hA2⟩ := exists_planeGLPerm_of_isOpposite ho
  obtain ⟨A₁, hA₁1, hA₁2⟩ := exists_planeGLPerm_of_isOpposite ho₁
  obtain ⟨σ, hσ1, hσ2⟩ := exists_perm_pair hz hz₁
  set G : Equiv.Perm (PlaneFlag k) := (planeGLPerm A₁)⁻¹ * planeGLPerm A
  have hG : G ∈ planeTypeAut k :=
    mul_mem (inv_mem (planeGLPerm_mem_planeTypeAut A₁)) (planeGLPerm_mem_planeTypeAut A)
  have hG1 : G (f c).1 = (f c₁).1 := by
    simp only [G, Equiv.Perm.mul_apply, hA1, ← hA₁1, Equiv.Perm.inv_def, Equiv.symm_apply_apply]
  have hG2 : G (f d).1 = (f d₁).1 := by
    simp only [G, Equiv.Perm.mul_apply, hA2, ← hA₁2, Equiv.Perm.inv_def, Equiv.symm_apply_apply]
  have hGZ := prodCongr_mem_typeAut hab haz hbz hι hG σ
  refine ⟨hf.perm (Equiv.prodCongr G σ), hf.perm_mem_typeAut hGZ, hf.1.1 ?_, hf.1.1 ?_⟩
  · rw [hf.apply_perm]
    exact Prod.ext hG1 hσ1
  · rw [hf.apply_perm]
    exact Prod.ext hG2 hσ2

theorem planeProduct_realize (c d : C) (hcd : δ c d = longest cs Set.univ) (Ψ : C → C)
    (hΨ : IsWeylIsometry δ δ (foundation cs δ 2 c ∪ {d}) (foundation cs δ 2 c ∪ {d}) Ψ)
    (hΨc : Ψ c = c) (hΨd : Ψ d = d) :
    ∃ g ∈ typeAut cs δ, Set.EqOn g Ψ (foundation cs δ 2 c ∪ {d}) := by
  obtain ⟨ho, hz⟩ := opposite_of_planeProduct hδ hab haz hbz hι hMab hMaz hMbz hf hcd
  set X := foundation cs δ 2 c ∪ {d} with hX
  have hsub : ∀ J : Set ι, J.encard ≤ 2 → residue cs δ J c ⊆ X := fun J hJ =>
    (residue_subset_foundation hJ c).trans Set.subset_union_left
  have hpair : ∀ i j : ι, ({i, j} : Set ι).encard ≤ 2 := fun i j =>
    (Set.encard_insert_le _ _).trans (by rw [Set.encard_singleton]; norm_num)
  have hbij : ∀ J : Set ι, J.encard ≤ 2 → Set.BijOn Ψ (residue cs δ J c) (residue cs δ J c) :=
    fun J hJ => hΨ.bijOn_residue hδ hδ (Or.inl (self_mem_foundation 2 c)) hΨc (hsub J hJ)
      (hsub J hJ)
  have hiso : ∀ J : Set ι, J.encard ≤ 2 →
      IsTypeIso cs δ δ (residue cs δ J c) (residue cs δ J c) Ψ := fun J hJ =>
    (hΨ.mono (hsub J hJ) (hbij J hJ)).isTypeIso
  obtain ⟨G, hG, hG1, hG2⟩ := (isModelResidue_of_planeProduct hf hab c).exists_perm
    (fun _ => rfl) (fun _ => rfl) (hiso {a, b} (hpair a b))
  have hGmem : G ∈ planeTypeAut k := fun u v => ⟨hG2 u v, hG1 u v⟩
  have hzc : ∀ y, y ∈ panel cs δ z c ↔ (f y).1 = (f c).1 := fun y => mem_panel_z_iff hf haz hbz
  have hbz' := hbij {z} (by simp)
  let ez : (panel cs δ z c) ≃ Z := Equiv.ofBijective (fun y => (f y.1).2)
    ⟨fun y y' h => Subtype.ext (hf.1.1 (Prod.ext (((hzc y).mp y.2).trans ((hzc y').mp y'.2).symm)
      h)), fun t => by
      obtain ⟨y, hy⟩ := hf.1.2 ((f c).1, t)
      exact ⟨⟨y, (hzc y).mpr (by rw [hy])⟩, by simp only [hy]⟩⟩
  let σ : Equiv.Perm Z := ez.symm.trans ((hbz'.equiv Ψ).trans ez)
  have hσ : ∀ y (hy : y ∈ panel cs δ z c), σ (f y).2 = (f (Ψ y)).2 := by
    intro y hy
    have : ez.symm (f y).2 = ⟨y, hy⟩ := by
      rw [Equiv.symm_apply_eq]
      rfl
    change ez ((hbz'.equiv Ψ) (ez.symm (f y).2)) = _
    rw [this]
    rfl
  have hGZ := prodCongr_mem_typeAut hab haz hbz hι hGmem σ
  set g := hf.perm (Equiv.prodCongr G σ) with hg
  have hgmem := hf.perm_mem_typeAut hGZ
  have hgf : ∀ y, f (g y) = (G (f y).1, σ (f y).2) := fun y => by rw [hg, hf.apply_perm]; rfl
  have hcR : c ∈ residue cs δ {a, b} c := self_mem_residue _ c
  have hcP : c ∈ panel cs δ z c := self_mem_residue _ c
  have hσc : σ (f c).2 = (f c).2 := by rw [hσ c hcP, hΨc]
  have hGc : G (f c).1 = (f c).1 := by rw [hG c hcR, hΨc]
  have hagR : ∀ y ∈ residue cs δ {a, b} c, g y = Ψ y := by
    intro y hy
    refine hf.1.1 ?_
    rw [hgf, hG y hy, (mem_residue_ab_iff hf hab).mp hy, hσc,
      ← (mem_residue_ab_iff hf hab).mp ((hbij _ (hpair a b)).mapsTo hy)]
  have hagP : ∀ y ∈ panel cs δ z c, g y = Ψ y := by
    intro y hy
    refine hf.1.1 ?_
    rw [hgf, hσ y hy, (hzc y).mp hy, hGc, ← (hzc _).mp (hbz'.mapsTo hy)]
  have hagd : g d = Ψ d := by
    rw [hΨd]
    obtain ⟨p, hp⟩ := hf.1.2 ((f d).1, (f c).2)
    obtain ⟨q, hq⟩ := hf.1.2 ((f c).1, (f d).2)
    have hpR : p ∈ residue cs δ {a, b} c := (mem_residue_ab_iff hf hab).mpr (by rw [hp])
    have hqP : q ∈ panel cs δ z c := (hzc q).mpr (by rw [hq])
    have hpd : δ p d = cs.simple z := (planeProduct_dist_z hf haz hbz).mpr
      ⟨fun e => hz (by rw [← e, hp]), by rw [hp]⟩
    have hΨp : Ψ p = p := by
      have h1 : δ (Ψ p) d = cs.simple z := by
        rw [← hΨd, hΨ.2 p (hsub _ (hpair a b) hpR) d (Or.inr rfl), hpd]
      obtain ⟨-, h2⟩ := (planeProduct_dist_z hf haz hbz).mp h1
      have h3 := (mem_residue_ab_iff hf hab).mp ((hbij _ (hpair a b)).mapsTo hpR)
      refine hf.1.1 (Prod.ext ?_ ?_)
      · rw [h2, hp]
      · rw [h3, hp]
    have hΨq : Ψ q = q := by
      have hqd : q ∈ residue cs δ {a, b} d := (mem_residue_ab_iff hf hab).mpr (by rw [hq])
      have h1 : Ψ q ∈ residue cs δ {a, b} d := by
        rw [mem_residue_iff_mem_parabolic hδ, dist_inv hδ, ← hΨd,
          hΨ.2 _ (hsub _ (by simp) hqP) d (Or.inr rfl), ← dist_inv hδ]
        exact (mem_residue_iff_mem_parabolic hδ).mp hqd
      have h2 := (mem_residue_ab_iff hf hab).mp h1
      have h3 := (hzc _).mp (hbz'.mapsTo hqP)
      refine hf.1.1 (Prod.ext ?_ ?_)
      · rw [h3, hq]
      · rw [h2, hq]
    refine hf.1.1 ?_
    rw [hgf]
    have e1 : (f d).1 = (f p).1 := by rw [hp]
    have e2 : (f d).2 = (f q).2 := by rw [hq]
    rw [e1, hG p hpR, hΨp, e2, hσ q hqP, hΨq, hp, hq]
  have hgc : g c = c := (hagR c hcR).trans hΨc
  have hprod : ∀ {i : ι}, i ≠ z → M i z = 2 → (i = a ∨ i = b) →
      ∀ y ∈ residue cs δ {i, z} c, g y = Ψ y := by
    intro i hiz hMiz hi y hy
    have hJ := hpair i z
    let ϑ : C → C := fun y => g⁻¹ (Ψ y)
    have hϑiso : IsTypeIso cs δ δ (residue cs δ {i, z} c) (residue cs δ {i, z} c) ϑ := by
      have h1 := isTypeIso_residue_of_mem_typeAut hδ (inv_mem hgmem)
        (by rw [Equiv.Perm.inv_eq_iff_eq, hgc]) {i, z}
      exact ⟨h1.1.comp (hbij _ hJ), fun u hu v hv j =>
        (h1.2 _ ((hbij _ hJ).mapsTo hu) _ ((hbij _ hJ).mapsTo hv) j).trans
          ((hiso _ hJ).2 u hu v hv j)⟩
    have hfix : ∀ u ∈ panel cs δ i c ∪ panel cs δ z c, ϑ u = u := by
      rintro u (hu | hu)
      · have huR : u ∈ residue cs δ {a, b} c :=
          residue_mono (Set.singleton_subset_iff.mpr (by rcases hi with rfl | rfl <;> simp)) c hu
        change g⁻¹ (Ψ u) = u
        rw [← hagR u huR, Equiv.Perm.inv_def, Equiv.symm_apply_apply]
      · change g⁻¹ (Ψ u) = u
        rw [← hagP u hu, Equiv.Perm.inv_def, Equiv.symm_apply_apply]
    have := fix_residue_of_commute hδ hiz hMiz hϑiso hfix y hy
    change g⁻¹ (Ψ y) = y at this
    rw [Equiv.Perm.inv_eq_iff_eq] at this
    exact this.symm
  refine ⟨g, hgmem, ?_⟩
  rintro y (hy | hy)
  · obtain ⟨J, hJ, hyJ⟩ := mem_foundation_iff.mp hy
    by_cases hzJ : z ∈ J
    · by_cases haJ : a ∈ J
      · have hbJ : b ∉ J := by
          intro hbJ
          have : ({a, b, z} : Set ι) ⊆ J := by
            intro i hi
            rcases hi with rfl | rfl | hi
            · exact haJ
            · exact hbJ
            · rw [Set.mem_singleton_iff.mp hi]; exact hzJ
          have h3 := Set.encard_le_encard this
          rw [Set.encard_insert_of_notMem (by simp [hab, haz]),
            Set.encard_pair hbz] at h3
          have : (1 : ℕ∞) + 2 ≤ 2 := h3.trans hJ
          norm_num at this
        have hJ' : J ⊆ {a, z} := fun i hi => by
          rcases hι i with rfl | rfl | rfl
          · simp
          · exact absurd hi hbJ
          · simp
        exact hprod haz hMaz (Or.inl rfl) y (residue_mono hJ' c hyJ)
      · have hJ' : J ⊆ {b, z} := fun i hi => by
          rcases hι i with rfl | rfl | rfl
          · exact absurd hi haJ
          · simp
          · simp
        exact hprod hbz hMbz (Or.inr rfl) y (residue_mono hJ' c hyJ)
    · have hJ' : J ⊆ {a, b} := fun i hi => by
        rcases hι i with rfl | rfl | rfl
        · simp
        · simp
        · exact absurd hi hzJ
      exact hagR y (residue_mono hJ' c hyJ)
  · rw [Set.mem_singleton_iff.mp hy]
    exact hagd

end Building3

theorem planeProduct_extension [Finite W] {C C' : Type*} {δ : C → C → W} {δ' : C' → C' → W}
    (hδ : IsWeylDistanceBuilding cs δ) (hδ' : IsWeylDistanceBuilding cs δ') {k : Type*}
    [Field k] {Z : Type*} {a b z : ι} (hab : a ≠ b) (haz : a ≠ z) (hbz : b ≠ z)
    (hι : ∀ i, i = a ∨ i = b ∨ i = z) (hMab : M a b = 3) (hMaz : M a z = 2) (hMbz : M b z = 2)
    {f : C → PlaneFlag k × Z} (hf : IsChamberModel cs δ (planeProduct k Z a b z) f)
    {f' : C' → PlaneFlag k × Z} (hf' : IsChamberModel cs δ' (planeProduct k Z a b z) f') :
    Rig₂ cs δ ∧ Rig₂ cs δ' ∧
    ∀ (c d : C) (c' d' : C'), δ c d = longest cs Set.univ → δ' c' d' = longest cs Set.univ →
      ∀ φ : C → C', IsWeylIsometry δ δ' (foundation cs δ 2 c ∪ {d})
          (foundation cs δ' 2 c' ∪ {d'}) φ → φ c = c' → φ d = d' →
        ∃ F : C → C', IsTypeIso cs δ δ' Set.univ Set.univ F ∧
          Set.EqOn F φ (foundation cs δ 2 c ∪ {d}) ∧
          ∀ F' : C → C', IsTypeIso cs δ δ' Set.univ Set.univ F' →
            Set.EqOn F' φ (foundation cs δ 2 c ∪ {d}) → F' = F := by
  have hrig := rig₂_of_planeProduct hδ hab haz hbz hι hMab hMaz hMbz hf
  refine ⟨hrig, rig₂_of_planeProduct hδ' hab haz hbz hι hMab hMaz hMbz hf', ?_⟩
  intro c d c' d' hcd hcd' φ hφ hφc hφd
  exact ext_of_transitive hδ hrig
    (planeProduct_transitive hδ hab haz hbz hι hMab hMaz hMbz hf)
    (planeProduct_realize hδ hab haz hbz hι hMab hMaz hMbz hf) hδ' (hf.isTypeIso hf') hcd hcd'
    hφ hφc hφd

end CFSG.Monster.B.Geometry
