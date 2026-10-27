module

public import CFSG.Open.Catalog

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open (WreathedTwoGroup)

section Generic

variable {D Q : Type*} [Group D] [Group Q]

private theorem wrSylow_base_mul_comm (hD : ∀ x y : D, x * y = y * x) {a b : D ≀ᵣ Q}
    (ha : a.right = 1) (hb : b.right = 1) : a * b = b * a := by
  refine RegularWreathProduct.ext ?_ ?_
  · funext x
    simp only [RegularWreathProduct.mul_left, Pi.mul_apply, ha, hb, inv_one, one_mul]
    exact hD _ _
  · simp [ha, hb]

private theorem wrSylow_left_const (hD : ∀ x y : D, x * y = y * x)
    (hQ : ∀ r x : Q, r ≠ 1 → x = 1 ∨ x = r) {t a : D ≀ᵣ Q} (ht : t.right ≠ 1)
    (ha : a.right = 1) (h : t * a = a * t) (x : Q) : a.left x = a.left 1 := by
  have key : ∀ y, a.left (t.right⁻¹ * y) = a.left y := by
    intro y
    have h1 := congrArg (fun w : D ≀ᵣ Q => w.left y) h
    simp only [RegularWreathProduct.mul_left, Pi.mul_apply, ha, inv_one, one_mul] at h1
    rw [hD (a.left y) (t.left y)] at h1
    exact mul_left_cancel h1
  rcases hQ t.right⁻¹ x (inv_ne_one.mpr ht) with hx | hx
  · rw [hx]
  · rw [hx]
    simpa using key 1

private def wrSylowEval {G : Type*} [Group G] (ι : G →* D ≀ᵣ Q) (h : ∀ g, (ι g).right = 1)
    (x : Q) : G →* D where
  toFun g := (ι g).left x
  map_one' := by simp
  map_mul' a b := by simp [h a]

@[simp]
private theorem wrSylowEval_apply {G : Type*} [Group G] (ι : G →* D ≀ᵣ Q)
    (h : ∀ g, (ι g).right = 1) (x : Q) (g : G) : wrSylowEval ι h x g = (ι g).left x :=
  rfl

private theorem wrSylow_exists_two_gen {G C : Type*} [Group G] [Group C] [IsCyclic C]
    (f : G →* C) (hf : IsCyclic f.ker) :
    ∃ s : Finset G, s.card ≤ 2 ∧ Subgroup.closure (s : Set G) = ⊤ := by
  classical
  obtain ⟨c, hc⟩ := IsCyclic.exists_generator (α := f.range)
  obtain ⟨g₁, hg₁⟩ := c.2
  obtain ⟨k, hk⟩ := IsCyclic.exists_generator (α := f.ker)
  refine ⟨{(k : G), g₁}, Finset.card_le_two, ?_⟩
  rw [eq_top_iff]
  intro a _
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hc ⟨f a, a, rfl⟩)
  have hfa : f a = f (g₁ ^ n) := by
    have := congrArg Subtype.val hn
    simpa [hg₁] using this.symm
  have hmem : a * (g₁ ^ n)⁻¹ ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, ← hfa, mul_inv_cancel]
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hk ⟨_, hmem⟩)
  have haj : a = (k : G) ^ j * g₁ ^ n := by
    have := congrArg Subtype.val hj
    simp only [Subgroup.coe_zpow] at this
    rw [this]
    group
  rw [haj]
  refine Subgroup.mul_mem _ (Subgroup.zpow_mem _ (Subgroup.subset_closure ?_) _)
    (Subgroup.zpow_mem _ (Subgroup.subset_closure ?_) _)
  · simp
  · simp

private theorem wrSylow_exists_two_gen_of_injective {G : Type*} [Group G] [IsMulCommutative G]
    [IsCyclic D] (hQ : ∃ σ : Q, σ ≠ 1 ∧ ∀ x, x = 1 ∨ x = σ) (ι : G →* D ≀ᵣ Q)
    (hι : Function.Injective ι) :
    ∃ s : Finset G, s.card ≤ 2 ∧ Subgroup.closure (s : Set G) = ⊤ := by
  obtain ⟨σ, -, hσ⟩ := hQ
  have hD : ∀ x y : D, x * y = y * x := fun x y => mul_comm' x y
  have hQ' : ∀ r x : Q, r ≠ 1 → x = 1 ∨ x = r := by
    intro r x hr
    rw [(hσ r).resolve_left hr]
    exact hσ x
  have : IsCyclic Q := by
    refine ⟨⟨σ, fun x => ?_⟩⟩
    rcases hσ x with rfl | rfl
    · exact Subgroup.mem_zpowers_iff.mpr ⟨0, by simp⟩
    · exact Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩
  by_cases hall : ∀ g, (ι g).right = 1
  · let f := wrSylowEval ι hall 1
    have hcyc : IsCyclic f.ker := by
      refine isCyclic_of_injective ((wrSylowEval ι hall σ).comp f.ker.subtype) ?_
      rw [injective_iff_map_eq_one]
      rintro ⟨g, hg⟩ hg1
      have hg0 : (ι g).left 1 = 1 := hg
      have hgσ : (ι g).left σ = 1 := hg1
      have hg' : ι g = 1 := by
        refine RegularWreathProduct.ext ?_ (hall g)
        funext x
        rcases hσ x with rfl | rfl
        · exact hg0
        · exact hgσ
      exact Subtype.ext (hι (by rw [hg']; simp))
    exact wrSylow_exists_two_gen f hcyc
  · obtain ⟨t, ht⟩ := not_forall.mp hall
    let κ : G →* Q := RegularWreathProduct.rightHom.comp ι
    let ι' : ↥κ.ker →* D ≀ᵣ Q := ι.comp κ.ker.subtype
    have hι' : Function.Injective ι' := hι.comp κ.ker.subtype_injective
    have hN : ∀ g : ↥κ.ker, (ι' g).right = 1 := fun g => g.2
    have hconst : ∀ (g : ↥κ.ker) x, (ι' g).left x = (ι' g).left 1 := by
      intro g x
      refine wrSylow_left_const hD hQ' ht (hN g) ?_ x
      change ι t * ι g = ι g * ι t
      rw [← map_mul, ← map_mul, mul_comm' t g]
    have hcyc : IsCyclic ↥κ.ker := by
      refine isCyclic_of_injective (wrSylowEval ι' hN 1) ?_
      rw [injective_iff_map_eq_one]
      intro g hg1
      have hg0 : (ι' g).left 1 = 1 := hg1
      have hg' : ι' g = 1 := by
        refine RegularWreathProduct.ext ?_ (hN g)
        funext x
        rw [hconst g x]
        exact hg0
      exact hι' (by rw [hg', map_one])
    exact wrSylow_exists_two_gen κ hcyc

private theorem wrSylow_exists_index_le_two {G : Type*} [Group G] [Finite Q]
    (hD : ∀ x y : D, x * y = y * x) (hQ : Nat.card Q ≤ 2) (ι : G →* D ≀ᵣ Q)
    (hι : Function.Injective ι) :
    ∃ N : Subgroup G, IsMulCommutative N ∧ N.index ≤ 2 := by
  let κ : G →* Q := RegularWreathProduct.rightHom.comp ι
  refine ⟨κ.ker, IsMulCommutative.of_comm fun a b => ?_, ?_⟩
  · refine Subtype.ext (hι ?_)
    simp only [Subgroup.coe_mul, map_mul]
    exact wrSylow_base_mul_comm hD a.2 b.2
  · rw [Subgroup.index_ker]
    exact (Subgroup.card_le_card_group _).trans hQ

end Generic

private theorem wrSylow_exists_two_cases :
    ∃ σ : Multiplicative (ZMod 2), σ ≠ 1 ∧ ∀ x, x = 1 ∨ x = σ :=
  ⟨Multiplicative.ofAdd 1, by decide, by decide⟩

private theorem wrSylow_card_two : Nat.card (Multiplicative (ZMod 2)) ≤ 2 := by
  simp [Nat.card_eq_fintype_card]

private theorem wrSylow_exists_relIndex_le_two {E : Type*} [Group E] (P : Subgroup E) (m : ℕ)
    (ι : ↥P →* WreathedTwoGroup m) (hι : Function.Injective ι) :
    ∃ A ≤ P, IsMulCommutative A ∧ A.relIndex P ≤ 2 := by
  obtain ⟨N, hN, hidx⟩ := wrSylow_exists_index_le_two (fun x y => mul_comm x y)
    wrSylow_card_two ι hι
  refine ⟨N.map P.subtype, Subgroup.map_subtype_le N, inferInstance, ?_⟩
  have h : (N.map P.subtype).subgroupOf P = N :=
    Subgroup.comap_map_eq_self_of_injective P.subtype_injective N
  rw [Subgroup.relIndex, h]
  exact hidx

private theorem wrSylow_exists_closure_two {E : Type*} [Group E] (A : Subgroup E)
    [IsMulCommutative A] (m : ℕ) (ι : ↥A →* WreathedTwoGroup m) (hι : Function.Injective ι) :
    ∃ s : Finset E, s.card ≤ 2 ∧ Subgroup.closure (s : Set E) = A := by
  classical
  obtain ⟨s, hs, hcl⟩ := wrSylow_exists_two_gen_of_injective wrSylow_exists_two_cases ι hι
  refine ⟨s.image A.subtype, Finset.card_image_le.trans hs, ?_⟩
  rw [Finset.coe_image, ← MonoidHom.map_closure, hcl, Subgroup.map_top, Subgroup.range_subtype]

theorem wreathedTwoGroup_exists_isCommutative_relIndex_le_two (m : ℕ)
    (P : Subgroup (WreathedTwoGroup m)) :
    ∃ A ≤ P, IsMulCommutative A ∧ A.relIndex P ≤ 2 :=
  wrSylow_exists_relIndex_le_two P m P.subtype P.subtype_injective

theorem wreathedTwoGroup_isCommutative_closure_two (m : ℕ) (A : Subgroup (WreathedTwoGroup m))
    (hA : IsMulCommutative A) :
    ∃ s : Finset (WreathedTwoGroup m), s.card ≤ 2 ∧ Subgroup.closure (s : Set _) = A := by
  have := hA
  exact wrSylow_exists_closure_two A m A.subtype A.subtype_injective

theorem exists_isCommutative_relIndex_le_two_of_sylow_wreathed {E : Type} [Group E] [Finite E]
    (h : ∀ S : Sylow 2 E, ∃ m : ℕ, Nonempty (↥S ≃* WreathedTwoGroup m))
    (P : Subgroup E) (hP : IsPGroup 2 P) :
    ∃ A ≤ P, IsMulCommutative A ∧ A.relIndex P ≤ 2 := by
  obtain ⟨S, hPS⟩ := hP.exists_le_sylow
  obtain ⟨m, ⟨φ⟩⟩ := h S
  exact wrSylow_exists_relIndex_le_two P m (φ.toMonoidHom.comp (Subgroup.inclusion hPS))
    (φ.injective.comp (Subgroup.inclusion_injective hPS))

theorem isCommutative_closure_two_of_sylow_wreathed {E : Type} [Group E] [Finite E]
    (h : ∀ S : Sylow 2 E, ∃ m : ℕ, Nonempty (↥S ≃* WreathedTwoGroup m))
    (A : Subgroup E) (hA : IsPGroup 2 A) (hc : IsMulCommutative A) :
    ∃ s : Finset E, s.card ≤ 2 ∧ Subgroup.closure (s : Set E) = A := by
  have := hc
  obtain ⟨S, hAS⟩ := hA.exists_le_sylow
  obtain ⟨m, ⟨φ⟩⟩ := h S
  exact wrSylow_exists_closure_two A m (φ.toMonoidHom.comp (Subgroup.inclusion hAS))
    (φ.injective.comp (Subgroup.inclusion_injective hAS))

end CFSG.LocalAnalysis.WeakClosure81

end
