module

public import CFSG.RankThree.Lattice.SteinbergBIE6EvenCenter

public noncomputable section

namespace CFSG.RankThree.Lattice

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.RankThree.E6 CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley
open scoped Pointwise

@[expose] def IsSeparated (S S' : Set (Fin Tag.E6.rank)) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S', a ≠ b ∧ Tag.E6.cartan a b = 0

section Separated

variable {S S' : Set (Fin Tag.E6.rank)}

theorem exists_ne_zero_of_isRoot {α : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α) :
    ∃ i, α i ≠ 0 := by
  by_contra h
  push Not at h
  have h0 : α = 0 := funext h
  have := iform_self_E6 hα
  rw [h0] at this
  simp [iform] at this

theorem not_mem_of_isSeparated (hsep : IsSeparated S S') {a : Fin Tag.E6.rank} (ha : a ∈ S) :
    a ∉ S' := fun h => (hsep a ha a h).1 rfl

theorem commute_pinnedX_of_isSeparated {K : Type} [Field K] (hsep : IsSeparated S S')
    {α β : Fin Tag.E6.rank → ℤ} (hα : α ∈ parabolicRoots Tag.E6 S)
    (hβ : β ∈ parabolicRoots Tag.E6 S') (c d : K) :
    Commute (pinnedX Tag.E6 K α c) (pinnedX Tag.E6 K β d) := by
  obtain ⟨a, ha⟩ := exists_ne_zero_of_isRoot hα.1
  have haS : a ∈ S := mem_parabolicRoots_of_support hα ha
  have hβa : β a = 0 := hβ.2 a (not_mem_of_isSeparated hsep haS)
  have hne : α ≠ β := fun e => ha (by rw [e]; exact hβa)
  have hne' : α ≠ -β := fun e => ha (by rw [e, Pi.neg_apply, hβa, neg_zero])
  have hnot : ¬ IsRoot Tag.E6 (α + β) := by
    intro hr
    have hsupp : ∀ i, (α + β) i ≠ 0 → i ∈ S ∨ i ∈ S' := by
      intro i hi
      by_contra h
      push Not at h
      exact hi (by rw [Pi.add_apply, hα.2 i h.1, hβ.2 i h.2, add_zero])
    rcases support_split hr (fun a ha b hb => (hsep a ha b hb).2) hsupp with h | h
    ·
      obtain ⟨b, hb⟩ := exists_ne_zero_of_isRoot hβ.1
      have hbS' : b ∈ S' := mem_parabolicRoots_of_support hβ hb
      have hαb : α b = 0 := hα.2 b fun hbS => not_mem_of_isSeparated hsep hbS hbS'
      exact not_mem_of_isSeparated hsep (h b (by rw [Pi.add_apply, hαb, zero_add]; exact hb)) hbS'
    · exact not_mem_of_isSeparated hsep haS (h a (by rw [Pi.add_apply, hβa, add_zero]; exact ha))
  exact (simply_laced_root_commutator_unit Tag.E6 (Or.inr (Or.inl rfl)) hα.1 hβ.1 hne hne').2
    hnot K _ (Subgroup.subset_closure ⟨c, rfl⟩) _ (Subgroup.subset_closure ⟨d, rfl⟩)

theorem commute_of_isSeparated {K : Type} [Field K] (hsep : IsSeparated S S') {x y : ModGL Tag.E6 K}
    (hx : x ∈ subsystemGroup Tag.E6 K S) (hy : y ∈ subsystemGroup Tag.E6 K S') :
    Commute x y := by
  rw [subsystemGroup_eq_rootSpan] at hx hy
  have h1 : rootSpan Tag.E6 K (parabolicRoots Tag.E6 S') ≤ Subgroup.centralizer {x} := by
    have h2 : rootSpan Tag.E6 K (parabolicRoots Tag.E6 S) ≤
        ⨅ β ∈ parabolicRoots Tag.E6 S', ⨅ d : K,
          Subgroup.centralizer {pinnedX Tag.E6 K β d} := by
      refine le_iInf₂ fun β hβ => le_iInf fun d => rootSpan_le_centralizer fun α hα c => ?_
      exact (commute_pinnedX_of_isSeparated hsep hα hβ c d).eq
    have hx' := h2 hx
    refine rootSpan_le_centralizer fun β hβ d => ?_
    have := Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hx' β) hβ
    exact (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_iInf.1 this d)).symm
  exact (Subgroup.mem_centralizer_singleton_iff.1 (h1 hy)).symm

end Separated

section Product

variable {Ω : Type} [Field Ω]

theorem e6Commutant_iSup {ι : Type*} (P : ι → Subgroup (ModGL Tag.E6 Ω)) :
    e6Commutant ((⨆ k, P k : Subgroup (ModGL Tag.E6 Ω)) : Set (ModGL Tag.E6 Ω)) =
      ⋂ k, e6Commutant (P k : Set (ModGL Tag.E6 Ω)) := by
  ext X
  simp only [Set.mem_iInter]
  constructor
  · intro hX k
    exact e6Commutant_anti (le_iSup P k) hX
  · intro hX g hg
    exact (iSup_le (fun k => fun x hx => hX k x hx) : (⨆ k, P k) ≤ commuteSubgroup X) hg

theorem mem_e6Commutant_subsystemGroup_iff {ι : Type*} (S : ι → Set (Fin Tag.E6.rank))
    {J : Set (Fin Tag.E6.rank)} (hJ : J = ⋃ k, S k) (X : Module.End Ω (RootModule Tag.E6 Ω)) :
    X ∈ e6Commutant (subsystemGroup Tag.E6 Ω J : Set (ModGL Tag.E6 Ω)) ↔
      ∀ k, X ∈ e6Commutant (subsystemGroup Tag.E6 Ω (S k) : Set (ModGL Tag.E6 Ω)) := by
  constructor
  · intro hX k
    refine e6Commutant_anti (Subgroup.closure_mono ?_) hX
    rintro _ ⟨i, hi, c, h⟩
    exact ⟨i, hJ ▸ Set.mem_iUnion.2 ⟨k, hi⟩, c, h⟩
  · intro hX
    refine mem_e6Commutant_subsystemGroup (fun i hi c => ?_) (fun i hi c => ?_)
    · rw [hJ] at hi
      obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hi
      exact hX k _ (xUnit_mem_subsystemGroup hk c)
    · rw [hJ] at hi
      obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hi
      exact hX k _ (yUnit_mem_subsystemGroup hk c)

theorem e6_product_layers {ι : Type} [Fintype ι] [DecidableEq ι] (J : Set (Fin Tag.E6.rank))
    (S : ι → Set (Fin Tag.E6.rank)) (P : ι → Subgroup (ModGL Tag.E6 Ω))
    (hsep : ∀ k l, k ≠ l → IsSeparated (S k) (S l)) (hJ : J = ⋃ k, S k)
    (hle : ∀ k, P k ≤ subsystemGroup Tag.E6 Ω (S k))
    (hC : ∀ k, e6Commutant (P k : Set (ModGL Tag.E6 Ω)) =
      e6Commutant (subsystemGroup Tag.E6 Ω (S k) : Set (ModGL Tag.E6 Ω))) :
    (∀ k l, k ≠ l → ∀ x ∈ P k, ∀ y ∈ P l, Commute x y) ∧
    ∃ μ : (∀ k, P k) →* ModGL Tag.E6 Ω,
      (∀ k (y : P k), μ (Pi.mulSingle k y) = y) ∧
      μ.range = ⨆ k, P k ∧
      e6Commutant (μ.range : Set (ModGL Tag.E6 Ω)) =
        e6Commutant (subsystemGroup Tag.E6 Ω J : Set (ModGL Tag.E6 Ω)) ∧
      (∀ h ∈ torusGroup Tag.E6 Ω, ∀ z ∈ subsystemGroup Tag.E6 Ω J,
        (∀ x ∈ μ.range, h * z * x = x * (h * z)) → h * z ∈ torusGroup Tag.E6 Ω) ∧
      ∀ x : ∀ k, P k, μ x = 1 ↔ (∀ k, x k ∈ Subgroup.center (P k)) ∧
        ∀ i : Fin Tag.E6.rank, torusRootChar (μ x) (Pi.single i 1) = 1 := by
  have hcomm : Pairwise fun k l => ∀ x y : ModGL Tag.E6 Ω, x ∈ P k → y ∈ P l → Commute x y :=
    fun k l hkl x y hx hy => commute_of_isSeparated (hsep k l hkl) (hle k hx) (hle l hy)
  refine ⟨fun k l hkl x hx y hy => hcomm hkl x y hx hy, Subgroup.noncommPiCoprod hcomm,
    fun k y => Subgroup.noncommPiCoprod_mulSingle k y, Subgroup.noncommPiCoprod_range, ?_, ?_, ?_⟩
  ·
    rw [Subgroup.noncommPiCoprod_range, e6Commutant_iSup]
    ext X
    rw [Set.mem_iInter, mem_e6Commutant_subsystemGroup_iff S hJ X]
    exact forall_congr' fun k => by rw [hC k]
  ·
    intro h hh z hz hc
    refine mem_torusGroup_of_commute_subsystemGroup hh hz fun x hx => ?_
    have hX : ((h * z : ModGL Tag.E6 Ω) : Module.End Ω (RootModule Tag.E6 Ω)) ∈
        e6Commutant (subsystemGroup Tag.E6 Ω J : Set (ModGL Tag.E6 Ω)) := by
      refine (mem_e6Commutant_subsystemGroup_iff S hJ _).2 fun k => ?_
      rw [← hC k]
      intro y hy
      refine commute_val_of_mul_eq (hc y ?_)
      rw [Subgroup.noncommPiCoprod_range]
      exact le_iSup P k hy
    exact mul_eq_of_commute_val (hX x hx)
  ·
    intro x
    rw [Subgroup.noncommPiCoprod_apply]
    constructor
    · intro h1
      refine ⟨fun k => ?_, fun i => by rw [h1, torusRootChar_one]⟩
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      have he := Finset.mul_noncommProd_erase Finset.univ (Finset.mem_univ k)
        (fun l => ((x l : P l) : ModGL Tag.E6 Ω))
        (fun i _ j _ h ↦ hcomm h _ _ (x i).prop (x j).prop)
      rw [h1] at he
      have hR : Commute (y : ModGL Tag.E6 Ω) ((Finset.univ.erase k).noncommProd
          (fun l => ((x l : P l) : ModGL Tag.E6 Ω)) (fun i hi j hj h ↦ hcomm h _ _ (x i).prop
            (x j).prop)) :=
        Finset.noncommProd_commute _ _ _ _ fun l hl =>
          hcomm (Finset.ne_of_mem_erase hl).symm _ _ y.2 (x l).2
      have hxk : ((x k : P k) : ModGL Tag.E6 Ω) = ((Finset.univ.erase k).noncommProd
          (fun l => ((x l : P l) : ModGL Tag.E6 Ω)) (fun i hi j hj h ↦ hcomm h _ _ (x i).prop
            (x j).prop))⁻¹ := eq_inv_of_mul_eq_one_left he
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hxk]
      exact hR.inv_right.eq
    · rintro ⟨hZ, hχ⟩
      have hH : ∀ k, ((x k : P k) : ModGL Tag.E6 Ω) ∈ torusGroup Tag.E6 Ω := fun k =>
        ((mem_center_iff_of_e6Commutant_eq (hle k) (hC k) (x k)).1 (hZ k)).1
      have hT := Subgroup.noncommProd_mem (torusGroup Tag.E6 Ω) (t := Finset.univ)
        (f := fun l => ((x l : P l) : ModGL Tag.E6 Ω))
        (fun i _ j _ h ↦ hcomm h _ _ (x i).prop (x j).prop) fun k _ => hH k
      exact eq_one_of_torusRootChar_single hT hχ

end Product

end CFSG.RankThree.Lattice
