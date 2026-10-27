module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qNFqBase
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qStructNorm

public section

namespace CFSG.Quasithin.H13.F431.D4q.StdLoc

open CFSG.ComponentClassification.RankTwoExceptional.D4 CFSG.LieType.Chevalley CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.Quasithin.H13.F431.D4q.Struct CFSG.Quasithin.H13.F431.D4q.NFq

set_option linter.unusedSectionVars false

section Defs

variable {K : Type} [Field K] (σ : K ≃+* K)

@[expose] noncomputable def d4Va : Subgroup (ModGL TwistTag.D4.tag K) :=
  Subgroup.closure (Set.range (fun c : d4k K σ => d4x₅ K c) ∪
    Set.range (fun c : d4k K σ => d4x₆ K c))

noncomputable abbrev VaC : Subgroup (Cm σ) := (d4Va σ).subgroupOf (d4C K σ)

theorem mem_VaC {x : Cm σ} : x ∈ VaC σ ↔ (x : ModGL TwistTag.D4.tag K) ∈ d4Va σ :=
  Subgroup.mem_subgroupOf

end Defs

section Coord

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (hσ : ∀ c, σ (σ (σ c)) = c)

theorem d4x₅_mem_d4Va (e : d4k K σ) : d4x₅ K e ∈ d4Va σ :=
  Subgroup.subset_closure (Or.inl ⟨e, rfl⟩)

theorem d4x₆_mem_d4Va (f : d4k K σ) : d4x₆ K f ∈ d4Va σ :=
  Subgroup.subset_closure (Or.inr ⟨f, rfl⟩)

include hσ in
theorem beta_Va (e e' : d4k K σ) : beta σ hσ (0, 0, 0, e) (0, 0, 0, e') = 0 :=
  Subtype.ext (by simp [beta, trT])

include hσ in
theorem beta_Va_zero (e : d4k K σ) : beta σ hσ (0, 0, 0, e) 0 = 0 :=
  Subtype.ext (by simp [beta, trT])

include hσ in
theorem mem_d4Va_iff {g : ModGL TwistTag.D4.tag K} :
    g ∈ d4Va σ ↔ ∃ e f : d4k K σ, g = vmk σ (0, 0, 0, e) f := by
  constructor
  · intro hg
    refine Subgroup.closure_induction
      (p := fun g _ => ∃ e f : d4k K σ, g = vmk σ (0, 0, 0, e) f) ?_ ?_ ?_ ?_ hg
    · rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
      · exact ⟨c, 0, x5_eq_vmk σ c⟩
      · exact ⟨0, c, x6_eq_vmk σ c⟩
    · exact ⟨0, 0, (vmk_zero σ).symm⟩
    · rintro _ _ _ _ ⟨e, f, rfl⟩ ⟨e', f', rfl⟩
      refine ⟨e + e', f + f', ?_⟩
      rw [vmk_mul σ hσ, beta_Va σ hσ]
      simp only [Prod.mk_add_mk, add_zero, zero_add]
    · rintro _ _ ⟨e, f, rfl⟩
      exact ⟨e, gam σ hσ (0, 0, 0, e) + f, vmk_inv σ hσ _ _⟩
  · rintro ⟨e, f, rfl⟩
    have h1 : vmk σ (0, 0, 0, e) f = d4x₅ K e * d4x₆ K f := by
      rw [x5_eq_vmk σ e, x6_eq_vmk σ f, vmk_mul σ hσ, beta_Va_zero σ hσ]
      simp only [add_zero, zero_add]
    rw [h1]
    exact mul_mem (d4x₅_mem_d4Va σ e) (d4x₆_mem_d4Va σ f)

include hσ in
theorem mem_d4Va_iff_coord {g : ModGL TwistTag.D4.tag K} :
    g ∈ d4Va σ ↔ ∃ e f : K, σ e = e ∧ σ f = f ∧ g = d4v K σ 0 0 0 e f := by
  rw [mem_d4Va_iff σ hσ]
  constructor
  · rintro ⟨e, f, rfl⟩
    exact ⟨e, f, e.2, f.2, rfl⟩
  · rintro ⟨e, f, he, hf, rfl⟩
    exact ⟨⟨e, he⟩, ⟨f, hf⟩, rfl⟩

include hσ in
theorem d4Va_le_d4Vr : d4Va σ ≤ d4Vr K σ := fun g hg => by
  obtain ⟨e, f, rfl⟩ := (mem_d4Va_iff σ hσ).1 hg
  exact vmk_mem σ hσ _ _

include hσ in
theorem d4Va_le_d4C : d4Va σ ≤ d4C K σ := fun _ hg =>
  graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
    (graphFixedSimpleComplement_le _ (d4Va_le_d4Vr σ hσ hg))

include hσ in
theorem mem_VaC_of_coord {x : Cm σ} {e f : K} (he : σ e = e) (hf : σ f = f)
    (hx : (x : ModGL TwistTag.D4.tag K) = d4v K σ 0 0 0 e f) : x ∈ VaC σ :=
  (mem_VaC σ).2 ((mem_d4Va_iff_coord σ hσ).2 ⟨e, f, he, hf, hx⟩)

include hσ in
theorem exists_coord_of_mem_VaC {x : Cm σ} (hx : x ∈ VaC σ) :
    ∃ e f : K, σ e = e ∧ σ f = f ∧ (x : ModGL TwistTag.D4.tag K) = d4v K σ 0 0 0 e f :=
  (mem_d4Va_iff_coord σ hσ).1 ((mem_VaC σ).1 hx)

include hσ in
theorem d4Va_comm {a b : ModGL TwistTag.D4.tag K} (ha : a ∈ d4Va σ) (hb : b ∈ d4Va σ) :
    a * b = b * a := by
  obtain ⟨e, f, rfl⟩ := (mem_d4Va_iff σ hσ).1 ha
  obtain ⟨e', f', rfl⟩ := (mem_d4Va_iff σ hσ).1 hb
  rw [vmk_mul σ hσ, vmk_mul σ hσ, beta_Va σ hσ, beta_Va σ hσ, add_comm (0, 0, 0, e) (0, 0, 0, e'),
    zero_add, zero_add, add_comm f f']

include hσ in
theorem d4Va_mul_self {a : ModGL TwistTag.D4.tag K} (ha : a ∈ d4Va σ) : a * a = 1 := by
  obtain ⟨e, f, rfl⟩ := (mem_d4Va_iff σ hσ).1 ha
  have he : e + e = 0 := Subtype.ext (CharTwo.add_self_eq_zero (e : K))
  have hf : f + f = 0 := Subtype.ext (CharTwo.add_self_eq_zero (f : K))
  rw [vmk_mul σ hσ, beta_Va σ hσ, zero_add, hf]
  have h0 : ((0, 0, 0, e) + (0, 0, 0, e) : Vc σ) = 0 := by
    simp only [Prod.mk_add_mk, add_zero, he]
    rfl
  rw [h0]
  exact vmk_zero σ

include hσ in
theorem d4x₅_one_ne_one : d4x₅ K 1 ≠ 1 := fun h => by
  have h1 : vmk σ (0, 0, 0, 1) 0 = vmk σ 0 0 := by
    rw [← x5_eq_vmk σ 1, vmk_zero σ]
    exact h
  have h2 := (vmk_inj σ h1).1
  have h3 := congrArg (fun y : Vc σ => (y.2.2.2 : K)) h2
  exact one_ne_zero h3

end Coord

section Group

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (hσ : ∀ c, σ (σ (σ c)) = c)

include hσ in
theorem VaC_comm : ∀ a ∈ VaC σ, ∀ b ∈ VaC σ, a * b = b * a := fun _ ha _ hb =>
  Subtype.ext (d4Va_comm σ hσ ((mem_VaC σ).1 ha) ((mem_VaC σ).1 hb))

include hσ in
theorem VaC_two : ∀ a ∈ VaC σ, a ^ 2 = 1 := fun _ ha =>
  Subtype.ext (by
    rw [pow_two, Subgroup.coe_mul]
    exact d4Va_mul_self σ hσ ((mem_VaC σ).1 ha))

include hσ in
theorem VaC_ne_bot : VaC σ ≠ ⊥ := by
  intro h
  have hx : d4x₅ K ((1 : d4k K σ) : K) ∈ d4Va σ := d4x₅_mem_d4Va σ 1
  have hxC : d4x₅ K ((1 : d4k K σ) : K) ∈ d4C K σ := d4Va_le_d4C σ hσ hx
  have hmem : (⟨d4x₅ K ((1 : d4k K σ) : K), hxC⟩ : Cm σ) ∈ VaC σ := (mem_VaC σ).2 hx
  rw [h, Subgroup.mem_bot] at hmem
  exact d4x₅_one_ne_one σ hσ (congrArg Subtype.val hmem)

end Group

end CFSG.Quasithin.H13.F431.D4q.StdLoc
