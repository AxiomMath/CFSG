module

public import CFSG.Quasithin.AppendixH.Common.OctadPtStabCard
public import CFSG.Assembly.ComponentTypeDefs

public section

open scoped Pointwise

namespace CFSG.ASVolI.AppH

open CFSG.ASVolI.ChH CFSG.Monster.Code

theorem eq_rImg_octFix_of_fixing {Γ : Subgroup S24} (hΓ : Γ ≤ M24g)
    {V : Type*} [CommGroup V] (ρ : ↥Γ →* MulAut V) (hρ : Function.Injective ρ)
    {A : Subgroup (MulAut V)} (hA : Nat.card ↥A = 16) {O' : Finset (Fin 24)} (hO' : IsOctad O')
    (hfix : ∀ a ∈ A, ∃ γ : ↥Γ, ρ γ = a ∧ ∀ x ∈ O', (γ : S24) x = x) :
    octFix O' ≤ Γ ∧ A = rImg ρ (octFix O') := by
  have hcardF : Nat.card ↥(octFix O') = 16 := card_octFix hO'
  have hA_le : A ≤ rImg ρ (octFix O') := by
    intro a ha
    obtain ⟨γ, hγ, hfixγ⟩ := hfix a ha
    rw [rImg, Subgroup.mem_map]
    refine ⟨γ, ?_, hγ⟩
    rw [Subgroup.mem_subgroupOf]
    exact mem_octFix_iff.2 ⟨hΓ γ.2, hfixγ⟩
  let ι : ↥((octFix O').subgroupOf Γ) → ↥(octFix O') :=
    fun x => ⟨(x : ↥Γ).1, Subgroup.mem_subgroupOf.1 x.2⟩
  have hιinj : Function.Injective ι := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : ↥(octFix O') => (z : S24)) hxy
  have hle_card : Nat.card ↥((octFix O').subgroupOf Γ) ≤ Nat.card ↥(octFix O') :=
    Nat.card_le_card_of_injective ι hιinj
  have hcard_map : Nat.card ↥(rImg ρ (octFix O')) =
      Nat.card ↥((octFix O').subgroupOf Γ) := by
    rw [rImg]
    exact Subgroup.card_map_of_injective hρ
  haveI : Finite ↥((octFix O').subgroupOf Γ) := inferInstance
  let f : ↥A → ↥((octFix O').subgroupOf Γ) := fun a =>
    let γ := Classical.choose (hfix (a : MulAut V) a.2)
    ⟨γ, Subgroup.mem_subgroupOf.2
      (mem_octFix_iff.2 ⟨hΓ γ.2, (Classical.choose_spec (hfix (a : MulAut V) a.2)).2⟩)⟩
  have hf_inj : Function.Injective f := by
    intro a b hab
    have ha := (Classical.choose_spec (hfix (a : MulAut V) a.2)).1
    have hb := (Classical.choose_spec (hfix (b : MulAut V) b.2)).1
    have hval : (Classical.choose (hfix (a : MulAut V) a.2) : ↥Γ) =
        Classical.choose (hfix (b : MulAut V) b.2) :=
      congrArg (fun z : ↥((octFix O').subgroupOf Γ) => (z : ↥Γ)) hab
    apply Subtype.ext
    calc (a : MulAut V) = ρ (Classical.choose (hfix (a : MulAut V) a.2)) := ha.symm
      _ = ρ (Classical.choose (hfix (b : MulAut V) b.2)) := by rw [hval]
      _ = (b : MulAut V) := hb
  have hcardA_le_sub : Nat.card ↥A ≤ Nat.card ↥((octFix O').subgroupOf Γ) :=
    Nat.card_le_card_of_injective f hf_inj
  have hsub_eq : Nat.card ↥((octFix O').subgroupOf Γ) = Nat.card ↥(octFix O') := by
    apply le_antisymm hle_card
    calc Nat.card ↥(octFix O') = 16 := hcardF
      _ = Nat.card ↥A := hA.symm
      _ ≤ Nat.card ↥((octFix O').subgroupOf Γ) := hcardA_le_sub
  have hF_le : octFix O' ≤ Γ := by
    haveI : Finite ↥((octFix O').subgroupOf Γ) :=
      Nat.finite_of_card_ne_zero (by rw [hsub_eq, hcardF]; norm_num)
    haveI : Finite ↥(octFix O') :=
      Nat.finite_of_card_ne_zero (by rw [hcardF]; norm_num)
    have hbij := hιinj.bijective_of_nat_card_le (le_of_eq hsub_eq.symm)
    intro x hx
    obtain ⟨y, hy⟩ := hbij.2 ⟨x, hx⟩
    have hxy : x = (y : ↥Γ) := by
      have h := congrArg (fun z : ↥(octFix O') => (z : S24)) hy
      simpa using h.symm
    rw [hxy]
    exact (y : ↥Γ).2
  have hcard_rImg : Nat.card ↥(rImg ρ (octFix O')) = 16 := by
    rw [hcard_map, hsub_eq, hcardF]
  haveI : Finite ↥(rImg ρ (octFix O')) :=
    Nat.finite_of_card_ne_zero (by rw [hcard_rImg]; norm_num)
  have hA_eq : A = rImg ρ (octFix O') :=
    Subgroup.eq_of_le_of_card_ge hA_le (by rw [hcard_rImg, hA])
  exact ⟨hF_le, hA_eq⟩

end CFSG.ASVolI.AppH

