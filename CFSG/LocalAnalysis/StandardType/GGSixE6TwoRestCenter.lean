module

public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoRestDefs
public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoRestFrame
public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoRestBasic
public import CFSG.LieType.Chevalley.ProductInjectivity
public import CFSG.LieType.Chevalley.E6GraphLeviRealization
public import CFSG.LieType.Chevalley.TwistedE6EvenCoverLifts
public import CFSG.LieType.Chevalley.HeightSeries
public import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCoverRoots
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.StandardType.GGSixE6Two

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open CFSG.SeitzReduction
  CFSG.StandardType.GGHalf CFSG.Timmesfeld.LieEmbed CFSG.LieType.Steinberg.Adjoint
open scoped commutatorElement

@[expose] def e6rz_stdL1 : Set (Fin Tag.E6.rank → ℤ) :=
  {γ | IsRoot .E6 γ ∧ iform γ E6Pilot.yLamAS = 1}

private theorem e6rz_level_le_two :
    ∀ γ ∈ rootFinset .E6, iform γ E6Pilot.yLamAS ≤ 2 := by
  decide +kernel

private theorem e6rz_partner :
    ∀ γ ∈ rootFinset .E6, iform γ E6Pilot.yLamAS = 1 →
      ∃ δ ∈ rootFinset .E6, iform δ E6Pilot.yLamAS = 1 ∧ (γ + δ) ∈ rootFinset .E6 := by
  decide +kernel

private theorem e6rz_l2_pos :
    ∀ γ ∈ rootFinset .E6, iform γ E6Pilot.yLamAS = 2 → 0 < height γ := by
  decide +kernel

private theorem e6rz_stdQRoots_eq :
    stdQRoots = e6rz_stdL1 ∪ stdZRoots := by
  ext γ
  constructor
  · rintro ⟨hγ, hpos⟩
    have hle := e6rz_level_le_two γ (mem_rootFinset.2 hγ)
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact Or.inl ⟨hγ, by omega⟩
    · exact Or.inr ⟨hγ, heq⟩
  · rintro (⟨hγ, h⟩ | ⟨hγ, h⟩)
    · exact ⟨hγ, by rw [h]; norm_num⟩
    · exact ⟨hγ, by rw [h]; norm_num⟩

private theorem e6rz_partner_mem
    {β : Fin Tag.E6.rank → ℤ} (hβ : β ∈ e6rz_stdL1) :
    ∃ δ ∈ e6rz_stdL1, IsRoot .E6 (β + δ) := by
  obtain ⟨hβr, hβl⟩ := hβ
  obtain ⟨δ, hδf, hδl, hδs⟩ := e6rz_partner β (mem_rootFinset.2 hβr) hβl
  exact ⟨δ, ⟨mem_rootFinset.1 hδf, hδl⟩, mem_rootFinset.1 hδs⟩

private theorem e6rz_f2_cases (a : F2) : a = 0 ∨ a = 1 := by
  have hcard : Nat.card F2 = 2 := by simpa using GaloisField.card 2 1 (by norm_num)
  by_cases hz : a = 0
  · exact Or.inl hz
  · obtain ⟨y, hy, huniq⟩ := (Nat.card_eq_two_iff' (0 : F2)).mp hcard
    exact Or.inr ((huniq a hz).trans (huniq 1 one_ne_zero).symm)

private theorem e6rz_rootSpan_closure
    (S : Set (Fin Tag.E6.rank → ℤ)) :
    rootSpan .E6 F2 S = Subgroup.closure {g : (Module.End F2 (RootModule .E6 F2))ˣ |
      ∃ β ∈ S, pinnedX .E6 F2 β 1 = g} := by
  rw [rootSpan_eq_closure F2 S]
  apply le_antisymm
  · refine (Subgroup.closure_le _).mpr ?_
    rintro g ⟨β, hβ, c, rfl⟩
    rcases e6rz_f2_cases c with rfl | rfl
    · rw [pinnedX_zero]; exact Subgroup.one_mem _
    · exact Subgroup.subset_closure ⟨β, hβ, rfl⟩
  · refine (Subgroup.closure_le _).mpr ?_
    rintro g ⟨β, hβ, rfl⟩
    exact Subgroup.subset_closure ⟨β, hβ, 1, rfl⟩

private theorem e6rz_map_subtype_rootSpan
    (S : Set (Fin Tag.E6.rank → ℤ)) :
    ((rootSpan .E6 F2 S).subgroupOf (adjointGroup .E6 F2)).map
        (adjointGroup .E6 F2).subtype = rootSpan .E6 F2 S := by
  rw [Subgroup.subgroupOf_map_subtype]
  exact inf_of_le_left (E6Pilot.rootSpan_le_adjointGroup_E6 S)

private theorem e6rz_subgroupOf_rootSpan_eq_closure
    (S : Set (Fin Tag.E6.rank → ℤ)) :
    (rootSpan .E6 F2 S).subgroupOf (adjointGroup .E6 F2) =
      Subgroup.closure {g : EC | ∃ β ∈ S, xr β = g} := by
  apply Subgroup.map_injective (adjointGroup .E6 F2).subtype_injective
  rw [e6rz_map_subtype_rootSpan S, e6rz_rootSpan_closure S, MonoidHom.map_closure]
  have hset : {g : (Module.End F2 (RootModule .E6 F2))ˣ | ∃ β ∈ S, pinnedX .E6 F2 β 1 = g} =
      (Subtype.val '' {g : EC | ∃ β ∈ S, xr β = g}) := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨β, hβ, rfl⟩
      exact ⟨xr β, ⟨β, hβ, rfl⟩, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨β, hβ, rfl⟩ := hy
      exact ⟨β, hβ, rfl⟩
  rw [hset]
  rfl

private theorem e6rz_qStd_eq_closure :
    qStd = Subgroup.closure {g : EC | ∃ β ∈ stdQRoots, xr β = g} := by
  rw [qStd, e6rz_subgroupOf_rootSpan_eq_closure]

private theorem e6rz_z0Std_eq_closure :
    z0Std = Subgroup.closure {g : EC | ∃ β ∈ stdZRoots, xr β = g} := by
  rw [z0Std, e6rz_subgroupOf_rootSpan_eq_closure]

private theorem e6rz_xr_mul_self
    {β : Fin Tag.E6.rank → ℤ} (hβ : IsRoot .E6 β) : xr β * xr β = 1 := by
  refine Subtype.ext ?_
  change pinnedX .E6 F2 β 1 * pinnedX .E6 F2 β 1 = (1 : (Module.End F2 (RootModule .E6 F2))ˣ)
  rw [← pinnedX_add, CharTwo.add_self_eq_zero (1 : F2), pinnedX_zero]

private theorem e6rz_level_nsmul_add_ge_three
    {γ δ : Fin Tag.E6.rank → ℤ}
    (hγ : γ ∈ stdQRoots) (hδ : δ ∈ stdQRoots)
    (h : 3 ≤ iform γ E6Pilot.yLamAS + iform δ E6Pilot.yLamAS) {a b : ℕ} (ha : 1 ≤ a)
    (hb : 1 ≤ b) : 3 ≤ iform (a • γ + b • δ) E6Pilot.yLamAS := by
  have hγ1 : 1 ≤ iform γ E6Pilot.yLamAS := by have := hγ.2; omega
  have hδ1 : 1 ≤ iform δ E6Pilot.yLamAS := by have := hδ.2; omega
  have ha' : (1 : ℤ) ≤ (a : ℤ) := by exact_mod_cast ha
  have hb' : (1 : ℤ) ≤ (b : ℤ) := by exact_mod_cast hb
  have ha0 : (0 : ℤ) ≤ (a : ℤ) := by positivity
  have hb0 : (0 : ℤ) ≤ (b : ℤ) := by positivity
  rw [show a • γ + b • δ = (a : ℤ) • γ + (b : ℤ) • δ from by
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]]
  rw [iform_add_left, iform_smul_left, iform_smul_left]
  nlinarith [mul_le_mul_of_nonneg_left hγ1 ha0, mul_le_mul_of_nonneg_left hδ1 hb0]

private theorem e6rz_not_isRoot_nsmul_add
    {γ δ : Fin Tag.E6.rank → ℤ}
    (hγ : γ ∈ stdQRoots) (hδ : δ ∈ stdQRoots)
    (h : 3 ≤ iform γ E6Pilot.yLamAS + iform δ E6Pilot.yLamAS) {a b : ℕ} (ha : 1 ≤ a)
    (hb : 1 ≤ b) : ¬ IsRoot .E6 (a • γ + b • δ) := by
  intro hr
  have h3 := e6rz_level_nsmul_add_ge_three hγ hδ h ha hb
  have h2 := e6rz_level_le_two _ (mem_rootFinset.2 hr)
  omega

private theorem e6rz_commute_of_level_sum_ge_three
    {γ δ : Fin Tag.E6.rank → ℤ} (hγ : γ ∈ stdQRoots) (hδ : δ ∈ stdQRoots)
    (h : 3 ≤ iform γ E6Pilot.yLamAS + iform δ E6Pilot.yLamAS) (c d : F2) :
    pinnedX .E6 F2 γ c * pinnedX .E6 F2 δ d = pinnedX .E6 F2 δ d * pinnedX .E6 F2 γ c := by
  by_cases hγδ : γ = δ
  · subst hγδ
    rw [← pinnedX_add, ← pinnedX_add, add_comm]
  have hγpos : 0 < iform γ E6Pilot.yLamAS := hγ.2
  have hδpos : 0 < iform δ E6Pilot.yLamAS := hδ.2
  have hne' : γ ≠ -δ := by
    rintro h
    have hδγ : δ = -γ := by rw [h]; simp
    rw [hδγ, iform_neg_left] at hδpos
    linarith
  have h0 : 0 ≤ iform γ δ := by
    rcases SimplyLacedCover.iform_mem TwistedE6Cover.simplyLaced_E6 hγ.1 hδ.1 hγδ hne' with
      h' | h' | h'
    · exfalso
      have hr : IsRoot .E6 (γ + δ) :=
        SimplyLacedCover.isRoot_add TwistedE6Cover.simplyLaced_E6 hγ.1 hδ.1 h'
      exact e6rz_not_isRoot_nsmul_add hγ hδ h (a := 1) (b := 1) le_rfl le_rfl
        (by simpa using hr)
    · exact le_of_eq h'.symm
    · exact zero_le_one.trans h'.ge
  exact TwistedE6Cover.commute_pinnedX_of_iform hγ.1 hδ.1 hne' h0 c d

private theorem e6rz_pinnedX_commute_of_not_isRoot_add
    {γ δ : Fin Tag.E6.rank → ℤ} (hγ : γ ∈ stdQRoots) (hδ : δ ∈ stdQRoots)
    (hγδ : γ ≠ δ) (hne' : γ ≠ -δ) (hnot : ¬ IsRoot .E6 (γ + δ)) (c d : F2) :
    pinnedX .E6 F2 γ c * pinnedX .E6 F2 δ d = pinnedX .E6 F2 δ d * pinnedX .E6 F2 γ c := by
  have h0 : 0 ≤ iform γ δ := by
    rcases SimplyLacedCover.iform_mem TwistedE6Cover.simplyLaced_E6 hγ.1 hδ.1 hγδ hne' with
      h' | h' | h'
    · exfalso
      exact hnot (SimplyLacedCover.isRoot_add TwistedE6Cover.simplyLaced_E6 hγ.1 hδ.1 h')
    · exact le_of_eq h'.symm
    · exact zero_le_one.trans h'.ge
  exact TwistedE6Cover.commute_pinnedX_of_iform hγ.1 hδ.1 hne' h0 c d

private theorem e6rz_xr_commute_of_not_isRoot_add
    {γ δ : Fin Tag.E6.rank → ℤ} (hγ : γ ∈ stdQRoots) (hδ : δ ∈ stdQRoots)
    (hγδ : γ ≠ δ) (hne' : γ ≠ -δ) (hnot : ¬ IsRoot .E6 (γ + δ)) :
    xr γ * xr δ = xr δ * xr γ := by
  apply Subtype.ext
  change pinnedX .E6 F2 γ 1 * pinnedX .E6 F2 δ 1 = pinnedX .E6 F2 δ 1 * pinnedX .E6 F2 γ 1
  exact e6rz_pinnedX_commute_of_not_isRoot_add hγ hδ hγδ hne' hnot 1 1

private theorem e6rz_xr_commute_of_level_sum_ge_three
    {γ δ : Fin Tag.E6.rank → ℤ} (hγ : γ ∈ stdQRoots) (hδ : δ ∈ stdQRoots)
    (h : 3 ≤ iform γ E6Pilot.yLamAS + iform δ E6Pilot.yLamAS) :
    xr γ * xr δ = xr δ * xr γ := by
  apply Subtype.ext
  change pinnedX .E6 F2 γ 1 * pinnedX .E6 F2 δ 1 = pinnedX .E6 F2 δ 1 * pinnedX .E6 F2 γ 1
  exact e6rz_commute_of_level_sum_ge_three hγ hδ h 1 1

private theorem e6rz_stdZRoots_subset_stdQRoots : stdZRoots ⊆ stdQRoots := by
  rintro γ ⟨hγ, h⟩
  exact ⟨hγ, by rw [h]; norm_num⟩

private theorem e6rz_z0Std_le_qStd :
    z0Std ≤ qStd := by
  rw [e6rz_z0Std_eq_closure, e6rz_qStd_eq_closure]
  refine (Subgroup.closure_le _).mpr ?_
  rintro g ⟨γ, hγ, rfl⟩
  exact Subgroup.subset_closure ⟨γ, e6rz_stdZRoots_subset_stdQRoots hγ, rfl⟩

private theorem e6rz_z0Std_central :
    z0Std ≤ Subgroup.centralizer (qStd : Set EC) := by
  rw [e6rz_z0Std_eq_closure]
  refine (Subgroup.closure_le _).mpr ?_
  rintro z ⟨γ, hγ, rfl⟩
  refine Subgroup.mem_centralizer_iff.2 ?_
  intro q hq
  rw [e6rz_qStd_eq_closure] at hq
  induction hq using Subgroup.closure_induction with
  | mem β hβ =>
      obtain ⟨β', hβ', rfl⟩ := hβ
      exact e6rz_xr_commute_of_level_sum_ge_three hβ' (e6rz_stdZRoots_subset_stdQRoots hγ) (by
        have h1 := hγ.2
        have h2 := hβ'.2
        omega)
  | one => rw [mul_one, one_mul]
  | mul a b ha hb iha ihb =>
      calc (a * b) * xr γ = a * (b * xr γ) := by group
        _ = a * (xr γ * b) := by rw [ihb]
        _ = (a * xr γ) * b := by group
        _ = (xr γ * a) * b := by rw [iha]
        _ = xr γ * (a * b) := by group
  | inv a ha iha =>
      calc a⁻¹ * xr γ = a⁻¹ * (xr γ * a) * a⁻¹ := by group
        _ = a⁻¹ * (a * xr γ) * a⁻¹ := by rw [← iha]
        _ = xr γ * a⁻¹ := by group

private theorem e6rz_z0Std_comm
    {a b : EC} (ha : a ∈ z0Std)
    (hb : b ∈ z0Std) : a * b = b * a :=
  (Subgroup.mem_centralizer_iff.1 (e6rz_z0Std_central ha) b
    (e6rz_z0Std_le_qStd hb)).symm

private noncomputable def e6rz_p
    (l : List (Fin Tag.E6.rank → ℤ)) : EC :=
  (l.map (fun β => xr β)).prod

private theorem e6rz_p_append
    (l1 l2 : List (Fin Tag.E6.rank → ℤ)) :
    e6rz_p (l1 ++ l2) = e6rz_p l1 * e6rz_p l2 := by
  simp [e6rz_p, List.map_append, List.prod_append]

private theorem e6rz_p_reverse
    {l : List (Fin Tag.E6.rank → ℤ)} (hl : ∀ β ∈ l, IsRoot .E6 β) :
    e6rz_p l.reverse = (e6rz_p l)⁻¹ := by
  induction l with
  | nil => simp [e6rz_p]
  | cons a l ih =>
    have hl' : ∀ β ∈ l, IsRoot .E6 β := fun β hβ => hl β (List.mem_cons_of_mem _ hβ)
    rw [List.reverse_cons, e6rz_p_append, ih hl']
    simp only [e6rz_p, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right (e6rz_xr_mul_self (hl a List.mem_cons_self))]

private theorem e6rz_p_mem_qStd
    {l : List (Fin Tag.E6.rank → ℤ)} (hl : ∀ β ∈ l, β ∈ stdQRoots) : e6rz_p l ∈ qStd := by
  rw [e6rz_qStd_eq_closure, e6rz_p]
  refine Subgroup.list_prod_mem _ ?_
  intro x hx
  obtain ⟨β, hβ, rfl⟩ := List.mem_map.1 hx
  exact Subgroup.subset_closure ⟨β, hl β hβ, rfl⟩

private theorem e6rz_K_mul_mem
    {u₁ u₂ : EC}
    {l₁ l₂ : List (Fin Tag.E6.rank → ℤ)} (hl₁ : ∀ β ∈ l₁, β ∈ stdQRoots)
    (hl₂ : ∀ β ∈ l₂, β ∈ stdQRoots) (hz₁ : u₁ * (e6rz_p l₁)⁻¹ ∈ z0Std)
    (hz₂ : u₂ * (e6rz_p l₂)⁻¹ ∈ z0Std) :
    u₁ * u₂ * (e6rz_p (l₁ ++ l₂))⁻¹ ∈ z0Std := by
  obtain ⟨z₁, hz₁', rfl⟩ : ∃ z₁, z₁ ∈ z0Std ∧ u₁ = z₁ * e6rz_p l₁ :=
    ⟨_, hz₁, by group⟩
  obtain ⟨z₂, hz₂', rfl⟩ : ∃ z₂, z₂ ∈ z0Std ∧ u₂ = z₂ * e6rz_p l₂ :=
    ⟨_, hz₂, by group⟩
  have hc : e6rz_p l₁ * z₂ = z₂ * e6rz_p l₁ :=
    Subgroup.mem_centralizer_iff.1 (e6rz_z0Std_central hz₂') (e6rz_p l₁)
      (e6rz_p_mem_qStd hl₁)
  have heq : (z₁ * e6rz_p l₁) * (z₂ * e6rz_p l₂) * (e6rz_p (l₁ ++ l₂))⁻¹ = z₁ * z₂ := by
    rw [e6rz_p_append, mul_inv_rev]
    rw [show (z₁ * e6rz_p l₁) * (z₂ * e6rz_p l₂) * ((e6rz_p l₂)⁻¹ * (e6rz_p l₁)⁻¹) =
      z₁ * (e6rz_p l₁ * z₂) * (e6rz_p l₁)⁻¹ by group]
    rw [hc]
    group
  rw [heq]
  exact z0Std.mul_mem hz₁' hz₂'

private theorem e6rz_K_inv_mem
    {u : EC}
    {l : List (Fin Tag.E6.rank → ℤ)} (hl : ∀ β ∈ l, β ∈ stdQRoots)
    (hz : u * (e6rz_p l)⁻¹ ∈ z0Std) :
    u⁻¹ * (e6rz_p l.reverse)⁻¹ ∈ z0Std := by
  obtain ⟨z, hz', rfl⟩ : ∃ z, z ∈ z0Std ∧ u = z * e6rz_p l := ⟨_, hz, by group⟩
  have hpinv : (e6rz_p l.reverse)⁻¹ = e6rz_p l := by
    rw [e6rz_p_reverse (fun β hβ => (hl β hβ).1)]
    group
  have heq : (z * e6rz_p l)⁻¹ * (e6rz_p l.reverse)⁻¹ = z⁻¹ := by
    rw [hpinv, mul_inv_rev]
    have hc := Subgroup.mem_centralizer_iff.1 (e6rz_z0Std_central (z0Std.inv_mem hz'))
      (e6rz_p l)⁻¹ (qStd.inv_mem (e6rz_p_mem_qStd hl))
    rw [hc]
    group
  rw [heq]
  exact z0Std.inv_mem hz'

private noncomputable def e6rz_K :
    Subgroup EC where
  carrier := {u | ∃ l, (∀ β ∈ l, β ∈ stdQRoots) ∧ u * (e6rz_p l)⁻¹ ∈ z0Std}
  mul_mem' := by
    intro u₁ u₂ hu₁ hu₂
    obtain ⟨l₁, hl₁, hz₁⟩ := hu₁
    obtain ⟨l₂, hl₂, hz₂⟩ := hu₂
    have hmem : ∀ β ∈ l₁ ++ l₂, β ∈ stdQRoots := by
      intro β hβ
      rcases List.mem_append.1 hβ with h | h
      · exact hl₁ β h
      · exact hl₂ β h
    exact ⟨l₁ ++ l₂, hmem, e6rz_K_mul_mem hl₁ hl₂ hz₁ hz₂⟩
  one_mem' := ⟨[], by simp, by simp [e6rz_p]⟩
  inv_mem' := by
    intro u hu
    obtain ⟨l, hl, hz⟩ := hu
    exact ⟨l.reverse, fun β hβ => hl β (List.mem_reverse.1 hβ), e6rz_K_inv_mem hl hz⟩

private theorem e6rz_qStd_le_K :
    qStd ≤ e6rz_K := by
  rw [e6rz_qStd_eq_closure]
  refine (Subgroup.closure_le _).mpr ?_
  rintro g ⟨β, hβ, rfl⟩
  refine ⟨[β], by simpa using hβ, ?_⟩
  simp [e6rz_p]

private theorem e6rz_stdL1_subset_stdQRoots
    : e6rz_stdL1 ⊆ stdQRoots :=
  fun γ hγ => e6rz_stdQRoots_eq ▸ Or.inl hγ

private theorem e6rz_mem_stdL1_of_root_add
    {β δ : Fin Tag.E6.rank → ℤ} (hβ : β ∈ stdQRoots) (hδ : δ ∈ e6rz_stdL1)
    (hmem : (β + δ) ∈ rootFinset .E6) : β ∈ e6rz_stdL1 := by
  rcases (e6rz_stdQRoots_eq ▸ hβ : β ∈ e6rz_stdL1 ∪ stdZRoots) with h | h
  · exact h
  · exfalso
    have h3 : 3 ≤ iform (β + δ) E6Pilot.yLamAS := by
      rw [iform_add_left]
      have h1 := h.2
      have h2 := hδ.2
      omega
    have h2 := e6rz_level_le_two (β + δ) hmem
    omega

private theorem e6rz_ne_of_mem_root_add
    {β δ : Fin Tag.E6.rank → ℤ} (hβ : β ∈ stdQRoots) (hδ : δ ∈ e6rz_stdL1)
    (hmem : (β + δ) ∈ rootFinset .E6) : β ≠ δ := by
  have hβ1 := e6rz_mem_stdL1_of_root_add hβ hδ hmem
  rintro rfl
  have hroot : IsRoot .E6 (β + β) := mem_rootFinset.1 hmem
  have h2 : IsRoot .E6 ((2 : ℤ) • β) := by
    have : (2 : ℤ) • β = β + β := by simp [two_smul]
    rwa [this]
  rcases h2.eq_one_or_neg_one_of_eq_smul (m := 2) rfl with h | h <;> omega

private theorem e6rz_ne_neg_of_mem_stdL1 
    {β δ : Fin Tag.E6.rank → ℤ} (hβ : β ∈ stdQRoots) (hδ : δ ∈ e6rz_stdL1) : β ≠ -δ := by
  rintro h
  have hδβ : δ = -β := by rw [h]; simp
  have h1 := hδ.2
  rw [hδβ, iform_neg_left] at h1
  have h2 := hβ.2
  omega

private theorem e6rz_pow_two_mul {G : Type*} [Group G]
    (a : G) (ha : a * a = 1) (k : ℕ) : a ^ (2 * k) = 1 := by
  rw [pow_mul, show a ^ 2 = 1 by rw [pow_two, ha], one_pow]

private theorem e6rz_pow_odd {G : Type*} [Group G]
    (a : G) (ha : a * a = 1) {n : ℕ} (hn : Odd n) : a ^ n = a := by
  obtain ⟨k, rfl⟩ := hn
  rw [pow_succ, e6rz_pow_two_mul a ha k, one_mul]

private theorem e6rz_pow_even {G : Type*} [Group G]
    (a : G) (ha : a * a = 1) {n : ℕ} (hn : Even n) : a ^ n = 1 := by
  obtain ⟨k, rfl⟩ := hn
  rw [← two_mul]
  exact e6rz_pow_two_mul a ha k

private theorem e6rz_pinnedX_commutator_E6
    {β δ : Fin Tag.E6.rank → ℤ}
    (hβ : IsRoot .E6 β) (hδ : IsRoot .E6 δ) (hne : β ≠ δ) (hne' : β ≠ -δ)
    (hadd : IsRoot .E6 (β + δ)) (c d : F2) :
    ⁅pinnedX .E6 F2 β c, pinnedX .E6 F2 δ d⁆ = pinnedX .E6 F2 (β + δ) (c * d) :=
  E6GraphLevi.commutator_pinnedX_of_two (E := F2) CharTwo.two_eq_zero hβ hδ hne hne' hadd c d

private theorem e6rz_comm_eq_of_mem
    {β δ : Fin Tag.E6.rank → ℤ}
    (hβ : β ∈ stdQRoots) (hδ : δ ∈ e6rz_stdL1) (hmem : (β + δ) ∈ rootFinset .E6) :
    ⁅xr β, xr δ⁆ = xr (β + δ) := by
  have hβ1 := e6rz_mem_stdL1_of_root_add hβ hδ hmem
  have hβδ := e6rz_ne_of_mem_root_add hβ hδ hmem
  have hne' := e6rz_ne_neg_of_mem_stdL1 hβ hδ
  have h2 : ⁅(xr β : ModGL .E6 F2), (xr δ : ModGL .E6 F2)⁆ = (xr (β + δ) : ModGL .E6 F2) := by
    show ⁅pinnedX .E6 F2 β 1, pinnedX .E6 F2 δ 1⁆ = pinnedX .E6 F2 (β + δ) 1
    simpa using e6rz_pinnedX_commutator_E6 hβ1.1 hδ.1 hβδ hne' (mem_rootFinset.1 hmem) 1 1
  have h1 : ((⁅xr β, xr δ⁆ : EC) : ModGL .E6 F2) =
      ⁅(xr β : ModGL .E6 F2), (xr δ : ModGL .E6 F2)⁆ :=
    map_commutatorElement (adjointGroup .E6 F2).subtype (xr β) (xr δ)
  exact Subtype.ext (h1.trans h2)

private theorem e6rz_comm_eq_one_of_not_mem
    {β δ : Fin Tag.E6.rank → ℤ} (hβ : β ∈ stdQRoots) (hδ : δ ∈ e6rz_stdL1)
    (hnot : (β + δ) ∉ rootFinset .E6) : ⁅xr β, xr δ⁆ = 1 := by
  rcases (e6rz_stdQRoots_eq ▸ hβ : β ∈ e6rz_stdL1 ∪ stdZRoots) with hβ1 | hβ2
  · by_cases hβδ : β = δ
    · subst hβδ
      rw [commutatorElement_self]
    · have hne' := e6rz_ne_neg_of_mem_stdL1 hβ hδ
      have hcomm := e6rz_xr_commute_of_not_isRoot_add hβ (e6rz_stdL1_subset_stdQRoots hδ)
        hβδ hne' (fun hr => hnot (mem_rootFinset.2 hr))
      rw [commutatorElement_eq_one_iff_mul_comm.2 hcomm]
  · have hxrZ : xr β ∈ z0Std := by
      rw [e6rz_z0Std_eq_closure]
      exact Subgroup.subset_closure ⟨β, hβ2, rfl⟩
    have hδq : xr δ ∈ qStd := by
      rw [e6rz_qStd_eq_closure]
      exact Subgroup.subset_closure ⟨δ, e6rz_stdL1_subset_stdQRoots hδ, rfl⟩
    have hcomm := Subgroup.mem_centralizer_iff.1 (e6rz_z0Std_central hxrZ) (xr δ) hδq
    rw [commutatorElement_eq_one_iff_mul_comm.2 hcomm.symm]

private theorem e6rz_comm_mem_z0
    {β δ : Fin Tag.E6.rank → ℤ}
    (hβ : β ∈ stdQRoots) (hδ : δ ∈ e6rz_stdL1) : ⁅xr β, xr δ⁆ ∈ z0Std := by
  by_cases hmem : (β + δ) ∈ rootFinset .E6
  · rw [e6rz_comm_eq_of_mem hβ hδ hmem, e6rz_z0Std_eq_closure]
    refine Subgroup.subset_closure ⟨β + δ, ⟨mem_rootFinset.1 hmem, ?_⟩, rfl⟩
    rw [iform_add_left]
    have h1 := (e6rz_mem_stdL1_of_root_add hβ hδ hmem).2
    have h2 := hδ.2
    omega
  · rw [e6rz_comm_eq_one_of_not_mem hβ hδ hmem]
    exact z0Std.one_mem

private theorem e6rz_commutator_prod
    {l : List (Fin Tag.E6.rank → ℤ)} (hl : ∀ β ∈ l, β ∈ stdQRoots)
    {δ : Fin Tag.E6.rank → ℤ} (hδ : δ ∈ e6rz_stdL1) :
    ⁅e6rz_p l, xr δ⁆ = (l.map (fun β => ⁅xr β, xr δ⁆)).prod := by
  induction l with
  | nil => simp [e6rz_p]
  | cons a l ih =>
    have hl' : ∀ β ∈ l, β ∈ stdQRoots := fun β hβ => hl β (List.mem_cons_of_mem _ hβ)
    have ha := hl a List.mem_cons_self
    have hmeml : (l.map (fun β => ⁅xr β, xr δ⁆)).prod ∈ z0Std := by
      refine Subgroup.list_prod_mem (K := z0Std) ?_
      intro x hx
      obtain ⟨β, hβ, rfl⟩ := List.mem_map.1 hx
      exact e6rz_comm_mem_z0 (hl' β hβ) hδ
    have hih : ⁅e6rz_p l, xr δ⁆ ∈ z0Std := by rw [ih hl']; exact hmeml
    have haq : xr a ∈ qStd := by
      rw [e6rz_qStd_eq_closure]
      exact Subgroup.subset_closure ⟨a, ha, rfl⟩
    have hcent : xr a * ⁅e6rz_p l, xr δ⁆ * (xr a)⁻¹ = ⁅e6rz_p l, xr δ⁆ := by
      have h := Subgroup.mem_centralizer_iff.1 (e6rz_z0Std_central hih) (xr a) haq
      rw [h, mul_assoc, mul_inv_cancel, mul_one]
    rw [show e6rz_p (a :: l) = xr a * e6rz_p l by
      simp [e6rz_p, List.map_cons, List.prod_cons]]
    rw [List.map_cons, List.prod_cons]
    rw [commutatorElement_mul_left_eq_conj_mul, hcent, ih hl']
    exact (e6rz_z0Std_comm (e6rz_comm_mem_z0 ha hδ) hmeml).symm

private noncomputable instance e6rz_z0Std_commMonoid :
    CommMonoid ↥z0Std :=
  { (inferInstance : Group ↥z0Std) with
    mul_comm := fun a b => Subtype.ext (e6rz_z0Std_comm a.2 b.2) }

private noncomputable def e6rz_zr
    (γ : Fin Tag.E6.rank → ℤ) : z0Std := by
  classical
  exact if h : γ ∈ stdZRoots then
    ⟨xr γ, by
      rw [e6rz_z0Std_eq_closure]
      exact Subgroup.subset_closure ⟨γ, h, rfl⟩⟩
  else 1

private theorem e6rz_zr_of_mem
    {γ : Fin Tag.E6.rank → ℤ} (h : γ ∈ stdZRoots) : ((e6rz_zr γ : z0Std) : EC) = xr γ := by
  rw [e6rz_zr]
  simp only [dif_pos h]

private theorem e6rz_zr_pow_count
    {γ : Fin Tag.E6.rank → ℤ} (h : γ ∈ stdZRoots) (n : ℕ) :
    e6rz_zr γ ^ n = if Odd n then e6rz_zr γ else 1 := by
  have hzz : e6rz_zr γ * e6rz_zr γ = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, e6rz_zr_of_mem h, e6rz_xr_mul_self h.1]
    rfl
  rcases Nat.even_or_odd n with he | ho
  · rw [if_neg (Nat.not_odd_iff_even.2 he)]
    exact e6rz_pow_even _ hzz he
  · rw [if_pos ho]
    exact e6rz_pow_odd _ hzz ho

private noncomputable def e6rz_cz
    (l : List (Fin Tag.E6.rank → ℤ)) (δ : Fin Tag.E6.rank → ℤ) (hδ : δ ∈ e6rz_stdL1)
    (hl : ∀ β ∈ l, β ∈ stdQRoots) (β : Fin Tag.E6.rank → ℤ) : z0Std := by
  classical
  exact if h : β ∈ l then ⟨⁅xr β, xr δ⁆, e6rz_comm_mem_z0 (hl β h) hδ⟩ else 1

private theorem e6rz_cz_of_mem
    {l : List (Fin Tag.E6.rank → ℤ)} {δ : Fin Tag.E6.rank → ℤ} {hδ : δ ∈ e6rz_stdL1}
    {hl : ∀ β ∈ l, β ∈ stdQRoots} {β : Fin Tag.E6.rank → ℤ} (hβ : β ∈ l) :
    ((e6rz_cz l δ hδ hl β : z0Std) : EC) = ⁅xr β, xr δ⁆ := by
  rw [e6rz_cz]
  simp only [dif_pos hβ]

private theorem e6rz_pairing_eq
    {l : List (Fin Tag.E6.rank → ℤ)} (hl : ∀ β ∈ l, β ∈ stdQRoots)
    {δ : Fin Tag.E6.rank → ℤ} (hδ : δ ∈ e6rz_stdL1) :
    (l.map (e6rz_cz l δ hδ hl)).prod =
      ∏ β ∈ l.toFinset.filter (fun β => Odd (l.count β) ∧ (β + δ) ∈ rootFinset .E6),
        e6rz_zr (β + δ) := by
  rw [Finset.prod_list_map_count, Finset.prod_filter]
  refine Finset.prod_congr rfl ?_
  intro β hβ
  have hβmem : β ∈ l := List.mem_toFinset.1 hβ
  have hβQ := hl β hβmem
  have hcz : ((e6rz_cz l δ hδ hl β : z0Std) : EC) = ⁅xr β, xr δ⁆ := e6rz_cz_of_mem hβmem
  rcases (e6rz_stdQRoots_eq ▸ hβQ : β ∈ e6rz_stdL1 ∪ stdZRoots) with hβ1 | hβ2
  · by_cases hroot : (β + δ) ∈ rootFinset .E6
    · have hmemZ : (β + δ) ∈ stdZRoots := ⟨mem_rootFinset.1 hroot, by
        rw [iform_add_left]
        have h1 := hβ1.2
        have h2 := hδ.2
        omega⟩
      have hczz : e6rz_cz l δ hδ hl β = e6rz_zr (β + δ) := by
        apply Subtype.ext
        rw [hcz, e6rz_zr_of_mem hmemZ, e6rz_comm_eq_of_mem hβQ hδ hroot]
      rw [hczz, e6rz_zr_pow_count hmemZ (l.count β)]
      by_cases hodd : Odd (l.count β)
      · rw [if_pos hodd, if_pos ⟨hodd, hroot⟩]
      · rw [if_neg hodd, if_neg (fun h => hodd h.1)]
    · have hcz1 : e6rz_cz l δ hδ hl β = 1 := by
        apply Subtype.ext
        rw [hcz, e6rz_comm_eq_one_of_not_mem hβQ hδ hroot]
        rfl
      rw [hcz1, one_pow, if_neg (fun h => hroot h.2)]
  · have hnotroot : (β + δ) ∉ rootFinset .E6 := by
      intro hmem
      have h3 : 3 ≤ iform (β + δ) E6Pilot.yLamAS := by
        rw [iform_add_left]
        have h1 := hβ2.2
        have h2 := hδ.2
        omega
      have h2' := e6rz_level_le_two (β + δ) hmem
      omega
    have hxrZ : xr β ∈ z0Std := by
      rw [e6rz_z0Std_eq_closure]
      exact Subgroup.subset_closure ⟨β, hβ2, rfl⟩
    have hδq : xr δ ∈ qStd := by
      rw [e6rz_qStd_eq_closure]
      exact Subgroup.subset_closure ⟨δ, e6rz_stdL1_subset_stdQRoots hδ, rfl⟩
    have hval : ⁅xr β, xr δ⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.2
        (Subgroup.mem_centralizer_iff.1 (e6rz_z0Std_central hxrZ) (xr δ) hδq).symm
    have hcz1 : e6rz_cz l δ hδ hl β = 1 := by
      apply Subtype.ext
      rw [hcz, hval]
      rfl
    rw [hcz1, one_pow, if_neg (fun h => hnotroot h.2)]

private theorem e6rz_z0_indep
    {T : Finset (Fin Tag.E6.rank → ℤ)} (hT : ∀ γ ∈ T, γ ∈ stdZRoots)
    (h : (∏ γ ∈ T, e6rz_zr γ) = 1) : T = ∅ := by
  by_contra hne
  have hLpos : ∀ γ ∈ T.toList, IsRoot .E6 γ ∧ 0 < height γ := by
    intro γ hγ
    have hγT : γ ∈ T := T.mem_toList.1 hγ
    exact ⟨(hT γ hγT).1, e6rz_l2_pos γ (mem_rootFinset.2 (hT γ hγT).1) (hT γ hγT).2⟩
  have hlist : (T.toList.map e6rz_zr).prod = 1 := by
    rw [← List.prod_toFinset e6rz_zr T.nodup_toList]
    simpa using h
  have hval : ((T.toList.map e6rz_zr).prod : EC) = (T.toList.map (fun γ => xr γ)).prod := by
    change z0Std.subtype (T.toList.map e6rz_zr).prod = _
    rw [map_list_prod, List.map_map]
    exact congrArg List.prod (List.map_congr_left
      (fun γ hγ => e6rz_zr_of_mem (hT γ (T.mem_toList.1 hγ))))
  have hxr : (T.toList.map (fun γ => xr γ)).prod = 1 := by
    rw [← hval, hlist]
    rfl
  have hmap : (T.toList.map (fun γ => pinnedX .E6 F2 γ 1)).prod =
      ((T.toList.map (fun γ => xr γ)).prod : ModGL .E6 F2) := by
    change (T.toList.map (fun γ => pinnedX .E6 F2 γ 1)).prod =
      (adjointGroup .E6 F2).subtype ((T.toList.map (fun γ => xr γ)).prod)
    rw [map_list_prod, List.map_map]
    rfl
  have hprod : (T.toList.map (fun γ => pinnedX .E6 F2 γ (1 : F2))).prod =
      (T.toList.map (fun γ => pinnedX .E6 F2 γ (0 : F2))).prod := by
    rw [hmap, hxr]
    simp [pinnedX_zero]
  have hinj := pinnedX_list_prod_injective (τ := .E6) (R := F2) T.toList T.nodup_toList hLpos
    (fun _ => (1 : F2)) (fun _ => (0 : F2)) hprod
  obtain ⟨γ0, hγ0⟩ := Finset.nonempty_iff_ne_empty.2 hne
  exact one_ne_zero (hinj γ0 (T.mem_toList.2 hγ0))

private theorem e6rz_z0_prod_image_eq_one
    {s : Finset (Fin Tag.E6.rank → ℤ)} {δ : Fin Tag.E6.rank → ℤ}
    (hβQ : ∀ β ∈ s, β ∈ stdQRoots) (hs : ∀ β ∈ s, (β + δ) ∈ rootFinset .E6)
    (hδ : δ ∈ e6rz_stdL1) (h : (∏ β ∈ s, e6rz_zr (β + δ)) = 1) : s = ∅ := by
  have hinj : ∀ β ∈ s, ∀ β' ∈ s, β + δ = β' + δ → β = β' :=
    fun β _ β' _ heq => add_right_cancel heq
  have himg : (∏ γ ∈ s.image (fun β => β + δ), e6rz_zr γ) = 1 := by
    rw [Finset.prod_image hinj]
    exact h
  have hT : ∀ γ ∈ s.image (fun β => β + δ), γ ∈ stdZRoots := by
    intro γ hγ
    obtain ⟨β, hβ, rfl⟩ := Finset.mem_image.1 hγ
    refine ⟨mem_rootFinset.1 (hs β hβ), ?_⟩
    rw [iform_add_left]
    rcases (e6rz_stdQRoots_eq ▸ hβQ β hβ : β ∈ e6rz_stdL1 ∪ stdZRoots) with h1 | h2
    · have h1' := h1.2
      have h2' := hδ.2
      omega
    · exfalso
      have h3 : 3 ≤ iform (β + δ) E6Pilot.yLamAS := by
        rw [iform_add_left]
        have h1 := h2.2
        have h2 := hδ.2
        omega
      have h2' := e6rz_level_le_two (β + δ) (hs β hβ)
      omega
  exact Finset.image_eq_empty.1 (e6rz_z0_indep hT himg)

private theorem e6rz_comm_mem_z0'
    {β δ : Fin Tag.E6.rank → ℤ} (hβ : β ∈ stdQRoots) (hδ : δ ∈ stdQRoots) :
    ⁅xr β, xr δ⁆ ∈ z0Std := by
  rcases (e6rz_stdQRoots_eq ▸ hδ : δ ∈ e6rz_stdL1 ∪ stdZRoots) with hδ1 | hδ2
  · exact e6rz_comm_mem_z0 hβ hδ1
  · have hxrZ : xr δ ∈ z0Std := by
      rw [e6rz_z0Std_eq_closure]
      exact Subgroup.subset_closure ⟨δ, hδ2, rfl⟩
    have hβq : xr β ∈ qStd := by
      rw [e6rz_qStd_eq_closure]
      exact Subgroup.subset_closure ⟨β, hβ, rfl⟩
    have hc := Subgroup.mem_centralizer_iff.1 (e6rz_z0Std_central hxrZ) (xr β) hβq
    rw [commutatorElement_eq_one_iff_mul_comm.2 hc]
    exact z0Std.one_mem

private theorem e6rz_commutator_mem_z0
    {g₁ g₂ : EC}
    (h₁ : g₁ ∈ qStd) (h₂ : g₂ ∈ qStd) : ⁅g₁, g₂⁆ ∈ z0Std := by
  rw [e6rz_qStd_eq_closure] at h₁ h₂
  have hP : ∀ g ∈ Subgroup.closure {x : EC | ∃ β ∈ stdQRoots, xr β = x},
      ∀ g₂ ∈ Subgroup.closure {x : EC | ∃ β ∈ stdQRoots, xr β = x}, ⁅g, g₂⁆ ∈ z0Std := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem a ha =>
        obtain ⟨β, hβ, rfl⟩ := ha
        intro g₂ hg₂
        induction hg₂ using Subgroup.closure_induction with
        | mem b hb =>
            obtain ⟨δ, hδ, rfl⟩ := hb
            exact e6rz_comm_mem_z0' hβ hδ
        | one => rw [commutatorElement_one_right]; exact z0Std.one_mem
        | mul b c hb hc ihb ihc =>
            rw [commutatorElement_mul_right_eq_mul_conj]
            have hbq : b ∈ qStd := by rw [e6rz_qStd_eq_closure]; exact hb
            have hcen : b * ⁅xr β, c⁆ * b⁻¹ = ⁅xr β, c⁆ := by
              have := Subgroup.mem_centralizer_iff.1 (e6rz_z0Std_central ihc) b hbq
              rw [this, mul_assoc, mul_inv_cancel, mul_one]
            have heq : ⁅xr β, b⁆ * b * ⁅xr β, c⁆ * b⁻¹ =
                ⁅xr β, b⁆ * ⁅xr β, c⁆ := by
              rw [show ⁅xr β, b⁆ * b * ⁅xr β, c⁆ * b⁻¹ =
                ⁅xr β, b⁆ * (b * ⁅xr β, c⁆ * b⁻¹) by group, hcen]
            rw [heq]
            exact z0Std.mul_mem ihb ihc
        | inv b hb ihb =>
            rw [commutatorElement_inv_right]
            have hbq : b ∈ qStd := by rw [e6rz_qStd_eq_closure]; exact hb
            have hib : ⁅b, xr β⁆ ∈ z0Std := by
              rw [show ⁅b, xr β⁆ = ⁅xr β, b⁆⁻¹ from
                (commutatorElement_inv (xr β) b).symm]
              exact z0Std.inv_mem ihb
            have hcen := Subgroup.mem_centralizer_iff.1 (e6rz_z0Std_central hib) b⁻¹
              (qStd.inv_mem hbq)
            rw [show b⁻¹ * ⁅b, xr β⁆ * b = ⁅b, xr β⁆ by
              rw [hcen, mul_assoc, inv_mul_cancel, mul_one]]
            exact hib
    | one => intro g₂ hg₂; rw [commutatorElement_one_left]; exact z0Std.one_mem
    | mul a b ha hb iha ihb =>
        intro g₂ hg₂
        rw [commutatorElement_mul_left_eq_conj_mul]
        have haq : a ∈ qStd := by rw [e6rz_qStd_eq_closure]; exact ha
        have hcen : a * ⁅b, g₂⁆ * a⁻¹ = ⁅b, g₂⁆ := by
          have := Subgroup.mem_centralizer_iff.1 (e6rz_z0Std_central (ihb g₂ hg₂)) a haq
          rw [this, mul_assoc, mul_inv_cancel, mul_one]
        rw [hcen]
        exact z0Std.mul_mem (ihb g₂ hg₂) (iha g₂ hg₂)
    | inv a ha iha =>
        intro g₂ hg₂
        rw [commutatorElement_inv_left]
        have haq : a ∈ qStd := by rw [e6rz_qStd_eq_closure]; exact ha
        have hia : ⁅g₂, a⁆ ∈ z0Std := by
          rw [show ⁅g₂, a⁆ = ⁅a, g₂⁆⁻¹ from (commutatorElement_inv a g₂).symm]
          exact z0Std.inv_mem (iha g₂ hg₂)
        have hcen := Subgroup.mem_centralizer_iff.1 (e6rz_z0Std_central hia) a⁻¹
          (qStd.inv_mem haq)
        rw [show a⁻¹ * ⁅g₂, a⁆ * a = ⁅g₂, a⁆ by
          rw [hcen, mul_assoc, inv_mul_cancel, mul_one]]
        exact hia
  exact hP g₁ h₁ g₂ h₂

private noncomputable def e6rz_N :
    Subgroup qStd :=
  z0Std.subgroupOf qStd

private noncomputable instance e6rz_N_normal :
    e6rz_N.Normal := by
  rw [e6rz_N, Subgroup.normal_subgroupOf_iff e6rz_z0Std_le_qStd]
  intro h k hh hk
  have hc := Subgroup.mem_centralizer_iff.1 (e6rz_z0Std_central hh) k hk
  rw [hc, mul_assoc, mul_inv_cancel, mul_one]
  exact hh

private theorem e6rz_quotient_mul_comm :
    ∀ x y : qStd ⧸ e6rz_N, x * y = y * x := by
  intro x y
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective e6rz_N x
  obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective e6rz_N y
  rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_iff_div_mem]
  have hc : ⁅a, b⁆ ∈ e6rz_N := by
    rw [e6rz_N, Subgroup.mem_subgroupOf]
    change ⁅(a : EC), (b : EC)⁆ ∈ z0Std
    exact e6rz_commutator_mem_z0 a.2 b.2
  simpa [commutatorElement_def, div_eq_mul_inv, mul_assoc] using hc

private noncomputable def e6rz_xrq
    (β : Fin Tag.E6.rank → ℤ) : qStd := by
  classical
  exact if h : β ∈ stdQRoots then
    ⟨xr β, by rw [e6rz_qStd_eq_closure]; exact Subgroup.subset_closure ⟨β, h, rfl⟩⟩
  else 1

private theorem e6rz_xrq_val
    {β : Fin Tag.E6.rank → ℤ} (hβ : β ∈ stdQRoots) : ((e6rz_xrq β : qStd) : EC) = xr β := by
  rw [e6rz_xrq]
  simp only [dif_pos hβ]

private theorem e6rz_p_mem_z0_of_even
    {l : List (Fin Tag.E6.rank → ℤ)} (hl : ∀ β ∈ l, β ∈ stdQRoots)
    (heven : ∀ β ∈ l, β ∈ e6rz_stdL1 → Even (l.count β)) : e6rz_p l ∈ z0Std := by
  letI : CommMonoid (qStd ⧸ e6rz_N) :=
    { (inferInstance : Group (qStd ⧸ e6rz_N)) with mul_comm := e6rz_quotient_mul_comm }
  have hp : (⟨e6rz_p l, e6rz_p_mem_qStd hl⟩ : qStd) = (l.map e6rz_xrq).prod := by
    apply Subtype.ext
    change e6rz_p l = qStd.subtype (l.map e6rz_xrq).prod
    rw [e6rz_p, map_list_prod, List.map_map]
    exact congrArg List.prod (List.map_congr_left (fun β hβ => (e6rz_xrq_val (hl β hβ)).symm))
  have hphi : QuotientGroup.mk' e6rz_N (l.map e6rz_xrq).prod =
      (l.map (fun β => QuotientGroup.mk' e6rz_N (e6rz_xrq β))).prod :=
    (List.prod_map_hom l e6rz_xrq (QuotientGroup.mk' e6rz_N)).symm
  have hcount := Finset.prod_list_map_count l (fun β => QuotientGroup.mk' e6rz_N (e6rz_xrq β))
  have h1 : ∀ β ∈ l.toFinset, (QuotientGroup.mk' e6rz_N (e6rz_xrq β)) ^ (l.count β) = 1 := by
    intro β hβ
    have hβmem := List.mem_toFinset.1 hβ
    have hβQ := hl β hβmem
    rcases (e6rz_stdQRoots_eq ▸ hβQ : β ∈ e6rz_stdL1 ∪ stdZRoots) with hβ1 | hβ2
    · refine e6rz_pow_even _ ?_ (heven β hβmem hβ1)
      rw [← map_mul, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, e6rz_N,
        Subgroup.mem_subgroupOf]
      change ((e6rz_xrq β : qStd) : EC) * ((e6rz_xrq β : qStd) : EC) ∈ z0Std
      rw [e6rz_xrq_val hβQ, e6rz_xr_mul_self hβQ.1]
      exact z0Std.one_mem
    · have hone : QuotientGroup.mk' e6rz_N (e6rz_xrq β) = 1 := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, e6rz_N, Subgroup.mem_subgroupOf]
        change ((e6rz_xrq β : qStd) : EC) ∈ z0Std
        rw [e6rz_xrq_val hβQ, e6rz_z0Std_eq_closure]
        exact Subgroup.subset_closure ⟨β, hβ2, rfl⟩
      rw [hone, one_pow]
  have hmk : QuotientGroup.mk' e6rz_N (⟨e6rz_p l, e6rz_p_mem_qStd hl⟩ : qStd) = 1 := by
    rw [hp, hphi, hcount]
    exact Finset.prod_eq_one h1
  have hmemN : (⟨e6rz_p l, e6rz_p_mem_qStd hl⟩ : qStd) ∈ e6rz_N :=
    (QuotientGroup.eq_one_iff _).1 hmk
  rw [e6rz_N, Subgroup.mem_subgroupOf] at hmemN
  exact hmemN

private theorem e6rz_center_qStd :
    (Subgroup.center ↥qStd).map qStd.subtype = z0Std := by
  refine le_antisymm ?_ ?_
  · rintro g hg
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.1 hg
    obtain ⟨l, hl, hz⟩ := e6rz_qStd_le_K q.2
    have hfilter : ∀ δ ∈ e6rz_stdL1,
        (l.toFinset.filter (fun β => Odd (l.count β) ∧ (β + δ) ∈ rootFinset .E6)) = ∅ := by
      intro δ hδ
      have hδq : xr δ ∈ qStd := by
        rw [e6rz_qStd_eq_closure]
        exact Subgroup.subset_closure ⟨δ, e6rz_stdL1_subset_stdQRoots hδ, rfl⟩
      have hcomm : (q : EC) * xr δ = xr δ * (q : EC) := by
        have hh := congrArg Subtype.val (Subgroup.mem_center_iff.1 hq ⟨xr δ, hδq⟩)
        simpa using hh.symm
      have hqp : ⁅(q : EC), xr δ⁆ = ⁅e6rz_p l, xr δ⁆ := by
        have hqdecomp : (q : EC) = (q * (e6rz_p l)⁻¹) * e6rz_p l := by group
        conv_lhs => rw [hqdecomp]
        rw [commutatorElement_mul_left_eq_conj_mul]
        have hpl : e6rz_p l ∈ qStd := e6rz_p_mem_qStd hl
        have hc : ⁅e6rz_p l, xr δ⁆ ∈ qStd := by
          rw [commutatorElement_def]
          exact qStd.mul_mem (qStd.mul_mem (qStd.mul_mem hpl hδq) (qStd.inv_mem hpl))
            (qStd.inv_mem hδq)
        have hzc := (Subgroup.mem_centralizer_iff.1 (e6rz_z0Std_central hz) _ hc).symm
        have hzx : (q * (e6rz_p l)⁻¹) * xr δ = xr δ * (q * (e6rz_p l)⁻¹) :=
          (Subgroup.mem_centralizer_iff.1 (e6rz_z0Std_central hz) _ hδq).symm
        have hz1 : ⁅q * (e6rz_p l)⁻¹, xr δ⁆ = 1 :=
          commutatorElement_eq_one_iff_mul_comm.2 hzx
        rw [hzc, hz1, mul_one]
        group
      have hp1 : ⁅e6rz_p l, xr δ⁆ = 1 := by
        rw [← hqp]
        exact commutatorElement_eq_one_iff_mul_comm.2 hcomm
      have h2 : (l.map (fun β => ⁅xr β, xr δ⁆)).prod = 1 := by
        rw [← e6rz_commutator_prod hl hδ]
        exact hp1
      have h3 : ((l.map (e6rz_cz l δ hδ hl)).prod : EC) =
          (l.map (fun β => ⁅xr β, xr δ⁆)).prod := by
        change z0Std.subtype (l.map (e6rz_cz l δ hδ hl)).prod = _
        rw [map_list_prod, List.map_map]
        exact congrArg List.prod (List.map_congr_left (fun β hβ => e6rz_cz_of_mem hβ))
      have h4 : (l.map (e6rz_cz l δ hδ hl)).prod = 1 := by
        apply Subtype.ext
        rw [h3, h2]
        rfl
      have h5 : (∏ β ∈ l.toFinset.filter
          (fun β => Odd (l.count β) ∧ (β + δ) ∈ rootFinset .E6), e6rz_zr (β + δ)) = 1 := by
        rw [← e6rz_pairing_eq hl hδ]
        exact h4
      exact e6rz_z0_prod_image_eq_one
        (fun β hβ => hl β (List.mem_toFinset.1 (Finset.mem_filter.1 hβ).1))
        (fun β hβ => (Finset.mem_filter.1 hβ).2.2) hδ h5
    have heven : ∀ β ∈ l.toFinset, β ∈ e6rz_stdL1 → Even (l.count β) := by
      intro β hβ hβ1
      by_contra hne
      have hodd : Odd (l.count β) := Nat.not_even_iff_odd.1 hne
      obtain ⟨δ, hδ, hroot⟩ := e6rz_partner_mem hβ1
      have hmem : β ∈ l.toFinset.filter
          (fun β => Odd (l.count β) ∧ (β + δ) ∈ rootFinset .E6) :=
        Finset.mem_filter.2 ⟨hβ, hodd, mem_rootFinset.2 hroot⟩
      rw [hfilter δ hδ] at hmem
      exact Finset.notMem_empty β hmem
    have hp : e6rz_p l ∈ z0Std :=
      e6rz_p_mem_z0_of_even hl (fun β hβ hβ1 => heven β (List.mem_toFinset.2 hβ) hβ1)
    have hqdecomp : (q : EC) = (q * (e6rz_p l)⁻¹) * e6rz_p l := by group
    change (q : EC) ∈ z0Std
    rw [hqdecomp]
    exact z0Std.mul_mem hz hp
  · rintro g hg
    refine Subgroup.mem_map.2 ⟨⟨g, e6rz_z0Std_le_qStd hg⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro x
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 (e6rz_z0Std_central hg) (x : EC) x.2)

private theorem e6rz_center_map_injective {G : Type*} [Group G] (H : Subgroup G)
    {f : G →* G} (hf : Function.Injective f) :
    (Subgroup.center ↥(H.map f)).map (H.map f).subtype =
      ((Subgroup.center ↥H).map H.subtype).map f := by
  let φ : ↥H ≃* ↥(H.map f) := H.equivMapOfInjective f hf
  have hcomp : (H.map f).subtype.comp φ.toMonoidHom = f.comp H.subtype := by
    ext x
    rfl
  have hcenter : Subgroup.center ↥(H.map f) =
      Subgroup.map φ.toMonoidHom (Subgroup.center ↥H) := (Subgroup.map_center_eq φ).symm
  rw [hcenter, Subgroup.map_map, hcomp, ← Subgroup.map_map]

end CFSG.StandardType.GGSixE6Two

public section

namespace CFSG.StandardType.GGSixE6Two

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open CFSG.SeitzReduction
  CFSG.StandardType.GGHalf CFSG.Timmesfeld.LieEmbed CFSG.LieType.Steinberg.Adjoint

theorem center_qE :
    (Subgroup.center ↥qE).map qE.subtype = z0E := by
  have h := e6rz_center_map_injective (f := (MulAut.conj nQ).toMonoidHom) qStd
    (MulAut.conj nQ).injective
  rw [← qE_eq_map_qStd, e6rz_center_qStd, ← z0E_eq_map_z0Std] at h
  exact h

end CFSG.StandardType.GGSixE6Two

