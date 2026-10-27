module

public import CFSG.Fischer.Uniq.Graph
public import CFSG.Fischer.Aut.Generate
public import CFSG.Sporadic.Fi23.Centralizer

public section

namespace CFSG.Sporadic.Fi23

open CFSG.Blueprint.Fischer CFSG.Fischer

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem d_zpow (k : ℤ) : d ^ k = 1 ∨ d ^ k = d := by
  have h2 : d ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact d_sq
  obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
  · left; rw [zpow_mul, h2, one_zpow]
  · right; rw [zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]

theorem eq_of_centralizes_star_d
    {g : J} (hg : g * d = d * g)
    (h : ∀ x ∈ LocalClass D23 d, g * x * g⁻¹ = x) : g = 1 ∨ g = d := by
  have hgC : g ∈ Cd := mem_Cd.2 hg
  have hker : (⟨g, hgC⟩ : Cd) ∈ rho.ker := by
    rw [MonoidHom.mem_ker]
    refine Equiv.ext fun u => ?_
    rw [rho_apply]
    have : (⟨g, hgC⟩ : Cd) • ptE u = ptE u := Subtype.ext (h _ (ptE u).2)
    rw [this, Equiv.symm_apply_apply]
    rfl
  rw [ker_rho] at hker
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hker
  have hk' : d ^ k = g := by
    have := congrArg Subtype.val hk
    rwa [Subgroup.coe_zpow] at this
  rcases d_zpow k with h1 | h1
  · exact Or.inl (hk'.symm.trans h1)
  · exact Or.inr (hk'.symm.trans h1)

theorem eq_of_centralizes_star
    {s : J} (hs : s ∈ D23) {g : J} (hg : g * s = s * g)
    (h : ∀ x ∈ LocalClass D23 s, g * x * g⁻¹ = x) : g = 1 ∨ g = s := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 hs
  have hg' : c⁻¹ * g * c * d = d * (c⁻¹ * g * c) := by
    calc c⁻¹ * g * c * d = c⁻¹ * (g * (c * d * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * d * c⁻¹) * g) * c := by rw [hg]
      _ = d * (c⁻¹ * g * c) := by group
  have h' : ∀ x ∈ LocalClass D23 d, (c⁻¹ * g * c) * x * (c⁻¹ * g * c)⁻¹ = x := by
    intro x hx
    have hx' : c * x * c⁻¹ ∈ LocalClass D23 (c * d * c⁻¹) :=
      (Pair.conj_mem_localClass_iff pair_J c).2 hx
    have e := h _ hx'
    calc (c⁻¹ * g * c) * x * (c⁻¹ * g * c)⁻¹ = c⁻¹ * (g * (c * x * c⁻¹) * g⁻¹) * c := by group
      _ = c⁻¹ * (c * x * c⁻¹) * c := by rw [e]
      _ = x := by group
  rcases eq_of_centralizes_star_d hg' h' with h1 | h1
  · left
    calc g = c * (c⁻¹ * g * c) * c⁻¹ := by group
      _ = 1 := by rw [h1]; group
  · right
    calc g = c * (c⁻¹ * g * c) * c⁻¹ := by group
      _ = c * d * c⁻¹ := by rw [h1]

theorem isCoatom_centralizer_d :
    IsCoatom (Subgroup.centralizer ({d} : Set J)) := by
  have := isPreprimitive
  rw [← stabilizer_root_eq_centralizer]
  exact MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive J root

theorem isCoatom_centralizer_of_mem {s : J} (hs : s ∈ D23) :
    IsCoatom (Subgroup.centralizer ({s} : Set J)) := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 hs
  have e := centralizer_singleton_eq_map (MulAut.conj c) d
  rw [MulAut.conj_apply] at e
  rw [e]
  exact ((MulAut.conj c).mapSubgroup.isCoatom_iff _).2 isCoatom_centralizer_d

theorem card_centralizer_of_mem {s : J} (hs : s ∈ D23) :
    Nat.card (Subgroup.centralizer ({s} : Set J)) = 129123503308800 := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 hs
  rw [card_centralizer_conj c d]
  exact card_centralizer_d

theorem commutator_centralizer_of_mem
    {s : J} (hs : s ∈ D23) :
    commutator (Subgroup.centralizer ({s} : Set J)) = ⊤ := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 hs
  exact commutator_centralizer_conj c d commutator_C

end CFSG.Sporadic.Fi23
