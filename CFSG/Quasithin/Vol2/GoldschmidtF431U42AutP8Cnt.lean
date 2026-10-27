module

public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.Group

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

variable {G : Type*} [Group G]

@[expose, instance_reducible] def conjEltAction (H : Subgroup G) : MulAction ↥H G where
  smul h x := (h : G) * x * (h : G)⁻¹
  one_smul x := by
    show ((1 : ↥H) : G) * x * ((1 : ↥H) : G)⁻¹ = x
    simp
  mul_smul a b x := by
    show ((a * b : ↥H) : G) * x * ((a * b : ↥H) : G)⁻¹ =
      (a : G) * ((b : G) * x * (b : G)⁻¹) * (a : G)⁻¹
    simp [mul_assoc]

theorem card_le_mul_of_conj_elt [Finite G] {H : Subgroup G} {x : G} {S : Finset G}
    (h : ∀ a ∈ H, a * x * a⁻¹ ∈ S) :
    Nat.card ↥H ≤ Nat.card ↥(H ⊓ Subgroup.centralizer ({x} : Set G)) * S.card := by
  classical
  let inst : MulAction ↥H G := conjEltAction H
  have hidx := MulAction.index_stabilizer ↥H x
  have hcard := Subgroup.card_mul_index (MulAction.stabilizer ↥H x)
  have hsub : MulAction.orbit ↥H x ⊆ ↑S := by
    intro C hC
    rw [MulAction.mem_orbit_iff] at hC
    obtain ⟨a, rfl⟩ := hC
    exact h a a.2
  have hncard : (MulAction.orbit ↥H x).ncard ≤ S.card :=
    (Set.ncard_le_ncard hsub (Finset.finite_toSet _)).trans (by rw [Set.ncard_coe_finset])
  have e : (H ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf H = MulAction.stabilizer ↥H x := by
    ext a
    rw [Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff]
    constructor
    · rintro ⟨-, ha⟩
      have ha' : (a : G) * x = x * a := Subgroup.mem_centralizer_singleton_iff.1 ha
      show (a : G) * x * (a : G)⁻¹ = x
      rw [ha']
      group
    · intro ha
      have ha' : (a : G) * x * (a : G)⁻¹ = x := ha
      refine ⟨a.2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      calc (a : G) * x = (a : G) * x * (a : G)⁻¹ * a := by group
        _ = x * a := by rw [ha']
  have hstab : Nat.card ↥(MulAction.stabilizer ↥H x) =
      Nat.card ↥(H ⊓ Subgroup.centralizer ({x} : Set G)) := by
    rw [← e]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [hstab, hidx] at hcard
  rw [← hcard]
  exact Nat.mul_le_mul_left _ hncard

theorem mulMap_injective {A B E : Subgroup G} (hA : A ≤ E) (hB : B ≤ E)
    (hAB : ∀ x, x ∈ A → x ∈ B → x = 1) :
    Function.Injective (fun p : ↥A × ↥B => (⟨(p.1 : G) * (p.2 : G),
      E.mul_mem (hA p.1.2) (hB p.2.2)⟩ : ↥E)) := by
  rintro ⟨⟨x, hx⟩, ⟨u, hu⟩⟩ ⟨⟨x', hx'⟩, ⟨u', hu'⟩⟩ he
  have he' : x * u = x' * u' := congrArg Subtype.val he
  have hxx : x'⁻¹ * x = u' * u⁻¹ := by
    calc x'⁻¹ * x = x'⁻¹ * (x * u) * u⁻¹ := by group
      _ = x'⁻¹ * (x' * u') * u⁻¹ := by rw [he']
      _ = u' * u⁻¹ := by group
  have h1 : x'⁻¹ * x ∈ A := A.mul_mem (A.inv_mem hx') hx
  have h2 : x'⁻¹ * x ∈ B := by rw [hxx]; exact B.mul_mem hu' (B.inv_mem hu)
  have h3 : x'⁻¹ * x = 1 := hAB _ h1 h2
  have hxe : x = x' := by
    calc x = x' * (x'⁻¹ * x) := by group
      _ = x' := by rw [h3]; group
  have hue : u = u' := by
    have : u' * u⁻¹ = 1 := by rw [← hxx]; exact h3
    calc u = (u' * u⁻¹)⁻¹ * u' := by group
      _ = u' := by rw [this]; group
  subst hxe
  subst hue
  rfl

theorem card_mul_le_of_inf_bot [Finite G] {A B E : Subgroup G} (hA : A ≤ E) (hB : B ≤ E)
    (hAB : ∀ x, x ∈ A → x ∈ B → x = 1) : Nat.card ↥A * Nat.card ↥B ≤ Nat.card ↥E := by
  have := Nat.card_le_card_of_injective _ (mulMap_injective hA hB hAB)
  rwa [Nat.card_prod] at this

theorem exists_mul_of_card_eq [Finite G] {A B E : Subgroup G} (hA : A ≤ E) (hB : B ≤ E)
    (hAB : ∀ x, x ∈ A → x ∈ B → x = 1) (hc : Nat.card ↥A * Nat.card ↥B = Nat.card ↥E) :
    ∀ y ∈ E, ∃ a ∈ A, ∃ b ∈ B, y = a * b := by
  have hinj := mulMap_injective hA hB hAB
  have hbij : Function.Bijective _ := hinj.bijective_of_nat_card_le (by rw [Nat.card_prod, hc])
  intro y hy
  obtain ⟨⟨a, b⟩, hab⟩ := hbij.2 ⟨y, hy⟩
  exact ⟨a, a.2, b, b.2, (congrArg Subtype.val hab).symm⟩

end CFSG.Quasithin.H13.F431.U42Aut
