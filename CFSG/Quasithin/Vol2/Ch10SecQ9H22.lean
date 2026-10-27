module

public import CFSG.Quasithin.Vol2.Ch10SecQ9H21
public import CFSG.Quasithin.Vol2.Ch10SecQ9H20

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F

open Matrix

variable {m k : ℕ}

theorem perfect_subgroupOf {G : Type*} [Group G] {X K : Subgroup G} (hXK : X ≤ K)
    (hperf : ⁅X, X⁆ = X) : ⁅X.subgroupOf K, X.subgroupOf K⁆ = X.subgroupOf K := by
  apply Subgroup.map_injective K.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_of_le_left hXK, hperf]

theorem topH_eq_one_of_perfect {X : Subgroup (Matrix.SpecialLinearGroup (Fin (2 + k)) (ZMod 2))}
    (hX : X ≤ stabStd 2 k) (hperf : ⁅X, X⁆ = X) (x : ↥(stabStd 2 k)) (hx : x.1 ∈ X) :
    topH 2 k x = 1 := by
  have h := eq_bot_of_perfect_SL2 (H := (X.subgroupOf (stabStd 2 k)).map (topH 2 k))
    (by rw [← Subgroup.map_commutator, perfect_subgroupOf hX hperf])
  have hmem : topH 2 k x ∈ (X.subgroupOf (stabStd 2 k)).map (topH 2 k) :=
    ⟨x, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  rw [h, Subgroup.mem_bot] at hmem
  exact hmem

theorem botH_eq_one_of_perfect {X : Subgroup (Matrix.SpecialLinearGroup (Fin (m + 2)) (ZMod 2))}
    (hX : X ≤ stabStd m 2) (hperf : ⁅X, X⁆ = X) (x : ↥(stabStd m 2)) (hx : x.1 ∈ X) :
    botH m 2 x = 1 := by
  have h := eq_bot_of_perfect_SL2 (H := (X.subgroupOf (stabStd m 2)).map (botH m 2))
    (by rw [← Subgroup.map_commutator, perfect_subgroupOf hX hperf])
  have hmem : botH m 2 x ∈ (X.subgroupOf (stabStd m 2)).map (botH m 2) :=
    ⟨x, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  rw [h, Subgroup.mem_bot] at hmem
  exact hmem

theorem le_o2G' {G : Type*} [Group G] (X : Subgroup G) {N : Subgroup G} (hNX : N ≤ X)
    (hN : ∀ y ∈ X, ∀ z ∈ N, y * z * y⁻¹ ∈ N) (hp : IsPGroup 2 N) : N ≤ o2G X := by
  refine le_o2G X hNX (fun y hy => ?_) hp
  rw [Subgroup.mem_normalizer_iff]
  intro z
  refine ⟨hN y hy z, fun h => ?_⟩
  have := hN y⁻¹ (X.inv_mem hy) _ h
  rwa [show y⁻¹ * (y * z * y⁻¹) * y⁻¹⁻¹ = z by group] at this

@[expose] def kerIn (X : Subgroup (Matrix.SpecialLinearGroup (Fin (m + k)) (ZMod 2)))
    (hX : X ≤ stabStd m k) {H : Type*} [Group H] (f : ↥(stabStd m k) →* H) :
    Subgroup (Matrix.SpecialLinearGroup (Fin (m + k)) (ZMod 2)) where
  carrier := {z | ∃ h : z ∈ X, f ⟨z, hX h⟩ = 1}
  one_mem' := ⟨X.one_mem, map_one f⟩
  mul_mem' := fun {a b} ⟨ha, ha'⟩ ⟨hb, hb'⟩ => ⟨X.mul_mem ha hb, by
    rw [show (⟨a * b, hX (X.mul_mem ha hb)⟩ : ↥(stabStd m k)) = ⟨a, hX ha⟩ * ⟨b, hX hb⟩ from rfl,
      map_mul, ha', hb', one_mul]⟩
  inv_mem' := fun {a} ⟨ha, ha'⟩ => ⟨X.inv_mem ha, by
    rw [show (⟨a⁻¹, hX (X.inv_mem ha)⟩ : ↥(stabStd m k)) = (⟨a, hX ha⟩)⁻¹ from rfl, map_inv,
      ha', inv_one]⟩

theorem card_map_ge {X : Subgroup (Matrix.SpecialLinearGroup (Fin (m + k)) (ZMod 2))}
    (hX : X ≤ stabStd m k) {H : Type*} [Group H] (f : ↥(stabStd m k) →* H)
    (hf : ∀ x : ↥(stabStd m k), x.1 ∈ X → f x = 1 → x.1 * x.1 = 1)
    (hcard : Nat.card X = Nat.card (o2G X) * 168) :
    168 ≤ Nat.card ((X.subgroupOf (stabStd m k)).map f) := by
  have hKO : kerIn X hX f ≤ o2G X := by
    refine le_o2G' X (fun z hz => hz.1) (fun y hy z hz => ⟨X.mul_mem (X.mul_mem hy hz.1)
      (X.inv_mem hy), ?_⟩) (fun z => ⟨1, Subtype.ext ?_⟩)
    · obtain ⟨hzX, hz1⟩ := hz
      rw [show (⟨y * z * y⁻¹, hX (X.mul_mem (X.mul_mem hy hzX) (X.inv_mem hy))⟩ :
        ↥(stabStd m k)) = ⟨y, hX hy⟩ * ⟨z, hX hzX⟩ * (⟨y, hX hy⟩)⁻¹ from rfl,
        map_mul, map_mul, hz1, mul_one, map_inv, mul_inv_cancel]
    · obtain ⟨hzX, hz1⟩ := z.2
      rw [pow_one, pow_two, Subgroup.coe_mul, Subgroup.coe_one]
      exact hf ⟨z.1, hX hzX⟩ hzX hz1
  have h1 := card_eq_ker_mul_range (f.comp (X.subgroupOf (stabStd m k)).subtype)
  have h2 : Nat.card (f.comp (X.subgroupOf (stabStd m k)).subtype).ker ≤ Nat.card (o2G X) := by
    refine le_trans (Nat.card_le_card_of_injective
      (fun x : ↥(f.comp (X.subgroupOf (stabStd m k)).subtype).ker =>
        (⟨x.1.1.1, Subgroup.mem_subgroupOf.mp x.1.2, x.2⟩ : ↥(kerIn X hX f))) ?_) ?_
    · intro a b h
      have h' := congrArg Subtype.val h
      exact Subtype.ext (Subtype.ext (Subtype.ext h'))
    · exact Subgroup.card_le_of_le hKO
  have h3 : Nat.card (X.subgroupOf (stabStd m k)) = Nat.card X :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX).toEquiv
  have h4 : (f.comp (X.subgroupOf (stabStd m k)).subtype).range =
      (X.subgroupOf (stabStd m k)).map f := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [h3, hcard, h4] at h1
  have hpos : 0 < Nat.card (o2G X) := Nat.card_pos
  by_contra hlt
  have hlt' : Nat.card ((X.subgroupOf (stabStd m k)).map f) < 168 := by omega
  have := Nat.mul_le_mul h2 (le_of_lt hlt')
  nlinarith

end CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F
