module

public import CFSG.LocalAnalysis.WeakClosure81.TwelveMinimal
public import CFSG.LocalAnalysis.WeakClosure81.TwelveTwoD

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Open Subgroup

section TwoE

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {n m : ℕ}

theorem regularOnNonzero_map_comp {H : Type} [Group H] (φ : H →* G) (ρ : G →* LGL 2 V)
    (T : Subgroup H) (Z : Submodule (ZMod 2) V) (h : RegularOnNonzero (ρ.comp φ) T Z) :
    RegularOnNonzero ρ (T.map φ) Z := by
  refine ⟨?_, ?_⟩
  · intro x hx hx1 z hz hfix
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    have hy1 : y ≠ 1 := fun h1 => hx1 (by rw [h1, map_one])
    exact h.1 y hy hy1 z hz hfix
  · intro z hz hz0 z' hz' hz'0
    obtain ⟨y, hy, hyz⟩ := h.2 z hz hz0 z' hz' hz'0
    exact ⟨φ y, Subgroup.mem_map_of_mem φ hy, hyz⟩

theorem twelveTwo_two_general
    {ρ : G →* LGL 2 V} {B A : Subgroup G}
    {Z : Submodule (ZMod 2) V} (h : Setting12One ρ B Z A n m) {L : Subgroup G}
    (hL : IsMinimalNotLE B A L) (hZ : Module.finrank (ZMod 2) Z ≤ m) :
    (m = n ∨ (2 ≤ m ∧ m ∣ n ∧ m < n)) ∧ Module.finrank (ZMod 2) Z = m ∧
      (∀ x ∈ B ⊓ L, Odd (orderOf x) → x ≠ 1 → ∀ z ∈ Z, ρ x z = z → z = 0) ∧
      ∃ (t : G) (T : Subgroup G), t ∈ L ∧ t * t = 1 ∧ t ∉ B ∧ T ≤ B ⊓ L ∧ IsCyclic T ∧
        Nat.card T = 2 ^ m - 1 ∧ (∀ x ∈ T, t * x * t = x⁻¹) ∧ RegularOnNonzero ρ T Z ∧
        commSpace (T.map ρ) Z = Z := by
  haveI : Finite G := rankOne_finite h.type
  obtain ⟨k, hk, hSL, hminL⟩ := Setting12One.exists_restrict_of_minimal h hL
  obtain ⟨hkm, hZk, hodd, tL, TL, htL2, htLB, hTLB, hTLcyc, hTLcard, hTLinv, hTLreg, hTLcomm⟩ :=
    twelveTwo_two_spec hSL hminL hZ
  refine ⟨by rw [← hkm]; exact hk, hZk, ?_, (tL : G), TL.map L.subtype, tL.2, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · intro x hx hodd' hx1 z hz hfix
    have hxL : x ∈ L := hx.2
    refine hodd ⟨x, hxL⟩ (Subgroup.mem_subgroupOf.mpr hx.1) ?_ ?_ z hz hfix
    · rwa [Subgroup.orderOf_mk]
    · exact fun h1 => hx1 (congrArg Subtype.val h1)
  · simpa using congrArg Subtype.val htL2
  · exact fun hB => htLB (Subgroup.mem_subgroupOf.mpr hB)
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    exact ⟨Subgroup.mem_subgroupOf.mp (hTLB hy), y.2⟩
  · haveI := hTLcyc
    let e := Subgroup.equivMapOfInjective TL L.subtype (Subgroup.subtype_injective L)
    exact isCyclic_of_surjective e.toMonoidHom e.surjective
  · rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective L), hTLcard, hkm]
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    have := hTLinv y hy
    simpa using congrArg Subtype.val this
  · exact regularOnNonzero_map_comp L.subtype ρ TL Z hTLreg
  · have hmap : (TL.map L.subtype).map ρ = TL.map (ρ.comp L.subtype) := Subgroup.map_map ..
    rw [hmap]
    exact hTLcomm

end TwoE

end CFSG.LocalAnalysis.WeakClosure81
