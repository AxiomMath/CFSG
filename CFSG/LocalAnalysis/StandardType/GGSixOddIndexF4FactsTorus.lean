module

public import CFSG.LocalAnalysis.StandardType.GGSixOddIndexF4FactsRank
public import CFSG.LocalAnalysis.ComponentInitial.DerivedFixedLayer

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.LieType.Chevalley CFSG.LieType.Ree

section Transport

variable {U G : Type*} [Group U] [Group G] {ψ : U →* G}

theorem ggF4_map_centralizer_singleton (hψ : Function.Injective ψ) (b : U) :
    (Subgroup.centralizer {b}).map ψ = ψ.range ⊓ Subgroup.centralizer {ψ b} := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨⟨u, rfl⟩, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp hu]
  · rintro ⟨⟨u, rfl⟩, hx⟩
    refine ⟨u, Subgroup.mem_centralizer_singleton_iff.mpr (hψ ?_), rfl⟩
    rw [map_mul, map_mul]
    exact Subgroup.mem_centralizer_singleton_iff.mp hx

theorem ggF4_inf_centralizer_map (hψ : Function.Injective ψ) {B : Subgroup G}
    (hB : B ≤ ψ.range) (L : Subgroup U) :
    B ⊓ Subgroup.centralizer ((L.map ψ : Subgroup G) : Set G) =
      (B.comap ψ ⊓ Subgroup.centralizer (L : Set U)).map ψ := by
  ext x
  constructor
  · rintro ⟨hxB, hxC⟩
    obtain ⟨u, rfl⟩ := hB hxB
    have hxC' : ∀ y ∈ ((L.map ψ : Subgroup G) : Set G), y * ψ u = ψ u * y :=
      Subgroup.mem_centralizer_iff.mp hxC
    refine ⟨u, ⟨hxB, Subgroup.mem_centralizer_iff.mpr fun l hl => hψ ?_⟩, rfl⟩
    rw [map_mul, map_mul]
    exact hxC' (ψ l) ⟨l, hl, rfl⟩
  · rintro ⟨u, ⟨huB, huC⟩, rfl⟩
    have huC' : ∀ l ∈ (L : Set U), l * u = u * l := Subgroup.mem_centralizer_iff.mp huC
    refine ⟨huB, Subgroup.mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨l, hl, rfl⟩
    rw [← map_mul, ← map_mul, huC' l hl]

theorem ggF4_isElemAbelian_comap (hψ : Function.Injective ψ) {p : ℕ} {B : Subgroup G}
    (hB : IsElemAbelian p B) : IsElemAbelian p (B.comap ψ) := by
  refine ⟨⟨⟨fun a b => Subtype.ext (hψ ?_)⟩⟩, fun x hx => hψ ?_⟩
  · change ψ ((a : U) * b) = ψ ((b : U) * a)
    rw [map_mul, map_mul]
    exact congrArg Subtype.val (hB.1.is_comm.comm ⟨ψ a, a.2⟩ ⟨ψ b, b.2⟩)
  · rw [map_pow, hB.2 _ hx, map_one]

end Transport

end CFSG.StandardType
