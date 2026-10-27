module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.A3ComponentsBasic
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRk2ExclNB

public section

namespace CFSG.Quasithin.Rk2

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement

set_option linter.unusedSectionVars false

section Up

variable {G : Type} [Group G] (L : Subgroup G)

@[expose] def up (X : Subgroup ↥L) : Subgroup G := X.map L.subtype

variable {L}

theorem up_le (X : Subgroup ↥L) : up L X ≤ L := Subgroup.map_subtype_le X

theorem mem_up {X : Subgroup ↥L} {x : G} : x ∈ up L X ↔ ∃ h : x ∈ L, (⟨x, h⟩ : ↥L) ∈ X := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨h, hx⟩
    exact ⟨⟨x, h⟩, hx, rfl⟩

theorem up_mono {X Y : Subgroup ↥L} (h : X ≤ Y) : up L X ≤ up L Y := Subgroup.map_mono h

theorem up_le_up_iff {X Y : Subgroup ↥L} : up L X ≤ up L Y ↔ X ≤ Y :=
  Subgroup.map_le_map_iff_of_injective L.subtype_injective

theorem up_injective : Function.Injective (up L) := Subgroup.map_injective L.subtype_injective

theorem up_commutator (X Y : Subgroup ↥L) : ⁅up L X, up L Y⁆ = up L ⁅X, Y⁆ :=
  (Subgroup.map_commutator X Y L.subtype).symm

theorem up_top : up L (⊤ : Subgroup ↥L) = L := by
  rw [up, Subgroup.map_top, Subgroup.range_subtype]

theorem up_sup (X Y : Subgroup ↥L) : up L (X ⊔ Y) = up L X ⊔ up L Y := Subgroup.map_sup _ _ _

theorem perfectCore_up [Finite G] (X : Subgroup ↥L) :
    perfectCore (up L X) = up L (perfectCore X) :=
  (map_perfectCore L.subtype X).symm

end Up

section PCore

variable {Γ G : Type} [Group Γ] [Group G]

theorem pCoreOf_map_of_injective (f : Γ →* G) (hf : Function.Injective f) (X : Subgroup Γ) :
    pCoreOf 2 (X.map f) = (pCoreOf 2 X).map f := by
  let e : ↥X ≃* ↥(X.map f) := X.equivMapOfInjective f hf
  have h1 := CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 e
  have h2 : (X.map f).subtype.comp e.toMonoidHom = f.comp X.subtype := by
    ext x
    rfl
  unfold pCoreOf
  rw [← h1, Subgroup.map_map, h2, ← Subgroup.map_map]

end PCore

section Irred

variable {Γ G : Type} [Group Γ] [Group G]

theorem BlockIrred.of_map (f : Γ →* G) (hf : Function.Injective f) {X : Subgroup Γ}
    (h : BlockIrred (X.map f)) : BlockIrred X := by
  have hU : blockU (X.map f) = (blockU X).map f := by
    unfold blockU blockQ
    rw [pCoreOf_map_of_injective f hf, Subgroup.map_commutator]
  have hZ : blockZ (X.map f) = (blockZ X).map f := by
    unfold blockZ
    rw [hU]
    ext g
    constructor
    · rintro ⟨⟨u, hu, rfl⟩, hc⟩
      refine ⟨u, ⟨hu, ?_⟩, rfl⟩
      have hc' : f u ∈ Subgroup.centralizer ((X.map f : Subgroup G) : Set G) := hc
      refine Subgroup.mem_centralizer_iff.2 fun x hx => hf ?_
      have := Subgroup.mem_centralizer_iff.1 hc' (f x) ⟨x, hx, rfl⟩
      rw [map_mul, map_mul]
      exact this
    · rintro ⟨u, ⟨hu, hc⟩, rfl⟩
      refine ⟨⟨u, hu, rfl⟩, ?_⟩
      have hc' : u ∈ Subgroup.centralizer (X : Set Γ) := hc
      refine Subgroup.mem_centralizer_iff.2 ?_
      rintro _ ⟨x, hx, rfl⟩
      have := Subgroup.mem_centralizer_iff.1 hc' x hx
      rw [← map_mul, ← map_mul, this]
  obtain ⟨hlt, hirr⟩ := h
  rw [hU, hZ] at hlt hirr
  refine ⟨(Subgroup.map_lt_map_iff_of_injective hf).1 hlt, fun W hZW hWU hn => ?_⟩
  have h2 := hirr (W.map f) (Subgroup.map_mono hZW) (Subgroup.map_mono hWU)
    ((Subgroup.map_mono hn).trans (Subgroup.le_normalizer_map f))
  rcases h2 with h2 | h2
  · exact Or.inl (Subgroup.map_injective hf h2)
  · exact Or.inr (Subgroup.map_injective hf h2)

end Irred

end CFSG.Quasithin.Rk2
