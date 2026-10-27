module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.FlagBorel
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.L3YC.L3YCT6Lin

public section

namespace CFSG.Quasithin

open CFSG.Open hiding StatedSL StatedSp
open CFSG.LieType.BorelTits
open CFSG.Assembly.LowTwoRank (StatedSL)

namespace Stellmacher.L3YC

section Core

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem coord_data {L U W : Subgroup G} {F : Type} [Field F] [Fintype F]
    (α : ↥L →* ↥(StatedSL 3 F)) (hnat : IsSumOfNaturalModulesVia L U ⊥ α false 1)
    (hWU : W ≤ U) (hW : Nat.card ↥W = 4) {a : G} (haW : a ∈ W) (ha1 : a ≠ 1) :
    ∃ (B : ↥U ≃* Multiplicative (Fin 3 → F)) (W' : AddSubgroup (Fin 3 → F)) (a' : Fin 3 → F),
      (∀ (l : ↥L) (u v : ↥U), (v : G) = l * u * l⁻¹ →
        Multiplicative.toAdd (B v) =
          ((α l : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec
            (Multiplicative.toAdd (B u))) ∧
      Nat.card W' = 4 ∧ a' ∈ W' ∧ a' ≠ 0 ∧
      (∀ u : ↥U, Multiplicative.toAdd (B u) ∈ W' ↔ (u : G) ∈ W) ∧
      ∀ hau : a ∈ U, Multiplicative.toAdd (B ⟨a, hau⟩) = a' := by
  classical
  obtain ⟨B, hB⟩ := Stellmacher.PU.L3YC.natural_coord α hnat
  let W' : AddSubgroup (Fin 3 → F) :=
    { carrier := {x | ∃ u : ↥U, (u : G) ∈ W ∧ Multiplicative.toAdd (B u) = x}
      zero_mem' := ⟨1, W.one_mem, by simp⟩
      add_mem' := by
        rintro _ _ ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩
        exact ⟨u * v, W.mul_mem hu hv, by simp⟩
      neg_mem' := by
        rintro _ ⟨u, hu, rfl⟩
        exact ⟨u⁻¹, W.inv_mem hu, by simp⟩ }
  have hmemW' : ∀ u : ↥U, Multiplicative.toAdd (B u) ∈ W' ↔ (u : G) ∈ W := by
    intro u
    constructor
    · rintro ⟨v, hv, hvu⟩
      have : v = u := B.injective (Multiplicative.toAdd.injective hvu)
      exact this ▸ hv
    · exact fun h => ⟨u, h, rfl⟩
  have hW'card : Nat.card W' = 4 := by
    rw [← hW]
    refine (Nat.card_congr (Equiv.ofBijective
      (fun x : W => (⟨Multiplicative.toAdd (B ⟨x, hWU x.2⟩), (hmemW' _).mpr x.2⟩ : W')) ⟨?_, ?_⟩)).symm
    · intro x y hxy
      have h1 := congrArg Subtype.val hxy
      have := B.injective (Multiplicative.toAdd.injective h1)
      exact Subtype.ext (Subtype.mk.inj this)
    · rintro ⟨_, ⟨u, hu, rfl⟩⟩
      exact ⟨⟨u, hu⟩, rfl⟩
  let au : ↥U := ⟨a, hWU haW⟩
  have hau0 : Multiplicative.toAdd (B au) ≠ 0 := by
    intro h
    have h1 : B au = 1 := by
      apply Multiplicative.toAdd.injective
      simpa using h
    have h2 : au = 1 := B.injective (by simpa using h1)
    exact ha1 (congrArg Subtype.val h2)
  exact ⟨B, W', Multiplicative.toAdd (B au), hB, hW'card, (hmemW' au).mpr haW, hau0, hmemW', fun _ => rfl⟩

omit [Finite G] in
theorem conj_facts {L U W : Subgroup G} {F : Type} [Field F] [Fintype F]
    (α : ↥L →* ↥(StatedSL 3 F)) (hnat : IsSumOfNaturalModulesVia L U ⊥ α false 1)
    (hWU : W ≤ U) {a : G} (haW : a ∈ W)
    (B : ↥U ≃* Multiplicative (Fin 3 → F)) (W' : AddSubgroup (Fin 3 → F)) (a' : Fin 3 → F)
    (hB : ∀ (l : ↥L) (u v : ↥U), (v : G) = l * u * l⁻¹ →
        Multiplicative.toAdd (B v) =
          ((α l : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec
            (Multiplicative.toAdd (B u)))
    (hmemW' : ∀ u : ↥U, Multiplicative.toAdd (B u) ∈ W' ↔ (u : G) ∈ W)
    (hBa : ∀ hau : a ∈ U, Multiplicative.toAdd (B ⟨a, hau⟩) = a')
    (g : GL (Fin 3) F) (x : ↥L) (hxα : (α x : GL (Fin 3) F) = g) (hga : glAct g a' = a')
    {w' : Fin 3 → F} (hw'W : w' ∈ W') (hgw' : glAct g w' ∉ W') :
    (x : G) * a * (x : G)⁻¹ = a ∧ ∃ w ∈ W, (x : G) * w * (x : G)⁻¹ ∉ W := by
  have hact : ∀ u : ↥U, (x : G) * u * (x : G)⁻¹ ∈ U := fun u => by
    have : (x : G) ∈ Subgroup.normalizer (U : Set G) := hnat.1 x.2
    exact (Subgroup.mem_normalizer_iff.mp this u).mp u.2
  have hcoord : ∀ u : ↥U, Multiplicative.toAdd (B ⟨_, hact u⟩) =
      glAct g (Multiplicative.toAdd (B u)) := by
    intro u
    have := hB x u ⟨_, hact u⟩ rfl
    rw [this, hxα]
  refine ⟨?_, ?_⟩
  · have haU : a ∈ U := hWU haW
    have h1 := hcoord ⟨a, haU⟩
    rw [hBa haU, hga] at h1
    have h2 := B.injective (Multiplicative.toAdd.injective (h1.trans (hBa haU).symm))
    exact congrArg Subtype.val h2
  · obtain ⟨u, hu⟩ := B.surjective (Multiplicative.ofAdd w')
    have hu' : Multiplicative.toAdd (B u) = w' := by rw [hu]; rfl
    have huW : (u : G) ∈ W := (hmemW' u).mp (by rw [hu']; exact hw'W)
    refine ⟨u, huW, fun hmem => hgw' ?_⟩
    rw [← hu', ← hcoord u]
    exact (hmemW' _).mpr hmem

end Core

end Stellmacher.L3YC

end CFSG.Quasithin
