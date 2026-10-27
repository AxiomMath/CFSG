module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineNA6Gen

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Coord

open CFSG.Quasithin CFSG.Open Subgroup

variable {Y : Type} [Group Y] {X : Type} [Group X]

structure ModelBase (G L₀ T₀ : Subgroup Y) : Prop where
  T₀_le : T₀ ≤ G
  L₀_le : L₀ ≤ G
  sylow : IsSylowIn 2 T₀ G
  three_dvd : 3 ∣ Nat.card L₀
  le_of_normal : ∀ K : Subgroup Y, K ≤ G → (∀ g ∈ G, ∀ x ∈ K, g * x * g⁻¹ ∈ K) → K ≠ ⊥ →
    L₀ ≤ K
  cent : ∀ g ∈ G, (∀ x ∈ L₀, g * x = x * g) → g = 1
  comm : ∀ x ∈ G, ∀ y ∈ G, x * y * x⁻¹ * y⁻¹ ∈ L₀

theorem modelBase_of_modelFacts {G L₀ T₀ : Subgroup Y} (hM : NFA6.ModelFacts G L₀ T₀) :
    ModelBase G L₀ T₀ :=
  ⟨hM.T₀_le, hM.L₀_le, hM.sylow, hM.three_dvd, hM.le_of_normal, hM.cent,
    fun _ hx _ hy => hM.commutator_mem hx hy⟩

private theorem exists_embedding_of_sylow [Finite Y] {G L₀ T₀ : Subgroup Y}
    (hM : ModelBase G L₀ T₀) [Finite X] (e : X ≃* G) {D : Subgroup X}
    (hD : IsSylowIn 2 D ⊤) :
    ∃ ι : X →* Y, Function.Injective ι ∧ ι.range = G ∧ D.map ι = T₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ι₀ : X →* Y := G.subtype.comp e.toMonoidHom with hι₀def
  have hι₀ : Function.Injective ι₀ := G.subtype_injective.comp e.injective
  have hr₀ : ι₀.range = G := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact (e x).2
    · intro hy
      exact ⟨e.symm ⟨y, hy⟩, by simp [ι₀]⟩
  have hT₀' : IsSylowIn 2 (T₀.comap ι₀) ⊤ := by
    refine isSylowIn_of_card_eq le_top ?_
    have h1 : Nat.card (T₀.comap ι₀) = Nat.card T₀ := by
      rw [← card_map_of_injective hι₀, map_comap_eq_self (hr₀ ▸ hM.T₀_le)]
    have h2 : Nat.card (⊤ : Subgroup X) = Nat.card G := by
      rw [card_top]
      exact Nat.card_congr e.toEquiv
    rw [h1, h2]
    exact hM.sylow.card_eq
  obtain ⟨g, hg⟩ := NFA6.exists_eq_map_conj hD hT₀'
  set ι : X →* Y := ι₀.comp (MulAut.conj g⁻¹).toMonoidHom with hιdef
  have hι : Function.Injective ι := hι₀.comp (MulAut.conj g⁻¹).injective
  have hr : ι.range = G := by
    rw [← hr₀]
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨g * x * g⁻¹, by simp [ι, mul_assoc]⟩
  have hT : D.map ι = T₀ := by
    rw [hg, hιdef, ← map_map, map_map (f := (MulAut.conj g).toMonoidHom)]
    have hid : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
        MonoidHom.id X := by
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    rw [hid, map_id, map_comap_eq_self (hr₀ ▸ hM.T₀_le)]
  exact ⟨ι, hι, hr, hT⟩

theorem exists_embedding [Finite Y] {G L₀ T₀ : Subgroup Y} (hM : ModelBase G L₀ T₀)
    [Finite X] (e : X ≃* G) {L D : Subgroup X} (hLn : L.Normal) (hL1 : L ≠ ⊥) (hLp : ⁅L, L⁆ = L)
    (hD : IsSylowIn 2 D ⊤) :
    ∃ ι : X →* Y, Function.Injective ι ∧ ι.range = G ∧ L.map ι = L₀ ∧ D.map ι = T₀ := by
  obtain ⟨ι, hι, hr, hT⟩ := exists_embedding_of_sylow hM e hD
  refine ⟨ι, hι, hr, ?_, hT⟩
  have hmapG : L.map ι ≤ G := hr ▸ map_le_range ι L
  refine le_antisymm ?_ (hM.le_of_normal _ hmapG ?_ ?_)
  · rw [← hLp, map_commutator, commutator_le]
    intro x hx y hy
    rw [commutatorElement_def]
    exact hM.comm _ (hmapG hx) _ (hmapG hy)
  · intro g' hg' y hy
    rw [← hr] at hg'
    obtain ⟨h, rfl⟩ := hg'
    obtain ⟨l, hl, rfl⟩ := hy
    exact ⟨h * l * h⁻¹, hLn.conj_mem l hl h, by simp⟩
  · rwa [Ne, map_eq_bot_iff_of_injective _ hι]

end CFSG.LocalAnalysis.WeakClosure81.Coord
