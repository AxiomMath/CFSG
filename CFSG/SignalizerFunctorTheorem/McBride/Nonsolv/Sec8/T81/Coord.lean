module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec8.T81.CoordAux

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace T81

variable {G : Type*} [Group G] [Finite G]

theorem eq_sSup_of_refines {M : Subgroup G} {Ω Ω' : Set (Subgroup G)}
    (hΩ : IsDirectProduct Ω M) (hΩ' : IsDirectProduct Ω' M)
    (href : ∀ X ∈ Ω, ∃ Y ∈ Ω', X ≤ Y) {Y : Subgroup G} (hY : Y ∈ Ω') :
    Y = sSup {X | X ∈ Ω ∧ X ≤ Y} := by
  refine le_antisymm ?_ (sSup_le fun X hX => hX.2)
  set Q : Subgroup G := sSup {X | X ∈ Ω ∧ X ≤ Y}
  let f : ↥M →* G := Y.subtype.comp (hΩ'.coord hY)
  have hf : ∀ m : M, f m ∈ Q := by
    refine hom_mem_of_forall_mem hΩ f Q fun X hX x hx => ?_
    obtain ⟨Y', hY', hXY'⟩ := href X hX
    by_cases hYY : Y' = Y
    · subst hYY
      have h1 : f ⟨x, hΩ.le hX hx⟩ = x := hΩ'.coord_of_mem hY' (hXY' hx)
      rw [h1]
      exact le_sSup (show X ∈ {X | X ∈ Ω ∧ X ≤ Y'} from ⟨hX, hXY'⟩) hx
    · have h1 : f ⟨x, hΩ.le hX hx⟩ = 1 := by
        have h2 := hΩ'.coord_of_mem_ne hY hY' hYY (hXY' hx)
        simp only [f, MonoidHom.comp_apply, Subgroup.subtype_apply]
        rw [h2]
        rfl
      rw [h1]
      exact one_mem Q
  intro y hy
  have h1 := hf ⟨y, hΩ'.le hY hy⟩
  have h2 : f ⟨y, hΩ'.le hY hy⟩ = y := hΩ'.coord_of_mem hY hy
  rwa [h2] at h1

theorem projIn_le_iSup_projIn_of_refines {M D : Subgroup G} {Ω Ω' : Set (Subgroup G)}
    (hΩ : IsDirectProduct Ω M) (hΩ' : IsDirectProduct Ω' M)
    (href : ∀ X ∈ Ω, ∃ Y ∈ Ω', X ≤ Y) {Y : Subgroup G} (hY : Y ∈ Ω') :
    projIn Ω' Y D ≤ ⨆ X ∈ Ω, projIn Ω X D := by
  intro y hy
  obtain ⟨d, hdD, hdy⟩ := (hΩ'.mem_projIn_iff hY).mp hy
  let f : ↥M →* G := Y.subtype.comp (hΩ'.coord hY)
  have key : f d ∈ ⨆ X ∈ Ω, projIn Ω X D := by
    refine hom_mem_of_coord_mem hΩ f _ d fun X hX => ?_
    obtain ⟨Y', hY', hXY'⟩ := href X hX
    have hdX : ((hΩ.coord hX d : X) : G) ∈ projIn Ω X D :=
      (hΩ.mem_projIn_iff hX).mpr ⟨d, hdD, rfl⟩
    by_cases hYY : Y' = Y
    · subst hYY
      have h1 : f ⟨(hΩ.coord hX d : G), hΩ.le hX (hΩ.coord hX d).2⟩ = (hΩ.coord hX d : G) :=
        hΩ'.coord_of_mem hY' (hXY' (hΩ.coord hX d).2)
      rw [h1]
      exact Subgroup.mem_iSup_of_mem X (Subgroup.mem_iSup_of_mem hX hdX)
    · have h1 : f ⟨(hΩ.coord hX d : G), hΩ.le hX (hΩ.coord hX d).2⟩ = 1 := by
        have h2 := hΩ'.coord_of_mem_ne hY hY' hYY (hXY' (hΩ.coord hX d).2)
        simp only [f, MonoidHom.comp_apply, Subgroup.subtype_apply]
        rw [h2]
        rfl
      rw [h1]
      exact one_mem _
  have hfd : f d = y := hdy
  rwa [hfd] at key

theorem projIn_le_projIn_of_le {H M D : Subgroup G} {T T' : Set (Subgroup G)}
    (m : Subgroup G → Subgroup G) (hT : IsDirectProduct T H) (hT' : IsDirectProduct T' M)
    (hHM : H ≤ M) (hmT : ∀ K ∈ T, m K ∈ T') (hKm : ∀ K ∈ T, K ≤ m K)
    (hinj : ∀ K ∈ T, ∀ K' ∈ T, m K = m K' → K = K') (_hDH : D ≤ H)
    {L : Subgroup G} (hL : L ∈ T) : projIn T L D ≤ projIn T' (m L) D := by
  intro x hx
  obtain ⟨d, hdD, hdx⟩ := (hT.mem_projIn_iff hL).mp hx
  rw [hT'.mem_projIn_iff (hmT L hL)]
  refine ⟨⟨d, hHM d.2⟩, hdD, ?_⟩
  let f₁ : ↥H →* G := L.subtype.comp (hT.coord hL)
  let f₂ : ↥H →* G :=
    (m L).subtype.comp ((hT'.coord (hmT L hL)).comp (Subgroup.inclusion hHM))
  have hf : f₁ = f₂ := by
    refine hom_ext_of_forall_mem hT f₁ f₂ fun K hK z hz => ?_
    by_cases hKL : K = L
    · subst hKL
      have h1 : f₁ ⟨z, hT.le hK hz⟩ = z := hT.coord_of_mem hK hz
      have h2 : f₂ ⟨z, hT.le hK hz⟩ = z := hT'.coord_of_mem (hmT K hK) (hKm K hK hz)
      rw [h1, h2]
    · have hmne : m K ≠ m L := fun h => hKL (hinj K hK L hL h)
      have h1 : f₁ ⟨z, hT.le hK hz⟩ = 1 := by
        have h3 := hT.coord_of_mem_ne hL hK hKL hz
        simp only [f₁, MonoidHom.comp_apply, Subgroup.subtype_apply]
        rw [h3]
        rfl
      have h2 : f₂ ⟨z, hT.le hK hz⟩ = 1 := by
        have h3 := hT'.coord_of_mem_ne (hmT L hL) (hmT K hK) hmne (hKm K hK hz)
        change (((hT'.coord (hmT L hL)) ⟨z, _⟩ : ↥(m L)) : G) = 1
        rw [h3]
        rfl
      rw [h1, h2]
  have h1 : f₁ d = f₂ d := by rw [hf]
  rw [← hdx]
  exact h1.symm

end T81

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
