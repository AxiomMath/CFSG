module

public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic

public section

namespace CFSG.Quasithin.H23P4

open CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

theorem mem_of_mem_normalizer_isParabolic2 {L P : Subgroup G} (hP : IsParabolic2 L P) {g : G}
    (hgL : g ∈ L) (hg : g ∈ Subgroup.normalizer (P : Set G)) : g ∈ P := by
  obtain ⟨hPL, S, hS, hN⟩ := hP
  have hSP : S ≤ P := fun s hs => hN ⟨hS.le hs, Subgroup.le_normalizer hs⟩
  have hSylP : IsSylowTwoOf S P := by
    refine isSylowTwoOf_of_card_eq hSP hS.isPGroup (le_antisymm ?_ ?_)
    · exact card_le_twoPart hSP hS.isPGroup
    · rw [hS.card_eq]
      exact twoPart_mono hPL
  set S' : Subgroup G := S.map (MulAut.conj g).toMonoidHom with hS'
  have hS'P : S' ≤ P := by
    rintro _ ⟨s, hs, rfl⟩
    have := (Subgroup.mem_normalizer_iff.mp hg s).mp (hSP hs)
    simpa [MulAut.conj_apply] using this
  have hS'2 : IsPGroup 2 S' := hS.isPGroup.map _
  have hcard : Nat.card S' = Nat.card S :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hSylP' : IsSylowTwoOf S' P :=
    isSylowTwoOf_of_card_eq hS'P hS'2 (by rw [hcard]; exact hSylP.card_eq)
  obtain ⟨h, hhP, hh⟩ := hSylP.exists_conj hSylP'
  have hk : h⁻¹ * g ∈ Subgroup.normalizer (S : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have : g * x * g⁻¹ ∈ S' := ⟨x, hx, by simp [MulAut.conj_apply]⟩
      rw [hh] at this
      obtain ⟨s, hs, hsx⟩ := this
      have hsx' : h * s * h⁻¹ = g * x * g⁻¹ := by simpa [MulAut.conj_apply] using hsx
      have : h⁻¹ * g * x * (h⁻¹ * g)⁻¹ = s := by
        have e : s = h⁻¹ * (g * x * g⁻¹) * h := by rw [← hsx']; group
        rw [e]; group
      rw [this]
      exact hs
    · intro hx
      have hmem : g * x * g⁻¹ ∈ S.map (MulAut.conj h).toMonoidHom :=
        ⟨h⁻¹ * g * x * (h⁻¹ * g)⁻¹, hx, by simp [MulAut.conj_apply]; group⟩
      rw [← hh] at hmem
      obtain ⟨x', hx', hx'x⟩ := hmem
      have : x' = x := by
        have := congrArg (fun y => g⁻¹ * y * g) hx'x
        simpa [MulAut.conj_apply] using this
      rw [← this]
      exact hx'
  have hkL : h⁻¹ * g ∈ L := L.mul_mem (L.inv_mem (hPL hhP)) hgL
  have hkP : h⁻¹ * g ∈ P := hN ⟨hkL, hk⟩
  have : g = h * (h⁻¹ * g) := by group
  rw [this]
  exact P.mul_mem hhP hkP

end CFSG.Quasithin.H23P4
