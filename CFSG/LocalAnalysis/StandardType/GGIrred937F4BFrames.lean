module

public import CFSG.LocalAnalysis.StandardType.GGIrred937F4Base
public import CFSG.LocalAnalysis.StandardType.GGIrred937F4BDescent
public import CFSG.LocalAnalysis.StandardType.GGIrred937F4BSplit
public import CFSG.HardMathSupport.Timmesfeld.Torality.F4Block
public import CFSG.RankThree.PartOne.KF4.A2Frame

public section

namespace CFSG.StandardType

namespace Irred937

open CFSG CFSG.Open CFSG.StandardType CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KF4

open scoped MatrixGroups

theorem f4_exists_a2Frame
    {α β : Fin Tag.F4.rank → ℤ} (h : IsA2Pair α β) (L : Type) [Field L] :
    ∃ (ρ : SL(3, L) →* ModGL Tag.F4 L) (σ : Fin 3 → Fin 3 → Fin Tag.F4.rank → ℤ),
      IsA2Frame ρ σ ∧ σ 0 1 = α ∧ σ 1 2 = β ∧
      {r | ∃ i j : Fin 3, i ≠ j ∧ r = σ i j} = a2Roots α β := by
  have key : ∀ (ρ : SL(3, L) →* ModGL Tag.F4 L) (σ : Fin 3 → Fin 3 → Fin Tag.F4.rank → ℤ),
      IsA2Frame ρ σ → σ 0 1 = α → σ 1 2 = β →
      {r | ∃ i j : Fin 3, i ≠ j ∧ r = σ i j} = a2Roots α β := by
    intro ρ σ hfr h01 h12
    have e02 : σ 0 2 = σ 0 1 + σ 1 2 := (hfr.add 0 1 2).symm
    have e10 : σ 1 0 = -σ 0 1 := hfr.neg 0 1
    have e21 : σ 2 1 = -σ 1 2 := hfr.neg 1 2
    have e20 : σ 2 0 = -σ 0 2 := hfr.neg 0 2
    ext r
    simp only [a2Roots, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨i, j, hij, rfl⟩
      fin_cases i <;> fin_cases j <;>
        first | exact absurd rfl hij | simp [e02, e10, e21, e20, h01, h12]
    · rintro (rfl | rfl | rfl | rfl | rfl | rfl)
      · exact ⟨0, 1, by decide, h01.symm⟩
      · exact ⟨1, 0, by decide, by rw [e10, h01]⟩
      · exact ⟨1, 2, by decide, h12.symm⟩
      · exact ⟨2, 1, by decide, by rw [e21, h12]⟩
      · exact ⟨0, 2, by decide, by rw [e02, h01, h12]⟩
      · exact ⟨2, 0, by decide, by rw [e20, e02, h01, h12]⟩
  obtain ⟨v, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := f4_a2Pair_orbit h
  · have hfr := (f4Long_frame (L := L)).transport v
    have e1 : v • CFSG.RankThree.E6.chainRoot f4chainLong 0 1 = α := by
      rw [(f4chainLong_values).1]; exact h1
    have e2 : v • CFSG.RankThree.E6.chainRoot f4chainLong 1 2 = β := by
      rw [(f4chainLong_values).2.1]; exact h2
    exact ⟨_, _, hfr, e1, e2, key _ _ hfr e1 e2⟩
  · have hfr := (f4Short_frame (L := L)).transport v
    have e1 : v • f4ShortSigma 0 1 = α := by rw [(f4ShortSigma_values).2.2.1]; exact h1
    have e2 : v • f4ShortSigma 1 2 = β := by rw [(f4ShortSigma_values).2.2.2]; exact h2
    exact ⟨_, _, hfr, e1, e2, key _ _ hfr e1 e2⟩

theorem a2Frame_w₀_compat
    {τ : Tag} {L : Type} [Field L] {ρ : SL(3, L) →* ModGL τ L}
    {σ : Fin 3 → Fin 3 → Fin τ.rank → ℤ} (h : IsA2Frame ρ σ) (w₀ : WeylGroup τ)
    (hw₀ : ∀ v : Fin τ.rank → ℤ, w₀ • v = -v) :
    ∀ i j : Fin 3, i ≠ j →
      weylQuotientHom τ L ⟨canonicalRep (coxeterSystem τ) L w₀,
          canonicalRep_mem_monomialSubgroup L w₀⟩ • σ i j =
        σ ((Equiv.refl (Fin 3)) j) ((Equiv.refl (Fin 3)) i):= by
  intro i j hij
  have hπ : weylQuotientHom τ L ⟨canonicalRep (coxeterSystem τ) L w₀,
      canonicalRep_mem_monomialSubgroup L w₀⟩ = w₀ :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep w₀)
  show _ = σ j i
  rw [hπ, hw₀, h.neg i j]

end Irred937

end CFSG.StandardType

end
