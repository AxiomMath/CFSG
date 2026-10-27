module

public import CFSG.LocalAnalysis.StandardType.GGTBJE6TwoBase
public import CFSG.LocalAnalysis.StandardType.GGLieCoreSmallUnitary
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSU
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTame.Order216

public section

namespace CFSG.StandardType.E6Two

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.RankThree.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.HardMathSupport.Timmesfeld.CrossChar

open Matrix
open scoped MatrixGroups commutatorElement


private theorem a2Solv_frameRoots_eq_a2Roots_of_apply
    {τ : Tag} {σ : Fin 3 → Fin 3 → Fin τ.rank → ℤ}
    {α β : Fin τ.rank → ℤ} (hadd : ∀ i j k, σ i j + σ j k = σ i k)
    (hneg : ∀ i j, σ j i = -σ i j) (h01 : σ 0 1 = α) (h12 : σ 1 2 = β) :
    frameRoots σ = a2Roots α β := by
  have e02 : σ 0 2 = σ 0 1 + σ 1 2 := (hadd 0 1 2).symm
  have e10 : σ 1 0 = -σ 0 1 := hneg 0 1
  have e21 : σ 2 1 = -σ 1 2 := hneg 1 2
  have e20 : σ 2 0 = -σ 0 2 := hneg 0 2
  ext r
  simp only [frameRoots, a2Roots, Set.mem_setOf_eq, Set.mem_insert_iff,
    Set.mem_singleton_iff]
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

private theorem a2Solv_exists_a2Frame
    {L : Type} [Field L] {α β : Fin Tag.E6.rank → ℤ} (h : IsA2Pair α β) :
    ∃ (ψ : SL(3, L) →* ModGL Tag.E6 L) (σ : Fin 3 → Fin 3 → Fin Tag.E6.rank → ℤ),
      CFSG.RankThree.PartOne.KF4.IsA2Frame ψ σ ∧ σ 0 1 = α ∧ σ 1 2 = β ∧
        frameRoots σ = a2Roots α β := by
  obtain ⟨v, h0, h2⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_weyl_a2Pair_E6 h
  have hfr := (CFSG.HardMathSupport.Timmesfeld.CrossChar.e6_base_frame (L := L)).transport v
  let σ : Fin 3 → Fin 3 → Fin Tag.E6.rank → ℤ := fun i j =>
    v • CFSG.RankThree.E6.chainRoot CFSG.RankThree.E6.chain13 i j
  have h01 : σ 0 1 = α := by
    change v • CFSG.RankThree.E6.chainRoot CFSG.RankThree.E6.chain13 0 1 = α
    rw [CFSG.HardMathSupport.Timmesfeld.CrossChar.e6_base_01, h0]
  have h12 : σ 1 2 = β := by
    change v • CFSG.RankThree.E6.chainRoot CFSG.RankThree.E6.chain13 1 2 = β
    rw [CFSG.HardMathSupport.Timmesfeld.CrossChar.e6_base_12, h2]
  have hroots : frameRoots σ = a2Roots α β :=
    a2Solv_frameRoots_eq_a2Roots_of_apply hfr.add hfr.neg h01 h12
  exact ⟨_, σ, hfr, h01, h12, hroots⟩

theorem isSolvable_rationalComponent_of_a2
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ} (S : LangSetup Tag.E6 L p₀)
    (hq : S.D.q = 2) {a : Fin Tag.E6.rank → Lˣ} (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a)) {α β : Fin Tag.E6.rank → ℤ}
    (hαβ : IsA2Pair (τ := Tag.E6) α β)
    (hΨ : componentRoots (rootCharHom a) i = a2Roots α β)
    (hρ : ∀ γ ∈ a2Roots α β, S.ρ γ = -γ) :
    Group.IsSolvable ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  classical
  obtain ⟨ψ, σ, hψA2, -, -, hroots⟩ := a2Solv_exists_a2Frame (L := L) hαβ
  have hψSL : IsSLFrame ψ σ := IsSLFrame.of_isA2Frame hψA2
  have hΨ' : componentRoots (rootCharHom a) i = frameRoots σ := hΨ.trans hroots.symm
  have hfin : (a2Roots α β).Finite := by
    rw [show a2Roots α β = ↑({α, -α, β, -β, α + β, -(α + β)} :
      Finset (Fin Tag.E6.rank → ℤ)) by
      ext x
      simp [a2Roots]]
    exact Finset.finite_toSet _
  have hstab : ∀ γ ∈ a2Roots α β, S.ρ γ ∈ a2Roots α β := by
    intro γ hγ
    rw [hρ γ hγ]
    simp only [a2Roots, Set.mem_insert_iff, Set.mem_singleton_iff] at hγ ⊢
    rcases hγ with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  have hs1 : componentOrbitLength S.ρ (a2Roots α β) = 1 :=
    componentOrbitLength_eq_one hfin hstab
  have hs1' : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1 := by
    rw [hΨ]; exact hs1
  have hπ : ∀ x y : Fin 3, x ≠ y →
      (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)] (σ x y) = σ y x := by
    intro x y hxy
    rw [hs1', Function.iterate_one]
    have hmem : σ x y ∈ a2Roots α β := by
      rw [← hroots]; exact ⟨x, y, hxy, rfl⟩
    rw [hρ (σ x y) hmem]
    exact (hψSL.neg x y).symm
  have hRU := rationalComponent_of_unitary_frame_T S hT i (le_refl 3) hψSL hΨ'
    (1 : Equiv.Perm (Fin 3)) hπ
  exact CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.isSolvable_of_card_dvd_216
    (hRU.2 (by rw [hs1', pow_one, hq]))

end CFSG.StandardType.E6Two

end
