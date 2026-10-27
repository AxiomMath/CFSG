module

public import CFSG.LocalAnalysis.StandardType.FS81.N7MainRecOut
public import CFSG.LocalAnalysis.StandardType.FS81.N7MainNF

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly
open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace Basis3

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def autMat (B : Basis3 G 8) :
    ↥(ggAutomizer ⊤ B.span) →* Matrix (Fin 8) (Fin 8) (ZMod 3) :=
  B.matHom.comp (ggAutomizer ⊤ B.span).subtype

theorem autMat_injective (B : Basis3 G 8) : Function.Injective B.autMat :=
  fun _ _ h => Subtype.ext (B.matOf_injective h)

theorem autMat_mem_evenAll0 (B : Basis3 G 8) {b₀ : G} (hb0 : B.b 0 = b₀)
    (hN0 : B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) = evenAll0 7)
    (x : ↥(ggAutomizer ⊤ B.span)) {c : ZMod 3} (hc : B.autMat x *ᵥ nmE0 = c • nmE0) :
    B.autMat x ∈ evenAll0 7 := by
  obtain ⟨g, -, hgN, hg⟩ := mem_ggAutomizer_iff.mp x.2
  have himg := B.conj_b_of_mulVec_single hg (i := 0) (c := c) hc
  rw [hb0] at himg
  have hgb : g ∈ Subgroup.normalizer (Subgroup.zpowers b₀ : Set G) := by
    refine mem_normalizer_zpowers_of_conj ?_
    rw [himg]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers b₀) _
  rw [← hN0]
  exact (B.mem_realized_iff _ _).mpr ⟨x.1, ⟨g, hgb, hgN, hg⟩, rfl⟩

@[expose] noncomputable def n7MSetup (B : Basis3 G 8) {b₀ : G} (hb0 : B.b 0 = b₀)
    (hN0 : B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) = evenAll0 7)
    (hodd : OddCoreTrivial B.span)
    (hcard : 2 ^ 8 * Nat.factorial 8 < Nat.card ↥(ggAutomizer ⊤ B.span)) :
    N7MSetup ↥(ggAutomizer ⊤ B.span) where
  ρ := B.autMat
  ρ_inj := B.autMat_injective
  surj_H1 A hA := by
    rw [← hN0] at hA
    obtain ⟨φ, ⟨g, -, hgN, hg⟩, hφA⟩ := (B.mem_realized_iff _ _).mp hA
    exact ⟨⟨φ, mem_ggAutomizer_iff.mpr ⟨g, trivial, hgN, hg⟩⟩, hφA⟩
  norm_iff x := by
    refine ⟨fun ⟨c, hc⟩ => B.autMat_mem_evenAll0 hb0 hN0 x hc, ?_⟩
    rintro ⟨σ, s, -, ⟨hσ0, -⟩, hA⟩
    refine ⟨s 0, ?_⟩
    rw [hA, nmE0, spMat_mulVec_single, hσ0, mul_one]
    funext i
    by_cases hi : i = 0
    · subst hi
      simp
    · simp [Pi.single_eq_of_ne hi]
  odd_core := hodd
  big := hcard

theorem perm_mem_realized_of_setup (B : Basis3 G 8) {b₀ : G} (hb0 : B.b 0 = b₀)
    (hN0 : B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) = evenAll0 7)
    (hodd : OddCoreTrivial B.span)
    (hcard : 2 ^ 8 * Nat.factorial 8 < Nat.card ↥(ggAutomizer ⊤ B.span))
    (hFK : ∀ A ∈ nmFK, ∃ x, (B.n7MSetup hb0 hN0 hodd hcard).ρ x = A) (σ : Equiv.Perm (Fin 8)) :
    spMat σ 1 ∈ B.realized ⊤ := by
  obtain ⟨x, hx⟩ := hFK (spMat σ 1) ⟨σ, 1, fun _ => Or.inl rfl, by simp, rfl⟩
  obtain ⟨g, -, hgN, hg⟩ := mem_ggAutomizer_iff.mp x.2
  exact (B.mem_realized_iff _ _).mpr ⟨x.1, ⟨g, trivial, hgN, hg⟩, hx⟩

end Basis3

theorem l1N7Main_of_setupFK
    (hFK : ∀ (X : Type) [Group X] [Finite X] (S : N7MSetup X), ∀ A ∈ nmFK, ∃ x, S.ρ x = A) :
    L1N7Main := by
  refine l1N7Main_of_perm fun G _ _ b₀ K E hstd B hB _ _ hodd hN0 => ?_
  obtain ⟨hspan, hb0, -⟩ := hB
  subst hspan
  obtain ⟨-, ⟨-, -, -, -, -, hcard⟩, -⟩ := hstd
  exact B.perm_mem_realized_of_setup hb0 hN0 hodd hcard (hFK _ _)

end CFSG.StandardType.FrameRoute.FS81

end
