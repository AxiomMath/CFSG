module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115CharTwoTools
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Residual
public import CFSG.Quasithin.Background.A3ComponentsBasic

public section

namespace CFSG.Quasithin.Rk2

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X6 CFSG.Quasithin
open scoped commutatorElement

structure Rank2Pkg.Ext (Y : Type) [Group Y] (U : Subgroup Y) (P : Fin 2 → Subgroup Y) : Prop where
  charTwo_par : ∀ j, CharTwo (P j)
  le_perfectCore : ∀ j, U ≤ perfectCore (P j)
  inner : ∀ j, ∀ g ∈ P j, ∃ y ∈ perfectCore (P j), ∀ x ∈ perfectCore (P j),
    ⁅g * y⁻¹, x⁆ ∈ pCoreOf 2 (perfectCore (P j))
  solvable_le_normalizer : ∀ X : Subgroup Y, U ≤ X → Group.IsSolvable ↥X →
    X ≤ Subgroup.normalizer (U : Set Y)

theorem Rank2Pkg.Ext.map {Y Y' : Type} [Group Y] [Group Y'] [Finite Y] [Finite Y']
    {U : Subgroup Y} {P : Fin 2 → Subgroup Y} (h : Rank2Pkg.Ext Y U P) (e : Y ≃* Y') :
    Rank2Pkg.Ext Y' (U.map e.toMonoidHom) (fun j => (P j).map e.toMonoidHom) where
  charTwo_par j := CFSG.QuasithinUnique.Ch1.charTwo_map_mulEquiv e (h.charTwo_par j)
  le_perfectCore j := by
    rw [← map_perfectCore e.toMonoidHom (P j)]
    exact Subgroup.map_mono (h.le_perfectCore j)
  inner j g hg := by
    obtain ⟨g₀, hg₀, rfl⟩ := hg
    obtain ⟨y₀, hy₀, hy⟩ := h.inner j g₀ hg₀
    refine ⟨e y₀, ?_, fun x hx => ?_⟩
    · rw [← map_perfectCore e.toMonoidHom (P j)]
      exact ⟨y₀, hy₀, rfl⟩
    · rw [← map_perfectCore e.toMonoidHom (P j)] at hx ⊢
      obtain ⟨x₀, hx₀, rfl⟩ := hx
      rw [CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 e]
      have := Subgroup.mem_map_of_mem e.toMonoidHom (hy x₀ hx₀)
      convert this using 1
      simp [commutatorElement_def]
  solvable_le_normalizer X hUX hX := by
    have hsymm : ∀ A : Subgroup Y, (A.map e.toMonoidHom).map e.symm.toMonoidHom = A := fun A => by
      rw [Subgroup.map_map]
      have : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id Y := by ext; simp
      rw [this, Subgroup.map_id]
    have hsymm' : ∀ A : Subgroup Y', (A.map e.symm.toMonoidHom).map e.toMonoidHom = A := fun A => by
      rw [Subgroup.map_map]
      have : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id Y' := by ext; simp
      rw [this, Subgroup.map_id]
    have h1 : U ≤ X.map e.symm.toMonoidHom := by
      have := Subgroup.map_mono (f := e.symm.toMonoidHom) hUX
      rwa [hsymm] at this
    have h2 := h.solvable_le_normalizer _ h1 (map_isSolvable_equiv e.symm X hX)
    rw [← hsymm' X, ← Subgroup.map_equiv_normalizer_eq U e]
    exact Subgroup.map_mono h2

end CFSG.Quasithin.Rk2
