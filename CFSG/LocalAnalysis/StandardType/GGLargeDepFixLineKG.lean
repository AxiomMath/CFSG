module

public import CFSG.LocalAnalysis.StandardType.GGLargeFixDefs
public import CFSG.LocalAnalysis.StandardType.GGResKnownGroup
public import CFSG.LocalAnalysis.StandardType.GGLargeDepConnected
public import CFSG.LocalAnalysis.StandardType.GGLargeDepRestrict
public import CFSG.LocalAnalysis.StandardType.GGLargeDepOrder
public import CFSG.LocalAnalysis.StandardType.GGLargeDepNoImprim
public import CFSG.LocalAnalysis.StandardType.GGLargeDepNoSym
import CFSG.LocalAnalysis.StandardType.GGLargeDepNoImprimBase

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma l04fD6_finite {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {ι : Type} {s : ι → (V ≃ₗ[ZMod p] V)} {x : V}
    (hlin : GGLargeLinHyp p N h α r s x) : Module.Finite (ZMod p) V := by
  have : Finite ι := hlin.finT
  exact ggFixLine_finite s hlin.s_refl hlin.fix_s

private lemma l04fD6_card_eq {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {ι : Type} (r : Fin (N - 1) → (V ≃ₗ[ZMod p] V))
    (s : ι → (V ≃ₗ[ZMod p] V)) (hA : ggLargeGrp r s ≤ ggLinStab (ggFixLineT r s))
    (hinj : Function.Injective (ggLargeRho r s hA)) :
    Nat.card ↥((ggLargeRho r s hA).range) = Nat.card ↥(ggLargeGrp r s) :=
  (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

theorem ggLargeDepFixLineLin_of_kg (hKG : GGReflClassLargeInput') : GGLargeDepFixLineLin := by
  intro p N _ V _ _ h α r ι s x hlin hdep hcard
  have hN : 11 ≤ N := hlin.N_ge
  by_contra hne
  simp only [not_le] at hne
  have htwo : 2 ≤ Module.finrank (ZMod p) ↥(ggLinFix (Set.range r)) := by omega
  let C : GGLargeDepCase p N h α r s x := ⟨hlin, hdep, hcard, htwo⟩
  have hconn : GGLargeConnected r s := ggLargeDep_connected C
  obtain ⟨hA, hd1, hd2, hρ⟩ := ggLargeDep_restrict C hconn
  have : Module.Finite (ZMod p) V := l04fD6_finite hlin
  have : Module.Finite (ZMod p) ↥(ggFixLineT r s) :=
    FiniteDimensional.finiteDimensional_submodule (ggFixLineT r s)
  let Q : Subgroup (↥(ggFixLineT r s) ≃ₗ[ZMod p] ↥(ggFixLineT r s)) :=
    (ggLargeRho r s hA).range
  have hd9 : 9 ≤ Module.finrank (ZMod p) ↥(ggFixLineT r s) := by omega
  have hKGapp := hKG p hlin.p_ne_two ↥(ggFixLineT r s)
    (Module.finrank (ZMod p) ↥(ggFixLineT r s)) rfl hd9 Q hρ.2.1 hρ.2.2
  rcases hKGapp with himp | hbound | hsym1 | hsym2
  · exact (ggLargeDep_noImprim C.lin.toNineLinHyp C.two hA hρ) himp
  · exfalso
    have hcardQ : Nat.card Q = Nat.card ↥(ggLargeGrp r s) := l04fD6_card_eq r s hA hρ.1
    rw [hcardQ] at hbound
    have hlt := ggLargeDep_order C hd1 hd2
    omega
  · exact (ggLargeDep_noSym C hconn hA hρ) (Or.inl hsym1)
  · exact (ggLargeDep_noSym C hconn hA hρ) (Or.inr hsym2)

end CFSG.StandardType

end
