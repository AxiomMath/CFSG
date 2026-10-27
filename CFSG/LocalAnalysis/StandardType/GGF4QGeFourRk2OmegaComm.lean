module

public import CFSG.LocalAnalysis.StandardType.GGF4PairRootLeviTransport
public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourKGPos
import CFSG.LocalAnalysis.StandardType.GGF4QGeFourRk2Cross
import CFSG.ClassicalInvolution.WeakCT.TwistedSpinModel
import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Assembly CFSG.LieType.Universal CFSG.LieType.RootSystem
open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
open CFSG.LieType.CurtisTits (rankOne)

theorem ggF4QGeFourRk2_commute_of_tableBPosImage_POmegaMinus
    {G : Type} [Group G] [Finite G] {p : ℕ} {Bs : Subgroup G}
    (hpp : p.Prime) (hp2 : p ≠ 2) (hBs : IsElemAbelian p Bs) (hNT : GGNoTransvection p Bs)
    {A : Subgroup (MulAut ↥Bs)} (hAind : A ≤ ggInduced ⊤ Bs)
    {e : CoxeterMatrix.F₄.Group ≃* ↥A} (hpres : GGCoxeterPres p A CoxeterMatrix.F₄ e)
    {X : Subgroup G} (hXA : ggAutomizer X Bs ≤ A) {f : ℕ} (hf : 2 ≤ f)
    (hpos : GGTableBPosImage p Bs .POmegaMinus 4 f X)
    (w : CoxeterMatrix.F₄.Group) (i j : Fin 4)
    (hi : ((e (w * CoxeterMatrix.F₄.simple i * w⁻¹) : ↥A) : MulAut ↥Bs) ∈ ggAutomizer X Bs)
    (hj : ((e (w * CoxeterMatrix.F₄.simple j * w⁻¹) : ↥A) : MulAut ↥Bs) ∈ ggAutomizer X Bs) :
    CoxeterMatrix.F₄ i j = 2 →
      ∀ a ∈ ggRankOneIn X Bs ((e (w * CoxeterMatrix.F₄.simple i * w⁻¹) : ↥A) : MulAut ↥Bs),
        ∀ b ∈ ggRankOneIn X Bs ((e (w * CoxeterMatrix.F₄.simple j * w⁻¹) : ↥A) : MulAut ↥Bs),
          a * b = b * a := by
  by_cases hij : i = j
  · subst j
    intro h2
    have h1 : CoxeterMatrix.F₄ i i = 1 := CoxeterMatrix.F₄.diagonal i
    exact False.elim (by omega)
  obtain ⟨ψ, _hker, _hrange, ε, hε, hlev, _⟩ := hpos
  have hadm : StatedLieAdmissible .POmegaMinus 4 2 f :=
    ⟨Nat.prime_two, by omega, by change 4 ≤ 4; exact le_rfl⟩
  obtain ⟨ν, hν⟩ := (ggTagFacts_POmegaMinus hadm (by decide)).2.1
  have hM : ∀ k l : Fin 3, (coxeterMatrix (ggU .POmegaMinus 4 f).D.isFiniteType)
      ((Equiv.refl (Fin 3)) k) ((Equiv.refl (Fin 3)) l) = CoxeterMatrix.B 3 k l := by
    intro k l
    rw [coxeterMatrix_POmegaMinus_four]
    rfl
  obtain ⟨u, c, d, hSi, hSj, h2, _h3, _h4⟩ :=
    exists_f4_pair_rootLevi_transport (ggU .POmegaMinus 4 f).D hpp hp2 hBs hNT hAind hpres
      hXA ψ ε hε hlev (Equiv.refl _) hM ν hν w i j hij hi hj
  let ψ' : (ggU .POmegaMinus 4 f).K →* G :=
    (MulAut.conj (ψ (ν u))).toMonoidHom.comp ψ
  have hnative :
      ∀ a ∈ ggRootLevi (ggU .POmegaMinus 4 f).D
        (Pi.single ((Equiv.refl (Fin 3)) 0) 1),
      ∀ b ∈ ggRootLevi (ggU .POmegaMinus 4 f).D
        (Pi.single ((Equiv.refl (Fin 3)) 2) 1), a * b = b * a := by
    change ∀ a ∈ rankOne (minusDatum 4 (minusCoeffs_irr 2 f)).rootGroup (0 : Fin 3),
      ∀ b ∈ rankOne (minusDatum 4 (minusCoeffs_irr 2 f)).rootGroup (2 : Fin 3), a * b = b * a
    exact CFSG.ClassicalInvolution.WeakCT.commute_rankOne_minusDatum
      (minusCoeffs_irr 2 f) 0 2 (by decide)
  have hmap :
      ∀ a ∈ (ggRootLevi (ggU .POmegaMinus 4 f).D
        (Pi.single ((Equiv.refl (Fin 3)) 0) 1)).map ψ',
      ∀ b ∈ (ggRootLevi (ggU .POmegaMinus 4 f).D
        (Pi.single ((Equiv.refl (Fin 3)) 2) 1)).map ψ', a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hnative a ha b hb]
  intro hlabel
  rw [hSi, hSj]
  rcases h2 hlabel with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hmap
  · intro a ha b hb
    exact (hmap b hb a ha).symm

end CFSG.StandardType

end
