module

public import CFSG.LocalAnalysis.StandardType.GGF4PairRootLeviTransport
public import CFSG.ClassicalInvolution.WeakCT.TwistedSpinModel
import CFSG.LocalAnalysis.StandardType.GGF4QGeFourRk2Cross
import CFSG.RankThree.PartOne.CTP.SpinMinusEven
import CFSG.RankThree.PartOne.CTP.SpinCenterEven
import CFSG.ClassicalInvolution.Models.LinearPairs.Pairs
import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Assembly CFSG.LieType.Universal CFSG.LieType.RootSystem
open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
open CFSG.LieType.CurtisTits (rankOne)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)

theorem linearBlockStandardPair_minusDatum_even {F : Type} [Field F] [Finite F] [CharP F 2]
    {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {n : ℕ} {i j : Fin (n - 1)}
    (hij : i.val + 1 = j.val) (hi : i.val + 1 < n - 1) (hj : j.val + 1 < n - 1) :
    ∃ W : Subgroup (spinGroup (quadMinus n F b c)),
      LinearBlockStandardPair F W (rankOne (minusDatum n hirr).rootGroup i)
        (rankOne (minusDatum n hirr).rootGroup j) := by
  obtain ⟨emb, hinj, h0, h1⟩ := CFSG.RankThree.PartOne.CTP.exists_sl3_minus_even b c hij hi hj
  apply CFSG.ClassicalInvolution.WeakCT.linearBlockStandardPair_of_levi emb hinj
  · rw [CFSG.ClassicalInvolution.WeakCT.rankOne_minusDatum_long hirr hi, h0]
  · rw [CFSG.ClassicalInvolution.WeakCT.rankOne_minusDatum_long hirr hj, h1]

theorem ggF4QGeFourRk2_linear_of_tableBPosImage_POmegaMinus
    {G : Type} [Group G] [Finite G] {p : ℕ} {Bs : Subgroup G}
    (hpp : p.Prime) (hp2 : p ≠ 2) (hBs : IsElemAbelian p Bs) (hNT : GGNoTransvection p Bs)
    {A : Subgroup (MulAut ↥Bs)} (hAind : A ≤ ggInduced ⊤ Bs)
    {e : CoxeterMatrix.F₄.Group ≃* ↥A} (hpres : GGCoxeterPres p A CoxeterMatrix.F₄ e)
    {X : Subgroup G} (hXA : ggAutomizer X Bs ≤ A) {f : ℕ} (hf : 2 ≤ f)
    (hpos : GGTableBPosImage p Bs .POmegaMinus 4 f X)
    (w : CoxeterMatrix.F₄.Group) (i j : Fin 4)
    (hi : ((e (w * CoxeterMatrix.F₄.simple i * w⁻¹) : ↥A) : MulAut ↥Bs) ∈ ggAutomizer X Bs)
    (hj : ((e (w * CoxeterMatrix.F₄.simple j * w⁻¹) : ↥A) : MulAut ↥Bs) ∈ ggAutomizer X Bs) :
    CoxeterMatrix.F₄ i j = 3 →
      ∃ (F : Type) (_ : Field F) (_ : Finite F) (W : Subgroup G), CharP F 2 ∧
        LinearBlockStandardPair F W
          (ggRankOneIn X Bs ((e (w * CoxeterMatrix.F₄.simple i * w⁻¹) : ↥A) : MulAut ↥Bs))
          (ggRankOneIn X Bs ((e (w * CoxeterMatrix.F₄.simple j * w⁻¹) : ↥A) : MulAut ↥Bs)) := by
  by_cases hij : i = j
  · subst j
    intro h3
    have h1 : CoxeterMatrix.F₄ i i = 1 := CoxeterMatrix.F₄.diagonal i
    exact False.elim (by omega)
  obtain ⟨ψ, hker, _hrange, ε, hε, hlev, _⟩ := hpos
  have hadm : StatedLieAdmissible .POmegaMinus 4 2 f :=
    ⟨Nat.prime_two, by omega, by change 4 ≤ 4; exact le_rfl⟩
  obtain ⟨ν, hν⟩ := (ggTagFacts_POmegaMinus hadm (by decide)).2.1
  have hM : ∀ k l : Fin 3, (coxeterMatrix (ggU .POmegaMinus 4 f).D.isFiniteType)
      ((Equiv.refl (Fin 3)) k) ((Equiv.refl (Fin 3)) l) = CoxeterMatrix.B 3 k l := by
    intro k l
    rw [coxeterMatrix_POmegaMinus_four]
    rfl
  obtain ⟨u, c, d, hSi, hSj, _h2, h3, _h4⟩ :=
    exists_f4_pair_rootLevi_transport (ggU .POmegaMinus 4 f).D hpp hp2 hBs hNT hAind hpres
      hXA ψ ε hε hlev (Equiv.refl _) hM ν hν w i j hij hi hj
  let ψ' : (ggU .POmegaMinus 4 f).K →* G :=
    (MulAut.conj (ψ (ν u))).toMonoidHom.comp ψ
  have hψinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans (CFSG.RankThree.PartOne.CTP.center_spinGroup_quadMinus_eq_bot
      (F := GaloisField 2 f) (by decide : 4 ≤ 4) (minusCoeffs_irr 2 f)).le
  have hψ'inj : Function.Injective ψ' := (MulAut.conj (ψ (ν u))).injective.comp hψinj
  have hnative : ∃ W : Subgroup (ggU .POmegaMinus 4 f).K,
      LinearBlockStandardPair (GaloisField 2 f) W
        (ggRootLevi (ggU .POmegaMinus 4 f).D (Pi.single ((Equiv.refl (Fin 3)) 0) 1))
        (ggRootLevi (ggU .POmegaMinus 4 f).D (Pi.single ((Equiv.refl (Fin 3)) 1) 1)) := by
    change ∃ W : Subgroup (spinGroup
        (quadMinus 4 (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)),
      LinearBlockStandardPair (GaloisField 2 f) W
        (rankOne (minusDatum 4 (minusCoeffs_irr 2 f)).rootGroup (0 : Fin 3))
        (rankOne (minusDatum 4 (minusCoeffs_irr 2 f)).rootGroup (1 : Fin 3))
    exact linearBlockStandardPair_minusDatum_even
      (F := GaloisField 2 f) (n := 4) (b := (minusCoeffs 2 f).1) (c := (minusCoeffs 2 f).2)
      (minusCoeffs_irr 2 f)
      (i := (0 : Fin 3)) (j := (1 : Fin 3)) (by decide) (by decide) (by decide)
  obtain ⟨W, hW⟩ := hnative
  have hpair := CFSG.ClassicalInvolution.Models.linearBlockStandardPair_map hW ψ' hψ'inj
  intro hlabel
  refine ⟨GaloisField 2 f, inferInstance, inferInstance, W.map ψ', inferInstance, ?_⟩
  rw [hSi, hSj]
  obtain ⟨rfl, rfl⟩ := h3 hlabel
  exact hpair

end CFSG.StandardType

end
