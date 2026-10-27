module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyTwoCapAltEquiv
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin
open CFSG.RankThree.PartTwo (altHeart)
open CFSG.HardMathSupport.Cooperstein.Coordinator (altAct altHeart_endo_eq_zero_or_id
  mk_pairEW_ne_zero)
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry (pairEW)

theorem s16k_centralizer_alt_trivial {Q : Type} [CommGroup Q] [Finite Q]
    {L' : Subgroup (MulAut Q)} {n : ℕ} (hn : 5 ≤ n) (hN : AlternatingNatural L' ⊤ ⊥ n) :
    Subgroup.centralizer (L' : Set (MulAut Q)) = ⊥ := by
  classical
  have hn0 : 0 < n := by omega
  obtain ⟨π, ψ, _hπsurj, hψ⟩ := s16c167_altNatural_equiv (W := Q) hn0 hN
  let e : Q ≃* Multiplicative (altHeart n) := (Subgroup.topEquiv.symm).trans ψ
  have he_apply : ∀ q : Q, e q = ψ ⟨q, Subgroup.mem_top q⟩ := by
    intro q
    show ψ (Subgroup.topEquiv.symm q) = ψ ⟨q, Subgroup.mem_top q⟩
    rw [show Subgroup.topEquiv.symm q = ⟨q, Subgroup.mem_top q⟩ from
      Subtype.ext (Subgroup.topEquiv_symm_apply_coe q)]
  have heq : ∀ (γ : alternatingGroup (Fin n)) (q : Q),
      e ((π γ : MulAut Q) q) = Multiplicative.ofAdd
        (altAct (γ : Equiv.Perm (Fin n)) (Multiplicative.toAdd (e q))) := by
    intro γ q
    have h := hψ γ (Subgroup.topEquiv.symm q) (Subgroup.mem_top _)
    rw [Subgroup.topEquiv_symm_apply_coe] at h
    rw [he_apply ((π γ : MulAut Q) q), he_apply q]
    exact h
  rw [Subgroup.eq_bot_iff_forall]
  intro c hc
  have hcomm : ∀ γ : alternatingGroup (Fin n),
      c * (π γ : MulAut Q) = (π γ : MulAut Q) * c :=
    fun γ => (Subgroup.mem_centralizer_iff.1 hc (π γ) (π γ).2).symm
  let F : MulAut (Multiplicative (altHeart n)) := MulAut.congr e c
  let g : altHeart n →+ altHeart n :=
    { toFun := fun v => Multiplicative.toAdd (F (Multiplicative.ofAdd v))
      map_zero' := by simp
      map_add' := fun v w => by
        change Multiplicative.toAdd (F (Multiplicative.ofAdd v * Multiplicative.ofAdd w)) =
          Multiplicative.toAdd (F (Multiplicative.ofAdd v)) +
            Multiplicative.toAdd (F (Multiplicative.ofAdd w))
        rw [map_mul]
        rfl }
  have hFact : ∀ (γ : alternatingGroup (Fin n)) (x : Multiplicative (altHeart n)),
      F (Multiplicative.ofAdd (altAct (γ : Equiv.Perm (Fin n)) (Multiplicative.toAdd x))) =
        Multiplicative.ofAdd (altAct (γ : Equiv.Perm (Fin n))
          (Multiplicative.toAdd (F x))) := by
    intro γ x
    have h1 : e.symm (Multiplicative.ofAdd (altAct (γ : Equiv.Perm (Fin n))
        (Multiplicative.toAdd x))) = (π γ : MulAut Q) (e.symm x) := by
      apply e.injective
      rw [e.apply_symm_apply]
      have h := heq γ (e.symm x)
      rw [e.apply_symm_apply] at h
      exact h.symm
    have h2 : F (Multiplicative.ofAdd (altAct (γ : Equiv.Perm (Fin n))
        (Multiplicative.toAdd x))) = e (c ((π γ : MulAut Q) (e.symm x))) := by
      show e (c (e.symm (Multiplicative.ofAdd (altAct (γ : Equiv.Perm (Fin n))
        (Multiplicative.toAdd x))))) = e (c ((π γ : MulAut Q) (e.symm x)))
      rw [h1]
    have h3 : c ((π γ : MulAut Q) (e.symm x)) = (π γ : MulAut Q) (c (e.symm x)) := by
      have := congrArg (fun m : MulAut Q => m (e.symm x)) (hcomm γ)
      simpa [MulAut.mul_apply] using this
    rw [h2, h3, heq γ (c (e.symm x))]
    rfl
  have hg : ∀ σ ∈ alternatingGroup (Fin n), ∀ v,
      g (altAct σ v) = altAct σ (g v) := by
    intro σ hσ v
    have h := congrArg Multiplicative.toAdd (hFact ⟨σ, hσ⟩ (Multiplicative.ofAdd v))
    simpa [g, toAdd_ofAdd] using h
  rcases altHeart_endo_eq_zero_or_id hn g hg with hg0 | hgid
  · exfalso
    set a : Fin n := ⟨0, by omega⟩
    set b : Fin n := ⟨1, by omega⟩
    set d : Fin n := ⟨2, by omega⟩
    have hab : a ≠ b := by simp [a, b, Fin.ext_iff]
    have hda : d ≠ a := by simp [a, d, Fin.ext_iff]
    have hdb : d ≠ b := by simp [b, d, Fin.ext_iff]
    have hvne : (pairEW a b : altHeart n) ≠ 0 := mk_pairEW_ne_zero hab hda hdb
    have hv0 : g (pairEW a b : altHeart n) = 0 := by rw [hg0]; rfl
    have hFv : F (Multiplicative.ofAdd (pairEW a b : altHeart n)) = 1 := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_one]
      exact hv0
    have h1 : Multiplicative.ofAdd (pairEW a b : altHeart n) = 1 := by
      apply F.injective
      rw [hFv, map_one]
    have h1' : Multiplicative.ofAdd (pairEW a b : altHeart n) = Multiplicative.ofAdd 0 := by
      rw [ofAdd_zero]
      exact h1
    exact hvne (Multiplicative.ofAdd.injective h1')
  · have hF1 : F = 1 := by
      ext x
      have h : g (Multiplicative.toAdd x) = Multiplicative.toAdd x := by
        simpa only [AddMonoidHom.id_apply] using
          congrArg (fun h : altHeart n →+ altHeart n => h (Multiplicative.toAdd x)) hgid
      change Multiplicative.toAdd (F (Multiplicative.ofAdd (Multiplicative.toAdd x))) =
        Multiplicative.toAdd x at h
      rw [ofAdd_toAdd] at h
      exact Multiplicative.toAdd.injective h
    have hc1 : c = 1 := (MulAut.congr e).injective (by
      rw [show MulAut.congr e c = F from rfl, hF1]
      exact (map_one (MulAut.congr e)).symm)
    exact hc1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
