module

public import CFSG.Timmesfeld.Bridge.Asc72Basic
public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenCls
import CFSG.OddTranspositions.PartThree.Ten.WreathClass
import CFSG.OddTranspositions.PartThree.Ten.CentralSymSplit
import CFSG.OddTranspositions.PartThree.Ten.WreathEndgame
import CFSG.RankThree.SteinbergR3ELargeEvenLinearTwoCover
public import CFSG.CGT.Timmesfeld75.Cfg214Gen
public import CFSG.LargeExtraspecial.S9TIXC
public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenInputs
public import CFSG.LocalAnalysis.WeakClosure81.SevenFour
public import CFSG.LocalAnalysis.WeakClosure81.SevenNineDefs
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Basic
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent

public section

namespace CFSG.OddTranspositions.PartFour

open scoped commutatorElement
open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge.Asc72 CFSG.LocalAnalysis.WeakClosure81
open CFSG.OddTranspositions.PartThree CFSG.OddTranspositions.PartThree.CentralSymSplit

variable {X : Type} [Group X]

private noncomputable def l2WreathEquivWreathSym (f m : ℕ) :
    L2Wreath f m ≃* WreathSym (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) m :=
  SemidirectProduct.congr
    (MulEquiv.piCongrRight fun _ =>
      CFSG.RankThree.projectiveSpecialLinearTwoEquivSLOfCharTwo (GaloisField 2 f))
    (MulEquiv.refl _) (fun σ => by ext h i; rfl)

private theorem l2WreathEquivWreathSym_inr (f m : ℕ) (σ : Equiv.Perm (Fin m)) :
    l2WreathEquivWreathSym f m (SemidirectProduct.inr σ) = SemidirectProduct.inr σ := by
  refine SemidirectProduct.ext ?_ rfl
  funext i
  simp [l2WreathEquivWreathSym]

private theorem exists_isConj_inr_swap {f m : ℕ} (hf : 2 ≤ f) (hm : 5 ≤ m)
    {C : Set (L2Wreath f m)} (hS : Setup (L2Wreath f m) C) {c : L2Wreath f m} (hc : c ∈ C) :
    ∃ i j : Fin m, i ≠ j ∧ IsConj (SemidirectProduct.inr (Equiv.swap i j)) c := by
  obtain ⟨d₀, rfl⟩ := hS.isClass
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.2 (by omega)
  have hπ : Function.Surjective
      (SemidirectProduct.rightHom : L2Wreath f m →* Equiv.Perm (Fin m)) :=
    SemidirectProduct.rightHom_surjective
  have h1 : ∀ x ∈ {g | IsConj d₀ g},
      (SemidirectProduct.rightHom : L2Wreath f m →* Equiv.Perm (Fin m)) x ≠ 1 :=
    fun x hx => map_ne_one_of_isConj _ hπ hS.gen hx
  have hconj : ∀ c ∈ {g | IsConj d₀ g}, ∀ g : L2Wreath f m, g * c * g⁻¹ ∈ {g | IsConj d₀ g} :=
    fun c hc g => hS.conj_mem g hc
  have hodd' := isOddTransp_image _ hS.oddT h1
  have hcls := image_isConj_class _ hπ d₀
  have hgen' := closure_image_eq_top _ hπ hS.gen
  have hsw : c.right.IsSwap := by
    rcases isSwap_or_triple_of_isOddTransp hm hodd' ⟨_, hcls⟩ hgen' with h | ⟨h6, htr⟩
    · exact h _ ⟨c, hc, rfl⟩
    · subst h6
      exact absurd (htr _ ⟨c, hc, rfl⟩) (WreathClass.not_triple_right hf hS.oddT hconj hc)
  have hcs := WreathClass.mem_swapSet_of_isSwap_right hf hm hS.oddT hconj hc hsw
  obtain ⟨i, j, hij, -⟩ := id hcs
  exact ⟨i, j, hij, WreathEndgame.isConj_of_mem_swapSet hij hcs⟩

theorem exists_isWreathTransposition_of_mulEquiv_l2Wreath [Finite X] {E : Set X} (hS : Setup X E)
    {f m : ℕ} (hf : 2 ≤ f) (hm : 5 ≤ m) (e : X ≃* L2Wreath f m) :
    ∃ s ∈ E, IsWreathTransposition X f m s := by
  obtain ⟨s, hs⟩ := hS.nonempty
  have hZ : Subgroup.center X = ⊥ := WreathEndgame.center_eq_bot_of_equiv hf e
  have hS' := hS.map e.toMonoidHom e.surjective
    (fun d hd h => hS.oddT.ne_one hd (e.injective (h.trans e.map_one.symm)))
  obtain ⟨i, j, hij, hc⟩ := exists_isConj_inr_swap hf hm hS' (Set.mem_image_of_mem _ hs)
  refine ⟨s, hs, by omega, GaloisField 2 f, inferInstance, inferInstance,
    GaloisField.card 2 f (by omega),
    (QuotientGroup.quotientMulEquivOfEq hZ).trans
      (QuotientGroup.quotientBot.trans (e.trans (l2WreathEquivWreathSym f m))), i, j, hij, ?_⟩
  have := (l2WreathEquivWreathSym f m).toMonoidHom.map_isConj hc
  change IsConj (l2WreathEquivWreathSym f m (SemidirectProduct.inr (Equiv.swap i j)))
    (l2WreathEquivWreathSym f m (e s)) at this
  rw [l2WreathEquivWreathSym_inr] at this
  exact this.symm

theorem derivedSeries_one_ne_two_of_mulEquiv_l2Wreath {f m : ℕ} (hm : m = 3 ∨ m = 4)
    (e : X ≃* L2Wreath f m) : derivedSeries X 1 ≠ derivedSeries X 2 := by
  intro h
  have hπs : Function.Surjective
      ((SemidirectProduct.rightHom : L2Wreath f m →* Equiv.Perm (Fin m)).comp e.toMonoidHom) :=
    SemidirectProduct.rightHom_surjective.comp e.surjective
  have h12 : derivedSeries (Equiv.Perm (Fin m)) 1 = derivedSeries (Equiv.Perm (Fin m)) 2 := by
    rw [← map_derivedSeries_eq hπs 1, ← map_derivedSeries_eq hπs 2, h]
  have hsolv : Group.IsSolvable (Equiv.Perm (Fin m)) :=
    Equiv.Perm.isSolvable (by simp; omega)
  have hstab : ∀ n, derivedSeries (Equiv.Perm (Fin m)) (n + 1) =
      derivedSeries (Equiv.Perm (Fin m)) 1 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [derivedSeries_succ, ih, ← derivedSeries_succ]; exact h12.symm
  obtain ⟨n, hn⟩ := hsolv.solvable
  have hbot : derivedSeries (Equiv.Perm (Fin m)) 1 = ⊥ := by
    rw [← hstab n]
    exact le_bot_iff.mp ((derivedSeries_antitone _ (Nat.le_succ n)).trans hn.le)
  have hcomm : ∀ a b : Equiv.Perm (Fin m), a * b = b * a := by
    intro a b
    have h1 : ⁅a, b⁆ ∈ derivedSeries (Equiv.Perm (Fin m)) 1 :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  rcases hm with rfl | rfl
  · exact absurd (hcomm (Equiv.swap 0 1) (Equiv.swap 1 2)) (by decide)
  · exact absurd (hcomm (Equiv.swap 0 1) (Equiv.swap 1 2)) (by decide)

theorem nonempty_mulEquiv_psl2Model_of_l2Wreath_one {f : ℕ} (e : X ≃* L2Wreath f 1) :
    Nonempty (X ≃* CFSG.Theory.Comparator.PSL2Model f) := by
  let u : (Fin 1 → CFSG.Theory.Comparator.PSL2Model f) ≃* CFSG.Theory.Comparator.PSL2Model f :=
    MulEquiv.funUnique (Fin 1) (CFSG.Theory.Comparator.PSL2Model f)
  let g : CFSG.Theory.Comparator.PSL2Model f →* L2Wreath f 1 :=
    SemidirectProduct.inl.comp u.symm.toMonoidHom
  have hg : Function.Bijective g := by
    refine ⟨SemidirectProduct.inl_injective.comp u.symm.injective, fun w => ?_⟩
    refine ⟨u w.left, ?_⟩
    apply SemidirectProduct.ext
    · simp [g]
    · exact Subsingleton.elim _ _
  exact ⟨e.trans (MulEquiv.ofBijective g hg).symm⟩

theorem eq_one_of_mulEquiv_l2Wreath_zero {f : ℕ} (e : X ≃* L2Wreath f 0) (x : X) : x = 1 := by
  have : Subsingleton (L2Wreath f 0) :=
    ⟨fun a b => SemidirectProduct.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)⟩
  exact e.injective (Subsingleton.elim _ _)

end CFSG.OddTranspositions.PartFour
