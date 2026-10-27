module

public import CFSG.LocalAnalysis.StandardType.GGTBRowCoordFrame
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitExcPlus
public import CFSG.LocalAnalysis.StandardType.GGTBRowFrame
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcWeylTorusAut

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

private theorem ggE6Row_torusMulAut_toAdd {τ : Tag} {p : ℕ} [NeZero p] (u : WeylGroup τ)
    (x : Multiplicative (Fin τ.rank → ZMod p)) :
    Multiplicative.toAdd (ExcWeylOuter.torusMulAut τ p u x) =
      TableBExc.torusAct τ p u (Multiplicative.toAdd x) := by
  rw [show x = Multiplicative.ofAdd (Multiplicative.toAdd x) from
    (ofAdd_toAdd x).symm]
  rw [ExcWeylOuter.torusMulAut_apply]
  simp only [toAdd_ofAdd]

private theorem ggE6Row_frame_of_model {τ : Tag} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {L' : Type} [Group L'] [Finite L'] {A : Subgroup (MulAut L')}
    {M : CoxeterMatrix (Fin τ.rank)} (e : M.Group ≃* WeylGroup τ)
    (he : ∀ i, e (M.simple i) = simple τ i) (h : GGExcPlusWeylModel τ p A)
    (hsc : GGTorusSelfCent p A) : GGWeylFrame p A M := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨Φ, w, hw, hact, hnorm⟩ := h
  have hn : ∀ i, MulAut.conj (w i) ∈ Subgroup.normalizer (A : Set (MulAut L')) :=
    fun i => conj_mem_normalizer_of_torusWeylElt hsc (hw i)
  let ρ : Fin τ.rank → MulAut A := fun i => ggConjAut A (hn i)
  have hρ : ∀ i (a : A), Multiplicative.toAdd (Φ (ρ i a)) =
      TableBExc.torusAct τ p (simple τ i) (Multiplicative.toAdd (Φ a)) :=
    fun i a => hact i a (ρ i a) (ggConjAut_apply A (hn i) a)
  have hρrefl : ∀ i, GGIsReflection p (ρ i) := by
    intro i
    refine ⟨?_, ?_⟩
    · refine MulEquiv.ext fun a => ?_
      apply Φ.injective
      apply Multiplicative.toAdd.injective
      rw [pow_two, MulAut.mul_apply, hρ, hρ, torusAct_simple_involutive, MulAut.one_apply]
    · have hcardA : Nat.card A = p ^ τ.rank := by
        rw [Nat.card_congr Φ.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_fun,
          Nat.card_zmod, Nat.card_fin]
      have hcardFix : Nat.card {a : A // ρ i a = a} = Nat.card
          {x : Fin τ.rank → ZMod p // TableBExc.torusAct τ p (simple τ i) x = x} := by
        refine Nat.card_congr (Equiv.subtypeEquiv (Φ.toEquiv.trans Multiplicative.toAdd) ?_)
        intro a
        change ρ i a = a ↔ TableBExc.torusAct τ p (simple τ i)
          (Multiplicative.toAdd (Φ a)) = Multiplicative.toAdd (Φ a)
        rw [← hρ]
        constructor
        · intro hh; rw [hh]
        · intro hh; exact Φ.injective (Multiplicative.toAdd.injective hh)
      rw [hcardFix, card_fix_torusAct_simple τ hp2 i, hcardA]
  let Ψ : WeylGroup τ →* MulAut A :=
    (MulAut.congr Φ.symm).toMonoidHom.comp (ExcWeylOuter.torusMulAut τ p)
  have hΨapply : ∀ (u : WeylGroup τ) (a : A),
      Multiplicative.toAdd (Φ (Ψ u a)) =
        TableBExc.torusAct τ p u (Multiplicative.toAdd (Φ a)) := by
    intro u a
    have hcongr : Ψ u a = Φ.symm (ExcWeylOuter.torusMulAut τ p u (Φ a)) := by
      show ((MulAut.congr Φ.symm) (ExcWeylOuter.torusMulAut τ p u)) a = _
      rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply]
      rfl
    rw [hcongr, MulEquiv.apply_symm_apply, ggE6Row_torusMulAut_toAdd]
  have hΨsimple : ∀ i, Ψ (simple τ i) = ρ i := by
    intro i
    refine MulEquiv.ext fun a => ?_
    apply Φ.injective
    apply Multiplicative.toAdd.injective
    rw [hΨapply, hρ]
  let H : Subgroup (MulAut L') := (MulAut.conj : L' →* MulAut L').range
  let K : Subgroup (MulAut A) := ggAutomizer H A
  have hmem : ∀ u, Ψ u ∈ K := by
    intro u
    obtain ⟨ω, rfl⟩ := (coxeterSystem τ).wordProd_surjective u
    induction ω with
    | nil => rw [CoxeterSystem.wordProd_nil, map_one]; exact K.one_mem
    | cons i ω ih =>
      rw [CoxeterSystem.wordProd_cons, map_mul]
      refine K.mul_mem ?_ ih
      rw [hΨsimple i]
      exact Subgroup.subset_closure
        (ggConjAut_mem_ggInduced (H := H) (Bs := A)
          (g := MulAut.conj (w i)) (MonoidHom.mem_range.mpr ⟨w i, rfl⟩) (hn i))
  let Ψcod : WeylGroup τ →* ↥K := Ψ.codRestrict K hmem
  have hΨinj : Function.Injective Ψ :=
    (MulAut.congr Φ.symm).injective.comp (ExcWeylOuter.torusMulAut_injective (τ := τ) hp2)
  have hΨcod_inj : Function.Injective Ψcod :=
    (MonoidHom.injective_codRestrict Ψ K hmem).mpr hΨinj
  have hK_le : K ≤ Ψ.range := by
    change Subgroup.closure (ggInduced H A) ≤ Ψ.range
    refine (Subgroup.closure_le _).mpr ?_
    rintro φ ⟨g, hgH, hgN, hφ⟩
    obtain ⟨m, rfl⟩ := MonoidHom.mem_range.mp hgH
    obtain ⟨u, hu⟩ := hnorm m hgN
    refine ⟨u, ?_⟩
    refine MulEquiv.ext fun a => ?_
    apply Φ.injective
    apply Multiplicative.toAdd.injective
    rw [hΨapply, hu a (φ a) (hφ a)]
  have hΨrange : Ψ.range = K :=
    le_antisymm (by rintro x ⟨u, rfl⟩; exact hmem u) hK_le
  have hΨcod_surj : Function.Surjective Ψcod := by
    intro y
    have hy : (y : MulAut A) ∈ Ψ.range := by rw [hΨrange]; exact y.2
    obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp hy
    exact ⟨u, Subtype.ext hu⟩
  let Ψiso : WeylGroup τ ≃* ↥K := MulEquiv.ofBijective Ψcod ⟨hΨcod_inj, hΨcod_surj⟩
  refine ⟨w, hn, hw, fun i => hρrefl i, e.trans Ψiso, fun i => ?_⟩
  show ((e.trans Ψiso) (M.simple i) : MulAut A) = ggConjAut A (hn i)
  rw [MulEquiv.trans_apply, he i]
  change Ψ (simple τ i) = ggConjAut A (hn i)
  exact hΨsimple i

theorem ggTorusWeylFrameW_of_excPlusModelSCr {τ : Tag} {p r : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {R : Type} [Group R] {I : Set (MulAut R)}
    {M : CoxeterMatrix (Fin τ.rank)} (e : M.Group ≃* WeylGroup τ)
    (he : ∀ i, e (M.simple i) = simple τ i) (h : GGExcPlusWeylModelSCr τ p r R I) :
    GGTorusWeylFrameW p r R I M := by
  intro L' _ _ ψ A hA
  exact ggE6Row_frame_of_model hp hp2 e he (h L' ψ A hA) hA.2.2.2.2.2.2.2

end CFSG.StandardType

end
