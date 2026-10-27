module

public import CFSG.LocalAnalysis.StandardType.GGFrameTBExcNum
public import CFSG.LocalAnalysis.StandardType.GGFrameWholeFacts
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNSEnnolaExcPlusAux2
import CFSG.LocalAnalysis.StandardType.GGFrameTBExcMat
import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeExcPlusAux
import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeExcPlusAux2
import CFSG.LocalAnalysis.StandardType.GGNoTransvectionAutForm
import CFSG.LocalAnalysis.StandardType.GGTorusGenExcTwoBase
import CFSG.LocalAnalysis.StandardType.GGExcRootAsGen
import CFSG.LocalAnalysis.StandardType.GGRootGenAvoidReflModel

public section

namespace CFSG.StandardType.FrameRoute

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

private theorem frameExcPlus_gen_torusAct {τ : Tag} {L' : Type} [Group L']
    {A : Subgroup (MulAut L')} (Φ : A ≃* Multiplicative (Fin τ.rank → ZMod 3))
    (hnorm : ∀ n : L', MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) →
      ∃ u : WeylGroup τ, ∀ a b : A,
        (b : MulAut L') = MulAut.conj n * a * (MulAut.conj n)⁻¹ →
          Multiplicative.toAdd (Φ b) =
            TableBExc.torusAct τ 3 u (Multiplicative.toAdd (Φ a))) :
    ∀ φ ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A,
      ∃ u : WeylGroup τ, ∀ a : A,
        Multiplicative.toAdd (Φ (φ a)) =
          TableBExc.torusAct τ 3 u (Multiplicative.toAdd (Φ a)) := by
  classical
  haveI : NeZero 3 := ⟨by norm_num⟩
  intro φ hφ
  change φ ∈ Subgroup.closure (ggInduced (MulAut.conj : L' →* MulAut L').range A) at hφ
  refine Subgroup.closure_induction (p := fun g _ => ∃ u : WeylGroup τ, ∀ a : A,
    Multiplicative.toAdd (Φ (g a)) =
      TableBExc.torusAct τ 3 u (Multiplicative.toAdd (Φ a))) ?_ ?_ ?_ ?_ hφ
  · rintro ψ ⟨g, hgH, hgN, hψ⟩
    obtain ⟨n, rfl⟩ := MonoidHom.mem_range.mp hgH
    obtain ⟨u, hu⟩ := hnorm n hgN
    exact ⟨u, fun a => hu a (ψ a) (hψ a)⟩
  · exact ⟨1, fun a => by rw [MulAut.one_apply, TableBExc.torusAct_one]⟩
  · rintro ψ χ _ _ ⟨u, hu⟩ ⟨v, hv⟩
    refine ⟨u * v, fun a => ?_⟩
    change Multiplicative.toAdd (Φ (ψ (χ a))) = _
    rw [hu (χ a), hv a, TableBExc.torusAct_mul]
  · rintro ψ _ ⟨u, hu⟩
    refine ⟨u⁻¹, fun a => ?_⟩
    have h1 : TableBExc.torusAct τ 3 u (Multiplicative.toAdd (Φ (ψ⁻¹ a))) =
        Multiplicative.toAdd (Φ a) := by
      rw [← hu (ψ⁻¹ a), MulAut.apply_inv_self]
    have h2 := congrArg (TableBExc.torusAct τ 3 u⁻¹) h1
    rw [← TableBExc.torusAct_mul, inv_mul_cancel, TableBExc.torusAct_one] at h2
    exact h2

private theorem frameExcPlus_false_of_gen_transvection
    {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {L' : Type} [Group L']
    {A : Subgroup (MulAut L')} {Φ : A ≃* Multiplicative (Fin τ.rank → ZMod 3)}
    (hgen : ∀ φ ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A,
      ∃ u : WeylGroup τ, ∀ a : A,
        Multiplicative.toAdd (Φ (φ a)) =
          TableBExc.torusAct τ 3 u (Multiplicative.toAdd (Φ a)))
    {φ : MulAut ↥A} (hφ : φ ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A)
    (htv : GGIsTransvection 3 φ) : False := by
  classical
  haveI : NeZero 3 := ⟨by norm_num⟩
  obtain ⟨u, hu⟩ := hgen φ hφ
  let ι : Multiplicative (Fin τ.rank → ZMod 3) →* MulAut L' :=
    A.subtype.comp Φ.symm.toMonoidHom
  have hι : Function.Injective ι := by
    intro x y hxy
    exact Φ.symm.injective (Subtype.ext hxy)
  have hιB : ι.range = A := by
    ext a
    constructor
    · rintro ⟨x, rfl⟩
      exact (Φ.symm x).2
    · intro ha
      exact ⟨Φ ⟨a, ha⟩, congrArg Subtype.val (MulEquiv.symm_apply_apply Φ ⟨a, ha⟩)⟩
  have ht : ∀ (b : A) (s : Fin τ.rank → ZMod 3),
      (b : MulAut L') = ι (Multiplicative.ofAdd s) →
        ((φ b : A) : MulAut L') =
          ι (Multiplicative.ofAdd (TableBExc.torusAct τ 3 u s)) := by
    intro b s hb
    have hbA : b = Φ.symm (Multiplicative.ofAdd s) := by
      apply Subtype.ext
      rw [hb]
      rfl
    have hb' : Multiplicative.toAdd (Φ b) = s := by
      rw [hbA, MulEquiv.apply_symm_apply]
      rfl
    have hstep : Multiplicative.toAdd (Φ (φ b)) = TableBExc.torusAct τ 3 u s := by
      rw [hu b, hb']
    have hφeq : Φ (φ b) = Multiplicative.ofAdd (TableBExc.torusAct τ 3 u s) :=
      Multiplicative.toAdd.injective hstep
    change ((φ b : A) : MulAut L') =
      (Φ.symm (Multiplicative.ofAdd (TableBExc.torusAct τ 3 u s)) : A).val
    rw [← hφeq, MulEquiv.symm_apply_apply]
  obtain ⟨hfix, hN⟩ := NoTvAut.transvection_coords (p := 3) hι hιB
    (t := fun s => TableBExc.torusAct τ 3 u s) ht htv
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hdet : (NoTvAut.cartanMod τ 3).det ≠ 0 := by
    rw [NoTvAut.det_cartanMod]
    exact (ExcFrames.isUnit_det_symmetrizedCartan (Or.inr hτ) (p := 3) (by norm_num)).ne_zero
  exact NoTvAut.false_of_isTransvection_similitude (p := 3) (by norm_num)
    NoTvAut.cartanMod_transpose hdet (NoTvAut.torusActHom τ 3 u) 1
    (fun x y => by rw [one_mul]; exact NoTvAut.torusAct_form u x y) hfix hN

theorem not_isTransvection_of_excPlusModel
    {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {L' : Type} [Group L']
    [Finite L'] {A : Subgroup (MulAut L')} (h : GGExcPlusWeylModel τ 3 A) :
    ∀ φ ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A, ¬ GGIsTransvection 3 φ := by
  obtain ⟨Φ, _, _, _, hnorm⟩ := h
  intro φ hφ htv
  exact frameExcPlus_false_of_gen_transvection hτ
    (frameExcPlus_gen_torusAct Φ hnorm) hφ htv

private theorem frameExcPlus_finiteMulAut (L' : Type) [Group L'] [Finite L'] :
    Finite (MulAut L') :=
  Finite.of_injective (fun f : MulAut L' => (f : L' → L')) DFunLike.coe_injective

private theorem frameExcPlus_frameNum_post {τ : Tag} {N d : ℕ}
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {L' : Type} [Group L'] [Finite L']
    {A : Subgroup (MulAut L')} (hA : IsElemAbelian 3 A)
    {𝒜 : Subgroup (MulAut ↥A)}
    {e : (CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartan τ)).Group ≃* ↥𝒜}
    (hpres : GGCoxeterPres 3 𝒜
      (CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartan τ)) e)
    (h3 : ∀ i j : Fin τ.rank, i ≠ j →
      (CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartan τ)).M i j ≤ 3)
    (hnt : ∀ φ ∈ 𝒜, ¬ GGIsTransvection 3 φ)
    (hN : (feT τ.rank).ncard = N)
    (hd : ∀ r ∈ feT τ.rank, {t | t ∈ feT τ.rank ∧ r * t ≠ t * r}.ncard = d)
    (hconn : ∀ r ∈ feT τ.rank, ∀ t ∈ feT τ.rank,
      Relation.ReflTransGen (fun a b => a ∈ feT τ.rank ∧ b ∈ feT τ.rank ∧ a * b ≠ b * a) r t) :
    FrameNumIs 𝒜 N (some d) ∧ FrameConn 𝒜 := by
  haveI : Finite (MulAut L') := frameExcPlus_finiteMulAut L'
  let ρ : ↥𝒜 →* FEMat τ.rank := (frameAdMat τ).comp e.symm.toMonoidHom
  have hρi : Function.Injective ρ :=
    (frameAdMat_injective τ).comp e.symm.injective
  have hρ : ∀ i : Fin τ.rank,
      ρ (e ((CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartan τ)).simple i)) =
        feS τ.rank i := by
    intro i
    have h1 : ρ (e ((CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartan τ)).simple i)) =
        frameAdMat τ
          ((CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartan τ)).simple i) := by
      show frameAdMat τ (e.symm (e
        ((CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartan τ)).simple i))) = _
      rw [MulEquiv.symm_apply_apply]
    rw [h1]
    have hsimple :
        (CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartan τ)).simple i = simple τ i := rfl
    rw [hsimple, frameAdMat_simple hτ i]
  exact frameNumIs_frameConn_of_frameRep (Bs := A) hA hpres h3 hnt hρi hρ hN hd hconn

theorem frameNumIs_frameConn_of_excPlusModel
    {τ : Tag} {N d : ℕ}
    (hτ : (τ = .E7 ∧ N = 63 ∧ d = 32) ∨ (τ = .E8 ∧ N = 120 ∧ d = 56)) {L' : Type} [Group L']
    [Finite L'] {A : Subgroup (MulAut L')} (hA : IsElemAbelian 3 A) (hsc : GGTorusSelfCent 3 A)
    (h : GGExcPlusWeylModel τ 3 A) :
    FrameNumIs (ggAutomizer (MulAut.conj : L' →* MulAut L').range A) N (some d) ∧
      FrameConn (ggAutomizer (MulAut.conj : L' →* MulAut L').range A) := by
  rcases hτ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · obtain ⟨w, hwN, hw, hrefl, e, he⟩ :=
      ggWTEx1_weylFrame_of_excPlusModel (τ := .E7) (p := 3)
        Nat.prime_three (by norm_num) hsc h
    let 𝒜 : Subgroup (MulAut ↥A) :=
      ggAutomizer (MulAut.conj : L' →* MulAut L').range A
    have hpres : GGCoxeterPres 3 𝒜
        (CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartan .E7)) e := by
      refine ⟨ggWTEx1_isWeylMatrix_E7, fun i => ?_⟩
      simpa only [he i] using hrefl i
    have h3 : ∀ i j : Fin 7, i ≠ j →
        (CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartan .E7)).M i j ≤ 3 := by
      rw [show CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartan .E7) = CoxeterMatrix.E₇
        from coxeterE7_eq.symm]
      intro i j _
      fin_cases i <;> fin_cases j <;> decide
    have hnt : ∀ φ ∈ 𝒜, ¬ GGIsTransvection 3 φ :=
      fun φ hφ => not_isTransvection_of_excPlusModel (Or.inl rfl) h φ hφ
    have hwhole := frameWhole_facts (n := 7) (N := 63) (d := 32)
      (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))
    exact frameExcPlus_frameNum_post (τ := .E7) (N := 63) (d := 32)
      (Or.inr (Or.inl rfl)) hA hpres h3 hnt hwhole.1 hwhole.2.1 hwhole.2.2
  · obtain ⟨w, hwN, hw, hrefl, e, he⟩ :=
      ggWTEx1_weylFrame_of_excPlusModel (τ := .E8) (p := 3)
        Nat.prime_three (by norm_num) hsc h
    let 𝒜 : Subgroup (MulAut ↥A) :=
      ggAutomizer (MulAut.conj : L' →* MulAut L').range A
    have hpres : GGCoxeterPres 3 𝒜
        (CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartan .E8)) e := by
      refine ⟨ggWTEx1_isWeylMatrix_E8, fun i => ?_⟩
      simpa only [he i] using hrefl i
    have h3 : ∀ i j : Fin 8, i ≠ j →
        (CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartan .E8)).M i j ≤ 3 := by
      rw [show CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartan .E8) = CoxeterMatrix.E₈
        from coxeterE8_eq.symm]
      intro i j _
      fin_cases i <;> fin_cases j <;> decide
    have hnt : ∀ φ ∈ 𝒜, ¬ GGIsTransvection 3 φ :=
      fun φ hφ => not_isTransvection_of_excPlusModel (Or.inr rfl) h φ hφ
    have hwhole := frameWhole_facts (n := 8) (N := 120) (d := 56)
      (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))
    exact frameExcPlus_frameNum_post (τ := .E8) (N := 120) (d := 56)
      (Or.inr (Or.inr rfl)) hA hpres h3 hnt hwhole.1 hwhole.2.1 hwhole.2.2

theorem largeEvenLabelAll_outdiagPrime_E7_E8
    {lab : LargeEvenLabel} (ht : lab.tag = .E7 ∨ lab.tag = .E8) (hn : lab.n = 1) :
    LargeEvenLabelAll lab fun R _ I _ => GGOutdiagPrime 3 R I := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht hn
  rcases ht with rfl | rfl
  · intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, i1, i2, hK, hq⟩ := hQ
    subst hn
    have hK2 : Nat.card K = 2 := by simpa using hK
    refine ⟨K, i1, i2, hK, hq, ?_⟩
    intro φ _ hφ
    exact ExcRootAs.ggOutdiagPrime_recipe_E7_E8 (τ := .E7) (Or.inl rfl) hK2 3
      φ (Set.mem_univ φ) hφ
  · intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, i1, i2, hK, hq⟩ := hQ
    subst hn
    have hK2 : Nat.card K = 2 := by simpa using hK
    refine ⟨K, i1, i2, hK, hq, ?_⟩
    intro φ _ hφ
    exact ExcRootAs.ggOutdiagPrime_recipe_E7_E8 (τ := .E8) (Or.inr rfl) hK2 3
      φ (Set.mem_univ φ) hφ

private theorem frameExcPlus_rowGe
    {τ : Tag} {N d k : ℕ}
    (hτ : (τ = .E7 ∧ N = 63 ∧ d = 32) ∨ (τ = .E8 ∧ N = 120 ∧ d = 56))
    {R : Type} [Group R] {I : Set (MulAut R)}
    (hM : GGExcPlusWeylModelSCr τ 3 k R I) (hO : GGOutdiagPrime 3 R I) :
    ∀ r : ℕ, k ≤ r → GGTorusReflGenW 3 r R I ∧
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
        GGTorusTBGroup 3 r R I L' ψ A →
          (FrameNumIs (ggAutomizer (MulAut.conj : L' →* MulAut L').range A) N (some d) ∧
            FrameConn (ggAutomizer (MulAut.conj : L' →* MulAut L').range A)) ∧
          ∃ S : Subgroup L', IsPGroup 3 S ∧ ¬ IsCyclic S := by
  intro r hr
  have hpowk : 3 ^ k ≤ 3 ^ r := Nat.pow_le_pow_right (by norm_num) hr
  constructor
  · intro L' _ _ ψ A hA
    have hAk : GGTorusTBGroup 3 k R I L' ψ A :=
      ggTorusTBGroup_of_pow_le hA (le_trans hpowk hA.2.2.2.2.2.1)
    exact (ggTorusReflGenW_of_excPlusModel Nat.prime_three (by norm_num) hM) L' ψ A hAk
  · intro L' _ _ ψ A hA
    have hAk : GGTorusTBGroup 3 k R I L' ψ A :=
      ggTorusTBGroup_of_pow_le hA (le_trans hpowk hA.2.2.2.2.2.1)
    refine ⟨frameNumIs_frameConn_of_excPlusModel hτ hA.2.2.2.1 hA.2.2.2.2.2.2.2
      (hM L' ψ A hAk), ?_⟩
    have hO' : ∀ φ ∈ I, φ ^ 3 = 1 →
        φ ∈ Set.range (MulAut.conj : R →* MulAut R) := by
      intro φ hφ hφ3
      exact MonoidHom.mem_range.mp (hO φ hφ hφ3)
    exact exists_noncyclic_three_of_forall_conj hA.2.2.2.1
      (le_trans (by norm_num) hA.2.2.2.2.2.2.1)
      (exists_mulAut_conj_of_mem hA.1 hA.2.1 hA.2.2.1 hO' hA.2.2.2.1 hA.2.2.2.2.1)

theorem frameTBBody_E7
    {lab : LargeEvenLabel} (ht : lab.tag = .E7) (hn : lab.n = 1) :
    LargeEvenLabelAll lab (frameTBBody lab) := by
  have hmodel := ggNEE_largeEvenLabelAll_model_excPlus (p := 3) Nat.prime_three (by norm_num)
    (lab := lab) (Or.inl ht) (by rw [hn]; norm_num)
  rw [show ggNEE_tagOf lab.tag = .E7 by simp [ggNEE_tagOf, ht],
    show ggNbrExcPlusRank lab.tag = 6 by simp [ggNbrExcPlusRank, ht]] at hmodel
  refine frameTBBody_of_rowGe (N := 63) (d := some 32)
    (by simp [frameLabNum, frameTagNum, ht]) ?_
  exact (LargeEvenLabelAll.and hmodel
    (largeEvenLabelAll_outdiagPrime_E7_E8 (Or.inl ht) hn)).mono
    fun R _ I _ ⟨hM, hO⟩ =>
      frameExcPlus_rowGe (Or.inl ⟨rfl, rfl, rfl⟩) (k := 6) hM hO

theorem frameTBBody_E8
    {lab : LargeEvenLabel} (ht : lab.tag = .E8) (hn : lab.n = 1) :
    LargeEvenLabelAll lab (frameTBBody lab) := by
  have hmodel := ggNEE_largeEvenLabelAll_model_excPlus (p := 3) Nat.prime_three (by norm_num)
    (lab := lab) (Or.inr ht) (by rw [hn]; norm_num)
  rw [show ggNEE_tagOf lab.tag = .E8 by simp [ggNEE_tagOf, ht],
    show ggNbrExcPlusRank lab.tag = 7 by simp [ggNbrExcPlusRank, ht]] at hmodel
  have hnum : frameLabNum lab = (120, some 56) := by simp [frameLabNum, frameTagNum, ht]
  exact (LargeEvenLabelAll.and hmodel (largeEvenLabelAll_outdiagPrime_E7_E8 (Or.inr ht) hn)).mono
    fun R _ I _ ⟨hM, hO⟩ r _ hg => by
      rw [hnum]
      exact frameExcPlus_rowGe (Or.inr ⟨rfl, rfl, rfl⟩) (k := 7) hM hO r (hg.2 ht)

end CFSG.StandardType.FrameRoute

end
