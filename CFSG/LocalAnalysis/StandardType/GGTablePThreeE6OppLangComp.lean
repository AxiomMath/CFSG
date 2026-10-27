module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6RatQS
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6RatDistinct
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TableT
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6FrobData
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6FrobAdd
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6RatTransfer
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TwoDefs
public import Certificates.Certificate707002
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6RatLabelA
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TwoRatLabelD
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6OppCoset
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6OppNegA5
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcActOuterCartan
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcActOuterPerfTwoDFourStable
public import CFSG.LieType.Chevalley.CLSOddToralOrdinaryComponentRootFactor
import CFSG.Quasithin.H13.NQTermLinearThreeTools
public import CFSG.Blueprint.LieModelAPI
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.PsuGoodAux.Descent
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.Defs
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.Layer
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.Models
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenAsm
public import CFSG.HardMathSupport.Solomon.Coordinator.LBIInput6_1Main
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTame.SuN
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcActOuterPerfTwoDRank
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdx
public import CFSG.LocalAnalysis.GLTheoremA.P51.Quaternion
public import CFSG.LocalAnalysis.GLTheoremA.P55.Dihedral
public import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma106107
public import CFSG.LocalAnalysis.GLTheoremA.S3.Lemma35
public import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma62Aux
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TableTStatic
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TableTTransport
public import CFSG.Models.Transport
public import CFSG.Quasithin.Vol2.Ch11SecBK10A

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private theorem e6Opp_lang_firstHalf
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] (S : LangSetup Tag.E6 L 3)
    {a : Fin Tag.E6.rank → Lˣ} (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus)
    (hap : ∀ j, a j ^ 3 = 1) (h1 : rootDiagUnit Tag.E6 a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (huniq : ∀ i' : KernelComponent (rootCharHom a),
      CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i') →
        rationalComponent S.ρ S.Γ (rootCharHom a) i' =
          rationalComponent S.ρ S.Γ (rootCharHom a) i) :
    ((3 : ℕ) : L) ≠ 0 ∧
    rootDiagUnit Tag.E6 a ^ 3 = 1 ∧
    CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ∧
    ∃ (ω : L) (v : Fin Tag.E6.rank → ZMod 3),
      IsPrimitiveRoot ω 3 ∧
      (∀ j, ((a j : Lˣ) : L) = ω ^ (v j).val) ∧
      v ≠ 0 ∧
      kernelRoots (rootCharHom a) = kernelRoots (e6Chi v) ∧
      (∀ Ψ' : Set (Fin Tag.E6.rank → ℤ), E6KerComponent v Ψ' →
        ∃ kk : ℕ, (S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[kk] ''
          componentRoots (rootCharHom a) i = Ψ') ∧
      ((compRank (componentRoots (rootCharHom a) i) = 5 ∧
          (componentRoots (rootCharHom a) i).ncard = 40 ∧
          componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1) ∨
        (compRank (componentRoots (rootCharHom a) i) = 5 ∧
          (componentRoots (rootCharHom a) i).ncard = 30 ∧
          componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1) ∨
        (compRank (componentRoots (rootCharHom a) i) = 4 ∧
          (componentRoots (rootCharHom a) i).ncard = 24 ∧
          componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1) ∨
        (compRank (componentRoots (rootCharHom a) i) = 2 ∧
          (componentRoots (rootCharHom a) i).ncard = 6 ∧
          componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 3 ∧
          ((((S.D.q : ℕ) : ZMod 3) = 1 → twistInner (componentRoots (rootCharHom a) i)
              ((S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[3])) ∧
            (((S.D.q : ℕ) : ZMod 3) = 2 → ¬ twistInner (componentRoots (rootCharHom a) i)
              ((S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[3]))))) := by
  classical
  have h3ne : ((3 : ℕ) : L) ≠ 0 := by
    have h2 : ((2 : ℕ) : L) = 0 := CharP.cast_eq_zero L 2
    have h3 : ((3 : ℕ) : L) = 1 := by
      have hcast : ((3 : ℕ) : L) = ((2 : ℕ) : L) + 1 := by norm_num
      rw [hcast, h2, zero_add]
    rw [h3]; exact one_ne_zero
  obtain ⟨ω, hω⟩ :=
    CFSG.Quasithin.H13.NQTerm.exists_isPrimitiveRoot_of_isAlgClosed (n := 3) (by norm_num) h3ne
  have ha3 : ∀ j, ((a j : L)) ^ 3 = 1 := fun j => by
    rw [← Units.val_pow_eq_pow_val, hap j, Units.val_one]
  choose k hklt hk using fun j => hω.eq_pow_of_pow_eq_one (ha3 j)
  let v : Fin Tag.E6.rank → ZMod 3 := fun j => (k j : ZMod 3)
  have hv : ∀ j, ((a j : Lˣ) : L) = ω ^ (v j).val := by
    intro j
    rw [ZMod.val_natCast_of_lt (hklt j)]
    exact (hk j).symm
  have hvne : v ≠ 0 := by
    intro hv0
    apply h1
    have ha1 : a = 1 := by
      funext j
      apply Units.ext
      have h : ((a j : Lˣ) : L) = 1 := by
        have hj := hv j
        rw [hv0] at hj
        simpa using hj
      simpa using h
    rw [ha1, rootDiagUnit_one]
  have hTp : rootDiagUnit Tag.E6 a ^ 3 = 1 := by
    rw [rootDiagUnit_pow]
    rw [show a ^ 3 = 1 from funext fun j => hap j, rootDiagUnit_one]
  have hQSi : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
    e6_rationalComponent_quasisimple S hT hap h1 i
  have horbit : ∀ i' : KernelComponent (rootCharHom a),
      ∃ kk : ℕ, (S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[kk] ''
        componentRoots (rootCharHom a) i = componentRoots (rootCharHom a) i' := by
    intro i'
    by_contra hno
    have hno' : ∀ kk : ℕ, (S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[kk] ''
        componentRoots (rootCharHom a) i ≠ componentRoots (rootCharHom a) i' := by
      intro kk hk
      exact hno ⟨kk, hk⟩
    exact (rationalComponent_ne_of_not_orbit S hT i i' hno' hQSi)
      ((huniq i' (e6_rationalComponent_quasisimple S hT hap h1 i')).symm)
  have hker' : kernelRoots (e6Chi v) =
      {γ | IsRoot Tag.E6 γ ∧ ∑ k, ((γ k : ℤ) : ZMod 3) * v k = 0} := by
    ext γ
    have hchi : (e6Chi v) (Multiplicative.ofAdd γ) =
        Multiplicative.ofAdd (∑ k, ((γ k : ℤ) : ZMod 3) * v k) := rfl
    simp only [kernelRoots, Set.mem_setOf_eq, hchi, ofAdd_eq_one]
  have hker : kernelRoots (rootCharHom a) = kernelRoots (e6Chi v) := by
    rw [(frobRootMap_e6_admissible S hT ω hω v hv).2, ← hker']
  have horbitE : ∀ Ψ' : Set (Fin Tag.E6.rank → ℤ), E6KerComponent v Ψ' →
      ∃ kk : ℕ, (S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[kk] ''
        componentRoots (rootCharHom a) i = Ψ' := by
    intro Ψ' hΨ'
    obtain ⟨i', rfl⟩ := hΨ'
    obtain ⟨i'', hi''⟩ : ∃ i'' : KernelComponent (rootCharHom a),
        componentRoots (rootCharHom a) i'' = componentRoots (e6Chi v) i' := by
      obtain ⟨x, rfl⟩ := Quotient.exists_rep i'
      exact ⟨⟦⟨x.1, hker.ge x.2⟩⟧,
        CFSG.LieType.Chevalley.OddToralOrdinary.componentRoots_eq_of_kernelRoots_eq
          hker (hker.ge x.2) x.2⟩
    obtain ⟨kk, hkk⟩ := horbit i''
    exact ⟨kk, hkk.trans hi''⟩
  have hTres := e6TableT_sound S.ρ v ((S.D.q : ℕ) : ZMod 3)
    (frobRootMap_map_add S.D S.frob) (fun γ hγ => (S.frob.isRoot_iff γ).2 hγ)
    (frobRootMap_e6_admissible S hT ω hω v hv).1 hvne
    (componentRoots (rootCharHom a) i) (e6_kerComponent_of_component hω v hv i) horbitE
  exact ⟨h3ne, hTp, hQSi, ω, v, hω, hv, hvne, hker, horbitE, hTres⟩

theorem e6Opp_lang_rationalComponents_untw
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] (S : LangSetup Tag.E6 L 3)
    (hr : ((S.D.q : ℕ) : ZMod 3) = 2) (hW : E6CosetW S.ρ)
    {a : Fin Tag.E6.rank → Lˣ} (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus)
    (hap : ∀ j, a j ^ 3 = 1) (h1 : rootDiagUnit Tag.E6 a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (huniq : ∀ i' : KernelComponent (rootCharHom a),
      CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i') →
        rationalComponent S.ρ S.Γ (rootCharHom a) i' =
          rationalComponent S.ρ S.Γ (rootCharHom a) i) :
    ∃ lab : LargeEvenLabel, RationalLabelIs S i lab ∧ 2 ^ lab.n = S.D.q ∧
      ((lab.tag = .A ∧ lab.rank = 5) ∨ (lab.tag = .twD ∧ lab.rank = 4)) := by
  classical
  obtain ⟨_, _, hQSi, ω, v, hω, hv, hvne, _, horbitE, hTres⟩ :=
    e6Opp_lang_firstHalf S hT hap h1 i huniq
  have hadm : E6Admissible (fun i => S.ρ (Pi.single i 1)) v 2 := by
    have h := (frobRootMap_e6_admissible S hT ω hω v hv).1
    rwa [hr] at h
  have hΨ : E6KerComponent v (componentRoots (rootCharHom a) i) :=
    e6_kerComponent_of_component hω v hv i
  have hsolv : ¬ E6SolvTwo S.ρ (componentRoots (rootCharHom a) i) := by
    rintro (⟨hr1, ho1⟩ | ⟨hr2, hn6, ho1, -⟩)
    · rcases hTres with ⟨h5, -, -⟩ | ⟨h5, -, -⟩ | ⟨h4, -, -⟩ | ⟨h2, -, -, -⟩ <;> omega
    · rcases hTres with ⟨h5, -, -⟩ | ⟨h5, -, -⟩ | ⟨h4, -, -⟩ | ⟨h2, hn, ho3, -⟩ <;> omega
  have hout : ∀ Ψ' : Set (Fin Tag.E6.rank → ℤ), E6KerComponent v Ψ' →
      (∀ k : ℕ, (S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[k] ''
        componentRoots (rootCharHom a) i ≠ Ψ') → E6SolvTwo S.ρ Ψ' := by
    intro Ψ' hΨ' hno
    obtain ⟨kk, hkk⟩ := horbitE Ψ' hΨ'
    exact absurd hkk (hno kk)
  have hrow : E6RowTwoW S.ρ (componentRoots (rootCharHom a) i) :=
    (Certificates.certificate707002 S.ρ v (frobRootMap_map_add S.D S.frob)
      (fun γ hγ => (S.frob.isRoot_iff γ).2 hγ) hadm hvne
      (componentRoots (rootCharHom a) i) hΨ hsolv hout).1 hW
  rcases hrow with ⟨hr5, hn30, horb1, htw⟩ | ⟨hr4, hn24, horb1, hout', hsq⟩ |
    ⟨hr2, hn6, horb2, htw2⟩
  ·
    have hA : 1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
        (componentRoots (rootCharHom a) i).ncard =
          compRank (componentRoots (rootCharHom a) i) *
            (compRank (componentRoots (rootCharHom a) i) + 1) := by
      rw [hr5, hn30]; norm_num
    obtain ⟨lab, hdeg, hrank, htagInner, -, hRL⟩ :=
      rationalLabel_typeA S Nat.prime_three hT hap h1 i hA hQSi
    have hkind : twistKind S.ρ (rootCharHom a) i = .inner := by
      unfold twistKind
      rw [if_pos ?_]
      rwa [horb1, Function.iterate_one]
    have htag : lab.tag = .A := htagInner hkind
    have hrank' : lab.rank = 5 := by rw [hrank, hr5]
    have hdeg' : 2 ^ lab.n = S.D.q := by rw [hdeg, horb1, pow_one]
    exact ⟨lab, hRL, hdeg', Or.inl ⟨htag, hrank'⟩⟩
  ·
    have hshape : compRank (componentRoots (rootCharHom a) i) = 4 ∧
        (componentRoots (rootCharHom a) i).ncard = 24 := ⟨hr4, hn24⟩
    have hout'' : ¬ twistInner (componentRoots (rootCharHom a) i)
        ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength S.ρ
          (componentRoots (rootCharHom a) i)]) := by
      rwa [horb1, Function.iterate_one]
    have hsq' : twistInner (componentRoots (rootCharHom a) i)
        ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[2 * componentOrbitLength S.ρ
          (componentRoots (rootCharHom a) i)]) := by
      simpa [horb1] using hsq
    obtain ⟨lab, hdeg, htag, hrank, hRL⟩ :=
      rationalLabel_outerD_four_sq S Nat.prime_three hT hap h1 i hshape hout'' hsq' hQSi
    have hdeg' : 2 ^ lab.n = S.D.q := by rw [hdeg, horb1, pow_one]
    exact ⟨lab, hRL, hdeg', Or.inr ⟨htag, hrank⟩⟩
  ·
    exfalso
    rcases hTres with ⟨h5, -, -⟩ | ⟨h5, -, -⟩ | ⟨h4, -, -⟩ | ⟨h2, -, ho3, -⟩ <;> omega

private def e6NegTrans (σ : Equiv.Perm (Fin Tag.E6.rank → ℤ)) :
    Equiv.Perm (Fin Tag.E6.rank → ℤ) :=
  σ.trans (Equiv.neg _)

private theorem e6NegTrans_apply (σ : Equiv.Perm (Fin Tag.E6.rank → ℤ))
    (x : Fin Tag.E6.rank → ℤ) : e6NegTrans σ x = -σ x := by
  simp only [e6NegTrans, Equiv.trans_apply, Equiv.neg_apply]

private theorem e6NegTrans_add (σ : Equiv.Perm (Fin Tag.E6.rank → ℤ))
    (hadd : ∀ x y, σ (x + y) = σ x + σ y) (x y : Fin Tag.E6.rank → ℤ) :
    e6NegTrans σ (x + y) = e6NegTrans σ x + e6NegTrans σ y := by
  rw [e6NegTrans_apply, hadd, e6NegTrans_apply, e6NegTrans_apply, neg_add]

private theorem e6NegTrans_image_eq (σ : Equiv.Perm (Fin Tag.E6.rank → ℤ))
    (hneg : ∀ x, σ (-x) = -σ x) {Q : Set (Fin Tag.E6.rank → ℤ)}
    (hQ : ∀ x ∈ Q, -x ∈ Q) :
    (e6NegTrans σ : (Fin Tag.E6.rank → ℤ) → _) '' Q = σ '' Q := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨-x, hQ x hx, by rw [e6NegTrans_apply, hneg]⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨-x, hQ x hx, ?_⟩
    rw [e6NegTrans_apply, hneg, neg_neg]

private theorem e6NegTrans_iterate_neg (σ : Equiv.Perm (Fin Tag.E6.rank → ℤ))
    (hneg : ∀ x, σ (-x) = -σ x) (k : ℕ) (x : Fin Tag.E6.rank → ℤ) :
    ((σ : (Fin Tag.E6.rank → ℤ) → _)^[k]) (-x) = -((σ : _ → _)^[k]) x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, hneg]

private theorem e6NegTrans_image_iterate (σ : Equiv.Perm (Fin Tag.E6.rank → ℤ))
    (hneg : ∀ x, σ (-x) = -σ x) {Ψ : Set (Fin Tag.E6.rank → ℤ)}
    (hΨ : ∀ γ ∈ Ψ, -γ ∈ Ψ) (k : ℕ) :
    ((e6NegTrans σ : _ → _)^[k]) '' Ψ = ((σ : _ → _)^[k]) '' Ψ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hL : ((e6NegTrans σ : _ → _)^[k.succ]) '' Ψ =
        (e6NegTrans σ) '' ((e6NegTrans σ)^[k] '' Ψ) := by
      rw [Function.iterate_succ', Set.image_comp]
    have hR : ((σ : _ → _)^[k.succ]) '' Ψ = σ '' ((σ^[k]) '' Ψ) := by
      rw [Function.iterate_succ', Set.image_comp]
    rw [hL, hR, ih]
    refine e6NegTrans_image_eq σ hneg ?_
    intro x hx
    obtain ⟨γ, hγ, rfl⟩ := hx
    exact ⟨-γ, hΨ γ hγ, e6NegTrans_iterate_neg σ hneg k γ⟩

private theorem e6NegTrans_componentOrbitLength (σ : Equiv.Perm (Fin Tag.E6.rank → ℤ))
    (hneg : ∀ x, σ (-x) = -σ x) {Ψ : Set (Fin Tag.E6.rank → ℤ)}
    (hΨ : ∀ γ ∈ Ψ, -γ ∈ Ψ) :
    componentOrbitLength (e6NegTrans σ) Ψ = componentOrbitLength σ Ψ := by
  unfold componentOrbitLength
  congr 1
  ext k
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨hpos, h⟩
    exact ⟨hpos, by rw [← e6NegTrans_image_iterate σ hneg hΨ k]; exact h⟩
  · rintro ⟨hpos, h⟩
    exact ⟨hpos, by rw [e6NegTrans_image_iterate σ hneg hΨ k]; exact h⟩

private theorem e6NegTrans_iterate_two (σ : Equiv.Perm (Fin Tag.E6.rank → ℤ))
    (hneg : ∀ x, σ (-x) = -σ x) (x : Fin Tag.E6.rank → ℤ) :
    ((e6NegTrans σ : _ → _)^[2]) x = ((σ : _ → _)^[2]) x := by
  change (e6NegTrans σ) ((e6NegTrans σ) x) = σ (σ x)
  simp only [e6NegTrans_apply, hneg, neg_neg]

theorem e6Opp_lang_rationalComponents_tw
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] (S : LangSetup Tag.E6 L 3)
    (hr : ((S.D.q : ℕ) : ZMod 3) = 1)
    (hneg : ∃ u : WeylGroup Tag.E6, ∀ γ, IsRoot Tag.E6 γ → S.ρ γ = -(u • γ))
    {a : Fin Tag.E6.rank → Lˣ} (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus)
    (hap : ∀ j, a j ^ 3 = 1) (h1 : rootDiagUnit Tag.E6 a ≠ 1) (i : KernelComponent (rootCharHom a))
    (huniq : ∀ i' : KernelComponent (rootCharHom a),
      CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i') →
        rationalComponent S.ρ S.Γ (rootCharHom a) i' =
          rationalComponent S.ρ S.Γ (rootCharHom a) i) :
    ∃ lab : LargeEvenLabel, RationalLabelIs S i lab ∧ 2 ^ lab.n = S.D.q ∧
      ((lab.tag = .twA ∧ lab.rank = 5) ∨ (lab.tag = .twD ∧ lab.rank = 4)) := by
  classical
  obtain ⟨h3ne, _, hQSi, ω, v, hω, hv, hvne, _, horbitE, hTres⟩ :=
    e6Opp_lang_firstHalf S hT hap h1 i huniq
  obtain ⟨u, hu⟩ := hneg
  let ρ' : Equiv.Perm (Fin Tag.E6.rank → ℤ) := e6NegTrans S.ρ
  have hρ'apply : ∀ x : Fin Tag.E6.rank → ℤ, ρ' x = -S.ρ x :=
    fun x => e6NegTrans_apply S.ρ x
  have hρ'add : ∀ x y, ρ' (x + y) = ρ' x + ρ' y :=
    fun x y => e6NegTrans_add S.ρ (frobRootMap_map_add S.D S.frob) x y
  have hρ'neg : ∀ x : Fin Tag.E6.rank → ℤ, S.ρ (-x) = -S.ρ x := S.frob.neg_eq
  have hΨneg : ∀ γ ∈ componentRoots (rootCharHom a) i,
      -γ ∈ componentRoots (rootCharHom a) i :=
    fun γ hγ => CFSG.ComponentClassification.ExcSelector.neg_mem_componentRoots hγ
  have hW' : E6CosetW ρ' := by
    refine e6CosetW_of_eq_smul (ρ := ρ') (u := u) hρ'add ?_
    intro γ hγ
    rw [hρ'apply γ, hu γ hγ, neg_neg]
  have hadm' : E6Admissible (fun j => ρ' (Pi.single j 1)) v 2 := by
    have hS : E6Admissible (fun j => S.ρ (Pi.single j 1)) v 1 := by
      have h := (frobRootMap_e6_admissible S hT ω hω v hv).1
      rwa [hr] at h
    have hneg1 : ((-1 : ZMod 3) = 2) := by decide
    have h := e6Admissible_neg hS
    have h' : E6Admissible (fun j => -S.ρ (Pi.single j 1)) v 2 := by
      rw [← hneg1]
      exact h
    simpa only [hρ'apply] using h'
  have horbLen : componentOrbitLength ρ' (componentRoots (rootCharHom a) i) =
      componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) :=
    e6NegTrans_componentOrbitLength S.ρ hρ'neg hΨneg
  have hImg : ∀ k : ℕ, (ρ' : _ → _)^[k] '' componentRoots (rootCharHom a) i =
      (S.ρ : _ → _)^[k] '' componentRoots (rootCharHom a) i :=
    fun k => e6NegTrans_image_iterate S.ρ hρ'neg hΨneg k
  have hsolv : ¬ E6SolvTwo ρ' (componentRoots (rootCharHom a) i) := by
    rintro (⟨hr1, ho1⟩ | ⟨hr2, hn6, ho1, -⟩)
    · rw [horbLen] at ho1
      rcases hTres with ⟨h5, -, -⟩ | ⟨h5, -, -⟩ | ⟨h4, -, -⟩ | ⟨h2, -, ho3, -⟩ <;> omega
    · rw [horbLen] at ho1
      rcases hTres with ⟨h5, -, -⟩ | ⟨h5, -, -⟩ | ⟨h4, -, -⟩ | ⟨h2, hn, ho3, -⟩ <;> omega
  have hout : ∀ Ψ' : Set (Fin Tag.E6.rank → ℤ), E6KerComponent v Ψ' →
      (∀ k : ℕ, (ρ' : _ → _)^[k] '' componentRoots (rootCharHom a) i ≠ Ψ') →
      E6SolvTwo ρ' Ψ' := by
    intro Ψ' hΨ' hno
    obtain ⟨kk, hkk⟩ := horbitE Ψ' hΨ'
    exact absurd ((hImg kk).trans hkk) (hno kk)
  have hkercomp : E6KerComponent v (componentRoots (rootCharHom a) i) :=
    e6_kerComponent_of_component hω v hv i
  have hrow : E6RowTwoW ρ' (componentRoots (rootCharHom a) i) :=
    (Certificates.certificate707002 ρ' v hρ'add (fun γ hγ => by
        rw [hρ'apply γ]
        exact IsRoot.neg ((S.frob.isRoot_iff γ).2 hγ)) hadm' hvne
      (componentRoots (rootCharHom a) i) hkercomp hsolv hout).1 hW'
  rcases hrow with ⟨hr5, hn30, horb1, htw⟩ | ⟨hr4, hn24, horb1, hout', hsq⟩ |
    ⟨hr2, hn6, horb2, htw2⟩
  ·
    have horbLenS : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1 := by
      rw [← horbLen]; exact horb1
    have hnotS : ¬ twistInner (componentRoots (rootCharHom a) i) (S.ρ : _ → _) := by
      obtain ⟨w, hw, hwγ⟩ := htw
      refine CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSConn.not_twistInner_of_neg
        hw (fun γ hγ => ?_) (not_exists_neg_of_e6Class_A5 h3ne hap i hn30)
      have h1' : -S.ρ γ = w • γ := by
        simpa only [hρ'apply] using hwγ γ hγ
      simpa using congrArg Neg.neg h1'
    have hr5r : compRank (componentRoots (rootCharHom a) i) = 5 := hr5
    have hn30r : (componentRoots (rootCharHom a) i).ncard = 30 := hn30
    have hkind : twistKind S.ρ (rootCharHom a) i = .suN := by
      have hnotInner : ¬ twistInner (componentRoots (rootCharHom a) i)
          ((S.ρ : _ → _)^[componentOrbitLength S.ρ
            (componentRoots (rootCharHom a) i)]) := by
        rw [horbLenS, Function.iterate_one]
        exact hnotS
      have hnotExc : ¬ ((compRank (componentRoots (rootCharHom a) i) = 6 ∧
          (componentRoots (rootCharHom a) i).ncard = 72) ∨
          (compRank (componentRoots (rootCharHom a) i) = 4 ∧
            (componentRoots (rootCharHom a) i).ncard = 24 ∧
            ¬ twistInner (componentRoots (rootCharHom a) i)
              ((S.ρ : _ → _)^[2 * componentOrbitLength S.ρ
                (componentRoots (rootCharHom a) i)]))) := by
        rintro (⟨h6, -⟩ | ⟨h4, -, -⟩)
        · rw [hr5r] at h6; omega
        · rw [hr5r] at h4; omega
      have hnotTwoD : ¬ (4 ≤ compRank (componentRoots (rootCharHom a) i) ∧
          (componentRoots (rootCharHom a) i).ncard =
            2 * compRank (componentRoots (rootCharHom a) i) *
              (compRank (componentRoots (rootCharHom a) i) - 1)) := by
        rintro ⟨-, hcard⟩
        rw [hr5r, hn30r] at hcard
        omega
      have hsuN : 2 ≤ compRank (componentRoots (rootCharHom a) i) ∧
          (componentRoots (rootCharHom a) i).ncard =
            compRank (componentRoots (rootCharHom a) i) *
              (compRank (componentRoots (rootCharHom a) i) + 1) := by
        rw [hr5r, hn30r]; norm_num
      unfold twistKind
      rw [if_neg hnotInner, if_neg hnotExc, if_neg hnotTwoD, if_pos hsuN]
    have hA : 1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
        (componentRoots (rootCharHom a) i).ncard =
          compRank (componentRoots (rootCharHom a) i) *
            (compRank (componentRoots (rootCharHom a) i) + 1) := by
      rw [hr5r, hn30r]; norm_num
    obtain ⟨lab, hdeg, hrank, -, htagSuN, hRL⟩ :=
      rationalLabel_typeA S Nat.prime_three hT hap h1 i hA hQSi
    have htag : lab.tag = .twA := htagSuN hkind
    have hrank' : lab.rank = 5 := by rw [hrank, hr5r]
    have hdeg' : 2 ^ lab.n = S.D.q := by rw [hdeg, horbLenS, pow_one]
    exact ⟨lab, hRL, hdeg', Or.inl ⟨htag, hrank'⟩⟩
  ·
    have horbLenS : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1 := by
      rw [← horbLen]; exact horb1
    have hΨcomp : IsRootComponent (componentRoots (rootCharHom a) i) :=
      isRootComponent_componentRoots i
    have himg : (ρ' : _ → _) '' componentRoots (rootCharHom a) i =
        componentRoots (rootCharHom a) i := by
      have hne : {s : ℕ | 0 < s ∧ (ρ' : _ → _)^[s] '' componentRoots (rootCharHom a) i =
          componentRoots (rootCharHom a) i}.Nonempty := by
        by_contra h'
        rw [Set.not_nonempty_iff_eq_empty] at h'
        have hzero : componentOrbitLength ρ' (componentRoots (rootCharHom a) i) = 0 := by
          unfold componentOrbitLength
          rw [h', Nat.sInf_empty]
        omega
      have hmem : (1 : ℕ) ∈ {s : ℕ | 0 < s ∧
          (ρ' : _ → _)^[s] '' componentRoots (rootCharHom a) i =
            componentRoots (rootCharHom a) i} := by
        rw [← horb1]
        exact Nat.sInf_mem hne
      simpa only [Function.iterate_one] using hmem.2
    have hbij : Set.BijOn (ρ' : _ → _) (componentRoots (rootCharHom a) i)
        (componentRoots (rootCharHom a) i) := by
      refine ⟨?_, Set.injOn_of_injective ρ'.injective, ?_⟩
      · intro x hx
        rw [← himg]
        exact Set.mem_image_of_mem ρ' hx
      · intro y hy
        rw [← himg] at hy
        exact hy
    have hform : ∀ γ ∈ componentRoots (rootCharHom a) i,
        ∀ δ ∈ componentRoots (rootCharHom a) i,
        CFSG.LieType.Steinberg.Adjoint.iform (ρ' γ) (ρ' δ) =
          CFSG.LieType.Steinberg.Adjoint.iform γ δ := by
      intro γ _ δ _
      rw [hρ'apply γ, hρ'apply δ, iform_neg_left, iform_neg_right, neg_neg]
      exact S.frob.iform_eq γ δ
    have hnegρ' : ∀ γ ∈ componentRoots (rootCharHom a) i, ρ' (-γ) = -ρ' γ := by
      intro γ _
      rw [hρ'apply (-γ), hρ'apply γ, S.frob.neg_eq, neg_neg]
    have hw₀exists : ∃ w ∈ componentWeylGroup (componentRoots (rootCharHom a) i),
        ∀ γ ∈ componentRoots (rootCharHom a) i, w • γ = -γ := by
      have h4le : 4 ≤ compRank (componentRoots (rootCharHom a) i) := by omega
      have hcard' : (componentRoots (rootCharHom a) i).ncard =
          2 * compRank (componentRoots (rootCharHom a) i) *
            (compRank (componentRoots (rootCharHom a) i) - 1) := by
        rw [hn24, hr4]
      obtain ⟨r, -, e, he⟩ :=
        CFSG.LocalAnalysis.GLTheoremA.T171Sh.exists_cartanD_of_nonInner hΨcomp
          (ρ' : _ → _) hbij hform hnegρ' hout' h4le hcard'
      have hcardΔ : (simpleRoots (componentRoots (rootCharHom a) i)).card = r := by
        rw [← Fintype.card_coe, Fintype.card_congr e, Fintype.card_fin]
      have hr4' : r = 4 := by
        have hcomp := CFSG.HardMathSupport.Timmesfeld.RootAut.compRank_eq_card hΨcomp
        omega
      subst hr4'
      exact CFSG.LocalAnalysis.GLTheoremA.T171Sh.exists_neg_mem_of_cartanD hΨcomp e he
    obtain ⟨w₀, hw₀, hw₀γ⟩ := hw₀exists
    have hnotS : ¬ twistInner (componentRoots (rootCharHom a) i) (S.ρ : _ → _) := by
      rintro ⟨w, hw, hwγ⟩
      apply hout'
      refine ⟨w * w₀,
        mul_mem hw (CFSG.HardMathSupport.Timmesfeld.RootAut.componentWeylGroup_le _ hw₀),
        fun γ hγ => ?_⟩
      rw [hρ'apply γ, hwγ γ hγ, mul_smul, hw₀γ γ hγ, smul_neg]
    have hρ'2 : (ρ' : _ → _)^[2] = (S.ρ : _ → _)^[2] :=
      funext fun x => e6NegTrans_iterate_two S.ρ hρ'neg x
    have hsqS : twistInner (componentRoots (rootCharHom a) i) ((S.ρ : _ → _)^[2]) :=
      hρ'2 ▸ hsq
    have hout'' : ¬ twistInner (componentRoots (rootCharHom a) i)
        ((S.ρ : _ → _)^[componentOrbitLength S.ρ
          (componentRoots (rootCharHom a) i)]) := by
      rw [horbLenS, Function.iterate_one]
      exact hnotS
    have hsq' : twistInner (componentRoots (rootCharHom a) i)
        ((S.ρ : _ → _)^[2 * componentOrbitLength S.ρ
          (componentRoots (rootCharHom a) i)]) := by
      rw [horbLenS, mul_one]
      exact hsqS
    have hshape : compRank (componentRoots (rootCharHom a) i) = 4 ∧
        (componentRoots (rootCharHom a) i).ncard = 24 := ⟨hr4, hn24⟩
    obtain ⟨lab, hdeg, htag, hrank, hRL⟩ :=
      rationalLabel_outerD_four_sq S Nat.prime_three hT hap h1 i hshape hout'' hsq' hQSi
    have hdeg' : 2 ^ lab.n = S.D.q := by rw [hdeg, horbLenS, pow_one]
    exact ⟨lab, hRL, hdeg', Or.inr ⟨htag, hrank⟩⟩
  ·
    exfalso
    rw [horbLen] at horb2
    rcases hTres with ⟨h5, -, -⟩ | ⟨h5, -, -⟩ | ⟨h4, -, -⟩ | ⟨h2, -, ho3, -⟩ <;> omega

end CFSG.StandardType.TablePThreeKG

end
