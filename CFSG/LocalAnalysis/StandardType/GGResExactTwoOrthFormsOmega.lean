module

public import CFSG.LocalAnalysis.StandardType.GGResExactTwoOrthSmallDefs
import CFSG.LocalAnalysis.StandardType.GGTBJOmBlockZ
import CFSG.LocalAnalysis.GLTheoremA.CatA.T173UniGen
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentFrame
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentTypeSum
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogQuadraticNormalForms
import CFSG.HardMathSupport.Dickson.Bal207.LocalBalClassicalOrthTwoBasic
import CFSG.RankThree.PartOne.KC.OrthogonalFixedDerived
import CFSG.LocalAnalysis.ComponentInitial.EscapingNotAlternating
import CFSG.LocalAnalysis.ComponentInitial.LocalComponents
import CFSG.HardMathSupport.Dickson.Bal207.OrthInnerFixed
import CFSG.LocalAnalysis.StandardType.GGResExactTwoOrthFixOmega
import CFSG.LocalAnalysis.StandardType.GGResExactTwoOrthU42
import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalResU3ThreeSolv
import CFSG.HardMathSupport.Dickson.Bal207.OrthD4Loc
import CFSG.Holt.Fixed
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentExcl
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentLayer
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBaseIso
import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma106107
import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs16
import CFSG.LocalAnalysis.GLTheoremA.S11.InputsCE
import CFSG.LocalAnalysis.GLTheoremA.S11.InputsElim
import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
import CFSG.RankThree.PartOne.FOC.CompCommutator
import CFSG.RankThree.PartOne.S15K.FixedWitt
import CFSG.RankThree.PartOne.S15K.LayerModel

public section

namespace CFSG.StandardType

open CFSG.Assembly
open CFSG.RankThree.Classical2 (orthDerived)
open Module Multiplicative Polynomial QuadraticMap
open SpCoord NbrOrth CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.LocalAnalysis.GLTheoremA.S172C.Cent CFSG.LocalAnalysis.GLTheoremA.T173U
open CFSG.GroupTheory.WeirSylow

namespace OrthTorus

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ}

private theorem ggResX2Forms_finrank_eq_two_mul (hK : Nat.card K = 2)
    (hQ : (polarBilin Q).Nondegenerate) (Δ : TBJOmData Q 3 A r) (hA : A ≤ orthDerived Q)
    (hchar : OrdPNsOm.charSum Q ⊤ ≡ 1 [ZMOD 3]) : Module.finrank K V = 2 * r := by
  have hU := ggResX2FixAux_isPlaneSystem (by norm_num) Δ hQ hA (by simp [hK])
  have hbot : polarPerp Q (⨆ j, Δ.F.U j) = ⊥ := by
    refine le_antisymm (fun v hv => ?_) bot_le
    refine Δ.noFixed hchar v (fun a ha => ?_)
    have ha' : a ∈ Δ.τ.range := by rwa [Δ.τ_range]
    obtain ⟨g, rfl⟩ := ha'
    exact mem_fixedSpace.mp ((Δ.mem_fixedSpace_iff g v).mpr fun j _ u hu =>
      mem_polarPerp_iff.mp hv u (le_iSup (fun j => Δ.F.U j) j hu))
  have h1 : Module.finrank K ↥(⨆ j, Δ.F.U j) = 2 * r :=
    finrank_iSup_eq_of_isPlaneSystem hU
  have h2 := finrank_polarPerp (Q := Q) hQ (⨆ j, Δ.F.U j)
  rw [hbot, finrank_bot] at h2
  have h3 : Module.finrank K ↥(⨆ j, Δ.F.U j) ≤ Module.finrank K V := Submodule.finrank_le _
  omega

private theorem ggResX2Forms_finrank_fixedSpace (hK : Nat.card K = 2)
    (hQ : (polarBilin Q).Nondegenerate) (Δ : TBJOmData Q 3 A r) (hA : A ≤ orthDerived Q)
    (hchar : OrdPNsOm.charSum Q ⊤ ≡ 1 [ZMOD 3]) (f₀ : Fin r → Multiplicative (ZMod 3)) :
    Module.finrank K (fixedSpace (Δ.τ f₀)) =
      2 * Nat.card {i : Fin r // toAdd (f₀ i) = 0} := by
  classical
  have hU := ggResX2FixAux_isPlaneSystem (by norm_num) Δ hQ hA (by simp [hK])
  have hdimV := ggResX2Forms_finrank_eq_two_mul hK hQ Δ hA hchar
  set S : Finset (Fin r) := Finset.univ.filter (fun i => toAdd (f₀ i) ≠ 0) with hS
  have hSW : (⨆ j ∈ S, Δ.F.U j) ≤ polarPerp Q (fixedSpace (Δ.τ f₀)) :=
    iSup₂_le fun j hj u hu => mem_polarPerp_iff.2 fun v hv => by
      rw [polar_comm]
      exact (Δ.mem_fixedSpace_iff f₀ v).mp hv j (Finset.mem_filter.mp hj).2 u hu
  have hfix : fixedSpace (Δ.τ f₀) = polarPerp Q (⨆ j ∈ S, Δ.F.U j) := by
    refine le_antisymm (fun v hv => ?_) (fun v hv => ?_)
    · refine mem_polarPerp_iff.2 fun u hu => ?_
      rw [polar_comm]
      exact mem_polarPerp_iff.1 (hSW hu) v hv
    · refine (Δ.mem_fixedSpace_iff f₀ v).mpr fun j hj u hu => ?_
      have hjS : j ∈ S := by
        rw [hS]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩
      exact (le_iSup₂_of_le j hjS le_rfl : Δ.F.U j ≤ (⨆ j ∈ S, Δ.F.U j)) hu
      |> fun h => mem_polarPerp_iff.1 hv u h
  have hScard : S.card = r - Nat.card {i : Fin r // toAdd (f₀ i) = 0} := by
    have h1 : S.card = Fintype.card {i : Fin r // toAdd (f₀ i) ≠ 0} := by
      rw [Fintype.card_subtype]
    rw [h1, Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_fin]
  have hZle : Nat.card {i : Fin r // toAdd (f₀ i) = 0} ≤ r := by
    rw [Nat.card_eq_fintype_card]
    simpa using Fintype.card_subtype_le (p := fun i : Fin r => toAdd (f₀ i) = 0)
  have hcompl : IsCompl (polarPerp Q (⨆ j ∈ S, Δ.F.U j)) (⨆ j ∈ S, Δ.F.U j) :=
    (isCompl_polarPerp (hU.nondeg_biSup S)).symm
  have hsum := Submodule.finrank_add_eq_of_isCompl hcompl
  rw [← hfix, hU.finrank_biSup S, hdimV] at hsum
  omega

private theorem ggResX2Forms_isPlusType_fixedSpace_iff (hK : Nat.card K = 2)
    (hQ : (polarBilin Q).Nondegenerate) (Δ : TBJOmData Q 3 A r) (hA : A ≤ orthDerived Q)
    (hchar : OrdPNsOm.charSum Q ⊤ ≡ 1 [ZMOD 3]) (f₀ : Fin r → Multiplicative (ZMod 3)) :
    IsPlusType (Q.comp (fixedSpace (Δ.τ f₀)).subtype) ↔
      Even (Nat.card {i : Fin r // toAdd (f₀ i) = 0}) := by
  have hU := ggResX2FixAux_isPlaneSystem (by norm_num) Δ hQ hA (by simp [hK])
  have hdimV := ggResX2Forms_finrank_eq_two_mul hK hQ Δ hA hchar
  have hx : OddOrderIsometry Q 3 (Δ.τ f₀) := Δ.oddOrderIsometry (by norm_num) hQ hA f₀
  have hpar : IsPlusType Q ↔ Even (Module.finrank K V / 2) := by
    rw [show Module.finrank K V / 2 = r by
      rw [hdimV, Nat.mul_div_cancel_left _ (by norm_num)]]
    exact hU.isPlusType_iff_of_finrank hdimV
  rw [CFSG.HardMathSupport.Dickson.Bal207.OrthRow.Two.isPlusType_fixedSpace_iff hK hx hpar,
    ggResX2Forms_finrank_fixedSpace hK hQ Δ hA hchar f₀,
    Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]

private theorem ggResX2Forms_not_quasisimple_small (hK : Nat.card K = 2)
    (hQ : (polarBilin Q).Nondegenerate) (Δ : TBJOmData Q 3 A r) (hA : A ≤ orthDerived Q)
    (hchar : OrdPNsOm.charSum Q ⊤ ≡ 1 [ZMOD 3]) (f₀ : Fin r → Multiplicative (ZMod 3))
    (hZle : Nat.card {i : Fin r // toAdd (f₀ i) = 0} ≤ 2)
    {F : Subgroup (V ≃ₗ[K] V)} (hFle : F ≤ supportedFixedDerived Q (Δ.τ f₀))
    (hFq : CFSG.IsQuasisimple ↥F)
    (hFn : (F.subgroupOf (supportedFixedDerived Q (Δ.τ f₀))).Normal) : False := by
  have hx : OddOrderIsometry Q 3 (Δ.τ f₀) := Δ.oddOrderIsometry (by norm_num) hQ hA f₀
  have hWdim : Module.finrank K (fixedSpace (Δ.τ f₀)) =
      2 * Nat.card {i : Fin r // toAdd (f₀ i) = 0} :=
    ggResX2Forms_finrank_fixedSpace hK hQ Δ hA hchar f₀
  have htype : 1 ≤ Nat.card {i : Fin r // toAdd (f₀ i) = 0} →
      (IsPlusType (Q.comp (fixedSpace (Δ.τ f₀)).subtype) ↔
        Even (Nat.card {i : Fin r // toAdd (f₀ i) = 0})) :=
    fun _ => ggResX2Forms_isPlusType_fixedSpace_iff hK hQ Δ hA hchar f₀
  have hsmall : Nat.card {i : Fin r // toAdd (f₀ i) = 0} ≤ 1 ∨
      (Nat.card {i : Fin r // toAdd (f₀ i) = 0} = 2 ∧ Nat.card K = 2) := by omega
  have hK'q : CFSG.IsQuasisimple ↥(F.subgroupOf (supportedFixedDerived Q (Δ.τ f₀))) :=
    (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr
      (Subgroup.subgroupOfEquivOfLe hFle)).2 hFq
  have hNn : ((F.subgroupOf (supportedFixedDerived Q (Δ.τ f₀))).map
      (supportedFixedDerivedEquiv hx).toMonoidHom).Normal :=
    hFn.map (supportedFixedDerivedEquiv hx).toMonoidHom
      (supportedFixedDerivedEquiv hx).surjective
  refine CFSG.HardMathSupport.Dickson.Bal207.OrthFix.orthDerived_not_quasisimple_small
    (W := ↥(fixedSpace (Δ.τ f₀))) hx.polarBilin_fixed_nondegenerate hWdim htype hsmall
    ((F.subgroupOf (supportedFixedDerived Q (Δ.τ f₀))).map
      (supportedFixedDerivedEquiv hx).toMonoidHom) hNn ?_
  exact (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).1
    (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_map_of_injective
      (f := (supportedFixedDerivedEquiv hx).toMonoidHom)
      (supportedFixedDerivedEquiv hx).injective
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).2 hK'q))

private theorem ggResX2Forms_primaryMultiplicity_le (hK : Nat.card K = 2)
    (hQ : (polarBilin Q).Nondegenerate) (Δ : TBJOmData Q 3 A r) (hA : A ≤ orthDerived Q)
    (f₀ : Fin r → Multiplicative (ZMod 3)) {h : K[X]}
    (hh : h ∈ primaryFactors (Δ.τ f₀).toLinearMap) (hX : h ≠ X - 1) :
    primaryMultiplicity (Δ.τ f₀).toLinearMap h ≤
      Nat.card {i : Fin r // toAdd (f₀ i) ≠ 0 ∧
        Δ.F.U i ≤ orbitSpace (Δ.τ f₀).toLinearMap h} := by
  classical
  have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  have hU := ggResX2FixAux_isPlaneSystem (by norm_num) Δ hQ hA (by simp [hK])
  have hx : OddOrderIsometry Q 3 (Δ.τ f₀) := Δ.oddOrderIsometry (by norm_num) hQ hA f₀
  have hdeg : h.natDegree = 2 := by
    rw [(CFSG.HardMathSupport.Dickson.Bal207.OrthRow.Two.primaryFactor_cases hK hx
      hh).resolve_left hX]
    exact CFSG.HardMathSupport.Timmesfeld.CrossChar.natDegree_cyc3 K
  set s : Finset (Fin r) :=
    Finset.univ.filter (fun i => Δ.F.U i ≤ orbitSpace (Δ.τ f₀).toLinearMap h) with hs
  have horb : orbitSpace (Δ.τ f₀).toLinearMap h = ⨆ j ∈ s, Δ.F.U j := by
    refine (Δ.orbitSpace_eq (by norm_num) hQ hA f₀ hh hX).trans ?_
    simp only [hs, Finset.mem_filter, Finset.mem_univ, true_and]
  have h1 : Module.finrank K (primaryComponent (Δ.τ f₀).toLinearMap h) =
      2 * primaryMultiplicity (Δ.τ f₀).toLinearMap h := by
    rw [finrank_primaryComponent, hdeg]
  have h2 : Module.finrank K (primaryComponent (Δ.τ f₀).toLinearMap h) ≤
      Module.finrank K (orbitSpace (Δ.τ f₀).toLinearMap h) :=
    Submodule.finrank_mono (show primaryComponent (Δ.τ f₀).toLinearMap h ≤
      orbitSpace (Δ.τ f₀).toLinearMap h from le_sup_left)
  rw [horb, hU.finrank_biSup s] at h2
  have h3 : s.card = Nat.card {i : Fin r // toAdd (f₀ i) ≠ 0 ∧
      Δ.F.U i ≤ orbitSpace (Δ.τ f₀).toLinearMap h} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext i
    simp only [hs, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun hi => ⟨Δ.active_of_le_orbitSpace (by norm_num) hQ hA f₀ hh hX i hi, hi⟩,
      fun hi => hi.2⟩
  omega

private theorem ggResX2Forms_card_le (Δ : TBJOmData Q 3 A r) (hA : A ≤ orthDerived Q)
    {E C : Subgroup ↥(orthDerived Q)} (hEA : ∀ e ∈ E, (e : V ≃ₗ[K] V) ∈ A)
    (S : (Fin r → Multiplicative (ZMod 3)) → Prop)
    (hS : ∀ f, Δ.τΩ hA f ∈ Subgroup.centralizer (C : Set ↥(orthDerived Q)) → S f) :
    Nat.card ↥(E ⊓ Subgroup.centralizer (C : Set ↥(orthDerived Q))) ≤ Nat.card {f // S f} := by
  classical
  have hex : ∀ e : ↥(E ⊓ Subgroup.centralizer (C : Set ↥(orthDerived Q))),
      ∃ f, Δ.τΩ hA f = (e : ↥(orthDerived Q)) := by
    intro e
    have heA : ((e : ↥(orthDerived Q)) : V ≃ₗ[K] V) ∈ Δ.τ.range := by
      rw [Δ.τ_range]
      exact hEA _ (Subgroup.mem_inf.mp e.2).1
    obtain ⟨f, hf⟩ := heA
    exact ⟨f, Subtype.ext hf⟩
  choose g hg using hex
  refine Nat.card_le_card_of_injective
    (fun e => ⟨g e, hS _ (by rw [hg e]; exact (Subgroup.mem_inf.mp e.2).2)⟩) ?_
  intro e₁ e₂ h12
  have h' : g e₁ = g e₂ := congrArg Subtype.val h12
  apply Subtype.ext
  rw [← hg e₁, ← hg e₂, h']

private theorem ggResX2Forms_card_scalar (P : Fin r → Prop)
    (f₀ : Fin r → Multiplicative (ZMod 3)) :
    Nat.card {f : Fin r → Multiplicative (ZMod 3) //
      ∃ m : ZMod 3, ∀ i, P i → toAdd (f i) = m * toAdd (f₀ i)} ≤
      3 * 3 ^ (r - Nat.card {i // P i}) := by
  classical
  have hex : ∀ f : {f : Fin r → Multiplicative (ZMod 3) //
      ∃ m : ZMod 3, ∀ i, P i → toAdd (f i) = m * toAdd (f₀ i)},
      ∃ m : ZMod 3, ∀ i, P i → toAdd (f.1 i) = m * toAdd (f₀ i) := fun f => f.2
  choose m hm using hex
  let g : {f : Fin r → Multiplicative (ZMod 3) //
      ∃ m : ZMod 3, ∀ i, P i → toAdd (f i) = m * toAdd (f₀ i)} →
      ZMod 3 × ({i // ¬ P i} → Multiplicative (ZMod 3)) := fun f => (m f, fun i => f.1 i.1)
  have hg : Function.Injective g := by
    intro f₁ f₂ h12
    have h1 : m f₁ = m f₂ := congrArg Prod.fst h12
    have h2 := congrArg Prod.snd h12
    apply Subtype.ext
    funext i
    by_cases hi : P i
    · apply toAdd.injective
      rw [hm f₁ i hi, hm f₂ i hi, h1]
    · exact congrFun h2 ⟨i, hi⟩
  have hc3 : Nat.card (Multiplicative (ZMod 3)) = 3 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  have hcompl : Nat.card {i // ¬ P i} = r - Nat.card {i // P i} := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
      Fintype.card_fin]
  calc _ ≤ Nat.card (ZMod 3 × ({i // ¬ P i} → Multiplicative (ZMod 3))) :=
        Nat.card_le_card_of_injective g hg
    _ = 3 * 3 ^ (r - Nat.card {i // P i}) := by
      rw [Nat.card_prod, Nat.card_zmod, Nat.card_fun, hc3, hcompl]

private theorem ggResX2Forms_card_vanish (Z : Fin r → Prop) :
    Nat.card {f : Fin r → Multiplicative (ZMod 3) // ∀ i, Z i → f i = 1} ≤
      3 ^ (r - Nat.card {i // Z i}) := by
  classical
  let g : {f : Fin r → Multiplicative (ZMod 3) // ∀ i, Z i → f i = 1} →
      ({i // ¬ Z i} → Multiplicative (ZMod 3)) := fun f i => f.1 i.1
  have hg : Function.Injective g := by
    intro f₁ f₂ h12
    apply Subtype.ext
    funext i
    by_cases hi : Z i
    · rw [f₁.2 i hi, f₂.2 i hi]
    · exact congrFun h12 ⟨i, hi⟩
  have hc3 : Nat.card (Multiplicative (ZMod 3)) = 3 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  have hcompl : Nat.card {i // ¬ Z i} = r - Nat.card {i // Z i} := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
      Fintype.card_fin]
  calc _ ≤ Nat.card ({i // ¬ Z i} → Multiplicative (ZMod 3)) :=
        Nat.card_le_card_of_injective g hg
    _ = 3 ^ (r - Nat.card {i // Z i}) := by
      rw [Nat.card_fun, hc3, hcompl]

end OrthTorus

theorem ggResExactTwoOrthFormsOmega_holds : GGResExactTwoOrthFormsOmega := by
  intro F _ _ _ hF2 V _ _ _ Q hQ hdim hchar E hEab hEsc t htE ht1 C hC hcard
  let A : Subgroup (V ≃ₗ[F] V) := E.map (orthDerived Q).subtype
  have hEA : ∀ e ∈ E, (e : V ≃ₗ[F] V) ∈ A := fun e he => Subgroup.mem_map_of_mem _ he
  have hAΩ : A ≤ orthDerived Q := by
    intro a ha
    rcases Subgroup.mem_map.mp ha with ⟨e, he, rfl⟩
    exact e.2
  have hApow : ∀ a ∈ A, a ^ 3 = 1 := by
    intro a ha
    rcases Subgroup.mem_map.mp ha with ⟨e, he, rfl⟩
    have h : e ^ 3 = 1 := hEab.2 e he
    exact Subtype.ext_iff.mp h
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    intro a ha b hb
    rcases Subgroup.mem_map.mp ha with ⟨e₁, he₁, rfl⟩
    rcases Subgroup.mem_map.mp hb with ⟨e₂, he₂, rfl⟩
    have h := hEab.1.is_comm.comm ⟨e₁, he₁⟩ ⟨e₂, he₂⟩
    have h' : (e₁ : ↥(orthDerived Q)) * e₂ = e₂ * e₁ := Subtype.ext_iff.mp h
    exact congrArg Subtype.val h'
  have hmax : ∀ g ∈ orthDerived Q, g ^ 3 = 1 → (∀ c ∈ A, g * c = c * g) → g ∈ A := by
    intro g hgΩ hg3 hgc
    let g' : ↥(orthDerived Q) := ⟨g, hgΩ⟩
    have hg'3 : g' ^ 3 = 1 := by
      apply Subtype.ext
      simpa using hg3
    have hg'c : ∀ e ∈ E, g' * e = e * g' := by
      intro e he
      apply Subtype.ext
      exact hgc (e : V ≃ₗ[F] V) (hEA e he)
    exact Subgroup.mem_map_of_mem _ (hEsc g' hg'c hg'3)
  have hne : ∃ b ∈ A, b ≠ 1 := by
    refine ⟨(t : V ≃ₗ[F] V), hEA t htE, ?_⟩
    intro h
    apply ht1
    apply Subtype.ext
    exact h
  have h8 : 8 ≤ Module.finrank F V := by rcases hdim with h | h <;> omega
  obtain ⟨m, hm⟩ := CFSG.ComponentClassification.UnbalancedCatalog.even_finrank_of_charTwo Q hQ
  have hm4 : 4 ≤ m := by omega
  have hm' : Module.finrank F V = 2 * m := by omega
  have hT : ∃ T : Submodule F V, finrank F T = 3 ∧ ∀ v ∈ T, Q v = 0 :=
    CFSG.RankThree.PartOne.exists_threeSingular_of_dim Q hQ hm4 hm'
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hpq : 3 ∣ Nat.card F - 1 ∨ 3 ∣ Nat.card F + 1 := by
    right
    rw [hF2]
  obtain ⟨r, τ, F_data, D, i₁, i₂, i₃, c, θ, hτF, hinj, hrange, hdim_D, hcp, hfix, htwist,
    hroots, hθinj, hθrange, hθact, hnorm, hswap, hdinv, hsign, hnoFix, hexFix⟩ :=
    OrthTorus.exists_torus_blocks (p := 3) hp2 hpq hQ hT hAΩ hApow hAcomm hmax hne
  let Δ : OrthTorus.TBJOmData Q 3 A r :=
    { τ := τ, F := F_data, D := D, c := c, θ := θ, τ_eq := hτF, τ_inj := hinj, τ_range := hrange,
      finrank_D := hdim_D, c_pow := hcp, c_fix := hfix, c_twist := htwist, c_roots := hroots,
      θ_inj := hθinj, θ_range := hθrange, θ_act := hθact, normalizer := hnorm,
      swapMove := hswap, dinvMove := hdinv, signMove := hsign, noFixed := hnoFix,
      exFixed := hexFix }
  obtain ⟨f₀, hf₀⟩ := Δ.τ_range.symm.le (hEA t htE)
  have htx : (t : V ≃ₗ[F] V) = Δ.τ f₀ := hf₀.symm
  have hx : OddOrderIsometry Q 3 (t : V ≃ₗ[F] V) := by
    rw [htx]
    exact Δ.oddOrderIsometry hp2 hQ hAΩ f₀
  have hx₀ : OddOrderIsometry Q 3 (Δ.τ f₀) := Δ.oddOrderIsometry hp2 hQ hAΩ f₀
  have hdimV : Module.finrank F V = 2 * r :=
    OrthTorus.ggResX2Forms_finrank_eq_two_mul hF2 hQ Δ hAΩ hchar
  have hr5 : r ≤ 5 := by rcases hdim with h | h <;> omega
  rcases OrthTorus.component_cases (p := 3) hQ (Fact.out : Nat.Prime 3) hp2 (x := t) hx hC with
      ⟨h, hh, hhX, hCeq⟩ | ⟨F', hF'q, hF'S, hF'norm, hFix, hCeq⟩
  ·
    rw [htx] at hh hCeq
    subst hCeq
    have hm4 : 4 ≤ primaryMultiplicity (Δ.τ f₀).toLinearMap h :=
      ggResX2_four_le_primaryMultiplicity hF2 hx₀ hh hhX
        (ResU3Three.not_isSolvable_of_isQuasisimple hC.2.2)
    have hmP := OrthTorus.ggResX2Forms_primaryMultiplicity_le hF2 hQ Δ hAΩ f₀ hh hhX
    have hle := OrthTorus.ggResX2Forms_card_le Δ hAΩ hEA
      (C := (specialBlock Q (Δ.τ f₀) h).subgroupOf (orthDerived Q))
      (fun f => ∃ m : ZMod 3, ∀ i, (toAdd (f₀ i) ≠ 0 ∧
        Δ.F.U i ≤ orbitSpace (Δ.τ f₀).toLinearMap h) → toAdd (f i) = m * toAdd (f₀ i))
      (fun f hf => by
        obtain ⟨m, hm⟩ := OrthTorus.ggResExactTwoOrthFixOmega_scalar hp2 Δ hQ hAΩ f₀ f hh hhX
          (fun n hn _ => Subgroup.mem_centralizer_iff.mp hf n hn)
        exact ⟨m, fun i hi => hm i hi.1 hi.2⟩)
    have h9 := hcard.trans (hle.trans (OrthTorus.ggResX2Forms_card_scalar
      (fun i => toAdd (f₀ i) ≠ 0 ∧ Δ.F.U i ≤ orbitSpace (Δ.τ f₀).toLinearMap h) f₀))
    have hk : 1 ≤ r - Nat.card {i : Fin r // toAdd (f₀ i) ≠ 0 ∧
        Δ.F.U i ≤ orbitSpace (Δ.τ f₀).toLinearMap h} := by
      by_contra hk
      rw [show r - Nat.card {i : Fin r // toAdd (f₀ i) ≠ 0 ∧
        Δ.F.U i ≤ orbitSpace (Δ.τ f₀).toLinearMap h} = 0 by omega] at h9
      norm_num at h9
    have hm4' : primaryMultiplicity (Δ.τ f₀).toLinearMap h = 4 := by omega
    exact ⟨by omega, ggResX2_isU42_specialBlock hF2 hQ hT hx₀ hh hhX hm4'⟩
  ·
    rw [htx] at hF'S hF'norm hFix
    subst hCeq
    set Z := Nat.card {i : Fin r // toAdd (f₀ i) = 0} with hZ
    have hZ3 : 3 ≤ Z := by
      by_contra hlt
      exact OrthTorus.ggResX2Forms_not_quasisimple_small hF2 hQ Δ hAΩ hchar f₀ (by omega)
        hF'S hF'q hF'norm
    have hW := OrthTorus.ggResX2Forms_finrank_fixedSpace hF2 hQ Δ hAΩ hchar f₀
    have hF'eq : F' = supportedFixedDerived Q (Δ.τ f₀) := hFix.resolve_left (by omega)
    have hvan : ∀ f, Δ.τΩ hAΩ f ∈ Subgroup.centralizer
        (F'.subgroupOf (orthDerived Q) : Set ↥(orthDerived Q)) →
        ∀ i, toAdd (f₀ i) = 0 → f i = 1 := by
      intro f hf i hi
      obtain ⟨k, hkne, hk0⟩ : ∃ k : Fin r, k ≠ i ∧ toAdd (f₀ k) = 0 := by
        obtain ⟨k, hk⟩ := Fintype.exists_ne_of_one_lt_card
          (α := {j : Fin r // toAdd (f₀ j) = 0}) (by rw [← Nat.card_eq_fintype_card]; omega)
          ⟨i, hi⟩
        exact ⟨k.1, fun h => hk (Subtype.ext h), k.2⟩
      exact OrthTorus.ggResX2FixAux_dinv_eq_one hp2 Δ hQ hAΩ (Ne.symm hkne) hi hk0 (by omega)
        hF'eq (fun n hn _ => Subgroup.mem_centralizer_iff.mp hf n hn)
    have h9 := hcard.trans ((OrthTorus.ggResX2Forms_card_le Δ hAΩ hEA
      (fun f => ∀ i, toAdd (f₀ i) = 0 → f i = 1) hvan).trans
      (OrthTorus.ggResX2Forms_card_vanish (fun i => toAdd (f₀ i) = 0)))
    rw [← hZ] at h9
    have hk : 2 ≤ r - Z := by
      by_contra hk
      have hpow : 3 ^ (r - Z) ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hZ3' : Z = 3 := by omega
    have hW6 : finrank F (fixedSpace (Δ.τ f₀)) = 6 := by omega
    have hnp : ¬ IsPlusType (Q.comp (fixedSpace (Δ.τ f₀)).subtype) := by
      rw [OrthTorus.ggResX2Forms_isPlusType_fixedSpace_iff hF2 hQ Δ hAΩ hchar f₀, ← hZ, hZ3']
      decide
    have hts : ∀ U : Submodule F (fixedSpace (Δ.τ f₀)), finrank F U = 3 →
        ∃ u ∈ U, (Q.comp (fixedSpace (Δ.τ f₀)).subtype) u ≠ 0 := by
      intro U hU
      by_contra hcon
      push Not at hcon
      exact hnp ⟨U, by omega, hcon⟩
    rw [hF'eq]
    exact ⟨by omega, ggResX2_isU42_fixed hF2 hx₀ hW6 hts⟩

end CFSG.StandardType
