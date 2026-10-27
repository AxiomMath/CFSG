module

public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP9Orth
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP9Wa
public import CFSG.LieType.ChevTwo.OrthogonalBasic
import CFSG.LocalAnalysis.StandardType.GGAutomizerEquiv
import CFSG.LocalAnalysis.StandardType.GGFrameFSxOrth
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.OutL5Proof
import CFSG.RankThree.PartTwo.Sec14.Ronan148JInner
import CFSG.RankThree.PartOne.S11d.OrthCaseH
import CFSG.RankThree.PartOne.S11d.OrthDicksonOmega
import CFSG.GH74.E2.DirectProd
import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP9Norm
import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP9SignOmega
import CFSG.LocalAnalysis.ComponentInitial.SteinbergCBShearAxis
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoConfig
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoEscape
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrHom
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrLarge
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrXGen
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbDefs
public import CFSG.LocalAnalysis.AGLEmbedding.ZZPrimeDefs
public import CFSG.Quasithin.Background.B1MoreElevenD
public import CFSG.Quasithin.Background.B1MoreElevenF
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.EmptyFaithfulMultiple.InputB19Proof
public import CFSG.RankThree.PartTwo.Sec12.Notation
public import CFSG.RankThree.PartTwo.Sec4.Item47Statement
public import CFSG.RankThree.PartTwo.Sec4.Item47Witness
public import CFSG.RankThree.PartTwo.Sec8.Statements
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement
import CFSG.CGT.PushingUpLit.BHS.NaturalDefs
import CFSG.CGT.PushingUpLit.BHS.SymNatDefs
import CFSG.Holt.Centralizer
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.PairFacts
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.FixedBlock
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TightBridge
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TightModuleAux
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.AltSixBound
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.BlockCensus
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellMotion
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
import CFSG.LocalAnalysis.RankThreeTheoremC.D2LocalCGT3
import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessEven
import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessOdd
import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldCentralizer
import CFSG.RankThree.PartOne.N143.LowTwoRankSplit
import CFSG.RankThree.PartOne.N143.SectionCenter
import CFSG.RankThree.PartOne.N143.SectionRankBound
import CFSG.RankThree.PartOne.N143.SectionRankProof
import CFSG.RankThree.PartOne.N143.SectionRankSplit
import CFSG.RankThree.PartOne.N143.SectionReduce
import CFSG.RankThree.PartOne.S11d.OutClassicalTwo
import CFSG.RankThree.PartOne.S11d.OutLinear
import CFSG.RankThree.PartOne.S11d.OutSymplectic
import CFSG.RankThree.PartOne.S11d.OutUnitary
import CFSG.RankThree.PartTwo.Sec19.Item194Used
import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherDefs
import CFSG.Sporadic.Bridge.Fi24Data
import CFSG.Sporadic.Presentation.Fi24PrimeExact
import Certificates.Certificate19800
import Certificates.Certificate9207
import Certificates.Certificate9591
import Certificates.Certificate9594
import Certificates.Certificate9595
import Certificates.Certificate9597
import Certificates.Certificate9602

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Open CFSG.LieType.ChevTwo QuadraticMap

variable {G : Type} [Group G] [Finite G] {Bs K : Subgroup G} {z : G}
  {ι : Type} [Fintype ι] [DecidableEq ι] {Q₀ : (ι → ZMod 2) → ZMod 2}
  {q : QuadraticForm (ZMod 2) (ι → ZMod 2)}

theorem center_statedOmega_eq_bot_of_goodQ (hQ : GoodQ Q₀) :
    Subgroup.center (StatedOmega Q₀) = ⊥ := by
  refine le_antisymm (fun c hc => ?_) bot_le
  rw [Subgroup.mem_bot]
  have hκ : kappa Q₀ ⟨c, statedOmega_le_isoGrp Q₀ c.2⟩ = MulAut.conj c := by
    simpa using kappa_eq_conj (Q := Q₀) (g := ⟨c, statedOmega_le_isoGrp Q₀ c.2⟩) c.2
  have hconj : MulAut.conj c = 1 := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    rw [MulAut.conj_apply, MulAut.one_apply]
    change (c : GL ι (ZMod 2)) * (x : GL ι (ZMod 2)) * (c : GL ι (ZMod 2))⁻¹ =
      (x : GL ι (ZMod 2))
    have hcomm : (c : GL ι (ZMod 2)) * (x : GL ι (ZMod 2)) =
        (x : GL ι (ZMod 2)) * (c : GL ι (ZMod 2)) :=
      (congrArg (fun z : ↥(StatedOmega Q₀) => (z : GL ι (ZMod 2)))
        (Subgroup.mem_center_iff.mp hc x)).symm
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  have hg : (⟨c, statedOmega_le_isoGrp Q₀ c.2⟩ : isoGrp Q₀) = 1 :=
    hQ.kappa_injective (by rw [hκ, hconj, map_one])
  exact Subtype.ext
    (congrArg (fun g : isoGrp Q₀ => (g : GL ι (ZMod 2))) hg)

omit [Finite G] in
theorem bstar_eq_zpowers_sup_inf_of_native_orth (hQ : GoodQ Q₀) (hind : OmegaTwoAutInduced Q₀)
    (e : K ≃* StatedOmega Q₀) (hBs : IsElemAbelian 3 Bs)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hker : Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers z)
    (hBstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs) :
    Bs = Subgroup.zpowers z ⊔ Bs ⊓ K := by
  have hcenter : Subgroup.center K = ⊥ := by
    apply Subgroup.eq_bot_of_card_eq
    rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv,
      center_statedOmega_eq_bot_of_goodQ hQ, Subgroup.card_bot]
  have hKC : K ⊓ Subgroup.centralizer (K : Set G) = ⊥ := by
    refine le_antisymm (fun x hx => ?_) bot_le
    have hxZ : (⟨x, hx.1⟩ : K) ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      exact fun y => Subtype.ext ((Subgroup.mem_centralizer_iff.mp hx.2) y y.property)
    rw [hcenter, Subgroup.mem_bot] at hxZ
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hxZ)
  have hinner : ∀ b ∈ Bs, ∃ k ∈ K, ∀ x ∈ K, b * x * b⁻¹ = k * x * k⁻¹ := by
    intro b hb
    have hb3 : (⟨b, hN hb⟩ : Subgroup.normalizer (K : Set G)) ^ 3 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact hBs.2 b hb
    have hψ3 : (K.normalizerMonoidHom ⟨b, hN hb⟩) ^ 3 = 1 := by
      rw [← map_pow, hb3, map_one]
    obtain ⟨k, hk⟩ := autThreePowInner_of_goodQ hQ hind e
      (K.normalizerMonoidHom ⟨b, hN hb⟩) 1 (fun x => by
        rw [pow_one, ← CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.mulAut_pow_apply_iterate,
          hψ3, MulAut.one_apply])
    refine ⟨k, k.property, fun x hx => ?_⟩
    have h := congrArg (fun z : K => (z : G)) (hk ⟨x, hx⟩)
    simpa only [Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.coe_mul,
      Subgroup.coe_inv] using h
  have hsplit := CFSG.RankThree.PartTwo.Sec14.Ronan148J.sup_eq_of_forall_inner
    (fun b hb c hc => IsElemAbelian.comm hBs hb hc) hBs.2 hBstar hKC hN hinner
  rw [hker] at hsplit
  exact hsplit.symm

omit [DecidableEq ι] in
theorem omegaGroup_eq_orthDerived_of_card (hnd : (polarBilin q).Nondegenerate) {a : ℕ}
    (hι : Fintype.card ι = 2 * a) (ha : 4 ≤ a) :
    CFSG.RankThree.OrthogonalInvolutions.omegaGroup q hnd =
      CFSG.RankThree.Classical2.orthDerived q := by
  have hdim : Module.finrank (ZMod 2) (ι → ZMod 2) = 2 * a := by
    rw [Module.finrank_fintype_fun_eq_card, hι]
  have hT := CFSG.RankThree.PartOne.exists_threeSingular_of_dim q hnd ha hdim
  exact le_antisymm
    (CFSG.RankThree.PartOne.FieldFix.omegaGroup_le_orthDerived hnd hT)
    (CFSG.RankThree.PartOne.FieldFix.orthDerived_le_omegaGroup hnd)

@[expose] noncomputable def orthTorusLin (hq : ⇑q = Q₀) (e : K ≃* StatedOmega Q₀)
    (Bs : Subgroup G) : Subgroup ((ι → ZMod 2) ≃ₗ[ZMod 2] (ι → ZMod 2)) :=
  ((Bs.subgroupOf K).map (e.trans (statedOmegaEquivDerived hq)).toMonoidHom).map
    (CFSG.RankThree.Classical2.orthDerived q).subtype

omit [Finite G] in
theorem selfCent_orthTorusLin (hQ : GoodQ Q₀) (hind : OmegaTwoAutInduced Q₀) (hq : ⇑q = Q₀)
    (e : K ≃* StatedOmega Q₀) (hBs : IsElemAbelian 3 Bs)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hker : Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers z)
    (hBstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs) :
    ∀ g ∈ CFSG.RankThree.Classical2.orthDerived q,
      (∀ c ∈ orthTorusLin hq e Bs, g * c = c * g) → g ^ 3 = 1 → g ∈ orthTorusLin hq e Bs := by
  have hsplit := bstar_eq_zpowers_sup_inf_of_native_orth hQ hind e hBs hN hker hBstar
  intro g hg hcomm hg3
  let ε : K ≃* CFSG.RankThree.Classical2.orthDerived q :=
    e.trans (statedOmegaEquivDerived hq)
  have hsc := selfCentralizing_torus_of_split_model ε hker hsplit hBstar
  let Z : CFSG.RankThree.Classical2.orthDerived q := ⟨g, hg⟩
  have hcomm' : ∀ Y ∈ (Bs.subgroupOf K).map ε.toMonoidHom, Z * Y = Y * Z := by
    intro Y hY
    apply Subtype.ext
    have hYt : (Y : (ι → ZMod 2) ≃ₗ[ZMod 2] (ι → ZMod 2)) ∈ orthTorusLin hq e Bs :=
      Subgroup.mem_map_of_mem _ hY
    simpa [Z] using hcomm _ hYt
  have hZ3 : Z ^ 3 = 1 := by
    apply Subtype.ext
    simpa [Z] using hg3
  have hmem := hsc Z hcomm' hZ3
  simpa [orthTorusLin, ε, Z] using
    Subgroup.mem_map_of_mem (CFSG.RankThree.Classical2.orthDerived q).subtype hmem

theorem exists_linEquiv_of_mulAut_orthDerived (hq : ⇑q = Q₀) (hind : OmegaTwoAutInduced Q₀)
    (α : MulAut ↥(CFSG.RankThree.Classical2.orthDerived q)) :
    ∃ h : (ι → ZMod 2) ≃ₗ[ZMod 2] (ι → ZMod 2),
      ∀ x : CFSG.RankThree.Classical2.orthDerived q,
        ((α x : CFSG.RankThree.Classical2.orthDerived q) :
          (ι → ZMod 2) ≃ₗ[ZMod 2] (ι → ZMod 2)) = h * x * h⁻¹ := by
  let E : ↥(StatedOmega Q₀) ≃* CFSG.RankThree.Classical2.orthDerived q :=
    ((CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι (ZMod 2)).subgroupMap (StatedOmega Q₀)).trans
      (MulEquiv.subgroupCongr (by
        rw [CFSG.ClassicalGroups.Orthogonal.statedOmega_eq_comap hq]
        exact Subgroup.map_comap_eq_self_of_surjective
          (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι (ZMod 2)).surjective _))
  let α' : MulAut ↥(StatedOmega Q₀) := MulAut.congr E.symm α
  obtain ⟨g, -, hgα⟩ := hind α'
  have hEval : ∀ z : ↥(StatedOmega Q₀),
      ((E z : CFSG.RankThree.Classical2.orthDerived q) :
        (ι → ZMod 2) ≃ₗ[ZMod 2] (ι → ZMod 2)) =
      CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι (ZMod 2) (z : GL ι (ZMod 2)) :=
    fun _ => rfl
  refine ⟨CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι (ZMod 2) g, fun x => ?_⟩
  have hα' : α' (E.symm x) = E.symm (α x) := by
    simp [α', MulAut.congr_apply]
  have hL : CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι (ZMod 2)
      ((α' (E.symm x) : ↥(StatedOmega Q₀)) : GL ι (ZMod 2)) =
        ((α x : CFSG.RankThree.Classical2.orthDerived q) :
          (ι → ZMod 2) ≃ₗ[ZMod 2] (ι → ZMod 2)) := by
    rw [hα', ← hEval (E.symm (α x)), MulEquiv.apply_symm_apply]
  have hR : CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι (ZMod 2)
      (((E.symm x : ↥(StatedOmega Q₀)) : GL ι (ZMod 2))) =
        (x : (ι → ZMod 2) ≃ₗ[ZMod 2] (ι → ZMod 2)) := by
    rw [← hEval (E.symm x), MulEquiv.apply_symm_apply]
  have hx := hgα (E.symm x)
  calc ((α x : CFSG.RankThree.Classical2.orthDerived q) :
        (ι → ZMod 2) ≃ₗ[ZMod 2] (ι → ZMod 2))
      = CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι (ZMod 2)
          ((α' (E.symm x) : ↥(StatedOmega Q₀)) : GL ι (ZMod 2)) := hL.symm
    _ = CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι (ZMod 2)
          (g * ((E.symm x : ↥(StatedOmega Q₀)) : GL ι (ZMod 2)) * g⁻¹) := by rw [hx]
    _ = CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι (ZMod 2) g *
          CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι (ZMod 2)
            ((E.symm x : ↥(StatedOmega Q₀)) : GL ι (ZMod 2)) *
          (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι (ZMod 2) g)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
    _ = CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι (ZMod 2) g *
          x * (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι (ZMod 2) g)⁻¹ := by
      rw [hR]

omit [Finite G] in
theorem exists_omCoord_of_native_orth (hQ : GoodQ Q₀) (hind : OmegaTwoAutInduced Q₀)
    (hq : ⇑q = Q₀) (hnd : (polarBilin q).Nondegenerate) {a : ℕ}
    (hι : Fintype.card ι = 2 * a) (ha : 4 ≤ a) (e : K ≃* StatedOmega Q₀)
    (hBs : IsElemAbelian 3 Bs) (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hker : Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers z)
    (hBstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs) :
    ∃ C : ChoiceTwoOm.OmCoord (ZMod 2) q (orthTorusLin hq e Bs),
      ((C.W0 = ⊥ ∧ C.s = a) ∨ (C.s + 1 = a ∧ C.W0 ≠ ⊥)) ∧
        (CFSG.GroupTheory.WeirSylow.IsPlusType q ↔ Even C.s) := by
  have hω : CFSG.RankThree.OrthogonalInvolutions.omegaGroup q hnd =
      CFSG.RankThree.Classical2.orthDerived q :=
    omegaGroup_eq_orthDerived_of_card hnd hι ha
  have hdim : Module.finrank (ZMod 2) (ι → ZMod 2) = 2 * a := by
    rw [Module.finrank_fintype_fun_eq_card, hι]
  have hEΩ : orthTorusLin hq e Bs ≤
      CFSG.RankThree.OrthogonalInvolutions.omegaGroup q hnd := by
    rw [hω]
    rintro x ⟨y, -, rfl⟩
    exact y.2
  have hE : IsElemAbelian 3 (orthTorusLin hq e Bs) :=
    ((hBs.subgroupOf K).map (e.trans (statedOmegaEquivDerived hq)).toMonoidHom).map
      (CFSG.RankThree.Classical2.orthDerived q).subtype
  have hsc : ∀ g ∈ CFSG.RankThree.OrthogonalInvolutions.omegaGroup q hnd,
      (∀ c ∈ orthTorusLin hq e Bs, g * c = c * g) → g ^ 3 = 1 →
        g ∈ orthTorusLin hq e Bs := by
    intro g hg hcomm hg3
    rw [hω] at hg
    exact selfCent_orthTorusLin hQ hind hq e hBs hN hker hBstar g hg hcomm hg3
  obtain ⟨C, hpos, -, hplus, -⟩ :=
    exists_omCoord_of_selfCent_two (K := ZMod 2) (V := ι → ZMod 2) (Q := q)
      (by simp) hnd hdim ha hEΩ hE hsc
  refine ⟨C, ?_, hplus⟩
  rcases hpos with ⟨hW, hs⟩ | ⟨hs, hW2, -⟩
  · exact Or.inl ⟨hW, hs⟩
  · refine Or.inr ⟨hs, fun hbot => ?_⟩
    rw [hbot, finrank_bot] at hW2
    omega

theorem native_orth_torus_action_data (hQ : GoodQ Q₀) (hind : OmegaTwoAutInduced Q₀)
    (hq : ⇑q = Q₀) (hnd : (polarBilin q).Nondegenerate) {a : ℕ}
    (hι : Fintype.card ι = 2 * a) (ha : 4 ≤ a) (e : K ≃* StatedOmega Q₀)
    (hBs : IsElemAbelian 3 Bs) (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hker : Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers z)
    (hBstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hNK : Subgroup.normalizer (Bs : Set G) ⊓ Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.normalizer (K : Set G))
    (C : ChoiceTwoOm.OmCoord (ZMod 2) q (orthTorusLin hq e Bs)) :
    ∃ (s : ℕ) (T : Multiplicative (Fin s → ZMod 3) →* G), s = C.s ∧ Function.Injective T ∧
      T.range = Bs ⊓ K ∧
      (∀ g ∈ Subgroup.normalizer (Bs : Set G) ⊓ Subgroup.centralizer ({z} : Set G),
        ∃ (π : Equiv.Perm (Fin s)) (η : Fin s → Bool), ∀ f,
          g * T (Multiplicative.ofAdd f) * g⁻¹ =
            T (Multiplicative.ofAdd (ChoiceTwo.moveExp π η f))) ∧
      (C.W0 ≠ ⊥ → ∀ (π : Equiv.Perm (Fin s)) (η : Fin s → Bool),
        ∃ g ∈ Subgroup.normalizer (Bs : Set G) ⊓ Subgroup.centralizer ({z} : Set G),
          ∀ f, g * T (Multiplicative.ofAdd f) * g⁻¹ =
            T (Multiplicative.ofAdd (ChoiceTwo.moveExp π η f))) := by
  classical
  let ε : K ≃* CFSG.RankThree.Classical2.orthDerived q := e.trans (statedOmegaEquivDerived hq)
  let ψ : CFSG.RankThree.Classical2.orthDerived q →* G := K.subtype.comp ε.symm.toMonoidHom
  have hψ : Function.Injective ψ := fun x y h => ε.symm.injective (Subtype.ext h)
  have hAsub : orthTorusLin hq e Bs =
      ((Bs.subgroupOf K).map (e.trans (statedOmegaEquivDerived hq)).toMonoidHom).map
        (CFSG.RankThree.Classical2.orthDerived q).subtype := rfl
  have hAle : orthTorusLin hq e Bs ≤ CFSG.RankThree.Classical2.orthDerived q := by
    intro c hc
    rw [hAsub] at hc
    obtain ⟨d, -, rfl⟩ := Subgroup.mem_map.mp hc
    exact d.property
  let tor : Multiplicative (Fin C.s → ZMod 3) →* CFSG.RankThree.Classical2.orthDerived q :=
    { toFun := fun f => ⟨C.tor (Multiplicative.toAdd f), hAle (C.tor_mem _)⟩
      map_one' := Subtype.ext C.tor_zero
      map_mul' := fun f f' => Subtype.ext (C.tor_add _ _) }
  let T : Multiplicative (Fin C.s → ZMod 3) →* G := ψ.comp tor
  have hT : Function.Injective T := by
    intro f f' h
    exact Multiplicative.toAdd.injective (C.tor_injective (congrArg Subtype.val (hψ h)))
  have hmem : ∀ Y : CFSG.RankThree.Classical2.orthDerived q,
      (Y : (ι → ZMod 2) ≃ₗ[ZMod 2] (ι → ZMod 2)) ∈ orthTorusLin hq e Bs ↔ ψ Y ∈ Bs := by
    intro Y
    rw [hAsub]
    constructor
    · intro hY
      obtain ⟨d, hd, hYd⟩ := Subgroup.mem_map.mp hY
      obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hd
      rw [show Y = ε k from Subtype.ext hYd.symm]
      change ((ε.symm (ε k) : K) : G) ∈ Bs
      rw [MulEquiv.symm_apply_apply]
      exact Subgroup.mem_subgroupOf.mp hk
    · intro hY
      exact Subgroup.mem_map.mpr ⟨Y, Subgroup.mem_map.mpr
        ⟨ε.symm Y, Subgroup.mem_subgroupOf.mpr hY, ε.apply_symm_apply Y⟩, rfl⟩
  have hrange : T.range = Bs ⊓ K := by
    ext b
    constructor
    · rintro ⟨f, rfl⟩
      exact ⟨(hmem (tor f)).mp (C.tor_mem (Multiplicative.toAdd f)),
        (ε.symm (tor f)).property⟩
    · intro hb
      have hbX : ε ⟨b, hb.2⟩ ∈ (Bs.subgroupOf K).map ε.toMonoidHom :=
        Subgroup.mem_map_of_mem ε.toMonoidHom (Subgroup.mem_subgroupOf.mpr hb.1)
      have hbA : (ε ⟨b, hb.2⟩ : (ι → ZMod 2) ≃ₗ[ZMod 2] (ι → ZMod 2)) ∈
          orthTorusLin hq e Bs := by
        rw [hAsub]
        exact Subgroup.mem_map_of_mem _ hbX
      obtain ⟨f, hf⟩ := C.mem_tor _ hbA
      refine ⟨Multiplicative.ofAdd f, ?_⟩
      have hfk : tor (Multiplicative.ofAdd f) = ε ⟨b, hb.2⟩ := Subtype.ext hf
      change ψ (tor (Multiplicative.ofAdd f)) = b
      rw [hfk]
      change ((ε.symm (ε ⟨b, hb.2⟩) : K) : G) = b
      simp
  refine ⟨C.s, T, rfl, hT, hrange, ?_, ?_⟩
  · intro g hg
    let α : MulAut (CFSG.RankThree.Classical2.orthDerived q) :=
      MulAut.congr ε (K.normalizerMonoidHom ⟨g, hNK hg⟩)
    obtain ⟨h, hh⟩ := exists_linEquiv_of_mulAut_orthDerived hq hind α
    have hconj : ∀ Y : CFSG.RankThree.Classical2.orthDerived q,
        ψ (α Y) = g * ψ Y * g⁻¹ := by
      intro Y
      change ((ε.symm (α Y) : K) : G) = g * ((ε.symm Y : K) : G) * g⁻¹
      simp only [α, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
      exact Subgroup.normalizerMonoidHom_apply_apply_coe K ⟨g, hNK hg⟩ (ε.symm Y)
    have hα : ∀ f : Fin C.s → ZMod 3,
        ((α (tor (Multiplicative.ofAdd f)) : CFSG.RankThree.Classical2.orthDerived q) :
          (ι → ZMod 2) ≃ₗ[ZMod 2] (ι → ZMod 2)) ∈ orthTorusLin hq e Bs := by
      intro f
      refine (hmem (α (tor (Multiplicative.ofAdd f)))).mpr ?_
      rw [hconj]
      exact (Subgroup.mem_normalizer_iff.mp hg.1 _).mp
        ((hmem (tor (Multiplicative.ofAdd f))).mp (C.tor_mem f))
    have hnorm : ∀ c ∈ orthTorusLin hq e Bs, h * c * h⁻¹ ∈ orthTorusLin hq e Bs := by
      intro c hc
      obtain ⟨f, hf⟩ := C.mem_tor c hc
      have hc' : h * C.tor f * h⁻¹ ∈ orthTorusLin hq e Bs := by
        rw [show h * C.tor f * h⁻¹ =
          ((α (tor (Multiplicative.ofAdd f)) :
            CFSG.RankThree.Classical2.orthDerived q) :
            (ι → ZMod 2) ≃ₗ[ZMod 2] (ι → ZMod 2))
          from (hh (tor (Multiplicative.ofAdd f))).symm]
        exact hα f
      rw [← hf]
      exact hc'
    obtain ⟨π, η, hπη⟩ := ChoiceTwoOm.OmCoord.exists_moveExp_of_conj C hnorm
    refine ⟨π, η, fun f => ?_⟩
    have hαf : α (tor (Multiplicative.ofAdd f)) =
        tor (Multiplicative.ofAdd (ChoiceTwo.moveExp π η (Multiplicative.toAdd f))) := by
      apply Subtype.ext
      rw [show ((α (tor (Multiplicative.ofAdd f)) : CFSG.RankThree.Classical2.orthDerived q) :
        (ι → ZMod 2) ≃ₗ[ZMod 2] (ι → ZMod 2)) =
        h * (tor (Multiplicative.ofAdd f) : (ι → ZMod 2) ≃ₗ[ZMod 2] (ι → ZMod 2)) * h⁻¹
        from hh (tor (Multiplicative.ofAdd f))]
      exact hπη _
    calc g * T (Multiplicative.ofAdd f) * g⁻¹
        = ψ (α (tor (Multiplicative.ofAdd f))) := (hconj _).symm
      _ = T (Multiplicative.ofAdd (ChoiceTwo.moveExp π η (Multiplicative.toAdd f))) := by
          rw [hαf]
          rfl
  · intro hW0 π η
    obtain ⟨w, hwΩ, hw⟩ :=
      (ChoiceTwoOm.OmCoord.exists_omega_conj_iff_of_W0_ne_bot hnd C hW0
        (ChoiceTwo.moveExp π η)).mpr ⟨π, η, rfl⟩
    have hwD : w ∈ CFSG.RankThree.Classical2.orthDerived q := by
      rw [← omegaGroup_eq_orthDerived_of_card hnd hι ha]
      exact hwΩ
    let g : G := ψ ⟨w, hwD⟩
    have hgK : g ∈ K := (ε.symm ⟨w, hwD⟩).property
    have hgT : ∀ f : Fin C.s → ZMod 3, g * T (Multiplicative.ofAdd f) * g⁻¹ =
        T (Multiplicative.ofAdd (ChoiceTwo.moveExp π η f)) := by
      intro f
      have h1 : (⟨w, hwD⟩ * tor (Multiplicative.ofAdd f) * ⟨w, hwD⟩⁻¹ :
          CFSG.RankThree.Classical2.orthDerived q) =
          tor (Multiplicative.ofAdd (ChoiceTwo.moveExp π η f)) := by
        apply Subtype.ext
        show w * C.tor f * w⁻¹ = C.tor (ChoiceTwo.moveExp π η f)
        exact hw f
      change ψ ⟨w, hwD⟩ * ψ (tor (Multiplicative.ofAdd f)) * (ψ ⟨w, hwD⟩)⁻¹ =
        ψ (tor (Multiplicative.ofAdd (ChoiceTwo.moveExp π η f)))
      rw [← map_inv, ← map_mul, ← map_mul, h1]
    have hzK : z ∈ Subgroup.centralizer (K : Set G) := by
      have hz : z ∈ Bs ⊓ Subgroup.centralizer (K : Set G) := by
        rw [hker]
        exact Subgroup.mem_zpowers z
      exact hz.2
    have hgc : g ∈ Subgroup.centralizer ({z} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr ((Subgroup.mem_centralizer_iff.mp hzK) g hgK)
    have hzg : z ∈ Subgroup.centralizer ({g} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_singleton_iff.mp hgc).symm
    have hgZ : g ∈ Subgroup.normalizer (Subgroup.zpowers z : Set G) := by
      apply CFSG.LocalAnalysis.ComponentInitial.mem_normalizer_of_forall_conj_mem
      intro t ht
      have hgt : g * t = t * g :=
        (Subgroup.mem_centralizer_singleton_iff.mp ((Subgroup.zpowers_le.mpr hzg) ht)).symm
      rw [hgt, mul_assoc, mul_inv_cancel, mul_one]
      exact ht
    have hgE : g ∈ Subgroup.normalizer (T.range : Set G) := by
      apply CFSG.LocalAnalysis.ComponentInitial.mem_normalizer_of_forall_conj_mem
      rintro t ⟨f, rfl⟩
      exact ⟨Multiplicative.ofAdd (ChoiceTwo.moveExp π η (Multiplicative.toAdd f)),
        (hgT (Multiplicative.toAdd f)).symm⟩
    have hsplit : Bs = Subgroup.zpowers z ⊔ T.range := by
      rw [hrange]
      exact bstar_eq_zpowers_sup_inf_of_native_orth hQ hind e hBs hN hker hBstar
    have hgBs : g ∈ Subgroup.normalizer (Bs : Set G) := by
      rw [hsplit]
      exact (Subgroup.normalizer_inf_normalizer_le_normalizer_sup
        (Subgroup.zpowers z) T.range) ⟨hgZ, hgE⟩
    exact ⟨g, ⟨hgBs, hgc⟩, hgT⟩

omit [Finite G] in
theorem rank_eq_of_native_orth (hQ : GoodQ Q₀) (hind : OmegaTwoAutInduced Q₀)
    (e : K ≃* StatedOmega Q₀) (hBs : IsElemAbelian 3 Bs) {n : ℕ} (hcard : Nat.card Bs = 3 ^ n)
    (hz : z ∈ Bs) (hz1 : z ≠ 1) (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hker : Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers z)
    (hBstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs) {s : ℕ}
    (T : Multiplicative (Fin s → ZMod 3) →* G) (hT : Function.Injective T)
    (hrange : T.range = Bs ⊓ K) : s + 1 = n := by
  let Z := Subgroup.zpowers z
  let E := Bs ⊓ K
  have hsplit : Bs = Z ⊔ E :=
    bstar_eq_zpowers_sup_inf_of_native_orth hQ hind e hBs hN hker hBstar
  have hZK : Z ≤ Subgroup.centralizer (K : Set G) := by
    change Subgroup.zpowers z ≤ Subgroup.centralizer (K : Set G)
    rw [← hker]
    exact inf_le_right
  have hcomm : ∀ x ∈ Z, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    ((Subgroup.mem_centralizer_iff.mp (hZK hx)) y hy.2).symm
  have hcenter : Subgroup.center K = ⊥ := by
    apply Subgroup.eq_bot_of_card_eq
    rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv,
      center_statedOmega_eq_bot_of_goodQ hQ, Subgroup.card_bot]
  have hdisj : Z ⊓ E = ⊥ := by
    refine le_antisymm (fun x hx => ?_) bot_le
    have hmem : (⟨x, hx.2.2⟩ : K) ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      exact fun k => Subtype.ext ((Subgroup.mem_centralizer_iff.mp (hZK hx.1)) k k.property)
    rw [hcenter, Subgroup.mem_bot] at hmem
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hmem)
  have hprod : Nat.card Bs = Nat.card Z * Nat.card E := by
    calc
      Nat.card Bs = Nat.card (Z ⊔ E : Subgroup G) :=
        congrArg (fun H : Subgroup G => Nat.card H) hsplit
      _ = Nat.card (Z × E) :=
        (Nat.card_congr (CFSG.GH74.E2.prodSupEquiv Z E hcomm hdisj).toEquiv).symm
      _ = _ := Nat.card_prod Z E
  have hEcard : Nat.card E = 3 ^ s := by
    rw [show E = T.range from hrange.symm,
      ← Nat.card_congr (MonoidHom.ofInjective hT).toEquiv]
    change Nat.card (Fin s → ZMod 3) = 3 ^ s
    simp only [Nat.card_fun, Nat.card_fin, Nat.card_zmod]
  have hzord : orderOf z = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime (hBs.2 z hz) hz1
  have hZ : Nat.card Z = 3 := by rw [Nat.card_zpowers, hzord]
  have hp : 3 ^ n = 3 ^ (s + 1) := by
    simpa only [hcard, hZ, hEcard, pow_succ, Nat.mul_comm] using hprod
  exact (Nat.pow_right_injective (by decide : 1 < 3) hp).symm

end CFSG.StandardType.FrameRoute

end
