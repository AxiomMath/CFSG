module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem10Stmts
public import CFSG.Quasithin.Vol2.Ch12Sec2Action
public import CFSG.Quasithin.Vol2.Ch12Sec2Ident
public import CFSG.Quasithin.Vol2.Ch3Sec2Lem328Iso
public import CFSG.Quasithin.H13.VolIAutSLFive
public import CFSG.Quasithin.SteinbergCBAlternatingAut
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3AutIso
public import CFSG.Quasithin.Recognition.CertU33AutBound
public import CFSG.Quasithin.Recognition.CertU33Simple
public import CFSG.Timmesfeld.Final.PSU33
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryTrace
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setting
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerNilp
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerQuad
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerSect1
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesExtraComponents
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Permutation.AlternatingAutomorphism
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.F2Equiv
public import CFSG.Quasithin.Vol2.Ch12Sec2Setting
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.ComponentClassification.OuterAutomorphisms

namespace Out1222

@[expose] def AutFourthPowerInner (S : Type*) [Group S] : Prop :=
  ∀ α : MulAut S, α ^ 4 ∈ inner S

theorem AutFourthPowerInner.of_mulEquiv {S T : Type*} [Group S] [Group T] (e : S ≃* T)
    (h : AutFourthPowerInner T) : AutFourthPowerInner S := by
  intro α
  have h1 : MulAut.congr e (α ^ 4) ∈ inner T := by
    rw [map_pow]
    exact h _
  rw [← inner_map_congr e] at h1
  exact (Subgroup.mem_map_iff_mem (f := (MulAut.congr e).toMonoidHom)
    (MulAut.congr e).injective).mp h1

theorem autFourthPowerInner_of_index_dvd {S : Type*} [Group S] (h : (inner S).index ∣ 4) :
    AutFourthPowerInner S := by
  intro α
  obtain ⟨m, hm⟩ := h
  rw [hm, pow_mul]
  exact (inner S).pow_mem ((inner S).pow_index_mem α) m

theorem autFourthPowerInner_of_card_le {X : Type*} [Group X] [Finite X]
    (hZ : Subgroup.center X = ⊥) (hA : Nat.card (MulAut X) ≤ 2 * Nat.card X) :
    AutFourthPowerInner X := by
  have hinj : Function.Injective (MulAut.conj : X →* MulAut X) := by
    refine (MonoidHom.ker_eq_bot_iff _).mp ((Subgroup.eq_bot_iff_forall _).2 fun g hg => ?_)
    have hcen : g ∈ Subgroup.center X := by
      refine Subgroup.mem_center_iff.mpr fun y => ?_
      have h1 := congrArg (fun φ : MulAut X => φ y) (MonoidHom.mem_ker.mp hg)
      simp only [MulAut.conj_apply, MulAut.one_apply] at h1
      calc y * g = (g * y * g⁻¹) * g := by rw [h1]
        _ = g * y := by group
    rwa [hZ, Subgroup.mem_bot] at hcen
  have hinn : Nat.card (inner X) = Nat.card X :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have : Finite (MulAut X) :=
    Finite.of_injective (fun f : MulAut X => (f : X → X)) DFunLike.coe_injective
  have hidx := (inner X).index_mul_card
  rw [hinn] at hidx
  have hpos : 0 < Nat.card X := Nat.card_pos
  have hle : (inner X).index ≤ 2 := by
    have h1 : (inner X).index * Nat.card X ≤ 2 * Nat.card X := hidx ▸ hA
    exact Nat.le_of_mul_le_mul_right h1 hpos
  have hne : (inner X).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  apply autFourthPowerInner_of_index_dvd
  obtain h | h : (inner X).index = 1 ∨ (inner X).index = 2 := by omega
  · rw [h]
    exact one_dvd _
  · rw [h]
    norm_num

theorem center_eq_bot_of_isSimpleGroup {X : Type*} [Group X] [IsSimpleGroup X]
    (hp : ¬ (Nat.card X).Prime) : Subgroup.center X = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
  · exact h
  · exfalso
    have : IsMulCommutative X :=
      ⟨⟨fun a b => (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top a) b).symm⟩⟩
    exact hp (Group.is_simple_iff_prime_card.mp ‹_›)

theorem pow_four_mem_sup_centralizer {Γ : Type*} [Group Γ] {A : Subgroup Γ}
    (h : AutFourthPowerInner ↥A) {x : Γ} (hx : x ∈ Subgroup.normalizer (A : Set Γ)) :
    x ^ 4 ∈ A ⊔ Subgroup.centralizer (A : Set Γ) := by
  obtain ⟨a, ha⟩ := h (A.normalizerMonoidHom ⟨x, hx⟩)
  have key : ∀ b : ↥A, (a : Γ) * b * (a : Γ)⁻¹ = x ^ 4 * b * (x ^ 4)⁻¹ := by
    intro b
    have h1 := congrArg (fun f : MulAut ↥A => ((f b : ↥A) : Γ)) ha
    simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h1
    rw [h1, ← map_pow]
    rfl
  have hc : (a : Γ)⁻¹ * x ^ 4 ∈ Subgroup.centralizer (A : Set Γ) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have h2 := key ⟨b, hb⟩
    calc b * ((a : Γ)⁻¹ * x ^ 4) = (a : Γ)⁻¹ * ((a : Γ) * b * (a : Γ)⁻¹) * x ^ 4 := by group
      _ = (a : Γ)⁻¹ * (x ^ 4 * b * (x ^ 4)⁻¹) * x ^ 4 := by rw [h2]
      _ = ((a : Γ)⁻¹ * x ^ 4) * b := by group
  have := Subgroup.mul_mem_sup a.2 hc
  rwa [mul_inv_cancel_left] at this

theorem center_sl_zmod_two_eq_bot (n : ℕ) [NeZero n] :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) = ⊥ := by
  refine center_sl_eq_bot fun r hr => ?_
  have h01 : ∀ s : ZMod 2, s = 0 ∨ s = 1 := by decide
  rcases h01 r with rfl | rfl
  · rw [zero_pow (NeZero.ne n)] at hr
    exact absurd hr (by decide)
  · rfl

theorem card_mulAut_sl_zmod_two_le {n : ℕ} (hn : 3 ≤ n) :
    Nat.card (MulAut (Matrix.SpecialLinearGroup (Fin n) (ZMod 2))) ≤
      2 * Nat.card (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) := by
  have : NeZero n := ⟨by omega⟩
  rw [Nat.card_congr (MulAut.congr (QuasithinUnique.Setup.Family.projEquiv n)).toEquiv,
    ← VolI.card_GL_zmod_two_eq]
  exact VolI.card_mulAut_projectiveSL_two_le hn

theorem autFourthPowerInner_sl_zmod_two {n : ℕ} (hn : 3 ≤ n) :
    AutFourthPowerInner (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) := by
  have : NeZero n := ⟨by omega⟩
  exact autFourthPowerInner_of_card_le (center_sl_zmod_two_eq_bot n)
    (card_mulAut_sl_zmod_two_le hn)

theorem autFourthPowerInner_alternatingGroup {n : ℕ} (h5 : 5 ≤ n) (h8 : n ≤ 8) :
    AutFourthPowerInner (alternatingGroup (Fin n)) := by
  apply autFourthPowerInner_of_index_dvd
  by_cases h6 : n = 6
  · subst h6
    exact dvd_of_eq QuasithinUnique.Setup.X3Aut.index_inner_alt6
  · exact (SteinbergCB.index_inner_dvd_two (by omega)).trans (by norm_num)

theorem autFourthPowerInner_u33Pres :
    AutFourthPowerInner U33G := by
  have : Finite U33G := u33Pres_finite_card_le.1
  have : IsSimpleGroup U33G := isSimpleGroup_u33Pres
  have hcard : Nat.card U33G = 6048 := card_u33Pres
  refine autFourthPowerInner_of_card_le (center_eq_bot_of_isSimpleGroup ?_) ?_
  · rw [hcard]
    norm_num
  · rw [hcard]
    exact card_mulAut_u33Pres_le.trans (by norm_num)

theorem autFourthPowerInner_of_centerQuotient {Q : Type*} [Group Q] [Group.IsPerfect Q]
    (h : AutFourthPowerInner (Q ⧸ Subgroup.center Q)) : AutFourthPowerInner Q := by
  intro α
  have h1 : CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom Q (α ^ 4) ∈
      inner (Q ⧸ Subgroup.center Q) := by
    rw [map_pow]
    exact h _
  have h2 : centerQuotientOuterHom Q (QuotientGroup.mk (α ^ 4)) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr h1
  have h3 : (QuotientGroup.mk (α ^ 4) : Outer Q) = 1 :=
    centerQuotient_outer_injective Q (h2.trans (map_one _).symm)
  exact (QuotientGroup.eq_one_iff _).mp h3

theorem autFourthPowerInner_threeA6 {Q : Type*} [Group Q] (hQ : CFSG.IsQuasisimple Q)
    (e : Q ⧸ Subgroup.center Q ≃* alternatingGroup (Fin 6)) : AutFourthPowerInner Q := by
  have : Group.IsPerfect Q := hQ.1
  exact autFourthPowerInner_of_centerQuotient
    (AutFourthPowerInner.of_mulEquiv e
      (autFourthPowerInner_alternatingGroup (by norm_num) (by norm_num)))

section Ident

variable {G : Type} [Group G] {L V : Subgroup G}

theorem nonempty_autOn_mulEquiv_of_surjective {S : Type*} [Group S]
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (φ : ↥L →* S) (hφ : Function.Surjective φ)
    (hker : φ.ker = (Subgroup.centralizer (V : Set G)).subgroupOf L) :
    Nonempty (↥(autOn L V) ≃* S) :=
  ⟨(QuotientGroup.quotientKerEquivOfSurjective _ (autOnSurj_surjective hLV)).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq ((ker_autOnSurj hLV).trans hker.symm)).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφ))⟩

theorem nonempty_autOn_mulEquiv_quotient (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hCV : L ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 L) :
    Nonempty (↥(autOn L V) ≃* ↥L ⧸ CFSG.pCore 2 ↥L) := by
  refine nonempty_autOn_mulEquiv_of_surjective hLV (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
    (QuotientGroup.mk'_surjective _) ?_
  rw [QuotientGroup.ker_mk']
  ext l
  rw [Subgroup.mem_subgroupOf]
  constructor
  · intro hl
    have hmem : (l : G) ∈ pCoreOf 2 L := ⟨l, hl, rfl⟩
    rw [← hCV] at hmem
    exact hmem.2
  · intro hl
    have hmem : (l : G) ∈ pCoreOf 2 L := by
      rw [← hCV]
      exact ⟨l.2, hl⟩
    obtain ⟨y, hy, hyl⟩ := hmem
    rwa [← Subtype.ext hyl]

end Ident

end Out1222

section Main

open Out1222

theorem out1222Fact_holds :
    Out1222Fact := by
  intro G _ _ L V _ _ hLV _ _ hO2 hmod x hx
  refine ⟨2, ?_⟩
  by_cases hne : L ≤ Subgroup.centralizer (V : Set G)
  · have hbot : autOn L V = ⊥ := by
      rw [eq_bot_iff]
      intro a ha
      obtain ⟨l, rfl⟩ := (A4.mem_autOn_iff hLV).mp ha
      rw [Subgroup.mem_bot, A4.actionOn_eq_one_iff hLV]
      exact hne l.2
    rw [hbot]
    refine Subgroup.mem_sup_right (Subgroup.mem_centralizer_iff.mpr fun g hg => ?_)
    rw [SetLike.mem_coe, Subgroup.mem_bot] at hg
    rw [hg, one_mul, mul_one]
  · have hA : AutFourthPowerInner ↥(autOn L V) := by
      rcases hmod with ⟨n, hn, ⟨e⟩, -⟩ | ⟨⟨e⟩, -, -⟩ | ⟨⟨e⟩, -, -⟩ |
        ⟨n, h5, h8, ⟨φ, hφs, hφk⟩, -⟩ | ⟨-, φ, hφs, hφk⟩ | ⟨hLie, -⟩ | ⟨hq, -, ⟨e⟩, hCV, -, -⟩
      · have hn3 : 3 ≤ n := by omega
        have := isSimpleGroup_sl_zmodTwo hn3
        obtain ⟨e'⟩ := nonempty_autOn_mulEquiv_of_simple hLV hO2 hne e
        exact .of_mulEquiv e' (autFourthPowerInner_sl_zmod_two hn3)
      · have := isSimpleGroup_sl_zmodTwo (n := 3) le_rfl
        obtain ⟨e'⟩ := nonempty_autOn_mulEquiv_of_simple hLV hO2 hne e
        exact .of_mulEquiv e' (autFourthPowerInner_sl_zmod_two le_rfl)
      · have := isSimpleGroup_sl_zmodTwo (n := 5) (by norm_num)
        obtain ⟨e'⟩ := nonempty_autOn_mulEquiv_of_simple hLV hO2 hne e
        exact .of_mulEquiv e' (autFourthPowerInner_sl_zmod_two (by norm_num))
      · obtain ⟨e'⟩ := nonempty_autOn_mulEquiv_of_surjective hLV φ hφs hφk
        exact .of_mulEquiv e' (autFourthPowerInner_alternatingGroup h5 h8)
      · obtain ⟨e'⟩ := nonempty_autOn_mulEquiv_of_surjective hLV φ hφs hφk
        exact .of_mulEquiv e' (autFourthPowerInner_alternatingGroup (by norm_num) (by norm_num))
      · obtain ⟨e1⟩ := CFSG.Timmesfeld.nonempty_mulEquiv_PSU3_of_lieModel hLie
        obtain ⟨e2⟩ := u33Pres_mulEquiv_PSU3
        have : IsSimpleGroup U33G := isSimpleGroup_u33Pres
        obtain ⟨e'⟩ := nonempty_autOn_mulEquiv_of_simple hLV hO2 hne (e1.trans e2.symm)
        exact .of_mulEquiv e' autFourthPowerInner_u33Pres
      · obtain ⟨e'⟩ := nonempty_autOn_mulEquiv_quotient hLV hCV
        exact .of_mulEquiv e' (autFourthPowerInner_threeA6 hq e)
    exact pow_four_mem_sup_centralizer hA hx

end Main

end CFSG.Quasithin.H13
