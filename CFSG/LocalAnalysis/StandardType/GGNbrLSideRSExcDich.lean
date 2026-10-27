module

public import CFSG.LocalAnalysis.StandardType.GGNbrLSideRSExcDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrLSideTransport
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Inner
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTamePrime
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Assembly
public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20Alt
public import CFSG.HardMathSupport.Solomon.Coordinator.L3C143AltMain
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Basic
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Certs
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang
public import CFSG.HardMathSupport.Solomon.Coordinator.ONCAutSix
public import CFSG.HardMathSupport.Solomon.Coordinator.ONNotIso
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Down
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma43Rest
public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop22
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec3Statements
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.Input252
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6D62
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6E66
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangFrame
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.Quasithin.Background.A3Structure319
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.F9FiveStruct
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.F9Geometry
public import CFSG.Quasithin.Background.GoldschmidtRankOneFacts
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.EmptyFaithful.S1421Defs
public import CFSG.Quasithin.EmptyFaithful.S142Statements
public import CFSG.Quasithin.H13.A5S1326
public import CFSG.Quasithin.H13.A5Top
public import CFSG.Quasithin.H13.J4Order
public import CFSG.Quasithin.Vol2.Ch11SecAFacts02
public import CFSG.Quasithin.Vol2.Ch11SecAFacts03
public import CFSG.Quasithin.Vol2.Ch11StatementsB
public import CFSG.Quasithin.Vol2.Ch11StatementsC
public import Certificates.Certificate10050
public import Certificates.Certificate13659
public import Certificates.Certificate13660
public import Certificates.Certificate8117
public import Certificates.Kernel.J4Count.FixCE

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.Blueprint.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.LangTorus

theorem ggNbrLSide_induces_of_injHom {R G : Type} [Group R] [Group G] (ι : R →* G)
    (hι : Function.Injective ι) {J : Subgroup R} {J' : Subgroup G} (hJ : J.map ι = J')
    (ψ : MulAut R) (y : G) (hy : ∀ r, ι (ψ r) = y * ι r * y⁻¹)
    (α : MulAut (↥J ⧸ Subgroup.center ↥J)) (hα : GGNbrLSideInduces ψ J α) :
    ∃ e : ↥J ⧸ Subgroup.center ↥J ≃* ↥J' ⧸ Subgroup.center ↥J',
      GGNbrLSideInduces (MulAut.conj y) J' (MulAut.congr e α) := by
  let ιJ : ↥J ≃* ↥J' :=
    (Subgroup.equivMapOfInjective J ι hι).trans (MulEquiv.subgroupCongr hJ)
  have hιJ : ∀ j : ↥J, (ιJ j : G) = ι (j : R) := fun j => rfl
  let e : ↥J ⧸ Subgroup.center ↥J ≃* ↥J' ⧸ Subgroup.center ↥J' :=
    QuotientGroup.congr _ _ ιJ (Subgroup.map_center_eq ιJ)
  have he : ∀ j : ↥J, e (QuotientGroup.mk j) = QuotientGroup.mk (ιJ j) :=
    fun j => QuotientGroup.congr_mk _ _ ιJ (Subgroup.map_center_eq ιJ) j
  refine ⟨e, ?_⟩
  intro j₁
  let j : ↥J := ιJ.symm j₁
  obtain ⟨j', hj'1, hj'2⟩ := hα j
  have hj : ιJ j = j₁ := by
    show ιJ (ιJ.symm j₁) = j₁
    exact MulEquiv.apply_symm_apply ιJ j₁
  have hjj : (j₁ : G) = ι (j : R) := by
    have h := hιJ (ιJ.symm j₁)
    simpa [j, MulEquiv.apply_symm_apply] using h
  have h1 : e.symm (QuotientGroup.mk j₁) = QuotientGroup.mk j := by
    have hmk : QuotientGroup.mk j₁ = e (QuotientGroup.mk j) := by rw [he j, hj]
    rw [hmk, MulEquiv.symm_apply_apply]
  refine ⟨ιJ j', ?_, ?_⟩
  · rw [hιJ j', hj'1, hy j, hjj, MulAut.conj_apply]
  · rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, h1, hj'2, he j']

theorem ggNbrLSideDich_of_transport
    {lab : LargeEvenLabel} {τ : Tag} {R : Type} [Group R] {I : Set (MulAut R)}
    (hLD : GGNbrLSideRSExcLangDich) (hG2 : τ = .G2 → 4 ≤ 2 ^ lab.n)
    (hrank : ggNbrLSideRank lab = τ.rank) (hT : GGNbrLSideRSExcTransport τ I (2 ^ lab.n)) :
    GGNbrLSideDich lab I := by
  intro φ hφ ψ hψ hφ1 hφ3 hψ3 hcomm J hJ Q hQ4 hQ3 hF α hα
  obtain ⟨F, _, _, hFQ, ⟨eF⟩⟩ := hF
  obtain ⟨L, _, _, p₀, S, a, e, y, hL2, hq, hT', ha3, hd1, hyM, hyC, hy3, hφe, hψe⟩ :=
    hT φ hφ ψ hψ hφ1 hφ3 hψ3 hcomm
  let ι : R →* ModGL τ L := S.Γ.subtype.comp e.toMonoidHom
  have hι : Function.Injective ι := S.Γ.subtype_injective.comp e.injective
  have hrange : ι.range = S.Γ := by
    refine le_antisymm ?_ ?_
    · rintro x ⟨r, rfl⟩
      exact (e r).2
    · intro x hx
      exact ⟨e.symm ⟨x, hx⟩, by simp [ι]⟩
  haveI : Finite ↥S.Γ := S.finite_Γ
  haveI : Finite R := Finite.of_injective e e.injective
  have hβ : ∀ c : R, ι (φ c) = rootDiagUnit τ a * ι c * (rootDiagUnit τ a)⁻¹ :=
    fun c => hφe c
  have h2L : ((2 : ℕ) : L) = 0 := by simpa using hL2
  have h3L : ((3 : ℕ) : L) = 1 := by
    rw [show ((3 : ℕ) : L) = ((2 : ℕ) : L) + 1 by norm_num, h2L, zero_add]
  have hpL : ((3 : ℕ) : L) ≠ 0 := by rw [h3L]; exact one_ne_zero
  have hsmall : τ = .G2 → 5 ≤ (3 : ℕ) ∨ 4 ≤ S.D.q :=
    fun h => Or.inr (by rw [hq]; exact hG2 h)
  have hTame :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.langSetup_hTame_of_prime
      S Nat.prime_three hpL hsmall hT' ha3 hd1
  obtain ⟨i, hqs, hJi⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.components_of_langSetup
      S Nat.prime_three ι hι hrange φ hβ hT' ha3 hd1 hTame hJ
  obtain ⟨e', hind⟩ := ggNbrLSide_induces_of_injHom ι hι hJi ψ y hψe α hα
  have hPSL3 : GGNbrLSideRSExcPSL3 S a i Q :=
    ⟨hT', ha3, hd1, hqs, hQ4, hQ3, F, inferInstance, inferInstance, hFQ,
      ⟨e'.symm.trans eF⟩⟩
  rcases hLD τ L p₀ S hL2 lab.n hq a i Q hPSL3 y hyM hyC hy3 (MulAut.congr e' α) hind with
    h | h
  · exact Or.inl (ggInnDiagPSL3_of_congr e' h)
  · right
    have h' : (Even lab.n ∧ 6 ≤ τ.rank) ∨ (Odd lab.n ∧ 12 ≤ τ.rank) := by
      simpa only [GGNbrLSideLargeRank, ggNbrLSideRank] using h
    simpa only [GGNbrLSideLargeRank, hrank] using h'

end CFSG.StandardType

end
