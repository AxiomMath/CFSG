module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2Toral
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2CoverData
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1TransferData
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1DTransport
public import CFSG.LocalAnalysis.StandardType.GGCentInnerDiagModel
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2OmegaSelect
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2OrthogonalSmall
import CFSG.GroupTheory.IsComponentOfMap
public import Certificates.Certificate7050Base

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly
open CFSG.Open (StatedOmega)
open CFSG.StandardType.ClassicalPosition CFSG.StandardType.ClassicalBlocks


@[expose] def Q2OmegaPlusBlockChoice : Prop :=
  ∀ (d : ℕ) (hd4 : 4 ≤ d) (F : Type) [Field F] [Fintype F] [CharP F 2]
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hpd : p ∣ d) (hpF : p ∣ Nat.card F - 1)
    (Φ : QuadraticForm F (Fin d ⊕ Fin d → F))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate)
    (hΦcoe : ⇑Φ = LargeEvenQPlus F d)
    (s : ↥(StatedOmega ⇑Φ)) (hsord : orderOf s = p)
    (C : Subgroup ↥(StatedOmega ⇑Φ))
    (hC : CFSG.Open.IsComponentOf C (Subgroup.centralizer ({s} : Set ↥(StatedOmega ⇑Φ))))
    (K : Type) [Field K] [Finite K] (hKcard : Nat.card K = Nat.card F)
    (ξ : ↥C ⧸ Subgroup.center ↥C ≃* LargeEvenProj (LargeEvenSLGroup (Fin d) K)),
    ∃ (ε : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) F)
      (hε : IsPrimAdjIdemIn (RingHom.id F)
        (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Φ))
        (Algebra.adjoin F (Units.val '' ({(s : GL (Fin d ⊕ Fin d) F)} :
          Set (GL (Fin d ⊕ Fin d) F)))) ε)
      (m : ℕ) (E : Type) (_ : Field E) (_ : Finite E) (_ : CharP E 2)
      (e : ↥(glBlockCentralizer (StatedOmega ⇑Φ).subtype
        ({(s : GL (Fin d ⊕ Fin d) F)} : Set (GL (Fin d ⊕ Fin d) F)) ε) ≃* GL (Fin m) E),
      CFSG.Open.IsComponentOf C (glBlockCentralizer (StatedOmega ⇑Φ).subtype
        ({(s : GL (Fin d ⊕ Fin d) F)} : Set (GL (Fin d ⊕ Fin d) F)) ε) ∧
      m = d ∧ Nat.card E = Nat.card F

theorem q2OmegaPlusBlockChoice_holds : Q2OmegaPlusBlockChoice := by
  unfold Q2OmegaPlusBlockChoice
  intro d hd4 F instF instFF instChar p hp hp2 hpd hpF Φ hΦ hΦcoe s hsord C hC K instK instKFin
    hKcard ξ
  have h8 : 8 ≤ Fintype.card (Fin d ⊕ Fin d) := by
    simp
    omega
  obtain ⟨P, ε, m, E, hEfield, hEfin, hEchar, hrest⟩ :=
    exists_selected_glBlock_omegaPlus_of_cardEq (K := K) Φ hΦ h8 hp hp2 (by omega) hpd hpF s hsord
      C hC hKcard ξ
  dsimp only at hrest
  obtain ⟨hεP, hεall, hsup, hCε, hmd, hEcard, ⟨e⟩, -, -⟩ := hrest
  exact ⟨ε, hεall ε hεP, m, E, hEfield, hEfin, hEchar, e, hCε, hmd, hEcard⟩

theorem q2Plus_actor_mem {G : Type} [Group G] {Bs L : Subgroup G}
    {R : Type} [Group R] (θ : ↥L ⧸ Subgroup.center ↥L ≃* R)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) {I : Set (MulAut R)}
    (hact : ∀ b ∈ Bs, ∃ φ ∈ I,
      LargeEvenInduces θ (fun l l' : ↥L => (l' : G) = b⁻¹ * l * b) φ)
    (b : ↥Bs) : ggInducedAut θ (ggGamma L hN b) ∈ I := by
  obtain ⟨φ, hφI, hφ⟩ := hact ((b : G)⁻¹) (Bs.inv_mem b.2)
  have hEq : ggInducedAut θ (ggGamma L hN b) = φ := by
    ext r
    obtain ⟨z, rfl⟩ := θ.surjective r
    induction z using QuotientGroup.induction_on with
    | H l =>
      rw [ggInducedAut_apply]
      exact (hφ l (ggGamma L hN b l) (by
        dsimp only
        rw [ggGamma_coe]
        group)).symm
  rw [hEq]
  exact hφI

theorem q2_orthogonalPlus_high_of_blockChoice (hsel : Q2OmegaPlusBlockChoice)
    (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J : Subgroup G) (hcfg : GGConfig p B Bs x L D J) (hInner : GGInnerDiagOn Bs L)
    (hN : Bs ≤ Subgroup.normalizer (J : Set G)) (d : ℕ) (K : Type) [Field K] [Finite K]
    (θ : ↥J ⧸ Subgroup.center ↥J ≃* LargeEvenProj (LargeEvenSLGroup (Fin d) K))
    (hpd : p ∣ d) (hpq : p ∣ Nat.card K - 1)
    (hplus : GGInnerDiagOnLab
      (fun p lab => q2RowFits .orthogonalPlus p d (Nat.card K) lab) p Bs L)
    (h4 : 4 ≤ d) :
    IsMulCommutative
      ((((ggBsAut hN).range).map (kgInducedAut θ)).comap (TableB.linConjAut (Fin d) K)) := by
  classical
  unfold Q2OmegaPlusBlockChoice at hsel
  unfold GGInnerDiagOnLab at hplus
  obtain ⟨hperfL, lab, hlab, hraw⟩ := hplus
  rcases lab with ⟨tag, rank, n⟩
  obtain ⟨R0, hR0, I0, F0, hQ0⟩ := largeEvenRawDatum_exists hraw
  letI : Group R0 := hR0
  obtain ⟨-, -, θ0, hP0⟩ := hQ0
  have htag : tag = .D := hP0.1.2.2.2.2.1
  subst tag
  have hrank : rank = d := hP0.1.2.2.2.2.2.1
  subst rank
  dsimp only [LargeEvenRawDatum, CFSG.Assembly.LargeEvenRawDatumLegacy] at hraw
  rw [if_neg (by omega : ¬ d = 3)] at hraw
  unfold LargeEvenRecipeOmegaPlus at hraw
  obtain ⟨F, hFfield, hFfin, hFcard, hQ⟩ := hraw
  letI : Field F := hFfield
  letI : Finite F := hFfin
  haveI : Fintype F := Fintype.ofFinite F
  have hcharF : CharP F 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hFcard
  letI : CharP F 2 := hcharF
  let Φ : QuadraticForm F (Fin d ⊕ Fin d → F) :=
    (TableBOrth.qPlusForm F d).copy (LargeEvenQPlus F d)
      (TableBOrth.coe_qPlusForm d).symm
  have hΦeq : Φ = TableBOrth.qPlusForm F d := by
    dsimp only [Φ]
    exact QuadraticMap.copy_eq _ _ _
  have hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate := by
    rw [hΦeq]
    exact TableBOrth.nondegenerate_qPlusForm d
  have hΦcoe : ⇑Φ = LargeEvenQPlus F d := rfl
  have h8 : 8 ≤ Fintype.card (Fin d ⊕ Fin d) := by simp; omega
  let Qc : (R : Type) → [Group R] → Set (MulAut R) → Set (MulAut R) → Prop :=
    fun R _ I _ =>
      IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
      ∃ θ : ↥L ⧸ Subgroup.center ↥L ≃* R,
        q2RowFits .orthogonalPlus p d (Nat.card K) ⟨.D, d, n⟩ ∧
        LargeEvenSplit p ⟨.D, d, n⟩ ∧
        Bs ≤ Subgroup.normalizer (L : Set G) ∧
        ∀ b ∈ Bs, ∃ φ ∈ I,
          LargeEvenInduces θ (fun l l' : ↥L => (l' : G) = b⁻¹ * l * b) φ
  change Qc (LargeEvenProj (LargeEvenOmega ⇑Φ))
    (LargeEvenInnSet (LargeEvenProj (LargeEvenOmega ⇑Φ))) ∅ at hQ
  obtain ⟨-, -, θL, hP⟩ := hQ
  obtain ⟨hrow, -, hNL, hact⟩ := hP
  have hp : p.Prime := hrow.1
  have hp2 : p ≠ 2 := hrow.2.1
  have hpQ : p ∣ Nat.card K - 1 := hrow.2.2.2.1
  have hn : 2 ≤ n := (q2RowFits_orthogonalPlus_parameters hlab hrow).2.2.2.1
  have hKcard : Nat.card K = 2 ^ n := hrow.2.2.2.2.2.2
  obtain ⟨y, u, -, hyu, huord, -, hJL, hJcomp⟩ := q1_fixed_component_data hcfg hNL
  let A : Subgroup (MulAut (LargeEvenProj (LargeEvenOmega ⇑Φ))) :=
    (ggGamma L hNL).range.map (ggInducedAut θL)
  have hAcomm : IsMulCommutative ↥A := by
    haveI : IsMulCommutative ↥Bs := hcfg.2.1.2.1.1
    haveI : IsMulCommutative ↥(ggGamma L hNL).range := inferInstance
    exact Subgroup.map_isMulCommutative (H := (ggGamma L hNL).range) (ggInducedAut θL)
  have hAI : ∀ a ∈ A, a ∈ LargeEvenInnSet (LargeEvenProj (LargeEvenOmega ⇑Φ)) := by
    intro a ha
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨b, rfl⟩ := hz
    exact q2Plus_actor_mem θL hNL hact b
  have hscal : (LargeEvenScalars (Fin d ⊕ Fin d) F).subgroupOf
      (LargeEvenOmega ⇑Φ) = ⊥ := by
    rw [hΦcoe]
    exact TableBOrth.scalars_subgroupOf_omegaPlus_eq_bot (K := F) (m := d) (by omega)
  have hZ : Subgroup.center ↥(LargeEvenOmega ⇑Φ) = ⊥ := by
    rw [hΦcoe]
    exact CFSG.RankThree.GF2n.Stroth80.center_statedOmega_quadPlus_eq_bot
      (m := d) (K := F) (by omega)
  have hconj : Function.Injective
      (MulAut.conj : ↥(LargeEvenOmega ⇑Φ) →* MulAut ↥(LargeEvenOmega ⇑Φ)) :=
    (MonoidHom.ker_eq_bot_iff _).mp (CFSG.GroupTheory.ker_conj_eq_center.trans hZ)
  let e : ↥(LargeEvenOmega ⇑Φ) ≃* LargeEvenProj (LargeEvenOmega ⇑Φ) :=
    TableBOrth.projMkEquiv hscal
  obtain ⟨σ, hσcomm, hσact⟩ :=
    q2OmegaQuotient_commutingLift (ι := Fin d ⊕ Fin d) (K := F) (Q := ⇑Φ)
      hscal hconj A hAcomm hAI
  let v : MulAut (LargeEvenProj (LargeEvenOmega ⇑Φ)) := ggInducedAut θL u
  have hvA : v ∈ A :=
    Subgroup.mem_map.mpr ⟨u, ⟨y, hyu⟩, rfl⟩
  have hvord : orderOf v = p := by
    change orderOf (ggInducedAut θL u) = p
    rw [orderOf_injective (ggInducedAut θL)
      (ggInducedAut_injective_of_perfect hperfL θL) u, huord]
  let s : ↥(LargeEvenOmega ⇑Φ) := σ ⟨v, hvA⟩
  have hσinj : Function.Injective σ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    apply Subtype.ext
    ext w
    have h := hσact a (e.symm w)
    change e (σ a * e.symm w * (σ a)⁻¹) =
      (a : MulAut (LargeEvenProj (LargeEvenOmega ⇑Φ))) (e (e.symm w)) at h
    rw [ha, MulEquiv.apply_symm_apply] at h
    simpa [MulEquiv.apply_symm_apply] using h.symm
  have hsord : orderOf s = p := by
    change orderOf (σ ⟨v, hvA⟩) = p
    have h1 : orderOf (σ ⟨v, hvA⟩) = orderOf (⟨v, hvA⟩ : ↥A) :=
      orderOf_injective σ hσinj ⟨v, hvA⟩
    have h2 : orderOf (⟨v, hvA⟩ : ↥A) = p := by
      rw [← orderOf_injective A.subtype A.subtype_injective ⟨v, hvA⟩]
      exact hvord
    exact h1.trans h2
  have hoddS : Odd (orderOf (s : GL (Fin d ⊕ Fin d) F)) := by
    rw [Subgroup.orderOf_coe, hsord]
    exact hp.odd_of_ne_two hp2
  obtain ⟨hJ0open, ι, hι⟩ := q2_cover_data (X := ↥L) hperfL θL u (J.subgroupOf L) hJcomp
  let J0 : Subgroup (LargeEvenProj (LargeEvenOmega ⇑Φ)) :=
    (J.subgroupOf L).map (q2CoverMap θL)
  let C : Subgroup ↥(LargeEvenOmega ⇑Φ) := J0.map e.symm.toMonoidHom
  have hJ0comp : CFSG.Open.IsComponentOf J0 (ggAutFixedSubgroup v) := hJ0open
  have hfixmap : (ggAutFixedSubgroup v).map e.symm.toMonoidHom =
      Subgroup.centralizer ({s} : Set ↥(LargeEvenOmega ⇑Φ)) := by
    ext x
    constructor
    · rintro ⟨r, hr, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h := hσact ⟨v, hvA⟩ (e.symm r)
      rw [show σ ⟨v, hvA⟩ = s from rfl, MulEquiv.apply_symm_apply,
        show v r = r from hr] at h
      have h2 : s * e.symm r * s⁻¹ = e.symm r := by
        apply e.injective
        rw [h, MulEquiv.apply_symm_apply]
      have h3 : s * e.symm r = e.symm r * s := by
        calc s * e.symm r = (s * e.symm r * s⁻¹) * s := by group
          _ = e.symm r * s := by rw [h2]
      exact h3.symm
    · intro hx
      refine ⟨e x, ?_, by simp⟩
      change v (e x) = e x
      have hcommx : x * s = s * x := Subgroup.mem_centralizer_singleton_iff.mp hx
      have h := hσact ⟨v, hvA⟩ x
      have hconjx : s * x * s⁻¹ = x := by
        calc s * x * s⁻¹ = x * s * s⁻¹ := by rw [hcommx]
          _ = x := by group
      rw [show σ ⟨v, hvA⟩ = s from rfl, hconjx] at h
      exact h.symm
  have hC : CFSG.Open.IsComponentOf C
      (Subgroup.centralizer ({s} : Set ↥(LargeEvenOmega ⇑Φ))) := by
    have hcomp : CFSG.Open.IsComponentOf C
        ((ggAutFixedSubgroup v).map e.symm.toMonoidHom) :=
      CFSG.isComponentOf_map_mulEquiv e.symm hJ0comp
    rw [hfixmap] at hcomp
    exact hcomp
  let eJL : ↥J ≃* ↥(J.subgroupOf L) := (Subgroup.subgroupOfEquivOfLe hJL).symm
  let eC0 : ↥J0 ≃* ↥C :=
    Subgroup.equivMapOfInjective J0 e.symm.toMonoidHom e.symm.injective
  let ξ : ↥C ⧸ Subgroup.center ↥C ≃* LargeEvenProj (LargeEvenSLGroup (Fin d) K) :=
    (centerQuotCongr eC0).symm.trans (ι.symm.trans ((centerQuotCongr eJL).symm.trans θ))
  have hpF : p ∣ Nat.card F - 1 := by
    rw [hFcard, ← hKcard]
    exact hpQ
  obtain ⟨ε, hε, m, E, hEfield, hEfin, hEchar, eε, hCε, hmd, hEcard⟩ :=
    hsel d h4 F p hp hp2 hpd hpF Φ hΦ hΦcoe s hsord C hC K
      (hKcard.trans hFcard.symm) ξ
  letI : Field E := hEfield
  letI : Finite E := hEfin
  letI : CharP E 2 := hEchar
  have hCεA : CFSG.Assembly.IsComponentOf C
      (glBlockCentralizer (LargeEvenOmega ⇑Φ).subtype
        ({(s : GL (Fin d ⊕ Fin d) F)} : Set (GL (Fin d ⊕ Fin d) F)) ε) :=
    CFSG.Assembly.isComponentOf_iff_open.mpr hCε
  let Cc : Subgroup ↥(LargeEvenOmega ⇑Φ) :=
    (Subgroup.centralizer ({(s : GL (Fin d ⊕ Fin d) F)} : Set (GL (Fin d ⊕ Fin d) F))).comap
      (LargeEvenOmega ⇑Φ).subtype
  let ρ : Cc →* GL (Fin m) E :=
    omegaLinearBlockRhoGL Φ hΦ h8 (s : GL (Fin d ⊕ Fin d) F) s.2 hoddS ε hε eε
  let AΩ : Subgroup ↥(LargeEvenOmega ⇑Φ) := σ.range
  have hcent_eq : Subgroup.centralizer ({s} : Set ↥(LargeEvenOmega ⇑Φ)) = Cc := by
    ext g
    simp only [Cc, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.coe_subtype, Subtype.ext_iff, Subgroup.coe_mul]
  have hAΩCc : AΩ ≤ Cc := by
    intro x hx
    change x ∈ σ.range at hx
    rw [← hcent_eq]
    rw [Subgroup.mem_centralizer_singleton_iff]
    obtain ⟨a, rfl⟩ := hx
    haveI : IsMulCommutative ↥AΩ := hσcomm
    have hc : (⟨σ a, ⟨a, rfl⟩⟩ : ↥AΩ) * ⟨s, ⟨⟨v, hvA⟩, rfl⟩⟩ =
        ⟨s, ⟨⟨v, hvA⟩, rfl⟩⟩ * ⟨σ a, ⟨a, rfl⟩⟩ := mul_comm' _ _
    exact congrArg Subtype.val hc
  let ρσ : ↥AΩ →* GL (Fin m) E := ρ.comp (Subgroup.inclusion hAΩCc)
  let Gsub : Subgroup (GL (Fin m) E) := ρσ.range
  have hGcomm : IsMulCommutative ↥Gsub := by
    haveI : IsMulCommutative ↥AΩ := hσcomm
    exact inferInstance
  have hm2 : 2 ≤ m := by omega
  let V : Subgroup (GL (Fin m) E) :=
    (Gsub.map (TableB.linConjAut (Fin m) E)).comap (TableB.linConjAut (Fin m) E)
  have hVcomm : IsMulCommutative ↥V :=
    q2Lin_commutative_fullPreimage (d := m) (K := E) hm2 Gsub hGcomm
  let aOf (b : ↥Bs) : ↥A :=
    ⟨ggInducedAut θL (ggGamma L hNL b),
      Subgroup.mem_map.mpr ⟨ggGamma L hNL b, ⟨b, rfl⟩, rfl⟩⟩
  let gOf (b : ↥Bs) : GL (Fin m) E := ρσ ⟨σ (aOf b), ⟨aOf b, rfl⟩⟩
  have hgOf (b : ↥Bs) : gOf b ∈ Gsub :=
    MonoidHom.mem_range.mpr ⟨⟨σ (aOf b), ⟨aOf b, rfl⟩⟩, rfl⟩
  let jsub (j : ↥J) : ↥(J.subgroupOf L) := ⟨⟨(j : G), hJL j.2⟩, j.2⟩
  let πj (j : ↥J) : ↥J0 :=
    ⟨q2CoverMap θL (jsub j : ↥L), Subgroup.mem_map_of_mem (q2CoverMap θL) (jsub j).2⟩
  let cOf (j : ↥J) : ↥C := eC0 (πj j)
  have hcOf_coe (j : ↥J) : ((cOf j : ↥C) : ↥(LargeEvenOmega ⇑Φ)) =
      e.symm (πj j : LargeEvenProj (LargeEvenOmega ⇑Φ)) := by
    exact Subgroup.coe_equivMapOfInjective_apply J0 e.symm.toMonoidHom
      e.symm.injective (πj j)
  let ψJC : ↥J ⧸ Subgroup.center ↥J ≃* ↥C ⧸ Subgroup.center ↥C :=
    (centerQuotCongr eJL).trans (ι.trans (centerQuotCongr eC0))
  have hψJC_mk (j : ↥J) : ψJC (QuotientGroup.mk j) = QuotientGroup.mk (cOf j) := by
    have h1 : (centerQuotCongr eJL) (QuotientGroup.mk j) =
        QuotientGroup.mk (jsub j) := by
      rw [centerQuotCongr_mk]
      rfl
    dsimp only [ψJC]
    simp only [MulEquiv.trans_apply]
    rw [h1, hι (jsub j)]
    rfl
  let ψ : ↥J ⧸ Subgroup.center ↥J ≃* LargeEvenProj (LargeEvenSLGroup (Fin m) E) :=
    ψJC.trans (linearBlockQuotientMarking eε hCεA)
  have hπ_ggGamma (b : ↥Bs) (j : ↥J) :
      (aOf b : MulAut (LargeEvenProj (LargeEvenOmega ⇑Φ)))
          (q2CoverMap θL (jsub j : ↥L)) =
        q2CoverMap θL ((ggGamma L hNL b) (jsub j)) := by
    simpa [aOf, q2CoverMap] using
      ggInducedAut_apply (θ := θL) (a := ggGamma L hNL b) (x := (jsub j : ↥L))
  have hJsub_act (b : ↥Bs) (j : ↥J) :
      ((jsub (ggBsAut hN b j) : ↥(J.subgroupOf L)) : ↥L) =
        ggGamma L hNL b (jsub j) := by
    apply Subtype.ext
    simp [jsub, ggBsAut, ggGamma]
  have hconjC (b : ↥Bs) (j : ↥J) :
      ((cOf (ggBsAut hN b j) : ↥C) : ↥(LargeEvenOmega ⇑Φ)) =
        ((⟨σ (aOf b), hAΩCc ⟨aOf b, rfl⟩⟩ : Cc) : ↥(LargeEvenOmega ⇑Φ)) *
          ((cOf j : ↥C) : ↥(LargeEvenOmega ⇑Φ)) *
          ((⟨σ (aOf b), hAΩCc ⟨aOf b, rfl⟩⟩ : Cc) : ↥(LargeEvenOmega ⇑Φ))⁻¹ := by
    have hc'_e : e ((cOf (ggBsAut hN b j) : ↥C) : ↥(LargeEvenOmega ⇑Φ)) =
        q2CoverMap θL (jsub (ggBsAut hN b j) : ↥L) := by
      rw [hcOf_coe, MulEquiv.apply_symm_apply]
    have hc_e : e ((cOf j : ↥C) : ↥(LargeEvenOmega ⇑Φ)) =
        q2CoverMap θL (jsub j : ↥L) := by
      rw [hcOf_coe, MulEquiv.apply_symm_apply]
    have hact' : (aOf b : MulAut (LargeEvenProj (LargeEvenOmega ⇑Φ)))
          (q2CoverMap θL (jsub j : ↥L)) =
        q2CoverMap θL (jsub (ggBsAut hN b j) : ↥L) := by
      rw [hπ_ggGamma b j, ← hJsub_act b j]
    apply e.injective
    calc
      e ((cOf (ggBsAut hN b j) : ↥C) : ↥(LargeEvenOmega ⇑Φ))
          = q2CoverMap θL (jsub (ggBsAut hN b j) : ↥L) := hc'_e
      _ = (aOf b : MulAut (LargeEvenProj (LargeEvenOmega ⇑Φ)))
            (q2CoverMap θL (jsub j : ↥L)) := hact'.symm
      _ = (aOf b : MulAut (LargeEvenProj (LargeEvenOmega ⇑Φ)))
            (e ((cOf j : ↥C) : ↥(LargeEvenOmega ⇑Φ))) := by rw [hc_e]
      _ = e ((σ (aOf b) : ↥(LargeEvenOmega ⇑Φ)) *
            ((cOf j : ↥C) : ↥(LargeEvenOmega ⇑Φ)) *
              (σ (aOf b) : ↥(LargeEvenOmega ⇑Φ))⁻¹) :=
        (hσact (aOf b) ((cOf j : ↥C) : ↥(LargeEvenOmega ⇑Φ))).symm
      _ = e (((⟨σ (aOf b), hAΩCc ⟨aOf b, rfl⟩⟩ : Cc) : ↥(LargeEvenOmega ⇑Φ)) *
            ((cOf j : ↥C) : ↥(LargeEvenOmega ⇑Φ)) *
              ((⟨σ (aOf b), hAΩCc ⟨aOf b, rfl⟩⟩ : Cc) : ↥(LargeEvenOmega ⇑Φ))⁻¹) := rfl
  have hstep (b : ↥Bs) (j : ↥J) :
      ψ (QuotientGroup.mk (ggBsAut hN b j)) =
        TableB.linConjAut (Fin m) E (gOf b) (ψ (QuotientGroup.mk j)) := by
    dsimp only [ψ]
    simp only [MulEquiv.trans_apply]
    rw [hψJC_mk, hψJC_mk]
    have hsq := omegaLinearBlock_quotientMarking_square Φ hΦ h8 (s : GL (Fin d ⊕ Fin d) F)
      s.2 hoddS ε hε eε hCεA (g := ⟨σ (aOf b), hAΩCc ⟨aOf b, rfl⟩⟩)
      (c := cOf j) (c' := cOf (ggBsAut hN b j)) (hconjC b j)
    rw [← hsq]
    rfl
  have hlin : Q2LinearLift ((ggBsAut hN).range.map (centerQuotAut ↥J)) := by
    unfold Q2LinearLift
    refine ⟨m, E, hEfield, hEfin, ψ, V, hVcomm, ?_⟩
    intro α hα
    obtain ⟨β, hβ, rfl⟩ := Subgroup.mem_map.mp hα
    obtain ⟨b, rfl⟩ := hβ
    refine ⟨gOf b, ?_, ?_⟩
    · exact Subgroup.mem_comap.mpr
        (Subgroup.mem_map_of_mem (TableB.linConjAut (Fin m) E) (hgOf b))
    · ext z
      obtain ⟨j, hj⟩ := QuotientGroup.mk_surjective (ψ.symm z)
      have hz : z = ψ (QuotientGroup.mk j) := by
        rw [hj, MulEquiv.apply_symm_apply]
      rw [hz]
      simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
        centerQuotAut_mk]
      exact hstep b j
  have hcomm := q2_commutative_of_linearLift (M := (ggBsAut hN).range.map (centerQuotAut ↥J))
    hlin (d := d) (K := K) (by omega) hn hKcard θ
  have hmap : (ggBsAut hN).range.map (kgInducedAut θ) =
      ((ggBsAut hN).range.map (centerQuotAut ↥J)).map
        (MulAut.congr θ).toMonoidHom := by
    simp only [kgInducedAut, Subgroup.map_map]
  rw [hmap]
  exact hcomm


theorem q2_orthogonalPlus_high
    (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J : Subgroup G) (hcfg : GGConfig p B Bs x L D J) (hInner : GGInnerDiagOn Bs L)
    (hN : Bs ≤ Subgroup.normalizer (J : Set G)) (d : ℕ) (K : Type) [Field K] [Finite K]
    (θ : ↥J ⧸ Subgroup.center ↥J ≃* LargeEvenProj (LargeEvenSLGroup (Fin d) K))
    (hpd : p ∣ d) (hpq : p ∣ Nat.card K - 1)
    (hplus : GGInnerDiagOnLab
      (fun p lab => q2RowFits .orthogonalPlus p d (Nat.card K) lab) p Bs L)
    (h4 : 4 ≤ d) :
    IsMulCommutative
      ((((ggBsAut hN).range).map (kgInducedAut θ)).comap (TableB.linConjAut (Fin d) K)) :=
  q2_orthogonalPlus_high_of_blockChoice q2OmegaPlusBlockChoice_holds
    G p B Bs x L D J hcfg hInner hN d K θ hpd hpq hplus h4


private theorem three_le_d_of_plus_marking
    {G : Type} [Group G] [Finite G] {p : ℕ} {Bs L : Subgroup G} {d : ℕ}
    {K : Type} [Field K] [Finite K]
    (hrow : GGInnerDiagOnLab
      (fun p lab => q2RowFits .orthogonalPlus p d (Nat.card K) lab) p Bs L) :
    3 ≤ d := by
  unfold GGInnerDiagOnLab at hrow
  obtain ⟨-, lab, hlabΛ, hraw⟩ := hrow
  obtain ⟨tag, rank, n⟩ := lab
  obtain ⟨R0, hR0, I0, F0, hcont0⟩ := largeEvenRawDatum_exists hraw
  letI : Group R0 := hR0
  obtain ⟨-, -, -, hfit0, -, -, -⟩ := hcont0
  exact (q2RowFits_orthogonalPlus_parameters hlabΛ hfit0).2.2.1

theorem q2_orthogonalPlus : Q2RowSolverInput .orthogonalPlus := by
  unfold Q2RowSolverInput
  intro G instG instFin p B Bs x L D J hcfg hInner hN d K instK instFinK θ hpd hpq hrow
  by_cases h3 : d = 3
  · exact q2_orthogonalPlus_d3 G p B Bs x L D J hcfg hN d h3 K θ hrow
  · have hd3 : 3 ≤ d := three_le_d_of_plus_marking hrow
    have h4 : 4 ≤ d := by omega
    exact q2_orthogonalPlus_high G p B Bs x L D J hcfg hInner hN d K θ hpd hpq hrow h4

end CFSG.StandardType

end
