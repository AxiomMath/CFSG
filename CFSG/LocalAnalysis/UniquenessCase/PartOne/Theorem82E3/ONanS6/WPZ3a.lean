module

public import CFSG.Adapters.LieModelL3U3Torus
public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
public import CFSG.GroupTheory.ConjActionModPCore
public import CFSG.GroupTheory.CoprimeActionSupport.CentralizerOnQuotientMembership
public import CFSG.GroupTheory.IsCyclicOfPRankLeOne
public import CFSG.GroupTheory.PRankQuotientLift
public import CFSG.LocalAnalysis.AGLEmbedding.CatalogComponent
public import CFSG.LocalAnalysis.RankFourTheoremC.Nongeneration.Planes
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight90P22
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K5SmallONan
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811K3Holds
public import CFSG.RankThree.PartTwo.KFacts.OutFixCentralThreeTools
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanKFacts
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanK12
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPFF2
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPG2
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPZ
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPZ2e
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPZs
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WS6
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CaseOneONan
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight90S123

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
section
open CFSG.Open
open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data IsSpor IsAlt)
open CFSG.ASVolI.ChIJK (IsWeaklyClosedIn)
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise
variable {G : Type} [Group G] [Finite G]
variable {D : Data G}
variable (c : Ctx82E3 D) {P A : Subgroup G} {a : G}

noncomputable abbrev action82E3 : ↥D.M →* MulAut c.Lbar :=
  CFSG.GroupTheory.conjModPCore 2 c.L D.M c.le_normalizer_L

noncomputable abbrev C82E3 : Subgroup G :=
  (action82E3 c).ker.map D.M.subtype

noncomputable abbrev abar82E3 (haL : a ∈ P ⊓ c.L) : c.Lbar :=
  QuotientGroup.mk (s := CFSG.Open.pCore 2 ↥c.L) (⟨a, haL.2⟩ : ↥c.L)

theorem not_mem_center_lbar_of_not_mem_zSub
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) (haL : a ∈ P ⊓ c.L)
    (haZ : a ∉ zSub P c.L) :
    abar82E3 c haL ∉ Subgroup.center c.Lbar := by
  classical
  intro hcenter
  have haM : a ∈ D.M := hP.le haL.1
  have haction : action82E3 c ⟨a, haM⟩ = 1 := by
    have hconj : MulAut.conj (abar82E3 c haL) = 1 := by
      apply MulEquiv.ext
      intro x
      rw [MulAut.conj_apply, MulAut.one_apply]
      have h := Subgroup.mem_center_iff.mp hcenter x
      calc abar82E3 c haL * x * (abar82E3 c haL)⁻¹
          = (x * abar82E3 c haL) * (abar82E3 c haL)⁻¹ := by rw [h]
        _ = x := by group
    rw [show action82E3 c ⟨a, haM⟩ = MulAut.conj (abar82E3 c haL) from
      CFSG.GroupTheory.conjModPCore_apply_eq_conj_mk 2 c.L D.M c.le_normalizer_L haM haL.2]
    exact hconj
  have hker : a ∈ (action82E3 c).ker.map D.M.subtype :=
    Subgroup.mem_map.mpr ⟨⟨a, haM⟩, MonoidHom.mem_ker.mpr haction, rfl⟩
  have hcomm :=
    (CFSG.GroupTheory.mem_map_ker_conjModPCore_iff 2 c.L D.M c.le_normalizer_L).mp hker
  have hcent : a ∈ Subgroup.centralizer ((P ⊓ c.L : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hO : a * y * a⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 c.L := hcomm.2 y hy.2
    have hPL : a * y * a⁻¹ * y⁻¹ ∈ P ⊓ c.L := by
      refine ⟨?_, ?_⟩
      · exact P.mul_mem (P.mul_mem (P.mul_mem haL.1 hy.1) (P.inv_mem haL.1)) (P.inv_mem hy.1)
      · exact c.L.mul_mem (c.L.mul_mem (c.L.mul_mem haL.2 hy.2) (c.L.inv_mem haL.2))
          (c.L.inv_mem hy.2)
    have hdisj : (P ⊓ c.L) ⊓ CFSG.Open.pCoreOf 2 c.L = ⊥ :=
      (IsPGroup.disjoint_of_ne 3 2 (by norm_num) (P ⊓ c.L) (CFSG.Open.pCoreOf 2 c.L)
        (hP.isPGroup.to_le inf_le_left)
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 c.L)).eq_bot
    have h1 : a * y * a⁻¹ * y⁻¹ = 1 := by
      have hmem : a * y * a⁻¹ * y⁻¹ ∈ (P ⊓ c.L) ⊓ CFSG.Open.pCoreOf 2 c.L :=
        Subgroup.mem_inf.mpr ⟨hPL, hO⟩
      rw [hdisj] at hmem
      exact Subgroup.mem_bot.mp hmem
    have hay : a * y = y * a := by
      calc a * y = (a * y * a⁻¹ * y⁻¹) * (y * a) := by group
        _ = 1 * (y * a) := by rw [h1]
        _ = y * a := one_mul _
    exact hay.symm
  exact haZ (Subgroup.mem_inf.mpr ⟨haL, hcent⟩)

theorem card_centralizer_aut_lbar_dvd_6480
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    (hK4 : K4) (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (haL : a ∈ P ⊓ c.L) (ha3 : orderOf a = 3) (haZ : a ∉ zSub P c.L) :
    Nat.card ↥(Subgroup.centralizer
      ({MulAut.conj (abar82E3 c haL)} : Set (MulAut c.Lbar))) ∣ 6480 := by
  classical
  let Y := c.Lbar ⧸ Subgroup.center c.Lbar
  let hN : ∀ σ : MulAut c.Lbar,
      Subgroup.map (σ : c.Lbar →* c.Lbar) (Subgroup.center c.Lbar) =
        Subgroup.center c.Lbar := fun σ => Subgroup.map_center_eq σ
  let Φ : MulAut c.Lbar →* MulAut Y :=
    CFSG.RankThree.PartTwo.KFacts.OutFixCentralThree.quotientAut
      (Subgroup.center c.Lbar) hN
  have hperf : Group.IsPerfect c.Lbar := Group.isPerfect_def.mpr hON.1.1
  let τ : MulAut c.Lbar := MulAut.conj (abar82E3 c haL)
  let σ : MulAut Y := Φ τ
  have hΦinj : Function.Injective Φ := by
    refine (injective_iff_map_eq_one Φ).mpr (fun α hα => ?_)
    exact CFSG.RankThree.PartTwo.KFacts.OutFixCentralThree.eq_one_of_quotientAut_eq_one
      (N := Subgroup.center c.Lbar) le_rfl hN hα
  have ha3' : a ^ 3 = 1 := by simpa [ha3] using pow_orderOf_eq_one a
  have habar3 : abar82E3 c haL ^ 3 = 1 := by
    change ((QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L)) (⟨a, haL.2⟩ : ↥c.L)) ^ 3 = 1
    rw [← map_pow]
    have h : (⟨a, haL.2⟩ : ↥c.L) ^ 3 = 1 := Subtype.ext (by simpa using ha3')
    rw [h, map_one]
  have hτ3 : τ ^ 3 = 1 := by
    change (MulAut.conj (abar82E3 c haL)) ^ 3 = 1
    rw [← map_pow, habar3, map_one]
  have hσ3 : σ ^ 3 = 1 := by
    change (Φ τ) ^ 3 = 1
    rw [← map_pow, hτ3, map_one]
  have hσne : σ ≠ 1 := by
    intro hσ1
    have hτ1 : τ = 1 := hΦinj (by simpa [σ] using hσ1)
    have hcenter : abar82E3 c haL ∈ Subgroup.center c.Lbar := by
      rw [Subgroup.mem_center_iff]
      intro x
      have h := congrArg (fun f : MulAut c.Lbar => f x) hτ1
      simp only [τ, MulAut.conj_apply, MulAut.one_apply] at h
      have hay : abar82E3 c haL * x = x * abar82E3 c haL := by
        calc abar82E3 c haL * x
            = (abar82E3 c haL * x * (abar82E3 c haL)⁻¹) * abar82E3 c haL := by group
          _ = x * abar82E3 c haL := by rw [h]
      exact hay.symm
    exact not_mem_center_lbar_of_not_mem_zSub c hP haL haZ hcenter
  have hσord : orderOf σ = 3 := by
    have hdvd : orderOf σ ∣ 3 := orderOf_dvd_of_pow_eq_one hσ3
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact absurd (orderOf_eq_one_iff.mp h1) hσne
    · exact h3
  have hK4' : Nat.card ↥(Subgroup.centralizer ({σ} : Set (MulAut Y))) ∣ 6480 := by
    simpa using (hK4 Y (H := (⊤ : Subgroup (MulAut Y))) hON.2.2 le_top σ
      (Subgroup.mem_top σ) hσord).1
  have hmap_le : (Subgroup.centralizer ({τ} : Set (MulAut c.Lbar))).map Φ ≤
      Subgroup.centralizer ({σ} : Set (MulAut Y)) := by
    rintro _ ⟨α, hα, rfl⟩
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    have hατ := Subgroup.mem_centralizer_singleton_iff.mp hα
    calc Φ α * σ = Φ α * Φ τ := rfl
      _ = Φ (α * τ) := (map_mul Φ α τ).symm
      _ = Φ (τ * α) := by rw [hατ]
      _ = Φ τ * Φ α := map_mul Φ τ α
      _ = σ * Φ α := rfl
  have hcardmap : Nat.card ↥((Subgroup.centralizer ({τ} : Set (MulAut c.Lbar))).map Φ) =
      Nat.card ↥(Subgroup.centralizer ({τ} : Set (MulAut c.Lbar))) :=
    Subgroup.card_map_of_injective hΦinj
  have h1 : Nat.card ↥((Subgroup.centralizer ({τ} : Set (MulAut c.Lbar))).map Φ) ∣
      Nat.card ↥(Subgroup.centralizer ({σ} : Set (MulAut Y))) :=
    Subgroup.card_dvd_of_le hmap_le
  have h2 : Nat.card ↥(Subgroup.centralizer ({σ} : Set (MulAut Y))) ∣ 6480 := by
    simpa using hK4'
  rw [hcardmap] at h1
  exact h1.trans h2

theorem mem_C82E3_of_action_eq_one
    {y : G} (hyM : y ∈ D.M)
    (hy : action82E3 c ⟨y, hyM⟩ = 1) :
    y ∈ C82E3 c :=
  Subgroup.mem_map.mpr ⟨⟨y, hyM⟩, MonoidHom.mem_ker.mpr hy, rfl⟩

theorem mem_zSub_of_mem_P_of_mem_C_of_pow_three
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) {x : G} (hxP : x ∈ P)
    (hxC : x ∈ C82E3 c) (hx3 : x ^ 3 = 1) : x ∈ zSub P c.L := by
  classical
  have hxL : x ∈ c.L :=
    c.forall_pow_three_eq_one_mem_L_of_threeCover
      CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.k3Exp_holds
      (CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.k3Out_holds c.Lbar hON)
      hON hP x hxP hx3
  have hcomm :=
    (CFSG.GroupTheory.mem_map_ker_conjModPCore_iff 2 c.L D.M c.le_normalizer_L).mp hxC
  refine Subgroup.mem_inf.mpr ⟨⟨hxP, hxL⟩, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hO : x * y * x⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 c.L := hcomm.2 y hy.2
  have hPL : x * y * x⁻¹ * y⁻¹ ∈ P ⊓ c.L := by
    refine ⟨?_, ?_⟩
    · exact P.mul_mem (P.mul_mem (P.mul_mem hxP hy.1) (P.inv_mem hxP)) (P.inv_mem hy.1)
    · exact c.L.mul_mem (c.L.mul_mem (c.L.mul_mem hxL hy.2) (c.L.inv_mem hxL))
        (c.L.inv_mem hy.2)
  have hdisj : (P ⊓ c.L) ⊓ CFSG.Open.pCoreOf 2 c.L = ⊥ :=
    (IsPGroup.disjoint_of_ne 3 2 (by norm_num) (P ⊓ c.L) (CFSG.Open.pCoreOf 2 c.L)
      (hP.isPGroup.to_le inf_le_left)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 c.L)).eq_bot
  have h1 : x * y * x⁻¹ * y⁻¹ = 1 := by
    have hmem : x * y * x⁻¹ * y⁻¹ ∈ (P ⊓ c.L) ⊓ CFSG.Open.pCoreOf 2 c.L :=
      Subgroup.mem_inf.mpr ⟨hPL, hO⟩
    rw [hdisj] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hxy : x * y = y * x := by
    calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
      _ = 1 * (y * x) := by rw [h1]
      _ = y * x := one_mul _
  exact hxy.symm

theorem pRank_three_centralizerOnQuotient_le_one
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) :
    CFSG.Open.pRank 3 (C82E3 c) ≤ 1 := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZcard : Nat.card ↥(zSub P c.L) = 3 := c.card_inf_centralizer_of_onan hON hP
  refine CFSG.SectionRank.pRank_le (by norm_num : 1 < 3) ?_
  intro E hEC hE
  have hEp : IsPGroup 3 E := by
    refine (isPGroup_iff_exists_pow_pow_eq_one).mpr ⟨1, fun x => ?_⟩
    simpa only [pow_one] using Subtype.ext (by simpa using hE.2 (x : G) x.2)
  have hEM : E ≤ D.M := by
    intro x hx
    obtain ⟨m, -, hm⟩ := Subgroup.mem_map.mp (hEC hx)
    rw [← hm]
    exact m.2
  let EM : Subgroup ↥D.M := E.subgroupOf D.M
  have hEMp : IsPGroup 3 EM := hEp.comap_subtype
  obtain ⟨T', hT'⟩ := hEMp.exists_le_sylow
  let T : Subgroup G := (T' : Subgroup ↥D.M).map D.M.subtype
  have hTsyl : CFSG.ABGLocalTools.IsSylowOf 3 T D.M := ⟨T', rfl⟩
  have hET : E ≤ T := by
    intro x hx
    exact Subgroup.mem_map.mpr
      ⟨⟨x, hEM hx⟩, hT' (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  obtain ⟨m, hmM, hconj⟩ := CFSG.ABGLocalTools.IsSylowOf.exists_mem_conj hP hTsyl
  let E' : Subgroup G := E.map (MulAut.conj m⁻¹).toMonoidHom
  have hE'card : Nat.card E' = Nat.card E := by
    change Nat.card (E.map (MulAut.conj m⁻¹).toMonoidHom) = Nat.card E
    rw [Subgroup.card_map_of_injective (MulAut.conj m⁻¹).injective]
  have hE'P : E' ≤ P := by
    rintro _ ⟨x, hx, rfl⟩
    have hc : (MulEquiv.toMonoidHom (MulAut.conj m⁻¹)) x = m⁻¹ * x * m := by
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [hc]
    exact (hconj x).mp (hET hx)
  have hE'C : E' ≤ C82E3 c := by
    rintro _ ⟨x, hx, rfl⟩
    have hc : (MulEquiv.toMonoidHom (MulAut.conj m⁻¹)) x = m⁻¹ * x * m := by
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [hc]
    have hxM : x ∈ D.M := hEM hx
    obtain ⟨y, hyker, hyval⟩ := Subgroup.mem_map.mp (hEC hx)
    have hyx : (⟨x, hxM⟩ : ↥D.M) = y := Subtype.ext hyval.symm
    have hact : action82E3 c ⟨x, hxM⟩ = 1 := by
      rw [hyx]
      exact MonoidHom.mem_ker.mp hyker
    have hconjM : m⁻¹ * x * m ∈ D.M :=
      D.M.mul_mem (D.M.mul_mem (D.M.inv_mem hmM) hxM) hmM
    have hact' : action82E3 c ⟨m⁻¹ * x * m, hconjM⟩ = 1 := by
      have h1 : (⟨m⁻¹ * x * m, hconjM⟩ : ↥D.M) =
          (⟨m, hmM⟩ : ↥D.M)⁻¹ * ⟨x, hxM⟩ * ⟨m, hmM⟩ := Subtype.ext rfl
      rw [h1, map_mul, map_mul, map_inv, hact]
      group
    exact mem_C82E3_of_action_eq_one c hconjM hact'
  have hE'Z : E' ≤ zSub P c.L := by
    rintro _ ⟨x, hx, rfl⟩
    have hc : (MulEquiv.toMonoidHom (MulAut.conj m⁻¹)) x = m⁻¹ * x * m := by
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    have hx3 : x ^ 3 = 1 := hE.2 x hx
    have hconj3 : (m⁻¹ * x * m) ^ 3 = 1 := by
      rw [← hc, ← map_pow, hx3, map_one]
    rw [hc]
    exact mem_zSub_of_mem_P_of_mem_C_of_pow_three c hON hP
      (by simpa using hE'P ⟨x, hx, rfl⟩) (by simpa using hE'C ⟨x, hx, rfl⟩) hconj3
  have hcardE' : Nat.card E ≤ 3 := by
    have hle : Nat.card E' ≤ Nat.card ↥(zSub P c.L) := Subgroup.card_le_of_le hE'Z
    rw [hZcard] at hle
    rwa [hE'card] at hle
  simpa using hcardE'

theorem p4_sections_centralizer'
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar) (h7 : D.sig = {7})
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hNZ : Subgroup.normalizer ((zSub P c.L : Subgroup G) : Set G) ≤ D.M)
    (haL : a ∈ P ⊓ c.L) (ha3 : orderOf a = 3) (haZ : a ∉ zSub P c.L)
    (hK9b : K9bIn) (hK4 : K4) :
    ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S →
      (∃ x y : S, x * y ≠ y * x) →
      CFSG.SignalizerFunctorTheorem.IsSectionOf S ↥(CM c a) →
        IsAlt S 5 ∨ IsAlt S 6 ∨ (∀ Q : Sylow 3 S, IsCyclic (Q : Subgroup S)) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro S _ _ hSsimple hSnonab hsec
  obtain ⟨K, f, hf⟩ := hsec
  have hInCat : CFSG.Assembly.InCatalog S := by
    let inc : ↥(CM c a) →* ↥D.M := Subgroup.inclusion (inf_le_left : CM c a ≤ D.M)
    let K' : Subgroup ↥D.M := K.map inc
    let eK : K ≃* K' :=
      Subgroup.equivMapOfInjective K inc (Subgroup.inclusion_injective _)
    let f' : K' →* S := f.comp eK.symm.toMonoidHom
    have hf' : Function.Surjective f' := hf.comp eK.symm.surjective
    have hcatM : CFSG.AGLEmbedding.CatalogSimpleSections ↥D.M :=
      CFSG.AGLEmbedding.catalogSimpleSections_of_isKProper c.kProper D.M c.M_ne_top
    exact hcatM.surjective_image K' f' hf' hSnonab
  let ι : K →* ↥D.M :=
    { toFun := fun y =>
        ⟨(y : G), (Subgroup.mem_inf.mp (Subtype.val y).2).1⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun _ _ => Subtype.ext rfl }
  let act : K →* MulAut c.Lbar := (action82E3 c).comp ι
  let KC : Subgroup K := act.ker
  let τ : MulAut c.Lbar := MulAut.conj (abar82E3 c haL)
  have hact_comm : ∀ y : K, act y * τ = τ * act y := by
    intro y
    have hya : (y : G) * a = a * (y : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp
        (Subgroup.mem_inf.mp (Subtype.val y).2).2
    have hyaM : ι y * (⟨a, hP.le haL.1⟩ : ↥D.M) =
        (⟨a, hP.le haL.1⟩ : ↥D.M) * ι y := Subtype.ext hya
    have hτ : τ = action82E3 c ⟨a, hP.le haL.1⟩ :=
      (CFSG.GroupTheory.conjModPCore_apply_eq_conj_mk 2 c.L D.M c.le_normalizer_L
        (hP.le haL.1) haL.2).symm
    show (action82E3 c) (ι y) * τ = τ * (action82E3 c) (ι y)
    rw [hτ, ← map_mul, ← map_mul, hyaM]
  have hact_le : act.range ≤ Subgroup.centralizer ({τ} : Set (MulAut c.Lbar)) := by
    rintro _ ⟨y, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hact_comm y)
  have hKCnormal : KC.Normal := by
    change act.ker.Normal
    infer_instance
  have hfKCnormal : (KC.map f).Normal := hKCnormal.map f hf
  rcases CFSG.eq_bot_or_eq_top_of_normal (KC.map f) hfKCnormal with hbot | htop
  ·
    have hdvdS : Nat.card S ∣ 6480 := by
      have hle : KC ≤ f.ker := by
        intro x hx
        rw [MonoidHom.mem_ker]
        have hmem : f x ∈ KC.map f := Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
        rw [hbot] at hmem
        exact Subgroup.mem_bot.mp hmem
      let g : K ⧸ KC →* S := QuotientGroup.lift KC f hle
      have hgsurj : Function.Surjective g := by
        intro s
        obtain ⟨x, rfl⟩ := hf s
        exact ⟨QuotientGroup.mk x, by simp [g]⟩
      have h1 : Nat.card S ∣ Nat.card (K ⧸ KC) := Subgroup.card_dvd_of_surjective hgsurj
      have h2 : Nat.card (K ⧸ KC) = Nat.card act.range :=
        Nat.card_congr (QuotientGroup.quotientKerEquivRange act).toEquiv
      have h3 : Nat.card act.range ∣
          Nat.card ↥(Subgroup.centralizer ({τ} : Set (MulAut c.Lbar))) :=
        Subgroup.card_dvd_of_le hact_le
      have h4 : Nat.card ↥(Subgroup.centralizer ({τ} : Set (MulAut c.Lbar))) ∣ 6480 :=
        card_centralizer_aut_lbar_dvd_6480 c hON hK4 hP haL ha3 haZ
      have h23 : Nat.card (K ⧸ KC) ∣
          Nat.card ↥(Subgroup.centralizer ({τ} : Set (MulAut c.Lbar))) := by
        rw [h2]
        exact h3
      exact h1.trans (h23.trans h4)
    rcases hK9b S hSsimple hSnonab hInCat hdvdS with h5 | h6
    · exact Or.inl h5
    · exact Or.inr (Or.inl h6)
  ·
    have hKCleC : ∀ y : KC, (y : G) ∈ C82E3 c := by
      intro y
      have hact1 : act (y : K) = 1 := MonoidHom.mem_ker.mp y.2
      exact mem_C82E3_of_action_eq_one c (ι (y : K)).2 (by
        change (action82E3 c) (ι (y : K)) = 1
        exact hact1)
    let ψ : KC →* ↥(C82E3 c) :=
      { toFun := fun y => ⟨(y : G), hKCleC y⟩
        map_one' := Subtype.ext rfl
        map_mul' := fun _ _ => Subtype.ext rfl }
    have hψinj : Function.Injective ψ := by
      intro a b hab
      have h1 : (a : G) = (b : G) :=
        congrArg (fun x : ↥(C82E3 c) => (x : G)) hab
      exact Subtype.ext (Subtype.ext (Subtype.ext h1))
    have hCrank : CFSG.Open.pRank 3 (⊤ : Subgroup ↥(C82E3 c)) ≤ 1 := by
      rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (C82E3 c)]
      exact pRank_three_centralizerOnQuotient_le_one c hON hP
    have hKCrank : CFSG.Open.pRank 3 (⊤ : Subgroup ↥KC) ≤ 1 :=
      (CFSG.SectionRank.pRank_top_le_of_injective (by norm_num : 1 < 3) ψ hψinj).trans hCrank
    have hfKCsurj : Function.Surjective (f.comp KC.subtype) := by
      intro s
      have hs : s ∈ KC.map f := by rw [htop]; exact Subgroup.mem_top s
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hs
      exact ⟨⟨x, hx⟩, rfl⟩
    have hSrank : CFSG.Open.pRank 3 (⊤ : Subgroup S) ≤ 1 := by
      have hquot :=
        CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.r890p22_pRank_quotient_le_one
          (p := 3) (by norm_num) (by norm_num) hKCrank (f.comp KC.subtype).ker
      rwa [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3)
        (QuotientGroup.quotientKerEquivOfSurjective (f.comp KC.subtype) hfKCsurj)] at hquot
    refine Or.inr (Or.inr ?_)
    intro Q
    exact CFSG.LocalAnalysis.RankFourTheoremC.Nongeneration.isCyclic_sylow_of_pRank_le_one
      (p := 3) (by norm_num) hSrank Q

end
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
section
open CFSG.Open
open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data IsSpor IsAlt)
open CFSG.ASVolI.ChIJK (IsWeaklyClosedIn)
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise
variable {G : Type} [Group G] [Finite G]
variable {D : Data G}
variable (c : Ctx82E3 D) {P A : Subgroup G} {a : G}

theorem g2_coprime_excluded'
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar) (h7 : D.sig = {7})
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hNZ : Subgroup.normalizer ((zSub P c.L : Subgroup G) : Set G) ≤ D.M)
    (haL : a ∈ P ⊓ c.L) (ha3 : orderOf a = 3) (haZ : a ∉ zSub P c.L)
    {J : Subgroup G} (hJ : J ∈ thetaComponentsAt 3 a) (h3 : 3 ∣ Nat.card J)
    {z : G} (hzZ : z ∈ zSub P c.L) (hz3 : orderOf z = 3)
    (hzN : z ∈ Subgroup.normalizer (J : Set G))
    (hK12 : K12SL) (hK9b : K9bIn) (hK4 : K4)
    (hπ : thetaQuotMulAut J (J.normalizerMonoidHom ⟨z, hzN⟩) ≠ 1)
    (hiso : Nonempty (J0 J ≃* Xbar c P J))
    (hinner : thetaQuotMulAut J (J.normalizerMonoidHom ⟨z, hzN⟩) ∈
      (MulAut.conj : (Jtilde J) →* MulAut (Jtilde J)).range)
    {p f : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) (hq : 3 ≤ p ^ f)
    (hmodel : CFSG.Blueprint.ChevalleyExceptionalModel (Xbar c P J) .G2 p f) : False := by
  obtain ⟨S, hSgrp, hSfin, hSsimple, hSnonab, hSsec, hcase⟩ :=
    g2_coprime_section'' c hON h7 hP hNZ haL ha3 haZ hJ h3 hzZ hz3 hzN hK12 hπ hiso hinner
      hp hp3 hq hmodel
  letI := hSgrp
  letI := hSfin
  have hP4 := p4_sections_centralizer' c hON h7 hP hNZ haL ha3 haZ hK9b hK4
  rcases hcase with ⟨hmod, hmodelS⟩ | ⟨hmod, hmodelS⟩
  · obtain ⟨⟨Q, hQnc⟩, h5, h6⟩ := psl3_section_data hmodelS hp3 hmod hq
    rcases hP4 S hSsimple hSnonab hSsec with h5' | h6' | hcyc
    · exact h5 h5'
    · exact h6 h6'
    · exact hQnc (hcyc Q)
  · obtain ⟨⟨Q, hQnc⟩, h5, h6⟩ := psu3_section_data hmodelS hp3 hmod hq
    rcases hP4 S hSsimple hSnonab hSsec with h5' | h6' | hcyc
    · exact h5 h5'
    · exact h6 h6'
    · exact hQnc (hcyc Q)

end
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
