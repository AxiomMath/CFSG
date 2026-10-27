module

public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3Defs
public import CFSG.LocalAnalysis.StandardType.GGPZWeylType
public import CFSG.LocalAnalysis.StandardType.GGR4JMeetRow
public import CFSG.LocalAnalysis.StandardType.GGKGAF4Core
public import CFSG.LocalAnalysis.StandardType.GGTBWNorm
public import CFSG.LocalAnalysis.StandardType.GGKGAF4Holds
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.StandardType.GGR4AutInn
public import CFSG.LocalAnalysis.StandardType.GGR4Lemma47c
public import CFSG.LocalAnalysis.StandardType.GGR4JMeetTransport
public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3Bridge
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBRkConfig
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48RkF4Holds
public import CFSG.GroupTheory.ConjKerCenter
public import CFSG.LocalAnalysis.StandardType.GGR4JMeetData
public import CFSG.LocalAnalysis.StandardType.GGResJLineA3
public import CFSG.LocalAnalysis.StandardType.GGResJLinearCubeAutomizer
public import CFSG.LocalAnalysis.StandardType.GGF4ThreeSCCube
public import CFSG.LocalAnalysis.StandardType.GGF4ThreeSCCubeHolds
public import CFSG.LocalAnalysis.StandardType.GGF4ThreeNbrRank
public import CFSG.LocalAnalysis.StandardType.GGTableBF4Torus
public import CFSG.LocalAnalysis.StandardType.GGTBTorDatum
public import CFSG.LocalAnalysis.StandardType.GGTBTorF4
public import CFSG.LocalAnalysis.StandardType.GGForkJrPumpLattice
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrWeylA
public import CFSG.LocalAnalysis.StandardType.GGLargeRowCard
public import CFSG.LocalAnalysis.StandardType.GGResLeaf
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalCover
public import CFSG.Timmesfeld.Orders.Classical
public import CFSG.Timmesfeld.Orders.Distinct
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
public import CFSG.LocalAnalysis.StandardType.GGR4JMeetCard
public import CFSG.LocalAnalysis.StandardType.GGR4JMeetDecomp
public import CFSG.LocalAnalysis.StandardType.GGF4OrderThreeRank
public import CFSG.LocalAnalysis.StandardType.GGF4OrderThreeLabel
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylOfKnown
public import CFSG.LocalAnalysis.GLTheoremB.Prop95IvT2

public section

namespace CFSG.StandardType
open CFSG.Assembly

private theorem f4_isWeylMatrix : GGIsWeylMatrix CoxeterMatrix.F₄ :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Equiv.refl _, (ggCoxeterMatrix_reindex_refl _).symm⟩))))

lemma ggResF4_hasLabel_F4
    {G : Type} [Group G] [Finite G] {Bs L : Subgroup G}
    (hF4 : GGInnerDiagOnLabel (fun p lab => p = 3 ∧ lab.tag = .F4 ∧ lab.n = 1) 3 Bs L) :
    GGHasLabel ⟨.F4, 0, 1⟩ (↥L ⧸ Subgroup.center ↥L) := by
  obtain ⟨-, lab, -, hraw⟩ := hF4
  obtain ⟨tag, rank, n⟩ := lab
  obtain ⟨R₀, _, I₀, F₀, hP₀⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨-, -, θ₀, hP₀'⟩ := hP₀
  obtain ⟨⟨-, htag, hn⟩, -, -⟩ := hP₀'
  cases htag
  cases hn
  change LargeEvenRawDatum ⟨.F4, 4, 1⟩ _ at hraw
  have hLabel4 : GGHasLabel ⟨.F4, 4, 1⟩ (↥L ⧸ Subgroup.center ↥L) := by
    unfold GGHasLabel
    exact largeEvenRawDatum_mono (fun R _ I F h => ⟨h.2.2.choose⟩) hraw
  simpa [GGHasLabel, LargeEvenRawDatum] using hLabel4

theorem ggResF4_exactTwo_parabolic_card_le_twelve
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs L J K : Subgroup G}
    (h2 : GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny)
    (hJ : ggAutomizer J Bs ≠ ⊥)
    (hAL : Nat.card ↥(ggAutomizer L Bs) = 1152) :
    Nat.card ↥(ggAutomizer J Bs) ≤ 12 := by
  have hdataF4 := ggWeylTypeData_of_isWeylMatrix f4_isWeylMatrix
  have hdataF4' : GGWeylTypeData 4 1152
      (Nat.card ↥(Subgroup.center (CoxeterMatrix.F₄).Group)) := by
    simpa [l04fFRC_ord_card_coxeterF4] using hdataF4
  have hdataF4'' : GGWeylTypeData 4 (Nat.card ↥(ggAutomizer L Bs))
      (Nat.card ↥(Subgroup.center (CoxeterMatrix.F₄).Group)) := by
    simpa [hAL] using hdataF4'
  obtain ⟨r, hr, hsurv⟩ :=
    ggResLeviDatumCard_rank_eq_of_weylTypeData h2 hJ hdataF4''
  exact ggWeylTypeData_card_le_twelve_of_rank_le_two hsurv (by omega)

theorem ggResF4_innerOnL_of_label
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs L : Subgroup G}
    (hF4 : GGInnerDiagOnLabel (fun p lab => p = 3 ∧ lab.tag = .F4) p Bs L)
    (hLperf : commutator ↥L = ⊤) :
    ∀ b ∈ Bs, ∃ k ∈ L, ∀ l ∈ L, b * l * b⁻¹ = k * l * k⁻¹ := by
  obtain ⟨-, lab, hlab, hraw⟩ := hF4
  obtain ⟨tag, rank, n⟩ := lab
  obtain ⟨R₀, _, I₀, F₀, hP₀⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨-, -, θ₀, hP₀'⟩ := hP₀
  obtain ⟨⟨-, htag⟩, -, -⟩ := hP₀'
  cases htag
  have hrank : rank = 0 := by simpa [LargeEvenInLambda2] using hlab.2
  subst hrank
  change LargeEvenRawDatum ⟨.F4, 0, n⟩ _ at hraw
  have hrow := ggR4RowFact_F4 (f := n) _ hraw
  obtain ⟨R, _, I, F, hQ, hrowfact⟩ := largeEvenRawDatum_exists hrow
  obtain ⟨-, -, θ, hP⟩ := hQ
  obtain ⟨-, hBsN, hBs3⟩ := hP
  intro b hb
  have hbN : b ∈ Subgroup.normalizer (L : Set G) := hBsN hb
  have hbNi : b⁻¹ ∈ Subgroup.normalizer (L : Set G) := Subgroup.inv_mem _ hbN
  obtain ⟨φ, hφI, hφ⟩ := hBs3 b hb
  obtain ⟨r, hr⟩ := hrowfact.1 φ hφI
  obtain ⟨v, hv⟩ := QuotientGroup.mk_surjective (θ.symm r)
  have hvθ : θ (QuotientGroup.mk v) = r := by
    rw [hv]
    exact θ.apply_symm_apply r
  let α : MulAut ↥L := L.normalizerMonoidHom ⟨b⁻¹, hbNi⟩
  let β : MulAut ↥L := MulAut.conj v
  have hαβ : ∀ l : ↥L, (QuotientGroup.mk (α l) : ↥L ⧸ Subgroup.center ↥L) =
      QuotientGroup.mk (β l) := by
    intro l
    apply θ.injective
    have h1 : θ (QuotientGroup.mk (α l)) = r * θ (QuotientGroup.mk l) * r⁻¹ := by
      have hmem : b⁻¹ * (l : G) * b ∈ L := by
        have := (Subgroup.mem_normalizer_iff.mp hbNi (l : G)).mp l.2
        simpa using this
      have hαl : (α l : ↥L) = ⟨b⁻¹ * (l : G) * b, hmem⟩ := by
        apply Subtype.ext
        change (L.normalizerMonoidHom ⟨b⁻¹, hbNi⟩ l : G) = b⁻¹ * (l : G) * b
        simpa using Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨b⁻¹, hbNi⟩ l
      rw [hαl]
      have h := hφ l ⟨b⁻¹ * (l : G) * b, hmem⟩ rfl
      rw [hr] at h
      exact h.symm
    have h2 : θ (QuotientGroup.mk (β l)) = r * θ (QuotientGroup.mk l) * r⁻¹ := by
      have hβl : (β l : ↥L) = v * l * v⁻¹ := by
        change (MulAut.conj v) l = v * l * v⁻¹
        exact MulAut.conj_apply v l
      rw [show (QuotientGroup.mk (β l) : ↥L ⧸ Subgroup.center ↥L) =
          QuotientGroup.mk v * QuotientGroup.mk l * (QuotientGroup.mk v)⁻¹ by
        rw [hβl]
        simp [map_mul]]
      simp only [map_mul, map_inv, hvθ]
    rw [h1, h2]
  have hαβeq : α = β :=
    CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.t2_perfect_aut_eq_of_mk_eq hLperf α β
      (fun l => hαβ l)
  have hαβcoe : ∀ l : ↥L, b⁻¹ * (l : G) * b = v * (l : G) * v⁻¹ := by
    intro l
    have h := congrArg (fun f : MulAut ↥L => (f l : G)) hαβeq
    have hαlcoe : (α l : G) = b⁻¹ * (l : G) * b := by
      change (L.normalizerMonoidHom ⟨b⁻¹, hbNi⟩ l : G) = b⁻¹ * (l : G) * b
      simpa using Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨b⁻¹, hbNi⟩ l
    have hβlcoe : (β l : G) = v * (l : G) * v⁻¹ := by
      change ((MulAut.conj v) l : G) = (v : G) * (l : G) * (v : G)⁻¹
      simpa using congrArg (fun x : ↥L => (x : G)) (MulAut.conj_apply v l)
    rw [hαlcoe, hβlcoe] at h
    exact h
  refine ⟨v⁻¹, Subgroup.inv_mem _ v.2, ?_⟩
  intro l hl
  have hm : b * l * b⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hbN l).mp hl
  have h := hαβcoe ⟨b * l * b⁻¹, hm⟩
  have h' : l = v * (b * l * b⁻¹) * v⁻¹ := by
    simpa [mul_assoc] using h
  have hX : b * l * b⁻¹ = v⁻¹ * l * v := by
    calc b * l * b⁻¹ = v⁻¹ * (v * (b * l * b⁻¹) * v⁻¹) * v := by
          simp only [Subgroup.coe_inv, Subgroup.coe_mul]
          group
      _ = v⁻¹ * l * v := by rw [← h']
  simpa [Subgroup.coe_inv] using hX

theorem ggResF4_innerOnL
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs L : Subgroup G}
    (hF4 : GGInnerDiagOnLabel (fun p lab => p = 3 ∧ lab.tag = .F4 ∧ lab.n = 1) p Bs L)
    (hLperf : commutator ↥L = ⊤) :
    ∀ b ∈ Bs, ∃ k ∈ L, ∀ l ∈ L, b * l * b⁻¹ = k * l * k⁻¹ := by
  refine ggResF4_innerOnL_of_label (p := p)
    (hF4 := largeEvenMarking_mono (fun lab R _ I F θ hP =>
      ⟨⟨hP.1.1, hP.1.2.1⟩, hP.2⟩) hF4) hLperf

theorem ggResF4_automizerJ_card_ge_48
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {f : ℕ}
    (hZk : GGCentreTwoKnown)
    (hCfg : GGConfig 3 B Bs x L D J) (hCard : Nat.card Bs = 3 ^ 5)
    (hF4 : GGHasLabel ⟨.F4, 0, f⟩ (↥L ⧸ Subgroup.center ↥L))
    (hLperf : commutator ↥L = ⊤)
    (hZL : ∀ g ∈ Subgroup.center ↥L, Nat.Coprime 3 (orderOf g))
    (hInnL : ∀ b ∈ Bs, ∃ k ∈ L, ∀ l ∈ L, b * l * b⁻¹ = k * l * k⁻¹) :
    48 ≤ Nat.card ↥(ggAutomizer J Bs) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Group.IsPerfect ↥L := Group.isPerfect_def.mpr hLperf
  obtain ⟨hJL, z, hz1, hz3, hJlayer, hJcomp, hEcz, hEea, hEcard⟩ :=
    ggR4Meet_data hCfg hCard hZL hInnL
  let eJ : ↥(J.subgroupOf L) ≃* ↥J := Subgroup.subgroupOfEquivOfLe hJL
  have hJperfSubClass : Group.IsPerfect ↥(J.subgroupOf L) :=
    Group.isPerfect_def.mpr hJcomp.2.2.1
  have hJperfClass : Group.IsPerfect ↥J :=
    Group.IsPerfect.ofSurjective (f := eJ.toMonoidHom) eJ.surjective
  have hJperf : commutator ↥J = ⊤ := Group.isPerfect_def.mp hJperfClass
  have hC3L : GGHasLabel ⟨.C, 3, f⟩
      (↥(J.subgroupOf L) ⧸ Subgroup.center ↥(J.subgroupOf L)) :=
    ggF4OrderThree_layer_label hF4 hz1 hz3 hJlayer hJcomp
  have hC3J : GGHasLabel ⟨.C, 3, f⟩ (↥J ⧸ Subgroup.center ↥J) := by
    apply ggHasLabel_of_mulEquiv (QuotientGroup.congr
      (Subgroup.center ↥(J.subgroupOf L)) (Subgroup.center ↥J) eJ
      (Subgroup.map_center_eq eJ))
    exact hC3L
  have hEbound := ggF4OrderThree_card_le hF4 hz1 hz3 hJlayer hJcomp hEcz hEea
  have hEinter : ((Bs ⊓ L).subgroupOf L) ⊓ (J.subgroupOf L) =
      (Bs ⊓ J).subgroupOf L := by
    apply Subgroup.ext
    intro u
    rw [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
      Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · rintro ⟨⟨hBs, hL⟩, hJ⟩
      exact ⟨hBs, hJ⟩
    · rintro ⟨hBs, hJ⟩
      exact ⟨⟨hBs, hJL hJ⟩, hJ⟩
  have hE3 : 3 ^ 3 ≤ Nat.card ↥(Bs ⊓ J) := by
    have h := hEbound
    rw [hEinter] at h
    have hsub : Nat.card ↥((Bs ⊓ J).subgroupOf L) = Nat.card ↥(Bs ⊓ J) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right.trans hJL)).toEquiv
    rw [hsub] at h
    omega
  have hZJ : ∀ g ∈ Subgroup.center ↥J, Nat.Coprime 3 (orderOf g) :=
    fun g hg => ggR4J_center_coprime hZk hJperf hC3J g hg
  have hInnJ : ∀ b ∈ Bs, ∃ k ∈ J, ∀ l ∈ J, b * l * b⁻¹ = k * l * k⁻¹ := by
    intro b hb
    refine ggR4J_inn_of_meet (p := 3) hCfg.tableB_facts.2.1
      (hCfg.2.2.1.1.trans hCfg.2.1.1) hCfg.2.2.1.2.2.1 ?_ hZJ (le_of_eq hCard) hE3 b hb
    have hDJ : D ≤ Subgroup.centralizer (J : Set G) := by
      have hD_eq := (hCfg.2.2.1.2.2.2.2).2.2
      rw [hD_eq]
      exact inf_le_right
    exact hDJ
  exact ggR4J_card_ge_c3 hCfg.tableB_facts.2.1 hCfg.2.1.2.2.2 hJperf hZJ hInnJ hC3J
lemma range_ggGamma_eq_map
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hCfg : GGConfig 3 B Bs x L D J)
    (hZL : ∀ g ∈ Subgroup.center ↥L, Nat.Coprime 3 (orderOf g))
    (hInnL : ∀ b ∈ Bs, ∃ k ∈ L, ∀ l ∈ L, b * l * b⁻¹ = k * l * k⁻¹)
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G)) :
    (ggGamma L hBsN).range = Subgroup.map MulAut.conj ((Bs ⊓ L).subgroupOf L) := by
  haveI : Fact (Nat.Prime 3) := ⟨hCfg.tableB_facts.1⟩
  have hBsEA : CFSG.Open.IsElemAbelian 3 Bs := hCfg.tableB_facts.2.1
  have hSC := hCfg.2.1.2.2.2
  obtain ⟨hsplit, -, -, -, -⟩ := ggLemma47c hBsEA hSC hZL hInnL
  have hcomm : ∀ a ∈ Bs ⊓ L, ∀ c ∈ Bs ⊓ Subgroup.centralizer (L : Set G), a * c = c * a :=
    fun a ha c hc => CFSG.Open.IsElemAbelian.comm hBsEA
      (Subgroup.mem_inf.mp ha).1 (Subgroup.mem_inf.mp hc).1
  ext φ
  constructor
  · rintro ⟨b, rfl⟩
    have hb : (b : G) ∈ (Bs ⊓ L) ⊔ (Bs ⊓ Subgroup.centralizer (L : Set G)) := by
      rw [← hsplit]
      exact b.2
    obtain ⟨a, ha, c, hc, hdec⟩ := (CFSG.mem_sup_of_commute hcomm).mp hb
    have haBs : a ∈ Bs := (Subgroup.mem_inf.mp ha).1
    have haL : a ∈ L := (Subgroup.mem_inf.mp ha).2
    have hcBs : c ∈ Bs := (Subgroup.mem_inf.mp hc).1
    have hcC : c ∈ Subgroup.centralizer (L : Set G) := (Subgroup.mem_inf.mp hc).2
    have hγa : ggGamma L hBsN ⟨a, haBs⟩ = MulAut.conj ⟨a, haL⟩ := by
      ext l
      rw [ggGamma_coe, MulAut.conj_apply]
      rfl
    have hγc : ggGamma L hBsN ⟨c, hcBs⟩ = 1 := by
      ext l
      simp only [MulAut.one_apply]
      rw [ggGamma_coe]
      change c * (l : G) * c⁻¹ = (l : G)
      have hlc : (l : G) * c = c * (l : G) :=
        Subgroup.mem_centralizer_iff.mp hcC (l : G) l.2
      rw [← hlc]
      group
    refine ⟨⟨a, haL⟩, ?_, ?_⟩
    · exact Subgroup.mem_subgroupOf.mpr ha
    · have hb_eq : b = ⟨a, haBs⟩ * ⟨c, hcBs⟩ := Subtype.ext (by
        change (b : G) = a * c
        exact hdec.symm)
      rw [hb_eq, map_mul, hγa, hγc, mul_one]
  · rintro ⟨a, ha, rfl⟩
    have haBL : (a : G) ∈ Bs ⊓ L := Subgroup.mem_subgroupOf.mp ha
    have haBs : (a : G) ∈ Bs := haBL.1
    refine ⟨⟨a, haBs⟩, ?_⟩
    ext l
    rw [ggGamma_coe, MulAut.conj_apply]
    rfl

lemma fix_ggGamma_eq_centralizer
    {G : Type} [Group G] {Bs L : Subgroup G} {z : G} (hzL : z ∈ L) (hzBs : z ∈ Bs)
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G)) :
    ggFixSub (ggGamma L hBsN ⟨z, hzBs⟩) =
      Subgroup.centralizer ({(⟨z, hzL⟩ : ↥L)} : Set ↥L) := by
  ext l
  rw [mem_ggFixSub, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    apply Subtype.ext
    have h' : z * (l : G) * z⁻¹ = (l : G) := by
      simpa only [ggGamma_coe] using congrArg (fun x : ↥L => (x : G)) h
    have h'' : z * (l : G) = (l : G) * z := by
      have := congrArg (fun x : G => x * z) h'
      simpa [mul_assoc] using this
    exact h''.symm
  · intro h
    apply Subtype.ext
    rw [ggGamma_coe]
    have hg : (l : G) * z = z * (l : G) := by
      simpa using congrArg (fun x : ↥L => (x : G)) h
    calc z * (l : G) * z⁻¹ = ((l : G) * z) * z⁻¹ := by rw [hg.symm]
      _ = (l : G) := by group

theorem ggResF4_automizerL_card_eq_1152
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hCfg : GGConfig 3 B Bs x L D J) (hCard : Nat.card Bs = 3 ^ 5)
    (hF4 : GGInnerDiagOnLabel (fun p lab => p = 3 ∧ lab.tag = .F4 ∧ lab.n = 1) 3 Bs L)
    (hLperf : commutator ↥L = ⊤)
    (hZL : ∀ g ∈ Subgroup.center ↥L, Nat.Coprime 3 (orderOf g))
    (hInnL : ∀ b ∈ Bs, ∃ k ∈ L, ∀ l ∈ L, b * l * b⁻¹ = k * l * k⁻¹) :
    Nat.card ↥(ggAutomizer L Bs) = 1152 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨hCfg.tableB_facts.1⟩
  haveI : Group.IsPerfect ↥L := Group.isPerfect_def.mpr hLperf
  have hF4mark := hF4
  obtain ⟨-, lab, -, hraw⟩ := hF4
  obtain ⟨tag, rank, n⟩ := lab
  obtain ⟨R₀, _, I₀, F₀, hP₀⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨-, -, θ₀, hP₀'⟩ := hP₀
  obtain ⟨⟨-, htag, hn⟩, -, -⟩ := hP₀'
  cases htag
  cases hn
  change LargeEvenRawDatum ⟨.F4, 4, 1⟩ _ at hraw
  have hKG := KGA.ggPumpCAutKnownF4_of_cent ggLabelRigidInput_holds
    KGA.ggF4C3CentInputStrong_holds
  have hSCF4raw := hKG 3 Nat.prime_three (by norm_num) 1 (by norm_num) (by norm_num) _ hraw
  obtain ⟨R, _, I, F, hQ, hSCF4⟩ := largeEvenRawDatum_exists hSCF4raw
  obtain ⟨-, -, θ, hP⟩ := hQ
  obtain ⟨-, hBsN, hBs3⟩ := hP
  have hAh : CFSG.Open.IsElemAbelian 3 (ggGamma L hBsN).range :=
    (ggGamma_range_hypsSC_L hCfg θ hBsN hBs3).1
  have hAI : ∀ a ∈ (ggGamma L hBsN).range, ∃ φ ∈ I, ∀ l : ↥L,
      φ (ggQuotHom θ l) = ggQuotHom θ (a l) :=
    (ggGamma_range_hypsSC_L hCfg θ hBsN hBs3).2.1
  have h3A : 3 ^ 3 ≤ Nat.card ↥(ggGamma L hBsN).range :=
    (ggGamma_range_hypsSC_L hCfg θ hBsN hBs3).2.2.1
  have hscA : GGTorusSelfCent 3 (ggGamma L hBsN).range :=
    (ggGamma_range_hypsSC_L hCfg θ hBsN hBs3).2.2.2
  obtain ⟨hcardBL, z, hzL, hzBs, hz1, hz3, hCD⟩ := ggR4Meet_split hCfg hCard hZL hInnL
  have hPre := hCfg.2.2.1
  obtain ⟨-, -, -, -, hJD, hJC, -⟩ := hPre
  have hJz : J = LargeEvenLayer (L ⊓ Subgroup.centralizer ({z} : Set G)) := by
    rw [← hCD]
    exact hJD
  have hCz : IsComponentOf J (L ⊓ Subgroup.centralizer ({z} : Set G)) := by
    rw [← hCD]
    exact hJC
  obtain ⟨hJL, hJlayer, hJcomp⟩ := ggR4Meet_transport hzL hJz hCz
  have hLabel4 : GGHasLabel ⟨.F4, 4, 1⟩ (↥L ⧸ Subgroup.center ↥L) := by
    unfold GGHasLabel
    exact largeEvenRawDatum_mono (fun R _ I F h => ⟨h.2.2.choose⟩) hraw
  have hLabel : GGHasLabel ⟨.F4, 0, 1⟩ (↥L ⧸ Subgroup.center ↥L) := by
    simpa [GGHasLabel, LargeEvenRawDatum] using hLabel4
  have hz1' : (⟨z, hzL⟩ : ↥L) ≠ 1 := by
    intro h
    exact hz1 (congrArg Subtype.val h)
  have hz3' : (⟨z, hzL⟩ : ↥L) ^ 3 = 1 := Subtype.ext (by simpa using hz3)
  have hC3L : GGHasLabel ⟨.C, 3, 1⟩
      (↥(J.subgroupOf L) ⧸ Subgroup.center ↥(J.subgroupOf L)) :=
    ggF4OrderThree_layer_label hLabel hz1' hz3' hJlayer hJcomp
  have hfix := fix_ggGamma_eq_centralizer hzL hzBs hBsN
  have hJcompFix : IsComponentOf (J.subgroupOf L)
      (ggFixSub (ggGamma L hBsN ⟨z, hzBs⟩)) := by
    rw [hfix]
    exact hJcomp
  let e : MulAut ↥L := ggGamma L hBsN ⟨z, hzBs⟩
  have heA : e ∈ (ggGamma L hBsN).range := ⟨⟨z, hzBs⟩, rfl⟩
  let ψ : ↥L →* R := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
  have hψsurj : Function.Surjective ψ :=
    θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hψker : ψ.ker ≤ Subgroup.center ↥L := by
    intro q hq
    rw [MonoidHom.mem_ker] at hq
    have hq' : (QuotientGroup.mk' (Subgroup.center ↥L)) q = 1 := by
      apply θ.injective
      simpa [ψ] using hq
    exact (QuotientGroup.eq_one_iff q).mp hq'
  have hSCF4app := hSCF4 ↥L ψ hψsurj hψker hLperf (ggGamma L hBsN).range hAh hAI h3A hscA
    ⟨e, heA, J.subgroupOf L, hJcompFix, hC3L⟩
  have hcard1 : Nat.card ↥(ggAutomizer L Bs) =
      Nat.card ↥(ggAutomizer L (Bs ⊓ L)) :=
    (ggLemma47c hCfg.tableB_facts.2.1 hCfg.2.1.2.2.2 hZL hInnL).2.2.2.2
  have hBsEA : CFSG.Open.IsElemAbelian 3 Bs := hCfg.tableB_facts.2.1
  have hBXea : CFSG.Open.IsElemAbelian 3 (Bs ⊓ L) := by
    constructor
    · refine ⟨⟨fun a b => ?_⟩⟩
      apply Subtype.ext
      exact CFSG.Open.IsElemAbelian.comm hBsEA
        (Subgroup.mem_inf.mp a.2).1 (Subgroup.mem_inf.mp b.2).1
    · intro a ha
      exact hBsEA.2 a (Subgroup.mem_inf.mp ha).1
  have hcard2 : Nat.card ↥(ggAutomizer L (Bs ⊓ L)) =
      Nat.card ↥(ggAutomizer (MulAut.conj : ↥L →* MulAut ↥L).range
        (Subgroup.map MulAut.conj ((Bs ⊓ L).subgroupOf L))) :=
    ggAutomizer_card_eq_inn inf_le_right hBXea hZL
  have hrange := range_ggGamma_eq_map hCfg hZL hInnL hBsN
  calc Nat.card ↥(ggAutomizer L Bs)
      = Nat.card ↥(ggAutomizer L (Bs ⊓ L)) := hcard1
    _ = Nat.card ↥(ggAutomizer (MulAut.conj : ↥L →* MulAut ↥L).range
          (Subgroup.map MulAut.conj ((Bs ⊓ L).subgroupOf L))) := hcard2
    _ = Nat.card ↥(ggAutomizer (MulAut.conj : ↥L →* MulAut ↥L).range
          (ggGamma L hBsN).range) := by rw [← hrange]
    _ = 1152 := hSCF4app.2


lemma ggResF4_marking_normalizer
    {G : Type} [Group G] [Finite G] {Bs L : Subgroup G}
    (hF4 : GGInnerDiagOnLabel (fun p lab => p = 3 ∧ lab.tag = .F4 ∧ lab.n = 1) 3 Bs L) :
    Bs ≤ Subgroup.normalizer (L : Set G) := by
  obtain ⟨-, lab, -, hraw⟩ := hF4
  obtain ⟨R, _, I, F, hQ⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨θ, hP⟩ := hQ.2.2
  exact hP.2.1

lemma ggResF4_card_Bs_le_five_of_label
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hCfg : GGConfig 3 B Bs x L D J)
    (hLperf : commutator ↥L = ⊤)
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hInnL : ∀ b ∈ Bs, ∃ k ∈ L, ∀ l ∈ L, b * l * b⁻¹ = k * l * k⁻¹)
    {fld : ℕ} (hLabel : GGHasLabel ⟨.F4, 0, fld⟩ (↥L ⧸ Subgroup.center ↥L)) :
    Nat.card Bs ≤ 3 ^ 5 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨hCfg.tableB_facts.1⟩
  have hBsEA : CFSG.Open.IsElemAbelian 3 Bs := hCfg.tableB_facts.2.1
  let ρ : ↥Bs →* MulAut ↥L :=
    (L.normalizerMonoidHom).comp (Subgroup.inclusion hBsN)
  have hρcoe : ∀ (b : ↥Bs) (l : ↥L), ((ρ b) l : G) = (b : G) * (l : G) * (b : G)⁻¹ := by
    intro b l
    simp only [ρ, MonoidHom.comp_apply, Subgroup.normalizerMonoidHom_apply_apply_coe]
    rfl
  have hρrange : ∀ b : ↥Bs, ρ b ∈ MulAut.conj.range := by
    intro b
    obtain ⟨k, hk, hkl⟩ := hInnL b b.2
    refine ⟨⟨k, hk⟩, ?_⟩
    ext l
    rw [hρcoe]
    simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
    exact (hkl l l.2).symm
  have hρle : ρ.range ≤ MulAut.conj.range := by
    rw [← Subgroup.map_top ρ, Subgroup.map_le_iff_le_comap]
    intro b _
    exact hρrange b
  let f : ↥Bs →* ↥(MulAut.conj.range) :=
    (Subgroup.inclusion hρle).comp ρ.rangeRestrict
  let eInn : ↥(MulAut.conj : ↥L →* MulAut ↥L).range ≃* (↥L ⧸ Subgroup.center ↥L) :=
    (QuotientGroup.quotientKerEquivRange (MulAut.conj : ↥L →* MulAut ↥L)).symm.trans
      (QuotientGroup.quotientMulEquivOfEq (CFSG.GroupTheory.ker_conj_eq_center (G := ↥L)))
  let g : ↥Bs →* (↥L ⧸ Subgroup.center ↥L) := eInn.toMonoidHom.comp f
  have hker : g.ker = (Bs ⊓ Subgroup.centralizer (L : Set G)).subgroupOf Bs := by
    ext b
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro h
      have hf : f b = 1 := by
        apply eInn.injective
        simpa [g] using h
      have hρ : ρ b = 1 := by
        have hval := congrArg (fun y : ↥(MulAut.conj.range) => (y : MulAut ↥L)) hf
        simpa [f] using hval
      refine ⟨b.2, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have h1 : (ρ b) ⟨l, hl⟩ = ⟨l, hl⟩ := by rw [hρ]; rfl
      have h2 : (b : G) * l * (b : G)⁻¹ = l := by
        have := congrArg (fun y : ↥L => (y : G)) h1
        rwa [hρcoe] at this
      have h2' : (b : G) * l = l * (b : G) := by
        calc (b : G) * l = ((b : G) * l * (b : G)⁻¹) * (b : G) := by group
          _ = l * (b : G) := by rw [h2]
      exact h2'.symm
    · rintro ⟨hb, hc⟩
      have hρ : ρ b = 1 := by
        ext l
        rw [hρcoe]
        simp only [MulAut.one_apply]
        have hcl := Subgroup.mem_centralizer_iff.mp hc (l : G) l.2
        calc (b : G) * (l : G) * (b : G)⁻¹ = ((l : G) * (b : G)) * (b : G)⁻¹ := by rw [hcl]
          _ = (l : G) := by group
      have hf : f b = 1 := by
        apply Subtype.ext
        simpa [f] using hρ
      simp [g, hf]
  have hkerCard : Nat.card ↥g.ker = 3 := by
    rw [hker]
    have hsub : Nat.card ↥((Bs ⊓ Subgroup.centralizer (L : Set G)).subgroupOf Bs) =
        Nat.card ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    rw [hsub]
    exact hCfg.card_bstar_inf_centralizer_L
  have htopEA : CFSG.Open.IsElemAbelian 3 (⊤ : Subgroup ↥Bs) := by
    constructor
    · refine ⟨⟨fun a b => by
        apply Subtype.ext
        apply Subtype.ext
        simpa using CFSG.Open.IsElemAbelian.comm hBsEA
          (a : ↥Bs).2 (b : ↥Bs).2⟩⟩
    · intro a _
      exact Subtype.ext (by simpa using hBsEA.2 (a : G) a.2)
  have hImageEA : CFSG.Open.IsElemAbelian 3 g.range := by
    have h := CFSG.Open.IsElemAbelian.map (E := (⊤ : Subgroup ↥Bs)) htopEA g
    rw [Subgroup.map_top] at h
    exact h
  have hLabel0 := hLabel
  unfold GGHasLabel LargeEvenRawDatum LargeEvenRecipeChevalley at hLabel
  obtain ⟨K, hKfield, hKfin, hKcard, ⟨eR⟩⟩ := hLabel
  letI : Field K := hKfield
  letI : Finite K := hKfin
  haveI : IsSimpleGroup (LargeEvenCenterQuot (LargeEvenChevH LargeEvenCartanF4 K false)) := by
    have hq := CFSG.LieType.Steinberg.Adjoint.isQuasisimple_f4 (K := K)
    haveI : IsSimpleGroup (CFSG.Blueprint.AdjointQuotient .F4 K) := hq.2.1
    obtain ⟨eR'⟩ := centerQuot_chevGroup_equiv K .F4
    exact eR'.isSimpleGroup
  haveI : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := eR.isSimpleGroup
  haveI : Group.IsPerfect ↥L := Group.isPerfect_def.mpr hLperf
  haveI : Group.IsPerfect (↥L ⧸ Subgroup.center ↥L) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (Subgroup.center ↥L))
      (QuotientGroup.mk'_surjective _)
  have hnoncommQ : ¬ IsMulCommutative (↥L ⧸ Subgroup.center ↥L) := by
    intro hcomm
    haveI : IsMulCommutative (↥L ⧸ Subgroup.center ↥L) := hcomm
    have hbot : commutator (↥L ⧸ Subgroup.center ↥L) = ⊥ :=
      commutator_eq_bot (G := ↥L ⧸ Subgroup.center ↥L)
    have htop : commutator (↥L ⧸ Subgroup.center ↥L) = ⊤ := Group.isPerfect_def.mp inferInstance
    rw [hbot] at htop
    exact bot_ne_top htop
  have hZbot : Subgroup.center (↥L ⧸ Subgroup.center ↥L) = ⊥ :=
    TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative hnoncommQ
  have hLabelQ : GGHasLabel ⟨.F4, 0, fld⟩
      ((↥L ⧸ Subgroup.center ↥L) ⧸ Subgroup.center (↥L ⧸ Subgroup.center ↥L)) := by
    unfold GGHasLabel at hLabel0 ⊢
    exact largeEvenRawDatum_mono (fun R' _ I F h => by
      obtain ⟨e⟩ := h
      exact ⟨(QuotientGroup.quotientMulEquivOfEq hZbot).trans
        QuotientGroup.quotientBot |>.trans e⟩) hLabel0

  have hImg4 : Nat.card ↥g.range ≤ 3 ^ 4 :=
    card_le_pow_four_of_ggHasLabel_F4 hLabelQ hImageEA
  have hmul : Nat.card ↥g.ker * Nat.card ↥g.range = Nat.card ↥Bs :=
    Subgroup.card_ker_mul_card_range g
  calc Nat.card ↥Bs = Nat.card ↥g.ker * Nat.card ↥g.range := hmul.symm
    _ = 3 * Nat.card ↥g.range := by rw [hkerCard]
    _ ≤ 3 * 3 ^ 4 := Nat.mul_le_mul_left 3 hImg4
    _ = 3 ^ 5 := by norm_num


lemma ggResF4_card_Bs_le_five
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hCfg : GGConfig 3 B Bs x L D J)
    (hLperf : commutator ↥L = ⊤)
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hInnL : ∀ b ∈ Bs, ∃ k ∈ L, ∀ l ∈ L, b * l * b⁻¹ = k * l * k⁻¹)
    (hLabel : GGHasLabel ⟨.F4, 0, 1⟩ (↥L ⧸ Subgroup.center ↥L)) :
    Nat.card Bs ≤ 3 ^ 5 :=
  ggResF4_card_Bs_le_five_of_label hCfg hLperf hBsN hInnL (fld := 1) hLabel

lemma ggResF4_card_Bs_eq_five
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hCfg : GGConfig 3 B Bs x L D J)
    (hLperf : commutator ↥L = ⊤)
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hInnL : ∀ b ∈ Bs, ∃ k ∈ L, ∀ l ∈ L, b * l * b⁻¹ = k * l * k⁻¹)
    (hF4 : GGInnerDiagOnLabel (fun p lab => p = 3 ∧ lab.tag = .F4 ∧ lab.n = 1) 3 Bs L) :
    Nat.card Bs = 3 ^ 5 := by
  have hLabel : GGHasLabel ⟨.F4, 0, 1⟩ (↥L ⧸ Subgroup.center ↥L) :=
    ggResF4_hasLabel_F4 hF4
  have hle : Nat.card Bs ≤ 3 ^ 5 :=
    ggResF4_card_Bs_le_five hCfg hLperf hBsN hInnL hLabel
  have hS : LargeEvenSStar 3 B x L := hCfg.1.2.2.2.2.2.2.1
  have hrank4 : 4 ≤ LargeEvenTwoLocalRank 3 G := hCfg.1.2.2.2.2.2.1.2.2.2
  have hBcard : Nat.card B = 3 ^ LargeEvenTwoLocalRank 3 G := hS.1.2.1
  have hB4 : 3 ^ 4 ≤ Nat.card B := by
    rw [hBcard]
    exact Nat.pow_le_pow_right (by norm_num) hrank4
  have h4 : 3 ^ 4 ≤ Nat.card Bs :=
    hB4.trans (Subgroup.card_le_of_le hCfg.2.1.1)
  have hMark : LargeEvenMarking ↥L (fun lab _ _ _ _ _ => lab.tag = .F4 ∧ lab.n = 1) :=
    largeEvenMarking_mono (fun lab R _ I F θ hP => hP.1.2) hF4
  have hge : 3 ^ 5 ≤ Nat.card Bs :=
    ggL48F4TwoThree_pow_five_le_card ggL48F4TwoThreeConfigInput_holds
      hCfg.1 hCfg.2.1 h4 hMark
  omega


theorem ggResF4_exactTwo_false_of_card
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G}
    (hZk : GGCentreTwoKnown)
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hCard : Nat.card Bs = 3 ^ 5)
    (hF4 : GGInnerDiagOnLabel (fun p lab => p = 3 ∧ lab.tag = .F4 ∧ lab.n = 1) 3 Bs L)
    (h2 : GGResLeviDatumExact2 3 Bs L J K ggSelAny ggTypAny) :
    False := by
  have hCfg : GGConfig 3 B Bs x L D J := hH.1
  have hS : LargeEvenSStar 3 B x L := hCfg.1.2.2.2.2.2.2.1
  have hLperf : commutator ↥L = ⊤ := hS.2.2.2.1.2.2.1
  haveI : Finite ↥L := Finite.of_injective (Subgroup.subtype L) Subtype.coe_injective
  haveI : Fintype ↥L := Fintype.ofFinite _
  haveI : Group.IsPerfect ↥L := Group.isPerfect_def.mpr hLperf
  haveI : Fintype ↥(Subgroup.center ↥L) := Fintype.ofFinite _
  have hLabel : GGHasLabel ⟨.F4, 0, 1⟩ (↥L ⧸ Subgroup.center ↥L) :=
    ggResF4_hasLabel_F4 hF4
  have hZcard : ¬ 3 ∣ Nat.card ↥(Subgroup.center ↥L) :=
    not_three_dvd_card_center_of_ggHasLabel_F4 hLabel
  have hZL : ∀ g ∈ Subgroup.center ↥L, Nat.Coprime 3 (orderOf g) := by
    intro g hg
    rw [Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 3)]
    intro h3
    apply hZcard
    have hdvd : orderOf g ∣ Nat.card ↥(Subgroup.center ↥L) := by
      rw [Nat.card_eq_fintype_card]
      have h := orderOf_dvd_card (x := (⟨g, hg⟩ : ↥(Subgroup.center ↥L)))
      simpa using h
    exact dvd_trans h3 hdvd
  have hInnL : ∀ b ∈ Bs, ∃ k ∈ L, ∀ l ∈ L, b * l * b⁻¹ = k * l * k⁻¹ :=
    ggResF4_innerOnL hF4 hLperf
  have h48 := ggResF4_automizerJ_card_ge_48 hZk hCfg hCard hLabel hLperf hZL hInnL
  have hJ : ggAutomizer J Bs ≠ ⊥ := by
    intro hbot
    rw [hbot] at h48
    simpa using h48
  have h1152 := ggResF4_automizerL_card_eq_1152 hCfg hCard hF4 hLperf hZL hInnL
  have h12 := ggResF4_exactTwo_parabolic_card_le_twelve h2 hJ h1152
  omega


theorem ggResF4ExactTwo_false_of_cent
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G}
    (hZk : GGCentreTwoKnown)
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hF4 : GGInnerDiagOnLabel (fun p lab => p = 3 ∧ lab.tag = .F4 ∧ lab.n = 1) 3 Bs L)
    (h2 : GGResLeviDatumExact2 3 Bs L J K ggSelAny ggTypAny) :
    False := by
  have hCfg : GGConfig 3 B Bs x L D J := hH.1
  have hS : LargeEvenSStar 3 B x L := hCfg.1.2.2.2.2.2.2.1
  have hLperf : commutator ↥L = ⊤ := hS.2.2.2.1.2.2.1
  have hInnL : ∀ b ∈ Bs, ∃ k ∈ L, ∀ l ∈ L, b * l * b⁻¹ = k * l * k⁻¹ :=
    ggResF4_innerOnL hF4 hLperf
  have hBsN : Bs ≤ Subgroup.normalizer (L : Set G) :=
    ggResF4_marking_normalizer hF4
  have hCard : Nat.card Bs = 3 ^ 5 :=
    ggResF4_card_Bs_eq_five hCfg hLperf hBsN hInnL hF4
  exact ggResF4_exactTwo_false_of_card hZk hH hCard hF4 h2


theorem ggResF4ExactTwo_false
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hF4 : GGInnerDiagOnLabel (fun p lab => p = 3 ∧ lab.tag = .F4 ∧ lab.n = 1) 3 Bs L)
    (h2 : GGResLeviDatumExact2 3 Bs L J K ggSelAny ggTypAny) :
    False :=
  ggResF4ExactTwo_false_of_cent ggCentreTwoKnown_holds hH hF4 h2


private lemma cartanA5_prod_le_one {a b : Fin 5} (hab : a ≠ b) :
    CartanMatrix.A 5 a b * CartanMatrix.A 5 b a ≤ 1 := by
  fin_cases a <;> fin_cases b <;> simp_all [CartanMatrix.A]

private lemma labels_le_three_of_cartan_A5
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {M : CoxeterMatrix Λ} {C : Matrix Λ Λ ℤ}
    (hC : GGIntCartan M C) {e : Fin 5 ≃ Λ}
    (hCA : ∀ i j, C (e i) (e j) = CartanMatrix.A 5 i j) :
    ∀ i j, i ≠ j → M i j ≤ 3 := by
  intro i j hij
  have hM := hC.2 i j hij
  have h1 : C i j = CartanMatrix.A 5 (e.symm i) (e.symm j) := by
    simpa using hCA (e.symm i) (e.symm j)
  have h2 : C j i = CartanMatrix.A 5 (e.symm j) (e.symm i) := by
    simpa using hCA (e.symm j) (e.symm i)
  rcases hM with ⟨hm, -, -⟩ | ⟨hm, -, -⟩ | ⟨hm, hprod, -, -⟩ | ⟨hm, hprod, -, -⟩
  · omega
  · omega
  · exfalso
    let a : Fin 5 := e.symm i
    let b : Fin 5 := e.symm j
    have hab : a ≠ b := by
      intro h
      apply hij
      simpa [a, b] using congrArg e h
    have hle := cartanA5_prod_le_one hab
    have h1' : C i j = CartanMatrix.A 5 a b := by simpa [a, b] using h1
    have h2' : C j i = CartanMatrix.A 5 b a := by simpa [a, b] using h2
    rw [h1', h2'] at hprod
    omega
  · exfalso
    let a : Fin 5 := e.symm i
    let b : Fin 5 := e.symm j
    have hab : a ≠ b := by
      intro h
      apply hij
      simpa [a, b] using congrArg e h
    have hle := cartanA5_prod_le_one hab
    have h1' : C i j = CartanMatrix.A 5 a b := by simpa [a, b] using h1
    have h2' : C j i = CartanMatrix.A 5 b a := by simpa [a, b] using h2
    rw [h1', h2'] at hprod
    omega

private lemma card_le_twentyfour_of_simplyLaced_rank_three
    {ι : Type} [Fintype ι] [DecidableEq ι] {M : CoxeterMatrix ι}
    (hM : GGIsWeylMatrix M) (hcard : Fintype.card ι = 3)
    (hsl : GGSimplyLacedConnected M) : Nat.card M.Group ≤ 24 := by
  rcases hM with ⟨n, e, hn, hA | ⟨hn2, hB⟩ | ⟨hn4, hD⟩⟩ | ⟨e, hE6⟩ | ⟨e, hE7⟩ |
    ⟨e, hE8⟩ | ⟨e, hF4⟩ | ⟨e, hG2⟩
  · have hn3 : n = 3 := by
      have hc : Fintype.card ι = n := by simpa using (Fintype.card_congr e).symm
      omega
    subst hn3
    exact l05nK3a_card_reindex_le (CoxeterMatrix.A 3) e hA
      (by rw [l05nK3a_card_coxeterA 3]; norm_num)
  · have hn3 : n = 3 := by
      have hc : Fintype.card ι = n := by simpa using (Fintype.card_congr e).symm
      omega
    subst hn3
    exfalso
    have h4 : M (e 1) (e 2) = 4 := by
      rw [hB, CoxeterMatrix.reindex_apply]
      norm_num [CoxeterMatrix.B]
    have hne : e 1 ≠ e 2 := e.injective.ne (by decide)
    rcases hsl.1 (e 1) (e 2) hne with h2 | h3 <;> omega
  · have hc : Fintype.card ι = n := by simpa using (Fintype.card_congr e).symm
    omega
  · have hc : Fintype.card ι = 6 := by simpa using (Fintype.card_congr e).symm
    omega
  · have hc : Fintype.card ι = 7 := by simpa using (Fintype.card_congr e).symm
    omega
  · have hc : Fintype.card ι = 8 := by simpa using (Fintype.card_congr e).symm
    omega
  · have hc : Fintype.card ι = 4 := by simpa using (Fintype.card_congr e).symm
    omega
  · have hc : Fintype.card ι = 2 := by simpa using (Fintype.card_congr e).symm
    omega



section ExactTwoAtEitherBase

open CFSG.Monster.B.Geometry


theorem ggResF4ExactTwo_K_base_false
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hF4 : GGInnerDiagOnLabel (fun p lab => p = 3 ∧ lab.tag = .F4 ∧ lab.n = 1) 3 Bs L)
    (h2 : GGResLeviDatumExact2 3 Bs K J L ggSelAny ggTypAny) :
    False := by
  have hCfg : GGConfig 3 B Bs x L D J := hH.1
  have hS : LargeEvenSStar 3 B x L := hCfg.1.2.2.2.2.2.2.1
  have hLperf : commutator ↥L = ⊤ := hS.2.2.2.1.2.2.1
  have hInnL : ∀ b ∈ Bs, ∃ k ∈ L, ∀ l ∈ L, b * l * b⁻¹ = k * l * k⁻¹ :=
    ggResF4_innerOnL hF4 hLperf
  have hBsN : Bs ≤ Subgroup.normalizer (L : Set G) :=
    ggResF4_marking_normalizer hF4
  have hCard : Nat.card Bs = 3 ^ 5 :=
    ggResF4_card_Bs_eq_five hCfg hLperf hBsN hInnL hF4
  haveI : Finite ↥L := Finite.of_injective (Subgroup.subtype L) Subtype.coe_injective
  haveI : Fintype ↥L := Fintype.ofFinite _
  haveI : Group.IsPerfect ↥L := Group.isPerfect_def.mpr hLperf
  haveI : Fintype ↥(Subgroup.center ↥L) := Fintype.ofFinite _
  have hLabel : GGHasLabel ⟨.F4, 0, 1⟩ (↥L ⧸ Subgroup.center ↥L) :=
    ggResF4_hasLabel_F4 hF4
  have hZcard : ¬ 3 ∣ Nat.card ↥(Subgroup.center ↥L) :=
    not_three_dvd_card_center_of_ggHasLabel_F4 hLabel
  have hZL : ∀ g ∈ Subgroup.center ↥L, Nat.Coprime 3 (orderOf g) := by
    intro g hg
    rw [Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 3)]
    intro h3
    apply hZcard
    have hdvd : orderOf g ∣ Nat.card ↥(Subgroup.center ↥L) := by
      rw [Nat.card_eq_fintype_card]
      have h := orderOf_dvd_card (x := (⟨g, hg⟩ : ↥(Subgroup.center ↥L)))
      simpa using h
    exact dvd_trans h3 hdvd
  have hAJ48 := ggResF4_automizerJ_card_ge_48 ggCentreTwoKnown_holds hCfg hCard hLabel hLperf hZL hInnL
  have hJ : ggAutomizer J Bs ≠ ⊥ := by
    intro hbot
    rw [hbot] at hAJ48
    simpa using hAJ48
  have h2D := h2
  rcases h2 with ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
    hS, hΛa1, hΛa3, hML, hCL, hMK, hCK, htyp, hlin, hrefl, hpair, hpairK, hsel,
    fL, fK, hclosL, hclosK, hconn, hclosJ⟩
  letI := i1
  letI := i2
  letI := i3
  letI := i4
  letI := i5
  letI := i6
  let : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  have hcardV : Nat.card V = 3 ^ 5 := by
    rw [← card_eq_of_ggLin ι]
    exact hCard
  have hdim : Module.finrank (ZMod 3) V = 5 := by
    have : Fintype V := Fintype.ofFinite V
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 3) (V := V)] at hcardV
    rw [ZMod.card] at hcardV
    exact Nat.pow_right_injective (by norm_num : 1 < 3) hcardV
  have hlinK : ∀ i w, ggLin (p := 3) ι (φ (Sum.inl i)) w =
      w - α (Sum.inl i) w • h (Sum.inl i) := fun i w => hlin (Sum.inl i) w
  have hrankK := ggResK_rank_core_add_one hH hlinK hpair hCL.1 hclosL
  have hrankCL5 : Matrix.rank (CL.map (Int.castRingHom (ZMod 3))) + 1 ≤ 5 := by
    simpa [hdim] using hrankK
  have hle5 : Fintype.card Λ ≤ 5 := by
    have h := ggIntCartan_card_le_rank_add_one hML hCL 3 (by norm_num : (3:ℕ) ≠ 2)
    omega
  obtain ⟨fL, hfL⟩ := fL
  have hfullX : GGWeylTypeData (Fintype.card Λ) (Nat.card ↥(ggAutomizer K Bs))
      (Nat.card ↥(Subgroup.center ↥(ggAutomizer K Bs))) := by
    have h := ggWeylTypeData_of_isWeylMatrix hML
    rw [← Nat.card_congr fL.toEquiv,
      ← Nat.card_congr (Subgroup.centerCongr fL).toEquiv]
    exact h
  obtain ⟨r, hr, hsurv⟩ :=
    ggResLeviDatumCard_rank_eq_of_weylTypeData h2D hJ hfullX
  by_cases hsmall : Fintype.card Λ ≤ 4
  · have hr2 : r ≤ 2 := by omega
    have h12 := ggWeylTypeData_card_le_twelve_of_rank_le_two hsurv hr2
    omega
  · have hn5 : Fintype.card Λ = 5 := by omega
    have hranklt : Matrix.rank (CL.map (Int.castRingHom (ZMod 3))) < Fintype.card Λ := by
      omega
    have hAE := ggIntCartan_A_or_E6_of_rank_lt hML hCL (p := 3)
      (by norm_num : (3:ℕ) ≠ 2) hranklt
    rcases hAE with ⟨nA, eA, hnA, hdvd, hCA⟩ | ⟨hp3, e6, hE6⟩
    · have hnA5 : nA = 5 := by
        have hc : Fintype.card Λ = nA := by
          simpa using (Fintype.card_congr eA).symm
        omega
      subst hnA5
      have h3ML := labels_le_three_of_cartan_A5 hCL hCA
      let T : Set Λ := {i | i ∉ S}
      have hTcard : Fintype.card T = 3 := by
        change Fintype.card {i : Λ // i ∉ S} = 3
        have hsub : Fintype.card {i : Λ // i ∈ S} = S.card := by
          rw [Fintype.card_subtype]
          simp
        rw [Fintype.card_subtype_compl (fun i : Λ => i ∈ S), hsub, hS, hn5]
      have hTne : Nonempty T := Fintype.card_pos_iff.mp (by omega)
      have hMJ := l05nBL_ggIsWeylMatrix_parMatrix_of_deletedConnected S ML CL
        hML hCL hconn hTne
      have h3J : ∀ i j : T, i ≠ j → (parMatrix ML T) i j ≤ 3 := by
        intro i j hij
        exact h3ML i.1 j.1 (fun h => hij (Subtype.ext h))
      have hsl := ggSimplyLacedConnected_of_weyl hMJ h3J
      have h24 := card_le_twentyfour_of_simplyLaced_rank_three hMJ hTcard hsl
      have hclosJ' : ggAutomizer J Bs =
          Subgroup.closure (Set.range fun i : T => φ (Sum.inl i)) :=
        hclosJ
      let eJ : (parMatrix ML T).Group ≃* ↥(ggAutomizer J Bs) :=
        ggParabolic_equiv_of_generator_equiv (X := ggAutomizer K Bs)
          (J := ggAutomizer J Bs) ML T (fun i => φ (Sum.inl i)) fL hfL hclosJ'
      have hAJ24 : Nat.card ↥(ggAutomizer J Bs) ≤ 24 := by
        rw [← Nat.card_congr eJ.toEquiv]
        exact h24
      omega
    · have hc : Fintype.card Λ = 6 := by
        simpa using (Fintype.card_congr e6).symm
      omega
theorem ggResF4ExactTwo_either_false
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hF4 : GGInnerDiagOnLabel (fun p lab => p = 3 ∧ lab.tag = .F4 ∧ lab.n = 1) 3 Bs L)
    (h2 : GGResLeviDatumExact2 3 Bs L J K ggSelAny ggTypAny ∨
      GGResLeviDatumExact2 3 Bs K J L ggSelAny ggTypAny) : False := by
  rcases h2 with h2 | h2
  · exact ggResF4ExactTwo_false hH hF4 h2
  · exact ggResF4ExactTwo_K_base_false hH hF4 h2

end ExactTwoAtEitherBase

theorem GGResHyp.false_of_F4_L_label_of_A3
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hD : GGResLineJDatum 3 Bs J .A3)
    {labL : LargeEvenLabel} (hΛL : LargeEvenInLambda2 labL)
    (hLab : GGHasLabel labL (↥L ⧸ Subgroup.center ↥L))
    (htag : labL.tag = .F4) : False := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨tag, rank, n⟩ := labL
  cases htag
  have hrank : rank = 0 := by simpa [LargeEvenInLambda2] using hΛL.2
  subst hrank
  have hLperf : commutator ↥L = ⊤ := (GGConfig.data_L hH.1).2.2.2
  haveI : Group.IsPerfect ↥L := Group.IsPerfect.mk hLperf
  have hRig : GGLabelRigidInput := ggLabelRigidInput_holds
  have hInn : GGInnerDiagOn Bs L := hH.2.2.1.1
  have hBsN : Bs ≤ Subgroup.normalizer (L : Set G) := ggInnerDiagOn_le_normalizer hInn
  have hF4 : GGInnerDiagOnLabel (fun p lab => p = 3 ∧ lab.tag = .F4) 3 Bs L :=
    largeEvenMarking_mono (fun lab R _ I F θ hP =>
      ⟨⟨rfl, by rw [hP.1]⟩, hP.2⟩) (ggInnerDiagOn_relabel hRig hInn hΛL hLab)
  have hInnL : ∀ b ∈ Bs, ∃ k ∈ L, ∀ l ∈ L, b * l * b⁻¹ = k * l * k⁻¹ :=
    ggResF4_innerOnL_of_label (p := 3) hF4 hLperf
  have hZcard : ¬ 3 ∣ Nat.card (Subgroup.center ↥L) :=
    not_three_dvd_card_center_of_ggHasLabel_F4 (f := n) hLab
  have hZL : ∀ g ∈ Subgroup.center ↥L, Nat.Coprime 3 (orderOf g) := by
    intro g hg
    rw [Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 3)]
    intro h3
    apply hZcard
    haveI : Fintype ↥(Subgroup.center ↥L) := Fintype.ofFinite _
    have hdvd : orderOf g ∣ Nat.card (Subgroup.center ↥L) := by
      rw [Nat.card_eq_fintype_card]
      have h := orderOf_dvd_card (x := (⟨g, hg⟩ : Subgroup.center ↥L))
      simpa using h
    exact dvd_trans h3 hdvd
  obtain ⟨E, hE, hEea, hEcard, hEbot⟩ :=
    GGResLineJDatum.exists_coroot_subgroup_of_A3 (GGResHyp.Bs_le_normalizer_J hH) hD
  have hEbs : E ≤ Bs := hE.trans inf_le_left
  have hEJ : E ≤ J := hE.trans inf_le_right
  obtain ⟨hDB, hDea, hDcard9, hxD, hJD, hJc, hDeq⟩ := hH.1.2.2.1
  have hDbs : D ≤ Bs := hDB.trans hH.1.2.1.1
  have hDcent : D ≤ Subgroup.centralizer (J : Set G) := by
    rw [hDeq]
    exact inf_le_right
  have hEDcent : E ≤ Subgroup.centralizer (D : Set G) := by
    intro e he d hd
    exact (Subgroup.mem_centralizer_iff.mp (hDcent hd) e (hEJ he)).symm
  have hDcentE : D ≤ Subgroup.centralizer (E : Set G) :=
    Subgroup.le_centralizer_iff.mp hEDcent
  have hDnormE : D ≤ Subgroup.normalizer (E : Set G) :=
    hDcentE.trans (Subgroup.centralizer_le_normalizer (E : Set G))
  have hDE : D ⊓ E = ⊥ := by
    refine le_antisymm ?_ bot_le
    rintro g ⟨hgD, hgE⟩
    have hgC : g ∈ Subgroup.centralizer (J : Set G) := hDcent hgD
    have hmem : g ∈ E ⊓ Subgroup.centralizer (J : Set G) := ⟨hgE, hgC⟩
    rw [hEbot, Subgroup.mem_bot] at hmem
    exact hmem
  have hcardSup : Nat.card (E ⊔ D : Subgroup G) = Nat.card E * Nat.card D :=
    CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer E D hDnormE
      (disjoint_iff.mpr (by simpa [inf_comm] using hDE))
  have hlower : 3 ^ 5 ≤ Nat.card Bs := by
    calc
      3 ^ 5 = Nat.card E * Nat.card D := by rw [hEcard, hDcard9]; norm_num
      _ = Nat.card (E ⊔ D : Subgroup G) := hcardSup.symm
      _ ≤ Nat.card Bs := Subgroup.card_le_of_le (sup_le hEbs hDbs)
  have hupper : Nat.card Bs ≤ 3 ^ 5 :=
    ggResF4_card_Bs_le_five_of_label (fld := n) hH.1 hLperf hBsN hInnL hLab
  have hCard : Nat.card Bs = 3 ^ 5 := le_antisymm hupper hlower
  obtain ⟨hJL, z, hz1, hz3, hJlayer, hJcomp, hBsLz, hBsLea, hcardBsL⟩ :=
    ggR4Meet_data hH.1 hCard hZL hInnL
  have hC3L : GGHasLabel ⟨.C, 3, n⟩
      (↥(J.subgroupOf L) ⧸ Subgroup.center ↥(J.subgroupOf L)) :=
    ggF4OrderThree_layer_label (f := n) hLab hz1 hz3 hJlayer hJcomp
  let eJ : ↥(J.subgroupOf L) ≃* ↥J := Subgroup.subgroupOfEquivOfLe hJL
  have hJperfSubClass : Group.IsPerfect ↥(J.subgroupOf L) :=
    Group.isPerfect_def.mpr hJcomp.2.2.1
  have hJperfClass : Group.IsPerfect ↥J :=
    Group.IsPerfect.ofSurjective (f := eJ.toMonoidHom) eJ.surjective
  have hJperf : commutator ↥J = ⊤ := Group.isPerfect_def.mp hJperfClass
  have hC3J : GGHasLabel ⟨.C, 3, n⟩ (↥J ⧸ Subgroup.center ↥J) := by
    apply ggHasLabel_of_mulEquiv (QuotientGroup.congr
      (Subgroup.center ↥(J.subgroupOf L)) (Subgroup.center ↥J) eJ
      (Subgroup.map_center_eq eJ))
    exact hC3L
  have hZJ : ∀ g ∈ Subgroup.center ↥J, Nat.Coprime 3 (orderOf g) := by
    have hZ3 : ¬ 3 ∣ Nat.card (Subgroup.center ↥J) :=
      (exists_elemAbelian_of_ggHasLabel_C_three (f := n) hJperf hC3J).1
    intro g hg
    rw [Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 3)]
    intro h3
    apply hZ3
    haveI : Fintype ↥(Subgroup.center ↥J) := Fintype.ofFinite _
    have hdvd : orderOf g ∣ Nat.card (Subgroup.center ↥J) := by
      rw [Nat.card_eq_fintype_card]
      have h := orderOf_dvd_card (x := (⟨g, hg⟩ : Subgroup.center ↥J))
      simpa using h
    exact dvd_trans h3 hdvd
  have hE3 : 3 ^ 3 ≤ Nat.card (Bs ⊓ J : Subgroup G) := by
    calc
      3 ^ 3 = Nat.card E := by rw [hEcard]; norm_num
      _ ≤ Nat.card (Bs ⊓ J : Subgroup G) :=
        Nat.card_le_card_of_injective (fun e : E => (⟨e, hE e.2⟩ : (Bs ⊓ J : Subgroup G)))
          (fun a b h => Subtype.ext (congrArg (fun x : (Bs ⊓ J : Subgroup G) => (x : G)) h))
  have hInnJ : ∀ b ∈ Bs, ∃ k ∈ J, ∀ l ∈ J, b * l * b⁻¹ = k * l * k⁻¹ := by
    intro b hb
    refine ggR4J_inn_of_meet (p := 3) hH.1.tableB_facts.2.1
      hDbs hDcard9 hDcent hZJ (le_of_eq hCard) hE3 b hb
  have h48 : 48 ≤ Nat.card (ggAutomizer J Bs) :=
    ggR4J_card_ge_c3 hH.1.tableB_facts.2.1 hH.1.2.1.2.2.2 hJperf hZJ hInnJ hC3J
  have h24 : Nat.card (ggAutomizer J Bs) = 24 :=
    ggAutomizer_card_of_lineJDatum_A3 (p := 3) rfl hD
  omega

private theorem rawDatumLegacy_torusLift_F4
    {rank n : ℕ} {Q : LargeEvenRawCont} (hminus : 3 ∣ 2 ^ n - 1)
    (h : LargeEvenRawDatumLegacy ⟨.F4, rank, n⟩ Q) :
    LargeEvenRawDatumLegacy ⟨.F4, rank, n⟩
      (fun R _ I F => Q R I F ∧ GGTorusLift 3 4 R) := by
  dsimp only [LargeEvenRawDatumLegacy, LargeEvenRecipeChevalley] at h ⊢
  obtain ⟨K, hField, hFinite, hKcard, hQ⟩ := h
  letI : Field K := hField
  letI : Finite K := hFinite
  haveI : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hKcard
  have hpq : 3 ∣ Nat.card K - 1 := by rw [hKcard]; exact hminus
  exact ⟨K, hField, hFinite, hKcard, hQ,
    TableBF4.ggTorusLift_F4 Nat.prime_three (by norm_num) hpq⟩

private theorem rawDatumLegacy_mono_F4
    {rank n : ℕ} {Q Q' : LargeEvenRawCont}
    (hQQ' : ∀ (R : Type) [Group R] (I F : Set (MulAut R)), Q R I F → Q' R I F)
    (h : LargeEvenRawDatumLegacy ⟨.F4, rank, n⟩ Q) :
    LargeEvenRawDatumLegacy ⟨.F4, rank, n⟩ Q' := by
  dsimp only [LargeEvenRawDatumLegacy, LargeEvenRecipeChevalley] at h ⊢
  obtain ⟨K, hField, hFinite, hKcard, hQ⟩ := h
  exact ⟨K, hField, hFinite, hKcard, hQQ' _ _ _ hQ⟩

private theorem rawDatumLegacy_exists_F4
    {rank n : ℕ} {Q : LargeEvenRawCont}
    (h : LargeEvenRawDatumLegacy ⟨.F4, rank, n⟩ Q) :
    ∃ (R : Type) (_ : Group R) (I F : Set (MulAut R)), Q R I F := by
  dsimp only [LargeEvenRawDatumLegacy, LargeEvenRecipeChevalley] at h
  obtain ⟨K, hField, hFinite, hKcard, hQ⟩ := h
  letI : Field K := hField
  letI : Finite K := hFinite
  exact ⟨_, inferInstance, _, _, hQ⟩

theorem GGResHyp.actual_J_card_eq_1152_of_split_F4
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    {n : ℕ}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hmark : GGInnerDiagOnLabel (fun _ lab => lab.tag = .F4 ∧ lab.n = n) 3 Bs J)
    (hplus : ¬ 3 ∣ 2 ^ n + 1) :
    Nat.card ↥(ggAutomizer J Bs) = 1152 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hJperf, lab, hΛ, hraw⟩ := hmark
  obtain ⟨tag, rank, n'⟩ := lab
  obtain ⟨R₀, _, I₀, F₀, hQR₀⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨-, -, θ₀, hP₀⟩ := hQR₀
  have htag : tag = .F4 := hP₀.1.1
  have hn : n' = n := hP₀.1.2
  subst tag
  subst n'
  have hminus : 3 ∣ 2 ^ n - 1 := by
    rcases ggThree_dvd_two_pow_sub_or_add n with h | h
    · exact h
    · exact absurd h hplus
  have hdiv : 3 ∣ (2 ^ n - 1) * (2 ^ n + 1) := dvd_mul_of_dvd_left hminus _
  have hex : ¬ (3 = 3 ∧ 3 ∣ 2 ^ n + 1) := by
    rintro ⟨-, h⟩
    exact hplus h
  have hTorW := ggTBTorF4_holds 3 Nat.prime_three (by norm_num)
    ⟨.F4, rank, n⟩ hΛ rfl hdiv hex
  have hTorRaw := hTorW _ hraw
  have hBothRaw := rawDatumLegacy_torusLift_F4 (rank := rank) (n := n) hminus hTorRaw
  obtain ⟨R, _, I, Fset, hBoth⟩ := rawDatumLegacy_exists_F4 hBothRaw
  obtain ⟨⟨hQR, hTorW'⟩, hT⟩ := hBoth
  obtain ⟨hSimple, hNonab, θ, hP⟩ := hQR
  have hN : Bs ≤ Subgroup.normalizer (J : Set G) := hP.2.1
  have hR : 3 ^ 4 ≤ Nat.card (ggGamma J hN).range :=
    GGResHyp.pow_le_card_range_gamma_J_of_torusLift hH θ hT
  have h3 : 3 ^ 3 ≤ Nat.card (ggGamma J hN).range :=
    le_trans (Nat.pow_le_pow_right (by norm_num) (by norm_num)) hR
  have hBs : IsElemAbelian 3 Bs := hH.1.tableB_facts.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs :=
    hH.1.2.1.2.2.2
  have hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut J θ ⟨b, hN hb⟩ ∈ I := by
    intro b hb
    obtain ⟨φ, hφI, hφ⟩ := hP.2.2 b⁻¹ (Bs.inv_mem hb)
    have hφeq : φ = ggLAut J θ ⟨b, hN hb⟩ := by
      simpa using eq_ggLAut_of_induces (L := J) (θ := θ) (b := b⁻¹)
        (hN (Bs.inv_mem hb)) hφ
    simpa [hφeq] using hφI
  have hTB : GGTorusTBGroup 3 4 R I ↥J
      (ggQuotHom θ) (ggGamma J hN).range := by
    exact ggTorusTBGroup_of_marking (p := 3) (r := 4) Nat.prime_three hBs hSC hJperf θ hN hBsI hR h3
  have hTB' : GGTorusTBGroup 3 (4 - ggTorEnn 3 ⟨.F4, rank, n⟩) R I ↥J
      (ggQuotHom θ) (ggGamma J hN).range := by
    simpa [ggTorEnn, hplus] using hTB
  have hTor : GGTorusTorData (2 ^ n - 1) 4 CartanMatrix.F₄ CoxeterMatrix.F₄
      ↥J (ggGamma J hN).range := by
    simpa [ggTorEnn, ggTorMpm, hminus, hplus] using
      (hTorW' ↥J (ggQuotHom θ) (ggGamma J hN).range hTB')
  have hnpos : 0 < n := by
    have hn1 : 1 ≤ n := by simpa using hΛ.1
    omega
  have hodd : Odd (2 ^ n - 1) := CFSG.Timmesfeld.Orders.odd_two_pow_sub_one hnpos
  obtain ⟨-, e, -, -⟩ := ggTBWeyl_of_torW (p := 3) (m := 2 ^ n - 1) (N := 4)
    (by norm_num) hodd hminus hBs hSC hN hTor
  calc Nat.card (ggAutomizer J Bs) = Nat.card (CoxeterMatrix.F₄).Group :=
        Nat.card_congr e.toEquiv.symm
    _ = 1152 := l04fFRC_ord_card_coxeterF4

theorem GGResHyp.exists_F4_framePair_of_marking_nonsplit
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    {n : ℕ}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hmark : GGInnerDiagOnLabel (fun _ lab => lab.tag = .F4 ∧ lab.n = n) 3 Bs J)
    (hplus : 3 ∣ 2 ^ n + 1) :
    ∃ c₁ ∈ ggAutomizer J Bs, ∃ c₂ ∈ ggAutomizer J Bs,
      GGIsReflection 3 c₁ ∧ GGIsReflection 3 c₂ ∧ 4 ∣ orderOf (c₁ * c₂) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hmark3 : GGF4ThreeMarking Bs J :=
    largeEvenMarking_mono (fun lab R _ I F θ hP =>
      ⟨⟨hP.1.1, rfl, by rw [hP.1.2]; exact hplus⟩, hP.2.1, hP.2.2⟩) hmark
  have hR : ∀ hN : Bs ≤ Subgroup.normalizer (J : Set G),
      3 ^ 4 ≤ Nat.card (ggGamma J hN).range := fun hN =>
    ggF4Three_rank_of_marking
      (ggF4ThreeSCTransvInput_of_cube ggF4ThreeSCCubeInput_holds)
      hH.1 hH.2.2.2.1 hmark3 hN
  exact ggF4Three_framePair_of_rank hH.1 hmark3 hR

theorem GGResHyp.actual_J_automizer_card_lower_of_marking_nonsplit
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    {n : ℕ}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hmark : GGInnerDiagOnLabel (fun _ lab => lab.tag = .F4 ∧ lab.n = n) 3 Bs J)
    (hplus : 3 ∣ 2 ^ n + 1) :
    2 ^ 4 * Nat.factorial 4 ≤ Nat.card ↥(ggAutomizer J Bs) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hmark3 : GGF4ThreeMarking Bs J :=
    largeEvenMarking_mono (fun lab R _ I F θ hP =>
      ⟨⟨hP.1.1, rfl, by rw [hP.1.2]; exact hplus⟩, hP.2.1, hP.2.2⟩) hmark
  have hR : ∀ hN : Bs ≤ Subgroup.normalizer (J : Set G),
      3 ^ 4 ≤ Nat.card (ggGamma J hN).range := fun hN =>
    ggF4Three_rank_of_marking
      (ggF4ThreeSCTransvInput_of_cube ggF4ThreeSCCubeInput_holds)
      hH.1 hH.2.2.2.1 hmark3 hN
  exact ggF4Three_automizer_card_lower_of_rank hH.1 hmark3 hR

theorem GGResHyp.actual_J_not_F4_for_A3
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hD : GGResLineJDatum 3 Bs J .A3)
    (hmark : GGInnerDiagOnLabel (fun _ lab => lab.tag = .F4) 3 Bs J) : False := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hJperf, lab, hΛ, hraw⟩ := hmark
  obtain ⟨tag, rank, n⟩ := lab
  have htag : tag = .F4 := by
    obtain ⟨R, _, I, _, hQR⟩ := largeEvenRawDatum_exists hraw
    obtain ⟨-, -, θ, hP⟩ := hQR
    exact hP.1
  subst tag
  have hmarkSplit : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .F4 ∧ lab.n = n) 3 Bs J := by
    refine ⟨hJperf, ⟨.F4, rank, n⟩, hΛ, ?_⟩
    refine rawDatumLegacy_mono_F4 (fun R _ I F hP => ?_) hraw
    obtain ⟨hSimple, hNonab, θ, hPmark⟩ := hP
    exact ⟨hSimple, hNonab, θ, ⟨⟨hPmark.1, rfl⟩, hPmark.2.1, hPmark.2.2⟩⟩
  by_cases hplus : 3 ∣ 2 ^ n + 1
  ·
    obtain ⟨c₁, hc₁, c₂, hc₂, hr₁, hr₂, h4⟩ :=
      GGResHyp.exists_F4_framePair_of_marking_nonsplit hH hmarkSplit hplus
    exact (ggWeylOfType_A_no_frame (p := 3) (by norm_num)
      hH.1.tableB_facts.2.1 (ggWeylOfType_of_lineJDatum_A3 hD) hc₁ hc₂ hr₁ hr₂) h4
  ·
    have hcard1152 := GGResHyp.actual_J_card_eq_1152_of_split_F4 hH hmarkSplit hplus
    have hcard24 : Nat.card (ggAutomizer J Bs) = 24 :=
      ggAutomizer_card_of_lineJDatum_A3 rfl hD
    omega

theorem GGResHyp.actual_J_not_F4_for_A2
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hD : GGResLineJDatum 3 Bs J .A2)
    (hmark : GGInnerDiagOnLabel (fun _ lab => lab.tag = .F4) 3 Bs J) : False := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hJperf, lab, hΛ, hraw⟩ := hmark
  obtain ⟨tag, rank, n⟩ := lab
  have htag : tag = .F4 := by
    obtain ⟨R, _, I, _, hQR⟩ := largeEvenRawDatum_exists hraw
    obtain ⟨-, -, θ, hP⟩ := hQR
    exact hP.1
  subst tag
  have hmarkSplit : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .F4 ∧ lab.n = n) 3 Bs J := by
    refine ⟨hJperf, ⟨.F4, rank, n⟩, hΛ, ?_⟩
    refine rawDatumLegacy_mono_F4 (fun R _ I F hP => ?_) hraw
    obtain ⟨hSimple, hNonab, θ, hPmark⟩ := hP
    exact ⟨hSimple, hNonab, θ, ⟨⟨hPmark.1, rfl⟩, hPmark.2.1, hPmark.2.2⟩⟩
  by_cases hplus : 3 ∣ 2 ^ n + 1
  ·
    obtain ⟨c₁, hc₁, c₂, hc₂, hr₁, hr₂, h4⟩ :=
      GGResHyp.exists_F4_framePair_of_marking_nonsplit hH hmarkSplit hplus
    have h6 : Nat.card ↥(ggAutomizer J Bs) = 6 :=
      ggAutomizer_card_of_lineJDatum_A2 (p := 3) rfl hD
    have h4dvd : 4 ∣ Nat.card ↥(ggAutomizer J Bs) :=
      dvd_trans h4 (Subgroup.orderOf_dvd_natCard (ggAutomizer J Bs) (mul_mem hc₁ hc₂))
    rw [h6] at h4dvd
    norm_num at h4dvd
  ·
    have h1152 := GGResHyp.actual_J_card_eq_1152_of_split_F4 hH hmarkSplit hplus
    have h6 : Nat.card ↥(ggAutomizer J Bs) = 6 :=
      ggAutomizer_card_of_lineJDatum_A2 (p := 3) rfl hD
    omega

theorem GGResHyp.actual_J_not_F4_for_all_lines
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    {T : GGResLineJType}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hD : GGResLineJDatum 3 Bs J T)
    (hmark : GGInnerDiagOnLabel (fun _ lab => lab.tag = .F4) 3 Bs J) : False := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hJperf, lab, hΛ, hraw⟩ := hmark
  obtain ⟨tag, rank, n⟩ := lab
  have htag : tag = .F4 := by
    obtain ⟨R, _, I, _, hQR⟩ := largeEvenRawDatum_exists hraw
    obtain ⟨-, -, θ, hP⟩ := hQR
    exact hP.1
  subst tag
  have hmarkSplit : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .F4 ∧ lab.n = n) 3 Bs J := by
    refine ⟨hJperf, ⟨.F4, rank, n⟩, hΛ, ?_⟩
    refine rawDatumLegacy_mono_F4 (fun R _ I F hP => ?_) hraw
    obtain ⟨hSimple, hNonab, θ, hPmark⟩ := hP
    exact ⟨hSimple, hNonab, θ, ⟨⟨hPmark.1, rfl⟩, hPmark.2.1, hPmark.2.2⟩⟩
  have h48 : Nat.card (ggAutomizer J Bs) ≤ 48 :=
    CFSG.StandardType.ResJCubicBlock.card_ggAutomizer_le_fortyEight_of_lineJDatum hD
  by_cases hplus : 3 ∣ 2 ^ n + 1
  ·
    have h384 := GGResHyp.actual_J_automizer_card_lower_of_marking_nonsplit hH hmarkSplit hplus
    norm_num at h384
    omega
  ·
    have h1152 := GGResHyp.actual_J_card_eq_1152_of_split_F4 hH hmarkSplit hplus
    omega


end CFSG.StandardType
