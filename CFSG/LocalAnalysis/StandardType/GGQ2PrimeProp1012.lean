module

public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeModels
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceQuotient
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas
public import CFSG.GH74.GLS.C3.Layer1.PU3Thm5
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.Models.Transport
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263Rank
public import CFSG.RankThree.PartTwo.Sec4.Census.Witness46
public import CFSG.RankThree.PartOne.KF.ClsBasic
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.RankThree.PartTwo.Census.Criteria
public import CFSG.ClassicalInvolution.Asc77.AscT8X4
public import CFSG.ClassicalInvolution.Asc77.AscT8YA3
public import CFSG.ClassicalInvolution.AschTight.S1916F2a
public import CFSG.ClassicalInvolution.AschTight.S19BCSW
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.InnerOvergroup
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Reduction
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinModelSp62
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPair
public import CFSG.ClassicalInvolution.Q3.Q3AMDBStmt
public import CFSG.ClassicalInvolution.Q3.Q3T6DCfg
public import CFSG.ClassicalInvolution.Q3.Q3T6DPart1
public import CFSG.ClassicalInvolution.Q3.Q3T6OpenSDEnd
public import CFSG.ClassicalInvolution.Q3.Q3T8B10
public import CFSG.ClassicalInvolution.Q3.Q3T8P26T01
public import CFSG.ClassicalInvolution.Q3.Q3T8P26T02
public import CFSG.ClassicalInvolution.Q3.Q3T8P26TH01
public import CFSG.ClassicalInvolution.Q3.Q3TIYOAMain
public import CFSG.ClassicalInvolution.Q3.TL3S8Gold
public import CFSG.ClassicalInvolution.Q3.TL3S8Sd
public import CFSG.ClassicalInvolution.SmallCases.NobqFinal
public import CFSG.GH74.GLS.C3.Layer1.Th2PU3
public import CFSG.GH74.GLS.C3.Layer1.Th2PU3Q
public import CFSG.Goldschmidt75.TheoremB
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.L44CoverTrivial
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog8L4
public import CFSG.LocalAnalysis.EvenBN.Tits.R2.CatalogSp6
public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.CentT.Sp62
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267Facts
public import CFSG.LocalAnalysis.GLTheoremA.S3.Inputs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCenter
public import CFSG.LocalAnalysis.StandardType.GGPRankBoundsSUOuter
public import CFSG.LocalAnalysis.StandardType.GGPRankBoundsSpEight
public import CFSG.RankThree.PartOne.S9.Sylow.GlobalRelative
public import CFSG.RankThree.PartTwo.Sec13.Item135
public import CFSG.RankThree.PartTwo.Sec13.Item135Simple
public import CFSG.RankThree.PartTwo.Sec13.Item135SimpleReduce
public import CFSG.RankThree.PartTwo.Sec21.Commute33
public import CFSG.RankThree.PartTwo.Sec21.HeringFFLSp6Facts
public import CFSG.RankThree.PartTwo.Sec21.Item21Early3ProofExists
public import CFSG.RankThree.PartTwo.Sec21.Item221Proof228Statements
public import CFSG.RankThree.PartTwo.Sec21.Item221ProofZGen
public import CFSG.RankThree.PartTwo.Sec21.Item228ResProofOne
public import CFSG.RankThree.PartTwo.Sec21.Item233
public import CFSG.RankThree.PartTwo.Sec21.Item233OneProof
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVU52
public import CFSG.RankThree.PartTwo.Sec6.Item612

public section

namespace CFSG.GGQ2Prime

open Subgroup CFSG.Open CFSG.Models CFSG.Assembly CFSG.StandardType
open scoped Pointwise

structure PumpUpConfig {Y : Type} [Group Y] (K X Xk T B : Subgroup Y) (z zk d : Y) : Prop where
  K_comp : CFSG.Open.IsComponentOf K ⊤
  K_lie : CFSG.StandardType.LargeEvenMarking K (fun _ _ _ _ _ _ => True)
  X_lt : X < K
  X_comp : CFSG.Open.IsComponentOf X (K ⊓ centralizer ({z} : Set Y))
  X_model : LieModel X .PSU 5 2 1
  Xk_le : Xk ≤ X
  Xk_model : LieModel Xk .PSU 4 2 1
  T_two : IsPGroup 2 T
  T_card : Nat.card T = 4
  T_norm : T ≤ normalizer (K : Set Y)
  T_faithful : T ⊓ centralizer (K : Set Y) = ⊥
  T_cent : T ≤ centralizer (Xk : Set Y)
  B_elem : IsElemAbelian 3 B
  z_mem : z ∈ B
  zk_mem : zk ∈ B
  d_mem : d ∈ B
  B_norm_K : B ≤ normalizer (K : Set Y)
  B_norm_T : B ≤ normalizer (T : Set Y)
  B_eq : B = (B ⊓ X) ⊔ closure {z, d}
  B_cent_X : B ⊓ centralizer (X : Set Y) = closure {z, d}
  d_center : d ∈ center Y
  d_ne : d ≠ 1
  z_fpf : ∀ t ∈ T, z * t * z⁻¹ = t → t = 1
  B_selfcent : ∀ g : Y, orderOf g = 3 → g ∈ centralizer (B : Set Y) → g ∈ B
  rank : ∀ F P : Subgroup Y, IsElemAbelian 3 F → IsPGroup 2 P → P ≠ ⊥ →
    F ≤ normalizer (P : Set Y) → Nat.card (F ⊔ zpowers d : Subgroup Y) ≤ 3 ^ 6
  zk_T : zk ∈ centralizer (T : Set Y)
  zk_norm : centralizer ({zk} : Set Y) ≤ normalizer (T : Set Y)
  zk_Xk : zk ∈ centralizer (Xk : Set Y)

structure O1ppDataK {G : Type} [Group G] [Finite G]
    (B : Subgroup G) (x zn zk : G) (L X Xk Tk : Subgroup G) : Prop
    extends O1ppData B x zn L X Xk Tk where
  zk_mem : zk ∈ B
  zk_Tk : zk ∈ centralizer (Tk : Set G)
  zk_norm : centralizer ({zk} : Set G) ≤ normalizer (Tk : Set G)
  zk_Xk : zk ∈ centralizer (Xk : Set G)
  B_cent_X : B ⊓ centralizer (X : Set G) = closure {x, x * zn⁻¹}
  B_eq : B = (B ⊓ X) ⊔ closure {x, x * zn⁻¹}
  x_fpf : ∀ t ∈ Tk, x * t * x⁻¹ = t → t = 1

open Classical in
@[expose] noncomputable def o1ppMk {G : Type} [Group G] (x zn g : G) : O1ppBar x zn :=
  if hg : g ∈ centralizer ({x * zn⁻¹} : Set G) then
    QuotientGroup.mk (⟨g, hg⟩ : centralizer ({x * zn⁻¹} : Set G))
  else 1

theorem elemAbelian_comm {G : Type} [Group G]
    {p : ℕ} {E : Subgroup G} (hE : IsElemAbelian p E) {a b : G}
    (ha : a ∈ E) (hb : b ∈ E) : a * b = b * a :=
  congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem o1pp_B_le_H {G : Type} [Group G] [Finite G] {B L X Xk Tk : Subgroup G} {x zn : G}
    (h : O1ppData B x zn L X Xk Tk) : B ≤ centralizer ({x * zn⁻¹} : Set G) := by
  obtain ⟨hBab, hxB, -⟩ := ggThmIHyp_unpack h.hyp
  have hd : x * zn⁻¹ ∈ B := mul_mem hxB (inv_mem h.zn_mem)
  intro b hb
  rw [mem_centralizer_singleton_iff]
  exact elemAbelian_comm hBab hb hd

theorem o1ppMk_of_mem {G : Type} [Group G] {x zn : G}
    {g : G} (hg : g ∈ centralizer ({x * zn⁻¹} : Set G)) :
    o1ppMk x zn g = QuotientGroup.mk (⟨g, hg⟩ : centralizer ({x * zn⁻¹} : Set G)) := by
  simp [o1ppMk, hg]

theorem o1pp_X_le_cx {G : Type} [Group G] [Finite G] {B L X Xk Tk : Subgroup G} {x zn : G}
    (h : O1ppData B x zn L X Xk Tk) : X ≤ centralizer ({x} : Set G) := by
  obtain ⟨⟨-, -, -, hxD, -, -, hD⟩, -⟩ := h.stdSub
  rw [hD] at hxD
  intro a ha
  rw [mem_centralizer_singleton_iff]
  exact (mem_centralizer_iff.1 (mem_inf.1 hxD).2) a ha

theorem o1pp_X_equiv {G : Type} [Group G] [Finite G] {B L X Xk Tk : Subgroup G} {x zn : G}
    (h : O1ppData B x zn L X Xk Tk) : Nonempty (X ≃* O1ppXBar x zn X) := by
  set H := centralizer ({x * zn⁻¹} : Set G) with hH
  set O := O1ppCore x zn with hOdef
  set π := QuotientGroup.mk' (LargeEvenPPrimeCore 3 ↥H) with hπdef
  obtain ⟨hHO, hO3⟩ := o1pp_core_facts x zn
  obtain ⟨hXs, -, h3⟩ := o1pp_X_facts u52SimpleSix h
  have hXO : X ≤ normalizer (O : Set G) := le_trans h.X_le hHO
  have hXObot : X ⊓ O = ⊥ := by
    haveI := hXs
    haveI := normal_subgroupOf_of_le_normalizer hXO
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (O.subgroupOf X) with h' | h'
    · rw [subgroupOf_eq_bot] at h'
      exact disjoint_iff.1 h'.symm
    · rw [subgroupOf_eq_top] at h'
      have := Nat.Coprime.eq_one_of_dvd hO3 (h3.trans (card_dvd_of_le h'))
      omega
  set f : X →* O1ppBar x zn := π.comp (inclusion h.X_le) with hf
  have hinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro a ha
    rw [MonoidHom.mem_ker, hf, MonoidHom.comp_apply, hπdef, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at ha
    have hmem : (a : G) ∈ X ⊓ O := mem_inf.2 ⟨a.2, mem_map_of_mem _ ha⟩
    rw [hXObot, mem_bot] at hmem
    rw [mem_bot]
    exact Subtype.ext hmem
  have hrange : f.range = O1ppXBar x zn X := by
    rw [hf, MonoidHom.range_comp, inclusion_range]
  exact ⟨(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)⟩

theorem o1pp_X_comp_cent {G : Type} [Group G] [Finite G] {B L X Xk Tk : Subgroup G} {x zn zk : G}
    (h : O1ppDataK B x zn zk L X Xk Tk) :
    CFSG.Open.IsComponentOf (O1ppXBar x zn X)
      (centralizer ({o1ppMk x zn x} : Set (O1ppBar x zn))) := by
  set H := centralizer ({x * zn⁻¹} : Set G) with hH
  set π := QuotientGroup.mk' (LargeEvenPPrimeCore 3 ↥H) with hπdef
  obtain ⟨hBab, hxB, -⟩ := ggThmIHyp_unpack h.hyp
  have hxH : x ∈ H := o1pp_B_le_H h.toO1ppData hxB
  have hx : o1ppMk x zn x = π ⟨x, hxH⟩ := o1ppMk_of_mem hxH
  have hXx := o1pp_X_le_cx h.toO1ppData
  have hle : O1ppXBar x zn X ≤ centralizer ({o1ppMk x zn x} : Set (O1ppBar x zn)) := by
    rintro _ ⟨a, ha, rfl⟩
    rw [mem_centralizer_singleton_iff, hx]
    show π a * π ⟨x, hxH⟩ = π ⟨x, hxH⟩ * π a
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.1 (hXx (mem_subgroupOf.1 ha)))
  have hx3 : ∃ n : ℕ, (⟨x, hxH⟩ : H) ^ 3 ^ n = 1 :=
    ⟨1, Subtype.ext (by simpa using hBab.2 x hxB)⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hC := CFSG.ComponentClassification.LBalance.Quot.map_centralizer_eq (p := 3) hx3
  have hN : centralizer ({o1ppMk x zn x} : Set (O1ppBar x zn)) ≤
      normalizer ((O1ppXBar x zn X : Subgroup (O1ppBar x zn)) : Set (O1ppBar x zn)) := by
    intro g hg
    rw [hx] at hg
    have hg' : g ∈ (centralizer ({(⟨x, hxH⟩ : H)} : Set H)).map π := by
      rw [hπdef]; exact hC ▸ hg
    obtain ⟨y, hy, rfl⟩ := hg'
    have hyx : (y : G) ∈ centralizer ({x} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (mem_centralizer_singleton_iff.1 hy)
    have hyN := h.X_normal (mem_inf.2 ⟨hyx, y.2⟩)
    have hyN' : y ∈ normalizer ((X.subgroupOf H : Subgroup H) : Set H) := by
      rw [mem_normalizer_iff]
      intro a
      simpa only [SetLike.mem_coe, mem_subgroupOf, Subgroup.coe_mul, InvMemClass.coe_inv] using
        mem_normalizer_iff.1 hyN (a : G)
    exact le_normalizer_map π (mem_map_of_mem π hyN')
  refine ⟨hle, IsSubnormal.step hle (normal_subgroupOf_of_le_normalizer hN) (IsSubnormal.refl _),
    ?_⟩
  obtain ⟨e⟩ := o1pp_X_equiv h.toO1ppData
  obtain ⟨hXs, h2, h3⟩ := o1pp_X_facts u52SimpleSix h.toO1ppData
  haveI := hXs
  have hnc : ∃ a b : X, a * b ≠ b * a := exists_noncomm_of_simple Nat.prime_three h3
    (fun h' => by rw [h'] at h2; omega)
  haveI : IsSimpleGroup (O1ppXBar x zn X) := (MulEquiv.isSimpleGroup_congr e).1 hXs
  refine CFSG.GH74.GLS.PU3.Thm5.isQuasisimple_of_simple ?_
  obtain ⟨a, b, hab⟩ := hnc
  exact ⟨e a, e b, fun h' => hab (e.injective (by simpa [map_mul] using h'))⟩

theorem le_normalizer_of_commute {Y : Type*} [Group Y] {A C : Subgroup Y}
    (h : ∀ a ∈ A, ∀ c ∈ C, a * c = c * a) : A ≤ normalizer (C : Set Y) :=
  fun a ha => centralizer_le_normalizer _ (mem_centralizer_iff.2 fun c hc => (h a ha c hc).symm)

theorem o1pp_d_center {G : Type} [Group G] [Finite G] {B L X Xk Tk : Subgroup G} {x zn : G}
    (h : O1ppData B x zn L X Xk Tk) :
    o1ppMk x zn (x * zn⁻¹) ∈ center (O1ppBar x zn) := by
  have hdH : x * zn⁻¹ ∈ centralizer ({x * zn⁻¹} : Set G) := mem_centralizer_singleton_iff.2 rfl
  rw [o1ppMk_of_mem hdH, mem_center_iff]
  intro g
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective g
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext (mem_centralizer_singleton_iff.1 y.2)

theorem o1pp_d_facts {G : Type} [Group G] [Finite G] {B L X Xk Tk : Subgroup G} {x zn : G}
    (h : O1ppData B x zn L X Xk Tk) :
    o1ppMk x zn (x * zn⁻¹) ^ 3 = 1 ∧ o1ppMk x zn (x * zn⁻¹) ≠ 1 := by
  set H := centralizer ({x * zn⁻¹} : Set G) with hH
  obtain ⟨hBab, hxB, -⟩ := ggThmIHyp_unpack h.hyp
  have hdB : x * zn⁻¹ ∈ B := mul_mem hxB (inv_mem h.zn_mem)
  have hdH := o1pp_B_le_H h hdB
  have hd3 : (⟨x * zn⁻¹, hdH⟩ : H) ^ 3 = 1 := Subtype.ext (by simpa using hBab.2 _ hdB)
  have hd1 : (⟨x * zn⁻¹, hdH⟩ : H) ≠ 1 := by
    intro h1
    have h1' : x * zn⁻¹ = 1 := congrArg Subtype.val h1
    rw [mul_inv_eq_one] at h1'
    exact h.zn_not_mem (h1' ▸ mem_zpowers zn)
  rw [o1ppMk_of_mem hdH]
  refine ⟨by rw [← QuotientGroup.mk_pow, hd3, QuotientGroup.mk_one], fun h1 => ?_⟩
  rw [QuotientGroup.eq_one_iff] at h1
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf (⟨x * zn⁻¹, hdH⟩ : H) = 3 := orderOf_eq_prime hd3 hd1
  have hdvd := Subgroup.orderOf_dvd_natCard _ h1
  rw [hord] at hdvd
  have := Nat.Coprime.eq_one_of_dvd (CFSG.pPrimeCore_coprime_card (p := 3) (G := H)) hdvd
  omega

theorem o1pp_rank {G : Type} [Group G] [Finite G] {B L X Xk Tk : Subgroup G} {x zn : G}
    (h : O1ppData B x zn L X Xk Tk) (F P : Subgroup (O1ppBar x zn))
    (hF : IsElemAbelian 3 F) (hP2 : IsPGroup 2 P) (hP : P ≠ ⊥)
    (hFP : F ≤ normalizer (P : Set (O1ppBar x zn))) :
    Nat.card (F ⊔ zpowers (o1ppMk x zn (x * zn⁻¹)) : Subgroup (O1ppBar x zn)) ≤ 3 ^ 6 := by
  set H := centralizer ({x * zn⁻¹} : Set G) with hH
  set d := o1ppMk x zn (x * zn⁻¹) with hd
  have hdc := o1pp_d_center h
  have hd3 := (o1pp_d_facts h).1
  have hFd : IsElemAbelian 3 (F ⊔ zpowers d) :=
    hF.sup_of_commute (CFSG.Open.isElemAbelian_zpowers hd3)
      (fun a _ b hb => mem_center_iff.1 ((zpowers_le (H := center _)).2 hdc hb) a)
  have hFdN : F ⊔ zpowers d ≤ normalizer (P : Set (O1ppBar x zn)) :=
    sup_le hFP ((zpowers_le).2 (center_le_normalizer _ hdc))
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hN3 : ¬ 3 ∣ Nat.card (LargeEvenPPrimeCore 3 H) := fun h3 => by
    have := Nat.Coprime.eq_one_of_dvd (CFSG.pPrimeCore_coprime_card (p := 3) (G := H)) h3
    omega
  obtain ⟨T, E, hT1, hT2, hE, hEc, hET⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.T263.lift_normalizing Nat.prime_three (by norm_num)
      (LargeEvenPPrimeCore 3 H) hN3 hP hP2 hFd hFdN
  obtain ⟨k, hk⟩ := (hE.map H.subtype).isPGroup.exists_card_eq
  have hk6 : k ≤ 6 := by
    have := le_twoLocalPrimeRank (by norm_num) (T.map H.subtype) (E.map H.subtype)
      (by rwa [Ne, map_eq_bot_iff_of_injective _ H.subtype_injective])
      (hT2.map _) ((map_mono hET).trans (le_normalizer_map _)) (hE.map _) hk
    rwa [h.rank_six] at this
  rw [← hEc, ← card_map_of_injective H.subtype_injective, hk]
  exact Nat.pow_le_pow_right (by norm_num) hk6

end CFSG.GGQ2Prime
