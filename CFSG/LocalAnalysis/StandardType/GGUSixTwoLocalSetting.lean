module

public import CFSG.LocalAnalysis.StandardType.GGUSixTwoLemmaA
public import CFSG.LocalAnalysis.StandardType.GGUSixTwoTorus
public import CFSG.CharacterTheory.Wreathed.BrauerWongSylowCentralizer
public import Mathlib.Data.Nat.Factorization.Basic

public import CFSG.GroupTheory.SupCommute
public import CFSG.GroupTheory.CentralizerSup
public import CFSG.GroupTheory.ConjTransport
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
public import CFSG.ClassicalGroups.Unitary.Simple
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure
public import CFSG.Sporadic.Schreier.J4SOrder
public import CFSG.Sporadic.Th.KernelSimple
public import CFSG.Sporadic.Th.Simple
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.Dihedral.DihedralFusionPrefixes
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.LargeEvenClassification.TopScalarLiftSquare
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Sporadic.ThSchreier.AutCore

public section

namespace CFSG.StandardType.USixTwo

open CFSG.Assembly CFSG.Open CFSG.ComponentClassification.Burgoyne.U
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
  (relPPrimeCore_le relPPrimeCore_normal coprime_card_relPPrimeCore)

variable {G : Type*} [Group G] {K : Type} [Field K]

structure LocalSetting {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (b : G) (L : Subgroup G)
    (φ : L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) (Bs : Subgroup G) : Prop where
  card_K : Nat.card K = 4
  orderOf_b : orderOf b = 3
  le_centralizer : L ≤ Subgroup.centralizer {b}
  normal : (L.subgroupOf (Subgroup.centralizer {b})).Normal
  isCyclic : ∀ S : Subgroup G, IsPGroup 3 S → S ≤ Subgroup.centralizer (L : Set G) → IsCyclic S
  elemAbelian : IsElemAbelian 3 Bs
  mem : b ∈ Bs
  card : Nat.card Bs = 3 ^ 5
  map_inf : ((Bs ⊓ L).subgroupOf L).map φ.toMonoidHom = torU K
  exists_conj : ∃ n ∈ Subgroup.normalizer (Bs : Set G), ∃ h : n * b * n⁻¹ ∈ L,
    φ ⟨n * b * n⁻¹, h⟩ = threeA hω

@[expose] noncomputable def conjEquiv {L : Subgroup G}
    (φ : L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) (n : G) :
    L.map (MulAut.conj n : G →* G) ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) :=
  ((MulAut.conj n).subgroupMap L).symm.trans φ

theorem conjEquiv_apply {L : Subgroup G}
    (φ : L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) (n : G) {x : G} (hx : x ∈ L)
    (h : n * x * n⁻¹ ∈ L.map (MulAut.conj n : G →* G)) :
    conjEquiv φ n ⟨n * x * n⁻¹, h⟩ = φ ⟨x, hx⟩ := by
  unfold conjEquiv
  rw [MulEquiv.trans_apply, MulEquiv.subgroupMap_symm_apply]
  congr 1
  apply Subtype.ext
  change (MulAut.conj n).symm (n * x * n⁻¹) = x
  rw [MulAut.conj_symm_apply]
  group

namespace LocalSetting

variable {ω : K} {hω : ω ^ 2 + ω + 1 = 0} {b : G} {L : Subgroup G}
  {φ : L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))} {Bs : Subgroup G}

theorem b_mem_centralizer_L (hS : LocalSetting hω b L φ Bs) :
    b ∈ Subgroup.centralizer (L : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  exact Subgroup.mem_centralizer_singleton_iff.mp (hS.le_centralizer hl)

theorem b_mem_centralizer_b (hS : LocalSetting hω b L φ Bs) :
    b ∈ Subgroup.centralizer ({b} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff]

theorem centralizer_Bs_le_centralizer_b (hS : LocalSetting hω b L φ Bs) :
    Subgroup.centralizer (Bs : Set G) ≤ Subgroup.centralizer ({b} : Set G) :=
  Subgroup.centralizer_le (by intro x hx; rw [Set.mem_singleton_iff] at hx; subst hx; exact hS.mem)

theorem centralizer_b_le_normalizer_L (hS : LocalSetting hω b L φ Bs) :
    Subgroup.centralizer ({b} : Set G) ≤ Subgroup.normalizer (L : Set G) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer hS.le_centralizer).mp hS.normal

theorem isSimpleGroup_L [Finite K] (hS : LocalSetting hω b L φ Bs) : IsSimpleGroup L := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Nat.card K = (2 ^ 1) ^ 2 := by rw [hS.card_K]; norm_num
  have hU : IsSimpleGroup (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) :=
    CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K 2 1 hK 6
      (by norm_num) (by norm_num)
  exact MulEquiv.isSimpleGroup φ

theorem isPerfect_U [Finite K] (hS : LocalSetting hω b L φ Bs) :
    Group.IsPerfect (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Nat.card K = (2 ^ 1) ^ 2 := by rw [hS.card_K]; norm_num
  haveI : Group.IsPerfect ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1)) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU (p := 2) (f := 1) hK
      (n := 6) (by norm_num) (by norm_num)
  exact Group.IsPerfect.ofSurjective
    (f := LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (QuotientGroup.mk'_surjective _)

theorem isPerfect_L [Finite K] (hS : LocalSetting hω b L φ Bs) : Group.IsPerfect L := by
  haveI : Group.IsPerfect (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) :=
    isPerfect_U hS
  exact Group.IsPerfect.ofSurjective
    (f := (φ.symm : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) →* L)) φ.symm.surjective

theorem center_L_eq_bot [Finite K] (hS : LocalSetting hω b L φ Bs) :
    Subgroup.center L = ⊥ := by
  haveI hsimple : IsSimpleGroup L := isSimpleGroup_L hS
  haveI hperf : Group.IsPerfect L := isPerfect_L hS
  haveI hnt : Nontrivial L := hsimple.toNontrivial
  rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center L) with h | h
  · exact h
  · exfalso
    have hcomm : IsMulCommutative L := Subgroup.center_eq_top_iff.mp h
    exact Group.IsPerfect.not_isMulCommutative L hcomm

theorem b_not_mem_L [Finite K] (hS : LocalSetting hω b L φ Bs) : b ∉ L := by
  intro hbL
  have hbcenter : (⟨b, hbL⟩ : L) ∈ Subgroup.center L := by
    rw [Subgroup.mem_center_iff]
    intro x
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (b_mem_centralizer_L hS) x.1 x.2)
  rw [center_L_eq_bot hS] at hbcenter
  rw [Subgroup.mem_bot] at hbcenter
  have hb1 : b = 1 := congrArg Subtype.val hbcenter
  have hord : orderOf b = 1 := by rw [hb1]; exact orderOf_one
  rw [hS.orderOf_b] at hord
  norm_num at hord

theorem card_zpowers_b (hS : LocalSetting hω b L φ Bs) :
    Nat.card (Subgroup.zpowers b) = 3 := by
  rw [Nat.card_zpowers, hS.orderOf_b]

theorem isPGroup_zpowers_b (hS : LocalSetting hω b L φ Bs) :
    IsPGroup 3 (Subgroup.zpowers b) := by
  refine IsPGroup.of_card (n := 1) ?_
  rw [card_zpowers_b hS, pow_one]

theorem card_Bbar [Finite K] (hS : LocalSetting hω b L φ Bs) :
    Nat.card ↥(Bs ⊓ L) = 3 ^ 4 := by
  have hmap := hS.map_inf
  calc Nat.card ↥(Bs ⊓ L)
      = Nat.card ↥((Bs ⊓ L).subgroupOf L) :=
        (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv).symm
    _ = Nat.card (((Bs ⊓ L).subgroupOf L).map φ.toMonoidHom) :=
        (Subgroup.card_map_of_injective φ.injective).symm
    _ = Nat.card (torU K) := by rw [hmap]
    _ = 3 ^ 4 := card_torU hS.card_K

theorem zpowers_b_inf_Bbar [Finite K] (hS : LocalSetting hω b L φ Bs) :
    Subgroup.zpowers b ⊓ (Bs ⊓ L) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxP, hxB⟩ := hx
  classical
  have hb3 : b ^ 3 = 1 := by
    have : orderOf b ∣ 3 := by rw [hS.orderOf_b]
    exact orderOf_dvd_iff_pow_eq_one.mp this
  have hfin : IsOfFinOrder b :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨3, by norm_num, hb3⟩
  change x ∈ Subgroup.zpowers b at hxP
  rw [hfin.mem_zpowers_iff_mem_range_orderOf, hS.orderOf_b] at hxP
  obtain ⟨i, hi3, rfl⟩ := Finset.mem_image.mp hxP
  rw [Finset.mem_range] at hi3
  rw [Subgroup.mem_bot]
  interval_cases i
  · simp
  · exfalso
    exact b_not_mem_L hS (by simpa using hxB.2)
  · exfalso
    apply b_not_mem_L hS
    have hb4 : b ^ 4 = b := by
      rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_add, hb3, one_mul, pow_one]
    have hb2 : b = (b ^ 2) ^ 2 := by
      rw [← pow_mul]
      norm_num
      exact hb4.symm
    rw [hb2]
    exact L.pow_mem hxB.2 2

noncomputable def inducedAut [Finite K] (hS : LocalSetting hω b L φ Bs) (g : G)
    (hg : g ∈ Subgroup.normalizer (L : Set G)) :
    MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) :=
  MulAut.congr φ (Subgroup.normalizerMonoidHom L ⟨g, hg⟩)

theorem inducedAut_apply [Finite K] (hS : LocalSetting hω b L φ Bs) {g : G}
    (hg : g ∈ Subgroup.normalizer (L : Set G)) {x : G} (hx : x ∈ L) :
    inducedAut hS g hg (φ ⟨x, hx⟩) =
      φ ⟨g * x * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg x).mp hx⟩ := by
  unfold inducedAut
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply]
  congr 1

theorem inducedAut_pow [Finite K] (hS : LocalSetting hω b L φ Bs) {g : G}
    (hg : g ∈ Subgroup.normalizer (L : Set G)) (k : ℕ) :
    inducedAut hS g hg ^ k = inducedAut hS (g ^ k)
      (Subgroup.pow_mem (Subgroup.normalizer (L : Set G)) hg k) := by
  unfold inducedAut
  rw [← map_pow, ← map_pow]
  apply congrArg (MulAut.congr φ)
  apply congrArg (Subgroup.normalizerMonoidHom L)
  exact Subtype.ext (by simp)

theorem inducedAut_of_mem_L [Finite K] (hS : LocalSetting hω b L φ Bs) {l : G} (hl : l ∈ L) :
    inducedAut hS l ((Subgroup.normal_subgroupOf_iff_le_normalizer hS.le_centralizer).mp
      hS.normal (hS.le_centralizer hl)) = MulAut.conj (φ ⟨l, hl⟩) := by
  ext u
  obtain ⟨x, rfl⟩ := φ.surjective u
  rw [inducedAut_apply, MulAut.conj_apply]
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1

theorem exists_mul_eq_of_mem_Bs [Finite G] [Finite K] (hS : LocalSetting hω b L φ Bs) {x : G}
    (hx : x ∈ Bs) :
    ∃ p ∈ Subgroup.zpowers b, ∃ y ∈ Bs ⊓ L, p * y = x := by
  classical
  set P := Subgroup.zpowers b with hP
  set Q := Bs ⊓ L with hQ
  have hPBs : P ≤ Bs := Subgroup.zpowers_le.mpr hS.mem
  have hQBs : Q ≤ Bs := inf_le_left
  have hdisj : P ⊓ Q = ⊥ := zpowers_b_inf_Bbar hS
  let toSup : ↥P × ↥Q → ↥Bs := fun z =>
    ⟨(z.1 : G) * (z.2 : G), Bs.mul_mem (hPBs z.1.2) (hQBs z.2.2)⟩
  have hinj : Function.Injective toSup := by
    rintro ⟨p1, y1⟩ ⟨p2, y2⟩ h
    have hprod : (p1 : G) * (y1 : G) = (p2 : G) * (y2 : G) := congrArg Subtype.val h
    have hmem : (p1 : G)⁻¹ * (p2 : G) ∈ P ⊓ Q := by
      constructor
      · exact P.mul_mem (P.inv_mem p1.2) p2.2
      · have heq : (p1 : G)⁻¹ * (p2 : G) = (y1 : G) * (y2 : G)⁻¹ := by
          have h' := congrArg (fun z : G => (p1 : G)⁻¹ * z * (y2 : G)⁻¹) hprod
          simpa [mul_assoc] using h'.symm
        rw [heq]
        exact Q.mul_mem y1.2 (Q.inv_mem y2.2)
    have hbot : (p1 : G)⁻¹ * (p2 : G) = 1 := by
      simpa [hdisj, Subgroup.mem_bot] using hmem
    have hp : p1 = p2 := by
      apply Subtype.ext
      have := congrArg (fun z : G => (p1 : G) * z) hbot
      simpa [mul_assoc] using this.symm
    have hy : y1 = y2 := by
      apply Subtype.ext
      have h' := hprod
      rw [hp] at h'
      exact mul_left_cancel h'
    exact Prod.ext hp hy
  haveI : Fintype ↥P := Fintype.ofFinite _
  haveI : Fintype ↥Q := Fintype.ofFinite _
  haveI : Fintype ↥Bs := Fintype.ofFinite _
  have hcard : Fintype.card (↥P × ↥Q) = Fintype.card ↥Bs := by
    rw [Fintype.card_prod, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      ← Nat.card_eq_fintype_card, card_zpowers_b hS, card_Bbar hS, hS.card]
    norm_num
  have hsurj : Function.Surjective toSup :=
    (Fintype.bijective_iff_injective_and_card toSup).mpr ⟨hinj, hcard⟩ |>.2
  obtain ⟨⟨p, y⟩, hpy⟩ := hsurj ⟨x, hx⟩
  exact ⟨p.1, p.2, y.1, y.2, congrArg Subtype.val hpy⟩

theorem inducedAut_apply_of_mem_torU [Finite K] (hS : LocalSetting hω b L φ Bs) {g : G}
    (hgN : g ∈ Subgroup.normalizer (L : Set G))
    (hgC : ∀ y ∈ Bs ⊓ L, g * y * g⁻¹ = y) :
    ∀ t ∈ torU K, inducedAut hS g hgN t = t := by
  intro t ht
  rw [← hS.map_inf] at ht
  obtain ⟨y, hy, rfl⟩ := ht
  unfold inducedAut
  simp only [MulEquiv.coe_toMonoidHom]
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply]
  exact congrArg φ (Subtype.ext (by
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    exact hgC y.1 hy))

theorem pow_three_mem_centralizer_b_inf [Finite G] [Finite K] (hS : LocalSetting hω b L φ Bs)
    {g : G} (hg : g ∈ Subgroup.centralizer (Bs : Set G)) :
    g ^ 3 ∈ Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer (L : Set G) := by
  have hgCb : g ∈ Subgroup.centralizer ({b} : Set G) := centralizer_Bs_le_centralizer_b hS hg
  have hgN : g ∈ Subgroup.normalizer (L : Set G) := centralizer_b_le_normalizer_L hS hgCb
  have hgC : ∀ y ∈ Bs ⊓ L, g * y * g⁻¹ = y := by
    intro y hy
    have hyc := Subgroup.mem_centralizer_iff.mp hg y hy.1
    rw [← hyc]
    group
  have hfix := inducedAut_apply_of_mem_torU hS hgN hgC
  have hα3 : inducedAut hS g hgN ^ 3 = 1 :=
    pow_three_eq_one_of_forall_fix_torU hS.card_K _ hfix
  have hαg3 : inducedAut hS (g ^ 3)
      (Subgroup.pow_mem (Subgroup.normalizer (L : Set G)) hgN 3) = 1 := by
    rw [← inducedAut_pow hS hgN 3, hα3]
  refine ⟨Subgroup.pow_mem _ hgCb 3, ?_⟩
  change g ^ 3 ∈ Subgroup.centralizer (L : Set G)
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have h := congrArg
    (fun α : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) =>
      α (φ ⟨x, hx⟩)) hαg3
  rw [inducedAut_apply] at h
  have h' : (⟨g ^ 3 * x * (g ^ 3)⁻¹,
      (Subgroup.mem_normalizer_iff.mp
        (Subgroup.pow_mem (Subgroup.normalizer (L : Set G)) hgN 3) x).mp hx⟩ : L) =
      ⟨x, hx⟩ := φ.injective (by simpa using h)
  have hval : g ^ 3 * x * (g ^ 3)⁻¹ = x := congrArg Subtype.val h'
  calc x * g ^ 3 = (g ^ 3 * x * (g ^ 3)⁻¹) * g ^ 3 := by rw [hval]
    _ = g ^ 3 * x := by group

theorem centralizer_b_inf_le_centralizer_Bs [Finite G] [Finite K] (hS : LocalSetting hω b L φ Bs) :
    Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer (L : Set G) ≤
      Subgroup.centralizer (Bs : Set G) := by
  intro g hg
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨p, hp, q, hq, rfl⟩ := exists_mul_eq_of_mem_Bs hS hy
  have hgP : g ∈ Subgroup.centralizer (Subgroup.zpowers b : Set G) := by
    rw [CFSG.centralizer_zpowers_eq_centralizer_singleton]
    exact hg.1
  have hgp : p * g = g * p := Subgroup.mem_centralizer_iff.mp hgP p hp
  have hgq : q * g = g * q := Subgroup.mem_centralizer_iff.mp hg.2 q hq.2
  symm
  calc g * (p * q) = (g * p) * q := by group
    _ = (p * g) * q := by rw [hgp]
    _ = p * (g * q) := by group
    _ = p * (q * g) := by rw [hgq]
    _ = (p * q) * g := by group

theorem conj_mem_centralizer_Bs [Finite K] (hS : LocalSetting hω b L φ Bs)
    {n g : G} (hn : n ∈ Subgroup.normalizer (Bs : Set G))
    (hg : g ∈ Subgroup.centralizer (Bs : Set G)) :
    n * g * n⁻¹ ∈ Subgroup.centralizer (Bs : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hn' : n⁻¹ ∈ Subgroup.normalizer (Bs : Set G) := Subgroup.inv_mem _ hn
  have hy' : n⁻¹ * y * n ∈ Bs := by
    simpa [inv_inv] using (Subgroup.mem_normalizer_iff.mp hn' y).mp hy
  have hcomm := Subgroup.mem_centralizer_iff.mp hg (n⁻¹ * y * n) hy'
  have := congrArg (fun z => n * z * n⁻¹) hcomm
  simpa [mul_assoc] using this

theorem relPPrimeCore_le_centralizer [Finite G] [Finite K] (hS : LocalSetting hω b L φ Bs) :
    relPPrimeCore 3 (Subgroup.centralizer {b}) ≤ Subgroup.centralizer (L : Set G) := by
  classical
  haveI hsimple : IsSimpleGroup L := isSimpleGroup_L hS
  obtain ⟨n, hnN, heL, hφe⟩ := hS.exists_conj
  set e : G := n * b * n⁻¹ with he
  have he3 : orderOf e = 3 := by
    have h := orderOf_injective (MulAut.conj n).toMonoidHom
      (MulAut.conj n).injective b
    simpa [he, MulAut.conj_apply, hS.orderOf_b] using h
  refine sSup_le ?_
  rintro N ⟨hNC, hNnorm, hNcop⟩
  have hNsub : (N.subgroupOf (Subgroup.centralizer ({b} : Set G))).Normal := hNnorm
  have hinfNormal : ((N ⊓ L).subgroupOf L).Normal := by
    rw [Subgroup.normal_subgroupOf_iff inf_le_right]
    intro x l hx hl
    constructor
    · have hxN : x ∈ N := hx.1
      have hlC : l ∈ Subgroup.centralizer ({b} : Set G) := hS.le_centralizer hl
      have hxN' : (⟨x, hNC hxN⟩ : Subgroup.centralizer ({b} : Set G)) ∈
          N.subgroupOf (Subgroup.centralizer ({b} : Set G)) := hxN
      have hconj := hNsub.conj_mem ⟨x, hNC hxN⟩ hxN' ⟨l, hlC⟩
      change l * x * l⁻¹ ∈ N
      exact hconj
    · exact L.mul_mem (L.mul_mem hl hx.2) (L.inv_mem hl)
  rcases Subgroup.Normal.eq_bot_or_eq_top ((N ⊓ L).subgroupOf L) with hbot | htop
  ·
    have hdisj : Disjoint (N ⊓ L) L := (Subgroup.subgroupOf_eq_bot.mp hbot)
    have hinfbot : N ⊓ L = ⊥ := by
      have h := hdisj.le_bot
      simpa [inf_assoc] using h
    have hdisj' : N.subgroupOf (Subgroup.centralizer ({b} : Set G)) ⊓
        L.subgroupOf (Subgroup.centralizer ({b} : Set G)) = ⊥ := by
      ext z
      constructor
      · rintro ⟨hzN, hzL⟩
        have hz : (z : G) ∈ N ⊓ L := ⟨hzN, hzL⟩
        have hz1 : (z : G) = 1 := by
          rw [hinfbot] at hz
          exact Subgroup.mem_bot.mp hz
        exact Subgroup.mem_bot.mpr (Subtype.ext hz1)
      · intro hz
        rw [Subgroup.mem_bot] at hz
        subst hz
        exact ⟨Subgroup.one_mem _, Subgroup.one_mem _⟩
    haveI hNsubI : (N.subgroupOf (Subgroup.centralizer ({b} : Set G))).Normal := hNnorm
    haveI hLsubI : (L.subgroupOf (Subgroup.centralizer ({b} : Set G))).Normal := hS.normal
    have hcomm : ⁅N.subgroupOf (Subgroup.centralizer ({b} : Set G)),
        L.subgroupOf (Subgroup.centralizer ({b} : Set G))⁆ ≤ ⊥ := by
      calc ⁅N.subgroupOf (Subgroup.centralizer ({b} : Set G)),
          L.subgroupOf (Subgroup.centralizer ({b} : Set G))⁆ ≤
          N.subgroupOf (Subgroup.centralizer ({b} : Set G)) ⊓
            L.subgroupOf (Subgroup.centralizer ({b} : Set G)) :=
        Subgroup.commutator_le_inf _ _
        _ = ⊥ := hdisj'
    have hcommbot : ⁅N.subgroupOf (Subgroup.centralizer ({b} : Set G)),
        L.subgroupOf (Subgroup.centralizer ({b} : Set G))⁆ = ⊥ := le_bot_iff.mp hcomm
    have hcent : N.subgroupOf (Subgroup.centralizer ({b} : Set G)) ≤
        Subgroup.centralizer
          (L.subgroupOf (Subgroup.centralizer ({b} : Set G)) : Set
            (Subgroup.centralizer ({b} : Set G))) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hcommbot
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hx' : (⟨x, hNC hx⟩ : Subgroup.centralizer ({b} : Set G)) ∈
        N.subgroupOf (Subgroup.centralizer ({b} : Set G)) := hx
    have hy' : (⟨y, hS.le_centralizer hy⟩ : Subgroup.centralizer ({b} : Set G)) ∈
        L.subgroupOf (Subgroup.centralizer ({b} : Set G)) := hy
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp (hcent hx')
      ⟨y, hS.le_centralizer hy⟩ hy')

  ·
    have hLNL : L ≤ N ⊓ L := (Subgroup.subgroupOf_eq_top.mp htop)
    have hLN : L ≤ N := hLNL.trans inf_le_left
    have heN : e ∈ N := hLN heL
    have h3N : 3 ∣ Nat.card N := by
      have := Subgroup.orderOf_dvd_natCard N heN
      rwa [he3] at this
    exact absurd h3N ((Nat.prime_three.coprime_iff_not_dvd).mp hNcop)

theorem le_zpowers_of_isPGroup [Finite G] [Finite K] (hS : LocalSetting hω b L φ Bs)
    {S : Subgroup G} (hS3 : IsPGroup 3 S)
    (hSR : S ≤ Subgroup.centralizer {b} ⊓ Subgroup.centralizer (L : Set G)) :
    S ≤ Subgroup.zpowers b := by
  classical
  obtain ⟨n, hnN, heL, hφe⟩ := hS.exists_conj
  set e : G := n * b * n⁻¹ with he
  have he3 : orderOf e = 3 := by
    have h := orderOf_injective (MulAut.conj n).toMonoidHom
      (MulAut.conj n).injective b
    simpa [he, MulAut.conj_apply, hS.orderOf_b] using h
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hle
  obtain ⟨x, hxS, hxP⟩ := Set.not_subset.mp hle
  set P := Subgroup.zpowers b with hP
  set T := S ⊔ P with hT
  have hPR : P ≤ Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer (L : Set G) :=
    Subgroup.zpowers_le.mpr ⟨b_mem_centralizer_b hS, b_mem_centralizer_L hS⟩
  have hTR : T ≤ Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer (L : Set G) :=
    sup_le hSR hPR
  have hTL : T ≤ Subgroup.centralizer (L : Set G) := hTR.trans inf_le_right
  have hSP : S ≤ Subgroup.normalizer (P : Set G) := by
    intro s hs
    have hbs : b * s = s * b :=
      Subgroup.mem_centralizer_iff.mp (hSR hs).1 b (by simp)
    have hsb : s * b * s⁻¹ = b := by
      rw [← hbs]
      group
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    simpa [P, CFSG.GroupTheory.map_conj_zpowers, hsb]
  have hT3 : IsPGroup 3 T :=
    IsPGroup.to_sup_of_normal_right' hS3 (isPGroup_zpowers_b hS) hSP
  have hTcyc : IsCyclic T := hS.isCyclic T hT3 hTL
  obtain ⟨m, hm⟩ := IsPGroup.exists_card_eq (p := 3) hT3
  have hcardP : Nat.card P = 3 := card_zpowers_b hS
  have hxT : x ∈ T := Subgroup.mem_sup_left hxS
  have hTne : T ≠ P := by
    intro h
    exact hxP (by simpa [h] using hxT)
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · rw [pow_zero] at hm
      have hdiv : Nat.card P ∣ Nat.card T := Subgroup.card_dvd_of_le le_sup_right
      rw [hm, hcardP] at hdiv
      norm_num at hdiv
    · exact h
  have hmne1 : m ≠ 1 := by
    intro hm1
    apply hTne
    symm
    refine Subgroup.eq_of_le_of_card_ge le_sup_right ?_
    rw [hm, hm1, hcardP]
    norm_num
  have hmge2 : 2 ≤ m := by omega
  obtain ⟨s, hsord⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := T)
  have hsgen : Subgroup.zpowers s = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, hsord]
  let s0 : G := n * (s : G) * n⁻¹
  have hs0ord : orderOf s0 = 3 ^ m := by
    have h1 : orderOf s0 = orderOf (s : G) := by
      rw [show s0 = (MulAut.conj n) (s : G) by rfl]
      exact orderOf_injective (MulAut.conj n).toMonoidHom
        (MulAut.conj n).injective (s : G)
    rw [h1, Subgroup.orderOf_coe, hsord, hm]
  have hsC : (s : G) ∈ Subgroup.centralizer (Bs : Set G) :=
    centralizer_b_inf_le_centralizer_Bs hS (hTR s.2)
  have hs0C : s0 ∈ Subgroup.centralizer (Bs : Set G) := by
    simpa [s0] using conj_mem_centralizer_Bs hS hnN hsC
  let bT : T := ⟨b, Subgroup.mem_sup_right (Subgroup.mem_zpowers b)⟩
  have hbT : bT ∈ Subgroup.zpowers s := by
    rw [hsgen]
    exact Subgroup.mem_top _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hbT
  have hkval : (s : G) ^ k = b := by
    have := congrArg Subtype.val hk
    simpa using this
  have he_s0k : e = s0 ^ k := by
    calc e = n * b * n⁻¹ := rfl
      _ = n * (s : G) ^ k * n⁻¹ := by rw [hkval]
      _ = s0 ^ k := by
        rw [show s0 = n * (s : G) * n⁻¹ from rfl, conj_zpow]
  have hs0pow : s0 ^ (3 ^ m : ℕ) = 1 := by
    rw [← hs0ord]
    exact pow_orderOf_eq_one s0
  let k' : ℤ := k % (3 ^ m : ℤ)
  have hk'_nonneg : 0 ≤ k' :=
    Int.emod_nonneg _ (by exact_mod_cast pow_ne_zero m (by norm_num : (3 : ℕ) ≠ 0))
  have hk'_eq : s0 ^ k = s0 ^ k' := by
    simpa [k'] using zpow_eq_zpow_emod' (x := s0) k hs0pow
  let k0 : ℕ := k'.toNat
  have hk0_cast : (k0 : ℤ) = k' := Int.toNat_of_nonneg hk'_nonneg
  have he_s0k0 : e = s0 ^ k0 := by
    rw [he_s0k, hk'_eq, ← hk0_cast, zpow_natCast]
  have hordk0 : orderOf (s0 ^ k0) = 3 := by
    rw [← he_s0k0, he3]
  have hgcd_eq : Nat.gcd (3 ^ m) k0 = 3 ^ (m - 1) := by
    have hq : 3 = 3 ^ m / Nat.gcd (3 ^ m) k0 := by
      rw [orderOf_pow, hs0ord] at hordk0
      exact hordk0.symm
    have hg_dvd : Nat.gcd (3 ^ m) k0 ∣ 3 ^ m := Nat.gcd_dvd_left _ _
    have hmul : 3 ^ m = 3 * Nat.gcd (3 ^ m) k0 := by
      calc 3 ^ m = (3 ^ m / Nat.gcd (3 ^ m) k0) * Nat.gcd (3 ^ m) k0 :=
          (Nat.div_mul_cancel hg_dvd).symm
        _ = 3 * Nat.gcd (3 ^ m) k0 := by rw [← hq]
    have hm1 : 3 ^ m = 3 ^ (m - 1) * 3 := by
      conv_lhs => rw [show m = (m - 1) + 1 by omega]
      rw [pow_succ]
    have h' : 3 * 3 ^ (m - 1) = 3 * Nat.gcd (3 ^ m) k0 := by
      rw [mul_comm 3 (3 ^ (m - 1))]
      exact hm1.symm.trans hmul
    exact (Nat.mul_left_cancel (by norm_num : 0 < 3) h').symm
  have hdvd : 3 ^ (m - 1) ∣ k0 := by
    rw [← hgcd_eq]
    exact Nat.gcd_dvd_right _ _
  obtain ⟨t, ht⟩ := hdvd
  have h3m1 : 3 ^ (m - 1) = 3 * 3 ^ (m - 2) := by
    rw [show m - 1 = (m - 2) + 1 by omega, pow_succ]
    ring
  have hk0_eq : k0 = 3 * (3 ^ (m - 2) * t) := by
    rw [ht, h3m1]
    ring
  have he_pow : e ∈ Subgroup.zpowers (s0 ^ 3) := by
    rw [he_s0k0, hk0_eq, pow_mul]
    exact Subgroup.npow_mem_zpowers (s0 ^ 3) (3 ^ (m - 2) * t)
  have hs03R : s0 ^ 3 ∈
      Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer (L : Set G) :=
    pow_three_mem_centralizer_b_inf hS hs0C
  have heR : e ∈ Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer (L : Set G) :=
    (Subgroup.zpowers_le.mpr hs03R) he_pow
  have heCL : e ∈ Subgroup.centralizer (L : Set G) := heR.2
  have heZ : (⟨e, heL⟩ : L) ∈ Subgroup.center L := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp heCL y.1 y.2
  rw [center_L_eq_bot hS] at heZ
  have he1 : e = 1 := by
    have := Subgroup.mem_bot.mp heZ
    exact congrArg Subtype.val this
  have hord1 : orderOf e = 1 := by rw [he1]; simp
  rw [he3] at hord1
  norm_num at hord1

theorem centralizer_inf_eq [Finite G] [Finite K] (hS : LocalSetting hω b L φ Bs) :
    Subgroup.centralizer {b} ⊓ Subgroup.centralizer (L : Set G) =
      relPPrimeCore 3 (Subgroup.centralizer {b}) ⊔ Subgroup.zpowers b := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Cb : Subgroup G := Subgroup.centralizer ({b} : Set G) with hCb
  set CL : Subgroup G := Subgroup.centralizer (L : Set G) with hCL
  set R : Subgroup G := Cb ⊓ CL with hR
  set P : Subgroup G := Subgroup.zpowers b with hP
  set O : Subgroup G := relPPrimeCore 3 Cb with hO
  have hPleR : P ≤ R := by
    rw [hR, hP]
    exact Subgroup.zpowers_le.mpr ⟨b_mem_centralizer_b hS, b_mem_centralizer_L hS⟩
  have hOleCb : O ≤ Cb := by rw [hO]; exact relPPrimeCore_le Cb
  have hOleCL : O ≤ CL := by
    rw [hCL, hO]
    exact relPPrimeCore_le_centralizer hS
  have hOleR : O ≤ R := le_inf hOleCb hOleCL
  have hOnormal : (O.subgroupOf Cb).Normal := by
    rw [hO]
    exact relPPrimeCore_normal Nat.prime_three Cb
  have hOcop : Nat.Coprime 3 (Nat.card O) := by
    rw [hO]
    exact coprime_card_relPPrimeCore Nat.prime_three Cb
  have hP3 : IsPGroup 3 P := by rw [hP]; exact isPGroup_zpowers_b hS
  have hPcard : Nat.card P = 3 := by rw [hP]; exact card_zpowers_b hS
  have hRnormalCb : (R.subgroupOf Cb).Normal := by
    rw [Subgroup.normal_subgroupOf_iff (by rw [hR]; exact inf_le_left)]
    intro x y hx hy
    have hx' : x ∈ Cb ⊓ CL := hx
    have hxCl : x ∈ CL := hx'.2
    have hxCb : x ∈ Cb := hx'.1
    refine ⟨Cb.mul_mem (Cb.mul_mem hy hxCb) (Cb.inv_mem hy), ?_⟩
    have hxCl' : x ∈ CL := hxCl
    rw [hCL, Subgroup.mem_centralizer_iff] at hxCl'
    change y * x * y⁻¹ ∈ CL
    rw [hCL, Subgroup.mem_centralizer_iff]
    intro l hl
    have hyN : y ∈ Subgroup.normalizer (L : Set G) :=
      centralizer_b_le_normalizer_L hS hy
    have hyl : y⁻¹ * l * y ∈ L := by
      simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hyN) l).mp hl
    have hcomm := hxCl' (y⁻¹ * l * y) hyl
    calc l * (y * x * y⁻¹) = y * ((y⁻¹ * l * y) * x) * y⁻¹ := by group
      _ = y * (x * (y⁻¹ * l * y)) * y⁻¹ := by rw [hcomm]
      _ = y * x * y⁻¹ * l := by group
  let Psub : Subgroup ↥R := P.subgroupOf R
  have hPsub3 : IsPGroup 3 Psub :=
    hP3.comap_of_injective R.subtype R.subtype_injective
  have hunique : ∀ S : Subgroup ↥R, IsPGroup 3 S → S ≤ Psub := by
    intro S hS3 s hs
    have hSmap3 : IsPGroup 3 (S.map R.subtype) := hS3.map R.subtype
    have hSmapR : S.map R.subtype ≤ R := by
      rintro - ⟨y, -, rfl⟩
      exact y.2
    have hsmap : (s : G) ∈ S.map R.subtype := Subgroup.mem_map_of_mem _ hs
    have hmem := le_zpowers_of_isPGroup hS hSmap3 hSmapR hsmap
    rw [Subgroup.mem_subgroupOf]
    simpa [hP] using hmem
  obtain ⟨S, hPsubleS⟩ := hPsub3.exists_le_sylow
  have hSlePsub : (S : Subgroup ↥R) ≤ Psub := hunique S S.isPGroup'
  have hSP : (S : Subgroup ↥R) = Psub := le_antisymm hSlePsub hPsubleS
  have hnotdvd : ¬ 3 ∣ Psub.index := by
    have h := S.not_dvd_index
    rwa [hSP] at h
  let PSyl : Sylow 3 ↥R := hPsub3.toSylow hnotdvd
  have hPsubCenter : (PSyl : Subgroup ↥R) ≤ Subgroup.center ↥R := by
    intro p hp
    rw [Subgroup.mem_center_iff]
    intro x
    apply Subtype.ext
    have hpP : (p : G) ∈ P := by
      have hp' : p ∈ Psub := hp
      rw [Subgroup.mem_subgroupOf] at hp'
      exact hp'
    have hxCb : (x : G) ∈ Cb := by rw [hCb]; exact x.2.1
    have hxP : (x : G) ∈ Subgroup.centralizer (P : Set G) := by
      rw [hP, CFSG.centralizer_zpowers_eq_centralizer_singleton]
      exact hxCb
    exact (Subgroup.mem_centralizer_iff.mp hxP (p : G) hpP).symm
  have hcomp := CFSG.Wreathed.BrauerWong.pPrimeCore_isComplement'_of_le_center PSyl hPsubCenter
  set K : Subgroup ↥R := CFSG.pPrimeCore 3 ↥R with hK
  have hRleCb : R ≤ Cb := by rw [hR]; exact inf_le_left
  have hOnormalR : (O.subgroupOf R).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hOleR]
    intro h k hh hk
    exact (Subgroup.normal_subgroupOf_iff hOleCb).mp hOnormal h k hh (hRleCb hk)
  have hOsubcop : Nat.Coprime 3 (Nat.card (O.subgroupOf R)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOleR).toEquiv]
    exact hOcop
  have hOsub_le_K : O.subgroupOf R ≤ K := by
    rw [hK]
    exact le_sSup ⟨hOnormalR, hOsubcop⟩
  have hKchar : K.Characteristic := by
    rw [hK]
    exact pPrimeCore_characteristic (p := 3) (G := ↥R)
  have hKmap_le_R : K.map R.subtype ≤ R := by
    rintro - ⟨k, -, rfl⟩
    exact k.2
  have hKmap_le_Cb : K.map R.subtype ≤ Cb := hKmap_le_R.trans inf_le_left
  have hKmap_cop : Nat.Coprime 3 (Nat.card (K.map R.subtype)) := by
    rw [Subgroup.card_map_of_injective R.subtype_injective]
    rw [hK]
    exact pPrimeCore_coprime_card (p := 3) (G := ↥R)
  have hKforward : ∀ c ∈ Cb, ∀ x ∈ (K.map R.subtype : Set G),
      c * x * c⁻¹ ∈ K.map R.subtype := by
    intro c hc x hx
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hx
    let eR : (R.subgroupOf Cb) ≃* R := Subgroup.subgroupOfEquivOfLe inf_le_left
    let φc : MulAut (R.subgroupOf Cb) := MulAut.conjNormal (H := R.subgroupOf Cb) ⟨c, hc⟩
    let ψ : MulAut R := eR.symm.trans (φc.trans eR)
    have hψk : (ψ k : G) = c * (k : G) * c⁻¹ := by
      change ((φc (eR.symm k) : ↥(R.subgroupOf Cb)) : G) = c * (k : G) * c⁻¹
      have h2 : ((φc (eR.symm k) : ↥(R.subgroupOf Cb)) : G) =
          c * ((eR.symm k : ↥(R.subgroupOf Cb)) : G) * c⁻¹ := by
        have h2' : (↑(φc (eR.symm k)) : ↥Cb) =
            (⟨c, hc⟩ : ↥Cb) * (↑(eR.symm k) : ↥Cb) * (⟨c, hc⟩ : ↥Cb)⁻¹ :=
          MulAut.conjNormal_apply (H := R.subgroupOf Cb) ⟨c, hc⟩ (eR.symm k)
        exact congrArg (fun z : ↥Cb => (z : G)) h2'
      rw [h2]
      rfl
    have hk' : ψ k ∈ K := by
      have hmap := (Subgroup.characteristic_iff_map_eq.mp hKchar ψ)
      rw [← hmap]
      exact Subgroup.mem_map_of_mem ψ.toMonoidHom hk
    exact Subgroup.mem_map.mpr ⟨ψ k, hk', hψk⟩
  have hKmap_normal : ((K.map R.subtype).subgroupOf Cb).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hKmap_le_Cb]
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact hKforward c hc x
    · intro hx
      have h := hKforward c⁻¹ (Cb.inv_mem hc) (c * x * c⁻¹) hx
      have hxeq : c⁻¹ * (c * x * c⁻¹) * c⁻¹⁻¹ = x := by group
      rwa [hxeq] at h
  have hKmap_le_O : K.map R.subtype ≤ O := by
    rw [hO]
    exact le_sSup ⟨hKmap_le_Cb, hKmap_normal, hKmap_cop⟩
  have hK_le_Osub : K ≤ O.subgroupOf R := by
    intro k hk
    exact hKmap_le_O (Subgroup.mem_map_of_mem R.subtype hk)
  have hK_eq : K = O.subgroupOf R := le_antisymm hK_le_Osub hOsub_le_K
  have hKmap_eq_O : K.map R.subtype = O := by
    calc K.map R.subtype = (O.subgroupOf R).map R.subtype := by rw [hK_eq]
      _ = O := Subgroup.map_subgroupOf_eq_of_le hOleR
  have hPsub_map : Psub.map R.subtype = P :=
    Subgroup.map_subgroupOf_eq_of_le hPleR
  have htop : (⊤ : Subgroup ↥R).map R.subtype = R := by
    rw [Subgroup.map_top]
    exact Subgroup.range_subtype R
  calc Cb ⊓ CL = R := rfl
    _ = (⊤ : Subgroup ↥R).map R.subtype := htop.symm
    _ = (K ⊔ (PSyl : Subgroup ↥R)).map R.subtype := by rw [hcomp.sup_eq_top]
    _ = O ⊔ P := by
      have hPSyl_map : (PSyl : Subgroup ↥R).map R.subtype = P := by
        rw [show (PSyl : Subgroup ↥R) = Psub from rfl, hPsub_map]
      rw [Subgroup.map_sup, hKmap_eq_O, hPSyl_map]

theorem conj (hS : LocalSetting hω b L φ Bs) {n : G} (hn : n ∈ Subgroup.normalizer (Bs : Set G))
    (hnL : n * b * n⁻¹ ∈ L) (hnφ : φ ⟨n * b * n⁻¹, hnL⟩ = threeA hω) :
    LocalSetting hω (n * b * n⁻¹) (L.map (MulAut.conj n : G →* G)) (conjEquiv φ n) Bs := by
  classical
  have hconj : ∀ x : G, (MulAut.conj n : G →* G) x = n * x * n⁻¹ := fun x => rfl
  have hminj : Function.Injective (MulAut.conj n : G →* G) := (MulAut.conj n).injective
  have hnmap : Bs.map (MulAut.conj n : G →* G) = Bs :=
    (Subgroup.mem_normalizer_iff_map_conj_eq).mp hn
  refine
    { card_K := hS.card_K
      orderOf_b := ?_
      le_centralizer := ?_
      normal := ?_
      isCyclic := ?_
      elemAbelian := hS.elemAbelian
      mem := ?_
      card := hS.card
      map_inf := ?_
      exists_conj := ?_ }
  ·
    have h : orderOf (n * b * n⁻¹) = orderOf b := by
      rw [show n * b * n⁻¹ = (MulAut.conj n) b from rfl]
      exact orderOf_injective (MulAut.conj n).toMonoidHom (MulAut.conj n).injective b
    rw [h, hS.orderOf_b]
  ·
    rintro _ ⟨l, hl, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hlb : l * b = b * l := Subgroup.mem_centralizer_singleton_iff.mp (hS.le_centralizer hl)
    calc n * l * n⁻¹ * (n * b * n⁻¹)
        = n * (l * b) * n⁻¹ := by group
      _ = n * (b * l) * n⁻¹ := by rw [hlb]
      _ = (n * b * n⁻¹) * (n * l * n⁻¹) := by group
  ·
    have hle : L.map (MulAut.conj n : G →* G) ≤ Subgroup.centralizer ({n * b * n⁻¹} : Set G) := by
      rintro _ ⟨l, hl, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hlb : l * b = b * l := Subgroup.mem_centralizer_singleton_iff.mp (hS.le_centralizer hl)
      calc n * l * n⁻¹ * (n * b * n⁻¹)
          = n * (l * b) * n⁻¹ := by group
        _ = n * (b * l) * n⁻¹ := by rw [hlb]
        _ = (n * b * n⁻¹) * (n * l * n⁻¹) := by group
    rw [Subgroup.normal_subgroupOf_iff (H := L.map (MulAut.conj n : G →* G))
      (K := Subgroup.centralizer ({n * b * n⁻¹} : Set G)) hle]
    intro x y hx hy
    obtain ⟨l, hl, rfl⟩ := hx
    have hyC : y * (n * b * n⁻¹) = (n * b * n⁻¹) * y :=
      Subgroup.mem_centralizer_singleton_iff.mp hy
    set c : G := n⁻¹ * y * n with hcdef
    have hcC : c * b = b * c := by
      have h2 : n⁻¹ * (y * (n * b * n⁻¹)) * n = n⁻¹ * ((n * b * n⁻¹) * y) * n := by
        rw [hyC]
      calc c * b = n⁻¹ * (y * (n * b * n⁻¹)) * n := by rw [hcdef]; group
        _ = n⁻¹ * ((n * b * n⁻¹) * y) * n := h2
        _ = b * c := by rw [hcdef]; group
    have hcCl : c ∈ Subgroup.centralizer ({b} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hcC
    have hconc : c * l * c⁻¹ ∈ L :=
      (Subgroup.normal_subgroupOf_iff hS.le_centralizer).mp hS.normal l c hl hcCl
    refine ⟨c * l * c⁻¹, hconc, ?_⟩
    show (MulAut.conj n : G →* G) (c * l * c⁻¹) = y * (n * l * n⁻¹) * y⁻¹
    rw [hcdef]
    rw [hconj]
    group
  ·
    intro S hS3 hSC
    let S' : Subgroup G := S.map (MulAut.conj (n⁻¹) : G →* G)
    have hS'3 : IsPGroup 3 S' := hS3.map (MulAut.conj (n⁻¹) : G →* G)
    have hS'CL : S' ≤ Subgroup.centralizer (L : Set G) := by
      intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      obtain ⟨s, hs, rfl⟩ := hz
      have hsC : s ∈ Subgroup.centralizer ((L.map (MulAut.conj n : G →* G) : Subgroup G) : Set G) :=
        hSC hs
      have hcomm : (n * l * n⁻¹) * s = s * (n * l * n⁻¹) :=
        Subgroup.mem_centralizer_iff.mp hsC (n * l * n⁻¹) (Subgroup.mem_map_of_mem _ hl)
      have hconjinv : (↑(MulAut.conj (n⁻¹)) : G →* G) s = n⁻¹ * s * n := by
        change (MulAut.conj (n⁻¹)) s = n⁻¹ * s * n
        rw [MulAut.conj_apply, inv_inv]
      rw [hconjinv]
      calc l * (n⁻¹ * s * n)
          = n⁻¹ * ((n * l * n⁻¹) * s) * n := by group
        _ = n⁻¹ * (s * (n * l * n⁻¹)) * n := by rw [hcomm]
        _ = (n⁻¹ * s * n) * l := by group
    have hcyc' : IsCyclic S' := hS.isCyclic S' hS'3 hS'CL
    exact (MulEquiv.isCyclic ((MulAut.conj (n⁻¹)).subgroupMap S)).mpr hcyc'
  ·
    exact (Subgroup.mem_normalizer_iff.mp hn b).mp hS.mem
  ·
    let M : Subgroup G := L.map (MulAut.conj n : G →* G)
    change ((Bs ⊓ M).subgroupOf M).map (conjEquiv φ n).toMonoidHom = torU K
    apply le_antisymm
    · intro t ht
      obtain ⟨z, hz, rfl⟩ := ht
      have hz' : (z : G) ∈ Bs ⊓ M := hz
      obtain ⟨x, hxL, hxz⟩ := Subgroup.mem_map.mp hz'.2
      have hzB : n * x * n⁻¹ ∈ Bs := by rw [← hconj x, hxz]; exact hz'.1
      have hxBs : x ∈ Bs := (Subgroup.mem_normalizer_iff.mp hn x).mpr hzB
      have hzM_eq : (z : M) = ⟨n * x * n⁻¹, Subgroup.mem_map.mpr ⟨x, hxL, rfl⟩⟩ :=
        Subtype.ext hxz.symm
      have ht_eq : conjEquiv φ n z = φ ⟨x, hxL⟩ := by
        rw [hzM_eq]
        exact conjEquiv_apply φ n hxL _
      change (conjEquiv φ n) z ∈ torU K
      rw [ht_eq]
      rw [← hS.map_inf]
      exact Subgroup.mem_map.mpr ⟨⟨x, hxL⟩, ⟨hxBs, hxL⟩, rfl⟩
    · intro t ht
      rw [← hS.map_inf] at ht
      obtain ⟨y, hy, rfl⟩ := ht
      have hyBs : (y : G) ∈ Bs := hy.1
      have hM : n * (y : G) * n⁻¹ ∈ M :=
        Subgroup.mem_map.mpr ⟨(y : G), y.2, rfl⟩
      have hBs : n * (y : G) * n⁻¹ ∈ Bs :=
        (Subgroup.mem_normalizer_iff.mp hn (y : G)).mp hyBs
      refine Subgroup.mem_map.mpr
        ⟨⟨n * (y : G) * n⁻¹, hM⟩, ⟨hBs, hM⟩, ?_⟩
      exact conjEquiv_apply φ n y.2 hM
  ·
    refine ⟨n, hn, Subgroup.mem_map.mpr ⟨n * b * n⁻¹, hnL, by rw [hconj]⟩, ?_⟩
    have hc := conjEquiv_apply φ n (x := n * b * n⁻¹) hnL
      (Subgroup.mem_map.mpr ⟨n * b * n⁻¹, hnL, by rw [hconj]⟩)
    simpa [hnφ] using hc

end LocalSetting

end CFSG.StandardType.USixTwo

end
