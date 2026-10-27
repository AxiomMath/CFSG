module

import CFSG.RankThree.PartTwo.Sec21.Item2119End3Proof2125Unique
import CFSG.RankThree.PartOne.S9.Sylow.ResidualLocal
import CFSG.RankThree.PartTwo.Sec11.FixedCentralizer
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.RankThree.GroupTheory.SteinbergCEFixedResidual
public import CFSG.RankThree.PartTwo.Sec21.Item211Res3ProofChoice
public import CFSG.RankThree.PartTwo.Sec21.Item21Late2Proof2120

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSL)

namespace Item2119End4Proof

variable {G : Type} [Group G] [Finite G]

theorem mem_thetaQuotCentralizer_of_le' {Y I : Subgroup G} (hIY : I ≤ Y) {x : G}
    (hx : x ∈ Sec4.thetaQuotCentralizer Y) (hxI : x ∈ Subgroup.normalizer (I : Set G)) :
    x ∈ Sec4.thetaQuotCentralizer I := by
  rw [Sec6.mem_thetaQuotCentralizer_iff] at hx ⊢
  refine ⟨hxI, fun i hi => ?_⟩
  have h1 := hx.2 i (hIY hi)
  have h2 : i⁻¹ * (x * i * x⁻¹) ∈ I :=
    I.mul_mem (I.inv_mem hi) ((Subgroup.mem_normalizer_iff.mp hxI i).mp hi)
  exact PartOne.Sec9A.inf_inSubgroup_theta_le Nat.prime_three hIY ⟨h2, h1⟩

theorem eq_of_mem_thetaComponentsAt_of_mem {e : G} {Y Y' J : Subgroup G}
    (hY : Y ∈ thetaComponentsAt 3 e) (hY' : Y' ∈ thetaComponentsAt 3 e) (hJY' : J ≤ Y')
    (hZJ : Subgroup.center (lBar J) = ⊥) {d : G} (hdJ : d ∈ J) (hdY : d ∈ Y) (hd3 : d ^ 3 = 1)
    (hd1 : d ≠ 1) : Y = Y' := by
  by_contra hne
  have h1 : Y ≤ Sec4.thetaQuotCentralizer Y' :=
    Item2119End3Proof.le_thetaQuotCentralizer_of_ne hY' hY (Ne.symm hne)
  have h2 : d ∈ Sec4.thetaQuotCentralizer J :=
    mem_thetaQuotCentralizer_of_le' hJY' (h1 hdY) (Subgroup.le_normalizer hdJ)
  exact hd1 (Item2119End3Proof.eq_one_of_mem_thetaQuotCentralizer hZJ hdJ h2 hd3)

theorem mem_sup_of_mem_thetaQuotCentralizer {A I : Subgroup G}
    (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (h3 : ∀ x ∈ A, x ^ 3 = 1)
    (h27 : Nat.card A = 27) {u v d : G} (huA : u ∈ A) (hvA : v ∈ A) (hdA : d ∈ A)
    (hdI : d ∈ I) (hZ : Subgroup.center (lBar I) = ⊥)
    (huI : I ≤ Subgroup.centralizer ({u} : Set G)) (hvI : I ≤ Subgroup.centralizer ({v} : Set G))
    (h9 : Nat.card (Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup G) = 9)
    (hd : d ∉ Subgroup.zpowers u ⊔ Subgroup.zpowers v) {x : G} (hxA : x ∈ A)
    (hx : x ∈ Sec4.thetaQuotCentralizer I) : x ∈ Subgroup.zpowers u ⊔ Subgroup.zpowers v := by
  obtain ⟨m, j, i, rfl⟩ :=
    Item2119EndProof.exists_basis_repr hcomm h3 h27 hdA huA hvA h9 hd x hxA
  have huC : u ∈ Sec4.thetaQuotCentralizer I :=
    Item211Res3Proof.mem_thetaQuotCentralizer_of_le_centralizer huI
  have hvC : v ∈ Sec4.thetaQuotCentralizer I :=
    Item211Res3Proof.mem_thetaQuotCentralizer_of_le_centralizer hvI
  have hwC : u ^ j * v ^ i ∈ Sec4.thetaQuotCentralizer I :=
    Subgroup.mul_mem _ (Subgroup.pow_mem _ huC j) (Subgroup.pow_mem _ hvC i)
  have hdm : d ^ m ∈ Sec4.thetaQuotCentralizer I := by
    have h := Subgroup.mul_mem _ hx (Subgroup.inv_mem _ hwC)
    rwa [mul_inv_cancel_right] at h
  have hdm3 : (d ^ m) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, h3 d hdA, one_pow]
  have hdm1 := Item2119End3Proof.eq_one_of_mem_thetaQuotCentralizer hZ (I.pow_mem hdI m) hdm hdm3
  rw [hdm1, one_mul]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.pow_mem _ (Subgroup.mem_zpowers u) j))
    (Subgroup.mem_sup_right (Subgroup.pow_mem _ (Subgroup.mem_zpowers v) i))

theorem inf_eq_zpowers_of_center_eq_bot {A I : Subgroup G}
    (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (h3 : ∀ x ∈ A, x ^ 3 = 1)
    (h27 : Nat.card A = 27) {u v d : G} (huA : u ∈ A) (hvA : v ∈ A) (hdA : d ∈ A)
    (hdI : d ∈ I) (hZ : Subgroup.center (lBar I) = ⊥)
    (huI : I ≤ Subgroup.centralizer ({u} : Set G)) (hvI : I ≤ Subgroup.centralizer ({v} : Set G))
    (h9 : Nat.card (Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup G) = 9)
    (hd : d ∉ Subgroup.zpowers u ⊔ Subgroup.zpowers v) : A ⊓ I = Subgroup.zpowers d := by
  apply le_antisymm
  · rintro x ⟨hxA, hxI⟩
    obtain ⟨m, j, i, rfl⟩ :=
      Item2119EndProof.exists_basis_repr hcomm h3 h27 hdA huA hvA h9 hd x hxA
    have huC : u ∈ Sec4.thetaQuotCentralizer I :=
      Item211Res3Proof.mem_thetaQuotCentralizer_of_le_centralizer huI
    have hvC : v ∈ Sec4.thetaQuotCentralizer I :=
      Item211Res3Proof.mem_thetaQuotCentralizer_of_le_centralizer hvI
    have hwC : u ^ j * v ^ i ∈ Sec4.thetaQuotCentralizer I :=
      Subgroup.mul_mem _ (Subgroup.pow_mem _ huC j) (Subgroup.pow_mem _ hvC i)
    have hwI : u ^ j * v ^ i ∈ I := by
      have h := I.mul_mem (I.inv_mem (I.pow_mem hdI m)) hxI
      rwa [inv_mul_cancel_left] at h
    have hwA : u ^ j * v ^ i ∈ A := A.mul_mem (A.pow_mem huA j) (A.pow_mem hvA i)
    have hw1 := Item2119End3Proof.eq_one_of_mem_thetaQuotCentralizer hZ hwI hwC (h3 _ hwA)
    rw [hw1, mul_one]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers d) m
  · rw [Subgroup.zpowers_le]
    exact ⟨hdA, hdI⟩

theorem mem_zpowers_of_mem_sup_of_mem_sup {u v e : G} (hue : u * e = e * u) (hve : v * e = e * v)
    (hu3 : u ^ 3 = 1) (hv3 : v ^ 3 = 1) (he3 : e ^ 3 = 1) (he1 : e ≠ 1)
    (hu : u ∉ Subgroup.zpowers e) (hv : v ∉ Subgroup.zpowers e)
    (hvu : v ∉ Subgroup.zpowers u ⊔ Subgroup.zpowers e) {x : G}
    (hx1 : x ∈ Subgroup.zpowers u ⊔ Subgroup.zpowers e)
    (hx2 : x ∈ Subgroup.zpowers v ⊔ Subgroup.zpowers e) : x ∈ Subgroup.zpowers e := by
  by_contra hxe
  have hx3 : x ^ 3 = 1 := by
    obtain ⟨i, -, j, -, rfl⟩ := Item21Late2Proof.exists_pow_mul_pow_of_mem_sup hue hu3 he3 hx1
    rw [(Commute.pow_pow (show Commute u e from hue) i j).mul_pow, ← pow_mul, ← pow_mul,
      mul_comm i, mul_comm j, pow_mul, pow_mul, hu3, he3, one_pow, one_pow, one_mul]
  have hxe' : x * e = e * x := by
    obtain ⟨i, -, j, -, rfl⟩ := Item21Late2Proof.exists_pow_mul_pow_of_mem_sup hue hu3 he3 hx1
    have h1 : Commute (u ^ i) e := (Commute.pow_left (show Commute u e from hue) i)
    have h2 : Commute (e ^ j) e := Commute.pow_left (Commute.refl e) j
    exact (h1.mul_left h2).eq
  have h9x : Nat.card (Subgroup.zpowers e ⊔ Subgroup.zpowers x : Subgroup G) = 9 :=
    Item21LateProof.card_zpowers_sup_zpowers hxe'.symm he3 hx3 he1 hxe
  have h9u : Nat.card (Subgroup.zpowers e ⊔ Subgroup.zpowers u : Subgroup G) = 9 :=
    Item21LateProof.card_zpowers_sup_zpowers hue.symm he3 hu3 he1 hu
  have h9v : Nat.card (Subgroup.zpowers e ⊔ Subgroup.zpowers v : Subgroup G) = 9 :=
    Item21LateProof.card_zpowers_sup_zpowers hve.symm he3 hv3 he1 hv
  have hle1 : Subgroup.zpowers e ⊔ Subgroup.zpowers x ≤ Subgroup.zpowers e ⊔ Subgroup.zpowers u :=
    sup_le le_sup_left (by rw [Subgroup.zpowers_le, sup_comm]; exact hx1)
  have hle2 : Subgroup.zpowers e ⊔ Subgroup.zpowers x ≤ Subgroup.zpowers e ⊔ Subgroup.zpowers v :=
    sup_le le_sup_left (by rw [Subgroup.zpowers_le, sup_comm]; exact hx2)
  have heq1 := Subgroup.eq_of_le_of_card_ge hle1 (by rw [h9x, h9u])
  have heq2 := Subgroup.eq_of_le_of_card_ge hle2 (by rw [h9x, h9v])
  apply hvu
  have hv' : v ∈ Subgroup.zpowers e ⊔ Subgroup.zpowers v :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers v)
  rw [← heq2, heq1, sup_comm] at hv'
  exact hv'

theorem card_lBar_dvd_card_lBar {I Y : Subgroup G} (hIY : I ≤ Y) :
    Nat.card (lBar I) ∣ Nat.card (lBar Y) := by
  set ρ : I →* lBar Y := (QuotientGroup.mk' (aschbacherSolvableCore 3 Y)).comp
    (Subgroup.inclusion hIY) with hρ
  have hker : ρ.ker ≤ aschbacherSolvableCore 3 I := by
    intro i hi
    rw [MonoidHom.mem_ker, hρ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hi
    have h1 : (i : G) ∈ I ⊓ inSubgroup (aschbacherSolvableCore 3) Y :=
      ⟨i.2, ⟨_, hi, rfl⟩⟩
    obtain ⟨j, hj, hji⟩ := PartOne.Sec9A.inf_inSubgroup_theta_le Nat.prime_three hIY h1
    have : j = i := Subtype.ext hji
    rwa [← this]
  have hdvd : Nat.card ρ.ker ∣ Nat.card (aschbacherSolvableCore 3 I) := by
    have h := Subgroup.card_dvd_of_le hker
    exact h
  have e1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (aschbacherSolvableCore 3 I)
  have e2 := Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker
  have e3 : Nat.card (I ⧸ ρ.ker) = Nat.card ρ.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv
  obtain ⟨k, hk⟩ := hdvd
  have hpos : 0 < Nat.card ρ.ker := Nat.card_pos
  have h1 : Nat.card (lBar I) * k = Nat.card ρ.range := by
    have h2 : Nat.card (lBar I) * (Nat.card ρ.ker * k) = Nat.card ρ.range * Nat.card ρ.ker := by
      rw [← hk, ← e3]
      change Nat.card (I ⧸ aschbacherSolvableCore 3 I) * _ = _
      rw [← e1, ← e2]
    have h3 : (Nat.card (lBar I) * k) * Nat.card ρ.ker = Nat.card ρ.range * Nat.card ρ.ker := by
      rw [← h2]
      ring
    exact Nat.eq_of_mul_eq_mul_right hpos h3
  exact Dvd.intro k h1 |>.trans (Subgroup.card_subgroup_dvd_card ρ.range)

theorem mem_thetaComponentsIn_sec11K' {L Y : Subgroup G} {c e : G}
    (hLc : L ∈ thetaComponentsAt 3 c) (hKY : Sec11.sec11K L e ≤ Y)
    (hq : IsQuasisimple (lBar (Sec11.sec11K L e)))
    (hcC : c ∈ Subgroup.centralizer ({e} : Set G)) :
    (Sec11.sec11K L e).subgroupOf (Subgroup.centralizer ({e} : Set G)) ∈
      thetaComponentsIn (Y.subgroupOf (Subgroup.centralizer ({e} : Set G)) ⊓
        Subgroup.centralizer
          ({(⟨c, hcC⟩ : Subgroup.centralizer ({e} : Set G))} : Set _)) := by
  set C := Subgroup.centralizer ({e} : Set G) with hC
  set c' : C := ⟨c, hcC⟩ with hc'
  set K := Sec11.sec11K L e with hK
  obtain ⟨hLc', hL'⟩ := mem_thetaComponentsIn_iff.mp hLc
  have hKC : K ≤ C := (Subgroup.map_subtype_le _).trans inf_le_right
  have hKc : K ≤ Subgroup.centralizer ({c} : Set G) :=
    ((Subgroup.map_subtype_le _).trans inf_le_left).trans hLc'
  set Z := Y.subgroupOf C ⊓ Subgroup.centralizer ({c'} : Set C) with hZdef
  have hKZ : K.subgroupOf C ≤ Z := by
    intro k hk
    rw [Subgroup.mem_subgroupOf] at hk
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mpr (hKY hk), ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp (hKc hk)
  set T := (K.subgroupOf C).subgroupOf Z with hT
  set eT : T ≃* K := (Subgroup.subgroupOfEquivOfLe hKZ).trans (Subgroup.subgroupOfEquivOfLe hKC)
    with heT
  refine mem_thetaComponentsIn_iff.mpr ⟨hKZ, ?_, ?_, ?_⟩
  · have hKp : Group.IsPerfect K := Sec6.isPerfect_inSubgroup_perfectResidual _
    exact Group.IsPerfect.ofSurjective (f := eT.symm.toMonoidHom) eT.symm.surjective
  · set ι : Z →* Subgroup.centralizer ({c} : Set G) :=
      (C.subtype.comp Z.subtype).codRestrict _ (fun z => by
        have hz := Subgroup.mem_centralizer_singleton_iff.mp z.2.2
        exact Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hz)) with hι
    set MD := (L.subgroupOf (Subgroup.centralizer ({c} : Set G))).comap ι with hMD
    have hMDsn : MD.IsSubnormal := hL'.2.1.comap ι
    have hTMD : T ≤ MD := by
      intro t ht
      rw [hT, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at ht
      rw [hMD, Subgroup.mem_comap, Subgroup.mem_subgroupOf]
      exact Sec11.sec11K_le L e ht
    have hTn : (T.subgroupOf MD).Normal := by
      constructor
      intro t ht m
      rw [Subgroup.mem_subgroupOf] at ht ⊢
      rw [hT, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at ht ⊢
      have hmL : (((m : Z) : C) : G) ∈ L := m.2
      have hmM : (((m : Z) : C) : G) ∈ L ⊓ Subgroup.centralizer ({e} : Set G) :=
        ⟨hmL, ((m : Z) : C).2⟩
      have := GroupTheory.conj_mem_inSubgroup_perfectResidual hmM ht
      simpa [hK, Sec11.sec11K] using this
    exact Subgroup.IsSubnormal.trans hTMD hTn.isSubnormal hMDsn
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (QuotientGroup.congr _ _ eT (CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv
        Nat.prime_three eT)).symm hq

end Item2119End4Proof

end CFSG.RankThree.PartTwo.Sec21
