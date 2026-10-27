module

public import CFSG.Monster.B.TwoA.Co2Inv.Kernel
public import CFSG.Monster.B.Co2Catalog
public import CFSG.Fischer.Pairs
public import CFSG.LieType.SteinbergBREvenSymplecticThreeRank
public import CFSG.ClassicalGroups.Symplectic.Simple
public import CFSG.RankThree.PartOne.S9.OddCore.TorsionBridge
public import CFSG.Sporadic.Co2
public import Certificates.Certificate3054
public import Certificates.Certificate16022
public import Certificates.Certificate3014
public import Certificates.Certificate3017
public import Certificates.Certificate3019
public import Certificates.Certificate3025
public import Certificates.Certificate3026
public import Certificates.Certificate3028
public import Certificates.Certificate3055
public import Certificates.Certificate3056
public import Certificates.Certificate3114
public import Certificates.Certificate3115
public import Certificates.Certificate3116
public import Certificates.Certificate3117
public import Certificates.Certificate3138
public import Certificates.Certificate16000
public import CFSG.Certificates.InvariantMerge
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.Monster.B.Gen.Max2Assembly
public import CFSG.Sporadic.Th.F2Spec

public noncomputable section

open scoped Pointwise

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.Co2

open CFSG.Blueprint CFSG.Monster CFSG.Monster.Code CFSG.Monster.B.Co2 CFSG.Monster.VisCert
  CFSG.Monster.B.Short CFSG.Monster.Visible CFSG.Monster.ScalarKernel CFSG.Monster.VisQuot
  CFSG.Monster.SpinLattice CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Census CFSG.Monster.Lifts
  CFSG.Monster.B.TwoA.Co2Inv CFSG.Monster.B.Co2Catalog CFSG.Assembly.LowTwoRank

local notation "Co₂" => NativeSporadic.Co2

@[expose] def centralizerMulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B) (x : A) :
    Subgroup.centralizer ({x} : Set A) ≃* Subgroup.centralizer ({e x} : Set B) where
  toFun y := ⟨e y, by
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      Subgroup.mem_centralizer_singleton_iff.1 y.2]⟩
  invFun y := ⟨e.symm y, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply,
      Subgroup.mem_centralizer_singleton_iff.1 y.2]⟩
  left_inv y := Subtype.ext (e.symm_apply_apply y)
  right_inv y := Subtype.ext (e.apply_symm_apply y)
  map_mul' a b := Subtype.ext (map_mul e (a : A) (b : A))

@[expose] def centralizerConjEquiv {A : Type} [Group A] (c x : A) :
    Subgroup.centralizer ({x} : Set A) ≃* Subgroup.centralizer ({c * x * c⁻¹} : Set A) :=
  centralizerMulEquiv (MulAut.conj c) x

@[expose] def rCr : Cr := ⟨rK, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩

theorem rCr_mul_self : rCr * rCr = 1 := Subtype.ext rK_mul_self

theorem rCr_mem_center : rCr ∈ Subgroup.center Cr := by
  rw [Subgroup.mem_center_iff]
  intro k
  exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 k.2)

@[expose] def spEquiv : TauCeti.BilinForm.isometryGroup bZ ≃* StatedSp 3 (ZMod 2) :=
  Classical.choice nonempty_isometryGroup_bZ_equiv

@[expose] def πr : Cr →* StatedSp 3 (ZMod 2) := spEquiv.toMonoidHom.comp resZ

theorem πr_surjective : Function.Surjective πr :=
  spEquiv.surjective.comp resZ_surjective_natCard_ker.1

theorem ker_πr : πr.ker = QCr := by
  ext k
  rw [MonoidHom.mem_ker, QCr_eq_ker, MonoidHom.mem_ker]
  change spEquiv (resZ k) = 1 ↔ _
  exact MulEquiv.map_eq_one_iff spEquiv

theorem QCr_normal : QCr.Normal := by
  rw [← ker_πr]
  infer_instance

theorem isSimpleGroup_sp62 : IsSimpleGroup (StatedSp 3 (ZMod 2)) := by
  have h : IsSimpleGroup (StatedProj (StatedSp 3 (ZMod 2))) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp (ZMod 2) 3 (by norm_num)
      (Or.inr (Or.inr ⟨by simp, le_rfl⟩))
  exact (MulEquiv.isSimpleGroup_congr
    (CFSG.LieType.SteinbergBR.EvenSp.projEquiv (K := ZMod 2) (n := 3) (by norm_num))).1 h

@[expose] def qcrEquiv : QCr ≃* Qgrp :=
  MulEquiv.ofBijective
    ({ toFun := fun k => ⟨((k : Cr) : Kstab v0), k.2⟩
       map_one' := rfl
       map_mul' := fun _ _ => rfl } : QCr →* Qgrp)
    ⟨fun x y h => by
      have h' : (((x : Cr) : Kstab v0) : OLq) = (((y : Cr) : Kstab v0) : OLq) :=
        congrArg (fun q : Qgrp => (q : OLq)) h
      exact Subtype.ext (Subtype.ext (Subtype.ext h')), fun q => by
      obtain ⟨k, hk⟩ := exists_Cr_of_mem_Qgrp q.2
      exact ⟨⟨k, mem_QCr.2 (hk ▸ q.2)⟩, Subtype.ext hk⟩⟩

theorem coe_qcrEquiv (e : QCr) : ((qcrEquiv e : Qgrp) : OLq) = (((e : Cr) : Kstab v0) : OLq) :=
  rfl

theorem isExtraspecial_QCr : IsExtraspecialPGroup 2 QCr :=
  CFSG.RankThree.PartOne.Torsion37.isExtraspecialPGroup_of_mulEquiv qcrEquiv.symm
    isExtraspecialPGroup_Qgrp

theorem rCr_mem_QCr : rCr ∈ QCr := by
  rw [mem_QCr]
  change ((rK : Kstab v0) : OLq) ∈ Qgrp
  rw [← coe_rQ]
  exact rQ.2

@[expose] def rE : QCr := ⟨rCr, rCr_mem_QCr⟩

theorem qcrEquiv_rE : qcrEquiv rE = rQ := by
  apply Subtype.ext
  rw [coe_qcrEquiv, coe_rQ]
  rfl

theorem center_QCr : Subgroup.center QCr = Subgroup.zpowers rE := by
  have hm := CFSG.RankThree.PartOne.Torsion37.center_map_mulEquiv qcrEquiv.symm
  rw [center_Qgrp_eq_zpowers, MonoidHom.map_zpowers] at hm
  rw [← hm]
  congr 1
  rw [← qcrEquiv_rE]
  exact qcrEquiv.symm_apply_apply rE

theorem mem_center_QCr {e : QCr} : e ∈ Subgroup.center QCr ↔ e = 1 ∨ e = rE := by
  rw [center_QCr]
  have hz : rE * rE = 1 := Subtype.ext rCr_mul_self
  constructor
  · intro hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    rcases Int.emod_two_eq_zero_or_one n with h | h
    · left
      rw [← Int.emod_add_mul_ediv n 2, h, zero_add, zpow_mul, show rE ^ (2 : ℤ) = 1 by
        rw [zpow_two, hz], one_zpow]
    · right
      rw [← Int.emod_add_mul_ediv n 2, h, zpow_add, zpow_mul, show rE ^ (2 : ℤ) = 1 by
        rw [zpow_two, hz], one_zpow, mul_one, zpow_one]
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact Subgroup.mem_zpowers _

theorem conj_mem_QCr {a b : Cr} (ha : a ∈ QCr) (hb : b ∈ QCr) :
    a * b * a⁻¹ = b ∨ a * b * a⁻¹ = b * rCr := by
  obtain ⟨-, hcomm, -, -⟩ := isExtraspecial_QCr
  set a' : QCr := ⟨a, ha⟩
  set b' : QCr := ⟨b, hb⟩
  have hc : a' * b' * a'⁻¹ * b'⁻¹ ∈ Subgroup.center QCr := by
    rw [← hcomm]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a') (Subgroup.mem_top b')
  rcases mem_center_QCr.1 hc with h | h
  · left
    have h' : a * b * a⁻¹ * b⁻¹ = 1 := congrArg (fun x : QCr => (x : Cr)) h
    calc a * b * a⁻¹ = a * b * a⁻¹ * b⁻¹ * b := by group
      _ = b := by rw [h', one_mul]
  · right
    have h' : a * b * a⁻¹ * b⁻¹ = rCr := congrArg (fun x : QCr => (x : Cr)) h
    have hcomm' : rCr * b = b * rCr := (Subgroup.mem_center_iff.1 rCr_mem_center b).symm
    calc a * b * a⁻¹ = a * b * a⁻¹ * b⁻¹ * b := by group
      _ = rCr * b := by rw [h']
      _ = b * rCr := hcomm'

theorem fPerms_six_perm : PermArr fPerms[6]! = true := fPerms_PermArr 6 (by norm_num)

theorem affMask_six_check : ∀ x : Fin 24,
    (affMask 0 7).testBit x = (affMask 0 1).testBit (fPerms[6]!)[(x : ℕ)]! := by
  decide +kernel

theorem permC_symm_fAut_six : (permC (fAut 6)).symm (affC 0 1) = affC 0 7 := by
  apply Subtype.ext
  funext x
  rw [permC_symm_apply, coe_permC, Visible.permWord_apply', coe_inv_autPerm, inv_inv,
    coe_affC (by norm_num) (by norm_num), coe_affC (by norm_num) (by norm_num), bvec_apply,
    bvec_apply]
  have hx : (((fAut 6 : AutPerm) : Equiv.Perm (Fin 24)) x : ℕ) = (fPerms[6]!)[(x : ℕ)]! := by
    rw [coe_fAut]
    exact decode_apply fPerms_six_perm x
  rw [hx, affMask_six_check x]

theorem qElt_affC (e l : ℕ) : qElt e l 0 = QuotientGroup.mk (gO (affC e l)) := by
  rw [qElt, transP_zero, PO_one, mul_one]

theorem fK_six_conj :
    ((fK 6 : Kstab v0) : OLq) * qElt 0 1 0 * ((fK 6 : Kstab v0) : OLq)⁻¹ = qElt 0 7 0 := by
  rw [qElt_affC, qElt_affC]
  change QuotientGroup.mk (PO (fAut 6)) * QuotientGroup.mk (gO (affC 0 1)) *
    (QuotientGroup.mk (PO (fAut 6)))⁻¹ = (QuotientGroup.mk (gO (affC 0 7)) : OLq)
  rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, PO_mul_gO,
    mul_inv_cancel_right, permC_symm_fAut_six]

@[expose] def qOne : Cr := ⟨qK (e := 0) (l := 1) (t := 0) (by norm_num) (by norm_num)
  (by norm_num), qK_mem_Cr _ _ _⟩

@[expose] def fSix : Cr := ⟨fK 6, by
  have h := cGen_mem_Cr ⟨6, by norm_num⟩
  rwa [cGen_of_lt (k := ⟨6, by norm_num⟩) (by norm_num)] at h⟩

theorem qOne_mem_QCr : qOne ∈ QCr := by
  rw [mem_QCr]
  exact mem_Qgrp_iff.2 ⟨0, by norm_num, 1, by norm_num, 0, by norm_num, rfl⟩

theorem fSix_conj_qOne :
    fSix * qOne * fSix⁻¹ ≠ qOne ∧ fSix * qOne * fSix⁻¹ ≠ qOne * rCr := by
  have hc : (((fSix * qOne * fSix⁻¹ : Cr) : Kstab v0) : OLq) = qElt 0 7 0 := fK_six_conj
  have h1 : (((qOne : Cr) : Kstab v0) : OLq) = qElt 0 1 0 := rfl
  have h2 : (((qOne * rCr : Cr) : Kstab v0) : OLq) = qElt 1 1 0 := by
    change qElt 0 1 0 * (rK : OLq) = qElt 1 1 0
    rw [← qElt_one_zero_zero, qElt_mul (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)]
    rfl
  constructor
  · intro h
    have := congrArg (fun k : Cr => ((k : Kstab v0) : OLq)) h
    rw [hc, h1] at this
    have := qElt_inj (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) this
    omega
  · intro h
    have := congrArg (fun k : Cr => ((k : Kstab v0) : OLq)) h
    rw [hc, h2] at this
    have := qElt_inj (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) this
    omega

theorem eq_one_or_eq_rCr_of_commute_QCr {h : Cr} (hc : ∀ e ∈ QCr, h * e = e * h) :
    h = 1 ∨ h = rCr := by
  set C : Subgroup Cr := Subgroup.centralizer (QCr : Set Cr) with hC
  have := QCr_normal
  have hCn : C.Normal := Subgroup.normal_centralizer
  have := isSimpleGroup_sp62
  have hCmap : (C.map πr).Normal := hCn.map πr πr_surjective
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (C.map πr) with hbot | htop
  ·
    have hhC : h ∈ C := Subgroup.mem_centralizer_iff.2 fun e he => (hc e he).symm
    have hhE : h ∈ QCr := by
      rw [← ker_πr, MonoidHom.mem_ker]
      have : πr h ∈ C.map πr := Subgroup.mem_map_of_mem _ hhC
      rw [hbot, Subgroup.mem_bot] at this
      exact this
    have hz : (⟨h, hhE⟩ : QCr) ∈ Subgroup.center QCr := by
      rw [Subgroup.mem_center_iff]
      intro e
      exact Subtype.ext (hc e e.2).symm
    rcases mem_center_QCr.1 hz with h1 | h1
    · left
      exact congrArg Subtype.val h1
    · right
      exact congrArg Subtype.val h1
  ·
    exfalso
    obtain ⟨c, hcC, hcx⟩ : ∃ c ∈ C, πr c = πr fSix := by
      have : πr fSix ∈ C.map πr := by rw [htop]; exact Subgroup.mem_top _
      obtain ⟨c, hc, h'⟩ := Subgroup.mem_map.1 this
      exact ⟨c, hc, h'⟩
    have he : c⁻¹ * fSix ∈ QCr := by
      rw [← ker_πr, MonoidHom.mem_ker, map_mul, map_inv, hcx, inv_mul_cancel]
    have hxq : fSix * qOne * fSix⁻¹ = (c⁻¹ * fSix) * qOne * (c⁻¹ * fSix)⁻¹ := by
      have : fSix * qOne * fSix⁻¹ = c * ((c⁻¹ * fSix) * qOne * (c⁻¹ * fSix)⁻¹) * c⁻¹ := by
        group
      rw [this]
      have hm : (c⁻¹ * fSix) * qOne * (c⁻¹ * fSix)⁻¹ ∈ QCr :=
        QCr_normal.conj_mem _ qOne_mem_QCr _
      have hc' := Subgroup.mem_centralizer_iff.1 hcC _ hm
      rw [← hc', mul_assoc, mul_inv_cancel, mul_one]
    have hw := fSix_conj_qOne
    rcases conj_mem_QCr he qOne_mem_QCr with h1 | h1
    · exact hw.1 (hxq.trans h1)
    · exact hw.2 (hxq.trans h1)

theorem eq_one_or_eq_rCr_of_mem_center {h : Cr} (hh : h ∈ Subgroup.center Cr) :
    h = 1 ∨ h = rCr :=
  eq_one_or_eq_rCr_of_commute_QCr fun e _ => (Subgroup.mem_center_iff.1 hh e).symm

instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem natCard_Kstab : Nat.card (Kstab v0) = 42305421312000 := by
  rw [← CFSG.Sporadic.Co2.card_Co2]
  exact Nat.card_congr (EquivLike.toEquiv co2CatalogEquiv)

instance finite_Kstab : Finite (Kstab v0) :=
  Nat.finite_of_card_ne_zero (by rw [natCard_Kstab]; norm_num)

instance finite_Cr : Finite Cr := Nat.finite_of_card_ne_zero (by rw [natCard_Cr]; norm_num)

theorem factorization_card_Kstab : (Nat.card (Kstab v0)).factorization 2 = 18 := by
  rw [natCard_Kstab, show (42305421312000 : ℕ) = 2 ^ 18 * 161382375 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem factorization_card_Cr : (Nat.card Cr).factorization 2 = 18 := by
  rw [natCard_Cr, show (743178240 : ℕ) = 2 ^ 18 * 2835 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

@[expose] def sylowOfCr (P : Sylow 2 Cr) : Sylow 2 (Kstab v0) :=
  Sylow.ofCard ((P : Subgroup Cr).map Cr.subtype) (by
    rw [Subgroup.card_map_of_injective Cr.subtype_injective, Sylow.card_eq_multiplicity,
      factorization_card_Cr, factorization_card_Kstab])

theorem QCr_le_sylow (P : Sylow 2 Cr) : QCr ≤ (P : Subgroup Cr) := by
  have := QCr_normal
  exact IsPGroup.le_sylow_of_normal isExtraspecial_QCr.1 P

theorem eq_one_or_eq_rCr_of_central (P : Sylow 2 Cr) {y : Cr}
    (hc : ∀ s ∈ (P : Subgroup Cr), y * s = s * y) : y = 1 ∨ y = rCr :=
  eq_one_or_eq_rCr_of_commute_QCr fun e he => hc e (QCr_le_sylow P he)

theorem eq_one_or_eq_rK_of_mem_sylowOfCr (P : Sylow 2 Cr) {x : Kstab v0}
    (hx : x ∈ (sylowOfCr P : Subgroup (Kstab v0)))
    (hc : ∀ s ∈ (sylowOfCr P : Subgroup (Kstab v0)), x * s = s * x) : x = 1 ∨ x = rK := by
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
  have hcomm : ∀ s ∈ (P : Subgroup Cr), y * s = s * y := fun s hs =>
    Subtype.ext (hc (s : Kstab v0) (Subgroup.mem_map_of_mem _ hs))
  rcases eq_one_or_eq_rCr_of_central P hcomm with h | h
  · left; rw [h]; rfl
  · right; rw [h]; rfl

theorem isConj_rK_of_central (S : Sylow 2 (Kstab v0)) (t : Kstab v0)
    (ht : t ∈ (S : Subgroup (Kstab v0)) ∧ ∀ s ∈ (S : Subgroup (Kstab v0)), t * s = s * t)
    (ht1 : t ≠ 1) : IsConj rK t := by
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 Cr))
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Kstab v0) (sylowOfCr P) S
  have hS : (S : Subgroup (Kstab v0)) = MulAut.conj g • (sylowOfCr P : Subgroup (Kstab v0)) := by
    rw [← hg, Sylow.coe_subgroup_smul]
  have hmem : g⁻¹ * t * g ∈ (sylowOfCr P : Subgroup (Kstab v0)) := by
    have h1 := ht.1
    rw [hS, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h1
    simpa [MulAut.smul_def, MulAut.conj_apply, mul_assoc] using h1
  have hcomm : ∀ s ∈ (sylowOfCr P : Subgroup (Kstab v0)),
      (g⁻¹ * t * g) * s = s * (g⁻¹ * t * g) := by
    intro s hs
    have hs' : g * s * g⁻¹ ∈ (S : Subgroup (Kstab v0)) := by
      rw [hS, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      simpa [MulAut.smul_def, MulAut.conj_apply, mul_assoc] using hs
    have e := ht.2 _ hs'
    calc g⁻¹ * t * g * s = g⁻¹ * (t * (g * s * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * s * g⁻¹) * t) * g := by rw [e]
      _ = s * (g⁻¹ * t * g) := by group
  rcases eq_one_or_eq_rK_of_mem_sylowOfCr P hmem hcomm with h1 | h1
  · exfalso
    apply ht1
    calc t = g * (g⁻¹ * t * g) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group
  · refine isConj_iff.2 ⟨g, ?_⟩
    rw [← h1]
    group

end CFSG.RankThree.Co2
