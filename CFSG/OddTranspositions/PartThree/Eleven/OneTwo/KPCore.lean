module

public import CFSG.OddTranspositions.PartThree.Eleven.Statements
public import CFSG.OddTranspositions.PartThree.Eleven.OneOne.Hyp
public import CFSG.OddTranspositions.PartThree.Eleven.Minus.Pair
public import CFSG.OddTranspositions.PartThree.Eleven.Minus.Quandle
public import CFSG.OddTranspositions.PartThree.EightFive.KBarSetup
public import Certificates.Certificate2326
public import CFSG.OddTranspositions.PartThree.Eleven.OneTwo.KTrans
import CFSG.CGT.Timmesfeld75.Sec4TwoBender
import CFSG.Timmesfeld.Bridge.OddTranspGenL2
import CFSG.CGT.Timmesfeld75.Derivations
import CFSG.CGT.Timmesfeld75.Lemma25
import CFSG.CGT.Timmesfeld75.SimpleCase
import CFSG.CGT.Timmesfeld75.Targets

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity CFSG.OddTranspositions.QZ
open scoped commutatorElement

section KPCore

variable {G : Type} [Group G] [Finite G] {D : Set G}

private theorem map_le_zpowers_of_normal_isPGroup {X : Type} [Group X] (L : Subgroup X)
    (z : X) (hz : z ∈ L) [(Subgroup.zpowers (⟨z, hz⟩ : L)).Normal]
    (hsimple : IsSimpleGroup (L ⧸ Subgroup.zpowers (⟨z, hz⟩ : L)))
    (hnotp : ¬ IsPGroup 2 (L ⧸ Subgroup.zpowers (⟨z, hz⟩ : L)))
    (R : Subgroup L) (hRn : R.Normal) (hRp : IsPGroup 2 R) :
    R.map L.subtype ≤ Subgroup.zpowers z := by
  haveI : IsSimpleGroup (L ⧸ Subgroup.zpowers (⟨z, hz⟩ : L)) := hsimple
  let q : L →* L ⧸ Subgroup.zpowers (⟨z, hz⟩ : L) :=
    QuotientGroup.mk' (Subgroup.zpowers (⟨z, hz⟩ : L))
  have hRq : (R.map q).Normal := hRn.map q (QuotientGroup.mk'_surjective _)
  have hRqp : IsPGroup 2 (R.map q) := hRp.map q
  rcases hRq.eq_bot_or_eq_top with hbot | htop
  · have hle : R ≤ q.ker := (Subgroup.map_eq_bot_iff (H := R)).mp hbot
    rw [QuotientGroup.ker_mk'] at hle
    rintro _ ⟨r, hr, rfl⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hle hr)
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, by rw [← hk]; simp⟩
  · have htop' : IsPGroup 2 (⊤ : Subgroup (L ⧸ Subgroup.zpowers (⟨z, hz⟩ : L))) :=
      htop ▸ hRqp
    exact absurd (htop'.of_equiv Subgroup.topEquiv) hnotp

theorem solvableRadical_eq_pCore_of_oddCore_eq_bot {X : Type} [Group X] [Finite X]
    (hO : CFSG.oddCore X = ⊥) (h2 : Nat.card (CFSG.pCore 2 X) = 2) :
    CFSG.solvableRadical X = CFSG.pCore 2 X := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P : Subgroup X := CFSG.pCore 2 X with hP
  set R : Subgroup X := CFSG.solvableRadical X with hR
  have h2P : Nat.card P = 2 := by rw [hP]; exact h2
  have hPn : P.Normal := CFSG.pCore_normal
  have hPsolv : Group.IsSolvable P := by
    haveI : Group.IsNilpotent P := CFSG.pCore_isNilpotent (G := X) (p := 2)
    infer_instance
  have hPleR : P ≤ R := le_sSup ⟨hPn, hPsolv⟩
  have hRnorm : R.Normal := CFSG.ABGLocalTools.solvableRadical_normal
  have hRsolv : Group.IsSolvable R := CFSG.ABGLocalTools.solvableRadical_isSolvable
  have hpp : CFSG.pPrimeCore 2 R = ⊥ := by
    have hnorm : ((CFSG.pPrimeCore 2 R).map R.subtype).Normal :=
      ConjAct.normal_of_characteristic_of_normal
    have hodd : Odd (Nat.card ((CFSG.pPrimeCore 2 R).map R.subtype)) := by
      rw [Subgroup.card_map_of_injective Subtype.val_injective]
      exact Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := R))
    have hle : (CFSG.pPrimeCore 2 R).map R.subtype ≤ CFSG.oddCore X :=
      CFSG.ABGLocalTools.le_oddCore_of_normal hnorm hodd
    rw [hO] at hle
    have hbot : (CFSG.pPrimeCore 2 R).map R.subtype = ⊥ := le_bot_iff.mp hle
    exact (Subgroup.map_eq_bot_iff_of_injective (H := CFSG.pPrimeCore 2 R)
      (f := R.subtype) Subtype.val_injective).mp hbot
  have hF_eq : CFSG.fittingSubgroup R = CFSG.pCore 2 R :=
    CFSG.Fitting_eq_pcore R 2 hpp
  have hFmap_le_P : (CFSG.fittingSubgroup R).map R.subtype ≤ P := by
    rw [hF_eq, hP]
    refine le_sSup ⟨ConjAct.normal_of_characteristic_of_normal, ?_⟩
    exact (CFSG.pCore_isPGroup (p := 2) (G := R)).map R.subtype
  have hPle_center : P ≤ Subgroup.center X := by
    intro p hp
    rw [Subgroup.mem_center_iff]
    intro x
    by_cases hp1 : p = 1
    · rw [hp1, mul_one, one_mul]
    · have hconj : x * p * x⁻¹ ∈ P := hPn.conj_mem p hp x
      have hne : x * p * x⁻¹ ≠ 1 := by
        intro h
        apply hp1
        have h' := congrArg (fun t => x⁻¹ * t * x) h
        simpa [mul_assoc] using h'
      obtain ⟨y, -, huniq⟩ := (Nat.card_eq_two_iff' (1 : P)).mp h2P
      have e1 : (⟨x * p * x⁻¹, hconj⟩ : P) = y := huniq _ (by simpa using hne)
      have e2 : (⟨p, hp⟩ : P) = y := huniq _ (by simpa using hp1)
      have hfix : x * p * x⁻¹ = p := congrArg Subtype.val (e1.trans e2.symm)
      calc x * p = x * p * x⁻¹ * x := by group
        _ = p * x := by rw [hfix]
  have hcentral : (⊤ : Subgroup R) ≤
      Subgroup.centralizer (CFSG.fittingSubgroup R : Set R) := by
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    apply Subtype.ext
    show (y : X) * (x : X) = (x : X) * (y : X)
    exact (Subgroup.mem_center_iff.mp (hPle_center (hFmap_le_P
      (Subgroup.mem_map_of_mem R.subtype hy))) (x : X)).symm
  have hFtop : CFSG.fittingSubgroup R = ⊤ := by
    refine top_le_iff.mp (hcentral.trans ?_)
    exact CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hRsolv
  have hRleP : R ≤ P := by
    have hmap : (CFSG.fittingSubgroup R).map R.subtype = R := by
      rw [hFtop, Subgroup.map_top, Subgroup.range_subtype]
    rw [← hmap]
    exact hFmap_le_P
  exact le_antisymm hRleP hPleR

namespace ElevenTwoFrame

variable {hC : HypothesisC D} {S : Sylow 2 G} {T : Sylow 2 (Halpha D hC.alpha)}
  {r : Fin 3 → Halpha D hC.alpha}

private theorem sq_mul_three_eq_one {X : Type} [Group X] {a b c : X}
    (hab : Commute a b) (hac : Commute a c) (hbc : Commute b c)
    (ha : a * a = 1) (hb : b * b = 1) (hc : c * c = 1) :
    (a * b * c) * (a * b * c) = 1 := by
  have hbc' : (b * c) * (b * c) = 1 := by
    rw [show b * c * (b * c) = b * (c * b) * c by group, hbc.symm.eq]
    rw [show b * (b * c) * c = b * b * (c * c) by group, hb, hc, mul_one]
  have habc : Commute a (b * c) := hab.mul_right hac
  rw [show a * b * c * (a * b * c) = a * (b * c) * (a * (b * c)) by group]
  rw [show a * (b * c) * (a * (b * c)) =
      a * ((b * c) * a) * (b * c) by group, habc.symm.eq]
  rw [show a * (a * (b * c)) * (b * c) = a * a * ((b * c) * (b * c)) by group,
    ha, hbc', mul_one]

private abbrev pcTH (hC : HypothesisC D) (r : Fin 3 → Halpha D hC.alpha) :
    Halpha D hC.alpha := r 0 * r 1 * r 2

private abbrev pcK (hC : HypothesisC D) (r : Fin 3 → Halpha D hC.alpha) : Subgroup G :=
  localGroup D (frameE hC r)

private abbrev pcL (hC : HypothesisC D) (r : Fin 3 → Halpha D hC.alpha) :
    Subgroup (Halpha D hC.alpha) := localGroup (DstarH hC) (r 0 * r 1 * r 2)

private abbrev pcLG (hC : HypothesisC D) (r : Fin 3 → Halpha D hC.alpha) : Subgroup G :=
  (pcL hC r).map (Halpha D hC.alpha).subtype

private abbrev pcB (hC : HypothesisC D) (r : Fin 3 → Halpha D hC.alpha) : Subgroup G :=
  Halpha D hC.alpha ⊓ Subgroup.centralizer {frameT hC r}

private abbrev pcM (hC : HypothesisC D) (r : Fin 3 → Halpha D hC.alpha) : Subgroup G :=
  Subgroup.zpowers hC.d ⊔ pcB hC r

private abbrev pcPG (hC : HypothesisC D) (r : Fin 3 → Halpha D hC.alpha) : Subgroup G :=
  (CFSG.pCore 2 (pcK hC r)).map (pcK hC r).subtype

private abbrev pcCpu (hC : HypothesisC D) (r : Fin 3 → Halpha D hC.alpha) : Subgroup G :=
  Subgroup.centralizer {hC.d} ⊓ pcPG hC r

private structure PCoreFacts (hC : HypothesisC D) (r : Fin 3 → Halpha D hC.alpha) where
  huK : hC.d ∈ pcK hC r
  heK : frameE hC r ∈ pcK hC r
  htK : frameT hC r ∈ pcK hC r
  hri_mem : ∀ i, r i ∈ DstarH hC
  hri_comm : ∀ i, Commute (r i) (pcTH hC r)
  htH_mem : pcTH hC r ∈ pcL hC r

private theorem pCore_frame_normalizers (P : PCoreFacts hC r) :
    pcLG hC r ≤ Halpha D hC.alpha ∧ pcLG hC r ≤ pcK hC r ∧
      hC.d ∈ Subgroup.centralizer (Halpha D hC.alpha : Set G) ∧
        ⁅pcLG hC r, pcM hC r⁆ ≤ pcLG hC r := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨huK, heK, htK, hri_mem, hri_comm, htH_mem⟩ := P
  set u : G := hC.d with hu
  set e : G := frameE hC r with he
  set t : G := frameT hC r with ht
  set K : Subgroup G := localGroup D e with hK
  set tH : Halpha D hC.alpha := r 0 * r 1 * r 2 with htH
  set L : Subgroup (Halpha D hC.alpha) := localGroup (DstarH hC) tH with hL
  let LG : Subgroup G := L.map (Halpha D hC.alpha).subtype
  let B : Subgroup G := Halpha D hC.alpha ⊓ Subgroup.centralizer {t}
  let M : Subgroup G := Subgroup.zpowers u ⊔ B
  let PG : Subgroup G := (CFSG.pCore 2 K).map K.subtype
  let Cpu : Subgroup G := Subgroup.centralizer {u} ⊓ PG
  have ht_coe : t = (tH : G) := by rw [ht, htH]; rfl
  have he_def : e = u * t := by rw [he, hu, ht]; rfl
  change LG ≤ Halpha D hC.alpha ∧ LG ≤ K ∧
      u ∈ Subgroup.centralizer (Halpha D hC.alpha : Set G) ∧ ⁅LG, M⁆ ≤ LG
  have hconj_mem : ∀ x ∈ Subgroup.centralizer ({tH} : Set (Halpha D hC.alpha)),
      ∀ y ∈ centSet (DstarH hC) tH, x * y * x⁻¹ ∈ centSet (DstarH hC) tH := by
    intro x hx y hy
    have hxt : Commute x tH := Subgroup.mem_centralizer_singleton_iff.mp hx
    refine ⟨DstarH_conj_mem hC (h := x) hy.1, ?_⟩
    rw [commute_iff_eq]
    calc (x * y * x⁻¹) * tH = x * y * (x⁻¹ * tH) := by group
      _ = x * y * (tH * x⁻¹) := by rw [hxt.inv_left.eq]
      _ = x * (y * tH) * x⁻¹ := by group
      _ = x * (tH * y) * x⁻¹ := by rw [hy.2.eq]
      _ = x * tH * (y * x⁻¹) := by group
      _ = tH * x * (y * x⁻¹) := by rw [hxt.eq]
      _ = tH * (x * y * x⁻¹) := by group
  have hLnorm : Subgroup.centralizer ({tH} : Set (Halpha D hC.alpha)) ≤
      Subgroup.normalizer (L : Set (Halpha D hC.alpha)) := by
    rw [Subgroup.le_normalizer_iff]
    intro x hx k hk
    rw [hL] at hk ⊢
    induction hk using Subgroup.closure_induction with
    | mem y hy => exact Subgroup.subset_closure (hconj_mem x hx y hy)
    | one => simpa using (Subgroup.closure (centSet (DstarH hC) tH)).one_mem
    | mul y z _ _ hy hz =>
        have h : x * (y * z) * x⁻¹ = (x * y * x⁻¹) * (x * z * x⁻¹) := by group
        rw [h]
        exact Subgroup.mul_mem _ hy hz
    | inv y _ hy =>
        have h : x * y⁻¹ * x⁻¹ = (x * y * x⁻¹)⁻¹ := by group
        rw [h]
        exact Subgroup.inv_mem _ hy
  have hLG_le_H : LG ≤ Halpha D hC.alpha := Subgroup.map_subtype_le L
  have hcentSet_le_K : ∀ y ∈ centSet (DstarH hC) tH, (y : G) ∈ K := by
    intro y hy
    have hyD : (y : G) ∈ D :=
      DalphaStar_subset hC.isBlock_alpha ((mem_DstarH_iff hC).mp hy.1)
    have hcomm_u : Commute (y : G) u :=
      (hC.DalphaStar_subset_commute ((mem_DstarH_iff hC).mp hy.1)).2
    have hcomm_t : Commute (y : G) t := by
      rw [ht_coe]
      exact hy.2.map (Halpha D hC.alpha).subtype
    rw [hK]
    exact mem_localGroup_of_mem ⟨hyD, hcomm_u.mul_right hcomm_t⟩
  have hLG_le_K : LG ≤ K := by
    change L.map (Halpha D hC.alpha).subtype ≤ K
    rw [Subgroup.map_le_iff_le_comap]
    refine (Subgroup.closure_le _).mpr ?_
    intro y hy
    exact hcentSet_le_K y hy
  have hu_central : u ∈ Subgroup.centralizer (Halpha D hC.alpha : Set G) := by
    rw [hu]
    change hC.d ∈ Subgroup.centralizer (Subgroup.closure (DalphaStar D hC.alpha) : Set G)
    rw [Subgroup.centralizer_closure]
    exact Subgroup.mem_centralizer_iff.mpr (fun y hy => (hC.DalphaStar_subset_commute hy).2)
  have hBnorm : B ≤ Subgroup.normalizer (LG : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro b hb l hl
    change b ∈ Halpha D hC.alpha ⊓ Subgroup.centralizer {t} at hb
    change l ∈ L.map (Halpha D hC.alpha).subtype at hl
    obtain ⟨lH, hlH, rfl⟩ := Subgroup.mem_map.mp hl
    set bH : Halpha D hC.alpha := ⟨b, hb.1⟩ with hbHdef
    have hbH : bH ∈ Subgroup.centralizer ({tH} : Set (Halpha D hC.alpha)) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      show (b : G) * t = t * (b : G)
      exact Subgroup.mem_centralizer_singleton_iff.mp hb.2
    have hbHnorm : bH ∈ Subgroup.normalizer (L : Set (Halpha D hC.alpha)) := hLnorm hbH
    refine Subgroup.mem_map.mpr ⟨bH * lH * bH⁻¹, ?_, ?_⟩
    · rw [Subgroup.mem_normalizer_iff] at hbHnorm
      exact (hbHnorm lH).mp hlH
    · simp [hbHdef]
  have hzu_norm : Subgroup.zpowers u ≤ Subgroup.normalizer (LG : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro x hx l hl
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hlH : l ∈ Halpha D hC.alpha := hLG_le_H hl
    have hcomm : Commute u l := (Subgroup.mem_centralizer_iff.mp hu_central l hlH).symm
    have hcommk : Commute (u ^ k) l := hcomm.zpow_left k
    have hred : l * u ^ k * (u ^ k)⁻¹ = l := by group
    rw [hcommk.eq, hred]
    exact hl
  have hMnorm : M ≤ Subgroup.normalizer (LG : Set G) := by
    change Subgroup.zpowers u ⊔ B ≤ Subgroup.normalizer (LG : Set G)
    exact sup_le hzu_norm hBnorm
  have hcomm_le : ⁅LG, M⁆ ≤ LG := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_right.mp hMnorm
  exact ⟨hLG_le_H, hLG_le_K, hu_central, hcomm_le⟩

private theorem pCore_pCore_map (h : ElevenTwoHyp hC) (hF : ElevenTwoFrame hC S T r)
    (P : PCoreFacts hC r)
    [(Subgroup.zpowers (⟨pcTH hC r, P.htH_mem⟩ : pcL hC r)).Normal]
    (hLG_le_K : pcLG hC r ≤ pcK hC r)
    (hnotp : ¬ IsPGroup 2 (pcL hC r ⧸
      Subgroup.zpowers (⟨pcTH hC r, P.htH_mem⟩ : pcL hC r))) :
    IsPGroup 2 (pcPG hC r) ∧
      (∀ k ∈ pcK hC r, ∀ x ∈ pcPG hC r, k * x * k⁻¹ ∈ pcPG hC r) ∧
      (⟨hC.d, P.huK⟩ : pcK hC r) ∉ CFSG.pCore 2 (pcK hC r) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨huK, heK, htK, hri_mem, hri_comm, htH_mem⟩ := P
  set u : G := hC.d with hu
  set e : G := frameE hC r with he
  set t : G := frameT hC r with ht
  set K : Subgroup G := localGroup D e with hK
  set tH : Halpha D hC.alpha := r 0 * r 1 * r 2 with htH
  set L : Subgroup (Halpha D hC.alpha) := localGroup (DstarH hC) tH with hL
  let LG : Subgroup G := L.map (Halpha D hC.alpha).subtype
  let B : Subgroup G := Halpha D hC.alpha ⊓ Subgroup.centralizer {t}
  let M : Subgroup G := Subgroup.zpowers u ⊔ B
  let PG : Subgroup G := (CFSG.pCore 2 K).map K.subtype
  let Cpu : Subgroup G := Subgroup.centralizer {u} ⊓ PG
  have ht_coe : t = (tH : G) := by rw [ht, htH]; rfl
  have he_def : e = u * t := by rw [he, hu, ht]; rfl
  change IsPGroup 2 PG ∧
      (∀ k ∈ K, ∀ x ∈ PG, k * x * k⁻¹ ∈ PG) ∧
      (⟨u, huK⟩ : K) ∉ CFSG.pCore 2 K
  have hPGp : IsPGroup 2 PG := (CFSG.pCore_isPGroup (p := 2) (G := K)).map K.subtype
  have hPGconj : ∀ k ∈ K, ∀ x ∈ PG, k * x * k⁻¹ ∈ PG := by
    intro k hk x hx
    change x ∈ (CFSG.pCore 2 K).map K.subtype at hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    refine Subgroup.mem_map.mpr ⟨⟨k, hk⟩ * y * ⟨k, hk⟩⁻¹, ?_, ?_⟩
    · exact (inferInstance : (CFSG.pCore 2 K).Normal).conj_mem y hy ⟨k, hk⟩
    · simp
  have hu_not_mem_P : (⟨u, huK⟩ : K) ∉ CFSG.pCore 2 K := by
    intro huP
    have hGamma_sub : ∀ x ∈ centSet D e, x ∈ PG := by
      intro x hx
      obtain ⟨k, hk, hkx⟩ := transitive h hF x hx
      refine Subgroup.mem_map.mpr ⟨⟨k, hk⟩ * ⟨u, huK⟩ * ⟨k, hk⟩⁻¹, ?_, ?_⟩
      · exact (inferInstance : (CFSG.pCore 2 K).Normal).conj_mem ⟨u, huK⟩ huP ⟨k, hk⟩
      · change k * u * k⁻¹ = x
        exact hkx
    have hK_eq : K = PG := by
      refine le_antisymm ?_ (Subgroup.map_subtype_le _)
      change localGroup D e ≤ PG
      rw [localGroup]
      exact (Subgroup.closure_le _).mpr hGamma_sub
    have hKp : IsPGroup 2 K := hK_eq ▸ hPGp
    have hLGp : IsPGroup 2 LG := hKp.to_le hLG_le_K
    have hLp : IsPGroup 2 L :=
      hLGp.of_equiv (Subgroup.equivMapOfInjective L (Halpha D hC.alpha).subtype
        Subtype.val_injective).symm
    exact hnotp (hLp.to_quotient (Subgroup.zpowers (⟨tH, htH_mem⟩ : L)))
  exact ⟨hPGp, hPGconj, hu_not_mem_P⟩

private theorem pCore_frameT_sq_and_cpu_le_M (h : ElevenTwoHyp hC)
    (hF : ElevenTwoFrame hC S T r) (P : PCoreFacts hC r) :
    frameT hC r * frameT hC r = 1 ∧ pcCpu hC r ≤ pcM hC r := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨huK, heK, htK, hri_mem, hri_comm, htH_mem⟩ := P
  set u : G := hC.d with hu
  set e : G := frameE hC r with he
  set t : G := frameT hC r with ht
  set K : Subgroup G := localGroup D e with hK
  set tH : Halpha D hC.alpha := r 0 * r 1 * r 2 with htH
  set L : Subgroup (Halpha D hC.alpha) := localGroup (DstarH hC) tH with hL
  let LG : Subgroup G := L.map (Halpha D hC.alpha).subtype
  let B : Subgroup G := Halpha D hC.alpha ⊓ Subgroup.centralizer {t}
  let M : Subgroup G := Subgroup.zpowers u ⊔ B
  let PG : Subgroup G := (CFSG.pCore 2 K).map K.subtype
  let Cpu : Subgroup G := Subgroup.centralizer {u} ⊓ PG
  have ht_coe : t = (tH : G) := by rw [ht, htH]; rfl
  have he_def : e = u * t := by rw [he, hu, ht]; rfl
  change t * t = 1 ∧ Cpu ≤ M
  have ht_sq : t * t = 1 := by
    have h0 : ((r 0 : Halpha D hC.alpha) : G) * ((r 0 : Halpha D hC.alpha) : G) = 1 :=
      hC.setup.oddT.mul_self_eq_one
        (DalphaStar_subset hC.isBlock_alpha ((mem_DstarH_iff hC).mp (hri_mem 0)))
    have h1 : ((r 1 : Halpha D hC.alpha) : G) * ((r 1 : Halpha D hC.alpha) : G) = 1 :=
      hC.setup.oddT.mul_self_eq_one
        (DalphaStar_subset hC.isBlock_alpha ((mem_DstarH_iff hC).mp (hri_mem 1)))
    have h2 : ((r 2 : Halpha D hC.alpha) : G) * ((r 2 : Halpha D hC.alpha) : G) = 1 :=
      hC.setup.oddT.mul_self_eq_one
        (DalphaStar_subset hC.isBlock_alpha ((mem_DstarH_iff hC).mp (hri_mem 2)))
    have c01 : Commute ((r 0 : Halpha D hC.alpha) : G) ((r 1 : Halpha D hC.alpha) : G) :=
      (hF.frame.commute 0 1).map (Halpha D hC.alpha).subtype
    have c02 : Commute ((r 0 : Halpha D hC.alpha) : G) ((r 2 : Halpha D hC.alpha) : G) :=
      (hF.frame.commute 0 2).map (Halpha D hC.alpha).subtype
    have c12 : Commute ((r 1 : Halpha D hC.alpha) : G) ((r 2 : Halpha D hC.alpha) : G) :=
      (hF.frame.commute 1 2).map (Halpha D hC.alpha).subtype
    rw [ht, frameT]
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact sq_mul_three_eq_one c01 c02 c12 h0 h1 h2
  have hM_eq : Subgroup.centralizer {u} ⊓ Subgroup.centralizer {e} =
      Subgroup.zpowers u ⊔ (Halpha D hC.alpha ⊓ Subgroup.centralizer {t}) := by
    rw [hu, he, ht]
    exact centralizer_d_inf h hF
  have hCpu_le_M : Cpu ≤ M := by
    change Cpu ≤ Subgroup.zpowers u ⊔ (Halpha D hC.alpha ⊓ Subgroup.centralizer {t})
    intro x hx
    have hxu : x ∈ Subgroup.centralizer {u} := hx.1
    have hxK : x ∈ K := Subgroup.map_subtype_le (CFSG.pCore 2 K) hx.2
    have hxe : x ∈ Subgroup.centralizer {e} := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (commute_frameE h hF x hxK).eq
    rw [← hM_eq]
    exact ⟨hxu, hxe⟩
  exact ⟨ht_sq, hCpu_le_M⟩

private theorem pCore_cpu_conj (P : PCoreFacts hC r)
    (hLG_le_K : pcLG hC r ≤ pcK hC r)
    (hLG_le_H : pcLG hC r ≤ Halpha D hC.alpha)
    (hu_central : hC.d ∈ Subgroup.centralizer (Halpha D hC.alpha : Set G))
    (hPGconj : ∀ k ∈ pcK hC r, ∀ x ∈ pcPG hC r, k * x * k⁻¹ ∈ pcPG hC r)
    (hcomm_le : ⁅pcLG hC r, pcM hC r⁆ ≤ pcLG hC r)
    (hCpu_le_M : pcCpu hC r ≤ pcM hC r) :
    (∀ l ∈ pcLG hC r, ∀ x ∈ pcCpu hC r, l * x * l⁻¹ ∈ pcCpu hC r) ∧
      ⁅pcLG hC r, pcCpu hC r⁆ ≤ pcCpu hC r ∧
        ⁅pcLG hC r, pcCpu hC r⁆ ≤ pcLG hC r := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨huK, heK, htK, hri_mem, hri_comm, htH_mem⟩ := P
  set u : G := hC.d with hu
  set e : G := frameE hC r with he
  set t : G := frameT hC r with ht
  set K : Subgroup G := localGroup D e with hK
  set tH : Halpha D hC.alpha := r 0 * r 1 * r 2 with htH
  set L : Subgroup (Halpha D hC.alpha) := localGroup (DstarH hC) tH with hL
  let LG : Subgroup G := L.map (Halpha D hC.alpha).subtype
  let B : Subgroup G := Halpha D hC.alpha ⊓ Subgroup.centralizer {t}
  let M : Subgroup G := Subgroup.zpowers u ⊔ B
  let PG : Subgroup G := (CFSG.pCore 2 K).map K.subtype
  let Cpu : Subgroup G := Subgroup.centralizer {u} ⊓ PG
  have ht_coe : t = (tH : G) := by rw [ht, htH]; rfl
  have he_def : e = u * t := by rw [he, hu, ht]; rfl
  change (∀ l ∈ LG, ∀ x ∈ Cpu, l * x * l⁻¹ ∈ Cpu) ∧
      ⁅LG, Cpu⁆ ≤ Cpu ∧ ⁅LG, Cpu⁆ ≤ LG
  have hCpu_inv : ∀ l ∈ LG, ∀ x ∈ Cpu, l * x * l⁻¹ ∈ Cpu := by
    intro l hl x hx
    have hlK : l ∈ K := hLG_le_K hl
    have hlH : l ∈ Halpha D hC.alpha := hLG_le_H hl
    refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_, hPGconj l hlK x hx.2⟩
    have hxu : x * u = u * x := Subgroup.mem_centralizer_singleton_iff.mp hx.1
    have hlu : Commute l u := Subgroup.mem_centralizer_iff.mp hu_central l hlH
    calc (l * x * l⁻¹) * u = l * x * (l⁻¹ * u) := by group
      _ = l * x * (u * l⁻¹) := by rw [hlu.inv_left.eq]
      _ = l * (x * u) * l⁻¹ := by group
      _ = l * (u * x) * l⁻¹ := by rw [hxu]
      _ = l * u * (x * l⁻¹) := by group
      _ = u * l * (x * l⁻¹) := by rw [hlu.eq]
      _ = u * (l * x * l⁻¹) := by group
  have hLG_le_normalizer_Cpu : LG ≤ Subgroup.normalizer (Cpu : Set G) :=
    Subgroup.le_normalizer_iff.mpr hCpu_inv
  have hcommCpu_le_Cpu : ⁅LG, Cpu⁆ ≤ Cpu :=
    Subgroup.le_normalizer_iff_commutator_le_right.mp hLG_le_normalizer_Cpu
  have hcommCpu_le_LG : ⁅LG, Cpu⁆ ≤ LG :=
    (Subgroup.commutator_mono le_rfl hCpu_le_M).trans hcomm_le
  exact ⟨hCpu_inv, hcommCpu_le_Cpu, hcommCpu_le_LG⟩

private theorem pCore_LG_inf_Cpu_le_zpowers_t (P : PCoreFacts hC r)
    [(Subgroup.zpowers (⟨pcTH hC r, P.htH_mem⟩ : pcL hC r)).Normal]
    (hCpu_inv : ∀ l ∈ pcLG hC r, ∀ x ∈ pcCpu hC r, l * x * l⁻¹ ∈ pcCpu hC r)
    (hPGp : IsPGroup 2 (pcPG hC r))
    (hsimple : IsSimpleGroup (pcL hC r ⧸
      Subgroup.zpowers (⟨pcTH hC r, P.htH_mem⟩ : pcL hC r)))
    (hnotp : ¬ IsPGroup 2 (pcL hC r ⧸
      Subgroup.zpowers (⟨pcTH hC r, P.htH_mem⟩ : pcL hC r))) :
    pcLG hC r ⊓ pcCpu hC r ≤ Subgroup.zpowers (frameT hC r) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨huK, heK, htK, hri_mem, hri_comm, htH_mem⟩ := P
  set u : G := hC.d with hu
  set e : G := frameE hC r with he
  set t : G := frameT hC r with ht
  set K : Subgroup G := localGroup D e with hK
  set tH : Halpha D hC.alpha := r 0 * r 1 * r 2 with htH
  set L : Subgroup (Halpha D hC.alpha) := localGroup (DstarH hC) tH with hL
  let LG : Subgroup G := L.map (Halpha D hC.alpha).subtype
  let B : Subgroup G := Halpha D hC.alpha ⊓ Subgroup.centralizer {t}
  let M : Subgroup G := Subgroup.zpowers u ⊔ B
  let PG : Subgroup G := (CFSG.pCore 2 K).map K.subtype
  let Cpu : Subgroup G := Subgroup.centralizer {u} ⊓ PG
  have ht_coe : t = (tH : G) := by rw [ht, htH]; rfl
  have he_def : e = u * t := by rw [he, hu, ht]; rfl
  change LG ⊓ Cpu ≤ Subgroup.zpowers t
  have hLGinfCpu_le_t : LG ⊓ Cpu ≤ Subgroup.zpowers t := by
    let R : Subgroup G := LG ⊓ Cpu
    have hR_inv : ∀ g ∈ LG, ∀ y ∈ R, g * y * g⁻¹ ∈ R := by
      intro g hg y hy
      exact ⟨LG.mul_mem (LG.mul_mem hg hy.1) (LG.inv_mem hg),
        hCpu_inv g hg y hy.2⟩
    let eLH : L ≃* LG := Subgroup.equivMapOfInjective L (Halpha D hC.alpha).subtype
      Subtype.val_injective
    let f : L →* G := LG.subtype.comp eLH.toMonoidHom
    have hf_inj : Function.Injective f := Subtype.val_injective.comp eLH.injective
    let R' : Subgroup L := R.comap f
    have hR'_norm : R'.Normal := by
      constructor
      intro r hr l
      change f (l * r * l⁻¹) ∈ R
      rw [map_mul, map_mul, map_inv]
      exact hR_inv (eLH l) (eLH l).2 (eLH r) hr
    have hRp : IsPGroup 2 R := hPGp.to_le (le_trans inf_le_right inf_le_right)
    have hR'_le : R'.map L.subtype ≤ Subgroup.zpowers tH :=
      map_le_zpowers_of_normal_isPGroup L tH htH_mem hsimple hnotp R' hR'_norm
        (hRp.comap_of_injective f hf_inj)
    have hR_eq : (R'.map L.subtype).map (Halpha D hC.alpha).subtype = R := by
      refine le_antisymm ?_ ?_
      · rintro x ⟨h, hh, rfl⟩
        obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hh
        have hmem : f r ∈ R := hr
        change (r : G) ∈ R at hmem
        exact hmem
      · intro x hx
        have hxLG : x ∈ LG := hx.1
        change x ∈ L.map (Halpha D hC.alpha).subtype at hxLG
        obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hxLG
        refine Subgroup.mem_map.mpr ⟨r, Subgroup.mem_map.mpr ⟨⟨r, hr⟩, ?_, rfl⟩, rfl⟩
        change (r : G) ∈ R
        exact hx
    calc R = (R'.map L.subtype).map (Halpha D hC.alpha).subtype := hR_eq.symm
      _ ≤ (Subgroup.zpowers tH).map (Halpha D hC.alpha).subtype := Subgroup.map_mono hR'_le
      _ = Subgroup.zpowers t := by
          rw [MonoidHom.map_zpowers, ht_coe]
          rfl
  exact hLGinfCpu_le_t

private theorem pCore_sq_pg_facts (h : ElevenTwoHyp hC) (hF : ElevenTwoFrame hC S T r)
    (P : PCoreFacts hC r)
    (hu_not_mem_P : (⟨hC.d, P.huK⟩ : pcK hC r) ∉ CFSG.pCore 2 (pcK hC r))
    (ht_sq : frameT hC r * frameT hC r = 1)
    (hcommCpu_le_Cpu : ⁅pcLG hC r, pcCpu hC r⁆ ≤ pcCpu hC r)
    (hcommCpu_le_LG : ⁅pcLG hC r, pcCpu hC r⁆ ≤ pcLG hC r)
    (hLGinfCpu_le_t : pcLG hC r ⊓ pcCpu hC r ≤ Subgroup.zpowers (frameT hC r)) :
    hC.d * hC.d = 1 ∧ frameE hC r ∈ pcPG hC r ∧ hC.d ∉ pcPG hC r ∧
      frameT hC r ∉ pcPG hC r ∧
        pcCpu hC r ≤ Subgroup.centralizer (pcLG hC r : Set G) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨huK, heK, htK, hri_mem, hri_comm, htH_mem⟩ := P
  set u : G := hC.d with hu
  set e : G := frameE hC r with he
  set t : G := frameT hC r with ht
  set K : Subgroup G := localGroup D e with hK
  set tH : Halpha D hC.alpha := r 0 * r 1 * r 2 with htH
  set L : Subgroup (Halpha D hC.alpha) := localGroup (DstarH hC) tH with hL
  let LG : Subgroup G := L.map (Halpha D hC.alpha).subtype
  let B : Subgroup G := Halpha D hC.alpha ⊓ Subgroup.centralizer {t}
  let M : Subgroup G := Subgroup.zpowers u ⊔ B
  let PG : Subgroup G := (CFSG.pCore 2 K).map K.subtype
  let Cpu : Subgroup G := Subgroup.centralizer {u} ⊓ PG
  have ht_coe : t = (tH : G) := by rw [ht, htH]; rfl
  have he_def : e = u * t := by rw [he, hu, ht]; rfl
  change u * u = 1 ∧ e ∈ PG ∧ u ∉ PG ∧ t ∉ PG ∧
      Cpu ≤ Subgroup.centralizer (LG : Set G)
  have hu_sq : u * u = 1 := by
    rw [hu]
    exact hC.setup.oddT.mul_self_eq_one hC.hd
  have he_P : (⟨e, heK⟩ : K) ∈ CFSG.pCore 2 K := by
    have hcen : (⟨e, heK⟩ : K) ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      exact (commute_frameE h hF g g.2).eq
    have he_sq : e * e = 1 := by
      have h : orderOf e ∣ 2 := by rw [orderOf_frameE h hF]
      rwa [orderOf_dvd_iff_pow_eq_one, pow_two] at h
    have hee : (⟨e, heK⟩ : K) * ⟨e, heK⟩ = 1 := Subtype.ext he_sq
    have hmem : Subgroup.zpowers (⟨e, heK⟩ : K) ∈
        {K : Subgroup K | K.Normal ∧ IsPGroup 2 K} :=
      ⟨Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hcen),
        IsPGroup.of_card_dvd_pow (n := 1) (by
          rw [Nat.card_zpowers]
          exact orderOf_dvd_iff_pow_eq_one.mpr (by simpa [pow_two] using hee))⟩
    exact (le_sSup hmem) (Subgroup.mem_zpowers _)
  have he_PG : e ∈ PG := by
    change e ∈ (CFSG.pCore 2 K).map K.subtype
    have hex : ∃ y : K, y ∈ CFSG.pCore 2 K ∧ (Subgroup.subtype K) y = e :=
      Exists.intro (⟨e, heK⟩ : K) (And.intro he_P rfl)
    exact Subgroup.mem_map.mpr hex
  have ht_not_mem_P : (⟨t, htK⟩ : K) ∉ CFSG.pCore 2 K := by
    intro htP
    apply hu_not_mem_P
    have hprod : (⟨u, huK⟩ : K) = ⟨e, heK⟩ * ⟨t, htK⟩ := by
      apply Subtype.ext
      show u = e * t
      rw [he_def, mul_assoc, ht_sq, mul_one]
    rw [hprod]
    exact (CFSG.pCore 2 K).mul_mem he_P htP
  have hu_not_mem_PG : u ∉ PG := by
    intro huPG
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp huPG
    exact hu_not_mem_P (by rwa [show y = ⟨u, huK⟩ from Subtype.ext hyx] at hy)
  have ht_not_mem_PG : t ∉ PG := by
    intro htPG
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp htPG
    exact ht_not_mem_P (by rwa [show y = ⟨t, htK⟩ from Subtype.ext hyx] at hy)
  have hcommCpu_le_t : ⁅LG, Cpu⁆ ≤ Subgroup.zpowers t :=
    (le_inf hcommCpu_le_LG hcommCpu_le_Cpu).trans hLGinfCpu_le_t
  have hcommCpu_eq_bot : ⁅LG, Cpu⁆ = ⊥ := by
    by_contra hne
    obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    have hxt : (x : G) = t := by
      rcases (mem_zpowers_of_mul_self ht_sq).mp (hcommCpu_le_t x.2) with h | h
      · exact absurd (Subtype.ext h) hx1
      · exact h
    have ht_mem : t ∈ Cpu := hxt ▸ hcommCpu_le_Cpu x.2
    exact ht_not_mem_PG ht_mem.2
  have hCpu_le_cent_LG : Cpu ≤ Subgroup.centralizer (LG : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).mp
      (by rw [Subgroup.commutator_comm]; exact hcommCpu_eq_bot)
  exact ⟨hu_sq, he_PG, hu_not_mem_PG, ht_not_mem_PG, hCpu_le_cent_LG⟩

private theorem pCore_M_decomposition (P : PCoreFacts hC r)
    (hu_central : hC.d ∈ Subgroup.centralizer (Halpha D hC.alpha : Set G)) :
    ∀ x ∈ pcM hC r, ∃ a ∈ Subgroup.zpowers hC.d, ∃ b ∈ pcB hC r, a * b = x := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨huK, heK, htK, hri_mem, hri_comm, htH_mem⟩ := P
  set u : G := hC.d with hu
  set e : G := frameE hC r with he
  set t : G := frameT hC r with ht
  set K : Subgroup G := localGroup D e with hK
  set tH : Halpha D hC.alpha := r 0 * r 1 * r 2 with htH
  set L : Subgroup (Halpha D hC.alpha) := localGroup (DstarH hC) tH with hL
  let LG : Subgroup G := L.map (Halpha D hC.alpha).subtype
  let B : Subgroup G := Halpha D hC.alpha ⊓ Subgroup.centralizer {t}
  let M : Subgroup G := Subgroup.zpowers u ⊔ B
  let PG : Subgroup G := (CFSG.pCore 2 K).map K.subtype
  let Cpu : Subgroup G := Subgroup.centralizer {u} ⊓ PG
  have ht_coe : t = (tH : G) := by rw [ht, htH]; rfl
  have he_def : e = u * t := by rw [he, hu, ht]; rfl
  change ∀ x ∈ M, ∃ a ∈ Subgroup.zpowers u, ∃ b ∈ B, a * b = x
  have hB_le_Cu : B ≤ Subgroup.centralizer ({u} : Set G) := by
    intro b hb
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hu_central b hb.1)
  have hM_le_Cu : M ≤ Subgroup.centralizer ({u} : Set G) := by
    change Subgroup.zpowers u ⊔ B ≤ Subgroup.centralizer ({u} : Set G)
    exact sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr
      (Commute.refl u).eq)) hB_le_Cu
  have hdecomp : ∀ x ∈ M, ∃ a ∈ Subgroup.zpowers u, ∃ b ∈ B, a * b = x := by
    intro x hxM
    have hA_M_normal : ((Subgroup.zpowers u).subgroupOf M).Normal := by
      refine Subgroup.normal_of_le_center ?_
      intro z hz
      rw [Subgroup.mem_center_iff]
      intro g
      have hz' : (z : G) ∈ Subgroup.zpowers u := hz
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz'
      have hgu : Commute (g : G) u :=
        Subgroup.mem_centralizer_singleton_iff.mp (hM_le_Cu g.2)
      have hcomm : Commute (z : G) (g : G) := by
        rw [← hk]
        exact Commute.zpow_left hgu.symm k
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      exact hcomm.symm.eq
    have hsup : (Subgroup.zpowers u ⊔ B).subgroupOf M =
        (Subgroup.zpowers u).subgroupOf M ⊔ B.subgroupOf M :=
      Subgroup.subgroupOf_sup (le_sup_left : Subgroup.zpowers u ≤ M)
        (le_sup_right : B ≤ M)
    have htop : (⟨x, hxM⟩ : M) ∈ (Subgroup.zpowers u).subgroupOf M ⊔ B.subgroupOf M := by
      rw [← hsup, Subgroup.mem_subgroupOf]
      exact hxM
    obtain ⟨a, ha, b, hb, hab⟩ := (Subgroup.mem_sup_of_normal_left
      (s := (Subgroup.zpowers u).subgroupOf M) (t := B.subgroupOf M)).mp htop
    exact ⟨(a : G), ha, (b : G), hb, by simpa using congrArg Subtype.val hab⟩
  exact hdecomp

private theorem pCore_Cpu_le_zpowers_e (h : ElevenTwoHyp hC) (hF : ElevenTwoFrame hC S T r)
    (P : PCoreFacts hC r)
    (hdecomp : ∀ x ∈ pcM hC r, ∃ a ∈ Subgroup.zpowers hC.d, ∃ b ∈ pcB hC r, a * b = x)
    (hCpu_le_M : pcCpu hC r ≤ pcM hC r)
    (hCpu_le_cent_LG : pcCpu hC r ≤ Subgroup.centralizer (pcLG hC r : Set G))
    (hu_central : hC.d ∈ Subgroup.centralizer (Halpha D hC.alpha : Set G))
    (ht_not_mem_PG : frameT hC r ∉ pcPG hC r)
    (hu_not_mem_PG : hC.d ∉ pcPG hC r)
    (ht_sq : frameT hC r * frameT hC r = 1)
    (hu_sq : hC.d * hC.d = 1) :
    pcCpu hC r ≤ Subgroup.zpowers (frameE hC r) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨huK, heK, htK, hri_mem, hri_comm, htH_mem⟩ := P
  set u : G := hC.d with hu
  set e : G := frameE hC r with he
  set t : G := frameT hC r with ht
  set K : Subgroup G := localGroup D e with hK
  set tH : Halpha D hC.alpha := r 0 * r 1 * r 2 with htH
  set L : Subgroup (Halpha D hC.alpha) := localGroup (DstarH hC) tH with hL
  let LG : Subgroup G := L.map (Halpha D hC.alpha).subtype
  let B : Subgroup G := Halpha D hC.alpha ⊓ Subgroup.centralizer {t}
  let M : Subgroup G := Subgroup.zpowers u ⊔ B
  let PG : Subgroup G := (CFSG.pCore 2 K).map K.subtype
  let Cpu : Subgroup G := Subgroup.centralizer {u} ⊓ PG
  have ht_coe : t = (tH : G) := by rw [ht, htH]; rfl
  have he_def : e = u * t := by rw [he, hu, ht]; rfl
  change Cpu ≤ Subgroup.zpowers e
  have hCpu_le_zpowers_e : Cpu ≤ Subgroup.zpowers e := by
    intro x hx
    obtain ⟨a, ha, b, hb, hab⟩ := hdecomp x (hCpu_le_M hx)
    have hb_comm : ∀ y ∈ centSet (DstarH hC) tH, Commute b y := by
      intro y hy
      have hyLG : (y : G) ∈ LG :=
        Subgroup.mem_map.mpr ⟨y, Subgroup.subset_closure hy, rfl⟩
      have hxl : Commute x (y : G) :=
        (Subgroup.mem_centralizer_iff.mp (hCpu_le_cent_LG hx) (y : G) hyLG).symm
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ha
      have hal : Commute (a : G) (y : G) := by
        rw [← hk]
        exact Commute.zpow_left
          ((Subgroup.mem_centralizer_iff.mp hu_central (y : G) y.2).symm) k
      have hb_eq : b = (a : G)⁻¹ * x := by
        rw [← hab]
        group
      rw [hb_eq]
      exact Commute.mul_left (Commute.inv_left hal) hxl
    have hb_t : (b : G) ∈ Subgroup.zpowers t := by
      rcases hF.frame.centralizer (⟨b, hb.1⟩ : Halpha D hC.alpha)
        (fun y hy => by
          apply Subtype.ext
          exact (hb_comm y hy).eq) with h1 | h1
      · have hb1 : b = 1 := congrArg (fun z : Halpha D hC.alpha => (z : G)) h1
        rw [hb1]
        exact Subgroup.one_mem _
      · have hbt : b = t := by
          rw [ht_coe]
          exact congrArg (fun z : Halpha D hC.alpha => (z : G)) h1
        rw [hbt]
        exact Subgroup.mem_zpowers _
    have hx_ut : x ∈ Subgroup.zpowers u ⊔ Subgroup.zpowers t := by
      rw [← hab]
      exact Subgroup.mul_mem_sup ha hb_t
    have hxP : x ∈ PG := hx.2
    have ha_cases : a = 1 ∨ a = u := (mem_zpowers_of_mul_self hu_sq).mp ha
    have hb_cases : (b : G) = 1 ∨ (b : G) = t := by
      rcases (mem_zpowers_of_mul_self ht_sq).mp hb_t with h | h
      · exact Or.inl h
      · exact Or.inr h
    rcases ha_cases with ha1 | ha1
    · rcases hb_cases with hb1 | hb1
      · rw [show x = 1 by rw [← hab, ha1, hb1, one_mul]]
        exact Subgroup.one_mem _
      · exfalso
        apply ht_not_mem_PG
        rw [← show x = t by rw [← hab, ha1, hb1, one_mul]]
        exact hxP
    · rcases hb_cases with hb1 | hb1
      · exfalso
        apply hu_not_mem_PG
        rw [← show x = u by rw [← hab, ha1, hb1, mul_one]]
        exact hxP
      · rw [show x = e by rw [← hab, ha1, hb1, ← he_def]]
        exact Subgroup.mem_zpowers _
  exact hCpu_le_zpowers_e

private theorem pCore_PG_le_zpowers_e (h : ElevenTwoHyp hC) (hF : ElevenTwoFrame hC S T r)
    (P : PCoreFacts hC r)
    (hu_central : hC.d ∈ Subgroup.centralizer (Halpha D hC.alpha : Set G))
    (hPGconj : ∀ k ∈ pcK hC r, ∀ x ∈ pcPG hC r, k * x * k⁻¹ ∈ pcPG hC r)
    (hPGp : IsPGroup 2 (pcPG hC r))
    (hu_sq : hC.d * hC.d = 1)
    (hCpu_le_zpowers_e : pcCpu hC r ≤ Subgroup.zpowers (frameE hC r))
    (ht_sq : frameT hC r * frameT hC r = 1) :
    pcPG hC r ≤ Subgroup.zpowers (frameE hC r) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨huK, heK, htK, hri_mem, hri_comm, htH_mem⟩ := P
  set u : G := hC.d with hu
  set e : G := frameE hC r with he
  set t : G := frameT hC r with ht
  set K : Subgroup G := localGroup D e with hK
  set tH : Halpha D hC.alpha := r 0 * r 1 * r 2 with htH
  set L : Subgroup (Halpha D hC.alpha) := localGroup (DstarH hC) tH with hL
  let LG : Subgroup G := L.map (Halpha D hC.alpha).subtype
  let B : Subgroup G := Halpha D hC.alpha ⊓ Subgroup.centralizer {t}
  let M : Subgroup G := Subgroup.zpowers u ⊔ B
  let PG : Subgroup G := (CFSG.pCore 2 K).map K.subtype
  let Cpu : Subgroup G := Subgroup.centralizer {u} ⊓ PG
  have ht_coe : t = (tH : G) := by rw [ht, htH]; rfl
  have he_def : e = u * t := by rw [he, hu, ht]; rfl
  change PG ≤ Subgroup.zpowers e
  have htH_H : t ∈ Halpha D hC.alpha := by rw [ht_coe]; exact tH.2
  have hut : Commute u t := (Subgroup.mem_centralizer_iff.mp hu_central t htH_H).symm
  have hPG_le_zpowers_e : PG ≤ Subgroup.zpowers e := by
    intro x hxPG
    have hxK : x ∈ K := Subgroup.map_subtype_le (CFSG.pCore 2 K) hxPG
    set a : G := x * u * x⁻¹ with hadef
    have haD : a ∈ D := by
      rw [hadef]
      exact hC.setup.normal x hC.d hC.hd
    have haPG : a * u ∈ PG := by
      have hxu : x * u * x⁻¹ * u = x * (u * x⁻¹ * u) := by group
      rw [hadef, hxu]
      refine PG.mul_mem hxPG ?_
      have h := hPGconj u huK x⁻¹ (PG.inv_mem hxPG)
      rwa [show u⁻¹ = u from inv_eq_of_mul_eq_one_right hu_sq] at h
    have ha_comm : Commute a u := by
      by_contra hnc
      have hodd : Odd (orderOf (a * u)) := hC.setup.oddT.odd_of_not_commute haD hC.hd hnc
      have h1 : a * u = 1 :=
        CFSG.Timmesfeld.Bridge.OddTransp.eq_one_of_isPGroup_of_odd hPGp haPG hodd
      have hau : a = u := by
        have h := congrArg (fun z : G => z * u) h1
        simpa [mul_assoc, hu_sq] using h
      exact hnc (by rw [hau])
    have ha_mem_Cpu : a * u ∈ Cpu :=
      ⟨Subgroup.mem_centralizer_singleton_iff.mpr
        (ha_comm.mul_left (Commute.refl u)).eq, haPG⟩
    by_cases hau : a = u
    · have hxCu : x ∈ Subgroup.centralizer {u} := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        have h := congrArg (fun z : G => z * x) hau
        rw [hadef] at h
        simpa [mul_assoc] using h
      exact hCpu_le_zpowers_e ⟨hxCu, hxPG⟩
    · exfalso
      have he_sq' : e * e = 1 := by
        rw [he_def]
        calc u * t * (u * t) = u * (t * u) * t := by group
          _ = u * (u * t) * t := by rw [hut.eq]
          _ = u * u * (t * t) := by group
          _ = 1 := by rw [hu_sq, ht_sq, mul_one]
      have h1 : a * u = e := by
        rcases (mem_zpowers_of_mul_self he_sq').mp (hCpu_le_zpowers_e ha_mem_Cpu) with h | h
        · exfalso
          apply hau
          have h2 := congrArg (fun z : G => z * u) h
          simpa [mul_assoc, hu_sq] using h2
        · exact h
      have h3 : a = t := by
        calc a = a * u * u := by rw [mul_assoc, hu_sq, mul_one]
          _ = e * u := by rw [h1]
          _ = t := by
            rw [he_def]
            rw [hut.eq, mul_assoc, hu_sq, mul_one]
      have hnot : t ∉ D := by rw [ht]; exact frameT_not_mem h hF
      exact hnot (h3 ▸ haD)
  exact hPG_le_zpowers_e

theorem pCore_localGroup (h : ElevenTwoHyp hC) (hF : ElevenTwoFrame hC S T r) :
    (CFSG.pCore 2 (localGroup D (frameE hC r))).map (localGroup D (frameE hC r)).subtype =
      Subgroup.zpowers (frameE hC r) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set u : G := hC.d with hu
  set e : G := frameE hC r with he
  set t : G := frameT hC r with ht
  set K : Subgroup G := localGroup D e with hK
  set tH : Halpha D hC.alpha := r 0 * r 1 * r 2 with htH
  set L : Subgroup (Halpha D hC.alpha) := localGroup (DstarH hC) tH with hL
  have ht_coe : t = (tH : G) := by rw [ht, htH]; rfl
  have he_def : e = u * t := by rw [he, hu, ht]; rfl
  have huK : u ∈ K := by
    rw [hK, he, hu]
    exact mem_localGroup_of_mem (d_mem_centSet h hF)
  have heK : e ∈ K := by
    rw [hK, he]
    exact frameE_mem_localGroup h hF
  have hriK : ∀ i, ((r i : Halpha D hC.alpha) : G) ∈ K := by
    intro i
    rw [hK, he]
    exact mem_localGroup_of_mem (mem_centSet h hF i)
  have htK : t ∈ K := by
    rw [ht]
    have hmul := K.mul_mem (K.mul_mem (hriK 0) (hriK 1)) (hriK 2)
    simpa [frameT] using hmul
  have hri_mem : ∀ i, r i ∈ DstarH hC := by
    intro i
    have hmem : r i ∈ Set.range r := ⟨i, rfl⟩
    rw [← hF.frame.inter_eq] at hmem
    exact hmem.2
  have hri_comm : ∀ i, Commute (r i) tH := by
    intro i
    rw [htH]
    exact ((hF.frame.commute i 0).mul_right (hF.frame.commute i 1)).mul_right
      (hF.frame.commute i 2)
  have htH_mem : tH ∈ L := by
    have h0 : r 0 ∈ L := Subgroup.subset_closure ⟨hri_mem 0, hri_comm 0⟩
    have h1 : r 1 ∈ L := Subgroup.subset_closure ⟨hri_mem 1, hri_comm 1⟩
    have h2 : r 2 ∈ L := Subgroup.subset_closure ⟨hri_mem 2, hri_comm 2⟩
    have hmul := L.mul_mem (L.mul_mem h0 h1) h2
    rwa [htH]
  have htH_center : (⟨tH, htH_mem⟩ : L) ∈ Subgroup.center L := by
    rw [Subgroup.mem_center_iff]
    intro x
    apply Subtype.ext
    show (x : Halpha D hC.alpha) * tH = tH * (x : Halpha D hC.alpha)
    exact (CFSG.Timmesfeld.commute_of_mem_closure (S := ({tH} : Set _))
      (S' := centSet (DstarH hC) tH)
      (fun a ha b hb => by rw [Set.mem_singleton_iff.mp ha]; exact hb.2.symm)
      (Subgroup.subset_closure (Set.mem_singleton tH)) x.2).eq.symm
  have hcenter_eq : Subgroup.center L = Subgroup.zpowers (⟨tH, htH_mem⟩ : L) := by
    refine le_antisymm ?_ (Subgroup.zpowers_le.mpr htH_center)
    intro z hz
    have hz' : (z : Halpha D hC.alpha) = 1 ∨ (z : Halpha D hC.alpha) = tH := by
      refine hF.frame.centralizer z ?_
      intro y hy
      have hyL : y ∈ L := Subgroup.subset_closure hy
      have hcomm := Subgroup.mem_center_iff.mp hz ⟨y, hyL⟩
      exact (Subtype.ext_iff.mp hcomm).symm
    rcases hz' with h1 | h1
    · have : z = 1 := Subtype.ext h1
      rw [this]
      exact Subgroup.one_mem _
    · have : z = ⟨tH, htH_mem⟩ := Subtype.ext h1
      rw [this]
      exact Subgroup.mem_zpowers _
  haveI hzp_norm : (Subgroup.zpowers (⟨tH, htH_mem⟩ : L)).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr htH_center)
  obtain ⟨eL⟩ := hF.frame.bender
  let eL' : L ⧸ Subgroup.zpowers (⟨tH, htH_mem⟩ : L) ≃* CFSG.Theory.Comparator.PSL2Model 2 :=
    (QuotientGroup.quotientMulEquivOfEq hcenter_eq).symm.trans eL
  have hsimple : IsSimpleGroup (L ⧸ Subgroup.zpowers (⟨tH, htH_mem⟩ : L)) :=
    CFSG.CGT.Timmesfeld75.isSimpleGroup_of_psl2 (f := 2) (by norm_num) eL'
  have hcard_q : Nat.card (L ⧸ Subgroup.zpowers (⟨tH, htH_mem⟩ : L)) = 60 := by
    rw [Nat.card_congr eL'.toEquiv,
      CFSG.Timmesfeld.Bridge.OddTransp.card_psl2Model (m := 2) (by norm_num)]
    norm_num
  have hnotp : ¬ IsPGroup 2 (L ⧸ Subgroup.zpowers (⟨tH, htH_mem⟩ : L)) := by
    intro hp
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hp
    rw [hcard_q] at hn
    have hle : n ≤ 5 := by
      by_contra hcon
      push Not at hcon
      have h6 : 2 ^ 6 ≤ 2 ^ n := pow_le_pow_right' (by norm_num) (by omega)
      omega
    interval_cases n <;> norm_num at hn
  let P : PCoreFacts hC r :=
    { huK := huK, heK := heK, htK := htK, hri_mem := hri_mem,
      hri_comm := hri_comm, htH_mem := htH_mem }
  obtain ⟨hLG_le_H, hLG_le_K, hu_central, hcomm_le⟩ := pCore_frame_normalizers P
  obtain ⟨hPGp, hPGconj, hu_not_mem_P⟩ := pCore_pCore_map h hF P hLG_le_K hnotp
  obtain ⟨ht_sq, hCpu_le_M⟩ := pCore_frameT_sq_and_cpu_le_M h hF P
  obtain ⟨hCpu_inv, hcommCpu_le_Cpu, hcommCpu_le_LG⟩ :=
    pCore_cpu_conj P hLG_le_K hLG_le_H hu_central hPGconj hcomm_le hCpu_le_M
  have hLGinfCpu_le_t :=
    pCore_LG_inf_Cpu_le_zpowers_t P hCpu_inv hPGp hsimple hnotp
  obtain ⟨hu_sq, he_PG, hu_not_mem_PG, ht_not_mem_PG, hCpu_le_cent_LG⟩ :=
    pCore_sq_pg_facts h hF P hu_not_mem_P ht_sq hcommCpu_le_Cpu hcommCpu_le_LG
      hLGinfCpu_le_t
  have hdecomp := pCore_M_decomposition P hu_central
  have hCpu_le_zpowers_e :=
    pCore_Cpu_le_zpowers_e h hF P hdecomp hCpu_le_M hCpu_le_cent_LG hu_central
      ht_not_mem_PG hu_not_mem_PG ht_sq hu_sq
  have hPG_le_zpowers_e :=
    pCore_PG_le_zpowers_e h hF P hu_central hPGconj hPGp hu_sq hCpu_le_zpowers_e ht_sq
  exact le_antisymm hPG_le_zpowers_e (Subgroup.zpowers_le.mpr he_PG)

end ElevenTwoFrame

end KPCore

end CFSG.OddTranspositions.PartThree
