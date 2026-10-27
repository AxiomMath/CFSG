module

public import CFSG.RankThree.PartTwo.Sec11.Item1120V0BarFam
public import CFSG.RankThree.PartTwo.Sec11.Item1120V0BarTau
public import CFSG.RankThree.PartTwo.Sec11.Item1120V0BarLocal
public import CFSG.RankThree.PartTwo.Sec11.Item1119StepsProof
import CFSG.RankThree.PartTwo.Sec11.Item1115NotFieldProof
import CFSG.RankThree.PartTwo.Sec11.Item1117Res3ProofModel
import CFSG.RankThree.PartTwo.Sec11.KS11LieProofCentCore
public import CFSG.RankThree.PartTwo.Sec11.DataExistsR
public import CFSG.RankThree.PartTwo.Sec11.Item1115Proof
public import CFSG.RankThree.PartTwo.Sec11.Item119K

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)

namespace Item1120V0Bar


variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d x s r g : G}

theorem thetaAut_mem_imgJ (h : Sec11Std G A c L a R Y) {w : G}
    (hwL : w ∈ Subgroup.normalizer (L : Set G)) (hwa : w * a = a * w)
    (hwY : w ∈ Subgroup.normalizer (Y : Set G)) {j : Y ⧸ aschbacherSolvableCore 3 Y}
    (hj : j ∈ imgJ Y L a) : Sec4.Item426.thetaAut Y hwY j ∈ imgJ Y L a := by
  have hwN : w ∈ Subgroup.normalizer (sec11K L a : Set G) :=
    GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_perfectResidual _
      (GroupTheory.SteinbergBY.mem_normalizer_inf hwL
        (Subgroup.le_normalizer (Subgroup.mem_centralizer_singleton_iff.mpr hwa)))
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hj
  have hk : w * (x : G) * w⁻¹ ∈ sec11K L a :=
    (Subgroup.mem_normalizer_iff.mp hwN (x : G)).mp (Subgroup.mem_subgroupOf.mp hx)
  have hact : Sec4.Item426.thetaAut Y hwY (QuotientGroup.mk' (aschbacherSolvableCore 3 Y) x) =
      QuotientGroup.mk' (aschbacherSolvableCore 3 Y) (Sec4.compAction Y ⟨w, hwY⟩ x) :=
    Sec4.Item426.thetaAut_mk Y hwY x
  rw [hact]
  refine Subgroup.mem_map_of_mem (QuotientGroup.mk' (aschbacherSolvableCore 3 Y))
    (Subgroup.mem_subgroupOf.mpr ?_)
  rw [Sec4.Item426.coe_compAction_apply]
  exact hk

theorem thetaAut_s_mem_theta_imgJ (h45 : Sec4.Item4_5) (h : Sec11Data G A c L a R Y d x s r g)
    (hsN : s ∈ Subgroup.normalizer (Y : Set G)) (hsa : s * a = a * s)
    {j : Y ⧸ aschbacherSolvableCore 3 Y}
    (hj : j ∈ imgJ Y L a) :
    j⁻¹ * Sec4.Item426.thetaAut Y hsN j ∈
      inSubgroup (aschbacherSolvableCore 3) (imgJ Y L a) := by
  have hsR : s ∈ R := (Item1116Proof.mem_R h).2.2
  have hsL : s ∈ Subgroup.normalizer (L : Set G) :=
    (Item1116Proof.le_centralizer_and_normalizer h45 h).2 hsR
  have hsC : s ∈ Sec4.thetaQuotCentralizer L := by
    have h1 : s ∈ Subgroup.zpowers s := Subgroup.mem_zpowers s
    rw [← h.inf_centralizer_eq] at h1
    exact h1.2
  have hsθ : ∀ l ∈ L, l⁻¹ * (s * l * s⁻¹) ∈ inSubgroup (aschbacherSolvableCore 3) L :=
    (Sec6.mem_thetaQuotCentralizer_iff.mp hsC).2
  have hsK : s ∈ Subgroup.normalizer (sec11K L a : Set G) :=
    GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_perfectResidual _
      (GroupTheory.SteinbergBY.mem_normalizer_inf hsL
        (Subgroup.le_normalizer (Subgroup.mem_centralizer_singleton_iff.mpr hsa)))
  have hKY : sec11K L a ≤ Y := h.sec11K_le
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hj
  have hky : (y : G) ∈ sec11K L a := Subgroup.mem_subgroupOf.mp hy
  have hyL : (y : G) ∈ L := sec11K_le L a hky
  obtain ⟨z, hz⟩ : ∃ z : G, z = (y : G)⁻¹ * (s * (y : G) * s⁻¹) := ⟨_, rfl⟩
  have hzK : z ∈ sec11K L a := by
    rw [hz]
    exact (sec11K L a).mul_mem ((sec11K L a).inv_mem hky)
      ((Subgroup.mem_normalizer_iff.mp hsK (y : G)).mp hky)
  have hzY : z ∈ Y := hKY hzK
  have hzθL : z ∈ inSubgroup (aschbacherSolvableCore 3) L := by
    rw [hz]
    exact hsθ _ hyL
  have hzθK : z ∈ inSubgroup (aschbacherSolvableCore 3) (sec11K L a) :=
    Sec13.inf_inSubgroup_theta_le (sec11K_le L a) ⟨hzK, hzθL⟩
  have hkey : (QuotientGroup.mk' (aschbacherSolvableCore 3 Y) y)⁻¹ *
      Sec4.Item426.thetaAut Y hsN (QuotientGroup.mk' (aschbacherSolvableCore 3 Y) y) =
        QuotientGroup.mk' (aschbacherSolvableCore 3 Y) ⟨z, hzY⟩ := by
    have e : Sec4.Item426.thetaAut Y hsN (QuotientGroup.mk' (aschbacherSolvableCore 3 Y) y) =
        QuotientGroup.mk' (aschbacherSolvableCore 3 Y) (Sec4.compAction Y ⟨s, hsN⟩ y) := rfl
    rw [e, ← map_inv, ← map_mul]
    congr 1
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_inv, Sec4.Item426.coe_compAction_apply]
    exact hz.symm
  let ι : sec11K L a →* Y := Subgroup.inclusion hKY
  let f0 : sec11K L a →* Y ⧸ aschbacherSolvableCore 3 Y :=
    (QuotientGroup.mk' (aschbacherSolvableCore 3 Y)).comp ι
  have hf0 : ∀ k : sec11K L a, f0 k ∈ imgJ Y L a := fun k => by
    refine Subgroup.mem_map.mpr ⟨ι k, Subgroup.mem_subgroupOf.mpr k.2, rfl⟩
  let f : sec11K L a →* imgJ Y L a := f0.codRestrict (imgJ Y L a) hf0
  have hfsurj : Function.Surjective f := by
    rintro ⟨q, hq⟩
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hq
    exact ⟨⟨(l : G), Subgroup.mem_subgroupOf.mp hl⟩, rfl⟩
  have hθK := solvable_prime_complement_core_characterization (H := ↥(sec11K L a)) Nat.prime_three
  haveI : Group.IsSolvable (aschbacherSolvableCore 3 (sec11K L a)) := hθK.1
  have hNnorm : ((aschbacherSolvableCore 3 (sec11K L a)).map f).Normal :=
    Subgroup.Normal.map inferInstance f hfsurj
  let φ : aschbacherSolvableCore 3 (sec11K L a) →*
      ↥((aschbacherSolvableCore 3 (sec11K L a)).map f) :=
    (f.comp (aschbacherSolvableCore 3 (sec11K L a)).subtype).codRestrict _
      (fun x => Subgroup.mem_map_of_mem f x.2)
  have hφs : Function.Surjective φ := by
    rintro ⟨q, hq⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hq
    exact ⟨⟨x, hx⟩, rfl⟩
  have hNsolv : Group.IsSolvable ↥((aschbacherSolvableCore 3 (sec11K L a)).map f) :=
    Group.isSolvable_of_surjective hφs
  have hNp : ¬ 3 ∣ Nat.card ↥((aschbacherSolvableCore 3 (sec11K L a)).map f) := by
    intro h3
    exact hθK.2.2.1 (h3.trans (Subgroup.card_map_dvd _ f))
  have hθJ := solvable_prime_complement_core_characterization
    (H := ↥(imgJ Y L a)) Nat.prime_three
  have hNle : (aschbacherSolvableCore 3 (sec11K L a)).map f ≤
      aschbacherSolvableCore 3 (imgJ Y L a) :=
    hθJ.2.2.2.1 _ hNnorm hNsolv hNp
  have hwJ : QuotientGroup.mk' (aschbacherSolvableCore 3 Y) ⟨z, hzY⟩ ∈ imgJ Y L a :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hzK)
  have hwN : (⟨QuotientGroup.mk' (aschbacherSolvableCore 3 Y) ⟨z, hzY⟩, hwJ⟩ :
      ↥(imgJ Y L a)) ∈ (aschbacherSolvableCore 3 (sec11K L a)).map f := by
    rw [inSubgroup] at hzθK
    obtain ⟨t, ht, htz⟩ := Subgroup.mem_map.mp hzθK
    refine Subgroup.mem_map.mpr ⟨t, ht, ?_⟩
    apply Subtype.ext
    show QuotientGroup.mk' (aschbacherSolvableCore 3 Y) (Subgroup.inclusion hKY t) =
      QuotientGroup.mk' (aschbacherSolvableCore 3 Y) ⟨z, hzY⟩
    congr 1
    exact Subtype.ext htz
  rw [inSubgroup]
  exact Subgroup.mem_map.mpr ⟨_, hNle hwN, hkey.symm⟩

theorem x_cube_mem_imgJ (h45 : Sec4.Item4_5) (h : Sec11Data G A c L a R Y d x s r g)
    (hx3Y : x ^ 3 ∈ Y) :
    QuotientGroup.mk' (aschbacherSolvableCore 3 Y) ⟨x ^ 3, hx3Y⟩ ∈ imgJ Y L a :=
  Subgroup.mem_map_of_mem (QuotientGroup.mk' (aschbacherSolvableCore 3 Y))
    (Subgroup.mem_subgroupOf.mpr (x_cube_mem_sec11K h45 h))

theorem orderOf_mk_x_cube (h : Sec11Data G A c L a R Y d x s r g) (hx3Y : x ^ 3 ∈ Y) :
    orderOf (QuotientGroup.mk' (aschbacherSolvableCore 3 Y) ⟨x ^ 3, hx3Y⟩) = orderOf (x ^ 3) := by
  have hxR : x ∈ R := (Item1116Proof.mem_R h).2.1
  have hx3R : x ^ 3 ∈ R := R.pow_mem hxR 3
  rw [orderOf_eq_orderOf_iff]
  intro n
  rw [← map_pow (QuotientGroup.mk' (aschbacherSolvableCore 3 Y)), QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff]
  constructor
  · intro hn
    have hwY : (x ^ 3) ^ n ∈ Y := Y.pow_mem hx3Y n
    have hw : QuotientGroup.mk' (aschbacherSolvableCore 3 Y) ⟨(x ^ 3) ^ n, hwY⟩ = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hn
    exact Item1117Res3Proof.eq_one_of_mk_eq_one h
      (Item1119Proof.R_le_P R g (R.pow_mem hx3R n)) hwY hw
  · intro hn
    have h1 : (⟨x ^ 3, hx3Y⟩ : Y) ^ n = 1 := Subtype.ext (by simpa using hn)
    rw [h1]
    exact Subgroup.one_mem _

theorem isSylowOf_zpowers_mk_x_cube (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117)
    (h : Sec11Data G A c L a R Y d x s r g) (hx3Y : x ^ 3 ∈ Y) :
    IsSylowOf 3
      (Subgroup.zpowers (QuotientGroup.mk' (aschbacherSolvableCore 3 Y) ⟨x ^ 3, hx3Y⟩))
      (imgJ Y L a) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q, hQ⟩ := isSylowOf_zpowers_x_cube h45 h113 h117 h
  have hKY : sec11K L a ≤ Y := h.sec11K_le
  have hx3K : x ^ 3 ∈ sec11K L a := x_cube_mem_sec11K h45 h
  let ι : sec11K L a →* Y := Subgroup.inclusion hKY
  have hιJ : ∀ k : sec11K L a,
      QuotientGroup.mk' (aschbacherSolvableCore 3 Y) (ι k) ∈ imgJ Y L a := fun k =>
    Subgroup.mem_map_of_mem (QuotientGroup.mk' (aschbacherSolvableCore 3 Y))
      (Subgroup.mem_subgroupOf.mpr k.2)
  let f : sec11K L a →* imgJ Y L a :=
    ((QuotientGroup.mk' (aschbacherSolvableCore 3 Y)).comp ι).codRestrict (imgJ Y L a) hιJ
  have hf : Function.Surjective f := by
    rintro ⟨q, hq⟩
    obtain ⟨l, hl, rfl⟩ := hq
    exact ⟨⟨(l : G), Subgroup.mem_subgroupOf.mp hl⟩, rfl⟩
  have hQz : (Q : Subgroup (sec11K L a)) = Subgroup.zpowers (⟨x ^ 3, hx3K⟩ : sec11K L a) := by
    refine Subgroup.map_injective (sec11K L a).subtype_injective ?_
    rw [hQ, MonoidHom.map_zpowers]
    rfl
  refine ⟨Q.mapSurjective hf, ?_⟩
  rw [Sylow.coe_mapSurjective, hQz, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
  rfl

theorem nine_le_orderOf_x_cube (h : Sec11Data G A c L a R Y d x s r g) (hx : 9 < orderOf x) :
    9 ≤ orderOf (x ^ 3) := by
  have hxR : x ∈ R := (Item1116Proof.mem_R h).2.1
  obtain ⟨k, hk⟩ := Item1116Proof.exists_pow_eq_one_of_mem h hxR
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hk)
  rw [hj] at hx
  have hj3 : 3 ≤ j := by
    by_contra hcon
    push Not at hcon
    interval_cases j <;> norm_num at hx
  have h3 : 3 ∣ orderOf x := by
    rw [hj]
    exact dvd_pow_self 3 (by omega)
  rw [orderOf_pow' x (by norm_num : (3 : ℕ) ≠ 0), Nat.gcd_eq_right h3, hj]
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  rw [pow_succ, Nat.mul_div_cancel _ (by norm_num : (0 : ℕ) < 3)]
  calc 9 = 3 ^ 2 := by norm_num
    _ ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem orderOf_conj_le_orderOf_thetaAut (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117)
    (h : Sec11Data G A c L a R Y d x s r g)
    (hcN : c ∈ Subgroup.normalizer (Y : Set G)) (hsN : s ∈ Subgroup.normalizer (Y : Set G))
    (hsa : s * a = a * s) {ζ : Y ⧸ aschbacherSolvableCore 3 Y} (hζ3 : ∃ k : ℕ, ζ ^ 3 ^ k = 1)
    (hζα : Sec4.Item426.thetaAut Y hcN ζ = ζ)
    (hζJ : ∀ j ∈ imgJ Y L a, ζ * j * ζ⁻¹ = j) :
    orderOf (MulAut.conj ζ) ≤ orderOf (Sec4.Item426.thetaAut Y hsN) := by
  classical
  have hc3 : c ^ 3 = 1 := h.mem_partTwoF.1.2 c h.mem_A
  have hζmem : ζ ∈ Sec4.Item426.fixSub (Sec4.Item426.thetaAut Y hcN) :=
    Sec4.Item426.mem_fixSub.mpr hζα
  rw [Sec4.Item426.fixSub_thetaAut_eq_map Y hcN hc3] at hζmem
  obtain ⟨y₀, hy₀, hπy₀⟩ := Subgroup.mem_map.mp hζmem
  obtain ⟨y', hy'z, ⟨k, hk⟩, hπy'⟩ :=
    exists_threeElement_lift (QuotientGroup.mk' (aschbacherSolvableCore 3 Y)) hπy₀ hζ3
  have hy'C : (y' : G) ∈ Subgroup.centralizer ({c} : Set G) := by
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hy'z
    rw [← hi]
    simpa using Subgroup.zpow_mem _ (Subgroup.mem_subgroupOf.mp hy₀) i
  have hyY : (y' : G) ∈ Y := y'.2
  have hyN : (y' : G) ∈ Subgroup.normalizer (Y : Set G) := Subgroup.le_normalizer hyY
  have hyτ : Sec4.Item426.thetaAut Y hyN = MulAut.conj ζ := by
    rw [thetaAut_of_mem Y hyY hyN]
    exact congrArg MulAut.conj hπy'
  have hy3 : (y' : G) ^ 3 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hRcL := Item1116Proof.le_centralizer_and_normalizer h45 h
  have hCcH : Subgroup.centralizer ({c} : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
    rw [CFSG.RankThree.GroupTheory.SteinbergBY.centralizer_singleton_eq_centralizer_zpowers]
    exact Subgroup.centralizer_le_normalizer _
  have hTX : R ⊓ Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (Y : Set G) := by
    rintro w ⟨hwR, hwC⟩
    exact h.toSec11Std.mem_normalizer_Y (Item1119StepsProof.sec11K_ne_bot h) (hRcL.2 hwR)
      (Subgroup.mem_centralizer_singleton_iff.mp hwC)
  set f : G → MulAut (Y ⧸ aschbacherSolvableCore 3 Y) := fun n =>
    if hn : n ∈ Subgroup.normalizer (Y : Set G) then Sec4.Item426.thetaAut Y hn else 1 with hfdef
  have hfeq : ∀ (n : G) (hn : n ∈ Subgroup.normalizer (Y : Set G)),
      f n = Sec4.Item426.thetaAut Y hn := fun n hn => dif_pos hn
  have hf : ∀ m ∈ Subgroup.normalizer (Y : Set G), ∀ n ∈ Subgroup.normalizer (Y : Set G),
      f (m * n) = f m * f n := by
    intro m hm n hn
    rw [hfeq _ (Subgroup.mul_mem _ hm hn), hfeq m hm, hfeq n hn]
    exact thetaAut_mul Y hm hn
  have hT := isSylowOf_inf_centralizer_a h113 h117 h
  have hTJ : ∀ t ∈ R ⊓ Subgroup.centralizer ({a} : Set G), ∀ j ∈ imgJ Y L a,
      f t j ∈ imgJ Y L a := by
    rintro t ⟨htR, htC⟩ j hj
    rw [hfeq t (hTX ⟨htR, htC⟩)]
    exact thetaAut_mem_imgJ h.toSec11Std (hRcL.2 htR)
      (Subgroup.mem_centralizer_singleton_iff.mp htC) (hTX ⟨htR, htC⟩) hj
  have hyH : (y' : G) ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓
      Subgroup.centralizer ({a} : Set G) :=
    ⟨hCcH hy'C, Sec6.le_centralizer_of_mem_thetaComponentsAt h.mem_thetaComponentsAt_Y hyY⟩
  have hyJ : ∀ j ∈ imgJ Y L a, f y' j = j := by
    intro j hj
    rw [hfeq _ hyN, hyτ, MulAut.conj_apply]
    exact hζJ j hj
  obtain ⟨m, ⟨hmN, hmH⟩, hmJ, hmT⟩ := exists_conj_mem_fixer (imgJ Y L a)
    (Subgroup.normalizer (Y : Set G))
    (Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓ Subgroup.centralizer ({a} : Set G))
    (R ⊓ Subgroup.centralizer ({a} : Set G)) f hf hT hTX hTJ hyN hyH ⟨k, hy3⟩ hyJ
  have hwN : m * (y' : G) * m⁻¹ ∈ Subgroup.normalizer (Y : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hmN hyN) (Subgroup.inv_mem _ hmN)
  have hτw : Sec4.Item426.thetaAut Y hwN =
      Sec4.Item426.thetaAut Y hmN * Sec4.Item426.thetaAut Y hyN *
        (Sec4.Item426.thetaAut Y hmN)⁻¹ := by
    rw [thetaAut_mul Y (Subgroup.mul_mem _ hmN hyN) (Subgroup.inv_mem _ hmN),
      thetaAut_mul Y hmN hyN, thetaAut_inv Y hmN]
  have hmJ' : ∀ j ∈ imgJ Y L a, Sec4.Item426.thetaAut Y hmN j = j := fun j hj => by
    rw [← hfeq m hmN]
    exact hmJ j hj
  have hmJinv : ∀ j ∈ imgJ Y L a, (Sec4.Item426.thetaAut Y hmN)⁻¹ j = j := fun j hj => by
    have := hmJ' j hj
    rw [MulAut.inv_apply, MulEquiv.symm_apply_eq]
    exact this.symm
  have hwJ : ∀ j ∈ imgJ Y L a, Sec4.Item426.thetaAut Y hwN j = j := by
    intro j hj
    rw [hτw]
    change Sec4.Item426.thetaAut Y hmN (Sec4.Item426.thetaAut Y hyN
      ((Sec4.Item426.thetaAut Y hmN)⁻¹ j)) = j
    rw [hmJinv j hj, hyτ, MulAut.conj_apply, hζJ j hj, hmJ' j hj]
  have hwT : m * (y' : G) * m⁻¹ ∈ R ⊓ Subgroup.centralizer ({a} : Set G) := hmT
  have hwsa := mem_zpowers_s_sup_zpowers_a_of_fixes h45 h hwT.1
    (Subgroup.mem_centralizer_singleton_iff.mp hwT.2) hwN hwJ
  have hYa : ∀ z ∈ Y, a * z = z * a := fun z hz =>
    (Subgroup.mem_centralizer_singleton_iff.mp
      (Sec6.le_centralizer_of_mem_thetaComponentsAt h.mem_thetaComponentsAt_Y hz)).symm
  have haN : a ∈ Subgroup.normalizer (Y : Set G) :=
    Subgroup.mem_normalizer_fintype fun z hz => by
      rw [hYa z hz, mul_inv_cancel_right]
      exact hz
  have hkey : ∀ v ∈ Subgroup.zpowers s ⊔ Subgroup.zpowers a,
      ∃ hv : v ∈ Subgroup.normalizer (Y : Set G),
        Sec4.Item426.thetaAut Y hv ∈ Subgroup.zpowers (Sec4.Item426.thetaAut Y hsN) := by
    intro v hv
    rw [Subgroup.sup_eq_closure] at hv
    induction hv using Subgroup.closure_induction with
    | mem v hv =>
      rcases hv with hv | hv
      · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
        exact ⟨Subgroup.zpow_mem _ hsN i, i, (thetaAut_zpow Y hsN i).symm⟩
      · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
        refine ⟨Subgroup.zpow_mem _ haN i, ?_⟩
        rw [thetaAut_eq_one_of_forall_commute Y (Subgroup.zpow_mem _ haN i) fun z hz =>
          ((show Commute a z from hYa z hz).zpow_left i).eq]
        exact Subgroup.one_mem _
    | one =>
      refine ⟨Subgroup.one_mem _, ?_⟩
      rw [thetaAut_eq_one_of_forall_commute Y (Subgroup.one_mem _) fun z _ => by simp]
      exact Subgroup.one_mem _
    | mul x y hx hy ihx ihy =>
      obtain ⟨hx', ihx⟩ := ihx
      obtain ⟨hy', ihy⟩ := ihy
      refine ⟨Subgroup.mul_mem _ hx' hy', ?_⟩
      rw [thetaAut_mul Y hx' hy']
      exact Subgroup.mul_mem _ ihx ihy
    | inv x hx ihx =>
      obtain ⟨hx', ihx⟩ := ihx
      refine ⟨Subgroup.inv_mem _ hx', ?_⟩
      rw [thetaAut_inv Y hx']
      exact Subgroup.inv_mem _ ihx
  obtain ⟨hwN', hwz⟩ := hkey (m * (y' : G) * m⁻¹) hwsa
  have hwz' : Sec4.Item426.thetaAut Y hwN ∈ Subgroup.zpowers (Sec4.Item426.thetaAut Y hsN) := hwz
  have hord : orderOf (Sec4.Item426.thetaAut Y hwN) = orderOf (MulAut.conj ζ) := by
    rw [hτw, hyτ]
    have := orderOf_injective (MulAut.conj (Sec4.Item426.thetaAut Y hmN)).toMonoidHom
      (MulAut.conj (Sec4.Item426.thetaAut Y hmN)).injective (MulAut.conj ζ)
    simpa [MulAut.conj_apply] using this
  rw [← hord]
  exact Nat.le_of_dvd (orderOf_pos _) (orderOf_dvd_of_mem_zpowers hwz')

theorem s_commutator_mem_theta (h45 : Sec4.Item4_5) (h : Sec11Data G A c L a R Y d x s r g)
    (hsa : s * a = a * s) :
    ∀ k ∈ sec11K L a, s * k * s⁻¹ * k⁻¹ ∈
      inSubgroup (aschbacherSolvableCore 3) (sec11K L a) := by
  have hsR : s ∈ R := (Item1116Proof.mem_R h).2.2
  have hsL : s ∈ Subgroup.normalizer (L : Set G) :=
    (Item1116Proof.le_centralizer_and_normalizer h45 h).2 hsR
  have hsC : s ∈ Sec4.thetaQuotCentralizer L := by
    have h1 : s ∈ Subgroup.zpowers s := Subgroup.mem_zpowers s
    rw [← h.inf_centralizer_eq] at h1
    exact h1.2
  have hsθ : ∀ l ∈ L, l⁻¹ * (s * l * s⁻¹) ∈ inSubgroup (aschbacherSolvableCore 3) L :=
    (Sec6.mem_thetaQuotCentralizer_iff.mp hsC).2
  have hsK : s ∈ Subgroup.normalizer (sec11K L a : Set G) :=
    GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_perfectResidual _
      (GroupTheory.SteinbergBY.mem_normalizer_inf hsL
        (Subgroup.le_normalizer (Subgroup.mem_centralizer_singleton_iff.mpr hsa)))
  intro k hk
  have hkL : k ∈ L := sec11K_le L a hk
  have hzK : k⁻¹ * (s * k * s⁻¹) ∈ sec11K L a :=
    (sec11K L a).mul_mem ((sec11K L a).inv_mem hk) ((Subgroup.mem_normalizer_iff.mp hsK k).mp hk)
  have hzθ : k⁻¹ * (s * k * s⁻¹) ∈ inSubgroup (aschbacherSolvableCore 3) (sec11K L a) :=
    Sec13.inf_inSubgroup_theta_le (sec11K_le L a) ⟨hzK, hsθ k hkL⟩
  have e : s * k * s⁻¹ * k⁻¹ = k * (k⁻¹ * (s * k * s⁻¹)) * k⁻¹ := by group
  rw [e]
  exact KS11LieProof.conj_mem_inSubgroup hk hzθ

theorem v0_data (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117)
    (hbig : Sec11Big G A c L a R Y d x s r g) :
    ∃ (hcN : c ∈ Subgroup.normalizer (Y : Set G)) (hsN : s ∈ Subgroup.normalizer (Y : Set G))
      (hx3Y : x ^ 3 ∈ Y) (hgY : g ∈ Y),
      V0Data Y (sec11K L a) c s hcN hsN (imgJ Y L a)
        (QuotientGroup.mk' (aschbacherSolvableCore 3 Y) ⟨x ^ 3, hx3Y⟩)
        (QuotientGroup.mk' (aschbacherSolvableCore 3 Y) ⟨g, hgY⟩) ∧
      (V0Concl (Sec4.Item426.thetaAut Y hsN)
          (QuotientGroup.mk' (aschbacherSolvableCore 3 Y) ⟨x ^ 3, hx3Y⟩)
          (QuotientGroup.mk' (aschbacherSolvableCore 3 Y) ⟨g, hgY⟩) →
        g * s * g⁻¹ ∈ Subgroup.closure ({s, a, x ^ 3} : Set G) ⊔
            Sec4.thetaQuotCentralizer Y ∧
          g * x ^ 3 * g⁻¹ ∈ Subgroup.closure ({s, a, x ^ 3} : Set G) ⊔
            Sec4.thetaQuotCentralizer Y) := by
  have h := hbig.toSec11Data
  have hsa : s * a = a * s := item1115_of_mhoV h45 h113 h117 G A c L a R Y d x s r g h
  obtain ⟨-, hxR, hsR⟩ := Item1116Proof.mem_R h
  obtain ⟨-, -, hV0Y⟩ := Item1119StepsProof.V0_le h45 h hsa
  have hsV : s ∈ Subgroup.closure ({s, a, x ^ 3} : Set G) := Subgroup.subset_closure (by simp)
  have hx3V : x ^ 3 ∈ Subgroup.closure ({s, a, x ^ 3} : Set G) :=
    Subgroup.subset_closure (by simp)
  have hsN : s ∈ Subgroup.normalizer (Y : Set G) := hV0Y hsV
  have hx3N : x ^ 3 ∈ Subgroup.normalizer (Y : Set G) := hV0Y hx3V
  have hgY : g ∈ Y := h.g_mem.1
  have hgN : g ∈ Subgroup.normalizer (Y : Set G) := Subgroup.le_normalizer hgY
  have hx3Y : x ^ 3 ∈ Y := Item1119Proof.x_cube_mem_Y h45 h
  have hRcL := Item1116Proof.le_centralizer_and_normalizer h45 h
  have hcR : c ∈ R := Item1115Proof.A_le_R h.toHyp91 h.mem_A
  have hca : c * a = a * c := congrArg Subtype.val
    (h.mem_partTwoF.1.1.is_comm.comm ⟨c, h.mem_A⟩ ⟨a, h.a_mem⟩)
  have hcN : c ∈ Subgroup.normalizer (Y : Set G) :=
    h.toSec11Std.mem_normalizer_Y (Item1119StepsProof.sec11K_ne_bot h) (hRcL.2 hcR) hca
  have hc3 : c ^ 3 = 1 := h.mem_partTwoF.1.2 c h.mem_A
  have hK' := mem_thetaComponentsIn_sec11K_inf h.toSec11Std
  have hT := kType119 G A c L a R Y h.toSec11Std d h.inf_eq h.closure_eq
  have hKY : sec11K L a ≤ Y := h.sec11K_le
  have hJα : imgJ Y L a ∈ thetaComponentsIn
      (Sec4.Item426.fixSub (Sec4.Item426.thetaAut Y hcN)) :=
    Sec4.Item426.map_mem_thetaComponentsIn_fixSub Y hcN hc3 hK'
  obtain ⟨eK⟩ := Sec4.Item426.nonempty_quotTheta_map_equiv Y hKY
  have hJT : IsType424 (imgJ Y L a ⧸ aschbacherSolvableCore 3 (imgJ Y L a)) :=
    isType424_of_mulEquiv eK.symm hT
  have hα3 : Sec4.Item426.thetaAut Y hcN ^ 3 = 1 := Sec4.Item426.thetaAut_pow_eq_one Y hcN hc3
  have hξJ := x_cube_mem_imgJ h45 h hx3Y
  have hξsyl := isSylowOf_zpowers_mk_x_cube h45 h113 h117 h hx3Y
  have hξ9 : 9 ≤ orderOf (QuotientGroup.mk' (aschbacherSolvableCore 3 Y) ⟨x ^ 3, hx3Y⟩) := by
    rw [orderOf_mk_x_cube h hx3Y]
    exact nine_le_orderOf_x_cube h hbig.orderOf_x_gt
  obtain ⟨k, hk⟩ := Item1116Proof.exists_pow_eq_one_of_mem h hsR
  have hσ3 : ∃ k : ℕ, Sec4.Item426.thetaAut Y hsN ^ 3 ^ k = 1 :=
    ⟨k, Sec4.Item426.thetaAut_pow_eq_one Y hsN hk⟩
  have hsc : s * c = c * s := Subgroup.mem_centralizer_singleton_iff.mp (hRcL.1 hsR)
  have hσα : Sec4.Item426.thetaAut Y hsN * Sec4.Item426.thetaAut Y hcN =
      Sec4.Item426.thetaAut Y hcN * Sec4.Item426.thetaAut Y hsN := by
    rw [← thetaAut_mul Y hsN hcN, ← thetaAut_mul Y hcN hsN]
    exact thetaAut_congr Y _ _ hsc
  have hσJ : ∀ j ∈ imgJ Y L a, j⁻¹ * Sec4.Item426.thetaAut Y hsN j ∈
      inSubgroup (aschbacherSolvableCore 3) (imgJ Y L a) :=
    fun j hj => thetaAut_s_mem_theta_imgJ h45 h hsN hsa hj
  have hσξ : Sec4.Item426.thetaAut Y hsN *
        MulAut.conj (QuotientGroup.mk' (aschbacherSolvableCore 3 Y) ⟨x ^ 3, hx3Y⟩) =
      MulAut.conj (QuotientGroup.mk' (aschbacherSolvableCore 3 Y) ⟨x ^ 3, hx3Y⟩) *
        Sec4.Item426.thetaAut Y hsN := by
    rw [← thetaAut_of_mem Y hx3Y hx3N, ← thetaAut_mul Y hsN hx3N, ← thetaAut_mul Y hx3N hsN]
    apply thetaAut_congr
    have hsx : s * x = x * s := h.toSec11Std.commute_s_x h.inf_L_eq h.inf_centralizer_eq
    exact ((show Commute s x from hsx).pow_right 3).eq
  have hγ3 : (QuotientGroup.mk' (aschbacherSolvableCore 3 Y) ⟨g, hgY⟩) ^ 3 = 1 := by
    have hg3 : g ^ 3 = 1 := by
      rw [← hbig.orderOf_g]
      exact pow_orderOf_eq_one g
    rw [← map_pow]
    have : (⟨g, hgY⟩ : Y) ^ 3 = 1 := Subtype.ext (by simpa using hg3)
    rw [this, map_one]
  have hP : IsPGroup 3 (Subgroup.closure ({s, x ^ 3, g} : Set G)) := by
    refine h.isPGroup_sec11P.to_le ?_
    rw [Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with hy | hy | hy <;> rw [hy]
    · exact Item1119Proof.R_le_P R g hsR
    · exact Item1119Proof.R_le_P R g (R.pow_mem hxR 3)
    · exact Item1119Proof.g_mem_P R g
  have hPτ := isPGroup_closure_thetaAut Y hsN hx3N hgN hP
  rw [thetaAut_of_mem Y hx3Y hx3N, thetaAut_of_mem Y hgY hgN] at hPτ
  have hLB : ∀ ζ : Y ⧸ aschbacherSolvableCore 3 Y, (∃ k : ℕ, ζ ^ 3 ^ k = 1) →
      Sec4.Item426.thetaAut Y hcN ζ = ζ → (∀ j ∈ imgJ Y L a, ζ * j * ζ⁻¹ = j) →
        orderOf (MulAut.conj ζ) ≤ orderOf (Sec4.Item426.thetaAut Y hsN) :=
    fun ζ h3 hα hJ => orderOf_conj_le_orderOf_thetaAut h45 h113 h117 h hcN hsN hsa h3 hα hJ
  refine ⟨hcN, hsN, hx3Y, hgY, ⟨hc3, hK', hT, ⟨k, hk⟩, hsc,
    s_commutator_mem_theta h45 h hsa, rfl, hα3, hJα, hJT, hξJ, hξsyl, hξ9, hσ3, hσα, hσJ, hσξ,
    hγ3, hPτ, hLB⟩, ?_⟩
  rintro ⟨hs1, hx1⟩
  have hmono : Subgroup.closure ({s, x ^ 3} : Set G) ⊔ Sec4.thetaQuotCentralizer Y ≤
      Subgroup.closure ({s, a, x ^ 3} : Set G) ⊔ Sec4.thetaQuotCentralizer Y := by
    refine sup_le_sup_right (Subgroup.closure_mono ?_) _
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy ⊢
    tauto
  have hb1 : g * s * g⁻¹ ∈ Subgroup.normalizer (Y : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hgN hsN) (Subgroup.inv_mem _ hgN)
  have hb2 : g * x ^ 3 * g⁻¹ ∈ Subgroup.normalizer (Y : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hgN hx3N) (Subgroup.inv_mem _ hgN)
  have e1 : Sec4.Item426.thetaAut Y hb1 =
      MulAut.conj (QuotientGroup.mk' (aschbacherSolvableCore 3 Y) ⟨g, hgY⟩) *
        Sec4.Item426.thetaAut Y hsN *
        (MulAut.conj (QuotientGroup.mk' (aschbacherSolvableCore 3 Y) ⟨g, hgY⟩))⁻¹ := by
    rw [thetaAut_mul Y (Subgroup.mul_mem _ hgN hsN) (Subgroup.inv_mem _ hgN),
      thetaAut_mul Y hgN hsN, thetaAut_inv Y hgN, thetaAut_of_mem Y hgY hgN]
  have e2 : Sec4.Item426.thetaAut Y hb2 =
      MulAut.conj (QuotientGroup.mk' (aschbacherSolvableCore 3 Y) ⟨g, hgY⟩) *
        MulAut.conj (QuotientGroup.mk' (aschbacherSolvableCore 3 Y) ⟨x ^ 3, hx3Y⟩) *
        (MulAut.conj (QuotientGroup.mk' (aschbacherSolvableCore 3 Y) ⟨g, hgY⟩))⁻¹ := by
    rw [thetaAut_mul Y (Subgroup.mul_mem _ hgN hx3N) (Subgroup.inv_mem _ hgN),
      thetaAut_mul Y hgN hx3N, thetaAut_inv Y hgN, thetaAut_of_mem Y hgY hgN,
      thetaAut_of_mem Y hx3Y hx3N]
  refine ⟨hmono ?_, hmono ?_⟩
  · refine mem_closure_sup_thetaQuotCentralizer Y hsN hx3N hb1 ?_
    rw [e1, thetaAut_of_mem Y hx3Y hx3N]
    exact hs1
  · refine mem_closure_sup_thetaQuotCentralizer Y hsN hx3N hb2 ?_
    rw [e2, thetaAut_of_mem Y hx3Y hx3N]
    exact hx1

theorem step1120V0Bar_core (F : ∀ (Z : Type) [Group Z], Prop) (hF : V0Fam F)
    (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117)
    (hbig : Sec11Big G A c L a R Y d x s r g)
    (hFZ : F (Y ⧸ aschbacherSolvableCore 3 Y)) :
    g * s * g⁻¹ ∈ Subgroup.closure ({s, a, x ^ 3} : Set G) ⊔ Sec4.thetaQuotCentralizer Y ∧
      g * x ^ 3 * g⁻¹ ∈ Subgroup.closure ({s, a, x ^ 3} : Set G) ⊔ Sec4.thetaQuotCentralizer Y := by
  obtain ⟨hcN, hsN, hx3Y, hgY, D, back⟩ := v0_data h45 h113 h117 hbig
  exact back (hF _ hFZ _ _ _ _ _ D.alpha_cube D.J_comp D.J_type D.xi_mem D.xi_sylow D.xi_nine
    D.sigma_three D.sigma_alpha D.sigma_J D.sigma_xi D.gamma_cube D.P_three D.lower_bound)

theorem step1120V0Bar_coreL3 (hL3 : V0FamL3)
    (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117)
    (hbig : Sec11Big G A c L a R Y d x s r g)
    (hFZ : Sec13.IsLThreePi (Y ⧸ aschbacherSolvableCore 3 Y)) :
    g * s * g⁻¹ ∈ Subgroup.closure ({s, a, x ^ 3} : Set G) ⊔ Sec4.thetaQuotCentralizer Y ∧
      g * x ^ 3 * g⁻¹ ∈ Subgroup.closure ({s, a, x ^ 3} : Set G) ⊔ Sec4.thetaQuotCentralizer Y := by
  obtain ⟨hcN, hsN, hx3Y, hgY, D, back⟩ := v0_data h45 h113 h117 hbig
  exact back (hL3 G Y (sec11K L a) c s hcN hsN _ _ _ hFZ D)

theorem step1120V0Bar_of_fam (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117)
    (hG2 : V0FamG2) (hD4 : V0FamD4) (hL3 : V0FamL3) : Step1120V0Bar := by
  intro G _ _ A c L a R Y d x s r g hbig _
  rcases hbig.isList with h | h | h
  · exact step1120V0Bar_core (fun Z _ => ∃ q : TauCeti.PrimePower, Sec4.IsoGTwo Z q) hG2
      h45 h113 h117 hbig h
  · exact step1120V0Bar_core (fun Z _ => ∃ n : ℕ, Sec8.IsoTrialityD4 Z n) hD4
      h45 h113 h117 hbig h
  · exact step1120V0Bar_coreL3 hL3 h45 h113 h117 hbig h

end Item1120V0Bar

end CFSG.RankThree.PartTwo.Sec11

end
