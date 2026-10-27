module

public import CFSG.OddTranspositions.PartThree.Eleven.Statements
public import CFSG.OddTranspositions.PartThree.Eleven.OneOne.Hyp
public import CFSG.OddTranspositions.PartThree.Eleven.Minus.Pair
public import CFSG.OddTranspositions.PartThree.Eleven.Minus.Quandle
public import CFSG.OddTranspositions.PartThree.EightFive.KBarSetup
public import Certificates.Certificate2326
public import CFSG.OddTranspositions.PartThree.Eleven.OneTwo.KPCore
public import CFSG.OddTranspositions.PartThree.Ten.SetupQ
public import CFSG.Sporadic.Schreier.Co1OddGen

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity CFSG.OddTranspositions.QZ

section KOddCore

variable {G : Type} [Group G] [Finite G] {D : Set G}

private lemma le_center_sup_commutator_of_perfect_center_quotient {X : Type} [Group X]
    (h : Group.IsPerfect (X ⧸ Subgroup.center X)) :
    (⊤ : Subgroup X) ≤ Subgroup.center X ⊔ ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ := by
  intro x _
  let π : X →* X ⧸ Subgroup.center X := QuotientGroup.mk' (Subgroup.center X)
  have hmap : Subgroup.map π ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ = ⊤ := by
    rw [Subgroup.map_commutator,
      Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective _)]
    exact Group.IsPerfect.commutator_eq_top
  have hx : π x ∈ Subgroup.map π ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ := by
    rw [hmap]
    exact Subgroup.mem_top _
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
  have hz : y⁻¹ * x ∈ Subgroup.center X := by
    rw [← QuotientGroup.ker_mk' (Subgroup.center X), MonoidHom.mem_ker]
    change π (y⁻¹ * x) = 1
    rw [map_mul, map_inv, hyx, inv_mul_cancel]
  have hx' : x = y * (y⁻¹ * x) := by group
  rw [hx']
  exact Subgroup.mul_mem _
    (Subgroup.mem_sup_right (S := Subgroup.center X) hy)
    (Subgroup.mem_sup_left (T := ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆) hz)

private lemma commutator_commutator_eq_commutator_of_perfect_center_quotient {X : Type} [Group X]
    (h : Group.IsPerfect (X ⧸ Subgroup.center X)) :
    ⁅⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆, ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆⁆ =
      ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ := by
  let J : Subgroup X := ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆
  have hle := le_center_sup_commutator_of_perfect_center_quotient h
  have htop : (⊤ : Subgroup X) = Subgroup.center X ⊔ J := (eq_top_iff.mpr hle).symm
  have h1 : ⁅Subgroup.center X, Subgroup.center X ⊔ J⁆ = ⊥ := by
    rw [Subgroup.commutator_sup_left (Subgroup.center X) (Subgroup.center X) J,
      Subgroup.commutator_center_left (Subgroup.center X), Subgroup.commutator_center_left J,
      sup_bot_eq]
  have h2 : ⁅J, Subgroup.center X ⊔ J⁆ = ⁅J, J⁆ := by
    rw [Subgroup.commutator_sup_left J (Subgroup.center X) J,
      Subgroup.commutator_center_right J, bot_sup_eq]
  have hmain : ⁅Subgroup.center X ⊔ J, Subgroup.center X ⊔ J⁆ = ⁅J, J⁆ := by
    rw [Subgroup.commutator_sup_right (Subgroup.center X) J (Subgroup.center X ⊔ J), h1, h2,
      bot_sup_eq]
  have hJ : J = ⁅J, J⁆ := by
    change ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ = ⁅J, J⁆
    rw [htop]
    exact hmain
  exact hJ.symm

namespace ElevenTwoFrame

variable {hC : HypothesisC D} {S : Sylow 2 G} {T : Sylow 2 (Halpha D hC.alpha)}
  {r : Fin 3 → Halpha D hC.alpha}

private lemma d_notMem_DalphaStar (hC : HypothesisC D) : hC.d ∉ DalphaStar D hC.alpha := by
  intro hmem
  have hdE : hC.d ∈ hC.E := by rwa [hC.DalphaStar_alpha] at hmem
  have hdα : hC.d ∈ hC.alpha := hC.d_mem_alpha
  rw [hC.alpha_eq_normSet_diff] at hdα
  exact hdα.2 hdE

private lemma mem_DalphaStar_of_mem_range (hF : ElevenTwoFrame hC S T r) (i : Fin 3) :
    ((r i : Halpha D hC.alpha) : G) ∈ DalphaStar D hC.alpha := by
  have hri : r i ∈ DstarH hC := by
    have hrange : r i ∈
        ((T : Subgroup (Halpha D hC.alpha)) : Set (Halpha D hC.alpha)) ∩ DstarH hC := by
      rw [hF.frame.inter_eq]
      exact Set.mem_range_self i
    exact hrange.2
  exact (mem_DstarH_iff hC).mp hri

private lemma frame_ne_d (hF : ElevenTwoFrame hC S T r) (i : Fin 3) :
    hC.d ≠ ((r i : Halpha D hC.alpha) : G) := by
  intro h
  exact d_notMem_DalphaStar hC (h ▸ mem_DalphaStar_of_mem_range hF i)

private lemma exists_mul_mem_centralizer_d_inf (h : ElevenTwoHyp hC) (hF : ElevenTwoFrame hC S T r)
    {x : G} (hx : x ∈ Subgroup.centralizer {hC.d} ⊓ Subgroup.centralizer {frameE hC r}) :
    ∃ a ∈ Subgroup.zpowers hC.d,
      ∃ b ∈ Halpha D hC.alpha ⊓ Subgroup.centralizer {frameT hC r}, a * b = x := by
  let M : Subgroup G := Subgroup.centralizer {hC.d} ⊓ Subgroup.centralizer {frameE hC r}
  let A : Subgroup M := (Subgroup.zpowers hC.d).subgroupOf M
  let B : Subgroup M :=
    (Halpha D hC.alpha ⊓ Subgroup.centralizer {frameT hC r}).subgroupOf M
  have hMeq : Subgroup.zpowers hC.d ⊔ (Halpha D hC.alpha ⊓
      Subgroup.centralizer {frameT hC r}) = M := by
    rw [show M = Subgroup.zpowers hC.d ⊔ (Halpha D hC.alpha ⊓
      Subgroup.centralizer {frameT hC r}) from centralizer_d_inf h hF]
  have hAle : Subgroup.zpowers hC.d ≤ M := by rw [← hMeq]; exact le_sup_left
  have hBle : Halpha D hC.alpha ⊓ Subgroup.centralizer {frameT hC r} ≤ M := by
    rw [← hMeq]; exact le_sup_right
  have hAnorm : A.Normal := by
    refine Subgroup.normal_of_le_center ?_
    intro a ha
    rw [Subgroup.mem_center_iff]
    intro m
    apply Subtype.ext
    have ha' : (a : G) ∈ Subgroup.zpowers hC.d :=
      Subgroup.mem_subgroupOf.mp (by simpa [A] using ha)
    have hm : (m : G) * hC.d = hC.d * (m : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp m.2).1
    have hle : Subgroup.zpowers hC.d ≤ Subgroup.centralizer ({(m : G)} : Set G) :=
      Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hm.symm)
    simpa using (Subgroup.mem_centralizer_singleton_iff.mp (hle ha')).symm
  haveI : A.Normal := hAnorm
  have hsup : A ⊔ B = ⊤ := by
    have hsub := Subgroup.subgroupOf_sup (A := Subgroup.zpowers hC.d)
      (A' := Halpha D hC.alpha ⊓ Subgroup.centralizer {frameT hC r}) hAle hBle
    rw [hMeq, Subgroup.subgroupOf_self] at hsub
    exact hsub.symm
  have hmem : (⟨x, hx⟩ : M) ∈ A ⊔ B := by rw [hsup]; exact Subgroup.mem_top _
  obtain ⟨a, ha, b, hb, hab⟩ := (Subgroup.mem_sup_of_normal_left (s := A) (t := B)).mp hmem
  refine ⟨(a : G), Subgroup.mem_subgroupOf.mp (by simpa [A] using ha),
    (b : G), Subgroup.mem_subgroupOf.mp (by simpa [B] using hb), ?_⟩
  simpa using congrArg Subtype.val hab

private lemma localGroup_centralizes_oddCore_image (h : ElevenTwoHyp hC)
    (hF : ElevenTwoFrame hC S T r) :
    ∀ lH : ↥(localGroup (DstarH hC) (r 0 * r 1 * r 2)),
    ∀ q ∈ ((CFSG.oddCore (localGroup D (frameE hC r))).map
        (localGroup D (frameE hC r)).subtype) ⊓ Subgroup.centralizer {hC.d},
    q * ((Halpha D hC.alpha).subtype
        ((localGroup (DstarH hC) (r 0 * r 1 * r 2)).subtype lH)) =
      ((Halpha D hC.alpha).subtype
        ((localGroup (DstarH hC) (r 0 * r 1 * r 2)).subtype lH)) * q := by
  classical
  set LH : Subgroup (Halpha D hC.alpha) := localGroup (DstarH hC) (r 0 * r 1 * r 2) with hLH
  set KG : Subgroup G := localGroup D (frameE hC r) with hKG
  set NG : Subgroup G := (CFSG.oddCore KG).map KG.subtype with hNG
  set CG : Subgroup G := Subgroup.centralizer {hC.d} with hCG
  set PG : Subgroup G := NG ⊓ CG with hPG
  let ι : ↥LH →* G := (Halpha D hC.alpha).subtype.comp LH.subtype
  obtain ⟨eB⟩ := hF.frame.bender
  haveI hPSLperfect : Group.IsPerfect (CFSG.Theory.Comparator.PSL2Model 2) :=
    SetupQ.isPerfect_psl2Model (by norm_num)
  haveI hperfQ : Group.IsPerfect (↥LH ⧸ Subgroup.center ↥LH) :=
    Group.IsPerfect.ofSurjective (f := eB.symm.toMonoidHom) eB.symm.surjective
  let J : Subgroup ↥LH := ⁅(⊤ : Subgroup ↥LH), (⊤ : Subgroup ↥LH)⁆
  have hJperf : ⁅J, J⁆ = J :=
    commutator_commutator_eq_commutator_of_perfect_center_quotient hperfQ
  have hJle : (⊤ : Subgroup ↥LH) ≤ Subgroup.center ↥LH ⊔ J :=
    le_center_sup_commutator_of_perfect_center_quotient hperfQ
  have hL0_le_KG : LH.map (Halpha D hC.alpha).subtype ≤ KG := by
    rw [Subgroup.map_le_iff_le_comap]
    intro x hx
    show (x : G) ∈ KG
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
        apply mem_localGroup_of_mem
        refine ⟨(hC.DalphaStar_subset_commute ((mem_DstarH_iff hC).mp hy.1)).1, ?_⟩
        have h1 := (hC.DalphaStar_subset_commute ((mem_DstarH_iff hC).mp hy.1)).2
        have h2 := hy.2.map (Halpha D hC.alpha).subtype
        show Commute (y : G) (frameE hC r)
        rw [frameE]
        exact h1.mul_right h2
    | one => exact KG.one_mem
    | mul a b _ _ ha hb => exact KG.mul_mem ha hb
    | inv a _ ha => exact KG.inv_mem ha
  have hL0_le_CG : LH.map (Halpha D hC.alpha).subtype ≤ CG := by
    rw [Subgroup.map_le_iff_le_comap]
    intro x hx
    show (x : G) ∈ CG
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcomm : Commute (x : G) hC.d := by
      induction hx using Subgroup.closure_induction with
      | mem y hy => exact (hC.DalphaStar_subset_commute ((mem_DstarH_iff hC).mp hy.1)).2
      | one => exact Commute.one_left _
      | mul a b _ _ ha hb => simpa only [Subgroup.coe_mul] using ha.mul_left hb
      | inv a _ ha => simpa only [Subgroup.coe_inv] using ha.inv_left
    exact hcomm.eq
  have hNGnorm : ∀ l ∈ KG, ∀ x ∈ NG, l * x * l⁻¹ ∈ NG := by
    intro l hl x hx
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hx
    refine Subgroup.mem_map.mpr ⟨(⟨l, hl⟩ : KG) * m * (⟨l, hl⟩ : KG)⁻¹,
      (inferInstance : (CFSG.oddCore KG).Normal).conj_mem m hm ⟨l, hl⟩, ?_⟩
    simp
  have hL0N : LH.map (Halpha D hC.alpha).subtype ≤
      Subgroup.normalizer (PG : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro l hl x hx
    obtain ⟨hxNG, hxCG⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨hNGnorm l (hL0_le_KG hl) x hxNG, ?_⟩
    exact CG.mul_mem (CG.mul_mem (hL0_le_CG hl) hxCG) (CG.inv_mem (hL0_le_CG hl))
  have hodd : Odd (Nat.card ↥PG) := by
    have hle : PG ≤ NG := inf_le_left
    have hdvd : Nat.card ↥PG ∣ Nat.card ↥NG := by
      have h := Subgroup.card_subgroup_dvd_card (PG.subgroupOf NG)
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv] at h
    have hNGodd : Odd (Nat.card ↥NG) := by
      have hcard : Nat.card ↥NG = Nat.card ↥(CFSG.oddCore KG) :=
        Subgroup.card_map_of_injective (K := CFSG.oddCore KG) (f := KG.subtype)
          Subtype.coe_injective
      rw [hcard]
      exact ABGLocalTools.odd_card_oddCore
    exact hNGodd.of_dvd_nat hdvd
  have hdvd : Nat.card ↥PG ∣ 4095 := by
    have hM : PG ≤ Subgroup.centralizer {hC.d} ⊓ Subgroup.centralizer {frameE hC r} := by
      refine le_inf inf_le_right fun x hx => ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (commute_frameE h hF x
        (Subgroup.map_subtype_le (CFSG.oddCore KG) (Subgroup.mem_inf.mp hx).1)).eq
    have hdvd480 : Nat.card ↥PG ∣ 480 := by
      have hdvdd := Subgroup.card_subgroup_dvd_card
        (PG.subgroupOf (Subgroup.centralizer {hC.d} ⊓
          Subgroup.centralizer {frameE hC r}))
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM).toEquiv,
        card_centralizer_d_inf h hF] at hdvdd
      exact hdvdd
    have hcop : Nat.Coprime (Nat.card ↥PG) (2 ^ 5) :=
      (Nat.coprime_two_right.mpr hodd).pow_right 5
    have h15 : Nat.card ↥PG ∣ 15 := by
      have h480 : (480 : ℕ) = 2 ^ 5 * 15 := by norm_num
      rw [h480] at hdvd480
      exact hcop.dvd_of_dvd_mul_left hdvd480
    exact h15.trans (by norm_num : (15 : ℕ) ∣ 4095)
  have hJcent : ∀ j ∈ J.map ι, ∀ q ∈ PG, q * j = j * q := by
    refine CFSG.Sporadic.Co1Schreier.OddGen.centralizes_of_perfect_of_dvd hodd hdvd ?_ ?_
    · intro j hj
      obtain ⟨jH, -, rfl⟩ := Subgroup.mem_map.mp hj
      exact hL0N (Subgroup.mem_map_of_mem (Halpha D hC.alpha).subtype jH.2)
    · rw [← Subgroup.map_commutator J J ι, hJperf]
  have hZcent : ∀ z ∈ Subgroup.center ↥LH, ∀ q ∈ PG, q * ι z = ι z * q := by
    intro z hz q hq
    have hz' : ∀ y ∈ centSet (DstarH hC) (r 0 * r 1 * r 2),
        Commute (z : Halpha D hC.alpha) y := by
      intro y hy
      show (z : Halpha D hC.alpha) * y = y * (z : Halpha D hC.alpha)
      have hc := congrArg (fun w : ↥LH => (w : Halpha D hC.alpha))
        (Subgroup.mem_center_iff.mp hz ⟨y, Subgroup.subset_closure hy⟩)
      simpa using hc.symm
    have hframe := hF.frame.centralizer (z : Halpha D hC.alpha) hz'
    rcases hframe with h1 | ht
    · have hz1 : ι z = 1 := by
        show (Halpha D hC.alpha).subtype (z : Halpha D hC.alpha) = 1
        rw [h1]; rfl
      rw [hz1, mul_one, one_mul]
    · have hzt : ι z = frameT hC r := by
        show (Halpha D hC.alpha).subtype (z : Halpha D hC.alpha) = frameT hC r
        rw [ht]; rfl
      rw [hzt]
      have hqNG : q ∈ NG := (Subgroup.mem_inf.mp hq).1
      have hqCG : q ∈ CG := (Subgroup.mem_inf.mp hq).2
      have hqK : q ∈ KG := Subgroup.map_subtype_le (CFSG.oddCore KG) hqNG
      have hqu : Commute q hC.d := Subgroup.mem_centralizer_singleton_iff.mp hqCG
      have hqe : Commute q (frameE hC r) := commute_frameE h hF q hqK
      have hu2 : hC.d * hC.d = 1 := hC.setup.oddT.mul_self_eq_one hC.hd
      have hue : hC.d * frameE hC r = frameT hC r := by
        rw [frameE, ← mul_assoc, hu2, one_mul]
      have hqt : Commute q (frameT hC r) := by
        rw [← hue]; exact hqu.mul_right hqe
      exact hqt.eq
  intro lH q hq
  have hmem : lH ∈ Subgroup.center ↥LH ⊔ J := hJle (Subgroup.mem_top lH)
  obtain ⟨z, hz, j, hj, hzj⟩ :=
    (Subgroup.mem_sup_of_normal_left (s := Subgroup.center ↥LH) (t := J)).mp hmem
  rw [← hzj, map_mul]
  calc q * (ι z * ι j) = (q * ι z) * ι j := by group
    _ = (ι z * q) * ι j := by rw [hZcent z hz q hq]
    _ = ι z * (q * ι j) := by group
    _ = ι z * (ι j * q) := by rw [hJcent (ι j) (Subgroup.mem_map_of_mem ι hj) q hq]
    _ = (ι z * ι j) * q := by group

theorem oddCore_localGroup (h : ElevenTwoHyp hC) (hF : ElevenTwoFrame hC S T r) :
    CFSG.oddCore (localGroup D (frameE hC r)) = ⊥ := by
  classical
  set KG : Subgroup G := localGroup D (frameE hC r) with hKG
  have huK : hC.d ∈ KG := mem_localGroup_of_mem (d_mem_centSet h hF)
  have hr0K : ((r 0 : Halpha D hC.alpha) : G) ∈ KG :=
    mem_localGroup_of_mem (mem_centSet h hF 0)
  let u' : KG := ⟨hC.d, huK⟩
  let r0' : KG := ⟨((r 0 : Halpha D hC.alpha) : G), hr0K⟩
  let N : Subgroup KG := CFSG.oddCore KG
  have hu'2 : (u' : KG) * (u' : KG) = 1 := Subtype.ext (hC.setup.oddT.mul_self_eq_one hC.hd)
  have hCN : N ⊓ Subgroup.centralizer ({u'} : Set KG) = ⊥ := by
    rw [eq_bot_iff]
    intro m hm
    obtain ⟨hmN, hmu⟩ := Subgroup.mem_inf.mp hm
    have hmPG : (m : G) ∈ (N.map KG.subtype) ⊓ Subgroup.centralizer {hC.d} := by
      refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_map_of_mem KG.subtype hmN, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg (fun w : KG => (w : G)) (Subgroup.mem_centralizer_singleton_iff.mp hmu)
    have hmM : (m : G) ∈ Subgroup.centralizer {hC.d} ⊓
        Subgroup.centralizer {frameE hC r} := by
      refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hmPG).2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (commute_frameE h hF (m : G)
        (Subgroup.map_subtype_le (CFSG.oddCore KG) (Subgroup.mem_inf.mp hmPG).1)).eq
    obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_mem_centralizer_d_inf h hF hmM
    have hbgen : ∀ y ∈ centSet (DstarH hC) (r 0 * r 1 * r 2),
        Commute (⟨b, hb.1⟩ : Halpha D hC.alpha) y := by
      intro y hy
      have hmy : Commute (m : G) (y : G) := by
        have h := localGroup_centralizes_oddCore_image h hF
          (⟨y, Subgroup.subset_closure hy⟩ :
            ↥(localGroup (DstarH hC) (r 0 * r 1 * r 2))) (m : G) hmPG
        show (m : G) * (y : G) = (y : G) * (m : G)
        exact h
      have hay : Commute a (y : G) := by
        have hyD : (y : G) ∈ DalphaStar D hC.alpha := (mem_DstarH_iff hC).mp hy.1
        have hcy : Commute (y : G) hC.d := (hC.DalphaStar_subset_commute hyD).2
        have hle : Subgroup.zpowers hC.d ≤ Subgroup.centralizer ({(y : G)} : Set G) :=
          Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hcy.eq.symm)
        exact Subgroup.mem_centralizer_singleton_iff.mp (hle ha)
      have hb_eq : b = a⁻¹ * (m : G) := by rw [← hab]; group
      have hby : Commute b (y : G) := by
        rw [hb_eq]
        exact hay.inv_left.mul_left hmy
      apply Subtype.ext
      exact hby.eq
    have hbframe := hF.frame.centralizer (⟨b, hb.1⟩ : Halpha D hC.alpha) hbgen
    have hbcase : b = 1 ∨ b = frameT hC r := by
      rcases hbframe with h1 | ht
      · left; exact congrArg Subtype.val h1
      · right
        rw [show b = ((⟨b, hb.1⟩ : Halpha D hC.alpha) : G) from rfl, ht]
        rfl
    have hu2 : hC.d * hC.d = 1 := hC.setup.oddT.mul_self_eq_one hC.hd
    have ha2 : a * a = 1 := by
      have h : orderOf a ∣ 2 := by
        have h := Subgroup.orderOf_dvd_natCard (Subgroup.zpowers hC.d) ha
        rwa [Nat.card_zpowers, hC.setup.oddT.orderOf_eq_two hC.hd] at h
      simpa [pow_two] using orderOf_dvd_iff_pow_eq_one.mp h
    have he2 : frameE hC r * frameE hC r = 1 := by
      have h : orderOf (frameE hC r) ∣ 2 := by rw [orderOf_frameE h hF]
      simpa [pow_two] using orderOf_dvd_iff_pow_eq_one.mp h
    have ht2 : frameT hC r * frameT hC r = 1 := by
      have ht_eq : frameT hC r = hC.d * frameE hC r := by
        have hue : frameE hC r = hC.d * frameT hC r := rfl
        rw [hue, ← mul_assoc, hu2, one_mul]
      rw [ht_eq]
      calc hC.d * frameE hC r * (hC.d * frameE hC r)
          = (hC.d * hC.d) * (frameE hC r * frameE hC r) := by
              rw [show hC.d * frameE hC r * (hC.d * frameE hC r)
                    = hC.d * (frameE hC r * hC.d) * frameE hC r from by group]
              rw [show frameE hC r * hC.d = hC.d * frameE hC r from
                (commute_frameE h hF hC.d huK).eq.symm]
              group
        _ = 1 := by rw [hu2, he2, one_mul]
    have hm2 : (m : G) ^ 2 = 1 := by
      rcases hbcase with hb1 | hbt
      · rw [← hab, hb1, mul_one]
        simpa [pow_two] using ha2
      · have har : ∀ i : Fin 3, Commute a (((r i : Halpha D hC.alpha) : G)) := by
          intro i
          have hyD : (((r i : Halpha D hC.alpha) : G)) ∈ DalphaStar D hC.alpha :=
            mem_DalphaStar_of_mem_range hF i
          have hcy : Commute (((r i : Halpha D hC.alpha) : G)) hC.d :=
            (hC.DalphaStar_subset_commute hyD).2
          have hle : Subgroup.zpowers hC.d ≤
              Subgroup.centralizer ({(((r i : Halpha D hC.alpha) : G))} : Set G) :=
            Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hcy.eq.symm)
          exact Subgroup.mem_centralizer_singleton_iff.mp (hle ha)
        have hat : Commute a (frameT hC r) := by
          have ht_eq : frameT hC r = ((r 0 : Halpha D hC.alpha) : G) *
              ((r 1 * r 2 : Halpha D hC.alpha) : G) := by
            rw [show frameT hC r =
              ((r 0 * r 1 * r 2 : Halpha D hC.alpha) : G) from rfl]
            exact congrArg (fun x : Halpha D hC.alpha => (x : G))
              (mul_assoc (r 0) (r 1) (r 2))
          rw [ht_eq]
          exact (har 0).mul_right ((har 1).mul_right (har 2))
        rw [← hab, hbt]
        calc (a * frameT hC r) ^ 2
            = (a * a) * (frameT hC r * frameT hC r) := by
                rw [pow_two]
                rw [show a * frameT hC r * (a * frameT hC r)
                      = a * (frameT hC r * a) * frameT hC r from by group]
                rw [hat.eq.symm]
                group
          _ = 1 := by rw [ha2, ht2, one_mul]
    have hoddm : Odd (orderOf (m : G)) := by
      have h : orderOf (m : KG) ∣ Nat.card ↥N := Subgroup.orderOf_dvd_natCard N hmN
      have h' : orderOf (m : G) ∣ Nat.card ↥N := by
        rwa [← Subgroup.orderOf_coe (m : KG)] at h
      exact (ABGLocalTools.odd_card_oddCore (H := KG)).of_dvd_nat h'
    have hord1 : orderOf (m : G) = 1 := by
      have hdvd : orderOf (m : G) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hm2
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
      · exact h
      · exact absurd (h ▸ hoddm) (by decide)
    exact Subtype.ext (orderOf_eq_one_iff.mp hord1)
  have hinv_u : ∀ y : N, (u' : KG) * (y : KG) * (u' : KG)⁻¹ = (y : KG)⁻¹ := by
    have hfpf : MonoidHom.FixedPointFree (⇑(MulAut.conjNormal (H := N) u')) := by
      intro y hy
      have hthis : (u' : KG) * (y : KG) * (u' : KG)⁻¹ = (y : KG) := by
        have := congrArg (fun w : N => (w : KG)) hy
        simpa [MulAut.conjNormal_apply] using this
      have hmem : (y : KG) ∈ N ⊓ Subgroup.centralizer ({u'} : Set KG) := by
        refine Subgroup.mem_inf.mpr ⟨y.2, ?_⟩
        rw [Subgroup.mem_centralizer_singleton_iff]
        have huy : (u' : KG) * (y : KG) = (y : KG) * u' := by
          have h := congrArg (fun z : KG => z * (u' : KG)) hthis
          simpa [mul_assoc, hu'2] using h
        exact huy.symm
      rw [hCN, Subgroup.mem_bot] at hmem
      exact Subtype.ext hmem
    have hinvol : Function.Involutive (⇑(MulAut.conjNormal (H := N) u')) := by
      intro y
      apply Subtype.ext
      simp only [MulAut.conjNormal_apply]
      calc (u' : KG) * ((u' : KG) * (y : KG) * (u' : KG)⁻¹) * (u' : KG)⁻¹
          = ((u' : KG) * (u' : KG)) * (y : KG) * ((u' : KG)⁻¹ * (u' : KG)⁻¹) := by group
        _ = (y : KG) := by
              rw [hu'2, one_mul]
              rw [show (u' : KG)⁻¹ = (u' : KG) from inv_eq_of_mul_eq_one_right hu'2]
              rw [hu'2, mul_one]
    have h := MonoidHom.FixedPointFree.coe_eq_inv_of_involutive hfpf hinvol
    intro y
    have := congrFun h y
    have := congrArg (fun w : N => (w : KG)) this
    simpa [MulAut.conjNormal_apply] using this
  have hinv_r : ∀ y : N, (r0' : KG) * (y : KG) * (r0' : KG)⁻¹ = (y : KG)⁻¹ := by
    obtain ⟨kG, hkKG, hkconj⟩ := transitive h hF ((r 0 : Halpha D hC.alpha) : G)
      (mem_centSet h hF 0)
    let k' : KG := ⟨kG, hkKG⟩
    have hk' : k' * u' * k'⁻¹ = r0' := Subtype.ext hkconj
    intro y
    have hmem : k'⁻¹ * (y : KG) * k' ∈ N := by
      simpa using (inferInstance : N.Normal).conj_mem (y : KG) y.2 k'⁻¹
    have h1 := hinv_u ⟨k'⁻¹ * (y : KG) * k', hmem⟩
    rw [← hk']
    calc k' * u' * k'⁻¹ * (y : KG) * (k' * u' * k'⁻¹)⁻¹
        = k' * (u' * (k'⁻¹ * (y : KG) * k') * u'⁻¹) * k'⁻¹ := by group
      _ = k' * (k'⁻¹ * (y : KG) * k')⁻¹ * k'⁻¹ := by rw [h1]
      _ = (y : KG)⁻¹ := by group
  rw [eq_bot_iff]
  intro n hn
  set nG : G := (n : G) with hnG
  have hn_inv_u : hC.d * nG * hC.d⁻¹ = nG⁻¹ := by
    have h := congrArg (fun w : KG => (w : G)) (hinv_u ⟨n, hn⟩)
    simpa [u', nG] using h
  have hn_inv_r : ((r 0 : Halpha D hC.alpha) : G) * nG *
      (((r 0 : Halpha D hC.alpha) : G))⁻¹ = nG⁻¹ := by
    have h := congrArg (fun w : KG => (w : G)) (hinv_r ⟨n, hn⟩)
    simpa [r0', nG] using h
  set uG : G := hC.d with huG
  set rG : G := ((r 0 : Halpha D hC.alpha) : G) with hrG
  have huD : uG ∈ D := hC.hd
  have hrD : rG ∈ D := (mem_centSet h hF 0).1
  have hne : uG ≠ rG := frame_ne_d hF 0
  have hcomm : Commute uG rG := ((mem_commSet h hF 0).2.1).symm
  have hn_odd : Odd (orderOf nG) := by
    have h : orderOf (n : KG) ∣ Nat.card ↥N := Subgroup.orderOf_dvd_natCard N hn
    have h' : orderOf nG ∣ Nat.card ↥N := by rwa [← Subgroup.orderOf_coe (n : KG)] at h
    exact (ABGLocalTools.odd_card_oddCore (H := KG)).of_dvd_nat h'
  have hux : uG * nG = nG⁻¹ * uG := by
    calc uG * nG = uG * nG * uG⁻¹ * uG := by group
      _ = nG⁻¹ * uG := by rw [hn_inv_u]
  have hrx : rG * nG = nG⁻¹ * rG := by
    calc rG * nG = rG * nG * rG⁻¹ * rG := by group
      _ = nG⁻¹ * rG := by rw [hn_inv_r]
  have hcomm_ur_n : Commute (uG * rG) nG := by
    have hconj : (uG * rG) * nG * (uG * rG)⁻¹ = nG := by
      calc (uG * rG) * nG * (uG * rG)⁻¹ = uG * (rG * nG * rG⁻¹) * uG⁻¹ := by group
        _ = uG * nG⁻¹ * uG⁻¹ := by rw [hn_inv_r]
        _ = (uG * nG * uG⁻¹)⁻¹ := by group
        _ = nG := by rw [hn_inv_u, inv_inv]
    have h := congrArg (fun z : G => z * (uG * rG)) hconj
    show (uG * rG) * nG = nG * (uG * rG)
    simpa [mul_assoc] using h
  have hord_ur : orderOf (uG * rG) = 2 :=
    hC.setup.oddT.orderOf_mul_eq_two huD hrD hne hcomm
  have hord2 : orderOf (nG⁻¹ * nG⁻¹) = orderOf nG := by
    have h1 : nG⁻¹ * nG⁻¹ = (nG ^ 2)⁻¹ := by rw [pow_two]; group
    rw [h1, orderOf_inv, orderOf_pow]
    have hg : (orderOf nG).gcd 2 = 1 := Nat.coprime_two_right.mpr hn_odd
    rw [hg, Nat.div_one]
  have hfac : uG * (nG * rG * nG⁻¹) = (nG⁻¹ * nG⁻¹) * (uG * rG) := by
    calc uG * (nG * rG * nG⁻¹) = uG * nG * rG * nG⁻¹ := by group
      _ = nG⁻¹ * uG * rG * nG⁻¹ := by rw [hux]
      _ = nG⁻¹ * (uG * rG) * nG⁻¹ := by group
      _ = nG⁻¹ * ((uG * rG) * nG⁻¹) := by group
      _ = nG⁻¹ * (nG⁻¹ * (uG * rG)) := by rw [hcomm_ur_n.inv_right.eq]
      _ = (nG⁻¹ * nG⁻¹) * (uG * rG) := by group
  have horder : orderOf (uG * (nG * rG * nG⁻¹)) = 2 * orderOf nG := by
    have hcomm2 : Commute (nG⁻¹ * nG⁻¹) (uG * rG) :=
      (hcomm_ur_n.symm.inv_left).mul_left hcomm_ur_n.symm.inv_left
    have hcop : (orderOf (nG⁻¹ * nG⁻¹)).Coprime (orderOf (uG * rG)) := by
      rw [hord2, hord_ur]
      exact Nat.coprime_two_right.mpr hn_odd
    rw [hfac, hcomm2.orderOf_mul_eq_mul_orderOf_of_coprime hcop, hord2, hord_ur, Nat.mul_comm]
  have hconj : nG * rG * nG⁻¹ ∈ D := hC.setup.conj_mem nG hrD
  have hprop := hC.setup.oddT.2 uG huD (nG * rG * nG⁻¹) hconj
  rw [horder] at hprop
  have hn1 : orderOf nG = 1 := by
    rcases hprop with hdvd | hodd
    · have h2 : 2 * orderOf nG = 2 := by
        rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
        · omega
        · exact h
      omega
    · obtain ⟨k, hk⟩ := hodd
      omega
  exact Subtype.ext (orderOf_eq_one_iff.mp hn1)

theorem solvableRadical_localGroup (h : ElevenTwoHyp hC) (hF : ElevenTwoFrame hC S T r) :
    (CFSG.solvableRadical (localGroup D (frameE hC r))).map
        (localGroup D (frameE hC r)).subtype =
      Subgroup.zpowers (frameE hC r) := by
  have hO : CFSG.oddCore (localGroup D (frameE hC r)) = ⊥ := oddCore_localGroup h hF
  have h2 : Nat.card (CFSG.pCore 2 (localGroup D (frameE hC r))) = 2 := by
    have hmap := pCore_localGroup h hF
    have hcard := congrArg (fun M : Subgroup G => Nat.card ↥M) hmap
    rw [Subgroup.card_map_of_injective Subtype.coe_injective, Nat.card_zpowers,
      orderOf_frameE h hF] at hcard
    exact hcard
  rw [solvableRadical_eq_pCore_of_oddCore_eq_bot hO h2]
  exact pCore_localGroup h hF

end ElevenTwoFrame

end KOddCore

end CFSG.OddTranspositions.PartThree
