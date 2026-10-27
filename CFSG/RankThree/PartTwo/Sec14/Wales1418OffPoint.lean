module

public import CFSG.RankThree.PartTwo.Sec14.Wales1418Off
public import CFSG.RankThree.PartTwo.Sec14.Item1413Res2Proof1420
public import CFSG.RankThree.PartTwo.Sec4.Wales430Theta
public import CFSG.RankThree.PartTwo.Sec11.Statements
public import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
public import CFSG.RankThree.PartTwo.KFacts.KFOut3
public import CFSG.RankThree.PartTwo.KFacts.KF1418MJ
import CFSG.RankThree.PartTwo.Sec14.Wales1418OffTools
import CFSG.RankThree.PartTwo.Sec14.Wales1418OffInner
import CFSG.RankThree.PartTwo.Sec14.Item148PtRes2ProofUpper
import CFSG.RankThree.PartTwo.Sec13.Ronan138P5Ambient
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.Sec13.Item13SLTwo
import CFSG.RankThree.PartTwo.Sec13.Item131aAlpha
import CFSG.RankThree.PartTwo.Sec12.Item128Bar
import CFSG.RankThree.PartTwo.Sec6.Item612Core
import CFSG.RankThree.PartTwo.Sec6.Item611Res7ProofKField
import CFSG.RankThree.PartTwo.Sec5.Tools

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Late
  CFSG.GH74.GLS
open CFSG.RankThree.PartTwo.Sec4 (thetaQuotCentralizer)
open scoped commutatorElement

namespace Wales1418Off

variable {G : Type} [Group G] [Finite G]

theorem invTwoBarNontrivial_of_mem {A K R : Subgroup G}
    (hR : R ∈ invariantPiSubgroups K A (piOf 2)) (hRθ : ¬ R ≤ thetaQuotCentralizer K) :
    Sec8.InvTwoBarNontrivial A K := by
  obtain ⟨hRK, hR2, hAR⟩ := (mem_invariantPiSubgroups_piOf_iff Nat.prime_two).mp hR
  refine ⟨(R.subgroupOf K).map (QuotientGroup.mk' (aschbacherSolvableCore 3 K)), ?_, ?_, ?_⟩
  · intro h0
    apply hRθ
    intro r hr
    have hr' : (⟨r, hRK hr⟩ : K) ∈ (QuotientGroup.mk' (aschbacherSolvableCore 3 K)).ker :=
      ((Subgroup.map_eq_bot_iff _).mp h0) (Subgroup.mem_subgroupOf.mpr hr)
    rw [QuotientGroup.ker_mk'] at hr'
    exact Sec6.theta_le_thetaQuotCentralizer K ⟨_, hr', rfl⟩
  · exact (hR2.comap_of_injective K.subtype K.subtype_injective).map _
  · intro τ hτ y hy
    obtain ⟨h, hN, hhA, rfl⟩ := Sec4.mem_autThetaQuot_iff.mp hτ
    obtain ⟨r, hr, rfl⟩ := hy
    refine ⟨K.normalizerMonoidHom ⟨h, hN⟩ r, ?_, rfl⟩
    have hr' : (r : G) ∈ R := Subgroup.mem_subgroupOf.mp hr
    show ((K.normalizerMonoidHom ⟨h, hN⟩ r : K) : G) ∈ R
    rw [Sec4.normalizerMonoidHom_apply_coe]
    exact (Subgroup.mem_normalizer_iff.mp (hAR hhA) r).mp hr'

theorem card_zpowers_sup_eq_nine {A : Subgroup G} (hA : CFSG.Assembly.IsElemAbelian 3 A)
    {e x : G} (heA : e ∈ A) (hxA : x ∈ A) (he1 : e ≠ 1) (hxe : x ∉ Subgroup.zpowers e) :
    Nat.card (Subgroup.zpowers e ⊔ Subgroup.zpowers x : Subgroup G) = 9 := by
  have hcomm : ∀ u ∈ Subgroup.zpowers e, ∀ v ∈ Subgroup.zpowers x, u * v = v * u :=
    fun u hu v hv => congrArg Subtype.val (hA.1.is_comm.comm
      ⟨u, Subgroup.zpowers_le.mpr heA hu⟩ ⟨v, Subgroup.zpowers_le.mpr hxA hv⟩)
  obtain ⟨h1, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm
  have hx1 : x ≠ 1 := fun h => hxe (h ▸ Subgroup.one_mem _)
  have he3 := Sec13.card_zpowers_of_pow_three (hA.2 e heA) he1
  have hx3 := Sec13.card_zpowers_of_pow_three (hA.2 x hxA) hx1
  have hinf : Subgroup.zpowers e ⊓ Subgroup.zpowers x = ⊥ := by
    have hdvd : Nat.card (Subgroup.zpowers e ⊓ Subgroup.zpowers x : Subgroup G) ∣ 3 :=
      hx3 ▸ Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact Subgroup.card_eq_one.mp h
    · exfalso
      have heq : Subgroup.zpowers e ⊓ Subgroup.zpowers x = Subgroup.zpowers x :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h, hx3])
      have hxm : x ∈ Subgroup.zpowers e ⊓ Subgroup.zpowers x := by
        rw [heq]
        exact Subgroup.mem_zpowers x
      exact hxe hxm.1
  rw [hinf, Subgroup.card_bot, mul_one, he3, hx3] at h1
  exact h1

theorem not_starConditionAt_of_not_commutator_le {A K : Subgroup G} {e x : G}
    (hA : Late.IsE27 A) (heA : e ∈ A) (he1 : e ≠ 1) (hK : K ∈ thetaComponentsAt 3 e)
    (hAK : A ≤ Subgroup.normalizer (K : Set G)) (hxA : x ∈ A)
    (hx : ¬ ⁅inSubgroup (aschbacherSolvableCore 3) (K ⊓ Subgroup.centralizer ({x} : Set G)), A⁆ ≤
      inSubgroup (aschbacherSolvableCore 3) K) :
    ¬ StarConditionAt A e := by
  intro hstar
  apply hx
  obtain ⟨hKC, hKθ⟩ := mem_thetaComponentsIn_iff.mp hK
  have hAθ : A ≤ Subgroup.normalizer ((inSubgroup (aschbacherSolvableCore 3) K : Subgroup G) :
      Set G) := fun a ha => Sec6.normalizer_le_normalizer_theta K (hAK ha)
  by_cases hxe : x ∈ Subgroup.zpowers e
  ·
    have hKx : K ≤ Subgroup.centralizer ({x} : Set G) := by
      intro k hk
      have hke : k * e = e * k := Subgroup.mem_centralizer_singleton_iff.mp (hKC hk)
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxe
      exact Subgroup.mem_centralizer_singleton_iff.mpr (Commute.zpow_right hke n)
    rw [inf_eq_left.mpr hKx]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp hAθ
  ·
    set B' := Subgroup.zpowers e ⊔ Subgroup.zpowers x with hB'def
    have hB'9 : Nat.card B' = 9 := card_zpowers_sup_eq_nine hA.1 heA hxA he1 hxe
    have hB' : IsHyperplane A B' :=
      ⟨sup_le (Subgroup.zpowers_le.mpr heA) (Subgroup.zpowers_le.mpr hxA), by rw [hA.2, hB'9]⟩
    have heB' : e ∈ B' := Subgroup.mem_sup_left (Subgroup.mem_zpowers e)
    have hxB' : x ∈ B' := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
    have h1 := Sec14.commutator_theta_le_of_starConditionAt hA heA he1 hstar hB' heB'
    set CB := Subgroup.centralizer (B' : Set G) with hCB
    set D := K ⊓ Subgroup.centralizer ({x} : Set G) with hD
    have hCBe : CB ≤ Subgroup.centralizer ({e} : Set G) :=
      Subgroup.centralizer_le (Set.singleton_subset_iff.mpr heB')
    have hCBx : CB ≤ Subgroup.centralizer ({x} : Set G) :=
      Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hxB')
    have hDCB : D ≤ CB := by
      intro y hy
      have hle : B' ≤ Subgroup.centralizer ({y} : Set G) := by
        refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
        · exact Subgroup.mem_centralizer_singleton_iff.mpr
            (Subgroup.mem_centralizer_singleton_iff.mp (hKC hy.1)).symm
        · exact Subgroup.mem_centralizer_singleton_iff.mpr
            (Subgroup.mem_centralizer_singleton_iff.mp hy.2).symm
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact Subgroup.mem_centralizer_singleton_iff.mp (hle hz)
    have hsn : (D.subgroupOf CB).IsSubnormal := by
      have h := hKθ.2.1.comap (Subgroup.inclusion hCBe)
      convert h using 1
      ext y
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.coe_inclusion, hD,
        Subgroup.mem_inf]
      exact ⟨fun hy => hy.1, fun hy => ⟨hy, hCBx y.2⟩⟩
    have h2 := Sec13.inSubgroup_theta_le_of_isSubnormal hDCB hsn
    have h3 : ⁅inSubgroup (aschbacherSolvableCore 3) D, A⁆ ≤
        inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({e} : Set G)) :=
      (Subgroup.commutator_mono h2 le_rfl).trans h1
    have h4 : ⁅inSubgroup (aschbacherSolvableCore 3) D, A⁆ ≤ K := by
      rw [Subgroup.commutator_le]
      intro t ht a ha
      have htK : t ∈ K := (Sec6.theta_le D ht).1
      have hat : a * t⁻¹ * a⁻¹ ∈ K :=
        (Subgroup.mem_normalizer_iff.mp (hAK ha) t⁻¹).mp (inv_mem htK)
      have e1 : ⁅t, a⁆ = t * (a * t⁻¹ * a⁻¹) := by
        rw [commutatorElement_def]
        group
      rw [e1]
      exact mul_mem htK hat
    exact (le_inf h3 h4).trans (Sec6.Res611Res7.theta_inf_le_theta hKC)

end Wales1418Off

section Off1418

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L S B : Subgroup G} {b : G}
  {E R : Subgroup G}

theorem Off1418.exists_complement
    (h : Off1418 G A c L S B b E R) (h422 : Sec4.Item4_22)
    (h45 : Sec4.Item4_5) (h131 : Item131) (hPGL : Item1412NotPGLR) :
    ∃ Lb ∈ lA A b, 3 ∣ Nat.card Lb ∧ Subgroup.zpowers b ⊔ (A ⊓ Lb) = A ∧
      Subgroup.zpowers b ⊓ (A ⊓ Lb) = ⊥ := by
  have hA := h.isE27
  have hbA := h.b_mem_A
  obtain ⟨Lb, hLb⟩ := Sec12.exists_mem_lA422 h422 h45 h.sec15R.toPartTwoStanding
    h.sec15R.toSec13Data.mem_partTwoF hA.2 h.b_omega
  have hAb : A ≤ Subgroup.centralizer ({b} : Set G) := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hA.1.1.is_comm.comm ⟨y, hy⟩ ⟨b, hbA⟩))
  have hLb' : Lb ∈ lA A b := Sec12.mem_lA_of_mem_lA422 hAb hLb
  have hS := Proof1413.sec14Std_at h.sec15R.toSec14Std h.b_omega hLb'
  have hZ := Item148PtRes2.center_eq_bot_of_sec14 Sec13.sporadicModels131 hS
  have hbL : b ∉ Lb := Sec13.not_mem_of_center_eq_bot hS.toSec13Data hZ
  obtain ⟨-, -, h9 | hP⟩ :=
    Sec13.facts_of_not_mem h131 Sec13.sporadicModels131 Sec13.slTwoCenter hS.toSec13Data hbL
  · refine ⟨Lb, hLb', ?_, (Item148PtRes2.eq_zpowers_sup_of_card hS.toSec13Data hbL h9).symm, ?_⟩
    · have h9d : 9 ∣ Nat.card Lb := h9 ▸ Subgroup.card_dvd_of_le inf_le_right
      exact (show 3 ∣ 9 by norm_num).trans h9d
    · have hb1 : b ≠ 1 := fun h1 => h.b_not_mem_E (h1 ▸ Subgroup.one_mem E)
      have hb3 := Sec13.card_zpowers_of_pow_three (hA.1.2 b hbA) hb1
      have hdvd : Nat.card (Subgroup.zpowers b ⊓ (A ⊓ Lb) : Subgroup G) ∣ 3 :=
        hb3 ▸ Subgroup.card_dvd_of_le inf_le_left
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h1
      · exact Subgroup.card_eq_one.mp h1
      · exfalso
        have heq : Subgroup.zpowers b ⊓ (A ⊓ Lb) = Subgroup.zpowers b :=
          Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h1, hb3])
        have hbm : b ∈ Subgroup.zpowers b ⊓ (A ⊓ Lb) := by
          rw [heq]
          exact Subgroup.mem_zpowers b
        exact hbL hbm.2.2
  · exact (hPGL G A c L h.sec15R h.fail b h.b_gamma Lb hLb' hP).elim

end Off1418

theorem step1418OffPointR_of
    (h422 : Sec4.Item4_22) (h45 : Sec4.Item4_5) (h46 : Sec4.Item4_6) (h131 : Item131)
    (hPGL : Item1412NotPGLR) (h430 : Sec4.Item4_30Theta) (h1134 : Sec11.Item1134E27)
    (hOut : KFacts.KFOut3) (hMJ : KFacts.KF1418MJ) : Step1418OffPointR := by
  intro G _ _ A c L S B b E R h e heE he1 K hK hAK hRK hRKθ hCe
  have hA := h.isE27
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hA.1
  have hA3 : IsPGroup 3 A := Sec5.isPGroup_of_isElemAbelian hAe
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hbA := h.b_mem_A
  have heA : e ∈ A := h.hyperplane_E.1 heE
  have heo : orderOf e = 3 := orderOf_eq_prime (hAe.2 e heA) he1
  have hD := h.sec15R.toSec13Data
  have hst := h.sec15R.toPartTwoStanding
  have hTF := hst.toTheoremFourHyp
  have hEF : partTwoE G = partTwoF G := (hTF.partTwoF_eq_partTwoE hD.partTwoS_eq).1.symm
  have hKp : Group.IsPerfect K := isPerfect_of_mem_thetaComponentsIn hK
  have hKq := Sec6.isQuasisimple_of_mem_thetaComponentsAt hK
  have hCne : Subgroup.centralizer ({e} : Set G) ≠ ⊤ := Sec6.centralizer_ne_top_of_ne_one hTF he1
  have hK46 := Sec13.Ronan138P5.isList46_of_mem_thetaComponentsAt h46 heo
    (hTF.sectionFourHyp hCne) hK
  obtain ⟨R', hR', -, hR'b, hR'θ⟩ := Wales1418Off.exists_inner_twoSubgroup_of_kfOut3 hOut hKp hKq
    hK46 hA3 hcomm hAK hbA h.R_two h.A_le_R hRK h.R_comm hRKθ
  obtain ⟨Lb, hLb, hLb3, hsup, hinf⟩ := h.exists_complement h422 h45 h131 hPGL
  have hKC : K ≤ Subgroup.centralizer ({e} : Set G) := le_centralizer_of_mem_thetaComponentsAt hK
  have hAC : A ≤ Subgroup.centralizer ({e} : Set G) := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm y hy e heA)
  have hS4 : SectionFourHyp ↥(K ⊔ A) := hTF.sectionFourHyp fun htop =>
    hCne (top_le_iff.mp (htop ▸ sup_le hKC hAC))
  have hbe : b ∉ Subgroup.zpowers e := fun hb =>
    h.b_not_mem_E (Subgroup.zpowers_le.mpr heE hb)
  rcases h430 G K A e b (A ⊓ Lb) R' hS4 hEF hKp hKq hA hAK
      h.sec15R.toSec14Std.maximal_isElemAbelian hCe heo hbA hbe hsup hinf h.normalizer_b
      (h.normalizer_inf Lb hLb hLb3) hR' hR'θ hR'b with ⟨x, hxA, hk⟩ | hMJ'
  ·
    have hKstar : K ∈ lStarAt A e :=
      ⟨Wales1418Off.mem_lStar_of_inf_le_zpowers heA he1 (fun y hy => hAe.2 y hy) hK hAK hCe.le,
        hK⟩
    have hsec : Late.sectionCentralizer A K ((aschbacherSolvableCore 3 K).map K.subtype) =
        (Subgroup.zpowers e : Set G) := by
      rw [Sec13.sectionCentralizer_eq_inf hAK, hCe]
    have hinv := Wales1418Off.invTwoBarNontrivial_of_mem hR' hR'θ
    obtain ⟨hf, hg⟩ := h1134 G A e K hst hD.mem_partTwoF hD.not_mem_partTwoT hA.2 heA he1 hKstar
      hsec (Or.inl ⟨A, hD.mem_partTwoE, le_rfl, hinv⟩) (fun _ => hEF) x hxA
    rcases hk with hk | hk
    · exact hf hk
    · exact hg hk
  ·
    obtain ⟨x, hxA, hx⟩ := hMJ G K A R' e hMJ' hAe hA.2 hAK hCe hR' hR'θ
    have hnot := Wales1418Off.not_starConditionAt_of_not_commutator_le hA heA he1 hK hAK hxA hx
    exact h.off _ (zpowers_mem_omegaA_iff.mpr ⟨heA,
      Sec13.card_zpowers_of_pow_three (hAe.2 e heA) he1, hnot⟩) (Subgroup.zpowers_le.mpr heE)

end CFSG.RankThree.PartTwo.Sec14
