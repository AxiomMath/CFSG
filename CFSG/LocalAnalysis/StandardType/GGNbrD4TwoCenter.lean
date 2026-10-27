module

public import CFSG.LocalAnalysis.StandardType.GGOrthDFourTwoPosition
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylNoLine
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
import CFSG.LocalAnalysis.StandardType.GGTBJConfigFacts
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpBstar
import CFSG.LocalAnalysis.StandardType.GGResOrthogonalExactTwo
import CFSG.LieType.SeitzGeneration.ExcHigh.TwE6FiveSylow
import CFSG.GroupTheory.AllPSubgroupsIsCyclicOfPRankLeOne
import CFSG.GroupTheory.SupCommute
import CFSG.LocalAnalysis.GLTheoremA.CatB.TimmGroup

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly


theorem GGConfig.card_gamma_of_D4two_nbr {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) {y : G} {X : Subgroup G}
    (hnb : GGNbr p B x D J y X) (hRig : GGLabelRigidInput)
    (hmark : GGInnerDiagOnLabel (fun p lab => ggRowP_EOmP p lab ∧ lab.n = 1 ∧ lab.rank = 4) p Bs X)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)) :
    p = 3 ∧ Nat.card (ggGamma X hN).range = 3 ^ 4 := by
  obtain ⟨hp, hBs, -, -, -⟩ := hcfg.tableB_facts
  obtain ⟨lab, -, -, -, -, -, -, -, ⟨⟨-, -, -, hpd⟩, hn, -⟩, -, -⟩ :=
    largeEvenMarking_exists_hasLabel hmark
  have hp3 : p = 3 := by
    rw [hn] at hpd
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hpd
  subst p
  have hact : ∃ b : ↥Bs, ggGamma X hN b ≠ 1 := by
    have h3 := pow_three_le_card_range_ggGamma_bstar hcfg hnb hN
    by_contra hall
    have hbot : (ggGamma X hN).range = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨b, rfl⟩
      rw [Subgroup.mem_bot]
      by_contra hb
      exact hall ⟨b, hb⟩
    rw [hbot, Subgroup.card_bot] at h3
    norm_num at h3
  exact ⟨rfl, OrthTorus.card_range_ggGamma_of_D4two_marking hRig hBs
    hcfg.2.1.2.2.2 hmark hN hact⟩

theorem GGConfig.card_bstar_twoLocalRank_of_D4two_nbr_of_eq {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) {y : G} {X : Subgroup G}
    (hnb : GGNbr p B x D J y X) (hRig : GGLabelRigidInput)
    (hmark : GGInnerDiagOnLabel (fun p lab => ggRowP_EOmP p lab ∧ lab.n = 1 ∧ lab.rank = 4) p Bs X)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)) (hBBs : B = Bs) :
    p = 3 ∧ Nat.card Bs = 3 ^ 5 ∧ LargeEvenTwoLocalRank p G = 5 := by
  subst Bs
  obtain ⟨rfl, hγ⟩ := hcfg.card_gamma_of_D4two_nbr hnb hRig hmark hN
  have hcard : Nat.card B = 3 ^ 5 := by
    rw [← card_range_ggGamma_mul_of_sHat Nat.prime_three hnb.1 hN, hγ]
    norm_num
  refine ⟨rfl, hcard, ?_⟩
  apply Nat.pow_right_injective (by norm_num : 2 ≤ 3)
  exact hcfg.card_B_eq.symm.trans hcard

theorem GGConfig.center_eq_bot_of_D4two_of_lt {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J X : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hlt : B < Bs)
    (hmark : GGInnerDiagOnLabel (fun p lab => ggRowP_EOmP p lab ∧ lab.n = 1 ∧ lab.rank = 4) p Bs X) :
    Subgroup.center ↥X = ⊥ := by
  have hmarkK : GGInnerDiagOn Bs X :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ hP => hP.2) hmark
  obtain ⟨lab, -, hhas, -, -, -, -, -, ⟨⟨⟨htag, -, -, -⟩, -, hr⟩, hN, -⟩⟩ :=
    largeEvenMarking_exists_hasLabel hmark
  have hodd := hcfg.odd_card_center_of_B_lt_Bs hlt hN
  have hcard : Nat.card (Subgroup.center ↥X) = 1 := by
    by_contra hne
    obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hne
    have hq2 : q ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hqd)
    exact OrthKExactTwo.center_not_dvd_of_orthogonal_marking hq hq2 hmarkK hhas
      (Or.inl htag) hr.ge hqd
  exact Subgroup.eq_bot_of_card_eq _ hcard

namespace OrthTorus

theorem exists_elemAbelian_four_of_D4two_marking {G : Type} [Group G] [Finite G]
    {Bs X : Subgroup G} (hRig : GGLabelRigidInput) (hBs : IsElemAbelian 3 Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hmark : GGInnerDiagOnLabel (fun p lab => ggRowP_EOmP p lab ∧ lab.n = 1 ∧ lab.rank = 4) 3 Bs X)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)) (hact : ∃ b : ↥Bs, ggGamma X hN b ≠ 1) :
    ∃ E : Subgroup G, E ≤ X ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hmarkK : GGInnerDiagOn Bs X :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ hP => hP.2) hmark
  obtain ⟨lab, -, hhas, -, -, -, -, -, ⟨⟨⟨htag, -, -, -⟩, -, hr⟩, -, -⟩⟩ :=
    largeEvenMarking_exists_hasLabel hmark
  have hZ : ¬ 3 ∣ Nat.card (Subgroup.center ↥X) :=
    OrthKExactTwo.center_not_dvd_of_orthogonal_marking Nat.prime_three (by decide)
      hmarkK hhas (Or.inl htag) hr.ge
  obtain ⟨F, hField, hFinite, hChar, V, hAdd, hMod, hFinDim, hNontrivial, Q, hQ, σ, ρ,
      -, -, hE, hcard, -⟩ :=
    exists_full_quadratic_image_of_D4two_marking hRig hBs hSC hmark hN hact
  let : Field F := hField
  let : Finite F := hFinite
  let : CharP F 2 := hChar
  let : AddCommGroup V := hAdd
  let : Module F V := hMod
  let : FiniteDimensional F V := hFinDim
  let ψ : ↥X →* ↥(CFSG.RankThree.Classical2.orthDerived Q) :=
    σ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥X))
  have hker : ψ.ker = Subgroup.center ↥X := by
    ext t
    simp [ψ]
  have hψ : Function.Surjective ψ :=
    σ.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center ↥X))
  have hle : ρ.range.map σ.toMonoidHom ≤ ψ.range := by
    rw [MonoidHom.range_eq_top.mpr hψ]
    exact le_top
  obtain ⟨E, hEa, -, hEc⟩ :=
    CFSG.LieType.SeitzGeneration.ExcHigh.TwFive.exists_lift_of_le_range ψ
      (by rwa [hker]) hle hE
  refine ⟨E.map X.subtype, Subgroup.map_subtype_le E, hEa.map X.subtype, ?_⟩
  rw [Subgroup.card_map_of_injective X.subtype_injective, hEc, hcard]

end OrthTorus

theorem GGConfig.pRank_centralizer_le_one_of_D4two_nbr_of_eq_of_center_ne_bot
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) {y : G} {X : Subgroup G}
    (hnb : GGNbr p B x D J y X) (hRig : GGLabelRigidInput)
    (hmark : GGInnerDiagOnLabel (fun p lab => ggRowP_EOmP p lab ∧ lab.n = 1 ∧ lab.rank = 4) p Bs X)
    (hBBs : B = Bs) (hZX : Subgroup.center ↥X ≠ ⊥) :
    CFSG.Open.pRank p (Subgroup.centralizer (X : Set G)) ≤ 1 := by
  classical
  have hmarkK : GGInnerDiagOn Bs X :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ hP => hP.2) hmark
  obtain ⟨lab, -, hhas, -, -, -, -, -, ⟨⟨⟨htag, -, -, -⟩, -, hr⟩, hN, -⟩⟩ :=
    largeEvenMarking_exists_hasLabel hmark
  obtain ⟨rfl, -, hμ⟩ := hcfg.card_bstar_twoLocalRank_of_D4two_nbr_of_eq hnb hRig hmark hN hBBs
  have hBs : IsElemAbelian 3 Bs := hcfg.2.1.2.1
  have hact : ∃ b : ↥Bs, ggGamma X hN b ≠ 1 := by
    have h3 := pow_three_le_card_range_ggGamma_bstar hcfg hnb hN
    by_contra hall
    have hbot : (ggGamma X hN).range = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨b, rfl⟩
      rw [Subgroup.mem_bot]
      by_contra hb
      exact hall ⟨b, hb⟩
    rw [hbot, Subgroup.card_bot] at h3
    norm_num at h3
  obtain ⟨A, hAX, hA, hAc⟩ := OrthTorus.exists_elemAbelian_four_of_D4two_marking
    hRig hBs hcfg.2.1.2.2.2 hmark hN hact
  have hZ3 : ¬ 3 ∣ Nat.card (Subgroup.center ↥X) :=
    OrthKExactTwo.center_not_dvd_of_orthogonal_marking Nat.prime_three (by decide)
      hmarkK hhas (Or.inl htag) hr.ge
  have hcop : Nat.Coprime 3 (Nat.card (Subgroup.center ↥X)) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hZ3
  have hcardZ : Nat.card (Subgroup.center ↥X) ≠ 1 :=
    fun h => hZX (Subgroup.eq_bot_of_card_eq _ h)
  obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hcardZ
  have hq2 : q = 2 := by
    by_contra hq2
    exact OrthKExactTwo.center_not_dvd_of_orthogonal_marking hq hq2
      hmarkK hhas (Or.inl htag) hr.ge hqd
  subst q
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 hqd
  let zg : G := ((z : ↥X) : G)
  have hz2 : zg ^ 2 = 1 := by
    have h : z ^ 2 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
    exact congrArg (fun t : Subgroup.center ↥X => ((t : ↥X) : G)) h
  have hzne : zg ≠ 1 := by
    intro h
    have hz1 : z = 1 := Subtype.ext (Subtype.ext h)
    rw [hz1, orderOf_one] at hz
    omega
  have hzo : orderOf zg = 2 := orderOf_eq_prime hz2 hzne
  obtain ⟨C, hCC, hC, hCc⟩ :=
    CFSG.SectionRank.exists_pRank (by norm_num : 1 < (3 : ℕ)) (Subgroup.centralizer (X : Set G))
  have hcomm : ∀ a ∈ A, ∀ c ∈ C, Commute a c :=
    fun a ha c hc => hCC hc a (hAX ha)
  have hAC : A ⊓ C = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    let t : Subgroup.center ↥X := ⟨⟨a, hAX ha.1⟩,
      Subgroup.mem_center_iff.mpr fun u => Subtype.ext (hCC ha.2 u u.2)⟩
    have ht3 : t ^ 3 = 1 := Subtype.ext (Subtype.ext (hA.2 a ha.1))
    have ht1 : t ^ Nat.gcd 3 (Nat.card (Subgroup.center ↥X)) = 1 :=
      pow_gcd_eq_one.mpr ⟨ht3, pow_card_eq_one' (x := t)⟩
    rw [hcop.gcd_eq_one, pow_one] at ht1
    exact congrArg (fun u : Subgroup.center ↥X => ((u : ↥X) : G)) ht1
  have hsup : IsElemAbelian 3 (A ⊔ C) := hA.sup_of_commute hC fun a ha c hc => (hcomm a ha c hc).eq
  have hsupc := CFSG.card_sup_eq_mul_of_commute A C hcomm hAC
  have hsupz : A ⊔ C ≤ Subgroup.centralizer ({zg} : Set G) := by
    refine sup_le ?_ ?_
    · intro a ha
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp z.2 ⟨a, hAX ha⟩)
    · intro c hc
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hCC hc zg (z : ↥X).2).symm
  have hle := TableB.card_le_of_twoLocal Nat.prime_three
    (CFSG.LocalAnalysis.GLTheoremA.Timm.isTwoLocal_centralizer hzo) hsupz hsup
  rw [hμ, hsupc, hAc, hCc, ← pow_add] at hle
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < (3 : ℕ))).mp hle
  omega

theorem GGConfig.cyclic_p_centralizer_of_D4two_nbr_of_eq_of_center_ne_bot
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) {y : G} {X : Subgroup G}
    (hnb : GGNbr p B x D J y X) (hRig : GGLabelRigidInput)
    (hmark : GGInnerDiagOnLabel (fun p lab => ggRowP_EOmP p lab ∧ lab.n = 1 ∧ lab.rank = 4) p Bs X)
    (hBBs : B = Bs) (hZX : Subgroup.center ↥X ≠ ⊥) :
    ∀ S : Subgroup G, S ≤ Subgroup.centralizer (X : Set G) → IsPGroup p S → IsCyclic S := by
  obtain ⟨hp, -, -, -, -⟩ := hcfg.tableB_facts
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  exact CFSG.all_pSubgroups_isCyclic_of_pRank_le_one hp hp2
    (hcfg.pRank_centralizer_le_one_of_D4two_nbr_of_eq_of_center_ne_bot hnb hRig hmark hBBs hZX)

theorem GGConfig.sStar_of_D4two_nbr_of_eq_of_center_ne_bot
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) {y : G} {X : Subgroup G}
    (hnb : GGNbr p B x D J y X) (hRig : GGLabelRigidInput)
    (hmark : GGInnerDiagOnLabel (fun p lab => ggRowP_EOmP p lab ∧ lab.n = 1 ∧ lab.rank = 4) p Bs X)
    (hBBs : B = Bs) (hZX : Subgroup.center ↥X ≠ ⊥) : LargeEvenSStar p B y X := by
  have hST : LargeEvenStandardType p B x L := hcfg.1.2.2.2.2.2.2.2
  have hcomp := (isComponentOf_of_isNeighborOf hST (isNeighborOf_of_ggNbr hcfg.2.2 hnb)).1
  exact ⟨hnb.1.1, hnb.1.2.1, hnb.1.2.2.1, hcomp,
    hcfg.cyclic_p_centralizer_of_D4two_nbr_of_eq_of_center_ne_bot hnb hRig hmark hBBs hZX⟩

end CFSG.StandardType

end
