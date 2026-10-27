module

public import CFSG.RankThree.PartTwo.Sec13.Item135Simple
import CFSG.RankThree.PartTwo.Sec14.Concl142HJPoint
import CFSG.RankThree.PartTwo.Sec15.Item1514StepsHJ
import CFSG.RankThree.PartTwo.Sec15.Item156ProofType
import CFSG.RankThree.PartTwo.KFacts.KS14HJSignalizer
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.Sporadic.ON
public import CFSG.Adapters.QiuzhenLegacy.FeitThompson.GroupAction.Quotient
public import CFSG.RankThree.PartTwo.Sec15.Item1514Steps1515
public import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofFactor
public import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofPoints
public import CFSG.Sporadic.J2

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

@[expose] def KS1515ONMult : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (Z : Subgroup X) [Z.Normal], Group.IsPerfect X →
    Z ≤ Subgroup.center X → Nat.Coprime 6 (Nat.card Z) →
    Sec4.IsTripleCover (X ⧸ Z) CFSG.Blueprint.NativeSporadic.ON → Z = ⊥

@[expose] noncomputable def Step1515HJListA7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L →
    Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
    ∀ Y ∈ scriptY0Star A (lB A), MeetsY4 A (lB A) L Y →
      (∀ X ∈ scriptY4 A (lB A), X ≤ L ⊓ Y →
        Nat.card (↥X ⧸ CFSG.pPrimeCore 3 ↥X) = 60 ∨
          Nat.card (↥X ⧸ CFSG.pPrimeCore 3 ↥X) = 2520) →
      IsEmpty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 7))

@[expose] noncomputable def Step1515HJListCover : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L →
    Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
    ∀ Y ∈ scriptY0Star A (lB A), MeetsY4 A (lB A) L Y →
      Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* CFSG.Blueprint.NativeSporadic.J2) →
      (∀ X ∈ scriptY4 A (lB A), X ≤ L ⊓ Y →
        Nat.card (↥X ⧸ CFSG.pPrimeCore 3 ↥X) = 60 ∨
          Nat.card (↥X ⧸ CFSG.pPrimeCore 3 ↥X) = 1080 ∨
          Nat.card (↥X ⧸ CFSG.pPrimeCore 3 ↥X) = 2520) →
      ∀ c' : G, Subgroup.zpowers c' ∈ omegaA A → Subgroup.zpowers c' ≠ Subgroup.zpowers c →
        Y = pPrimeCoreOf 3 Y ⊔
          deltaZero A (lB A) (Y ⊓ Subgroup.normalizer (Subgroup.zpowers c' : Set G)) →
        Y = (Y ⊓ L) ⊔ CFSG.Open.pCoreOf 2 Y

namespace Proof1515

variable {G : Type} [Group G] [Finite G]

theorem card_quot_pPrimeCore_dvd {X Q : Type*} [Group X] [Group Q] [Finite X] [Finite Q]
    (f : X →* Q) (hker : Nat.Coprime 3 (Nat.card f.ker)) :
    Nat.card (X ⧸ CFSG.pPrimeCore 3 X) ∣ Nat.card Q := by
  have hle : f.ker ≤ CFSG.pPrimeCore 3 X := le_sSup ⟨f.normal_ker, hker⟩
  have h1 : Nat.card (X ⧸ CFSG.pPrimeCore 3 X) ∣ Nat.card (X ⧸ f.ker) :=
    Subgroup.index_dvd_of_le hle
  have h2 : Nat.card (X ⧸ f.ker) = Nat.card f.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
  exact h1.trans (h2 ▸ Subgroup.card_subgroup_dvd_card _)

theorem card_quot_dvd_card_thetaQuot {X L : Subgroup G} (hXL : X ≤ L) :
    Nat.card (↥X ⧸ CFSG.pPrimeCore 3 ↥X) ∣ Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L) := by
  set θ := aschbacherSolvableCore 3 ↥L with hθ
  set f := (QuotientGroup.mk' θ).comp (Subgroup.inclusion hXL) with hf
  have hmap : f.ker.map (Subgroup.inclusion hXL) ≤ θ := by
    rintro _ ⟨x, hx, rfl⟩
    exact (QuotientGroup.eq_one_iff _).mp hx
  have hdvd : Nat.card f.ker ∣ Nat.card θ := by
    rw [← Subgroup.card_map_of_injective (Subgroup.inclusion_injective hXL)]
    exact Subgroup.card_dvd_of_le hmap
  exact card_quot_pPrimeCore_dvd f (Nat.Coprime.coprime_dvd_right hdvd
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
      CFSG.RankThree.three_not_dvd_card_aschbacherSolvableCore))

theorem card_quot_dvd_card_quot_two {X Y : Subgroup G} (hXY : X ≤ Y) :
    Nat.card (↥X ⧸ CFSG.pPrimeCore 3 ↥X) ∣ Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set f := (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)).comp (Subgroup.inclusion hXY) with hf
  have hK : IsPGroup 2 f.ker := by
    intro x
    have hx : Subgroup.inclusion hXY (x : ↥X) ∈ CFSG.pCore 2 ↥Y := by
      have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥Y) (Subgroup.inclusion hXY (x : ↥X)) = 1 :=
        x.2
      exact (QuotientGroup.eq_one_iff _).mp h1
    obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := 2) (⟨_, hx⟩ : CFSG.pCore 2 ↥Y)
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg (fun z : CFSG.pCore 2 ↥Y => ((z : ↥Y) : G)) hk
    simpa using this
  have hcop : Nat.Coprime 3 (Nat.card f.ker) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hK
    rw [hn]
    exact Nat.Coprime.pow_right _ (by norm_num)
  exact card_quot_pPrimeCore_dvd f hcop

theorem eq_sup_theta_of_cover {K L Y : Subgroup G} (hKL : K ≤ L) (hKY : K ≤ Y)
    (hY : Y = K ⊔ CFSG.Open.pCoreOf 2 Y) (hs : IsSimpleGroup (↥Y ⧸ CFSG.pCore 2 ↥Y))
    (hp : Group.IsPerfect (↥Y ⧸ CFSG.pCore 2 ↥Y))
    (hcard : Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L) ≤ Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y)) :
    L = K ⊔ (aschbacherSolvableCore 3 ↥L).map L.subtype := by
  set θ := aschbacherSolvableCore 3 ↥L with hθ
  set f := (QuotientGroup.mk' θ).comp (Subgroup.inclusion hKL) with hf
  set g := (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)).comp (Subgroup.inclusion hKY) with hg
  have hKN : K ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G) :=
    hKY.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y)
  have hgs : Function.Surjective g := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥Y) q
    have hy : (y : G) ∈ ((K ⊔ CFSG.Open.pCoreOf 2 Y : Subgroup G) : Set G) := by
      rw [← hY]
      exact y.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hKN] at hy
    obtain ⟨k, hk, n, hn, hkn⟩ := Set.mem_mul.mp hy
    obtain ⟨n', hn', rfl⟩ := hn
    refine ⟨⟨k, hk⟩, ?_⟩
    rw [hg, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq]
    have hyn : (Subgroup.inclusion hKY ⟨k, hk⟩)⁻¹ * y = n' := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion]
      rw [← hkn, Subgroup.coe_subtype]
      group
    rw [hyn]
    exact hn'
  have hθs : Group.IsSolvable θ :=
    (solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three).1
  have hker : f.ker ≤ g.ker := by
    have hmap : f.ker.map (Subgroup.inclusion hKL) ≤ θ := by
      rintro _ ⟨x, hx, rfl⟩
      exact (QuotientGroup.eq_one_iff _).mp hx
    have hsolv : Group.IsSolvable f.ker := by
      have : Group.IsSolvable ((f.ker.map (Subgroup.inclusion hKL)).subgroupOf θ) :=
        subgroup_solvable_of_solvable _
      exact Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.subgroupOfEquivOfLe hmap).symm.toMonoidHom.comp
          (f.ker.equivMapOfInjective _ (Subgroup.inclusion_injective hKL)).toMonoidHom)
        ((Subgroup.subgroupOfEquivOfLe hmap).symm.injective.comp
          (f.ker.equivMapOfInjective _ (Subgroup.inclusion_injective hKL)).injective)
    have hn : (f.ker.map g).Normal := f.normal_ker.map g hgs
    rcases hn.eq_bot_or_eq_top with h1 | h1
    · exact (Subgroup.map_eq_bot_iff _).mp h1
    · exfalso
      have hs' : Group.IsSolvable (f.ker.map g) :=
        Group.isSolvable_of_surjective (g.subgroupMap_surjective f.ker)
      have htop : Group.IsSolvable (↥Y ⧸ CFSG.pCore 2 ↥Y) := by
        rw [h1] at hs'
        exact Group.isSolvable_of_surjective (f := (⊤ : Subgroup (↥Y ⧸ CFSG.pCore 2 ↥Y)).subtype)
          (fun x => ⟨⟨x, Subgroup.mem_top x⟩, rfl⟩)
      have := hs.toNontrivial
      exact Group.IsPerfect.not_isSolvable _ htop
  have hfs : Function.Surjective f := by
    have h1 : Nat.card (↥K ⧸ g.ker) ≤ Nat.card (↥K ⧸ f.ker) := card_quotient_le_of_le hker
    have h2 : Nat.card (↥K ⧸ g.ker) = Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) :=
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective g hgs).toEquiv
    have h3 : Nat.card (↥K ⧸ f.ker) = Nat.card f.range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
    have h4 : Nat.card f.range = Nat.card (↥L ⧸ θ) :=
      le_antisymm (Subgroup.card_le_card_group _) (by omega)
    exact MonoidHom.range_eq_top.mp (Subgroup.eq_top_of_card_eq _ h4)
  refine le_antisymm (fun l hl => ?_) (sup_le hKL (Subgroup.map_subtype_le _))
  obtain ⟨x, hx⟩ := hfs (QuotientGroup.mk' θ ⟨l, hl⟩)
  rw [hf, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq] at hx
  have hl' : l = (x : G) * (((Subgroup.inclusion hKL x)⁻¹ * ⟨l, hl⟩ : ↥L) : G) := by simp
  rw [hl']
  exact mul_mem (Subgroup.mem_sup_left x.2) (Subgroup.mem_sup_right ⟨_, hx, rfl⟩)

theorem not_sq_dvd_small {N : ℕ} (hN : N = 60 ∨ N = 1080) {p : ℕ} (hp : p.Prime)
    (hp6 : Nat.Coprime 6 p) : ¬ p ^ 2 ∣ N := by
  have hcheck : ∀ q < 33, Nat.Coprime 6 q → 2 ≤ q → ¬ q ^ 2 ∣ 60 ∧ ¬ q ^ 2 ∣ 1080 := by
    decide
  intro hd
  have hN0 : 0 < N := by rcases hN with rfl | rfl <;> norm_num
  have hle := Nat.le_of_dvd hN0 hd
  have hp33 : p < 33 := by
    by_contra h
    have : 33 ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left (not_lt.mp h) 2
    rcases hN with rfl | rfl <;> omega
  obtain ⟨h1, h2⟩ := hcheck p hp33 hp6 hp.two_le
  rcases hN with rfl | rfl
  · exact h1 hd
  · exact h2 hd

theorem isSimpleGroup_of_mulEquiv_J2 {X : Type*} [Group X]
    (φ : X ≃* CFSG.Blueprint.NativeSporadic.J2) : IsSimpleGroup X := by
  have : IsSimpleGroup CFSG.Blueprint.NativeSporadic.J2 := CFSG.Sporadic.J2.isSimpleGroup_J2
  exact φ.isSimpleGroup

theorem not_isLThreeEpsAt_of_card_j2 {X : Type} [Group X] (hX : Nat.card X = 604800) (p f : ℕ)
    [Fact p.Prime] : ¬ IsLThreeEpsAt X p f :=
  KFacts.KS14.not_isLThreeEpsAt_of_card hX
    (KFacts.KS14.forall_of_forall_lt (by norm_num) (by norm_num) KFacts.KS14.checkSL_j2)
    (KFacts.KS14.forall_of_forall_lt (by norm_num) (by norm_num) KFacts.KS14.checkSU_j2) p f

theorem card_projSL_three_seven [Fact (Nat.Prime 7)] :
    Nat.card (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1)) = 1876896 := by
  have h := KFacts.KS14.card_projSL_three_mul_gcd (GaloisField 7 1)
  rw [GaloisField.card 7 1 (by norm_num)] at h
  norm_num at h
  omega

end Proof1515

open Proof1515


theorem step1515HJList_of
    (h148 : Item148R) (hbot : Item145BotS14) (h142 : Item142R)
    (h134 : Item134) (h48 : Sec4.Item4_8) (h135 : Item135Simple) (hON : KS1515ONMult)
    (hA7 : Step1515HJListA7) (hcov : Step1515HJListCover) : Step1515HJList := by
  intro G _ _ A c L h hJ Y hY hm
  obtain ⟨φL⟩ := hJ
  have hY4 : Y ∈ scriptY4 A (lB A) := hY.prop.1
  have hYΔ := eq_deltaZero_of_mem_scriptY4 hbot h hY4
  have hq := isQuasisimple_quot_pPrimeCore hY4
  have hne := pPrimeCore_ne_top_of_mem_scriptY4 hY4
  have hJc : Nat.card CFSG.Blueprint.NativeSporadic.J2 = 604800 := KFacts.KS14.card_nativeJ2
  have h3J : 3 ∣ Nat.card CFSG.Blueprint.NativeSporadic.J2 := by rw [hJc]; norm_num
  have hLJ : Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L) = 604800 := by
    rw [Nat.card_congr φL.toEquiv, hJc]
  have h3L : 3 ∣ Nat.card L := three_dvd_card_of_mulEquiv φL h3J
  have hnot34 : IsEmpty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃*
      CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2)) := by
    refine ⟨fun ψ => ?_⟩
    have h1 := Nat.card_congr ψ.toEquiv
    rw [hLJ, KFacts.KS14.card_projSL_three_four] at h1
    omega
  have hall := allPointsHJ_of_j2 h134 h48 h.toSec14Std ⟨φL⟩
  have hpt : ∀ (c' : G) (L' : Subgroup G), Subgroup.zpowers c' ∈ omegaA A → L' ∈ lA A c' →
      Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* CFSG.Blueprint.NativeSporadic.J2) := by
    intro c' L' hc' hL'
    obtain ⟨Le, hLe, hJe⟩ := hall c' hc'
    obtain ⟨φe⟩ := hJe
    have h3e : 3 ∣ Nat.card Le :=
      three_dvd_card_of_thetaQuot ((Nat.card_congr φe.toEquiv).symm ▸ h3J)
    have heq := (h.chosen136.2 c' hc' L' hL').2 Le hLe.1 h3e
    rw [← heq]
    exact ⟨φe⟩
  have hptc : ∀ (c' : G) (L' : Subgroup G), Subgroup.zpowers c' ∈ omegaA A → L' ∈ lA A c' →
      Nat.card (↥L' ⧸ aschbacherSolvableCore 3 ↥L') = 604800 := by
    intro c' L' hc' hL'
    obtain ⟨φ'⟩ := hpt c' L' hc' hL'
    rw [Nat.card_congr φ'.toEquiv, hJc]
  have : Nontrivial CFSG.Blueprint.NativeSporadic.J2 := nontrivial_J2
  have hθ : aschbacherSolvableCore 3 ↥L = CFSG.pCore 2 ↥L :=
    theta_eq_pCore_two_of_multFree (h135 G A c L h.toSec13Data (Or.inr (Or.inr ⟨φL⟩))) ⟨φL⟩
      multFree_J2
  have hθO : (aschbacherSolvableCore 3 ↥L).map L.subtype = CFSG.Open.pCoreOf 2 L := by
    rw [hθ]
    rfl
  have hboth : Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* CFSG.Blueprint.NativeSporadic.J2) →
      Y = (Y ⊓ L) ⊔ CFSG.Open.pCoreOf 2 Y →
      Y = (Y ⊓ L) ⊔ CFSG.Open.pCoreOf 2 Y ∧ L = (L ⊓ Y) ⊔ CFSG.Open.pCoreOf 2 L := by
    rintro ⟨φY⟩ hYL
    have hs : IsSimpleGroup (↥Y ⧸ CFSG.pCore 2 ↥Y) := isSimpleGroup_of_mulEquiv_J2 φY
    refine ⟨hYL, ?_⟩
    have hLK := eq_sup_theta_of_cover inf_le_right inf_le_left hYL hs hY4.2.2.2.1
      (by rw [hLJ, Nat.card_congr φY.toEquiv, hJc])
    rw [hθO, inf_comm] at hLK
    exact hLK
  obtain ⟨X₀, hX₀4, hX₀LY⟩ := hm
  have hX5 : ∀ X ∈ scriptY4 A (lB A), X ≤ L ⊓ Y →
      Nat.card (↥X ⧸ CFSG.pPrimeCore 3 ↥X) ∣ 604800 ∧
        Nat.card (↥X ⧸ CFSG.pPrimeCore 3 ↥X) ∈
          ({604800, 1080, 60, 3 * 460815505920, 2520, 1876896} : Set ℕ) := by
    intro X hX4 hXLY
    have hXΔ := eq_deltaZero_of_mem_scriptY4 hbot h hX4
    refine ⟨hLJ ▸ card_quot_dvd_card_thetaQuot (hXLY.trans inf_le_left), ?_⟩
    rcases cases148_of_mem_scriptY4 (h148 G A c L h) h.isElemAbelian.1 hX4 hXΔ with
      ⟨c', hc', -, L', hL', hcases⟩ | ⟨c', L', hc', hL', -, h3⟩ |
        ⟨-, ⟨c', L', hc', hL', ⟨φ7⟩⟩, -⟩ | ⟨c', L', n, m, hc', hL', -, -, -, hε⟩
    · obtain ⟨φJ'⟩ := hpt c' L' hc' hL'
      rcases hcases with hφ | ⟨hL'', -⟩ | ⟨p, f, e, hp, -, -, hiso, -⟩ | ⟨-, h6 | h5⟩
      · obtain ⟨φ⟩ := hφ
        rw [Nat.card_congr (φ.trans φJ').toEquiv, hJc]
        simp
      · exfalso
        rcases hL'' with hM | ⟨_, hφ⟩ | ⟨_, hφ⟩
        · obtain ⟨φM⟩ := hM
          have h1 := hptc c' L' hc' hL'
          rw [Nat.card_congr φM.toEquiv, KFacts.KS14.card_nativeM22] at h1
          omega
        · obtain ⟨φ⟩ := hφ
          exact Proof1514.not_isoLThreePi_of_j2 φJ' (p := 5) (e := 2)
            (Or.inl ⟨by norm_num, ⟨φ⟩⟩)
        · obtain ⟨φ⟩ := hφ
          exact Proof1514.not_isoLThreePi_of_j2 φJ' (p := 5) (e := 1)
            (Or.inr ⟨by norm_num, ⟨φ⟩⟩)
      · exact (Proof1514.not_isoLThreePi_of_j2 φJ' hiso).elim
      · rw [card_of_isTripleCover h6, card_alternatingGroup_six]
        simp
      · obtain ⟨φ⟩ := h5
        rw [Nat.card_congr φ.toEquiv, card_alternatingGroup_five]
        simp
    · rcases h3 with h3 | hφ | ⟨_, hφ⟩
      · rw [card_of_isTripleCover h3, CFSG.Sporadic.ON.card_ON]
        simp
      · obtain ⟨φ⟩ := hφ
        rw [Nat.card_congr φ.toEquiv, card_alternatingGroup_seven]
        simp
      · obtain ⟨φ⟩ := hφ
        rw [Nat.card_congr φ.toEquiv, card_projSL_three_seven]
        simp
    · exfalso
      have h1 := hptc c' L' hc' hL'
      rw [Nat.card_congr φ7.toEquiv, card_alternatingGroup_seven] at h1
      omega
    · exact (not_isLThreeEpsAt_of_card_j2 (hptc c' L' hc' hL') 2 (n * m) hε).elim
  have hX4' : ∀ X ∈ scriptY4 A (lB A), X ≤ L ⊓ Y →
      Nat.card (↥X ⧸ CFSG.pPrimeCore 3 ↥X) = 604800 ∨
        Nat.card (↥X ⧸ CFSG.pPrimeCore 3 ↥X) = 1080 ∨
        Nat.card (↥X ⧸ CFSG.pPrimeCore 3 ↥X) = 60 ∨
        Nat.card (↥X ⧸ CFSG.pPrimeCore 3 ↥X) = 2520 := by
    intro X hX4 hXLY
    obtain ⟨hd, hmem⟩ := hX5 X hX4 hXLY
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with h1 | h1 | h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl h1))
    · rw [h1] at hd
      norm_num at hd
    · exact Or.inr (Or.inr (Or.inr h1))
    · rw [h1] at hd
      norm_num at hd
  rcases cases148_of_mem_scriptY4 (h148 G A c L h) h.isElemAbelian.1 hY4 hYΔ with
    ⟨c', hc', hdec, L', hL', hcases⟩ | ⟨c', L', hc', hL', -, h3⟩ |
      ⟨-, ⟨c', L', hc', hL', ⟨φ7⟩⟩, -⟩ | ⟨c', L', n, m, hc', hL', -, -, -, hε⟩
  · obtain ⟨φJ'⟩ := hpt c' L' hc' hL'
    rcases hcases with hφ | ⟨hL'', -⟩ | ⟨p, f, e, hp, -, -, hiso, -⟩ | ⟨-, h6 | h5⟩
    ·
      obtain ⟨φ⟩ := hφ
      have hO := pPrimeCore_eq_pCore_of_mem_scriptY4 hY4 ⟨φ.trans φJ'⟩ multFree_J2
      have hYJ := nonempty_quot_pCore_two_equiv_of_multFree hY4 ⟨φ.trans φJ'⟩ multFree_J2
      obtain ⟨φY⟩ := hYJ
      refine Or.inr (Or.inr (Or.inr ?_))
      by_cases hbig : ∃ X ∈ scriptY4 A (lB A), X ≤ L ⊓ Y ∧
          Nat.card (↥X ⧸ CFSG.pPrimeCore 3 ↥X) = 604800
      ·
        obtain ⟨X, -, hXLY, hXJ⟩ := hbig
        have hXY : X ≤ Y := hXLY.trans inf_le_right
        have hXL : X ≤ L := hXLY.trans inf_le_left
        have hYX : Y = X ⊔ CFSG.Open.pCoreOf 2 Y := eq_sup_pCoreOf_two_of_card hXY (by
          rw [Nat.card_congr φY.toEquiv, hJc, hXJ])
        have hLX : L = X ⊔ (aschbacherSolvableCore 3 ↥L).map L.subtype :=
          eq_sup_theta_of_card hXL (by rw [hLJ, hXJ])
        constructor
        · refine le_antisymm ?_ (sup_le inf_le_left (CFSG.LieType.BorelTits.pCoreOf_le 2 Y))
          calc Y = X ⊔ CFSG.Open.pCoreOf 2 Y := hYX
            _ ≤ (Y ⊓ L) ⊔ CFSG.Open.pCoreOf 2 Y := sup_le_sup_right (le_inf hXY hXL) _
        · refine le_antisymm ?_ (sup_le inf_le_left (CFSG.LieType.BorelTits.pCoreOf_le 2 L))
          calc L = X ⊔ (aschbacherSolvableCore 3 ↥L).map L.subtype := hLX
            _ = X ⊔ CFSG.Open.pCoreOf 2 L := by rw [hθO]
            _ ≤ (L ⊓ Y) ⊔ CFSG.Open.pCoreOf 2 L := sup_le_sup_right (le_inf hXL hXY) _
      · have hsmall : ∀ X ∈ scriptY4 A (lB A), X ≤ L ⊓ Y →
            Nat.card (↥X ⧸ CFSG.pPrimeCore 3 ↥X) = 60 ∨
              Nat.card (↥X ⧸ CFSG.pPrimeCore 3 ↥X) = 1080 ∨
              Nat.card (↥X ⧸ CFSG.pPrimeCore 3 ↥X) = 2520 := by
          intro X hX4 hXLY
          rcases hX4' X hX4 hXLY with h1 | h1 | h1 | h1
          · exact (hbig ⟨X, hX4, hXLY, h1⟩).elim
          · exact Or.inr (Or.inl h1)
          · exact Or.inl h1
          · exact Or.inr (Or.inr h1)
        by_cases hcc : Subgroup.zpowers c' = Subgroup.zpowers c
        ·
          rw [hcc] at hdec
          have hfac := eq_inf_sup_pPrimeCoreOf_of_item142 h (h142 G A c L h) h3L hnot34 hY4 hdec
          rw [pPrimeCoreOf_eq_pCoreOf_two hO] at hfac
          exact hboth ⟨φY⟩ hfac
        · exact hboth ⟨φY⟩ (hcov G A c L h ⟨φL⟩ Y hY ⟨X₀, hX₀4, hX₀LY⟩ ⟨φY⟩ hsmall c' hc' hcc
            hdec)
    ·
      exfalso
      rcases hL'' with hM | ⟨_, hφ⟩ | ⟨_, hφ⟩
      · obtain ⟨φM⟩ := hM
        have h1 := hptc c' L' hc' hL'
        rw [Nat.card_congr φM.toEquiv, KFacts.KS14.card_nativeM22] at h1
        omega
      · obtain ⟨φ⟩ := hφ
        exact Proof1514.not_isoLThreePi_of_j2 φJ' (p := 5) (e := 2) (Or.inl ⟨by norm_num, ⟨φ⟩⟩)
      · obtain ⟨φ⟩ := hφ
        exact Proof1514.not_isoLThreePi_of_j2 φJ' (p := 5) (e := 1) (Or.inr ⟨by norm_num, ⟨φ⟩⟩)
    ·
      exact (Proof1514.not_isoLThreePi_of_j2 φJ' hiso).elim
    ·
      have hc : Nat.card (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y) = 1080 := by
        rw [card_of_isTripleCover h6, card_alternatingGroup_six]
      have heq := pPrimeCore_three_eq_pCore_two_of_not_sq_dvd hY4.2.2.2 hne
        fun p hp hp6 => hc ▸ not_sq_dvd_small (Or.inr rfl) hp hp6
      exact Or.inr (Or.inl (isTripleCover_congr (QuotientGroup.quotientMulEquivOfEq heq) h6))
    ·
      obtain ⟨φ⟩ := h5
      have hc : Nat.card (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y) = 60 := by
        rw [Nat.card_congr φ.toEquiv, card_alternatingGroup_five]
      have heq := pPrimeCore_three_eq_pCore_two_of_not_sq_dvd hY4.2.2.2 hne
        fun p hp hp6 => hc ▸ not_sq_dvd_small (Or.inl rfl) hp hp6
      exact Or.inl ⟨(QuotientGroup.quotientMulEquivOfEq heq).symm.trans φ⟩
  ·
    rcases h3 with hON' | hφ | ⟨_, hφ⟩
    ·
      have heq := pPrimeCore_three_eq_pCore_two_of hY4.2.2.2 hne fun Z _ hZc hcop ⟨φ⟩ =>
        hON _ Z hY4.2.2.2.1 hZc hcop (isTripleCover_congr φ.symm hON')
      exact Or.inr (Or.inr (Or.inl (isTripleCover_congr (QuotientGroup.quotientMulEquivOfEq heq)
        hON')))
    ·
      exfalso
      obtain ⟨φY⟩ := nonempty_quot_pCore_two_equiv_of_multFree hY4 hφ
        multFree_alternatingGroup_seven
      have hsmall7 : ∀ X ∈ scriptY4 A (lB A), X ≤ L ⊓ Y →
          Nat.card (↥X ⧸ CFSG.pPrimeCore 3 ↥X) = 60 ∨
            Nat.card (↥X ⧸ CFSG.pPrimeCore 3 ↥X) = 2520 := by
        intro X hX4 hXLY
        have hdY := card_quot_dvd_card_quot_two (hXLY.trans inf_le_right)
        rw [Nat.card_congr φY.toEquiv, card_alternatingGroup_seven] at hdY
        rcases hX4' X hX4 hXLY with h1 | h1 | h1 | h1
        · rw [h1] at hdY
          norm_num at hdY
        · rw [h1] at hdY
          norm_num at hdY
        · exact Or.inl h1
        · exact Or.inr h1
      exact (hA7 G A c L h ⟨φL⟩ Y hY ⟨X₀, hX₀4, hX₀LY⟩ hsmall7).false φY
    ·
      exfalso
      obtain ⟨φ⟩ := hφ
      have hL3 : IsLThreePi (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1)) :=
        ⟨7, 1, inferInstance, le_rfl, Or.inl ⟨by norm_num, ⟨MulEquiv.refl _⟩⟩⟩
      obtain ⟨φY⟩ := nonempty_quot_pCore_two_equiv_of_multFree hY4 ⟨φ⟩
        (multFree_of_isLThreePi hL3)
      obtain ⟨hdL, hmem⟩ := hX5 X₀ hX₀4 hX₀LY
      have hdY := card_quot_dvd_card_quot_two (hX₀LY.trans inf_le_right)
      rw [Nat.card_congr φY.toEquiv, card_projSL_three_seven] at hdY
      have hd := Nat.dvd_gcd hdL hdY
      rw [show Nat.gcd 604800 1876896 = 2016 by norm_num] at hd
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      rcases hmem with h1 | h1 | h1 | h1 | h1 | h1 <;> rw [h1] at hd <;> norm_num at hd
  ·
    exfalso
    have h1 := hptc c' L' hc' hL'
    rw [Nat.card_congr φ7.toEquiv, card_alternatingGroup_seven] at h1
    omega
  ·
    exact (not_isLThreeEpsAt_of_card_j2 (hptc c' L' hc' hL') 2 (n * m) hε).elim

end CFSG.RankThree.PartTwo.Sec15
