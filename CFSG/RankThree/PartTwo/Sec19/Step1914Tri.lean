module

public import CFSG.RankThree.PartTwo.Sec19.Step1914Split
public import CFSG.RankThree.PartTwo.Sec19.Step1914TriSeitz
import CFSG.RankThree.PartTwo.Sec19.Step1914E
import CFSG.RankThree.PartTwo.KFacts.KS18L34GenProof
import CFSG.RankThree.PartTwo.KFacts.K72SylowL3
public import CFSG.RankThree.PartTwo.Sec12.Item125Act
import CFSG.RankThree.PartTwo.Sec12.Item123Inputs
import CFSG.RankThree.PartOne.S9.Vanishing.Basic
import CFSG.RankThree.PartOne.KC.LinearSubfieldPointwise
import CFSG.RankThree.PartTwo.Sec4.Item413Setup
import CFSG.RankThree.PartTwo.Sec4.Item47Bridges
import CFSG.RankThree.PartTwo.Sec13.Item13Models
import CFSG.RankThree.PartTwo.Sec13.Item13Theta
import CFSG.RankThree.PartTwo.Sec15.HypR
import CFSG.RankThree.PartTwo.Sec18.Transport
import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
import CFSG.RankThree.PartTwo.Census.Classical.Bridges
import CFSG.ClassicalGroups.Unitary.Simple
import CFSG.RankThree.PartTwo.Sec21.Item222ProofCases
import CFSG.Models.PGLSimple
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec18
open CFSG.Assembly.RankThreeEven (projSL projSU)

namespace Step1914TriProof

section Simple

theorem isSimpleGroup_projSL_three_of_field (F : Type) [Field F] :
    IsSimpleGroup (projSL 3 F) :=
  CFSG.RankThree.PartTwo.Sec21.Item222Proof.isSimpleGroup_projSL_three F

theorem isSimpleGroup_projSU_three_of_ne_two (p e : ℕ) [Fact p.Prime] (he : 1 ≤ e)
    (hq : p ^ e ≠ 2) : IsSimpleGroup (projSU 3 p e) :=
  CFSG.PGLModel.isSimpleGroup_projSU_of_admissible ⟨Fact.out, he, le_rfl, fun h => hq (Prod.mk.inj h).2⟩

theorem three_dvd_card_of_isoLThreePi {X : Type} [Group X] {p e : ℕ} [Fact p.Prime]
    (he : 1 ≤ e) (h : Sec4.IsoLThreePi X p e) : 3 ∣ Nat.card X := by
  rcases h with ⟨-, ⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩
  · exact KFacts.three_dvd_card_of_mulEquiv_projSL φ
  · exact KFacts.three_dvd_card_of_mulEquiv_projSU (by omega) φ

theorem isSimpleGroup_of_isoLThreePi {X : Type} [Group X] [Finite X] {p e : ℕ} [Fact p.Prime]
    (he : 1 ≤ e) [Group.IsPerfect X] (h : Sec4.IsoLThreePi X p e) :
    IsSimpleGroup X ∧ p ^ e ≠ 2 := by
  have h3 := three_dvd_card_of_isoLThreePi he h
  have : Nontrivial X := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    have := Nat.le_of_dvd Nat.card_pos h3
    omega
  rcases h with ⟨hq, ⟨φ⟩⟩ | ⟨hq, ⟨φ⟩⟩
  · have := isSimpleGroup_projSL_three_of_field (GaloisField p e)
    refine ⟨φ.isSimpleGroup, fun h2 => ?_⟩
    rw [h2] at hq
    norm_num at hq
  · have hq2 : p ^ e ≠ 2 := by
      intro h2
      obtain ⟨rfl, rfl⟩ := (Nat.prime_two.pow_eq_iff).mp h2
      have := isSolvable_projSU_two
      have hsolv : Group.IsSolvable X :=
        Group.isSolvable_of_surjective (f := φ.symm.toMonoidHom) φ.symm.surjective
      exact Group.IsPerfect.not_isSolvable X hsolv
    have := isSimpleGroup_projSU_three_of_ne_two p e he hq2
    exact ⟨φ.isSimpleGroup, hq2⟩

theorem center_eq_bot_of_isSimpleGroup_of_isPerfect {X : Type*} [Group X] [IsSimpleGroup X]
    [Group.IsPerfect X] : Subgroup.center X = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
  · exact h
  · exfalso
    have hc : IsMulCommutative X := ⟨⟨fun a b => by
      have ha : a ∈ Subgroup.center X := h ▸ Subgroup.mem_top a
      exact (Subgroup.mem_center_iff.mp ha b).symm⟩⟩
    exact Group.IsPerfect.not_isMulCommutative X hc

theorem theta_eq_pCore_two_of_isSimpleGroup {I : Type} [Group I] [Finite I]
    [IsSimpleGroup (I ⧸ CFSG.pCore 2 I)] [Group.IsPerfect (I ⧸ CFSG.pCore 2 I)] :
    aschbacherSolvableCore 3 I = CFSG.pCore 2 I := by
  refine theta_eq_pCore_two_of_solvable fun N hN hs => ?_
  have := hN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · exact h
  · exfalso
    subst h
    have hsolv : Group.IsSolvable (I ⧸ CFSG.pCore 2 I) :=
      Group.isSolvable_of_surjective
        (f := ((Subgroup.topEquiv : (⊤ : Subgroup (I ⧸ CFSG.pCore 2 I)) ≃*
          (I ⧸ CFSG.pCore 2 I)) : (⊤ : Subgroup (I ⧸ CFSG.pCore 2 I)) →* (I ⧸ CFSG.pCore 2 I)))
        Subgroup.topEquiv.surjective
    exact Group.IsPerfect.not_isSolvable (I ⧸ CFSG.pCore 2 I) hsolv

end Simple

section Abstract

theorem conj_injective_of_center_eq_bot' {X : Type*} [Group X] (h : Subgroup.center X = ⊥) :
    Function.Injective (MulAut.conj : X →* MulAut X) := by
  intro x y hxy
  have hc : y⁻¹ * x ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro z
    have h1 := congrArg (fun σ : MulAut X => σ z) hxy
    simp only [MulAut.conj_apply] at h1
    calc z * (y⁻¹ * x) = y⁻¹ * (y * z * y⁻¹) * x := by group
      _ = y⁻¹ * (x * z * x⁻¹) * x := by rw [h1]
      _ = y⁻¹ * x * z := by group
  rw [h, Subgroup.mem_bot] at hc
  exact (inv_mul_eq_one.mp hc).symm

theorem card_map_mul_card_ker_subgroupOf {X Y : Type*} [Group X] [Group Y] [Finite X]
    (f : X →* Y) (H : Subgroup X) :
    Nat.card (H.map f) * Nat.card (f.ker.subgroupOf H) = Nat.card H := by
  have h1 := Subgroup.card_mul_index (f.comp H.subtype).ker
  rw [Subgroup.index_ker, MonoidHom.range_comp, Subgroup.range_subtype] at h1
  rw [mul_comm, ← h1]
  rfl

theorem eq_one_of_mem_theta' {I : Type} [Group I] [Finite I] {x : I}
    (hx : x ∈ aschbacherSolvableCore 3 I) {k : ℕ} (hk : x ^ 3 ^ k = 1) : x = 1 := by
  have hθ := solvable_prime_complement_core_characterization (H := I) Nat.prime_three
  have h2 : orderOf x ∣ Nat.card (aschbacherSolvableCore 3 I) := by
    have := orderOf_dvd_natCard (⟨x, hx⟩ : aschbacherSolvableCore 3 I)
    rwa [Subgroup.orderOf_mk] at this
  have hcop : Nat.Coprime (3 ^ k) (Nat.card (aschbacherSolvableCore 3 I)) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hθ.2.2.1)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hk) h2)

end Abstract

variable {G : Type} [Group G] [Finite G]

theorem nine_le_card_of_mem_of_not_mem {E B : Subgroup G} (hE : IsE27 E) (hBE : B ≤ E) {c x : G}
    (hc : orderOf c = 3) (hcB : c ∈ B) (hxB : x ∈ B) (hxc : x ∉ Subgroup.zpowers c) :
    9 ≤ Nat.card B := by
  have hdvd : Nat.card B ∣ 3 ^ 3 := by
    rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hE.2]
    exact Subgroup.card_dvd_of_le hBE
  obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  have h3 : 3 ∣ Nat.card B := by
    rw [← hc, ← Nat.card_zpowers]
    exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hcB)
  interval_cases k
  · rw [hk] at h3
    norm_num at h3
  · exfalso
    apply hxc
    have heq : Subgroup.zpowers c = B :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hcB)
        (by rw [hk, Nat.card_zpowers, hc]; norm_num)
    exact heq ▸ hxB
  · rw [hk]; norm_num
  · rw [hk]; norm_num

theorem eq_zpowers_sup_of_nine_le {E L : Subgroup G} (hE : IsE27 E) {c : G} (hcE : c ∈ E)
    (hcL : c ∉ L) (h9 : 9 ≤ Nat.card (E ⊓ L : Subgroup G)) :
    E = Subgroup.zpowers c ⊔ (E ⊓ L) := by
  have hdvd : Nat.card (E ⊓ L : Subgroup G) ∣ 3 ^ 3 := by
    rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hE.2]
    exact Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  have hne : Nat.card (E ⊓ L : Subgroup G) ≠ 27 := by
    intro h27
    have heq : E ⊓ L = E := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h27, hE.2])
    have hc' : c ∈ E ⊓ L := by rw [heq]; exact hcE
    exact hcL hc'.2
  have h9' : Nat.card (E ⊓ L : Subgroup G) = 9 := by
    interval_cases k <;> simp_all
  exact (Sec12.eq_of_card_nine_lt hE.2 (sup_le (Subgroup.zpowers_le.mpr hcE) inf_le_left)
    le_sup_right h9' (Subgroup.mem_sup_left (Subgroup.mem_zpowers c)) (fun h => hcL h.2)).symm

theorem zpowers_inf_eq_bot_of_not_mem {c : G} (hc : orderOf c = 3) {K : Subgroup G}
    (hcK : c ∉ K) : Subgroup.zpowers c ⊓ K = ⊥ := by
  have hdvd : Nat.card (Subgroup.zpowers c ⊓ K : Subgroup G) ∣ 3 := by
    rw [← hc, ← Nat.card_zpowers]
    exact Subgroup.card_dvd_of_le inf_le_left
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
  · exact Subgroup.card_eq_one.mp h1
  · exfalso
    have heq : Subgroup.zpowers c ⊓ K = Subgroup.zpowers c :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h3, Nat.card_zpowers, hc])
    have hc' : c ∈ Subgroup.zpowers c ⊓ K := by rw [heq]; exact Subgroup.mem_zpowers c
    exact hcK hc'.2

theorem normalizer_zpowers_le_of_three_dvd {A L E M : Subgroup G} {c : G}
    (hctx : Ctx1912 G A c L E M) (hL3 : 3 ∣ Nat.card L) :
    Subgroup.normalizer (Subgroup.zpowers c : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  have hFE : partTwoF G = partTwoE G :=
    (hctx.toTheoremFourHyp.partTwoF_eq_partTwoE hctx.partTwoS_eq).1
  have hD : Sec13Data G A c L := ⟨hctx.toPartTwoStanding, hctx.partTwoS_eq,
    hFE ▸ hctx.mem_partTwoE, hctx.not_mem_partTwoT, hctx.zpowers_mem_omegaA, hctx.mem_lA⟩
  have hLc : L ∈ thetaComponentsAt 3 c := hD.mem_thetaComponentsAt
  have huniq := (hctx.chosen136.2 c hctx.zpowers_mem_omegaA L hctx.mem_lA).2
  intro h hh
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hmem := map_mem_thetaComponentsAt (MulAut.conj h) hLc
  have hhc : h * c * h⁻¹ ∈ Subgroup.zpowers c :=
    (Subgroup.mem_normalizer_iff.mp hh c).mp (Subgroup.mem_zpowers c)
  have hzp : Subgroup.zpowers (h * c * h⁻¹) = Subgroup.zpowers c := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hhc) ?_
    rw [Nat.card_zpowers, Nat.card_zpowers]
    exact ((MulAut.conj h).orderOf_eq c).ge
  have hθc : thetaComponentsAt 3 (h * c * h⁻¹) = thetaComponentsAt 3 c := by
    rw [thetaComponentsAt_eq_thetaComponentsIn, thetaComponentsAt_eq_thetaComponentsIn,
      centralizer_singleton_eq_of_zpowers_eq hzp]
  have hmem' : L.map (MulAut.conj h).toMonoidHom ∈ thetaComponentsAt 3 c := by
    rw [← hθc]
    exact hmem
  exact huniq _ hmem'
    (by rw [Subgroup.card_map_of_injective (MulAut.conj h).injective]; exact hL3)

theorem le_gamma_of_closure_eq_top {E L : Subgroup G} (hE : IsE27 E)
    (hEN : E ≤ Subgroup.normalizer (L : Set G))
    (hgen : Subgroup.closure {k : L ⧸ aschbacherSolvableCore 3 L | ∃ B : Subgroup G, B ≤ E ∧
      2 ≤ CFSG.Open.pRank 3 B ∧ ∀ b ∈ B, ∀ hb : b ∈ Subgroup.normalizer (L : Set G),
        Sec12.thetaBarAct L ⟨b, hb⟩ k = k} = ⊤) :
    L ≤ gamma 2 E := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set θL := aschbacherSolvableCore 3 L with hθL
  have hθ := solvable_prime_complement_core_characterization (H := L) Nat.prime_three
  have hΘ : θL.map L.subtype ≤ gamma 2 E := by
    have hEab := Sec4.isElementaryAbelian_of_isElemAbelian hE.1
    refine PartOne.Vanish.le_of_forall_hyperplane_inf_centralizer_le Nat.prime_three hEab
      (by rw [hE.2]; norm_num) ?_ ?_ ?_
    · exact hEN.trans
        (GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_aschbacherSolvableCore 3 L)
    · rw [Subgroup.card_map_of_injective L.subtype_injective]
      exact hθ.2.2.1
    · intro D hDE hD9
      refine inf_le_right.trans ((Subgroup.centralizer_le_normalizer _).trans
        (normalizer_le_gamma hDE ?_))
      exact two_le_pRank_of_elemAbelian (isElemAbelian_of_le hE.1 hDE) (by rw [hD9]; norm_num)
  have hY : ((gamma 2 E).subgroupOf L).map (QuotientGroup.mk' θL) = ⊤ := by
    rw [eq_top_iff, ← hgen, Subgroup.closure_le]
    rintro k ⟨B, hBE, hB2, hfix⟩
    obtain ⟨y, hy, hyc⟩ := Sec12.exists_lift_fixed (hE.isPGroup.to_le hBE) (hBE.trans hEN) k
      (fun d hd => hfix d hd _)
    refine ⟨y, ?_, hy⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
    have hyC : (y : G) ∈ Subgroup.centralizer (B : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      have h1 := hyc b hb
      calc b * (y : G) = b * y * b⁻¹ * b := by group
        _ = y * b := by rw [h1]
    exact normalizer_le_gamma hBE hB2 (Subgroup.centralizer_le_normalizer _ hyC)
  intro x hx
  have hxY : QuotientGroup.mk' θL (⟨x, hx⟩ : L) ∈
      ((gamma 2 E).subgroupOf L).map (QuotientGroup.mk' θL) := hY ▸ Subgroup.mem_top _
  obtain ⟨y, hy, hyx⟩ := hxY
  rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hy
  have h1 : y⁻¹ * ⟨x, hx⟩ ∈ θL := QuotientGroup.eq.mp hyx
  have h2 : ((y⁻¹ * ⟨x, hx⟩ : L) : G) ∈ gamma 2 E := hΘ ⟨_, h1, rfl⟩
  have h3 : x = (y : G) * ((y⁻¹ * ⟨x, hx⟩ : L) : G) := by simp
  rw [h3]
  exact (gamma 2 E).mul_mem hy h2

end Step1914TriProof

open Step1914TriProof in
theorem rank3II_19_14Tri_of (h1913 : Step1913) (hS : SeitzL3Pi) : Step1914Tri := by
  intro G _ _ A c L E M hctx
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases h1913 G A c L E M hctx with hL3 | hM12
  swap
  · exact Or.inr (Or.inr hM12)
  have hst := hctx.toPartTwoStanding
  have hEE : E ∈ partTwoE G := hctx.mem_partTwoT.1
  have hE := isE27_of_mem_partTwoE hEE
  have hcA : c ∈ A := hctx.zpowers_mem_omegaA.1 (Subgroup.mem_zpowers c)
  have hcE : c ∈ E := mem_of_le_centralizer hst hctx.partTwoS_eq hEE
    (hctx.mem_partTwoE.1.2 c hcA) hctx.le_centralizer
  have hcL : c ∉ L := hctx.hypS.2.2 c hctx.zpowers_mem_omegaA L hctx.mem_lA
  have hc3 : orderOf c = 3 := by
    rw [← Nat.card_zpowers]
    exact hctx.zpowers_mem_omegaA.2.1
  obtain ⟨p, e, hp, he, hiso⟩ := hL3
  have hLperf : Group.IsPerfect L := isPerfect_of_mem_thetaComponentsIn hctx.mem_lA.1
  obtain ⟨hXs, hq2⟩ := isSimpleGroup_of_isoLThreePi he hiso
  have h3L : 3 ∣ Nat.card L :=
    (three_dvd_card_of_isoLThreePi he hiso).trans (Subgroup.card_quotient_dvd_card _)
  have hEN : E ≤ Subgroup.normalizer (L : Set G) :=
    (hctx.le_centralizer.trans (centralizer_le_normalizer_zpowers c)).trans
      (normalizer_zpowers_le_of_three_dvd hctx h3L)
  have hθeq : aschbacherSolvableCore 3 L = CFSG.pCore 2 L :=
    theta_eq_pCore_two_of_isSimpleGroup
  set θL := aschbacherSolvableCore 3 L with hθL
  set X := L ⧸ θL with hX
  set ι : L ⧸ CFSG.pCore 2 L ≃* X := QuotientGroup.quotientMulEquivOfEq hθeq.symm with hι
  have hisoX : Sec4.IsoLThreePi X p e := by
    rcases hiso with ⟨hq', ⟨φ⟩⟩ | ⟨hq', ⟨φ⟩⟩
    · exact Or.inl ⟨hq', ⟨ι.symm.trans φ⟩⟩
    · exact Or.inr ⟨hq', ⟨ι.symm.trans φ⟩⟩
  have : IsSimpleGroup X := ι.symm.isSimpleGroup
  have : Group.IsPerfect X := inferInstance
  have hZX : Subgroup.center X = ⊥ := center_eq_bot_of_isSimpleGroup_of_isPerfect
  set N := Subgroup.normalizer (L : Set G) with hN
  set ρ : N →* MulAut X := Sec12.thetaBarAct L with hρ
  set E' := E.subgroupOf N with hE'
  set Eb : Subgroup (MulAut X) := E'.map ρ with hEb
  have hE'E := isE27_subgroupOf hE hEN
  have hEbab : CFSG.Assembly.IsElemAbelian 3 Eb := Sec4.isElemAbelian_map ρ hE'E.1
  have hEbab' : CFSG.IsElementaryAbelian 3 Eb := Sec4.isElementaryAbelian_of_isElemAbelian hEbab
  have hcount := card_map_mul_card_ker_subgroupOf ρ E'
  rw [hE'E.2] at hcount
  have hcN : c ∈ N := hEN hcE
  have hρc : ρ ⟨c, hcN⟩ = 1 := by
    have hsc : c ∈ sectionCentralizer A L (θL.map L.subtype) := by
      rw [hctx.mem_lA.2.2.1]
      exact Subgroup.mem_zpowers c
    ext q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective θL q
    rw [MulAut.one_apply, hρ, Sec12.thetaBarAct_mk, QuotientGroup.mk'_apply,
      QuotientGroup.mk'_apply, QuotientGroup.eq_iff_div_mem]
    obtain ⟨z, hz, hzeq⟩ := hsc.2 y y.2
    have hz' : z = L.normalizerMonoidHom ⟨c, hcN⟩ y / y := by
      apply Subtype.ext
      rw [Subgroup.coe_div, Sec4.normalizerMonoidHom_apply_coe, div_eq_mul_inv]
      exact hzeq
    rw [← hz']
    exact hz
  have key : Subgroup.closure {k : X | ∃ B : Subgroup G, B ≤ E ∧ 2 ≤ CFSG.Open.pRank 3 B ∧
      ∀ b ∈ B, ∀ hb : b ∈ N, ρ ⟨b, hb⟩ k = k} = ⊤ → L ≤ M :=
    fun h => (le_gamma_of_closure_eq_top hE hEN h).trans hctx.mem_scriptM.2
  have hFB : Subgroup.closure {k : X | ∃ F : Subgroup (MulAut X), F ≤ Eb ∧ F ≠ ⊥ ∧
      ∀ φ ∈ F, φ k = k} = ⊤ → Subgroup.closure {k : X | ∃ B : Subgroup G, B ≤ E ∧
      2 ≤ CFSG.Open.pRank 3 B ∧ ∀ b ∈ B, ∀ hb : b ∈ N, ρ ⟨b, hb⟩ k = k} = ⊤ := by
    intro hgen
    rw [eq_top_iff, ← hgen]
    refine Subgroup.closure_mono ?_
    rintro k ⟨F, hFE, hF1, hFk⟩
    set B : Subgroup G := (F.comap ρ).map N.subtype ⊓ E with hB
    refine ⟨B, inf_le_right, ?_, ?_⟩
    · obtain ⟨⟨φ, hφF⟩, hφ1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hF1
      have hφ1' : φ ≠ 1 := fun h => hφ1 (Subtype.ext h)
      obtain ⟨ê, hêE, hêφ⟩ := hFE hφF
      have hcB : c ∈ B :=
        ⟨⟨⟨c, hcN⟩, (show ρ ⟨c, hcN⟩ ∈ F by rw [hρc]; exact F.one_mem), rfl⟩, hcE⟩
      have hêB : (ê : G) ∈ B :=
        ⟨⟨ê, (show ρ ê ∈ F by rw [hêφ]; exact hφF), rfl⟩, Subgroup.mem_subgroupOf.mp hêE⟩
      have hêc : (ê : G) ∉ Subgroup.zpowers c := by
        intro hmem
        obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hmem
        have hêeq : ê = (⟨c, hcN⟩ : N) ^ j :=
          Subtype.ext (by rw [Subgroup.coe_zpow]; exact hj.symm)
        apply hφ1'
        rw [← hêφ, hêeq, map_zpow, hρc, one_zpow]
      exact two_le_pRank_of_elemAbelian (isElemAbelian_of_le hE.1 inf_le_right)
        (nine_le_card_of_mem_of_not_mem hE inf_le_right hc3 hcB hêB hêc)
    · rintro b ⟨⟨n, hn, hnb⟩, -⟩ hb
      have : (⟨b, hb⟩ : N) = n := Subtype.ext hnb.symm
      rw [this]
      exact hFk _ hn
  have hfix : Subgroup.closure {x : X | ∃ φ ∈ Eb, φ ≠ 1 ∧ φ x = x} = ⊤ → L ≤ M := by
    intro h
    refine key (hFB ?_)
    rw [eq_top_iff, ← h]
    refine Subgroup.closure_mono ?_
    rintro x ⟨φ, hφ, hφ1, hφx⟩
    refine ⟨Subgroup.zpowers φ, Subgroup.zpowers_le.mpr hφ, fun hbot => hφ1 ?_, ?_⟩
    · have h1 : φ ∈ Subgroup.zpowers φ := Subgroup.mem_zpowers φ
      rw [hbot] at h1
      exact Subgroup.mem_bot.mp h1
    · intro ψ hψ
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hψ
      have hs : φ ∈ MulAction.stabilizer (MulAut X) x := hφx
      exact MulAction.mem_stabilizer_iff.mp (zpow_mem hs k)
  by_cases hcyc : IsCyclic Eb
  ·
    left
    apply key
    rw [eq_top_iff]
    intro k _
    apply Subgroup.subset_closure
    refine ⟨((ρ.ker.subgroupOf E').map E'.subtype).map N.subtype, ?_, ?_, ?_⟩
    · rintro _ ⟨_, ⟨z, -, rfl⟩, rfl⟩
      exact Subgroup.mem_subgroupOf.mp z.2
    · refine two_le_pRank_of_elemAbelian (isElemAbelian_of_le hE.1 ?_) ?_
      · rintro _ ⟨_, ⟨z, -, rfl⟩, rfl⟩
        exact Subgroup.mem_subgroupOf.mp z.2
      · have hEbd : Nat.card Eb ∣ 3 := by
          rw [← IsCyclic.exponent_eq_card]
          exact CFSG.IsElementaryAbelian.exponent_dvd_p 3 Eb
        rw [Subgroup.card_map_of_injective N.subtype_injective,
          Subgroup.card_map_of_injective E'.subtype_injective]
        have hpos : 0 < Nat.card (ρ.ker.subgroupOf E') := Nat.card_pos
        rcases (Nat.dvd_prime Nat.prime_three).mp hEbd with h1 | h3
        · rw [h1] at hcount
          omega
        · rw [h3] at hcount
          omega
    · rintro b ⟨_, ⟨z, hz, rfl⟩, rfl⟩ hb
      have hz' : ρ (z : N) = 1 := hz
      have : (⟨_, hb⟩ : N) = (z : N) := rfl
      rw [this, hz', MulAut.one_apply]
  have hEb9 : Nat.card Eb = 9 := by
    have hcmem : (⟨⟨c, hcN⟩, Subgroup.mem_subgroupOf.mpr hcE⟩ : E') ∈ ρ.ker.subgroupOf E' := by
      rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
      exact hρc
    have h3k : 3 ∣ Nat.card (ρ.ker.subgroupOf E') := by
      have hord : orderOf (⟨_, hcmem⟩ : ρ.ker.subgroupOf E') = 3 := by
        rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, Subgroup.orderOf_mk]
        exact hc3
      have h1 := orderOf_dvd_natCard (⟨_, hcmem⟩ : ρ.ker.subgroupOf E')
      rwa [hord] at h1
    obtain ⟨m, hm⟩ := h3k
    rw [hm] at hcount
    have hEbdvd : Nat.card Eb ∣ 3 ^ 2 := ⟨m, by
      have h' : 3 * (Nat.card Eb * m) = 27 := by rw [← hcount]; ring
      omega⟩
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hEbdvd
    interval_cases k
    · exfalso
      rw [pow_zero] at hk'
      exact hcyc (@isCyclic_of_subsingleton Eb _ (Nat.card_eq_one_iff_unique.mp hk').1)
    · exfalso
      rw [pow_one] at hk'
      exact hcyc (isCyclic_of_prime_card hk')
    · rw [hk']
      norm_num
  by_cases h4 : p ^ e = 4
  swap
  · exact Or.inl (hfix (hS X p e he hisoX hq2 h4 Eb hEbab hEb9))
  have hp2 : p = 2 := by
    have hpd : p ∣ 2 ^ 2 := by
      rw [show (2 : ℕ) ^ 2 = 4 by norm_num, ← h4]
      exact dvd_pow_self p (by omega)
    exact (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp (hp.out.dvd_of_dvd_pow hpd)
  subst hp2
  have he2 : e = 2 := Nat.pow_right_injective le_rfl (show 2 ^ e = 2 ^ 2 by rw [h4])
  subst he2
  obtain ⟨φP⟩ : Nonempty (L ⧸ CFSG.pCore 2 L ≃* projSL 3 (GaloisField 2 2)) := by
    rcases hiso with ⟨-, hφ⟩ | ⟨hq', -⟩
    · exact hφ
    · norm_num at hq'
  rcases KFacts.ks18L34Gen X ⟨ι.symm.trans φP⟩ Eb hEbab hEb9 with hgen | hinn
  · exact Or.inl (hfix hgen)
  right
  left
  refine ⟨⟨φP⟩, eq_zpowers_sup_of_nine_le hE hcE hcL ?_,
    zpowers_inf_eq_bot_of_not_mem hc3 fun h => hcL h.2⟩
  have hconj := conj_injective_of_center_eq_bot' hZX
  set Pb := Eb.comap (MulAut.conj : X →* MulAut X) with hPb
  have hPb9 : Nat.card Pb = 9 := by
    rw [← hEb9, ← Subgroup.map_comap_eq_self hinn, Subgroup.card_map_of_injective hconj]
  have hPbE : Pb ≤ ((E ⊓ L).subgroupOf L).map (QuotientGroup.mk' θL) := by
    intro x hx
    have hxconj : MulAut.conj x ∈ Eb := hx
    have hfixx : ∀ d (hd : d ∈ E), Sec12.thetaBarAct L ⟨d, hEN hd⟩ x = x := by
      intro d hd
      have hdEb : ρ ⟨d, hEN hd⟩ ∈ Eb := ⟨⟨d, hEN hd⟩, Subgroup.mem_subgroupOf.mpr hd, rfl⟩
      obtain ⟨y, hy⟩ := hinn hdEb
      have hyEb : MulAut.conj y ∈ Eb := hy ▸ hdEb
      have hcomm : MulAut.conj y * MulAut.conj x = MulAut.conj x * MulAut.conj y :=
        congrArg Subtype.val (hEbab.1.is_comm.comm ⟨_, hyEb⟩ ⟨_, hxconj⟩)
      have h1 : MulAut.conj (y * x * y⁻¹) = MulAut.conj x := by
        rw [map_mul, map_mul, map_inv, hcomm]
        group
      change ρ ⟨d, hEN hd⟩ x = x
      rw [← hy, MulAut.conj_apply]
      exact hconj h1
    have hx3 : x ^ 3 = 1 := hconj (by rw [map_pow, map_one]; exact hEbab.2 _ hxconj)
    obtain ⟨y, hyx, hyc⟩ := Sec12.exists_lift_fixed hE.isPGroup hEN x hfixx
    obtain ⟨a, m, hm3, hord⟩ :=
      Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos y).ne' 3 (by norm_num)
    set w : L := y ^ (m ^ 2) with hw
    have hwa : w ^ (3 ^ a) = 1 := by
      rw [hw, ← pow_mul, show m ^ 2 * 3 ^ a = (3 ^ a * m) * m by ring, pow_mul, ← hord,
        pow_orderOf_eq_one, one_pow]
    have hm2 : m ^ 2 % 3 = 1 := by
      have : m % 3 = 1 ∨ m % 3 = 2 := by omega
      rcases this with h | h <;> simp [Nat.pow_mod, h]
    have hwx : QuotientGroup.mk' θL w = x := by
      rw [hw, map_pow, hyx, ← Nat.div_add_mod (m ^ 2) 3, hm2, pow_add, pow_mul, hx3, one_pow,
        one_mul, pow_one]
    have hw3 : w ^ 3 = 1 := by
      have h1 : w ^ 3 ∈ θL := by
        rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_pow, hwx, hx3]
      refine eq_one_of_mem_theta' h1 (k := a) ?_
      rw [← pow_mul, mul_comm, pow_mul, hwa, one_pow]
    have hEw : E ≤ Subgroup.centralizer ({(w : G)} : Set G) := by
      intro d hd
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 : Commute d (y : G) := by
        have := hyc d hd
        calc d * (y : G) = d * y * d⁻¹ * d := by group
          _ = y * d := by rw [this]
      rw [hw, Subgroup.coe_pow]
      exact (h1.pow_right (m ^ 2)).eq
    have hwE : (w : G) ∈ E :=
      mem_of_le_centralizer hst hctx.partTwoS_eq hEE
        (by simpa using congrArg Subtype.val hw3) hEw
    exact ⟨w, Subgroup.mem_subgroupOf.mpr ⟨hwE, w.2⟩, hwx⟩
  calc 9 = Nat.card Pb := hPb9.symm
    _ ≤ Nat.card (((E ⊓ L).subgroupOf L).map (QuotientGroup.mk' θL)) :=
      Subgroup.card_le_of_le hPbE
    _ ≤ Nat.card ((E ⊓ L).subgroupOf L) :=
      Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd _ _)
    _ = Nat.card (E ⊓ L : Subgroup G) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv


theorem rank3II_19_14_of_more (h1913 : Step1913) (hS : SeitzL3Pi) (hmore : Step1914More) :
    Step1914 :=
  step1914_of_split (rank3II_19_14Tri_of h1913 hS) hmore

end CFSG.RankThree.PartTwo.Sec19
