module

public import CFSG.RankThree.PartTwo.KFacts.KS18MultProof
import CFSG.RankThree.PartTwo.Sec19.Step1913
import CFSG.RankThree.PartTwo.Sec17.Item171GenProofA7
import CFSG.RankThree.PartTwo.KFacts.KS14MathieuAutCore
import CFSG.RankThree.PartTwo.Sec16.Item163StepsQProof
import CFSG.RankThree.PartTwo.Sec16.Item162Proof
import CFSG.RankThree.PartTwo.Sec12.Item122
import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.RankThree.PartTwo.Sec16.Item163ResProofA7Norm

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec17 CFSG.GH74.GLS

namespace Res3LeA7

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem pCoreOf_eq_map (L : Subgroup G) :
    CFSG.Open.pCoreOf 2 L = (CFSG.pCore 2 ↥L).map L.subtype := CFSG.openPCoreOf_eq_map_pCore 2 L

theorem theta_eq_pCore_two
    (h135 : Item135) {A : Subgroup G} {e : G} {Le : Subgroup G}
    (he : Sec15R G A e Le)
    (h7 : Nonempty (↥Le ⧸ aschbacherSolvableCore 3 ↥Le ≃* alternatingGroup (Fin 7))) :
    aschbacherSolvableCore 3 ↥Le = CFSG.pCore 2 ↥Le :=
  Sec19.theta_eq_pCore_two_of_mult KFacts.KS14.ks18Mult
    (h135 G A e Le he.toSec13Data he.hypS_or_hypT) (Or.inr (Or.inr (Or.inr (Or.inl h7))))

theorem eq_delta_of_a7 {A : Subgroup G} {e : G} {Le : Subgroup G} (he : Sec15R G A e Le)
    (h142 : Concl142 A (lB A))
    (h7 : Nonempty (↥Le ⧸ aschbacherSolvableCore 3 ↥Le ≃* alternatingGroup (Fin 7))) :
    Le = delta A (lB A) Le := by
  refine le_antisymm ((Proof171Gen.le_sSup_invariantPiSubgroups_of_sec13Data he.toSec13Data
    h7).trans (sSup_le fun Q hQ => ?_)) (delta_le Le)
  obtain ⟨hQL, hQ3, hAQ⟩ := hQ
  exact le_delta (mem_scriptQ_of_concl142 h142 he.zpowers_mem_omegaA ⟨hQL.trans
    (he.toSec13Data.le_centralizer.trans (centralizer_singleton_le_normalizer_zpowers e)),
    hQ3, hAQ⟩) hQL

theorem mem_scriptY0
    (h135 : Item135) {A : Subgroup G} {e : G} {Le : Subgroup G}
    (he : Sec15R G A e Le) (h142 : Concl142 A (lB A))
    (h7 : Nonempty (↥Le ⧸ aschbacherSolvableCore 3 ↥Le ≃* alternatingGroup (Fin 7)))
    (hO : CFSG.Open.pCoreOf 2 Le ≠ ⊥) : Le ∈ scriptY0 A (lB A) := by
  have hY : Le ∈ scriptY A := by
    refine ⟨fun htop => ?_, he.toSec13Data.le_normalizer⟩
    apply Sec12.centralizer_ne_top_of_theoremFourHyp he.toTheoremFourHyp he.toSec13Data.ne_one
    exact top_le_iff.mp (htop ▸ he.toSec13Data.le_centralizer)
  exact ⟨⟨hY, eq_oPrimeResidualOf_of_sec15R he, eq_delta_of_a7 he h142 h7,
    h135 G A e Le he.toSec13Data he.hypS_or_hypT⟩, hY, hO⟩

theorem exists_mem_mk_eq {K L : Subgroup G} (hKL : K ≤ L)
    (hcov : L = K ⊔ (aschbacherSolvableCore 3 ↥L).map L.subtype)
    (q : ↥L ⧸ aschbacherSolvableCore 3 ↥L) :
    ∃ k : ↥L, (k : G) ∈ K ∧ (k : ↥L ⧸ aschbacherSolvableCore 3 ↥L) = q := by
  have hθn : (aschbacherSolvableCore 3 ↥L).Normal := by
    have := (solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three).2.1
    infer_instance
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
  have hmap : K ⊔ (aschbacherSolvableCore 3 ↥L).map L.subtype =
      (K.subgroupOf L ⊔ aschbacherSolvableCore 3 ↥L).map L.subtype := by
    rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hKL]
  have h1 : L.subtype l ∈ (K.subgroupOf L ⊔ aschbacherSolvableCore 3 ↥L).map L.subtype := by
    rw [← hmap, ← hcov]
    exact l.2
  have hl := (Subgroup.mem_map_iff_mem L.subtype_injective).mp h1
  obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_right.mp hl
  refine ⟨y, Subgroup.mem_subgroupOf.mp hy, ?_⟩
  rw [← hyz, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff z).mpr hz, mul_one]

theorem exists_invariant_two_subgroup {A : Subgroup G} {e : G} {Le : Subgroup G}
    (hD : Sec13Data G A e Le)
    (h7 : Nonempty (↥Le ⧸ aschbacherSolvableCore 3 ↥Le ≃* alternatingGroup (Fin 7)))
    (hθ : aschbacherSolvableCore 3 ↥Le = CFSG.pCore 2 ↥Le) {Y K : Subgroup G}
    (hAY : A ≤ Subgroup.normalizer (Y : Set G)) (hKY : K ≤ Y) (hKLe : K ≤ Le)
    (hcov : Le = K ⊔ (aschbacherSolvableCore 3 ↥Le).map Le.subtype) :
    ∃ Q : Subgroup G, Q ≠ ⊥ ∧ Q ≤ Y ⊓ Le ∧ IsPGroup 2 Q ∧
      A ≤ Subgroup.normalizer (Q : Set G) := by
  classical
  obtain ⟨φ⟩ := h7
  have hAL : A ≤ Subgroup.normalizer (Le : Set G) := hD.le_normalizer
  set Ebar := Sec4.autThetaQuot A Le with hEbar
  have hA9 : Nat.card Ebar = 9 := Proof171Gen.card_autThetaQuot_eq_nine hD
  obtain ⟨-, hZ, hinner, -, -⟩ :=
    KFacts.KS14.a7_facts (↥Le ⧸ aschbacherSolvableCore 3 ↥Le) ⟨φ⟩
  have hinj := Proof171Gen.conj_injective_of_center_eq_bot hZ
  have hEin : Ebar ≤ (MulAut.conj : (↥Le ⧸ aschbacherSolvableCore 3 ↥Le) →*
      MulAut (↥Le ⧸ aschbacherSolvableCore 3 ↥Le)).range := by
    intro τ hτ
    have h9 : τ ^ 3 ^ 2 = 1 := by
      have h := pow_card_eq_one' (G := Ebar) (x := ⟨τ, hτ⟩)
      rw [hA9] at h
      exact congrArg Subtype.val h
    obtain ⟨x, hx⟩ := hinner τ ⟨2, h9⟩
    exact ⟨x, hx.symm⟩
  set E := Ebar.comap (MulAut.conj : (↥Le ⧸ aschbacherSolvableCore 3 ↥Le) →*
      MulAut (↥Le ⧸ aschbacherSolvableCore 3 ↥Le)) with hE
  have hEcard : Nat.card E = 9 := by
    rw [← Subgroup.card_map_of_injective hinj, hE, Subgroup.map_comap_eq,
      inf_eq_right.mpr hEin, hA9]
  obtain ⟨Q₁, -, -, h4, -, hN, -⟩ := Proof171Gen.exists_sup_eq_top_of_card_nine φ hEcard
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 ↥Le) with hπ
  set P := (Q₁.comap π).map Le.subtype with hP
  have hAP : A ≤ Subgroup.normalizer (P : Set G) := by
    refine Proof171Gen.le_normalizer_of_forall_conj_mem fun a ha y hy => ?_
    obtain ⟨l, hl, rfl⟩ := hy
    set τ := Sec4.thetaQuotMulAut ↥Le (Le.normalizerMonoidHom ⟨a, hAL ha⟩) with hτ
    have hτE : τ ∈ Ebar := Sec4.mem_autThetaQuot_iff.mpr ⟨a, hAL ha, ha, rfl⟩
    obtain ⟨x, hx⟩ := hEin hτE
    have hxE : x ∈ E := by
      change MulAut.conj x ∈ Ebar
      rw [hx]
      exact hτE
    set l' := Le.normalizerMonoidHom ⟨a, hAL ha⟩ l with hl'
    have hl'G : (l' : G) = a * (l : G) * a⁻¹ :=
      Subgroup.normalizerMonoidHom_apply_apply_coe Le ⟨a, hAL ha⟩ l
    have hπl' : π l' = x * π l * x⁻¹ := by
      have h1 : π l' = τ (π l) := (Sec4.thetaQuotMulAut_mk _ l).symm
      rw [h1, ← hx, MulAut.conj_apply]
    have hmem : π l' ∈ Q₁ := by
      rw [hπl']
      exact (Subgroup.mem_normalizer_iff.mp (hN hxE) _).mp hl
    exact ⟨l', hmem, hl'G⟩
  have hP2 : IsPGroup 2 P := by
    rintro ⟨y, l, hl, rfl⟩
    have h4' : π l ^ 4 = 1 := by
      have h := pow_card_eq_one' (G := Q₁) (x := ⟨π l, hl⟩)
      rw [h4] at h
      exact congrArg Subtype.val h
    have hl4 : l ^ 4 ∈ CFSG.pCore 2 ↥Le := by
      have h1 : π (l ^ 4) = 1 := by rw [map_pow]; exact h4'
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact hθ ▸ h1
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 ↥Le)) ⟨l ^ 4, hl4⟩
    have hk' : l ^ 2 ^ (k + 2) = 1 := by
      have h := congrArg Subtype.val hk
      rw [Subgroup.coe_pow, Subgroup.coe_one] at h
      rw [show 2 ^ (k + 2) = 4 * 2 ^ k by ring, pow_mul]
      exact h
    have hk'' : (l : G) ^ 2 ^ (k + 2) = 1 := by
      simpa using congrArg Subtype.val hk'
    refine ⟨k + 2, Subtype.ext ?_⟩
    simpa using hk''
  have hQ1 : Q₁ ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at h4
    norm_num at h4
  obtain ⟨⟨q, hq⟩, hq1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hQ1
  obtain ⟨k, hkK, hkq⟩ := exists_mem_mk_eq hKLe hcov q
  have hkP : (k : G) ∈ P := by
    refine ⟨k, ?_, rfl⟩
    change π k ∈ Q₁
    rw [hπ, QuotientGroup.mk'_apply, hkq]
    exact hq
  refine ⟨P ⊓ Y, ?_, le_inf inf_le_right (inf_le_left.trans (Subgroup.map_subtype_le _)),
    hP2.to_le inf_le_left, (le_inf hAP hAY).trans Subgroup.inf_normalizer_le_normalizer_inf⟩
  intro hbot
  have hk1 : (k : G) ∈ P ⊓ Y := ⟨hkP, hKY hkK⟩
  rw [hbot, Subgroup.mem_bot] at hk1
  have hk1' : k = 1 := Subtype.ext hk1
  apply hq1
  apply Subtype.ext
  change q = 1
  rw [← hkq, hk1', QuotientGroup.mk_one]

end Res3LeA7

theorem step163LeA7Norm_of_items
    (h135 : Item135) (h142 : Concl142R) (h162 : Item162R) : Step163LeA7Norm := by
  intro G _ _ A c L h Y hY e Le he hLe h7 _ _ _ K hKY hKLe hcov
  have he' : Sec15R G A e Le := sec15R_of_point h he hLe
  have hθ := Res3LeA7.theta_eq_pCore_two h135 he' h7
  have h142' : Concl142 A (lB A) := h142 G A c L h
  have hYY : Y ∈ scriptY A := hY.prop.1.1
  have hO : CFSG.Open.pCoreOf 2 Le = (aschbacherSolvableCore 3 ↥Le).map Le.subtype := by
    rw [Res3LeA7.pCoreOf_eq_map, hθ]
  have hcov' : Le = (Y ⊓ Le) ⊔ CFSG.Open.pCoreOf 2 Le := by
    rw [hO]
    exact le_antisymm (hcov.le.trans (sup_le_sup_right (le_inf hKY hKLe) _))
      (sup_le inf_le_right (Subgroup.map_subtype_le _))
  have hLeY : Le ≤ Y := le_of_cover h (h162 G A c L h) hY he hLe hcov' fun hO1 => by
    obtain ⟨Ye, hLYe, hYe⟩ := Finite.exists_le_maximal (p := (· ∈ scriptY0 A (lB A)))
      (Res3LeA7.mem_scriptY0 h135 he' h142' h7 hO1)
    refine ⟨Ye, hYe, hLYe, fun _ => ?_⟩
    obtain ⟨Q, hQ1, hQYL, hQ2, hAQ⟩ :=
      Res3LeA7.exists_invariant_two_subgroup he'.toSec13Data h7 hθ hYY.2 hKY hKLe hcov
    have hQ3 : ¬ 3 ∣ Nat.card Q := by
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hQ2
      rw [hn]
      intro h3
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
        (Nat.prime_three.dvd_of_dvd_pow h3)
      omega
    have hQLe : Q ≤ Le := hQYL.trans inf_le_right
    refine ⟨Q, ⟨⟨mem_scriptQ_of_concl142 h142' he ⟨hQLe.trans
      (he'.toSec13Data.le_centralizer.trans (centralizer_singleton_le_normalizer_zpowers e)),
      (isPiSubgroup_piCompl_iff Nat.prime_three Q).mpr hQ3, hAQ⟩, le_inf
      ((hQLe.trans hLYe).trans Subgroup.le_normalizer)
      ((hQYL.trans inf_le_left).trans Subgroup.le_normalizer)⟩,
      (isPiSubgroup_piOf_iff Nat.prime_two Q).mpr hQ2⟩, hQ1⟩
  exact hLeY.trans Subgroup.le_normalizer

end CFSG.RankThree.PartTwo.Sec16
