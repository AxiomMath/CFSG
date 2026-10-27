module

public import CFSG.RankThree.PartTwo.Sec4.Item419Res2ProofUnitary
public import CFSG.RankThree.PartTwo.Sec4.Item424ProofKFacts
import CFSG.RankThree.PartTwo.Sec6.BThreeCensusOrders
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
import CFSG.RankThree.PartTwo.Sec4.Item413Orders
import CFSG.RankThree.PartTwo.Sec4.Item419ThetaProofTools
import CFSG.Timmesfeld.Orders.Exceptional
import CFSG.RankThree.PartTwo.Sec4.Item417Res6ProofU4
import CFSG.Models.PGLOrders

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

namespace Item419Res3

theorem card_projSU_three_two_mul_three {m : ℕ} (hm : Odd m) :
    Nat.card (projSU 3 2 m) * 3 = (2 ^ m) ^ 3 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 + 1)) := by
  have h := KFacts.KS14.card_projSU_three_mul_gcd 2 m hm.pos
  have hg : Nat.gcd 3 (2 ^ m + 1) = 3 :=
    Nat.gcd_eq_left (Res417Six.three_dvd_two_pow_add_one hm)
  rwa [hg] at h

theorem two_pow_dvd_card_projSU_three_two {m : ℕ} (hm : Odd m) :
    2 ^ (3 * m) ∣ Nat.card (projSU 3 2 m) := by
  have h := card_projSU_three_two_mul_three hm
  have h1 : 2 ^ (3 * m) ∣ Nat.card (projSU 3 2 m) * 3 := by
    rw [h, ← pow_mul, mul_comm m 3]
    exact Dvd.intro _ rfl
  have hcop : Nat.Coprime (2 ^ (3 * m)) 3 := Nat.Coprime.pow_left _ (by norm_num)
  exact hcop.dvd_of_dvd_mul_right h1

theorem card_projSU_three_two_three : Nat.card (projSU 3 2 3) = 5515776 :=
  CFSG.PGLModel.card_projSU_three_eight

theorem eleven_dvd_card_projSU_three_two_five : 11 ∣ Nat.card (projSU 3 2 5) := by
  have h := card_projSU_three_two_mul_three (m := 5) ⟨2, rfl⟩
  norm_num at h
  omega

theorem unitary_component_facts {G : Type} [Group G] [Finite G] {L : Subgroup G} {a : G}
    {K : Subgroup G} (hKle : K ≤ L ⊓ Subgroup.centralizer ({a} : Set G))
    (hKc : IsComponent (K.subgroupOf (L ⊓ Subgroup.centralizer ({a} : Set G)))) {m : ℕ}
    (hm : Odd m) (e : K ≃* projSU 3 2 m) :
    3 ≤ m ∧ Nat.card K ∣ Nat.card (L ⧸ aschbacherSolvableCore 3 L) := by
  have hq : IsQuasisimple K := CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (Subgroup.subgroupOfEquivOfLe hKle) hKc.1
  have hperf : Group.IsPerfect K := hq.1
  have hnt : Nontrivial K := CFSG.LocalCores.isQuasisimple_nontrivial hq
  have hnsol : ¬ Group.IsSolvable K := fun h => Group.IsPerfect.not_isSolvable K h
  have hm3 : 3 ≤ m := by
    obtain ⟨j, rfl⟩ := hm
    rcases j with _ | j
    · exfalso
      apply hnsol
      have hc : Nat.card (projSU 3 2 1) = 72 := Item419ThetaProof.card_projSU_three_two_one
      have : Finite (projSU 3 2 1) := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
      have : Fintype (projSU 3 2 1) := Fintype.ofFinite _
      have hs : Group.IsSolvable (projSU 3 2 1) :=
        CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow (a := 3)
          (b := 2) Nat.prime_two Nat.prime_three (by norm_num)
          (by rw [← Nat.card_eq_fintype_card, hc]; norm_num)
      exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    · omega
  refine ⟨hm3, ?_⟩
  have hs : IsSimpleGroup (projSU 3 2 m) :=
    Sec19.Step1914TriProof.isSimpleGroup_projSU_three_of_ne_two 2 m (by omega) (by
      have : 2 ^ 3 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm3
      omega)
  have hsK : IsSimpleGroup K := e.isSimpleGroup
  have hKL : K ≤ L := hKle.trans inf_le_left
  set f : K →* L ⧸ aschbacherSolvableCore 3 L :=
    (QuotientGroup.mk' (aschbacherSolvableCore 3 L)).comp (Subgroup.inclusion hKL) with hf
  have hθs : Group.IsSolvable (aschbacherSolvableCore 3 L) :=
    (solvable_prime_complement_core_characterization Nat.prime_three).1
  have hker : f.ker = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal f.ker with h | h
    · exact h
    · exfalso
      apply hnsol
      have hle : ∀ k : K, Subgroup.inclusion hKL k ∈ aschbacherSolvableCore 3 L := by
        intro k
        have hk : k ∈ f.ker := h ▸ Subgroup.mem_top k
        rw [MonoidHom.mem_ker, hf, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
          QuotientGroup.eq_one_iff] at hk
        exact hk
      let g : K →* aschbacherSolvableCore 3 L :=
        (Subgroup.inclusion hKL).codRestrict _ hle
      exact Group.isSolvable_of_isSolvable_injective (f := g) fun x y hxy =>
        Subgroup.inclusion_injective hKL (congrArg Subtype.val hxy)
  have hinj : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp hker
  rw [← Nat.card_congr (MonoidHom.ofInjective hinj).symm.toEquiv]
  exact Subgroup.card_subgroup_dvd_card _

theorem false_of_two_pow_nine {G : Type} [Group G] [Finite G] {L : Subgroup G} {a : G}
    {K : Subgroup G} (hKle : K ≤ L ⊓ Subgroup.centralizer ({a} : Set G))
    (hKc : IsComponent (K.subgroupOf (L ⊓ Subgroup.centralizer ({a} : Set G)))) {m : ℕ}
    (hm : Odd m) (e : K ≃* projSU 3 2 m) {M : ℕ}
    (hM : Nat.card (L ⧸ aschbacherSolvableCore 3 L) ∣ M) (h9 : ¬ 2 ^ 9 ∣ M) : False := by
  obtain ⟨hm3, hdvd⟩ := unitary_component_facts hKle hKc hm e
  apply h9
  have h1 : 2 ^ (3 * m) ∣ Nat.card K := by
    rw [Nat.card_congr e.toEquiv]
    exact two_pow_dvd_card_projSU_three_two hm
  exact (pow_dvd_pow 2 (by omega)).trans (h1.trans (hdvd.trans hM))

theorem false_of_two_pow_fifteen {G : Type} [Group G] [Finite G] {L : Subgroup G} {a : G}
    {K : Subgroup G} (hKle : K ≤ L ⊓ Subgroup.centralizer ({a} : Set G))
    (hKc : IsComponent (K.subgroupOf (L ⊓ Subgroup.centralizer ({a} : Set G)))) {m : ℕ}
    (hm : Odd m) (e : K ≃* projSU 3 2 m) {M : ℕ}
    (hM : Nat.card (L ⧸ aschbacherSolvableCore 3 L) ∣ M) (h15 : ¬ 2 ^ 15 ∣ M)
    (h19 : ¬ 19 ∣ M) : False := by
  obtain ⟨hm3, hdvd⟩ := unitary_component_facts hKle hKc hm e
  have hKM : Nat.card K ∣ M := hdvd.trans hM
  rw [Nat.card_congr e.toEquiv] at hKM
  rcases (show m = 3 ∨ 5 ≤ m by obtain ⟨j, rfl⟩ := hm; omega) with rfl | h5
  · apply h19
    rw [card_projSU_three_two_three] at hKM
    exact (show (19 : ℕ) ∣ 5515776 by norm_num).trans hKM
  · apply h15
    exact (pow_dvd_pow 2 (by omega)).trans ((two_pow_dvd_card_projSU_three_two hm).trans hKM)

theorem false_of_two_pow_twentyone {G : Type} [Group G] [Finite G] {L : Subgroup G} {a : G}
    {K : Subgroup G} (hKle : K ≤ L ⊓ Subgroup.centralizer ({a} : Set G))
    (hKc : IsComponent (K.subgroupOf (L ⊓ Subgroup.centralizer ({a} : Set G)))) {m : ℕ}
    (hm : Odd m) (e : K ≃* projSU 3 2 m) {M : ℕ}
    (hM : Nat.card (L ⧸ aschbacherSolvableCore 3 L) ∣ M) (h21 : ¬ 2 ^ 21 ∣ M)
    (h19 : ¬ 19 ∣ M) (h11 : ¬ 11 ∣ M) : False := by
  obtain ⟨hm3, hdvd⟩ := unitary_component_facts hKle hKc hm e
  have hKM : Nat.card K ∣ M := hdvd.trans hM
  rw [Nat.card_congr e.toEquiv] at hKM
  rcases (show m = 3 ∨ m = 5 ∨ 7 ≤ m by obtain ⟨j, rfl⟩ := hm; omega) with rfl | rfl | h7
  · apply h19
    rw [card_projSU_three_two_three] at hKM
    exact (show (19 : ℕ) ∣ 5515776 by norm_num).trans hKM
  · exact h11 (eleven_dvd_card_projSU_three_two_five.trans hKM)
  · apply h21
    exact (pow_dvd_pow 2 (by omega)).trans ((two_pow_dvd_card_projSU_three_two hm).trans hKM)

end Item419Res3

open Item419Res3

section Kinds


@[expose] def K419UnitaryOddChar : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsComponent L →
    (IsList46One (L ⧸ aschbacherSolvableCore 3 L) ∨ IsList46Two (L ⧸ aschbacherSolvableCore 3 L) ∨
      IsList46Three (L ⧸ aschbacherSolvableCore 3 L)) →
    ∀ a ∈ Subgroup.normalizer (L : Set G), orderOf a = 3 →
    a ∉ Subgroup.centralizer (L : Set G) → ∀ K : Subgroup G,
    K ≤ L ⊓ Subgroup.centralizer ({a} : Set G) →
    IsComponent (K.subgroupOf (L ⊓ Subgroup.centralizer ({a} : Set G))) →
    (∃ m : ℕ, Odd m ∧ Nonempty (K ≃* projSU 3 2 m)) →
      InducesStdKind L a .field ∨ InducesStdKind L a .graphField

@[expose] def K419UnitarySpor : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsComponent L →
    IsList46Five (L ⧸ aschbacherSolvableCore 3 L) →
    ∀ a ∈ Subgroup.normalizer (L : Set G), orderOf a = 3 →
    a ∉ Subgroup.centralizer (L : Set G) → ∀ K : Subgroup G,
    K ≤ L ⊓ Subgroup.centralizer ({a} : Set G) →
    IsComponent (K.subgroupOf (L ⊓ Subgroup.centralizer ({a} : Set G))) →
    (∃ m : ℕ, Odd m ∧ Nonempty (K ≃* projSU 3 2 m)) →
      InducesStdKind L a .field ∨ InducesStdKind L a .graphField

@[expose] def K419UnitaryChevTwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsComponent L →
    IsList46Six (L ⧸ aschbacherSolvableCore 3 L) →
    ∀ a ∈ Subgroup.normalizer (L : Set G), orderOf a = 3 →
    a ∉ Subgroup.centralizer (L : Set G) → ∀ K : Subgroup G,
    K ≤ L ⊓ Subgroup.centralizer ({a} : Set G) →
    IsComponent (K.subgroupOf (L ⊓ Subgroup.centralizer ({a} : Set G))) →
    (∃ m : ℕ, Odd m ∧ Nonempty (K ≃* projSU 3 2 m)) →
      InducesStdKind L a .field ∨ InducesStdKind L a .graphField

end Kinds

namespace Item419Res3

variable {X : Type} [Group X]

theorem card_dvd_of_isList46Four (hX : IsList46Four X) :
    Nat.card X ∣ Nat.factorial 9 ∨ Nat.card X ∣ 1080 ∨ Nat.card X ∣ 7560 := by
  rcases hX with ⟨n, hn, ⟨e⟩⟩ | h6 | h7
  · left
    rw [Nat.card_congr e.toEquiv]
    exact Sec6.BThreeCensus.card_alternatingGroup_dvd hn
  · right; left
    rw [Sec6.BThreeCensus.card_of_isExtOf h6, nat_card_alternatingGroup, Nat.card_fin,
      Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    decide
  · right; right
    rw [Sec6.BThreeCensus.card_of_isExtOf h7, nat_card_alternatingGroup, Nat.card_fin,
      Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    decide

theorem card_dvd_of_isList46Seven (hX : IsList46Seven X) :
    Nat.card X ∣ 9999360 ∨ Nat.card X ∣ 1451520 ∨ Nat.card X ∣ 4 ^ 10 * 254840625 := by
  rcases hX with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · left
    rw [Nat.card_congr e.toEquiv]
    refine (card_projSL_dvd 5 (GaloisField 2 1)).trans ?_
    rw [Sec6.BThreeCensus.card_SL_galoisField 5 2 1 one_ne_zero]
    decide
  · right; left
    rw [Nat.card_congr e.toEquiv, Sec6.BThreeCensus.card_projSp_three_two]
  · right; right
    rw [Nat.card_congr e.toEquiv]
    exact Sec6.BThreeCensus.card_projSU_five_four_dvd

theorem not_two_pow_nine_dvd_of_isList46Eight
    [Finite X] (hX : IsList46Eight X) : ∃ M : ℕ, Nat.card X ∣ M ∧ ¬ 2 ^ 9 ∣ M := by
  rcases hX with ⟨e, he1, he2, ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩⟩ | ⟨⟨f⟩⟩ | ⟨hZ, hG | ⟨⟨f⟩⟩⟩
  · interval_cases e
    · refine ⟨5616, ?_, by decide⟩
      rw [Nat.card_congr f.toEquiv]
      refine (card_projSL_dvd 3 (GaloisField 3 1)).trans ?_
      rw [Sec6.BThreeCensus.card_SL_galoisField 3 3 1 one_ne_zero]
      decide
    · refine ⟨42456960, ?_, by decide⟩
      rw [Nat.card_congr f.toEquiv]
      refine (card_projSL_dvd 3 (GaloisField 3 2)).trans ?_
      rw [Sec6.BThreeCensus.card_SL_galoisField 3 3 2 two_ne_zero]
      decide
  · interval_cases e
    · refine ⟨6048, ?_, by decide⟩
      rw [Nat.card_congr f.toEquiv]
      exact Sec6.BThreeCensus.card_projSU_three_three_dvd le_rfl
    · refine ⟨42573600, ?_, by decide⟩
      rw [Nat.card_congr f.toEquiv]
      exact Sec6.BThreeCensus.card_projSU_three_three_dvd (by norm_num)
  · refine ⟨12130560, ?_, by decide⟩
    rw [Nat.card_congr f.toEquiv]
    refine (card_projSL_dvd 4 (GaloisField 3 1)).trans ?_
    rw [Sec6.BThreeCensus.card_SL_galoisField 4 3 1 one_ne_zero]
    decide
  · refine ⟨6 * 4245696, ?_, by decide⟩
    rw [Sec6.BThreeCensus.card_eq_card_center_mul,
      (CFSG.Timmesfeld.card_chevalleyExceptionalModel_untwisted hG).1 rfl]
    have hG2 : CFSG.Open.ordG2 (3 ^ 1) = 4245696 := by norm_num [CFSG.Open.ordG2]
    rw [hG2]
    refine Nat.mul_dvd_mul_right ?_ _
    have h0 : 0 < Nat.card (Subgroup.center X) := Nat.card_pos
    interval_cases (Nat.card (Subgroup.center X)) <;> norm_num
  · refine ⟨6 * 3265920, ?_, by decide⟩
    rw [Sec6.BThreeCensus.card_eq_card_center_mul, Nat.card_congr f.toEquiv,
      Sec6.BThreeCensus.card_projSU_four_three]
    refine Nat.mul_dvd_mul_right ?_ _
    have h0 : 0 < Nat.card (Subgroup.center X) := Nat.card_pos
    interval_cases (Nat.card (Subgroup.center X)) <;> norm_num

end Item419Res3

theorem k419UnitaryCensus_of
    (hOdd : K419UnitaryOddChar) (hSpor : K419UnitarySpor)
    (hTwo : K419UnitaryChevTwo) : K419UnitaryCensus := by
  intro G _ _ L hL h46 a ha ha3 haC K hK hKc hU
  rcases (isList46_iff _).mp h46 with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  · exact hOdd G L hL (Or.inl h1) a ha ha3 haC K hK hKc hU
  · exact hOdd G L hL (Or.inr (Or.inl h2)) a ha ha3 haC K hK hKc hU
  · exact hOdd G L hL (Or.inr (Or.inr h3)) a ha ha3 haC K hK hKc hU
  · exfalso
    obtain ⟨m, hm, ⟨e⟩⟩ := hU
    rcases card_dvd_of_isList46Four h4 with hd | hd | hd
    · exact false_of_two_pow_nine hK hKc hm e hd (by decide)
    · exact false_of_two_pow_nine hK hKc hm e hd (by decide)
    · exact false_of_two_pow_nine hK hKc hm e hd (by decide)
  · exact hSpor G L hL h5 a ha ha3 haC K hK hKc hU
  · exact hTwo G L hL h6 a ha ha3 haC K hK hKc hU
  · exfalso
    obtain ⟨m, hm, ⟨e⟩⟩ := hU
    rcases card_dvd_of_isList46Seven h7 with hd | hd | hd
    · exact false_of_two_pow_fifteen hK hKc hm e hd (by decide) (by decide)
    · exact false_of_two_pow_fifteen hK hKc hm e hd (by decide) (by decide)
    · exact false_of_two_pow_twentyone hK hKc hm e hd (by decide) (by decide) (by decide)
  · exfalso
    obtain ⟨m, hm, ⟨e⟩⟩ := hU
    obtain ⟨M, hd, h9⟩ := not_two_pow_nine_dvd_of_isList46Eight h8
    exact false_of_two_pow_nine hK hKc hm e hd h9

end CFSG.RankThree.PartTwo.Sec4
