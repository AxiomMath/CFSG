module

public import CFSG.LocalAnalysis.UniquenessCase.UC7P3ReeU3Excl
import CFSG.Adapters.LieModelSmallOrders
import CFSG.Adapters.TauCetiLieModels
import CFSG.GH74.Orders.LieType
import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin
import CFSG.LocalAnalysis.StandardType.ChevTwoLieModel
import CFSG.RankThree.PartOne.N143.SectionGroup
public import CFSG.CharacterTheory.Burnside
public import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
open CFSG.RankThree.PartOne.Census3 (IsoLie)
open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree
  (Gls3ConclusionPlus Gls3StronglyThreeEmbeddedPlus)

variable {G : Type} [Group G] [Finite G]

theorem uc22ine229_l34_card {X : Type} [Group X]
    (h : IsoLie X (.A 2 ⟨2, 2, Nat.prime_two, by norm_num⟩)) : Nat.card X = 20160 := by
  obtain ⟨hv, ⟨e⟩⟩ := h
  have hL := CFSG.Models.lieModel_A 2 ⟨2, 2, Nat.prime_two, by norm_num⟩ hv e
  have hB := CFSG.StandardType.ChevTwo.blueprintLieModel_of_modelsLieModel
    (by simp [CFSG.Blueprint.classicalTags]) hL
  exact CFSG.Blueprint.LieModel.card_psl_three_four hB

theorem uc22ine229_l34_ne_ordA (x : ℕ) : CFSG.Open.ordA 1 x ≠ 20160 := by
  intro h
  have h1 : CFSG.Open.ordA 1 x = x * (x ^ 2 - 1) / Nat.gcd 2 (x - 1) := by
    simp [CFSG.Open.ordA]
  rw [h1] at h
  have hg : Nat.gcd 2 (x - 1) = 1 ∨ Nat.gcd 2 (x - 1) = 2 := by
    have hd : Nat.gcd 2 (x - 1) ∣ 2 := Nat.gcd_dvd_left _ _
    exact (Nat.dvd_prime Nat.prime_two).1 hd
  have hx1 : x ≠ 0 := by
    rintro rfl
    simp at h
  have hy : (x ^ 2 - 1) + 1 = x ^ 2 :=
    Nat.sub_add_cancel (Nat.one_le_pow _ _ (Nat.pos_of_ne_zero hx1))
  generalize hyy : x ^ 2 - 1 = y at hy h
  rcases le_or_gt x 35 with hx | hx
  · rcases hg with hg | hg <;> rw [hg] at h <;> interval_cases x <;> omega
  · have hy2 : 1295 ≤ y := by nlinarith
    have hm : 36 * 1295 ≤ x * y := Nat.mul_le_mul (by omega) hy2
    rcases hg with hg | hg <;> rw [hg] at h <;> omega

theorem uc22ine229_l34_false_of_isoLie_A1 {X : Type} [Group X] (hc : Nat.card X = 20160)
    (q : TauCeti.PrimePower) (h : IsoLie X (.A 1 q)) : False := by
  obtain ⟨hv, ⟨e⟩⟩ := h
  have hL := CFSG.Models.lieModel_A 1 q hv e
  have hB := CFSG.StandardType.ChevTwo.blueprintLieModel_of_modelsLieModel
    (by simp [CFSG.Blueprint.classicalTags]) hL
  have h1 := CFSG.GH74.card_of_lieModel_PSL (by norm_num) hB
  rw [hc] at h1
  exact uc22ine229_l34_ne_ordA _ h1.symm

theorem uc22ine229_l34_exists_two_three {n c : ℕ} (h : n ∣ 9 * 2 ^ c) :
    ∃ i j : ℕ, n = 2 ^ i * 3 ^ j := by
  obtain ⟨a, b, ha, hb, rfl⟩ := Nat.dvd_mul.1 h
  obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 (by simpa using ha : a ∣ 3 ^ 2)
  obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hb
  exact ⟨i, j, mul_comm _ _⟩

theorem uc22ine229_l34_inf_dvd {Y : Type} [Group Y] [Finite Y] {F J Q S : Subgroup Y}
    (hQ : Nat.card Q = 9) {a : ℕ} (hS : Nat.card S = 2 ^ a)
    (hJ : J ⊓ F = F ⊓ normalizer (Q : Set Y)) (hsup : Q ⊔ S = F ⊓ normalizer (Q : Set Y))
    (hSF : S ≤ F ⊓ normalizer (Q : Set Y)) : Nat.card ↥(J ⊓ F) ∣ 9 * 2 ^ a := by
  have h := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
    (H := S) (K := Q) (hSF.trans inf_le_right)
  rw [hQ, hS] at h
  rw [hJ, ← hsup, sup_comm, mul_comm]
  exact Dvd.intro _ h

theorem uc22ine229_l34_rows {Y : Type} [Group Y] [Finite Y] {F J P : Subgroup Y}
    (hc : Nat.card F = 20160) (hrows : Gls3ConclusionPlus Y F P)
    (hJ : J ⊓ F = F ⊓ normalizer ((P ⊓ F : Subgroup Y) : Set Y))
    (hno : ∀ m : ℕ, ¬ IsoLie ↥F (.reeG2 m)) :
    (∃ e : ℕ, F.index = 2 ^ e) ∧ Nat.card ↥(P ⊓ F) = 9 ∧
      ∃ c : ℕ, Nat.card ↥(J ⊓ F) ∣ 9 * 2 ^ c := by
  obtain ⟨-, -, hrows⟩ := hrows
  rcases hrows with ⟨q, -, hI, -⟩ | ⟨q, hq3, hI, -, -, -, -, hQ, -⟩ | ⟨m, hI, -⟩ | ⟨hI, -⟩ |
      ⟨⟨φ, -⟩, -⟩ | ⟨-, ⟨e, he⟩, -, -, hQ9, hΓ, S, hS, -, hsup, ⟨f⟩, -⟩ |
      ⟨-, hK, -, hQ9, hΓ, S, hS, hsup, h16, -⟩
  · exact (uc22ine229_l34_false_of_isoLie_A1 hc q hI).elim
  · exfalso
    have h1 : Nat.card ↥(P ⊓ F) ∣ 20160 := hc ▸ Subgroup.card_dvd_of_le inf_le_right
    rw [hQ] at h1
    have h2 : 3 ^ 3 ∣ q.card ^ 3 := by
      rw [TauCeti.PrimePower.card_def, hq3, ← pow_mul]
      exact pow_dvd_pow 3 (by have := q.exponent_pos; omega)
    exact absurd (h2.trans h1) (by norm_num)
  · exact (hno m hI).elim
  · exact (uc22ine229_l34_false_of_isoLie_A1 hc _ hI).elim
  · exfalso
    have h : Nat.card F = 360 := by
      rw [Nat.card_congr φ.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
      decide
    rw [hc] at h
    exact absurd h (by norm_num)
  · have hS8 : Nat.card S = 2 ^ 3 := by
      rw [Nat.card_congr f.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
      norm_num
    exact ⟨⟨e, he⟩, hQ9, 3, uc22ine229_l34_inf_dvd hQ9 hS8 hJ (hsup.trans hΓ) (hS.trans hΓ.le)⟩
  · exact ⟨⟨0, by rw [hK, Subgroup.index_top, pow_zero]⟩, hQ9, 4,
      uc22ine229_l34_inf_dvd hQ9 (h16.trans (by norm_num)) hJ (hsup.trans hΓ) (hS.trans hΓ.le)⟩

theorem uc22ine229_l34_data (hG3 : Gls3StronglyThreeEmbeddedPlus)
    (hRee : CFSG.AGLEmbedding.KFactReeInvolution) (k : Sec7Core4 G) (hp3 : k.p = 3)
    {H : Subgroup G} (hH : Sec7Core4.Config k H)
    (hF : IsoLie ↥(CFSG.generalizedFitting (↥H ⧸ CFSG.pPrimeCore k.p ↥H))
      (.A 2 ⟨2, 2, Nat.prime_two, by norm_num⟩)) :
    (∃ c : ℕ, Nat.card ↥(((H ⊓ k.M).subgroupOf H).map
        (QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥H))) ∣ 9 * 2 ^ c) ∧
      ∀ R : Subgroup (↥H ⧸ CFSG.pPrimeCore k.p ↥H), IsPGroup 3 R → Nat.card R ≤ 9 := by
  haveI : Fact k.p.Prime := ⟨k.prime⟩
  haveI : (CFSG.generalizedFitting (↥H ⧸ CFSG.pPrimeCore k.p ↥H)).Normal :=
    CFSG.LocalCores.generalized_fitting_characteristic.2
  obtain ⟨P₀⟩ : Nonempty (Sylow k.p ↥(H ⊓ k.M)) := inferInstance
  obtain ⟨P', -, hP'N⟩ := k.exists_sylow_map_of_isSylowOf hH
    (P := (P₀ : Subgroup ↥(H ⊓ k.M)).map (H ⊓ k.M).subtype) ⟨P₀, rfl⟩
  obtain ⟨hrows, hNoRee, -⟩ := k.rows3_of_config hG3 hRee hp3 hH P'
  obtain ⟨⟨e, he⟩, hQ9, c, hc⟩ := uc22ine229_l34_rows (uc22ine229_l34_card hF) hrows
    (k.inf_eq_and_le_normalizer_quotient hG3 hp3 hH P' hP'N).1 hNoRee
  set F := CFSG.generalizedFitting (↥H ⧸ CFSG.pPrimeCore k.p ↥H)
  set J := ((H ⊓ k.M).subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥H))
  refine ⟨⟨e + c, ?_⟩, fun R hR => ?_⟩
  · have h1 : F.relIndex J * Nat.card ↥(J ⊓ F) = Nat.card J := by
      rw [inf_comm]
      exact Subgroup.relIndex_mul_card F J
    have h2 : F.relIndex J ∣ 2 ^ e := by
      have := Subgroup.relIndex_dvd_index_of_normal (H := F) (K := J)
      rwa [he] at this
    rw [← h1, pow_add, show 9 * (2 ^ e * 2 ^ c) = 2 ^ e * (9 * 2 ^ c) by ring]
    exact mul_dvd_mul h2 hc
  · have hPF : (P' : Subgroup _) ≤ F := by
      intro z hz
      obtain ⟨a, ha⟩ := P'.isPGroup' ⟨z, hz⟩
      have hza : z ^ (k.p ^ a) = 1 := by simpa using congrArg Subtype.val ha
      have hcop : Nat.Coprime F.index (orderOf z) := by
        rw [he]
        exact Nat.Coprime.pow_left e (Nat.Coprime.coprime_dvd_right
          (orderOf_dvd_of_pow_eq_one hza) (Nat.Coprime.pow_right a (by rw [hp3]; decide)))
      obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
      rw [← hm]
      exact Subgroup.pow_mem _ (F.pow_index_mem z) m
    rw [inf_eq_left.2 hPF] at hQ9
    have hRp : IsPGroup k.p R := fun x => by
      obtain ⟨n, hn⟩ := hR x
      exact ⟨n, by rw [show k.p ^ n = 3 ^ n by rw [hp3]]; exact hn⟩
    obtain ⟨Q, hRQ⟩ := hRp.exists_le_sylow
    obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (↥H ⧸ CFSG.pPrimeCore k.p ↥H) P' Q
    calc Nat.card R ≤ Nat.card ((g • P' : Sylow k.p _) : Subgroup _) := Subgroup.card_le_of_le hRQ
      _ = Nat.card (P' : Subgroup _) := by
          rw [Sylow.card_eq_multiplicity (g • P'), ← Sylow.card_eq_multiplicity P']
      _ = 9 := hQ9

theorem uc22ine229_l34_solvable (hG3 : Gls3StronglyThreeEmbeddedPlus)
    (hRee : CFSG.AGLEmbedding.KFactReeInvolution) (k : Sec7Core4 G) (hp3 : k.p = 3)
    {H : Subgroup G} (hH : Sec7Core4.Config k H)
    (hF : IsoLie ↥(CFSG.generalizedFitting (↥H ⧸ CFSG.pPrimeCore k.p ↥H))
      (.A 2 ⟨2, 2, Nat.prime_two, by norm_num⟩)) :
    Group.IsSolvable ↥(H ⊓ k.M) ∧
      ∀ R : Subgroup G, R ≤ H → IsPGroup 3 R → Nat.card R ≤ 3 ^ 2 := by
  obtain ⟨⟨c, hc⟩, hR⟩ := uc22ine229_l34_data hG3 hRee k hp3 hH hF
  haveI : Fact k.p.Prime := ⟨k.prime⟩
  set K_ := CFSG.pPrimeCore k.p ↥H
  refine ⟨?_, fun R hRH hR3 => ?_⟩
  · set A := (H ⊓ k.M).subgroupOf H
    haveI : Group.IsSolvable ↥K_ :=
      CFSG.FeitThompson.isSolvable_of_odd_natCard _ (k.odd_card_pPrimeCore_of_not_le hH.not_le hH.two_le_pRank)
    have hKA : K_ ≤ A := fun x hx =>
      mem_subgroupOf.2 ⟨x.2, k.pPrimeCore_le_of_not_le hH.not_le hH.two_le_pRank ⟨x, hx, rfl⟩⟩
    obtain ⟨i, j, hij⟩ := uc22ine229_l34_exists_two_three hc
    haveI : Group.IsSolvable ↥(A.map (QuotientGroup.mk' K_)) := by
      letI := Fintype.ofFinite ↥(A.map (QuotientGroup.mk' K_))
      exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
        Nat.prime_two Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card, hij])
    haveI : Group.IsSolvable ↥(K_.subgroupOf A) :=
      Group.isSolvable_of_isSolvable_injective (f := (Subgroup.subgroupOfEquivOfLe hKA).toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hKA).injective
    haveI : Group.IsSolvable ↥A :=
      Group.isSolvable_of_ker_le_range (K_.subgroupOf A).subtype
        ((QuotientGroup.mk' K_).subgroupMap A) fun x hx => by
          have h1 : QuotientGroup.mk' K_ (x : ↥H) = 1 :=
            congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
          have h2 : (x : ↥H) ∈ K_ := (QuotientGroup.eq_one_iff (x : ↥H)).1 h1
          exact ⟨⟨x, mem_subgroupOf.2 h2⟩, rfl⟩
    exact Group.isSolvable_of_surjective
      (f := (Subgroup.subgroupOfEquivOfLe (inf_le_left : H ⊓ k.M ≤ H)).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe (inf_le_left : H ⊓ k.M ≤ H)).surjective
  · have hR' : IsPGroup 3 (R.subgroupOf H) :=
      hR3.of_injective (Subgroup.subgroupOfEquivOfLe hRH).toMonoidHom
        (Subgroup.subgroupOfEquivOfLe hRH).injective
    have hker : ¬ 3 ∣ Nat.card (QuotientGroup.mk' K_).ker := by
      rw [QuotientGroup.ker_mk']
      have h : Nat.Coprime k.p (Nat.card ↥K_) := CFSG.pPrimeCore_coprime_card
      rw [hp3] at h
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 h
    have hdis := CFSG.RankThree.PartOne.N143.disjoint_ker_of_isPGroup
      (QuotientGroup.mk' K_) Nat.prime_three hR' hker
    have h1 := hR ((R.subgroupOf H).map (QuotientGroup.mk' K_))
      (CFSG.RankThree.PartOne.N143.isPGroup_map_subgroup (QuotientGroup.mk' K_) hR')
    rw [CFSG.RankThree.PartOne.N143.card_map_of_disjoint_ker _ hdis] at h1
    calc Nat.card R = Nat.card (R.subgroupOf H) :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRH).toEquiv.symm
      _ ≤ 9 := h1
      _ = 3 ^ 2 := by norm_num

theorem uc22ine229_l34_mem_pPrimeCore (hG3 : Gls3StronglyThreeEmbeddedPlus)
    (hRee : CFSG.AGLEmbedding.KFactReeInvolution) (k : Sec7Core4 G) (hp3 : k.p = 3)
    {H : Subgroup G} (hH : Sec7Core4.Config k H)
    (hF : IsoLie ↥(CFSG.generalizedFitting (↥H ⧸ CFSG.pPrimeCore k.p ↥H))
      (.A 2 ⟨2, 2, Nat.prime_two, by norm_num⟩))
    {y : G} (hy : y ∈ H ⊓ k.M) (h6 : Nat.Coprime (orderOf y) 6) :
    ∃ hyH : y ∈ H, (⟨y, hyH⟩ : ↥H) ∈ CFSG.pPrimeCore k.p ↥H := by
  obtain ⟨⟨c, hc⟩, -⟩ := uc22ine229_l34_data hG3 hRee k hp3 hH hF
  refine ⟨hy.1, ?_⟩
  have hyJ : QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥H) ⟨y, hy.1⟩ ∈ ((H ⊓ k.M).subgroupOf H).map
      (QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥H)) :=
    Subgroup.mem_map_of_mem _ (mem_subgroupOf.2 hy)
  have h1 : orderOf (QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥H) ⟨y, hy.1⟩) ∣ orderOf y :=
    (orderOf_map_dvd _ _).trans (by rw [Subgroup.orderOf_mk])
  have h2 := orderOf_dvd_natCard (⟨_, hyJ⟩ :
    ↥(((H ⊓ k.M).subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥H))))
  rw [← Subgroup.orderOf_coe] at h2
  have h3 : Nat.Coprime (orderOf (QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥H) ⟨y, hy.1⟩))
      (9 * 2 ^ c) := by
    have h6' := Nat.Coprime.coprime_dvd_left h1 h6
    exact (Nat.Coprime.pow_right 2
      (Nat.Coprime.coprime_dvd_right (by norm_num : 3 ∣ 6) h6')).mul_right
      (Nat.Coprime.pow_right c (Nat.Coprime.coprime_dvd_right (by norm_num : 2 ∣ 6) h6'))
  have h4 := Nat.Coprime.eq_one_of_dvd h3 (h2.trans hc)
  rw [orderOf_eq_one_iff] at h4
  exact (QuotientGroup.eq_one_iff _).1 h4

end CFSG.LocalAnalysis.UniquenessCase.UC22
