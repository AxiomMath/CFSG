module

public import CFSG.RankThree.PartTwo.Sec6.Item611Res2Proof
import CFSG.RankThree.PartTwo.Sec6.Item612
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.LocalAnalysis.LargeEvenClassification.CoprimeCommutators

public section

namespace CFSG.RankThree.PartTwo.Sec6

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL projSU)


section Certs


@[expose] def Item611FieldL2S : Prop :=
  ∀ (G : Type) [Group G] [Finite G], PartTwoStanding G → ∀ A ∈ partTwoS G,
    4 < CFSG.Open.pRank 3 A → ∀ c ∈ A, c ≠ 1 → ∀ L ∈ lZeroStarAt A c,
      A ⊓ thetaQuotCentralizer L = Subgroup.zpowers c →
      ∀ E ∈ collectionIn (partTwoE G) A, L ∈ lZero E → ∀ T ∈ fourGroupsMinus E, T ≤ L →
        T ⊓ inSubgroup (aschbacherSolvableCore 3) L = ⊥ →
      (∃ e ∈ A, ∃ m : ℕ, 2 < m ∧
        Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSL 2 (GaloisField 3 (3 * m))) ∧
        KFacts.InducesStdKind L e .field) →
      c ∈ E → ∀ d ∈ E ⊓ Subgroup.centralizer (T : Set G), d ∉ Subgroup.zpowers c →
      ∀ S ∈ invariantPiSubgroups (Subgroup.centralizer {d} ⊓ Subgroup.centralizer (T : Set G)) E
          (piOf 2),
        S ≠ ⊥ → ⁅S, Subgroup.zpowers c⁆ = S → False

end Certs

namespace Res611Field

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem normalizer_le_normalizer_centralizer (T : Subgroup G) :
    Subgroup.normalizer (T : Set G) ≤
      Subgroup.normalizer ((Subgroup.centralizer (T : Set G) : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  simp only [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  constructor
  · intro hx t ht
    have ht' : g⁻¹ * t * g ∈ T := by
      have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) t).mp ht
      simpa using h
    have h := hx _ ht'
    calc t * (g * x * g⁻¹) = g * ((g⁻¹ * t * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * t * g)) * g⁻¹ := by rw [h]
      _ = g * x * g⁻¹ * t := by group
  · intro hx t ht
    have ht' : g * t * g⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp hg t).mp ht
    have h := hx _ ht'
    have h2 : g * (t * x) * g⁻¹ = g * (x * t) * g⁻¹ := by
      calc g * (t * x) * g⁻¹ = (g * t * g⁻¹) * (g * x * g⁻¹) := by group
        _ = (g * x * g⁻¹) * (g * t * g⁻¹) := h
        _ = g * (x * t) * g⁻¹ := by group
    simpa using h2

omit [Finite G] in
theorem le_normalizer_commutator_of {X H K : Subgroup G} (hH : X ≤ Subgroup.normalizer (H : Set G))
    (hK : X ≤ Subgroup.normalizer (K : Set G)) :
    X ≤ Subgroup.normalizer ((⁅H, K⁆ : Subgroup G) : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator,
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hH hx),
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hK hx)]

theorem mem_of_mem_lZero {A E L : Subgroup G} (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (hEA : E ≤ A) {c : G} (hc1 : c ≠ 1)
    (hCA : A ⊓ thetaQuotCentralizer L = Subgroup.zpowers c) (hLE : L ∈ lZero E) : c ∈ E := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e, heE, he1, hLe⟩ := mem_thetaComponentFamily_iff.mp hLE.1
  have heC : e ∈ Subgroup.zpowers c :=
    hCA ▸ ⟨hEA heE, mem_thetaQuotCentralizer_of_mem_thetaComponentsAt hLe⟩
  have hc3 : orderOf c = 3 := orderOf_eq_prime (hA.2 c (hCA ▸ Subgroup.mem_zpowers c).1) hc1
  have he3 : orderOf e = 3 := orderOf_eq_prime (hA.2 e (hEA heE)) he1
  have heq : Subgroup.zpowers e = Subgroup.zpowers c :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr heC)
      (by rw [Nat.card_zpowers, Nat.card_zpowers, hc3, he3])
  exact (Subgroup.zpowers_le.mpr heE) (heq ▸ Subgroup.mem_zpowers c)

theorem exists_d_S (hchar : CFSG.Assembly.IsCharTwoType G) {E T : Subgroup G}
    (hE : E ∈ partTwoE G) (hT : T ∈ fourGroupsMinus E) {c : G} (hcE : c ∈ E) (hc1 : c ≠ 1)
    (hcT : c ∈ Subgroup.centralizer (T : Set G)) :
    ∃ d ∈ E ⊓ Subgroup.centralizer (T : Set G), d ∉ Subgroup.zpowers c ∧
      ∃ S ∈ invariantPiSubgroups (Subgroup.centralizer {d} ⊓ Subgroup.centralizer (T : Set G)) E
        (piOf 2), S ≠ ⊥ ∧ ⁅S, Subgroup.zpowers c⁆ = S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hEab : CFSG.Assembly.IsElemAbelian 3 E := hE.1
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hEab.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  obtain ⟨hEN, hTab, hT4⟩ := mem_fourGroups_iff.mp hT.1
  have hT2 : IsPGroup 2 T := IsPGroup.of_card (n := 2) (by rw [hT4]; norm_num)
  have hT1 : T ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hT4
    omega
  set B := E ⊓ Subgroup.centralizer (T : Set G) with hB
  have hBab : CFSG.Assembly.IsElemAbelian 3 B := Sec5.isElemAbelian_of_le hEab inf_le_left
  have hB9 : Nat.card B = 9 :=
    card_inf_centralizer_of_mem_fourGroupsMinus (Late.isE27_of_mem_partTwoE hE) hT
  have hcB : c ∈ B := ⟨hcE, hcT⟩
  have hFB : Subgroup.zpowers c ≤ B := Subgroup.zpowers_le.mpr hcB
  have hF1 : Subgroup.zpowers c ≠ ⊥ := fun h =>
    hc1 (Subgroup.mem_bot.mp (h ▸ Subgroup.mem_zpowers c))
  obtain ⟨d, hdB, hd1, hne⟩ := exists_commutator_inf_centralizer_ne_bot hchar hT2 hT1 hBab
    (by omega) inf_le_right hFB hF1
  set Q := inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (T : Set G)) with hQ
  set X := Q ⊓ Subgroup.centralizer {d} with hX
  have hQ2 : IsPGroup 2 Q := CFSG.pCore_isPGroup.map _
  have hQC : Q ≤ Subgroup.centralizer (T : Set G) := Subgroup.map_subtype_le _
  have hNQ : Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (Q : Set G) :=
    (normalizer_le_normalizer_centralizer T).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
        (CFSG.pCore 2 (Subgroup.centralizer (T : Set G))))
  have hcN : c ∈ Subgroup.normalizer (T : Set G) := hEN hcE
  have hdE : d ∈ E := hdB.1
  have hNd : ∀ x ∈ E, x ∈ Subgroup.normalizer
      ((Subgroup.centralizer {d} : Subgroup G) : Set G) := fun x hx =>
    Subgroup.le_normalizer (Subgroup.mem_centralizer_singleton_iff.mpr (hEcomm x hx d hdE))
  have hEX : E ≤ Subgroup.normalizer (X : Set G) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hNQ (hEN hx), hNd x hx⟩
  have hcX : Subgroup.zpowers c ≤ Subgroup.normalizer (X : Set G) :=
    Subgroup.zpowers_le.mpr (hEX hcE)
  have hEc : E ≤ Subgroup.normalizer ((Subgroup.zpowers c : Subgroup G) : Set G) := fun x hx =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun y hy => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact ((Commute.zpow_left (hEcomm x hx c hcE).symm k)).eq)
  have hdc : d ∉ Subgroup.zpowers c := by
    intro hdc
    apply hne
    have hc3 : orderOf c = 3 := orderOf_eq_prime (hEab.2 c hcE) hc1
    have hd3 : orderOf d = 3 := orderOf_eq_prime (hEab.2 d hdE) hd1
    have heq : Subgroup.zpowers d = Subgroup.zpowers c :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hdc)
        (by rw [Nat.card_zpowers, Nat.card_zpowers, hc3, hd3])
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer, ← heq, Subgroup.le_centralizer_iff,
      Subgroup.zpowers_le]
    exact Subgroup.mem_centralizer_iff.mpr fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.mp hx.2
  set S := ⁅X, Subgroup.zpowers c⁆ with hS
  have hSX : S ≤ X := Subgroup.le_normalizer_iff_commutator_le_left.mp hcX
  refine ⟨d, hdB, hdc, S, ?_, hne, ?_⟩
  · rw [mem_invariantPiSubgroups_piOf_iff Nat.prime_two]
    refine ⟨fun x hx => ⟨(hSX hx).2, hQC (hSX hx).1⟩, hQ2.to_le (hSX.trans inf_le_left),
      le_normalizer_commutator_of hEX hEc⟩
  · have hX2 : IsPGroup 2 X := hQ2.to_le inf_le_left
    obtain ⟨k, hk⟩ := hX2.exists_card_eq
    have hc3 : IsPGroup 3 (Subgroup.zpowers c) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime (hEab.2 c hcE) hc1,
        pow_one])
    have hX3 : ¬ 3 ∣ Nat.card X := by
      rw [hk]
      intro h
      have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h)
      omega
    exact CFSG.LargeEvenClassification.Helpers.coprime_normalized_commutator_idempotent
      Nat.prime_three _ X hc3 hX3 hcX

end Res611Field

open Res611Field

section Certs


theorem item611FieldL2T_of (hF : Item611FieldL2S) : Item611FieldL2T := by
  intro G _ _ hst A hA hrank c hcA hc1 L hL hCA E hE hLE T hT hTL hTθ he
  have hcE : c ∈ E := mem_of_mem_lZero hA.1.1 hE.2 hc1 hCA hLE
  have hcT : c ∈ Subgroup.centralizer (T : Set G) := by
    have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
      le_centralizer_of_mem_thetaComponentsAt hL.1
    exact Subgroup.mem_centralizer_iff.mpr fun t ht =>
      Subgroup.mem_centralizer_singleton_iff.mp (hLc (hTL ht))
  obtain ⟨d, hdB, hdc, S, hS, hS1, hSc⟩ :=
    exists_d_S hst.charTwoType hE.1 hT hcE hc1 hcT
  exact hF G hst A hA hrank c hcA hc1 L hL hCA E hE hLE T hT hTL hTθ he hcE d hdB hdc S hS hS1 hSc

end Certs

end CFSG.RankThree.PartTwo.Sec6
