module

public import CFSG.RankThree.PartTwo.Sec5.Hyp
import CFSG.RankThree.PartTwo.Sec5.Theorem51
import CFSG.RankThree.PartTwo.Source.GammaTwoSubgroups
import CFSG.RankThree.PartTwo.Source.MinimalFaithfulCentralProduct
import CFSG.RankThree.PartTwo.Source.OrderThreeMinimalTwoGroup
import CFSG.RankThree.PartTwo.Source.PiecesContradiction
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.RankThree.PartTwo.Late.Defs

public section

namespace CFSG.RankThree.PartTwo.Sec6

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

universe u

variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
theorem isKleinFour_of_isElemAbelian {T : Subgroup G} (hT : CFSG.Assembly.IsElemAbelian 2 T)
    (hT4 : Nat.card T = 4) : IsKleinFour T := by
  refine ⟨hT4, ?_⟩
  have hdvd : Monoid.exponent T ∣ 2 := Monoid.exponent_dvd_of_forall_pow_eq_one fun t =>
    Subtype.ext (by rw [Subgroup.coe_pow]; exact hT.2 t t.2)
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exfalso
    have : Subsingleton T := Monoid.exp_eq_one_iff.mp h
    have := Finite.card_le_one_iff_subsingleton.mpr this
    omega
  · exact h

omit [Finite G] in
theorem not_isCyclic_of_isElemAbelian_two {T : Subgroup G}
    (hT : CFSG.Assembly.IsElemAbelian 2 T) (hT4 : Nat.card T = 4) : ¬ IsCyclic T := by
  have := isKleinFour_of_isElemAbelian hT hT4
  exact IsKleinFour.not_isCyclic

theorem card_inf_centralizer_of_mem_fourGroupsMinus {A T : Subgroup G} (hA : Late.IsE27 A)
    (hT : T ∈ fourGroupsMinus A) :
    Nat.card (A ⊓ Subgroup.centralizer (T : Set G) : Subgroup G) = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hTU, hTeq⟩ := hT
  obtain ⟨hAT, hTab, hT4⟩ := mem_fourGroups_iff.mp hTU
  have hK4 := isKleinFour_of_isElemAbelian hTab hT4
  have hcop : Nat.Coprime 3 (Nat.card T) := by rw [hT4]; norm_num
  obtain ⟨H, hHA, hH9, v, hv, hv1⟩ : ∃ H : Subgroup G, H ≤ A ∧ Nat.card H = 3 ^ 2 ∧
      ∃ v ∈ T ⊓ Subgroup.centralizer (H : Set G), v ≠ 1 := by
    by_contra hno
    push Not at hno
    have hTbot : T ≤ ⊥ := Sec5.le_of_forall_inf_centralizer_sub_le (k := 2) Nat.prime_three hA.1
      (by rw [hA.2]; norm_num) hAT hcop
      fun H hHA hH v hv => Subgroup.mem_bot.mpr (hno H hHA hH v hv)
    rw [le_bot_iff.mp hTbot, Subgroup.card_bot] at hT4
    norm_num at hT4
  have hHT : H ≤ A ⊓ Subgroup.centralizer (T : Set G) := fun x hx =>
    Subgroup.mem_inf.mpr ⟨hHA hx, Source.mem_centralizer_of_kleinFour hK4 (hA.1.2 x (hHA hx))
      (hAT (hHA hx)) hv.1 hv1 (Subgroup.mem_centralizer_iff.mp hv.2 x hx)⟩
  have h9 : 9 ∣ Nat.card (A ⊓ Subgroup.centralizer (T : Set G) : Subgroup G) := by
    have := Subgroup.card_dvd_of_le hHT
    rwa [hH9] at this
  have h27 : Nat.card (A ⊓ Subgroup.centralizer (T : Set G) : Subgroup G) ∣ 3 ^ 3 := by
    have := Subgroup.card_dvd_of_le (inf_le_left : A ⊓ Subgroup.centralizer (T : Set G) ≤ A)
    rwa [hA.2] at this
  have hne : Nat.card (A ⊓ Subgroup.centralizer (T : Set G) : Subgroup G) ≠ 27 := by
    intro h27'
    have hAeq : A ⊓ Subgroup.centralizer (T : Set G) = A :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h27', hA.2])
    have hTA : ⁅T, A⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.le_centralizer_iff]
      exact inf_eq_left.mp hAeq
    rw [← hTeq] at hTA
    rw [hTA, Subgroup.card_bot] at hT4
    norm_num at hT4
  obtain ⟨i, hi, hcard⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h27
  rw [hcard] at h9 hne ⊢
  interval_cases i
  · exfalso; norm_num at h9
  · exfalso; norm_num at h9
  · rfl
  · exfalso; exact hne rfl

section Transport

variable {X : Subgroup G}

omit [Finite G] in
theorem map_subgroupOf_inf_centralizer {K L : Subgroup G} (hK : K ≤ X) (hL : L ≤ X) :
    (K.subgroupOf X ⊓ Subgroup.centralizer ((L.subgroupOf X : Subgroup X) : Set X)).map
        X.subtype = K ⊓ Subgroup.centralizer (L : Set G) := by
  ext g
  constructor
  · rintro ⟨y, ⟨hyK, hyC⟩, rfl⟩
    refine ⟨hyK, Subgroup.mem_centralizer_iff.mpr fun l hl => ?_⟩
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hyC ⟨l, hL hl⟩ hl)
  · rintro ⟨hgK, hgC⟩
    refine ⟨⟨g, hK hgK⟩, ⟨hgK, Subgroup.mem_centralizer_iff.mpr fun l hl => ?_⟩, rfl⟩
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hgC l hl)

omit [Finite G] in
theorem subgroupOf_le_normalizer_subgroupOf {A S : Subgroup G}
    (hAS : A ≤ Subgroup.normalizer (S : Set G)) :
    A.subgroupOf X ≤ Subgroup.normalizer ((S.subgroupOf X : Subgroup X) : Set X) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro y
  exact Subgroup.mem_normalizer_iff.mp (hAS ha) y

omit [Finite G] in
theorem isElemAbelian_subgroupOf {p : ℕ} {A : Subgroup G} (hA : CFSG.Assembly.IsElemAbelian p A) :
    CFSG.Assembly.IsElemAbelian p (A.subgroupOf X) := CFSG.Open.IsElemAbelian.subgroupOf hA X

omit [Finite G] in
theorem card_subgroupOf_of_le {K : Subgroup G} (hK : K ≤ X) :
    Nat.card (K.subgroupOf X) = Nat.card K :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK).toEquiv

end Transport

theorem statement51_ambient (he : CFSG.Assembly.evenRank G = 3)
    {A S P T : Subgroup G} (hA : Late.IsE27 A) (hS : IsPGroup 2 S)
    (hAS : A ≤ Subgroup.normalizer (S : Set G)) (hP : IsPGroup 3 P)
    (hPN : A ⊔ S ≤ Subgroup.normalizer (P : Set G)) (hPS : ⁅P, S⁆ ≠ ⊥) (hTS : T ≤ S)
    (hT : T ≠ ⊥) (hAT : A ≤ Subgroup.normalizer (T : Set G)) :
    (Nat.card (A ⊓ Subgroup.centralizer (S : Set G) : Subgroup G) = 9 ∧
        S ⊓ Subgroup.centralizer (A : Set G) = ⊥) ∨
      ∀ W : Subgroup G, W ≤ S → A ≤ Subgroup.normalizer (W : Set G) → IsMulCommutative W →
        IsCyclic W := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set X := P ⊔ (A ⊔ S) with hX
  have hPX : P ≤ X := le_sup_left
  have hAX : A ≤ X := le_sup_left.trans le_sup_right
  have hSX : S ≤ X := le_sup_right.trans le_sup_right
  have hTX : T ≤ X := hTS.trans hSX
  have hXP : X ≤ Subgroup.normalizer (P : Set G) := sup_le Subgroup.le_normalizer hPN
  have hPn : (P.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPX).mpr hXP
  have hyp : SectionFiveHyp (A.subgroupOf X) (S.subgroupOf X) := by
    refine ⟨isElemAbelian_subgroupOf hA.1, by rw [card_subgroupOf_of_le hAX, hA.2], ?_, ?_, ?_⟩
    · rw [mem_invariantPiSubgroups_piOf_iff Nat.prime_two]
      exact ⟨le_top, hS.comap_of_injective X.subtype X.subtype_injective,
        subgroupOf_le_normalizer_subgroupOf hAS⟩
    · intro hbot
      apply hPS
      have hP3 : P.subgroupOf X ≤ CFSG.pCore 3 X :=
        le_sSup ⟨hPn, hP.comap_of_injective X.subtype X.subtype_injective⟩
      have hle : ⁅P.subgroupOf X, S.subgroupOf X⁆ ≤ ⁅CFSG.pCore 3 X, S.subgroupOf X⁆ :=
        Subgroup.commutator_mono hP3 le_rfl
      rw [hbot, le_bot_iff] at hle
      have := congrArg (Subgroup.map X.subtype) hle
      rwa [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hPX,
        Subgroup.map_subgroupOf_eq_of_le hSX, Subgroup.map_bot] at this
    · apply le_antisymm ((evenRank_subgroup_le X).trans he.le)
      have hT' : T.subgroupOf X ≠ ⊥ := by
        intro h
        apply hT
        rw [← Subgroup.map_subgroupOf_eq_of_le hTX, h, Subgroup.map_bot]
      have hloc : CFSG.Assembly.IsTwoLocal
          (Subgroup.normalizer ((T.subgroupOf X : Subgroup X) : Set X)) :=
        ⟨T.subgroupOf X, hT',
          (hS.to_le hTS).comap_of_injective X.subtype X.subtype_injective, rfl⟩
      have h3 : 3 ≤ CFSG.Open.pRank 3
          (Subgroup.normalizer ((T.subgroupOf X : Subgroup X) : Set X)) :=
        le_csSup (CFSG.RankThreeEvenClassification.Helpers.pRank_bddAbove 3 Nat.prime_three _)
          ⟨A.subgroupOf X, subgroupOf_le_normalizer_subgroupOf hAT,
            isElemAbelian_subgroupOf hA.1, by rw [card_subgroupOf_of_le hAX, hA.2]; norm_num⟩
      exact h3.trans (CFSG.RankThreeEvenClassification.Helpers.pRank_le_evenRank 3
        Nat.prime_three (by norm_num) _ hloc)
  rcases (Sec5.rank3II_5_1 hyp : Sec5.Statement51 _ _) with ⟨h1, h2, -⟩ | h2
  · left
    refine ⟨?_, ?_⟩
    · rw [← map_subgroupOf_inf_centralizer hAX hSX,
        Subgroup.card_map_of_injective X.subtype_injective]
      exact h1
    · rw [← map_subgroupOf_inf_centralizer hSX hAX, h2, Subgroup.map_bot]
  · right
    intro W hWS hAW hWc
    have hWX : W ≤ X := hWS.trans hSX
    have hWc' : IsMulCommutative (W.subgroupOf X) := by
      refine ⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩
      show ((a : X) : G) * ((b : X) : G) = ((b : X) : G) * ((a : X) : G)
      exact congrArg Subtype.val (hWc.is_comm.comm ⟨((a : X) : G), a.2⟩ ⟨((b : X) : G), b.2⟩)
    have hc := h2 (W.subgroupOf X) (fun x hx => hWS hx) (subgroupOf_le_normalizer_subgroupOf hAW)
      hWc'
    exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hWX).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hWX).surjective

theorem rank3II_6_4_2_of_evenRank_eq (he : CFSG.Assembly.evenRank G = 3)
    {A : Subgroup G} (hA : Late.IsE27 A) {T : Subgroup G} (hT : T ∈ fourGroupsPlus A)
    {S : Subgroup G} (hS : S ∈ invariantPiSubgroups ⊤ A (piOf 2)) (hTS : T ≤ S)
    {P : Subgroup G} (hP : P ∈ invariantPiSubgroups ⊤ (A ⊔ S) (piOf 3)) :
    P ≤ Subgroup.centralizer (S : Set G) := by
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
  by_contra hPS
  obtain ⟨-, hS2, hAS⟩ := (mem_invariantPiSubgroups_piOf_iff Nat.prime_two).mp hS
  obtain ⟨-, hP3, hPN⟩ := (mem_invariantPiSubgroups_piOf_iff Nat.prime_three).mp hP
  obtain ⟨hTU, hTA⟩ := hT
  obtain ⟨hAT, hTab, hT4⟩ := mem_fourGroups_iff.mp hTU
  have hT1 : T ≠ ⊥ := fun h => by rw [h, Subgroup.card_bot] at hT4; norm_num at hT4
  rcases statement51_ambient he hA hS2 hAS hP3 hPN hPS hTS hT1 hAT with ⟨-, h2⟩ | h2
  · apply hT1
    rw [eq_bot_iff, ← h2]
    exact le_inf hTS (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hTA)
  · exact not_isCyclic_of_isElemAbelian_two hTab hT4 (h2 T hTS hAT hTab.1)

theorem rank3II_6_4_2 :
    ∀ (G : Type) [Group G] [Finite G], PartTwoStanding G → ∀ A ∈ partTwoE G,
      ∀ T ∈ fourGroupsPlus A, ∀ S ∈ invariantPiSubgroups ⊤ A (piOf 2), T ≤ S →
        ∀ P ∈ invariantPiSubgroups ⊤ (A ⊔ S) (piOf 3), P ≤ Subgroup.centralizer (S : Set G) :=
  fun _ _ _ h _ hA _ hT _ hS hTS _ hP =>
    rank3II_6_4_2_of_evenRank_eq h.evenRank_eq (Late.isE27_of_mem_partTwoE hA) hT hS hTS hP

theorem rank3II_6_4_3_of_charTwo (hchar : CFSG.Assembly.IsCharTwoType G) {A : Subgroup G}
    (hA : Late.IsE27 A) {T : Subgroup G} (hT : T ∈ fourGroupsMinus A) :
    ∃ a ∈ A ⊓ Subgroup.centralizer (T : Set G), a ≠ 1 ∧
      ∃ S ∈ invariantPiSubgroups (Subgroup.centralizer {a}) A (piOf 2), T ≤ S ∧
        ¬ S ≤ Subgroup.centralizer ((A ⊓ Subgroup.centralizer (T : Set G) : Subgroup G) :
          Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hB9 := card_inf_centralizer_of_mem_fourGroupsMinus hA hT
  obtain ⟨hTU, -⟩ := hT
  obtain ⟨hAT, hTab, hT4⟩ := mem_fourGroups_iff.mp hTU
  have hT2 : IsPGroup 2 T := IsPGroup.of_card (n := 2) (by rw [hT4]; norm_num)
  have hT1 : T ≠ ⊥ := fun h => by rw [h, Subgroup.card_bot] at hT4; norm_num at hT4
  set B := A ⊓ Subgroup.centralizer (T : Set G) with hB
  set C := Subgroup.centralizer (T : Set G) with hC
  set Q := CFSG.Assembly.pCoreOf 2 C with hQ
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 C
  have hCT : C ≤ Subgroup.normalizer (T : Set G) := Subgroup.centralizer_le_normalizer _
  have hTC : T ≤ C := fun t ht => Subgroup.mem_centralizer_iff.mpr fun s hs =>
    congrArg Subtype.val (hTab.1.is_comm.comm ⟨s, hs⟩ ⟨t, ht⟩)
  have hTQ : T ≤ Q := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hTC hCT hT2
  have hAC : A ≤ Subgroup.normalizer (C : Set G) := fun a ha =>
    Source.mem_normalizer_centralizer (hAT ha)
  have hAQ : A ≤ Subgroup.normalizer (Q : Set G) := fun a ha =>
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 C (hAC ha)
  have hBQ : ¬ Q ≤ Subgroup.centralizer (B : Set G) := by
    intro hQB
    set N := Subgroup.normalizer (T : Set G) with hN
    have hNl : CFSG.Assembly.IsTwoLocal N := ⟨T, hT1, hT2, rfl⟩
    set R := CFSG.Assembly.pCoreOf 2 N with hR
    have hR2 : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N
    have hNR : N ≤ Subgroup.normalizer (R : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 N
    have hRN : R ≤ N := CFSG.LieType.BorelTits.pCoreOf_le 2 N
    have hBN : B ≤ N := inf_le_right.trans hCT
    have hRC : R ⊓ C ≤ Q := by
      refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right ?_
        (hR2.to_le inf_le_left)
      exact (le_inf (hCT.trans hNR) Subgroup.le_normalizer).trans
        Subgroup.inf_normalizer_le_normalizer_inf
    have hBR : B ≤ Subgroup.centralizer (R : Set G) := by
      intro b hb
      rw [Subgroup.mem_centralizer_iff]
      intro r hr
      have hbT : b ∈ Subgroup.centralizer (T : Set G) := hb.2
      have hrN : r ∈ N := hRN hr
      have hcR : b * r * b⁻¹ * r⁻¹ ∈ R :=
        R.mul_mem ((Subgroup.mem_normalizer_iff.mp (hNR (hBN hb)) r).mp hr) (R.inv_mem hr)
      have hcC : b * r * b⁻¹ * r⁻¹ ∈ C := by
        rw [Subgroup.mem_centralizer_iff]
        intro t ht
        have ht' : r⁻¹ * t * r ∈ T := by
          have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hrN) t).mp ht
          simpa using this
        have hb' : (r⁻¹ * t * r) * b = b * (r⁻¹ * t * r) :=
          Subgroup.mem_centralizer_iff.mp hbT _ ht'
        have hbt : t * b = b * t := Subgroup.mem_centralizer_iff.mp hbT t ht
        have hb'' : b⁻¹ * (r⁻¹ * t * r) = (r⁻¹ * t * r) * b⁻¹ := by
          calc b⁻¹ * (r⁻¹ * t * r) = b⁻¹ * ((r⁻¹ * t * r) * b) * b⁻¹ := by group
            _ = b⁻¹ * (b * (r⁻¹ * t * r)) * b⁻¹ := by rw [hb']
            _ = (r⁻¹ * t * r) * b⁻¹ := by group
        symm
        calc b * r * b⁻¹ * r⁻¹ * t = b * r * (b⁻¹ * (r⁻¹ * t * r)) * r⁻¹ := by group
          _ = b * r * ((r⁻¹ * t * r) * b⁻¹) * r⁻¹ := by rw [hb'']
          _ = b * t * (r * b⁻¹ * r⁻¹) := by group
          _ = t * b * (r * b⁻¹ * r⁻¹) := by rw [hbt]
          _ = t * (b * r * b⁻¹ * r⁻¹) := by group
      obtain ⟨c, hc⟩ : ∃ c : G, c = b * r * b⁻¹ * r⁻¹ := ⟨_, rfl⟩
      rw [← hc] at hcR hcC
      have hcQ : c ∈ Q := hRC ⟨hcR, hcC⟩
      have hbc : b * c = c * b := Subgroup.mem_centralizer_iff.mp (hQB hcQ) b hb
      have hb3 : b ^ 3 = 1 := hA.1.2 b hb.1
      have hbrb : b * r * b⁻¹ = c * r := by rw [hc]; group
      have hconj : ∀ y : G, b * (c * y) * b⁻¹ = c * (b * y * b⁻¹) := fun y => by
        calc b * (c * y) * b⁻¹ = (b * c) * y * b⁻¹ := by group
          _ = (c * b) * y * b⁻¹ := by rw [hbc]
          _ = c * (b * y * b⁻¹) := by group
      have hb3' : b * (b * b) = 1 := by rw [← pow_three]; exact hb3
      have key : r = c * (c * (c * r)) := by
        calc r = b * (b * b) * r * (b * (b * b))⁻¹ := by rw [hb3', one_mul, inv_one, mul_one]
          _ = b * (b * (b * r * b⁻¹) * b⁻¹) * b⁻¹ := by group
          _ = b * (b * (c * r) * b⁻¹) * b⁻¹ := by rw [hbrb]
          _ = b * (c * (b * r * b⁻¹)) * b⁻¹ := by rw [hconj r]
          _ = b * (c * (c * r)) * b⁻¹ := by rw [hbrb]
          _ = c * (b * (c * r) * b⁻¹) := by rw [hconj (c * r)]
          _ = c * (c * (b * r * b⁻¹)) := by rw [hconj r]
          _ = c * (c * (c * r)) := by rw [hbrb]
      have hc3 : c ^ 3 = 1 := by
        have h' : c * (c * c) = 1 := by
          calc c * (c * c) = c * (c * (c * r)) * r⁻¹ := by group
            _ = r * r⁻¹ := by rw [← key]
            _ = 1 := mul_inv_cancel r
        rw [pow_three]
        exact h'
      have hc1 : c = 1 := Source.eq_one_of_pow_three_eq_one hR2 hcR hc3
      calc r * b = c⁻¹ * (b * r * b⁻¹) * b := by rw [hbrb]; group
        _ = b * r := by rw [hc1]; group
    have hBR' : B ≤ R := (le_inf hBN hBR).trans (hchar N hNl)
    have hB3 : IsPGroup 3 B := hA.isPGroup.to_le inf_le_left
    have hbot : B = ⊥ := by
      have := Source.inf_eq_bot_of_isPGroup (p := 3) (q := 2) (by norm_num) hB3 hR2
      rwa [inf_eq_left.mpr hBR'] at this
    rw [hbot, Subgroup.card_bot] at hB9
    norm_num at hB9
  have hBe : CFSG.Assembly.IsElemAbelian 3 B := Source.isElemAbelian_of_le hA.1 inf_le_left
  have hcopQ : Nat.Coprime 3 (Nat.card Q) := by
    obtain ⟨k, hk⟩ := hQ2.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k (by norm_num)
  obtain ⟨a, haB, ha1, haS⟩ : ∃ a ∈ B, a ≠ 1 ∧
      ¬ Q ⊓ Subgroup.centralizer {a} ≤ Subgroup.centralizer (B : Set G) := by
    by_contra hno
    push Not at hno
    exact hBQ (Sec5.le_of_forall_inf_centralizer_le Nat.prime_three hBe (by rw [hB9]; norm_num)
      (inf_le_left.trans hAQ) hcopQ hno)
  have haA : a ∈ A := haB.1
  refine ⟨a, haB, ha1, Q ⊓ Subgroup.centralizer {a}, ?_, le_inf hTQ ?_, haS⟩
  · rw [mem_invariantPiSubgroups_piOf_iff Nat.prime_two]
    refine ⟨inf_le_right, hQ2.to_le inf_le_left, ?_⟩
    have hACa : A ≤ Subgroup.centralizer {a} := fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (hA.1.1.is_comm.comm ⟨x, hx⟩ ⟨a, haA⟩))
    exact (le_inf hAQ (hACa.trans Subgroup.le_normalizer)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  · intro t ht
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp haB.2 t ht)

theorem rank3II_6_4_3 :
    ∀ (G : Type) [Group G] [Finite G], PartTwoStanding G → ∀ A ∈ partTwoE G,
      ∀ T ∈ fourGroupsMinus A, ∃ a ∈ A ⊓ Subgroup.centralizer (T : Set G), a ≠ 1 ∧
        ∃ S ∈ invariantPiSubgroups (Subgroup.centralizer {a}) A (piOf 2), T ≤ S ∧
          ¬ S ≤ Subgroup.centralizer ((A ⊓ Subgroup.centralizer (T : Set G) : Subgroup G) : Set G) :=
  fun _ _ _ h _ hA _ hT =>
  rank3II_6_4_3_of_charTwo h.charTwoType (Late.isE27_of_mem_partTwoE hA) hT

theorem rank3II_6_4_4_of_evenRank_eq (he : CFSG.Assembly.evenRank G = 3)
    {A : Subgroup G} (hA : Late.IsE27 A) {T : Subgroup G} (hT : T ∈ fourGroupsMinus A)
    {S : Subgroup G} (hS : S ∈ invariantPiSubgroups ⊤ A (piOf 2)) (hTS : T ≤ S)
    (hST : ⁅S, A ⊓ Subgroup.centralizer (T : Set G)⁆ ≠ ⊥) {P : Subgroup G}
    (hP : P ∈ invariantPiSubgroups ⊤ (A ⊔ S) (piOf 3)) :
    P ≤ Subgroup.centralizer (S : Set G) := by
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
  by_contra hPS
  have hB9 := card_inf_centralizer_of_mem_fourGroupsMinus hA hT
  obtain ⟨-, hS2, hAS⟩ := (mem_invariantPiSubgroups_piOf_iff Nat.prime_two).mp hS
  obtain ⟨-, hP3, hPN⟩ := (mem_invariantPiSubgroups_piOf_iff Nat.prime_three).mp hP
  obtain ⟨hTU, -⟩ := hT
  obtain ⟨hAT, hTab, hT4⟩ := mem_fourGroups_iff.mp hTU
  have hT1 : T ≠ ⊥ := fun h => by rw [h, Subgroup.card_bot] at hT4; norm_num at hT4
  rcases statement51_ambient he hA hS2 hAS hP3 hPN hPS hTS hT1 hAT with ⟨h1, -⟩ | h2
  · have hle : A ⊓ Subgroup.centralizer (S : Set G) ≤ A ⊓ Subgroup.centralizer (T : Set G) :=
      inf_le_inf_left _ (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hTS))
    have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [h1, hB9])
    apply hST
    rw [← heq, Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.le_centralizer_iff]
    exact inf_le_right
  · exact not_isCyclic_of_isElemAbelian_two hTab hT4 (h2 T hTS hAT hTab.1)

theorem rank3II_6_4_4 :
    ∀ (G : Type) [Group G] [Finite G], PartTwoStanding G → ∀ A ∈ partTwoE G,
      ∀ T ∈ fourGroupsMinus A, ∀ S ∈ invariantPiSubgroups ⊤ A (piOf 2), T ≤ S →
        ⁅S, A ⊓ Subgroup.centralizer (T : Set G)⁆ ≠ ⊥ →
        ∀ P ∈ invariantPiSubgroups ⊤ (A ⊔ S) (piOf 3), P ≤ Subgroup.centralizer (S : Set G) :=
  fun _ _ _ h _ hA _ hT _ hS hTS hST _ hP =>
    rank3II_6_4_4_of_evenRank_eq h.evenRank_eq (Late.isE27_of_mem_partTwoE hA) hT hS hTS hST hP

end CFSG.RankThree.PartTwo.Sec6
