module

public import CFSG.RankThree.PartTwo.Sec18.Item189Glue
import CFSG.RankThree.PartTwo.Sec18.Item186a
import CFSG.RankThree.PartTwo.Sec20.OneBasics
import CFSG.RankThree.PartTwo.Sec11.FixedCentralizer
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.RankThree.PartTwo.Sec15.HypR

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.Assembly.RankThreeEven (projSL projSU)


variable {G : Type} [Group G] [Finite G]

theorem card_le_three_of_pRank_le_one189 {K E : Subgroup G} (hK : CFSG.Open.pRank 3 K ≤ 1)
    (hEK : E ≤ K) (hE : CFSG.Open.IsElemAbelian 3 E) : Nat.card E ≤ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hE3 : IsPGroup 3 E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
  obtain ⟨k, hk⟩ := hE3.exists_card_eq
  have hkle : k ≤ CFSG.Open.pRank 3 K :=
    le_csSup (CFSG.RankThreeEvenClassification.Helpers.pRank_bddAbove 3 Nat.prime_three K)
      ⟨E, hEK, hE, hk⟩
  rw [hk]
  calc 3 ^ k ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) (hkle.trans hK)
    _ = 3 := by norm_num

theorem mem_zpowers_of_commute189 {K : Subgroup G} (hK : CFSG.Open.pRank 3 K ≤ 1) {x z : G}
    (hxK : x ∈ K) (hzK : z ∈ K) (hx3 : x ^ 3 = 1) (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1)
    (hxz : x * z = z * x) : x ∈ Subgroup.zpowers z := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZ : CFSG.Assembly.IsElemAbelian 3 (Subgroup.zpowers z) := by
    refine ⟨inferInstance, fun y hy => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz3, one_zpow]
  have hE := Sec15.isElemAbelian_sup_zpowers hZ hx3 fun e he => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp he
    exact ((Commute.zpow_left hxz.symm k).eq)
  have hcard := card_le_three_of_pRank_le_one189 hK
    (sup_le (Subgroup.zpowers_le.mpr hzK) (Subgroup.zpowers_le.mpr hxK)) hE
  have hord : orderOf z = 3 := orderOf_eq_prime hz3 hz1
  have heq : Subgroup.zpowers z = Subgroup.zpowers z ⊔ Subgroup.zpowers x :=
    Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [Nat.card_zpowers, hord]; exact hcard)
  rw [heq]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)

omit [Finite G] in
theorem normalClosureIn_one189 (M : Subgroup G) : normalClosureIn M (1 : G) = ⊥ := by
  rw [normalClosureIn, eq_bot_iff, Subgroup.closure_le]
  rintro _ ⟨m, -, rfl⟩
  simp

theorem ne_one_of_pRank_eq_one189 {M : Subgroup G} {c : G}
    (hrank : CFSG.Open.pRank 3 (normalClosureIn M c) = 1) : c ≠ 1 := by
  rintro rfl
  have h0 := CFSG.RankThreeEvenClassification.Helpers.pRank_le_log_card 3 Nat.prime_three
    (normalClosureIn M (1 : G))
  rw [normalClosureIn_one189, Subgroup.card_bot, Nat.log_one_right] at h0
  rw [normalClosureIn_one189] at hrank
  omega

theorem step189Two : Step189Two := by
  intro G _ _ A M H c h hrank
  have hA := isE27_of_mem_partTwoE h.mem_partTwoE
  have hcA := mem_of_sec18H189 h
  have hc3 := pow_three_of_sec18H189 h
  have hcK := Sec20.self_mem_normalClosureIn M c
  have hWM : Subgroup.normalizer (A : Set G) ≤ M :=
    (normalizer_le_gamma le_rfl (by rw [hA.pRank_eq]; norm_num)).trans h.mem_scriptM.2
  intro w hw
  have hwc : w * c * w⁻¹ ∈ Subgroup.zpowers c := by
    by_cases hc1 : c = 1
    · rw [hc1, mul_one, mul_inv_cancel]
      exact Subgroup.one_mem _
    have hwA : w * c * w⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hw c).mp hcA
    have hwK : w * c * w⁻¹ ∈ normalClosureIn M c :=
      (Subgroup.mem_normalizer_iff.mp (Sec20.le_normalizer_normalClosureIn M c (hWM hw)) c).mp
        hcK
    have hcomm : (w * c * w⁻¹) * c = c * (w * c * w⁻¹) :=
      congrArg Subtype.val (hA.1.1.is_comm.comm ⟨_, hwA⟩ ⟨c, hcA⟩)
    have hwc3 : (w * c * w⁻¹) ^ 3 = 1 := hA.1.2 _ hwA
    exact mem_zpowers_of_commute189 hrank.le hwK hcK hwc3 hc3 hc1 hcomm
  apply Sec20.mem_normalizer_of_map_conj_le
  rw [Subgroup.map_le_iff_le_comap, Subgroup.zpowers_le, Subgroup.mem_comap]
  exact hwc

section NotNL

theorem hyp201One_of189 {A M H : Subgroup G} {c : G} (h : Sec18H G A M H c)
    (h7 : Hyp187 A M H c) :
    Sec20.Hyp201One G A M (inSubgroup perfectResidual H) (n189 H) c :=
  ⟨{ toPartTwoStanding := h.toPartTwoStanding
     partTwoS_eq := h.partTwoS_eq
     mem_partTwoE := h.mem_partTwoE
     mem_scriptM := h.mem_scriptM
     cases := Or.inl ⟨H, h7.1, h7.2.1, rfl, rfl, h7.2.2⟩
     centralizer_eq := h.centralizer_eq },
    ⟨H, h7.1, h7.2.1, rfl, rfl, h7.2.2⟩⟩

theorem conj_mem_zpowers_of_isSylowOf189 {K P : Subgroup G} {c : G}
    (hK : CFSG.Open.pRank 3 K ≤ 1) (hP : CFSG.ABGLocalTools.IsSylowOf 3 P K) (hcP : c ∈ P)
    (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1) {n : G} (hn : n ∈ Subgroup.normalizer (P : Set G)) :
    n * c * n⁻¹ ∈ Subgroup.zpowers c := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP3 : IsPGroup 3 P := hP.isPGroup
  have hPK : P ≤ K := hP.le
  have : Nontrivial P := ⟨⟨⟨c, hcP⟩, 1, fun h1 => hc1 (congrArg Subtype.val h1)⟩⟩
  have hZnt := hP3.center_nontrivial
  obtain ⟨a, ha⟩ := hP3.exists_card_eq
  have h3Z : 3 ∣ Nat.card (Subgroup.center P) := by
    obtain ⟨b, hb⟩ := (hP3.to_subgroup (Subgroup.center P)).exists_card_eq
    have hb0 : b ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hb
      exact (Finite.one_lt_card_iff_nontrivial.mpr hZnt).ne' hb
    rw [hb]
    exact dvd_pow_self 3 hb0
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center P) 3 h3Z
  set z' : G := ((z : P) : G) with hz'
  have hz'P : z' ∈ P := (z : P).2
  have hz'3 : z' ^ 3 = 1 := by
    rw [hz', ← Subgroup.coe_pow, ← Subgroup.coe_pow, ← hz, pow_orderOf_eq_one]
    rfl
  have hz'1 : z' ≠ 1 := by
    intro h1
    have hz1 : z = 1 := Subtype.ext (Subtype.ext h1)
    rw [hz1, orderOf_one] at hz
    exact absurd hz (by norm_num)
  have hcomm : ∀ y ∈ P, y * z' = z' * y := fun y hy =>
    congrArg Subtype.val ((Subgroup.mem_center_iff.mp z.2) ⟨y, hy⟩)
  have hmem : ∀ y ∈ P, y ^ 3 = 1 → y ∈ Subgroup.zpowers z' := fun y hy hy3 =>
    mem_zpowers_of_commute189 hK (hPK hy) (hPK hz'P) hy3 hz'3 hz'1 (hcomm y hy)
  have hzc : Subgroup.zpowers z' = Subgroup.zpowers c := by
    have hle : Subgroup.zpowers c ≤ Subgroup.zpowers z' :=
      Subgroup.zpowers_le.mpr (hmem c hcP hc3)
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime hc3 hc1,
      orderOf_eq_prime hz'3 hz'1]
  have hncP : n * c * n⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp hn c).mp hcP
  have hnc3 : (n * c * n⁻¹) ^ 3 = 1 := by
    rw [conj_pow, hc3, mul_one, mul_inv_cancel]
  rw [← hzc]
  exact hmem _ hncP hnc3

theorem exists_conj_of_mem189 {M : Subgroup G} {c : G} (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1)
    (hK : CFSG.Open.pRank 3 (normalClosureIn M c) ≤ 1) {m : G} (hm : m ∈ M) :
    ∃ k ∈ normalClosureIn M c, m * c * m⁻¹ ∈ Subgroup.zpowers (k * c * k⁻¹) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hP, hcP⟩ := Sec20.exists_isSylowOf_le (Sec20.isPGroup_zpowers_of_pow_three hc3)
    (Subgroup.zpowers_le.mpr (Sec20.self_mem_normalClosureIn M c))
  obtain ⟨k, hk, n, hn, rfl⟩ :=
    exists_mul_of_isSylowOf hP (Sec20.le_normalizer_normalClosureIn M c) hm
  refine ⟨k, hk, ?_⟩
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp
    (conj_mem_zpowers_of_isSylowOf189 hK hP (hcP (Subgroup.mem_zpowers c)) hc3 hc1 hn)
  refine Subgroup.mem_zpowers_iff.mpr ⟨j, ?_⟩
  rw [conj_zpow, hj]
  group

theorem normalizer_le_of_normal189 (hchar : CFSG.Assembly.IsCharTwoType G) {M K : Subgroup G}
    (hM : IsMaximalTwoLocal M) (hKM : K ≤ M) (hMK : M ≤ Subgroup.normalizer (K : Set G))
    {c : G} (hcK : c ∈ K) (hc1 : c ≠ 1) :
    Subgroup.normalizer (K : Set G) ≤ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := CFSG.Open.pCoreOf 2 M with hQ
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M
  have hMQ : M ≤ Subgroup.normalizer (Q : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M
  have hOK : CFSG.Open.pCoreOf 2 K ≠ ⊥ := by
    intro hbot
    have hKQ : K ⊓ Q ≤ CFSG.Open.pCoreOf 2 K :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
        (fun k hk => Sec20.mem_normalizer_inf_of_mem (Subgroup.le_normalizer hk) (hMQ (hKM hk)))
        (hQ2.to_le inf_le_right)
    rw [hbot] at hKQ
    have hcent : K ≤ M ⊓ Subgroup.centralizer (Q : Set G) := by
      refine fun k hk => ⟨hKM hk, Subgroup.mem_centralizer_iff.mpr fun q hq => ?_⟩
      have h1 : k * q * k⁻¹ * q⁻¹ ∈ K ⊓ Q := by
        constructor
        · have : q * k⁻¹ * q⁻¹ ∈ K :=
            (Subgroup.mem_normalizer_iff.mp (hMK ((CFSG.LieType.BorelTits.pCoreOf_le 2 M) hq))
              k⁻¹).mp (K.inv_mem hk)
          have e : k * q * k⁻¹ * q⁻¹ = k * (q * k⁻¹ * q⁻¹) := by group
          rw [e]
          exact K.mul_mem hk this
        · exact Q.mul_mem ((Subgroup.mem_normalizer_iff.mp (hMQ (hKM hk)) q).mp hq) (Q.inv_mem hq)
      have h2 := hKQ h1
      rw [Subgroup.mem_bot] at h2
      have : k * q = q * k := by
        calc k * q = (k * q * k⁻¹ * q⁻¹) * (q * k) := by group
          _ = q * k := by rw [h2, one_mul]
      exact this.symm
    obtain ⟨P, hP, hP2, hMP⟩ := hM.1
    have hKQ' : K ≤ Q := hcent.trans (hchar M ⟨P, hP, hP2, hMP⟩)
    have hc : c ∈ K ⊓ Q := ⟨hcK, hKQ' hcK⟩
    have := hKQ hc
    rw [Subgroup.mem_bot] at this
    exact hc1 this
  have hloc : IsPLocal 2 (Subgroup.normalizer (CFSG.Open.pCoreOf 2 K : Set G)) :=
    ⟨_, hOK, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K, rfl⟩
  have hMle : M ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 K : Set G) :=
    hMK.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K)
  have heq : Subgroup.normalizer (CFSG.Open.pCoreOf 2 K : Set G) = M := by
    by_contra hne
    exact hM.2 _ (lt_of_le_of_ne hMle (Ne.symm hne)) hloc
  rw [← heq]
  exact CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K

end NotNL

theorem step189Three_of (h1813 : Item181_3) (h184 : Item184_1) (h186 : Item186H)
    (hne : Step189FourNe) : Step189Three := by
  intro G _ _ A M H c h h7 i j hij
  have : IsSimpleGroup G := h.isSimpleGroup
  have hF := generalizedFitting_eq_of_mem_scriptHStar h.toSec18Std h7.1 h7.2.1
  have hL4 := (h184 G A M h.toSec18Std H h.mem_scriptH).1
  have h3 := (h1813 G A M h.toSec18Std H h.mem_scriptH hF).2 hL4
  have hN := (h186 G A M H c h h7).2.2.1
  have key : ∀ k : Fin 4, H ≤ Subgroup.normalizer (fourChar (s189 M H) k : Set G) →
      Subgroup.normalizer (fourChar (s189 M H) k : Set G) ≤ n189 H := by
    intro k hk
    have htop : Subgroup.normalizer (fourChar (s189 M H) k : Set G) ≠ ⊤ := by
      intro htop
      have hn : (fourChar (s189 M H) k).Normal := Subgroup.normalizer_eq_top_iff.mp htop
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (fourChar (s189 M H) k) with hbot | htop'
      · exact hne G A M H c h h7 k hbot
      · apply ne_top_of_mem_scriptH h.mem_scriptH
        rw [eq_top_iff, ← htop']
        exact (Sec20.fourChar_le _ k).trans
          ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_left)
    obtain ⟨X, hX, hle⟩ :=
      (IsCoatomic.eq_top_or_exists_le_coatom
        (Subgroup.normalizer (fourChar (s189 M H) k : Set G))).resolve_left htop
    have hXN : X ∈ scriptN (H : Set G) := ⟨hX, fun x hx => hle (hk hx)⟩
    rw [hN, Set.mem_singleton_iff] at hXN
    rw [hXN] at hle
    exact hle
  rcases h3 i j hij with hi | hj
  · exact Or.inl (key i hi)
  · exact Or.inr (key j hj)


theorem step189SNe_of (h186 : Item186H) (h187 : Item187) : Step189SNe := by
  intro G _ _ A M H c h h7 hnot hS
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSθ := s189_le_theta189_of_sAlpha_eq_bot hS
  have hsyl := isSylowOf_s189 h186 h h7
  rw [sup_eq_right.mpr hSθ] at hsyl
  apply hnot
  intro k hk
  have hkN : k ∈ Subgroup.normalizer (theta189 M H c : Set G) :=
    sk189_le_normalizer_theta189 M H c ((le_sup_right : normalClosureIn M c ≤ sk189 M H c) hk)
  obtain ⟨n, hn, m, hm, rfl⟩ :=
    exists_mul_of_isSylowOf hsyl (Subgroup.zpowers_le.mpr hkN) (Subgroup.mem_zpowers k)
  exact (n189 H).mul_mem (theta189_le_n189 h187 h h7 hn) (normalizer_s189_le h186 h h7 hm)

section FourNe

theorem omegaOneCenter_ne_bot189 {S : Type*} [Group S] [Finite S] {J : Subgroup S}
    (hJ : IsPGroup 2 J) (hJ1 : J ≠ ⊥) : CFSG.omegaOneCenter J ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial J := (Subgroup.nontrivial_iff_ne_bot J).mpr hJ1
  have hZ := hJ.center_nontrivial
  intro hbot
  have hdvd : 2 ∣ Nat.card (Subgroup.center J) := by
    obtain ⟨k, hk⟩ := (hJ.to_subgroup (Subgroup.center J)).exists_card_eq
    have h1 : 1 < Nat.card (Subgroup.center J) := Finite.one_lt_card_iff_nontrivial.mpr hZ
    rw [hk] at h1 ⊢
    exact dvd_pow_self 2 (by rintro rfl; simp at h1)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  have hmem : ((z : J) : S) ∈ CFSG.omegaOneCenter J := by
    rw [Sec20.mem_omegaOneCenter_iff']
    refine ⟨(z : J).2, fun y hy =>
      congrArg Subtype.val (Subgroup.mem_center_iff.mp z.2 ⟨y, hy⟩), ?_⟩
    rw [← Subgroup.coe_pow, ← Subgroup.coe_pow, ← hz, pow_orderOf_eq_one]
    rfl
  rw [hbot, Subgroup.mem_bot] at hmem
  have hz1 : z = 1 := Subtype.ext (Subtype.ext hmem)
  rw [hz1, orderOf_one] at hz
  exact absurd hz (by norm_num)

theorem isElementaryAbelian_of_le189 {S : Type*} [Group S] {E F : Subgroup S}
    [IsElementaryAbelian 2 E] (h : F ≤ E) : IsElementaryAbelian 2 F :=
  CFSG.IsElementaryAbelian.of_le inferInstance h

theorem higherElemThompson_ne_bot189 {S : Type*} [Group S] [Finite S] {j : ℕ}
    (hj : j < CFSG.pRank 2 S) : CFSG.higherElemThompson S j ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbdd : BddAbove {r : ℕ | ∃ A : Subgroup S, IsElementaryAbelian 2 A ∧
      Nat.card A = 2 ^ r} := by
    refine ⟨Nat.card S, fun r hr => ?_⟩
    obtain ⟨A, -, hA⟩ := hr
    calc r ≤ 2 ^ r := (Nat.lt_two_pow_self).le
      _ = Nat.card A := hA.symm
      _ ≤ Nat.card S := Subgroup.card_le_card_group A
  have hne : {r : ℕ | ∃ A : Subgroup S, IsElementaryAbelian 2 A ∧
      Nat.card A = 2 ^ r}.Nonempty := by
    refine ⟨0, ⊥, ?_, by rw [Subgroup.card_bot, pow_zero]⟩
    exact
      { toIsMulCommutative := ⟨⟨fun _ _ => Subsingleton.elim _ _⟩⟩
        exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one
          fun _ => Subsingleton.elim _ _ }
  obtain ⟨E, hE, hcard⟩ := Nat.sSup_mem hne hbdd
  change Nat.card E = 2 ^ CFSG.pRank 2 S at hcard
  have := hE
  obtain ⟨F, hF⟩ := Sylow.exists_subgroup_card_pow_prime 2
    (show 2 ^ (CFSG.pRank 2 S - j) ∣ Nat.card E by
      rw [hcard]; exact pow_dvd_pow 2 (Nat.sub_le _ _))
  have hF'E : F.map E.subtype ≤ E := Subgroup.map_subtype_le F
  have hF'el : IsElementaryAbelian 2 (F.map E.subtype) := isElementaryAbelian_of_le189 hF'E
  have hF'card : Nat.card (F.map E.subtype) = 2 ^ (CFSG.pRank 2 S - j) := by
    rw [Subgroup.card_map_of_injective E.subtype_injective, hF]
  have hF'mem : F.map E.subtype ∈ CFSG.higherElemThompsonFamily S j :=
    (CFSG.mem_higherElemThompsonFamily_iff j _).mpr ⟨hF'el, hF'card⟩
  intro hbot
  have hle : F.map E.subtype ≤ CFSG.higherElemThompson S j := le_sSup hF'mem
  rw [hbot, le_bot_iff] at hle
  rw [hle, Subgroup.card_bot] at hF'card
  have h1 : 1 ≤ CFSG.pRank 2 S - j := by omega
  have h2 : 2 ≤ 2 ^ (CFSG.pRank 2 S - j) :=
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (CFSG.pRank 2 S - j) := Nat.pow_le_pow_right (by norm_num) h1
  omega

theorem step189FourNe_of (hrk : Step189TwoRank) : Step189FourNe := by
  intro G _ _ A M H c h h7 i
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hr := hrk G A M H c h h7
  have hS2 : IsPGroup 2 (s189 M H) := isPGroup_s189 M H
  have hJ : ∀ j, j < 3 → CFSG.higherElemThompson (s189 M H) j ≠ ⊥ := fun j hj =>
    higherElemThompson_ne_bot189 (by omega)
  have hS1 : s189 M H ≠ ⊥ := by
    obtain ⟨x, hx⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp (hJ 0 (by norm_num))
    rw [Subgroup.ne_bot_iff_exists_ne_one]
    exact ⟨(x : s189 M H), fun h1 => hx (Subtype.ext h1)⟩
  fin_cases i
  · exact Sec20.omegaZOf_ne_bot hS2 hS1
  · change (CFSG.higherElemThompson (s189 M H) 0).map (s189 M H).subtype ≠ ⊥
    rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ (s189 M H).subtype_injective]
    exact hJ 0 (by norm_num)
  · change (CFSG.higherElemThompsonOmega (s189 M H) 1).map (s189 M H).subtype ≠ ⊥
    rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ (s189 M H).subtype_injective]
    exact omegaOneCenter_ne_bot189 (hS2.to_subgroup _) (hJ 1 (by norm_num))
  · change (CFSG.higherElemThompsonOmega (s189 M H) 2).map (s189 M H).subtype ≠ ⊥
    rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ (s189 M H).subtype_injective]
    exact omegaOneCenter_ne_bot189 (hS2.to_subgroup _) (hJ 2 (by norm_num))

end FourNe

section Certs


theorem step189NotNL_of (h1812 : Item181_2) (h184 : Item184_1) : Step189NotNL := by
  intro G _ _ A M H c h h7 hKθ hrank hKN
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hyp := hyp201One_of189 h h7
  set L := inSubgroup perfectResidual H with hLdef
  set K := normalClosureIn M c with hKdef
  set N := n189 H with hNdef
  set O := CFSG.Open.pCoreOf 2 L with hOdef
  have hsyl := Sec20.isSylowOf_three_inf_of_hyp201One h1812 h184 hyp
  have h9 := Sec20.card_inf_of_hyp201One h1812 h184 hyp
  have hNB := Sec20.normalizer_inf_le_of_hyp201One hyp h9
  have hsup := Sec20.sup_inf_eq_of_hyp201One hyp hsyl hNB
  have hLM := Sec20.not_le_of_hyp201One hyp
  have hOM := Sec20.pCoreOf_le_of_hyp201One hyp
  have hMK : M ≤ Subgroup.normalizer (K : Set G) := Sec20.le_normalizer_normalClosureIn M c
  have hKM : K ≤ M := normalClosureIn_le_of_sec18H189 h
  have hcK : c ∈ K := Sec20.self_mem_normalClosureIn M c
  have hc3 := pow_three_of_sec18H189 h
  have hc1 : c ≠ 1 := ne_one_of_pRank_eq_one189 hrank
  have hLN : L ≤ N := Subgroup.le_normalizer
  have hNO : N ≤ Subgroup.normalizer (O : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L
  have hcX : ∀ l ∈ L, c * l * c⁻¹ * l⁻¹ ∈ O := by
    have hc : c ∈ (Subgroup.zpowers c : Set G) := Subgroup.mem_zpowers c
    rw [← h.centralizer_eq] at hc
    exact hc.2
  have hkcX : ∀ k ∈ K, ∀ l ∈ L, (k * c * k⁻¹) * l * (k * c * k⁻¹)⁻¹ * l⁻¹ ∈ O := by
    intro k hk l hl
    have hkN : k ∈ N := hKN hk
    have hl' : k⁻¹ * l * k ∈ L := by
      have := (Subgroup.mem_normalizer_iff.mp (N.inv_mem hkN) l).mp hl
      simpa using this
    have h2 : k * (c * (k⁻¹ * l * k) * c⁻¹ * (k⁻¹ * l * k)⁻¹) * k⁻¹ ∈ O :=
      (Subgroup.mem_normalizer_iff.mp (hNO hkN) _).mp (hcX _ hl')
    have e : (k * c * k⁻¹) * l * (k * c * k⁻¹)⁻¹ * l⁻¹ =
        k * (c * (k⁻¹ * l * k) * c⁻¹ * (k⁻¹ * l * k)⁻¹) * k⁻¹ := by group
    rw [e]
    exact h2
  let X := Sec11.sectionCentralizerSubgroup N L O (le_refl N) hNO
  have hKX : K ≤ X := by
    rw [hKdef, normalClosureIn, Subgroup.closure_le]
    rintro _ ⟨m, hm, rfl⟩
    obtain ⟨k, hk, hmk⟩ := exists_conj_of_mem189 hc3 hc1 hrank.le hm
    have hkcX' : k * c * k⁻¹ ∈ X := Sec11.mem_sectionCentralizerSubgroup.mpr
      ⟨hKN (K.mul_mem (K.mul_mem hk hcK) (K.inv_mem hk)), hkcX k hk⟩
    exact (Subgroup.zpowers_le.mpr hkcX') hmk
  have hKX' : ∀ k ∈ K, ∀ l ∈ L, k * l * k⁻¹ * l⁻¹ ∈ O := fun k hk =>
    (Sec11.mem_sectionCentralizerSubgroup.mp (hKX hk)).2
  have hKY : K ≤ K ⊔ O := le_sup_left
  have hYK : K ⊔ O ≤ Subgroup.normalizer (K : Set G) := (sup_le hKM hOM).trans hMK
  have hKn : (K.subgroupOf (K ⊔ O)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKY).mpr hYK
  have hOs : Group.IsSolvable O := by
    have := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L).isNilpotent
    infer_instance
  have hres : inSubgroup perfectResidual (K ⊔ O) ≤ K :=
    inSubgroup_perfectResidual_le_of_isSolvable hKY
      (isSolvable_quotient_of_sup_eq hKY le_sup_right hYK rfl hOs)
  have hKp : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.mp (isPerfect_of_mem_thetaComponentsIn189 hKθ)
  have hLK : L ≤ Subgroup.normalizer (K : Set G) := by
    intro l hl
    apply Sec20.mem_normalizer_of_map_conj_le
    have hle : K.map (MulAut.conj l).toMonoidHom ≤ K ⊔ O := by
      rintro _ ⟨k, hk, rfl⟩
      change l * k * l⁻¹ ∈ K ⊔ O
      have h1 : k * l⁻¹ * k⁻¹ * l⁻¹⁻¹ ∈ O := hKX' k hk l⁻¹ (L.inv_mem hl)
      have h2 : l * (k * l⁻¹ * k⁻¹ * l⁻¹⁻¹) * l⁻¹ ∈ O :=
        (Subgroup.mem_normalizer_iff.mp (hNO (hLN hl)) _).mp h1
      have e : l * k * l⁻¹ = (l * (k * l⁻¹ * k⁻¹ * l⁻¹⁻¹) * l⁻¹) * k := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right h2) (Subgroup.mem_sup_left hk)
    have hp : ⁅K.map (MulAut.conj l).toMonoidHom, K.map (MulAut.conj l).toMonoidHom⁆ =
        K.map (MulAut.conj l).toMonoidHom := by
      rw [← Subgroup.map_commutator, hKp]
    exact (le_inSubgroup_perfectResidual hp hle).trans hres
  have hNK : N ≤ Subgroup.normalizer (K : Set G) := by
    rw [← hsup]
    exact sup_le hLK (inf_le_right.trans hMK)
  have hNM : Subgroup.normalizer (K : Set G) ≤ M :=
    normalizer_le_of_normal189 h.charTwoType h.mem_scriptM.1 hKM hMK hcK hc1
  exact hLM (hLN.trans (hNK.trans hNM))


theorem item189_of (h1812 : Item181_2) (h1813 : Item181_3) (h184 : Item184_1) (h186 : Item186H)
    (h187 : Item187) (hK0 : Step189K0) (hType : Step189KType) (hO2 : Sec20.Step189O2)
    (hO2B : Step189O2Bound) (hList : Step189List) (hFour : Step189FourNe)
    (hOdd : Step189OddL2) (hInsp : Step189InspectI) (hIdx : Step189IndexI)
    (h1411 : Asc82Item1411And1412) (hL16 : Step189L16) (hL4 : Step189L4) (hO3 : Step189O3) :
    Item189 :=
  item189_of_steps h186 h187 hK0 step189Two hType hO2 hO2B hList (step189NotNL_of h1812 h184)
    (step189Three_of h1813 h184 h186 hFour) (step189SNe_of h186 h187) hOdd hInsp hIdx h1411
    hL16 hL4 hO3

end Certs

end CFSG.RankThree.PartTwo.Sec18
