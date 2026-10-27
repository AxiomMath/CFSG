module

public import CFSG.Monster.B.GSide.TwoCOddCore
public import CFSG.Monster.B.Recog.GenericStrongClosure
public import CFSG.Monster.B.GSide.TwoBNative
public import CFSG.Monster.B.Recog.GenericGoldschmidtApp
public import CFSG.Monster.B.Recog.GenericGoldschmidtArith
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate120
public import Certificates.Certificate1020
public import Certificates.Certificate1022
public import Certificates.Certificate3011
public import Certificates.Certificate3012
public import Certificates.Certificate3014
public import Certificates.Certificate3015
public import Certificates.Certificate3016
public import Certificates.Certificate3017
public import Certificates.Certificate3018
public import Certificates.Certificate3019
public import Certificates.Certificate3020
public import Certificates.Certificate3021
public import Certificates.Certificate3022
public import Certificates.Certificate3023
public import Certificates.Certificate3025
public import Certificates.Certificate3026
public import Certificates.Certificate3028
public import Certificates.Certificate3041
public import Certificates.Certificate3042
public import Certificates.Certificate3045
public import Certificates.Certificate3048
public import Certificates.Certificate3049
public import Certificates.Certificate3050
public import Certificates.Certificate3051
public import Certificates.Certificate3054
public import Certificates.Certificate3055
public import Certificates.Certificate3056
public import Certificates.Certificate3057
public import Certificates.Certificate3058
public import Certificates.Certificate3059
public import Certificates.Certificate3060
public import Certificates.Certificate3061
public import Certificates.Certificate3062
public import Certificates.Certificate3063
public import Certificates.Certificate3072
public import Certificates.Certificate3073
public import Certificates.Certificate3074
public import Certificates.Certificate3075
public import Certificates.Certificate3076
public import Certificates.Certificate3077
public import Certificates.Certificate3078
public import Certificates.Certificate3079
public import Certificates.Certificate3080
public import Certificates.Certificate3098
public import Certificates.Certificate3099
public import Certificates.Certificate3100
public import Certificates.Certificate3101
public import Certificates.Certificate3102
public import Certificates.Certificate3103
public import Certificates.Certificate3106
public import Certificates.Certificate3107
public import Certificates.Certificate3108
public import Certificates.Certificate3109
public import Certificates.Certificate3110
public import Certificates.Certificate3111
public import Certificates.Certificate3114
public import Certificates.Certificate3115
public import Certificates.Certificate3116
public import Certificates.Certificate3117
public import Certificates.Certificate3118
public import Certificates.Certificate3121
public import Certificates.Certificate3124
public import Certificates.Certificate3125
public import Certificates.Certificate3126
public import Certificates.Certificate3127
public import Certificates.Certificate3175
public import Certificates.Certificate3176
public import Certificates.Certificate6007
public import Certificates.Certificate6023
public import Certificates.Certificate6024
public import Certificates.Certificate16001
public import Certificates.Certificate16015
public import Certificates.Certificate16016
public import Certificates.Certificate16021
public import Certificates.Certificate16022
public import Certificates.Certificate16028
public import Certificates.Certificate16029
public import Certificates.Certificate16033
public import Certificates.Certificate16035
public import Certificates.Certificate16036
public import Certificates.Certificate16040
public import Certificates.Certificate3027
public import Certificates.Certificate3081
public import Certificates.Certificate3082
public import Certificates.Certificate3083
public import Certificates.Certificate16951
public import Certificates.Certificate1953
public import Certificates.Certificate1954
public import Certificates.Certificate16042
public import Certificates.Certificate3029
public import Certificates.Certificate3030
public import Certificates.Certificate3031
public import Certificates.Certificate16003
public import Certificates.Certificate16010
public import Certificates.Certificate16023
public import Certificates.Certificate3033
public import Certificates.Certificate3034
public import Certificates.Certificate3035
public import Certificates.Certificate3036
public import Certificates.Certificate3065
public import Certificates.Certificate3066
public import Certificates.Certificate3067
public import Certificates.Certificate3032
public import Certificates.Certificate3068
public import Certificates.Certificate3069
public import CFSG.GroupTheory.ABGLocalTools.Basic

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.GSide

open CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Amalgam CFSG.Monster.B.CTIB

@[expose] def GoldschmidtTheorem : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (S : Sylow 2 X) (A : Subgroup X), A ≤ S →
    IsMulCommutative A →
    (∀ a ∈ A, ∀ g : X, g⁻¹ * a * g ∈ (S : Subgroup X) → g⁻¹ * a * g ∈ A) →
    let M : Subgroup X := Subgroup.normalClosure (A : Set X)
    let π := QuotientGroup.mk' (CFSG.Open.goldschmidtOddCore M)
    let T := ((S : Subgroup X).subgroupOf M).map π ⊓
      CFSG.Open.goldschmidtLayer (M ⧸ CFSG.Open.goldschmidtOddCore M)
    CFSG.Open.pCore 2 (M ⧸ CFSG.Open.goldschmidtOddCore M) ⊔
        CFSG.Open.goldschmidtLayer (M ⧸ CFSG.Open.goldschmidtOddCore M) = ⊤ ∧
    (A.subgroupOf M).map π =
      CFSG.Open.pCore 2 (M ⧸ CFSG.Open.goldschmidtOddCore M) ⊔
        Subgroup.closure {t | t ∈ T ∧ t ^ 2 = 1} ∧
    ∀ K : Subgroup (M ⧸ CFSG.Open.goldschmidtOddCore M), CFSG.Open.IsComponentOf K ⊤ →
      CFSG.Open.goldschmidtSimpleType (K ⧸ Subgroup.center K)

namespace TwoB

section Central

variable {Y : Type*} [Group Y] {z : Y}

theorem mem_zpowers_iff_of_mul_self (hz2 : z * z = 1) {x : Y} :
    x ∈ Subgroup.zpowers z ↔ x = 1 ∨ x = z := by
  rw [Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, rfl⟩
    obtain ⟨j, hj | hj⟩ := Int.even_or_odd' k
    · left
      rw [hj, zpow_mul, zpow_two, hz2, one_zpow]
    · right
      rw [hj, zpow_add, zpow_mul, zpow_two, hz2, one_zpow, one_mul, zpow_one]
  · rintro (rfl | rfl)
    · exact ⟨0, zpow_zero _⟩
    · exact ⟨1, zpow_one _⟩

theorem zpowers_normal_of_central (hz : ∀ g : Y, g * z = z * g) :
    (Subgroup.zpowers z).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
  rw [(Commute.zpow_right (hz g) k).eq, mul_inv_cancel_right]
  exact Subgroup.zpow_mem_zpowers _ k

theorem normalizer_eq_of_le {Y₀ Q : Subgroup Y} (hQn : ∀ g ∈ Y₀, ∀ q ∈ Q, g * q * g⁻¹ ∈ Q)
    (hNQ : Subgroup.normalizer (Q : Set Y) ≤ Y₀) : Subgroup.normalizer (Q : Set Y) = Y₀ := by
  refine le_antisymm hNQ fun g hg => ?_
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨hQn g hg h, fun hh => ?_⟩
  have h' := hQn g⁻¹ (Y₀.inv_mem hg) _ hh
  rwa [show g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h by group] at h'

theorem isPGroup_of_sq (hz2 : z * z = 1) {Q : Subgroup Y}
    (hQsq : ∀ q ∈ Q, q * q = 1 ∨ q * q = z) : IsPGroup 2 Q := by
  intro q
  refine ⟨2, Subtype.ext ?_⟩
  have h4 : (q : Y) ^ 2 ^ 2 = 1 := by
    rw [show 2 ^ 2 = 2 * 2 from rfl, pow_mul, sq (q : Y)]
    rcases hQsq q q.2 with h | h
    · rw [h, one_pow]
    · rw [h, sq, hz2]
  simpa using h4

theorem le_sylow_of_le_normalizer {Q : Subgroup Y} (hQ : IsPGroup 2 Q) (T : Sylow 2 Y)
    (hTQ : (T : Subgroup Y) ≤ Subgroup.normalizer (Q : Set Y)) : Q ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsup := IsPGroup.to_sup_of_normal_right' T.isPGroup' hQ hTQ
  calc Q ≤ (T : Subgroup Y) ⊔ Q := le_sup_right
    _ = T := T.is_maximal' hsup le_sup_left

theorem isPGroup_zpowers (hz2 : z * z = 1) : IsPGroup 2 (Subgroup.zpowers z) := by
  intro x
  refine ⟨1, Subtype.ext ?_⟩
  rcases (mem_zpowers_iff_of_mul_self hz2).1 x.2 with h | h
  · simp [h]
  · simp [h, sq, hz2]

theorem oddCore_eq_bot_of_four [Finite Y] (hz2 : z * z = 1) {Y₀ Q : Subgroup Y}
    (hQn : ∀ g ∈ Y₀, ∀ q ∈ Q, g * q * g⁻¹ ∈ Q)
    (hQB1 : ∀ R : Subgroup Y, R ≤ Q → (∀ g ∈ Y₀, ∀ r ∈ R, g * r * g⁻¹ ∈ R) →
      R = ⊥ ∨ R = Subgroup.zpowers z ∨ R = Q)
    {a b : Y} (ha : a ∈ Q) (hb : b ∈ Q) (ha2 : a * a = 1) (hb2 : b * b = 1) (ha1 : a ≠ 1)
    (hb1 : b ≠ 1) (hab : Commute a b) (hab1 : a * b ≠ 1) (habz : a * b ≠ z)
    (hOa : CFSG.oddCore (Subgroup.centralizer {a}) = ⊥)
    (hOb : CFSG.oddCore (Subgroup.centralizer {b}) = ⊥) : CFSG.oddCore Y = ⊥ := by
  rw [oddCore_eq_bot_iff]
  intro K hK hKodd
  have hCK : ∀ x : Y, CFSG.oddCore (Subgroup.centralizer {x}) = ⊥ →
      K ⊓ Subgroup.centralizer {x} = ⊥ := by
    intro x hOx
    have hle : K ⊓ Subgroup.centralizer {x} ≤ Subgroup.centralizer {x} := inf_le_right
    have hn : ((K ⊓ Subgroup.centralizer {x}).subgroupOf (Subgroup.centralizer {x})).Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact Subgroup.mem_inf.2 ⟨hK.conj_mem _ (Subgroup.mem_inf.1 hn).1 g,
        (Subgroup.centralizer {x}).mul_mem ((Subgroup.centralizer {x}).mul_mem g.2
          (Subgroup.mem_inf.1 hn).2) ((Subgroup.centralizer {x}).inv_mem g.2)⟩
    have hodd : Odd (Nat.card ((K ⊓ Subgroup.centralizer {x}).subgroupOf
        (Subgroup.centralizer {x}))) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
      exact hKodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
    have h1 := (oddCore_eq_bot_iff.1 hOx) _ hn hodd
    have h2 := Subgroup.subgroupOf_map_subtype (K ⊓ Subgroup.centralizer {x})
      (Subgroup.centralizer {x})
    rw [h1, Subgroup.map_bot, inf_eq_left.2 hle] at h2
    exact h2.symm
  have hKa := hCK a hOa
  have hKb := hCK b hOb
  set T := CFSG.GorensteinWalter.kleinFourOfCommutingInvolutions a b ha2 hb2 hab
  have hne : a ≠ b := fun h => hab1 (by rw [h, hb2])
  have : IsKleinFour T :=
    CFSG.GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions a b ha2 hb2 ha1 hb1 hne hab
  have hmem : ∀ x : Y, x ∈ T ↔ x = a * b ∨ x = a ∨ x = b ∨ x = 1 := fun x => by
    change x ∈ ({a * b, a, b, 1} : Set Y) ↔ _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  have haT : a ∈ T := (hmem a).2 (Or.inr (Or.inl rfl))
  have hbT : b ∈ T := (hmem b).2 (Or.inr (Or.inr (Or.inl rfl)))
  have habT : a * b ∈ T := (hmem _).2 (Or.inl rfl)
  have hTK : T ≤ Subgroup.normalizer (K : Set Y) := by
    rw [Subgroup.normalizer_eq_top_iff.2 hK]
    exact le_top
  have ha_ab : a ≠ a * b := fun h => hb1 (by
    have h' := congrArg (a⁻¹ * ·) h
    simpa using h'.symm)
  have hb_ab : b ≠ a * b := fun h => ha1 (by
    have h' := congrArg (· * b⁻¹) h
    simpa using h'.symm)
  have hdec := CFSG.ABGLocalTools.four_group_odd_eq_mul_centralizers hKodd hTK haT hbT habT ha1 hb1
    hab1 hne ha_ab hb_ab
  have hKab : ∀ k ∈ K, k * (a * b) = a * b * k := by
    intro k hk
    have hk' : k ∈ (K : Set Y) := hk
    rw [hdec, hKa, hKb] at hk'
    obtain ⟨_, ⟨x, hx, y, hy, rfl⟩, w, hw, rfl⟩ := hk'
    have hx1 : x = 1 := Subgroup.mem_bot.1 hx
    have hy1 : y = 1 := Subgroup.mem_bot.1 hy
    simp only [hx1, hy1, one_mul]
    exact Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hw).2
  set R : Subgroup Y := Q ⊓ Subgroup.centralizer (K : Set Y) with hRdef
  have hRn : ∀ g ∈ Y₀, ∀ r ∈ R, g * r * g⁻¹ ∈ R := by
    intro g hg r hr
    refine Subgroup.mem_inf.2 ⟨hQn g hg r (Subgroup.mem_inf.1 hr).1, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hk' : g⁻¹ * k * g ∈ K := by simpa using hK.conj_mem k hk g⁻¹
    have hc := (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hr).2) _ hk'
    calc k * (g * r * g⁻¹) = g * (g⁻¹ * k * g * r) * g⁻¹ := by group
      _ = g * (r * (g⁻¹ * k * g)) * g⁻¹ := by rw [hc]
      _ = g * r * g⁻¹ * k := by group
  have habR : a * b ∈ R :=
    Subgroup.mem_inf.2 ⟨Q.mul_mem ha hb, Subgroup.mem_centralizer_iff.2 fun k hk => hKab k hk⟩
  rcases hQB1 R inf_le_left hRn with h | h | h
  · rw [h, Subgroup.mem_bot] at habR
    exact absurd habR hab1
  · rw [h, mem_zpowers_iff_of_mul_self hz2] at habR
    rcases habR with h' | h'
    · exact absurd h' hab1
    · exact absurd h' habz
  · have haR : a ∈ R := h ▸ ha
    have hKle : K ≤ Subgroup.centralizer {a} := fun k hk => by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 haR).2) k hk
    rw [← inf_eq_left.2 hKle]
    exact hKa

end Central

section Hom

variable {Y X : Type*} [Group Y] [Group X] {z : Y} {π : Y →* X}

theorem map_eq_map_iff (hker : π.ker = Subgroup.zpowers z) (hz2 : z * z = 1) {a b : Y} :
    π a = π b ↔ b = a ∨ b = a * z := by
  have h : π a = π b ↔ a⁻¹ * b ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one]
  rw [h, hker, mem_zpowers_iff_of_mul_self hz2]
  constructor
  · rintro (h | h)
    · left
      rw [← mul_inv_cancel_left a b, h, mul_one]
    · right
      rw [← mul_inv_cancel_left a b, h]
  · rintro (h | h)
    · left
      rw [h, inv_mul_cancel]
    · right
      rw [h, ← mul_assoc, inv_mul_cancel, one_mul]

theorem map_eq_one_iff (hker : π.ker = Subgroup.zpowers z) (hz2 : z * z = 1) {a : Y} :
    π a = 1 ↔ a = 1 ∨ a = z := by
  rw [← MonoidHom.mem_ker, hker, mem_zpowers_iff_of_mul_self hz2]

theorem map_mem_map_iff (hker : π.ker = Subgroup.zpowers z) {Q : Subgroup Y} (hzQ : z ∈ Q)
    (y : Y) : π y ∈ Q.map π ↔ y ∈ Q := by
  rw [← Subgroup.mem_comap, Subgroup.comap_map_eq, hker,
    sup_eq_left.2 ((Subgroup.zpowers_le).2 hzQ)]

theorem map_mem_normalizer_iff (hπ : Function.Surjective π) (hker : π.ker = Subgroup.zpowers z)
    {Q : Subgroup Y} (hzQ : z ∈ Q) (g : Y) :
    π g ∈ Subgroup.normalizer ((Q.map π : Subgroup X) : Set X) ↔
      g ∈ Subgroup.normalizer (Q : Set Y) := by
  simp only [Subgroup.mem_normalizer_iff]
  constructor
  · intro h y
    have h' := h (π y)
    rwa [map_mem_map_iff hker hzQ, ← map_inv, ← map_mul, ← map_mul,
      map_mem_map_iff hker hzQ] at h'
  · intro h x
    obtain ⟨y, rfl⟩ := hπ x
    rw [map_mem_map_iff hker hzQ, ← map_inv, ← map_mul, ← map_mul, map_mem_map_iff hker hzQ]
    exact h y

theorem normalizer_map_eq (hπ : Function.Surjective π) (hker : π.ker = Subgroup.zpowers z)
    {Y₀ Q : Subgroup Y} (hzQ : z ∈ Q) (hN : Subgroup.normalizer (Q : Set Y) = Y₀) :
    Subgroup.normalizer ((Q.map π : Subgroup X) : Set X) = Y₀.map π := by
  have hzY : z ∈ Y₀ := hN ▸ Subgroup.le_normalizer hzQ
  ext x
  obtain ⟨y, rfl⟩ := hπ x
  rw [map_mem_normalizer_iff hπ hker hzQ, hN, map_mem_map_iff hker hzY]

theorem card_map_mul_two [Finite Y] (hker : π.ker = Subgroup.zpowers z) (hz2 : z * z = 1)
    (hz1 : z ≠ 1) {Y₀ : Subgroup Y} (hzY : z ∈ Y₀) : Nat.card (Y₀.map π) * 2 = Nat.card Y₀ := by
  have h1 := Subgroup.card_ker_mul_card_range (π.domRestrict Y₀)
  rw [MonoidHom.domRestrict_range, MonoidHom.ker_domRestrict, hker] at h1
  have hZ : Nat.card ((Subgroup.zpowers z).subgroupOf Y₀) = 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe ((Subgroup.zpowers_le).2 hzY)).toEquiv,
      Nat.card_zpowers, orderOf_eq_prime (by rw [sq]; exact hz2) hz1]
  rw [hZ] at h1
  linarith

theorem map_comm (hker : π.ker = Subgroup.zpowers z) {Q : Subgroup Y}
    (hQcomm : ∀ q ∈ Q, ∀ r ∈ Q, q * r = r * q ∨ q * r = r * q * z) :
    ∀ x ∈ Q.map π, ∀ y ∈ Q.map π, x * y = y * x := by
  rintro _ ⟨q, hq, rfl⟩ _ ⟨r, hr, rfl⟩
  have hz : π z = 1 := by
    rw [← MonoidHom.mem_ker, hker]
    exact Subgroup.mem_zpowers z
  rw [← map_mul, ← map_mul]
  rcases hQcomm q hq r hr with h | h
  · rw [h]
  · rw [h, map_mul, hz, mul_one]

theorem map_mul_self (hker : π.ker = Subgroup.zpowers z) {Q : Subgroup Y}
    (hQsq : ∀ q ∈ Q, q * q = 1 ∨ q * q = z) : ∀ x ∈ Q.map π, x * x = 1 := by
  rintro _ ⟨q, hq, rfl⟩
  rw [← map_mul, ← MonoidHom.mem_ker, hker]
  rcases hQsq q hq with h | h
  · rw [h]
    exact Subgroup.one_mem _
  · rw [h]
    exact Subgroup.mem_zpowers z

theorem strongly_closed_package [Finite Y] (hπ : Function.Surjective π)
    (hker : π.ker = Subgroup.zpowers z) (hz : ∀ g : Y, g * z = z * g) (hz2 : z * z = 1)
    {Y₀ Q : Subgroup Y} {D₀ : Set Y} (hzQ : z ∈ Q) (hQY : Q ≤ Y₀)
    (hNeq : Subgroup.normalizer (Q : Set Y) = Y₀)
    (hQsq : ∀ q ∈ Q, q * q = 1 ∨ q * q = z)
    (hQcomm : ∀ q ∈ Q, ∀ r ∈ Q, q * r = r * q ∨ q * r = r * q * z)
    (T : Sylow 2 Y) (hTY : (T : Subgroup Y) ≤ Y₀)
    (hD₀Q : D₀ ⊆ Q) (hD₀ : ∀ g : Y, ∀ a ∈ D₀, g * a * g⁻¹ ∈ Y₀ → g ∈ Y₀)
    (hFP : ∀ s ∈ Y₀, s ∉ Q → (s * s = 1 ∨ s * s = z) →
      ∃ a ∈ D₀, s * a * s⁻¹ = a ∨ s * a * s⁻¹ = a * z)
    {S : Subgroup X} (hS : S ≤ Subgroup.normalizer ((Q.map π : Subgroup X) : Set X)) :
    ∀ a ∈ Q.map π, ∀ g : X, g⁻¹ * a * g ∈ S → g⁻¹ * a * g ∈ Q.map π := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite X := Finite.of_surjective π hπ
  have hQn : ∀ g ∈ Y₀, ∀ q ∈ Q, g * q * g⁻¹ ∈ Q := fun g hg q hq =>
    (Subgroup.mem_normalizer_iff.1 (hNeq ▸ hg : g ∈ Subgroup.normalizer (Q : Set Y)) q).1 hq
  have hcen : ∀ g : Y, g⁻¹ * z * g = z := fun g => by
    rw [mul_assoc, ← hz g, inv_mul_cancel_left]
  have hD₀V : π '' D₀ ⊆ Q.map π := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨a, hD₀Q ha, rfl⟩
  have h1 : ∀ g k : X, ∀ a ∈ π '' D₀, ∀ b ∈ π '' D₀,
      g * a * g⁻¹ * (k * b * k⁻¹) = k * b * k⁻¹ * (g * a * g⁻¹) →
        g⁻¹ * k ∈ Subgroup.normalizer ((Q.map π : Subgroup X) : Set X) := by
    intro g k a ha b hb hgk
    obtain ⟨g', rfl⟩ := hπ g
    obtain ⟨k', rfl⟩ := hπ k
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    simp only [← map_inv, ← map_mul] at hgk
    rw [map_eq_map_iff hker hz2] at hgk
    have hy : g'⁻¹ * (k' * b' * k'⁻¹) * g' * a' * (g'⁻¹ * (k' * b' * k'⁻¹) * g')⁻¹ ∈ Y₀ := by
      have e : g'⁻¹ * (k' * b' * k'⁻¹) * g' * a' * (g'⁻¹ * (k' * b' * k'⁻¹) * g')⁻¹ =
          g'⁻¹ * ((k' * b' * k'⁻¹) * (g' * a' * g'⁻¹) * (k' * b' * k'⁻¹)⁻¹) * g' := by group
      rw [e]
      rcases hgk with h | h
      · rw [h, mul_inv_cancel_right, show g'⁻¹ * (g' * a' * g'⁻¹) * g' = a' by group]
        exact hQY (hD₀Q ha')
      · have hBz : k' * b' * k'⁻¹ * z * (k' * b' * k'⁻¹)⁻¹ = z := by
          rw [hz, mul_inv_cancel_right]
        have hBA : k' * b' * k'⁻¹ * (g' * a' * g'⁻¹) * (k' * b' * k'⁻¹)⁻¹ =
            g' * a' * g'⁻¹ * z := by
          rw [h, show g' * a' * g'⁻¹ * (k' * b' * k'⁻¹) * z * (k' * b' * k'⁻¹)⁻¹ =
            g' * a' * g'⁻¹ * (k' * b' * k'⁻¹ * z * (k' * b' * k'⁻¹)⁻¹) by group, hBz]
        rw [hBA, show g'⁻¹ * (g' * a' * g'⁻¹ * z) * g' = a' * (g'⁻¹ * z * g') by group, hcen]
        exact hQY (Q.mul_mem (hD₀Q ha') hzQ)
    have hyY := hD₀ _ a' ha' hy
    have hw : g'⁻¹ * k' * b' * (g'⁻¹ * k')⁻¹ ∈ Y₀ := by
      rw [show g'⁻¹ * k' * b' * (g'⁻¹ * k')⁻¹ = g'⁻¹ * (k' * b' * k'⁻¹) * g' by group]
      exact hyY
    rw [← map_inv, ← map_mul, map_mem_normalizer_iff hπ hker hzQ, hNeq]
    exact hD₀ _ b' hb' hw
  have h4 : ∀ a ∈ Recog.StrongClosure.dBar (π '' D₀), ∀ b ∈ Recog.StrongClosure.dBar (π '' D₀),
      IsPGroup 2 (Subgroup.closure ({a, b} : Set X)) → a * b = b * a := by
    intro a ha b hb hP
    obtain ⟨g, _, ⟨a', ha', rfl⟩, rfl⟩ := ha
    obtain ⟨k, _, ⟨b', hb', rfl⟩, rfl⟩ := hb
    obtain ⟨g', rfl⟩ := hπ g
    obtain ⟨k', rfl⟩ := hπ k
    have hPp := hP.comap_of_ker_isPGroup π (by rw [hker]; exact isPGroup_zpowers hz2)
    obtain ⟨P, hPP⟩ := hPp.exists_le_sylow
    obtain ⟨c, hc⟩ := MulAction.exists_smul_eq Y T P
    have hconj : ∀ x : Y, ∀ e ∈ D₀, π (x * e * x⁻¹) ∈
        Subgroup.closure ({π g' * π a' * (π g')⁻¹, π k' * π b' * (π k')⁻¹} : Set X) →
        c⁻¹ * (x * e * x⁻¹) * c ∈ Q := by
      intro x e he hxe
      have hmem : x * e * x⁻¹ ∈ (P : Subgroup Y) := hPP hxe
      rw [← hc, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
        ← map_inv, MulAut.smul_def, MulAut.conj_apply, inv_inv] at hmem
      have hT : c⁻¹ * (x * e * x⁻¹) * c ∈ (T : Subgroup Y) := hmem
      have hxY : c⁻¹ * x ∈ Y₀ := hD₀ _ e he (by
        rw [show c⁻¹ * x * e * (c⁻¹ * x)⁻¹ = c⁻¹ * (x * e * x⁻¹) * c by group]
        exact hTY hT)
      rw [show c⁻¹ * (x * e * x⁻¹) * c = c⁻¹ * x * e * (c⁻¹ * x)⁻¹ by group]
      exact hQn _ hxY e (hD₀Q he)
    have hA := hconj g' a' ha' (Subgroup.subset_closure (by
      rw [map_mul, map_mul, map_inv]
      exact Set.mem_insert _ _))
    have hB := hconj k' b' hb' (Subgroup.subset_closure (by
      rw [map_mul, map_mul, map_inv]
      exact Set.mem_insert_of_mem _ rfl))
    simp only [← map_inv, ← map_mul]
    rw [map_eq_map_iff hker hz2]
    have eAB : c⁻¹ * (g' * a' * g'⁻¹) * c * (c⁻¹ * (k' * b' * k'⁻¹) * c) =
        c⁻¹ * (g' * a' * g'⁻¹ * (k' * b' * k'⁻¹)) * c := by group
    have eBA : c⁻¹ * (k' * b' * k'⁻¹) * c * (c⁻¹ * (g' * a' * g'⁻¹) * c) =
        c⁻¹ * (k' * b' * k'⁻¹ * (g' * a' * g'⁻¹)) * c := by group
    rcases hQcomm _ hA _ hB with h | h
    · left
      rw [eAB, eBA] at h
      exact (mul_left_cancel (mul_right_cancel h)).symm
    · right
      have e3 : c⁻¹ * (k' * b' * k'⁻¹ * (g' * a' * g'⁻¹)) * c * z =
          c⁻¹ * (k' * b' * k'⁻¹ * (g' * a' * g'⁻¹) * z) * c := by
        rw [mul_assoc (c⁻¹ * (k' * b' * k'⁻¹ * (g' * a' * g'⁻¹))) c z, hz c]
        group
      rw [eAB, eBA, e3] at h
      rw [mul_left_cancel (mul_right_cancel h), mul_assoc _ z z, hz2, mul_one]
  have hFPX : ∀ w ∈ Subgroup.normalizer ((Q.map π : Subgroup X) : Set X), w * w = 1 →
      w ∉ Q.map π → ∃ a ∈ π '' D₀, a * w = w * a := by
    intro w hw hw2 hwV
    obtain ⟨s, rfl⟩ := hπ w
    rw [map_mem_normalizer_iff hπ hker hzQ, hNeq] at hw
    rw [map_mem_map_iff hker hzQ] at hwV
    have hs2 : s * s = 1 ∨ s * s = z := by
      rw [← map_mul, map_eq_one_iff hker hz2] at hw2
      exact hw2
    obtain ⟨a, ha, hsa⟩ := hFP s hw hwV hs2
    refine ⟨π a, ⟨a, ha, rfl⟩, ?_⟩
    rw [← map_mul, ← map_mul, map_eq_map_iff hker hz2]
    rcases hsa with h | h
    · left
      calc s * a = s * a * s⁻¹ * s := by group
        _ = a * s := by rw [h]
    · right
      calc s * a = s * a * s⁻¹ * s := by group
        _ = a * z * s := by rw [h]
        _ = a * s * z := by rw [mul_assoc, ← hz s, ← mul_assoc]
  exact Recog.strongly_closed_of_le_normalizer (map_comm hker hQcomm) (map_mul_self hker hQsq)
    hD₀V h1 h4 hFPX hS


theorem conj_of_map_mem_centralizer (hker : π.ker = Subgroup.zpowers z)
    (hz : ∀ g : Y, g * z = z * g) (hz2 : z * z = 1) {Q : Subgroup Y} {s : Y}
    (hs : π s ∈ Subgroup.centralizer ((Q.map π : Subgroup X) : Set X)) :
    ∀ q ∈ Q, s * q * s⁻¹ = q ∨ s * q * s⁻¹ = q * z := by
  intro q hq
  have h := (Subgroup.mem_centralizer_iff.1 hs) (π q) ⟨q, hq, rfl⟩
  rw [← map_mul, ← map_mul, map_eq_map_iff hker hz2] at h
  rcases h with h | h
  · left
    rw [h, mul_inv_cancel_right]
  · right
    rw [h, mul_assoc q s z, hz s, ← mul_assoc, mul_inv_cancel_right]

theorem centralizer_map_le (hπ : Function.Surjective π) (hker : π.ker = Subgroup.zpowers z)
    (hz : ∀ g : Y, g * z = z * g) (hz2 : z * z = 1) {Y₀ Q : Subgroup Y} (hzQ : z ∈ Q)
    (hNeq : Subgroup.normalizer (Q : Set Y) = Y₀)
    (hQB1c : ∀ g ∈ Y₀, (∀ q ∈ Q, g * q * g⁻¹ = q ∨ g * q * g⁻¹ = q * z) → g ∈ Q) :
    Subgroup.centralizer ((Q.map π : Subgroup X) : Set X) ≤ Q.map π := by
  intro w hw
  obtain ⟨s, rfl⟩ := hπ w
  have h1 := conj_of_map_mem_centralizer hker hz hz2 hw
  have h2 := conj_of_map_mem_centralizer hker hz hz2
    (show π s⁻¹ ∈ Subgroup.centralizer ((Q.map π : Subgroup X) : Set X) by
      rw [map_inv]
      exact Subgroup.inv_mem _ hw)
  have hsN : s ∈ Subgroup.normalizer (Q : Set Y) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rcases h1 h hh with e | e <;> rw [e]
      · exact hh
      · exact Q.mul_mem hh hzQ
    · intro hh
      have e : h = s⁻¹ * (s * h * s⁻¹) * s⁻¹⁻¹ := by group
      rw [e]
      rcases h2 _ hh with e' | e' <;> rw [e']
      · exact hh
      · exact Q.mul_mem hh hzQ
  exact ⟨s, hQB1c s (hNeq ▸ hsN) h1, rfl⟩

theorem eq_of_invariant_map (hπ : Function.Surjective π) (hker : π.ker = Subgroup.zpowers z)
    (hz2 : z * z = 1) (hz1 : z ≠ 1) {Y₀ Q : Subgroup Y} (hzQ : z ∈ Q)
    (hNeq : Subgroup.normalizer (Q : Set Y) = Y₀)
    (hQB1 : ∀ R : Subgroup Y, R ≤ Q → (∀ g ∈ Y₀, ∀ r ∈ R, g * r * g⁻¹ ∈ R) →
      R = ⊥ ∨ R = Subgroup.zpowers z ∨ R = Q)
    (R : Subgroup X) (hRV : R ≤ Q.map π)
    (hRn : ∀ g ∈ Subgroup.normalizer ((Q.map π : Subgroup X) : Set X), ∀ r ∈ R,
      g * r * g⁻¹ ∈ R) :
    R = ⊥ ∨ R = Q.map π := by
  have hzR : z ∈ R.comap π := by
    show π z ∈ R
    rw [(map_eq_one_iff hker hz2).2 (Or.inr rfl)]
    exact R.one_mem
  have hR'Q : R.comap π ≤ Q := fun r hr => (map_mem_map_iff hker hzQ r).1 (hRV hr)
  have hR'n : ∀ g ∈ Y₀, ∀ r ∈ R.comap π, g * r * g⁻¹ ∈ R.comap π := by
    intro g hg r hr
    show π (g * r * g⁻¹) ∈ R
    rw [map_mul, map_mul, map_inv]
    exact hRn _ ((map_mem_normalizer_iff hπ hker hzQ g).2 (hNeq ▸ hg)) _ hr
  have hmap : (R.comap π).map π = R := Subgroup.map_comap_eq_self_of_surjective hπ R
  rcases hQB1 _ hR'Q hR'n with h | h | h
  · exfalso
    rw [h] at hzR
    exact hz1 (Subgroup.mem_bot.1 hzR)
  · left
    rw [← hmap, h, Subgroup.map_eq_bot_iff, hker]
  · right
    rw [← hmap, h]

theorem eq_of_normal_map (hπ : Function.Surjective π) (hker : π.ker = Subgroup.zpowers z)
    (hz : ∀ g : Y, g * z = z * g) (hz2 : z * z = 1) (hz1 : z ≠ 1) {Y₀ Q : Subgroup Y}
    (hzQ : z ∈ Q) (hQY : Q ≤ Y₀) (hNeq : Subgroup.normalizer (Q : Set Y) = Y₀)
    (hQB1 : ∀ R : Subgroup Y, R ≤ Q → (∀ g ∈ Y₀, ∀ r ∈ R, g * r * g⁻¹ ∈ R) →
      R = ⊥ ∨ R = Subgroup.zpowers z ∨ R = Q)
    (hQB1c : ∀ g ∈ Y₀, (∀ q ∈ Q, g * q * g⁻¹ = q ∨ g * q * g⁻¹ = q * z) → g ∈ Q)
    (hQB2 : ∀ R : Subgroup Y, Q ≤ R → R ≤ Y₀ → (∀ g ∈ Y₀, ∀ r ∈ R, g * r * g⁻¹ ∈ R) →
      R = Q ∨ R = Y₀)
    (R : Subgroup X) (hRN : R ≤ Subgroup.normalizer ((Q.map π : Subgroup X) : Set X))
    (hRn : ∀ g ∈ Subgroup.normalizer ((Q.map π : Subgroup X) : Set X), ∀ r ∈ R,
      g * r * g⁻¹ ∈ R) :
    R = ⊥ ∨ R = Q.map π ∨ R = Subgroup.normalizer ((Q.map π : Subgroup X) : Set X) := by
  have hQn : ∀ g ∈ Y₀, ∀ q ∈ Q, g * q * g⁻¹ ∈ Q := fun g hg q hq =>
    (Subgroup.mem_normalizer_iff.1 (hNeq ▸ hg : g ∈ Subgroup.normalizer (Q : Set Y)) q).1 hq
  have hzR : z ∈ R.comap π := by
    show π z ∈ R
    rw [(map_eq_one_iff hker hz2).2 (Or.inr rfl)]
    exact R.one_mem
  have hR'Y : R.comap π ≤ Y₀ := fun r hr => by
    have h := hRN (show π r ∈ R from hr)
    rwa [map_mem_normalizer_iff hπ hker hzQ, hNeq] at h
  have hR'n : ∀ g ∈ Y₀, ∀ r ∈ R.comap π, g * r * g⁻¹ ∈ R.comap π := by
    intro g hg r hr
    show π (g * r * g⁻¹) ∈ R
    rw [map_mul, map_mul, map_inv]
    exact hRn _ ((map_mem_normalizer_iff hπ hker hzQ g).2 (hNeq ▸ hg)) _ hr
  have hRQn : ∀ g ∈ Y₀, ∀ r ∈ R.comap π ⊓ Q, g * r * g⁻¹ ∈ R.comap π ⊓ Q := fun g hg r hr =>
    Subgroup.mem_inf.2 ⟨hR'n g hg r (Subgroup.mem_inf.1 hr).1, hQn g hg r (Subgroup.mem_inf.1 hr).2⟩
  have hmap : (R.comap π).map π = R := Subgroup.map_comap_eq_self_of_surjective hπ R
  rcases hQB1 _ inf_le_right hRQn with h | h | h
  · exfalso
    have hz' : z ∈ R.comap π ⊓ Q := Subgroup.mem_inf.2 ⟨hzR, hzQ⟩
    rw [h] at hz'
    exact hz1 (Subgroup.mem_bot.1 hz')
  · left
    have hR'Q : R.comap π ≤ Q := by
      intro r hr
      refine hQB1c r (hR'Y hr) fun q hq => ?_
      have hc : r * q * r⁻¹ * q⁻¹ ∈ R.comap π ⊓ Q := by
        refine Subgroup.mem_inf.2 ⟨?_, Q.mul_mem (hQn r (hR'Y hr) q hq) (Q.inv_mem hq)⟩
        rw [show r * q * r⁻¹ * q⁻¹ = r * (q * r⁻¹ * q⁻¹) by group]
        exact (R.comap π).mul_mem hr (hR'n q (hQY hq) _ ((R.comap π).inv_mem hr))
      rw [h, mem_zpowers_iff_of_mul_self hz2] at hc
      rcases hc with hc | hc
      · left
        exact mul_inv_eq_one.1 hc
      · right
        rw [mul_inv_eq_iff_eq_mul.1 hc]
        exact (hz q).symm
    rw [← hmap, ← inf_eq_left.2 hR'Q, h, Subgroup.map_eq_bot_iff, hker]
  · rcases hQB2 _ (inf_eq_right.1 h) hR'Y hR'n with h' | h'
    · right
      left
      rw [← hmap, h']
    · right
      right
      rw [← hmap, h', normalizer_map_eq hπ hker hzQ hNeq]

theorem card_normalizer_map [Finite Y] (hπ : Function.Surjective π)
    (hker : π.ker = Subgroup.zpowers z) (hz2 : z * z = 1) (hz1 : z ≠ 1) {Y₀ Q : Subgroup Y}
    (hzQ : z ∈ Q) (hNeq : Subgroup.normalizer (Q : Set Y) = Y₀)
    (hORD : Nat.card Y₀ = 2 ^ 41 * 3 ^ 6 * 5 ^ 3 * 7 * 11 * 23) :
    Nat.card (Subgroup.normalizer ((Q.map π : Subgroup X) : Set X)) =
      2 ^ 40 * 3 ^ 6 * 5 ^ 3 * 7 * 11 * 23 := by
  rw [normalizer_map_eq hπ hker hzQ hNeq]
  have hzY : z ∈ Y₀ := hNeq ▸ Subgroup.le_normalizer hzQ
  have h := card_map_mul_two hker hz2 hz1 hzY
  rw [hORD] at h
  norm_num at h ⊢
  omega


end Hom


theorem eq_top_of_package {Y : Type} [Group Y] [Finite Y] {z : Y}
    (hz : ∀ g : Y, g * z = z * g) (hz2 : z * z = 1) (hz1 : z ≠ 1)
    {Y₀ Q : Subgroup Y} {D₀ : Set Y} (hzQ : z ∈ Q) (hQY : Q ≤ Y₀)
    (hQn : ∀ g ∈ Y₀, ∀ q ∈ Q, g * q * g⁻¹ ∈ Q)
    (hQsq : ∀ q ∈ Q, q * q = 1 ∨ q * q = z)
    (hQcomm : ∀ q ∈ Q, ∀ r ∈ Q, q * r = r * q ∨ q * r = r * q * z)
    (hNQ : Subgroup.normalizer (Q : Set Y) ≤ Y₀)
    (hQB1 : ∀ R : Subgroup Y, R ≤ Q → (∀ g ∈ Y₀, ∀ r ∈ R, g * r * g⁻¹ ∈ R) →
      R = ⊥ ∨ R = Subgroup.zpowers z ∨ R = Q)
    (hQB1c : ∀ g ∈ Y₀, (∀ q ∈ Q, g * q * g⁻¹ = q ∨ g * q * g⁻¹ = q * z) → g ∈ Q)
    (hQB2 : ∀ R : Subgroup Y, Q ≤ R → R ≤ Y₀ → (∀ g ∈ Y₀, ∀ r ∈ R, g * r * g⁻¹ ∈ R) →
      R = Q ∨ R = Y₀)
    (hORD : Nat.card Y₀ = 2 ^ 41 * 3 ^ 6 * 5 ^ 3 * 7 * 11 * 23)
    (T : Sylow 2 Y) (hTY : (T : Subgroup Y) ≤ Y₀) (hT : Nat.card T = 2 ^ 41)
    (hD₀Q : D₀ ⊆ Q) (hD₀ : ∀ g : Y, ∀ a ∈ D₀, g * a * g⁻¹ ∈ Y₀ → g ∈ Y₀)
    (hFP : ∀ s ∈ Y₀, s ∉ Q → (s * s = 1 ∨ s * s = z) →
      ∃ a ∈ D₀, s * a * s⁻¹ = a ∨ s * a * s⁻¹ = a * z)
    {a b : Y} (ha : a ∈ Q) (hb : b ∈ Q) (ha2 : a * a = 1) (hb2 : b * b = 1) (ha1 : a ≠ 1)
    (hb1 : b ≠ 1) (hab : Commute a b) (hab1 : a * b ≠ 1) (habz : a * b ≠ z)
    (hOa : CFSG.oddCore (Subgroup.centralizer {a}) = ⊥)
    (hOb : CFSG.oddCore (Subgroup.centralizer {b}) = ⊥) (hGold : GoldschmidtTheorem) :
    Y₀ = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZn : (Subgroup.zpowers z).Normal := zpowers_normal_of_central hz
  have hπ : Function.Surjective (QuotientGroup.mk' (Subgroup.zpowers z)) :=
    QuotientGroup.mk'_surjective _
  have hker : (QuotientGroup.mk' (Subgroup.zpowers z)).ker = Subgroup.zpowers z :=
    QuotientGroup.ker_mk' _
  have hNeq := normalizer_eq_of_le hQn hNQ
  have hOY := oddCore_eq_bot_of_four hz2 hQn hQB1 ha hb ha2 hb2 ha1 hb1 hab hab1 habz hOa hOb
  have hOX : CFSG.oddCore (Y ⧸ Subgroup.zpowers z) = ⊥ :=
    oddCore_eq_bot_iff.2 fun M hM hMo =>
      eq_bot_of_odd_normal_quot hz hz2 (oddCore_eq_bot_iff.1 hOY) M hM hMo
  have hTN : (T : Subgroup Y) ≤ Subgroup.normalizer (Q : Set Y) := hNeq ▸ hTY
  have hQT : Q ≤ T := le_sylow_of_le_normalizer (isPGroup_of_sq hz2 hQsq) T hTN
  have hSN : ((T.mapSurjective hπ : Sylow 2 (Y ⧸ Subgroup.zpowers z)) :
      Subgroup (Y ⧸ Subgroup.zpowers z)) ≤
      Subgroup.normalizer ((Q.map (QuotientGroup.mk' (Subgroup.zpowers z)) : Subgroup _) :
        Set (Y ⧸ Subgroup.zpowers z)) := by
    rw [Sylow.coe_mapSurjective]
    exact (Subgroup.map_mono hTN).trans (Subgroup.le_normalizer_map _)
  have hVS : Q.map (QuotientGroup.mk' (Subgroup.zpowers z)) ≤
      ((T.mapSurjective hπ : Sylow 2 (Y ⧸ Subgroup.zpowers z)) :
        Subgroup (Y ⧸ Subgroup.zpowers z)) := by
    rw [Sylow.coe_mapSurjective]
    exact Subgroup.map_mono hQT
  have hVab : IsMulCommutative (Q.map (QuotientGroup.mk' (Subgroup.zpowers z))) :=
    ⟨⟨fun x y => Subtype.ext (map_comm hker hQcomm x x.2 y y.2)⟩⟩
  have hcardN := card_normalizer_map hπ hker hz2 hz1 hzQ hNeq hORD
  have hX : (Nat.card (Y ⧸ Subgroup.zpowers z)).factorization 2 = 40 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.zpowers z)
    rw [Nat.card_zpowers, orderOf_eq_prime (by rw [sq]; exact hz2) hz1] at h1
    have h2 := (T : Subgroup Y).card_mul_index
    rw [hT] at h2
    have hodd : Odd (T : Subgroup Y).index := Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 T.not_dvd_index)
    have h3 : Nat.card (Y ⧸ Subgroup.zpowers z) = 2 ^ 40 * (T : Subgroup Y).index := by
      rw [h1] at h2
      omega
    rw [h3, Recog.GoldschmidtArith.factorization_two_pow_mul_odd _ hodd]
  have hV := Recog.normal_of_goldschmidt_conclusion (T.mapSurjective hπ) hVS hVab
    (hGold (Y ⧸ Subgroup.zpowers z) (T.mapSurjective hπ)
      (Q.map (QuotientGroup.mk' (Subgroup.zpowers z))) hVS hVab
      (strongly_closed_package hπ hker hz hz2 hzQ hQY hNeq hQsq hQcomm T hTY hD₀Q hD₀ hFP hSN))
    hOX (centralizer_map_le hπ hker hz hz2 hzQ hNeq hQB1c)
    (fun W hWV hNW => eq_of_invariant_map hπ hker hz2 hz1 hzQ hNeq hQB1 W hWV
      fun g hg r hr => (Subgroup.mem_normalizer_iff.1 (hNW hg) r).1 hr)
    (fun R hVR hRN hNR => by
      rcases eq_of_normal_map hπ hker hz hz2 hz1 hzQ hQY hNeq hQB1 hQB1c hQB2 R hRN
        (fun g hg r hr => (Subgroup.mem_normalizer_iff.1 (hNR hg) r).1 hr) with h | h | h
      · left
        rw [h]
        exact (le_bot_iff.1 (h ▸ hVR)).symm
      · exact Or.inl h
      · exact Or.inr h)
    (Recog.hAr_of_card (by rw [hcardN]; exact Dvd.intro (3 ^ 6 * 5 ^ 3 * 7 * 11 * 23) (by ring))
      (by rw [hcardN]; exact Dvd.intro_left (2 ^ 40 * 3 ^ 6 * 5 ^ 3 * 7 * 11) rfl) hX)
  have hQnorm : Q.Normal := by
    refine ⟨fun q hq g => ?_⟩
    have h1 : QuotientGroup.mk' (Subgroup.zpowers z) (g * q * g⁻¹) ∈
        Q.map (QuotientGroup.mk' (Subgroup.zpowers z)) := by
      rw [map_mul, map_mul, map_inv]
      exact hV.conj_mem _ ⟨q, hq, rfl⟩ _
    exact (map_mem_map_iff hker hzQ _).1 h1
  rw [← hNeq, Subgroup.normalizer_eq_top_iff.2 hQnorm]



section Transport

variable {S G : Type*} [Group S] [Group G] {Φ : S →* G}

theorem map_mem_centralizer_map_iff (hinj : Function.Injective Φ) {s t : S} :
    Φ s ∈ Subgroup.centralizer {Φ t} ↔ s ∈ Subgroup.centralizer {t} := by
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff,
    ← map_mul, ← map_mul]
  exact hinj.eq_iff

theorem eq_subgroupOf_map_comap {C : Subgroup G} {R : Subgroup C}
    (hR : R ≤ Φ.range.subgroupOf C) : R = (((R.map C.subtype).comap Φ).map Φ).subgroupOf C := by
  ext r
  rw [Subgroup.mem_subgroupOf, Subgroup.map_comap_eq, Subgroup.mem_inf]
  constructor
  · intro hr
    exact ⟨Subgroup.mem_subgroupOf.1 (hR hr), ⟨r, hr, rfl⟩⟩
  · rintro ⟨-, r', hr', hrr'⟩
    have e : r' = r := Subtype.ext hrr'
    rwa [← e]

theorem zpowers_subgroupOf {C : Subgroup G} {t : G} (ht : t ∈ C) (ht2 : t * t = 1) :
    (Subgroup.zpowers t).subgroupOf C = Subgroup.zpowers (⟨t, ht⟩ : C) := by
  ext y
  rw [Subgroup.mem_subgroupOf, TwoB.mem_zpowers_iff_of_mul_self ht2,
    TwoB.mem_zpowers_iff_of_mul_self (show (⟨t, ht⟩ : C) * ⟨t, ht⟩ = 1 from Subtype.ext ht2)]
  constructor
  · rintro (h | h)
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  · rintro (h | h)
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)

theorem exists_sylow_le_range [Finite G] (hinj : Function.Injective Φ) {x : S} {C : Subgroup G}
    (hC : (Subgroup.centralizer {x} : Subgroup S).map Φ ≤ C)
    (hG : ∃ m : ℕ, Odd m ∧ Nat.card G = 2 ^ 41 * m)
    (hORD : Nat.card (Subgroup.centralizer {x} : Subgroup S) =
      2 ^ 41 * 3 ^ 6 * 5 ^ 3 * 7 * 11 * 23) :
    ∃ T : Sylow 2 C, (T : Subgroup C) ≤ Φ.range.subgroupOf C ∧ Nat.card T = 2 ^ 41 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite S := Finite.of_injective Φ hinj
  obtain ⟨P⟩ : Nonempty (Sylow 2 (Subgroup.centralizer {x} : Subgroup S)) := inferInstance
  have hP : Nat.card P = 2 ^ 41 := by
    rw [P.card_eq_multiplicity, hORD, show 2 ^ 41 * 3 ^ 6 * 5 ^ 3 * 7 * 11 * 23 =
      2 ^ 41 * (3 ^ 6 * 5 ^ 3 * 7 * 11 * 23) by ring,
      Recog.GoldschmidtArith.factorization_two_pow_mul_odd _ (by decide)]
  obtain ⟨T₀, hT₀def⟩ : ∃ T₀ : Subgroup G,
      T₀ = ((P : Subgroup _).map (Subgroup.centralizer {x}).subtype).map Φ := ⟨_, rfl⟩
  have hT₀ : Nat.card T₀ = 2 ^ 41 := by
    rw [hT₀def, Subgroup.card_map_of_injective hinj,
      Subgroup.card_map_of_injective (Subgroup.centralizer {x}).subtype_injective, hP]
  obtain ⟨m, hm, hGm⟩ := hG
  have hT₀' : Nat.card T₀ = 2 ^ (Nat.card G).factorization 2 := by
    rw [hT₀, hGm, Recog.GoldschmidtArith.factorization_two_pow_mul_odd _ hm]
  have hT₀C : T₀ ≤ C := hT₀def ▸ (Subgroup.map_mono (Subgroup.map_subtype_le _)).trans hC
  have hT₀R : T₀ ≤ Φ.range := hT₀def ▸ Subgroup.map_le_range Φ _
  refine ⟨(Sylow.ofCard T₀ hT₀').subtype (by rw [Sylow.coe_ofCard]; exact hT₀C), ?_, ?_⟩
  · intro y hy
    rw [Sylow.coe_subtype, Sylow.coe_ofCard, Subgroup.mem_subgroupOf] at hy
    exact Subgroup.mem_subgroupOf.2 (hT₀R hy)
  · rw [Sylow.coe_subtype, Sylow.coe_ofCard,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT₀C).toEquiv, hT₀]

theorem oddCore_centralizer_mk_eq_bot (hinj : Function.Injective Φ) {x : S} {C : Subgroup G}
    (hC : ∀ s : S, Φ s ∈ C ↔ s ∈ Subgroup.centralizer {x}) {a : S} (haC : Φ a ∈ C)
    (haM : Subgroup.centralizer {Φ a} ≤ Φ.range)
    (hO : CFSG.oddCore ↥(Subgroup.centralizer {a} ⊓ Subgroup.centralizer {x}) = ⊥) :
    CFSG.oddCore ↥(Subgroup.centralizer {(⟨Φ a, haC⟩ : C)}) = ⊥ := by
  let f : ↥(Subgroup.centralizer {a} ⊓ Subgroup.centralizer {x}) →*
      ↥(Subgroup.centralizer {(⟨Φ a, haC⟩ : C)}) :=
    { toFun := fun s => ⟨⟨Φ (s : S), (hC s).2 (Subgroup.mem_inf.1 s.2).2⟩, by
        rw [Subgroup.mem_centralizer_singleton_iff]
        apply Subtype.ext
        show Φ (s : S) * Φ a = Φ a * Φ (s : S)
        rw [← map_mul, ← map_mul,
          Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 s.2).1]⟩
      map_one' := by
        apply Subtype.ext
        apply Subtype.ext
        exact map_one Φ
      map_mul' := fun s t => by
        apply Subtype.ext
        apply Subtype.ext
        exact map_mul Φ (s : S) (t : S) }
  have hf : Function.Bijective f := by
    refine ⟨fun s t h => ?_, fun y => ?_⟩
    · have h' : Φ (s : S) = Φ (t : S) :=
        congrArg (fun y : ↥(Subgroup.centralizer {(⟨Φ a, haC⟩ : C)}) => ((y : C) : G)) h
      exact Subtype.ext (hinj h')
    · have hya : ((y : C) : G) ∈ Subgroup.centralizer {Φ a} := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 y.2)
      obtain ⟨s, hs⟩ := haM hya
      have hsC : s ∈ Subgroup.centralizer {x} := (hC s).1 (hs ▸ (y : C).2)
      have hsa : s ∈ Subgroup.centralizer {a} := by
        rw [← map_mem_centralizer_map_iff hinj, hs]
        exact hya
      refine ⟨⟨s, Subgroup.mem_inf.2 ⟨hsa, hsC⟩⟩, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      exact hs
  exact oddCore_eq_bot_of_equiv (MulEquiv.ofBijective f hf) hO

theorem centralizer_le_range_gen
    {S G : Type} [Group S] [Group G] [Finite G] {Φ : S →* G}
    (hinj : Function.Injective Φ) {x : S} (hx2 : x * x = 1) (hx1 : x ≠ 1) {d : G}
    (P : S → Prop) (hP2 : ∀ a, P a → a * a = 1 ∧ a ≠ 1)
    (hPd : ∀ a, P a → Φ a ∈ dZero Φ.range d)
    (hCent : ∀ m ∈ Φ.range, Subgroup.centralizer {m * d * m⁻¹} ≤ Φ.range)
    (hD : ∀ y ∈ Φ.range, IsConj d y → y ∈ dZero Φ.range d)
    (hnorm : ∀ X : Subgroup G, X ≤ Φ.range → (∃ a ∈ X, a ∈ dZero Φ.range d) →
      Subgroup.normalizer (X : Set G) ≤ Φ.range)
    (hGcard : ∃ m : ℕ, Odd m ∧ Nat.card G = 2 ^ 41 * m)
    (Qh : Subgroup S) (hQC : Qh ≤ Subgroup.centralizer {x}) (hxQ : x ∈ Qh)
    (hQn : ∀ g ∈ Subgroup.centralizer {x}, ∀ q ∈ Qh, g * q * g⁻¹ ∈ Qh)
    (hQsq : ∀ q ∈ Qh, q * q = 1 ∨ q * q = x)
    (hQcomm : ∀ q ∈ Qh, ∀ r ∈ Qh, q * r = r * q ∨ q * r = r * q * x)
    (hQB1 : ∀ R : Subgroup S, R ≤ Qh →
      (∀ g ∈ Subgroup.centralizer {x}, ∀ r ∈ R, g * r * g⁻¹ ∈ R) →
      R = ⊥ ∨ R = Subgroup.zpowers x ∨ R = Qh)
    (hQB1c : ∀ g ∈ Subgroup.centralizer {x},
      (∀ q ∈ Qh, g * q * g⁻¹ = q ∨ g * q * g⁻¹ = q * x) → g ∈ Qh)
    (hQB2 : ∀ R : Subgroup S, Qh ≤ R → R ≤ Subgroup.centralizer {x} →
      (∀ g ∈ Subgroup.centralizer {x}, ∀ r ∈ R, g * r * g⁻¹ ∈ R) →
      R = Qh ∨ R = Subgroup.centralizer {x})
    (hQB3 : ∃ a ∈ Qh, ∃ b ∈ Qh, P a ∧ P b ∧ a * b = b * a ∧ a * b ≠ 1 ∧ a * b ≠ x ∧
      CFSG.oddCore ↥(Subgroup.centralizer {a} ⊓ Subgroup.centralizer {x}) = ⊥ ∧
      CFSG.oddCore ↥(Subgroup.centralizer {b} ⊓ Subgroup.centralizer {x}) = ⊥)
    (hFP : ∀ s ∈ Subgroup.centralizer {x}, s ∉ Qh → (s * s = 1 ∨ s * s = x) →
      ∃ a ∈ Qh, P a ∧ (s * a * s⁻¹ = a ∨ s * a * s⁻¹ = a * x))
    (hORD : Nat.card (Subgroup.centralizer {x} : Subgroup S) =
      2 ^ 41 * 3 ^ 6 * 5 ^ 3 * 7 * 11 * 23)
    (hGold : GoldschmidtTheorem) :
    Subgroup.centralizer {Φ x} ≤ Φ.range := by
  have hlabC : ∀ a : S, P a → Subgroup.centralizer {Φ a} ≤ Φ.range :=
    fun a ha => centralizer_le_of_mem_dZero hCent (hPd a ha)
  have hCiff : ∀ s : S, Φ s ∈ Subgroup.centralizer {Φ x} ↔ s ∈ Subgroup.centralizer {x} :=
    fun s => map_mem_centralizer_map_iff hinj
  set C := Subgroup.centralizer {Φ x} with hCdef
  set z : C := ⟨Φ x, mem_centralizer_singleton_self _⟩ with hzdef
  set Y₀ : Subgroup C := Φ.range.subgroupOf C with hY₀def
  set QY : Subgroup C := (Qh.map Φ).subgroupOf C with hQYdef
  set D₀ : Set C := {y | ∃ a ∈ Qh, P a ∧ (y : G) = Φ a} with hD₀def
  have hY₀ : ∀ y : C, y ∈ Y₀ → ∃ s, s ∈ Subgroup.centralizer {x} ∧ Φ s = (y : G) := by
    intro y hy
    obtain ⟨s, hs⟩ := Subgroup.mem_subgroupOf.1 hy
    exact ⟨s, (hCiff s).1 (by rw [hs]; exact y.2), hs⟩
  have hmkQ : ∀ q ∈ Qh, Φ q ∈ C := fun q hq => (hCiff q).2 (hQC hq)
  have hz : ∀ g : C, g * z = z * g := fun g =>
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 g.2)
  have hz2 : z * z = 1 := Subtype.ext (show Φ x * Φ x = 1 by rw [← map_mul, hx2, map_one])
  have hz1 : z ≠ 1 := fun h => hx1 (hinj ((congrArg Subtype.val h).trans (map_one Φ).symm))
  have hzQ : z ∈ QY := Subgroup.mem_subgroupOf.2 ⟨x, hxQ, rfl⟩
  have hQY : QY ≤ Y₀ := fun y hy => by
    obtain ⟨q, -, hq⟩ := Subgroup.mem_subgroupOf.1 hy
    exact Subgroup.mem_subgroupOf.2 ⟨q, hq⟩
  have hQnY : ∀ g ∈ Y₀, ∀ q ∈ QY, g * q * g⁻¹ ∈ QY := by
    intro g hg q hq
    obtain ⟨s, hs, hsg⟩ := hY₀ g hg
    obtain ⟨q', hq', hqq'⟩ := Subgroup.mem_subgroupOf.1 hq
    refine Subgroup.mem_subgroupOf.2 ⟨s * q' * s⁻¹, hQn s hs q' hq', ?_⟩
    show Φ (s * q' * s⁻¹) = (g : G) * q * (g : G)⁻¹
    rw [map_mul, map_mul, map_inv, hsg, hqq']
  have hQsqY : ∀ q ∈ QY, q * q = 1 ∨ q * q = z := by
    intro q hq
    obtain ⟨q', hq', hqq'⟩ := Subgroup.mem_subgroupOf.1 hq
    rcases hQsq q' hq' with h | h
    · left
      apply Subtype.ext
      show (q : G) * q = 1
      rw [← hqq', ← map_mul, h, map_one]
    · right
      apply Subtype.ext
      show (q : G) * q = Φ x
      rw [← hqq', ← map_mul, h]
  have hQcommY : ∀ q ∈ QY, ∀ r ∈ QY, q * r = r * q ∨ q * r = r * q * z := by
    intro q hq r hr
    obtain ⟨q', hq', hqq'⟩ := Subgroup.mem_subgroupOf.1 hq
    obtain ⟨r', hr', hrr'⟩ := Subgroup.mem_subgroupOf.1 hr
    rcases hQcomm q' hq' r' hr' with h | h
    · left
      apply Subtype.ext
      show (q : G) * r = r * q
      rw [← hqq', ← hrr', ← map_mul, h, map_mul]
    · right
      apply Subtype.ext
      show (q : G) * r = r * q * Φ x
      rw [← hqq', ← hrr', ← map_mul, h, map_mul, map_mul]
  obtain ⟨a, haQ, b, hbQ, hac, hbc, hab, hab1, habx, hOa, hOb⟩ := hQB3
  have hNQY : Subgroup.normalizer (QY : Set C) ≤ Y₀ := by
    intro g hg
    have hgN : (g : G) ∈ Subgroup.normalizer ((Qh.map Φ : Subgroup G) : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · intro hh
        have hhC : h ∈ C := by
          obtain ⟨q, hq, rfl⟩ := hh
          exact hmkQ q hq
        exact Subgroup.mem_subgroupOf.1
          ((Subgroup.mem_normalizer_iff.1 hg ⟨h, hhC⟩).1 (Subgroup.mem_subgroupOf.2 hh))
      · intro hh
        have hhC : (g : G) * h * (g : G)⁻¹ ∈ C := by
          obtain ⟨q, hq, hq'⟩ := hh
          rw [← hq']
          exact hmkQ q hq
        have hhC' : h ∈ C := by
          have h3 := C.mul_mem (C.mul_mem (C.inv_mem g.2) hhC) g.2
          rwa [show (g : G)⁻¹ * ((g : G) * h * (g : G)⁻¹) * g = h by group] at h3
        exact Subgroup.mem_subgroupOf.1
          ((Subgroup.mem_normalizer_iff.1 hg ⟨h, hhC'⟩).2 (Subgroup.mem_subgroupOf.2 hh))
    exact Subgroup.mem_subgroupOf.2 (hnorm _ (Subgroup.map_le_range Φ Qh)
      ⟨Φ a, ⟨a, haQ, rfl⟩, hPd a hac⟩ hgN)
  have hpull : ∀ R : Subgroup C, (∀ g ∈ Y₀, ∀ r ∈ R, g * r * g⁻¹ ∈ R) →
      ∀ g ∈ Subgroup.centralizer {x}, ∀ s ∈ (R.map C.subtype).comap Φ,
        g * s * g⁻¹ ∈ (R.map C.subtype).comap Φ := by
    intro R hRn g hg s hs
    obtain ⟨r, hr, hrs⟩ := hs
    have hgY : (⟨Φ g, (hCiff g).2 hg⟩ : C) ∈ Y₀ := Subgroup.mem_subgroupOf.2 ⟨g, rfl⟩
    refine ⟨_, hRn _ hgY r hr, ?_⟩
    show Φ g * (r : G) * (Φ g)⁻¹ = Φ (g * s * g⁻¹)
    rw [map_mul, map_mul, map_inv]
    congr 2
  have hQB1Y : ∀ R : Subgroup C, R ≤ QY → (∀ g ∈ Y₀, ∀ r ∈ R, g * r * g⁻¹ ∈ R) →
      R = ⊥ ∨ R = Subgroup.zpowers z ∨ R = QY := by
    intro R hRQ hRn
    have hRQh : (R.map C.subtype).comap Φ ≤ Qh := by
      intro s hs
      obtain ⟨r, hr, hrs⟩ := hs
      obtain ⟨q, hq, hqr⟩ := Subgroup.mem_subgroupOf.1 (hRQ hr)
      have e : q = s := hinj (hqr.trans hrs)
      exact e ▸ hq
    have hRR := eq_subgroupOf_map_comap (hRQ.trans hQY)
    rcases hQB1 _ hRQh (hpull R hRn) with h | h | h
    · left
      rw [hRR, h, Subgroup.map_bot, Subgroup.bot_subgroupOf]
    · right
      left
      rw [hRR, h, MonoidHom.map_zpowers]
      exact zpowers_subgroupOf _ (by rw [← map_mul, hx2, map_one])
    · right
      right
      rw [hRR, h]
  have hQB1cY : ∀ g ∈ Y₀, (∀ q ∈ QY, g * q * g⁻¹ = q ∨ g * q * g⁻¹ = q * z) → g ∈ QY := by
    intro g hg hgq
    obtain ⟨s, hs, hsg⟩ := hY₀ g hg
    refine Subgroup.mem_subgroupOf.2 ⟨s, hQB1c s hs fun q hq => ?_, hsg⟩
    have hqY : (⟨Φ q, hmkQ q hq⟩ : C) ∈ QY := Subgroup.mem_subgroupOf.2 ⟨q, hq, rfl⟩
    rcases hgq _ hqY with h | h
    · left
      apply hinj
      rw [map_mul, map_mul, map_inv, hsg]
      exact congrArg Subtype.val h
    · right
      apply hinj
      rw [map_mul, map_mul, map_inv, hsg, map_mul]
      exact congrArg Subtype.val h
  have hQB2Y : ∀ R : Subgroup C, QY ≤ R → R ≤ Y₀ → (∀ g ∈ Y₀, ∀ r ∈ R, g * r * g⁻¹ ∈ R) →
      R = QY ∨ R = Y₀ := by
    intro R hQR hRY hRn
    have hQhR : Qh ≤ (R.map C.subtype).comap Φ := fun q hq =>
      ⟨⟨Φ q, hmkQ q hq⟩, hQR (Subgroup.mem_subgroupOf.2 ⟨q, hq, rfl⟩), rfl⟩
    have hRC : (R.map C.subtype).comap Φ ≤ Subgroup.centralizer {x} := by
      intro s hs
      obtain ⟨r, -, hrs⟩ := hs
      exact (hCiff s).1 (by rw [← hrs]; exact r.2)
    have hRR := eq_subgroupOf_map_comap hRY
    rcases hQB2 _ hQhR hRC (hpull R hRn) with h | h
    · left
      rw [hRR, h]
    · right
      rw [hRR, h]
      ext y
      simp only [Subgroup.mem_subgroupOf]
      constructor
      · rintro ⟨s, -, hs⟩
        exact ⟨s, hs⟩
      · rintro ⟨s, hs⟩
        exact ⟨s, (hCiff s).1 (by rw [hs]; exact y.2), hs⟩
  have hORDY : Nat.card Y₀ = 2 ^ 41 * 3 ^ 6 * 5 ^ 3 * 7 * 11 * 23 := by
    have h1 : Y₀.map C.subtype = (Subgroup.centralizer {x} : Subgroup S).map Φ := by
      rw [hY₀def, Subgroup.subgroupOf_map_subtype]
      ext y
      simp only [Subgroup.mem_inf, MonoidHom.mem_range, Subgroup.mem_map]
      constructor
      · rintro ⟨⟨s, rfl⟩, hy⟩
        exact ⟨s, (hCiff s).1 hy, rfl⟩
      · rintro ⟨s, hs, rfl⟩
        exact ⟨⟨s, rfl⟩, (hCiff s).2 hs⟩
    have h2 : Nat.card (Y₀.map C.subtype) = Nat.card Y₀ :=
      Subgroup.card_map_of_injective C.subtype_injective
    rw [h1, Subgroup.card_map_of_injective hinj, hORD] at h2
    exact h2.symm
  obtain ⟨T, hTY, hT⟩ := exists_sylow_le_range hinj (C := C)
    (fun y hy => by
      obtain ⟨s, hs, rfl⟩ := hy
      exact (hCiff s).2 hs) hGcard hORD
  have hD₀Q : D₀ ⊆ QY := by
    rintro y ⟨a', ha', -, hy⟩
    exact Subgroup.mem_subgroupOf.2 ⟨a', ha', hy.symm⟩
  have hD₀Y : ∀ g : C, ∀ a' ∈ D₀, g * a' * g⁻¹ ∈ Y₀ → g ∈ Y₀ := by
    rintro g y ⟨a', -, ha'c, hy⟩ hgy
    have h1 : (y : G) ∈ dZero Φ.range d := hy ▸ hPd a' ha'c
    obtain ⟨m, hm, hmy⟩ := h1
    have h2 : (g : G) * y * (g : G)⁻¹ ∈ dZero Φ.range d :=
      hD _ (Subgroup.mem_subgroupOf.1 hgy) (by
        rw [← hmy]
        exact isConj_iff.2 ⟨g * m, by group⟩)
    exact Subgroup.mem_subgroupOf.2 (mem_of_conj_mem_dZero hCent ⟨m, hm, hmy⟩ h2)
  have hFPY : ∀ s ∈ Y₀, s ∉ QY → (s * s = 1 ∨ s * s = z) →
      ∃ a' ∈ D₀, s * a' * s⁻¹ = a' ∨ s * a' * s⁻¹ = a' * z := by
    intro s hs hsQ hs2
    obtain ⟨t, ht, hts⟩ := hY₀ s hs
    have htQ : t ∉ Qh := fun h => hsQ (Subgroup.mem_subgroupOf.2 ⟨t, h, hts⟩)
    have ht2 : t * t = 1 ∨ t * t = x := by
      rcases hs2 with h | h
      · left
        apply hinj
        rw [map_mul, hts, map_one]
        exact congrArg Subtype.val h
      · right
        apply hinj
        rw [map_mul, hts]
        exact congrArg Subtype.val h
    obtain ⟨a', ha', ha'c, hta⟩ := hFP t ht htQ ht2
    refine ⟨⟨Φ a', hmkQ a' ha'⟩, ⟨a', ha', ha'c, rfl⟩, ?_⟩
    rcases hta with h | h
    · left
      apply Subtype.ext
      show (s : G) * Φ a' * (s : G)⁻¹ = Φ a'
      rw [← hts, ← map_inv, ← map_mul, ← map_mul, h]
    · right
      apply Subtype.ext
      show (s : G) * Φ a' * (s : G)⁻¹ = Φ a' * Φ x
      rw [← hts, ← map_inv, ← map_mul, ← map_mul, h, map_mul]
  obtain ⟨ha2, ha1⟩ := hP2 a hac
  obtain ⟨hb2, hb1⟩ := hP2 b hbc
  have haY : (⟨Φ a, hmkQ a haQ⟩ : C) ∈ QY := Subgroup.mem_subgroupOf.2 ⟨a, haQ, rfl⟩
  have hbY : (⟨Φ b, hmkQ b hbQ⟩ : C) ∈ QY := Subgroup.mem_subgroupOf.2 ⟨b, hbQ, rfl⟩
  have key := eq_top_of_package (Y := C) (z := z) hz hz2 hz1 (Y₀ := Y₀) (Q := QY)
    (D₀ := D₀) hzQ hQY hQnY hQsqY hQcommY hNQY hQB1Y hQB1cY hQB2Y hORDY T hTY hT hD₀Q hD₀Y hFPY
    haY hbY
    (Subtype.ext (show Φ a * Φ a = 1 by rw [← map_mul, ha2, map_one]))
    (Subtype.ext (show Φ b * Φ b = 1 by rw [← map_mul, hb2, map_one]))
    (fun h => ha1 (hinj ((congrArg Subtype.val h).trans (map_one Φ).symm)))
    (fun h => hb1 (hinj ((congrArg Subtype.val h).trans (map_one Φ).symm)))
    (Subtype.ext (show Φ a * Φ b = Φ b * Φ a by rw [← map_mul, hab, map_mul]))
    (fun h => hab1 (hinj (by
      have h' := congrArg Subtype.val h
      rw [map_mul, map_one]
      exact h')))
    (fun h => habx (hinj (by
      have h' := congrArg Subtype.val h
      rw [map_mul]
      exact h')))
    (oddCore_centralizer_mk_eq_bot hinj hCiff (hmkQ a haQ) (hlabC a hac) hOa)
    (oddCore_centralizer_mk_eq_bot hinj hCiff (hmkQ b hbQ) (hlabC b hbc) hOb) hGold
  intro g hg
  have hgY : (⟨g, hg⟩ : C) ∈ Y₀ := key ▸ Subgroup.mem_top _
  exact Subgroup.mem_subgroupOf.1 hgY


end Transport

end TwoB


private theorem xhatS_ne_one_aux : xhatS ≠ 1 := fun h => by
  have h2 := orderOf_sEquiv_xs
  rw [sEquiv_xs, h, orderOf_one] at h2
  exact absurd h2 (by decide)

theorem mul_self_and_ne_one_of_isConj_cV0
    {a : Shat} (ha : IsConj (cV0 : Shat) a) :
    a * a = 1 ∧ a ≠ 1 := by
  obtain ⟨g, rfl⟩ := isConj_iff.1 ha
  refine ⟨?_, fun h => ?_⟩
  · calc g * (cV0 : Shat) * g⁻¹ * (g * cV0 * g⁻¹) = g * (cV0 * cV0) * g⁻¹ := by group
      _ = 1 := by rw [cV0_mul_self_coe, mul_one, mul_inv_cancel]
  · have h' : (cV0 : Shat) = 1 := by
      rw [show (cV0 : Shat) = g⁻¹ * (g * cV0 * g⁻¹) * g by group, h, mul_one, inv_mul_cancel]
    exact cV0_ne_one (Subtype.ext h')

theorem centralizer_le_range_of_twoB
    {G : Type} [Group G] [Finite G] {d : G} (hd : d ≠ 1)
    (ψ : Subgroup.centralizer {d} ≃* vStab cv0) (Φ : Shat →* G)
    (hΦ : ∀ a : vStab cv0, Φ a = psiInvHom ψ a)
    (hDM : conjugatesOf d ∩ (Φ.range : Set G) = dZero Φ.range d) (Qh : Subgroup Shat)
    (hQC : Qh ≤ Subgroup.centralizer {xhatS}) (hxQ : xhatS ∈ Qh)
    (hQn : ∀ g ∈ Subgroup.centralizer {xhatS}, ∀ q ∈ Qh, g * q * g⁻¹ ∈ Qh)
    (hQsq : ∀ q ∈ Qh, q * q = 1 ∨ q * q = xhatS)
    (hQcomm : ∀ q ∈ Qh, ∀ r ∈ Qh, q * r = r * q ∨ q * r = r * q * xhatS)
    (hQB1 : ∀ R : Subgroup Shat, R ≤ Qh →
      (∀ g ∈ Subgroup.centralizer {xhatS}, ∀ r ∈ R, g * r * g⁻¹ ∈ R) →
      R = ⊥ ∨ R = Subgroup.zpowers xhatS ∨ R = Qh)
    (hQB1c : ∀ g ∈ Subgroup.centralizer {xhatS},
      (∀ q ∈ Qh, g * q * g⁻¹ = q ∨ g * q * g⁻¹ = q * xhatS) → g ∈ Qh)
    (hQB2 : ∀ R : Subgroup Shat, Qh ≤ R → R ≤ Subgroup.centralizer {xhatS} →
      (∀ g ∈ Subgroup.centralizer {xhatS}, ∀ r ∈ R, g * r * g⁻¹ ∈ R) →
      R = Qh ∨ R = Subgroup.centralizer {xhatS})
    (hQB3 : ∃ a ∈ Qh, ∃ b ∈ Qh, IsConj (cV0 : Shat) a ∧ IsConj (cV0 : Shat) b ∧ a * b = b * a ∧
      a * b ≠ 1 ∧ a * b ≠ xhatS ∧
      CFSG.oddCore ↥(Subgroup.centralizer {a} ⊓ Subgroup.centralizer {xhatS}) = ⊥ ∧
      CFSG.oddCore ↥(Subgroup.centralizer {b} ⊓ Subgroup.centralizer {xhatS}) = ⊥)
    (hFP : ∀ s ∈ Subgroup.centralizer {xhatS}, s ∉ Qh → (s * s = 1 ∨ s * s = xhatS) →
      ∃ a ∈ Qh, IsConj (cV0 : Shat) a ∧ (s * a * s⁻¹ = a ∨ s * a * s⁻¹ = a * xhatS))
    (hORD : Nat.card (Subgroup.centralizer {xhatS} : Subgroup Shat) =
      2 ^ 41 * 3 ^ 6 * 5 ^ 3 * 7 * 11 * 23)
    (hGold : GoldschmidtTheorem) :
    Subgroup.centralizer {Φ xhatS} ≤ Φ.range := by
  have hΦc : Φ (cV0 : Shat) = d := map_cV0_of_psiInvHom hd ψ hΦ
  have hinj : Function.Injective Φ := injective_of_map_cV0_ne_one Φ (hΦc.symm ▸ hd)
  obtain ⟨-, -, hGcard, -, hnorm, -⟩ := completion_fusion hd ψ Φ hΦ hDM
  refine TwoB.centralizer_le_range_gen hinj xhatS_mul_self xhatS_ne_one_aux
    (fun a => IsConj (cV0 : Shat) a) (fun a ha => mul_self_and_ne_one_of_isConj_cV0 ha)
    (fun a ha => ?_) (completion_centralizer hd ψ Φ hΦ).2.2
    (fun y hy hdy => hDM ▸ (⟨hdy, hy⟩ : y ∈ conjugatesOf d ∩ (Φ.range : Set G))) hnorm hGcard
    Qh hQC hxQ hQn hQsq hQcomm hQB1 hQB1c hQB2 hQB3 hFP hORD hGold
  obtain ⟨g, rfl⟩ := isConj_iff.1 ha
  exact ⟨Φ g, ⟨g, rfl⟩, by rw [map_mul, map_mul, map_inv, hΦc]⟩

theorem centralizer_le_range_of_twoB_native
    {G : Type} [Group G] [Finite G] {d : G}
    (hd : d ≠ 1) (ψ : Subgroup.centralizer {d} ≃* vStab cv0) (Φ : Shat →* G)
    (hΦ : ∀ a : vStab cv0, Φ a = psiInvHom ψ a)
    (hDM : conjugatesOf d ∩ (Φ.range : Set G) = dZero Φ.range d) (hGold : GoldschmidtTheorem) :
    Subgroup.centralizer {Φ xhatS} ≤ Φ.range :=
  centralizer_le_range_of_twoB hd ψ Φ hΦ hDM QhatS QhatS_le_centralizer xhatS_mem_QhatS
    (fun _ hg _ hq => conj_mem_QhatS hg hq) (fun _ hq => mul_self_of_mem_QhatS hq)
    (fun _ hq _ hr => comm_of_mem_QhatS hq hr) eq_of_invariant_QhatS
    (fun _ hg h => mem_QhatS_of_conj hg h) eq_of_normal_QhatS exists_twoA_pair_QhatS
    (fun _ hs hsQ hs2 => exists_twoA_fixed_QhatS hs hsQ hs2) natCard_centralizer_xhatS hGold

theorem centralizer_le_range_of_rankS_eq_2048
    {G : Type} [Group G] [Finite G] {d : G}
    (hd : d ≠ 1) (ψ : Subgroup.centralizer {d} ≃* vStab cv0) (Φ : Shat →* G)
    (hΦ : ∀ a : vStab cv0, Φ a = psiInvHom ψ a)
    (hDM : conjugatesOf d ∩ (Φ.range : Set G) = dZero Φ.range d) (hGold : GoldschmidtTheorem) :
    ∀ s : Shat, orderOf s = 2 → rankS s = 2048 → Subgroup.centralizer {Φ s} ≤ Φ.range := by
  intro s hs hrk
  have hx : orderOf xhatS = 2 := sEquiv_xs ▸ orderOf_sEquiv_xs
  have hxr : rankS xhatS = 2048 := sEquiv_xs ▸ rankS_sEquiv_xs
  obtain ⟨g, rfl⟩ := isConj_iff.1 (isConj_of_rankS_eq hx hs (hxr.trans hrk.symm))
  rw [map_mul, map_mul, map_inv]
  exact centralizer_conj_le_range (centralizer_le_range_of_twoB_native hd ψ Φ hΦ hDM hGold)
    ⟨g, rfl⟩

theorem centralizer_le_range_of_rankS_eq_2158_of_gold
    {G : Type} [Group G] [Finite G] {d : G}
    (hd : d ≠ 1) (ψ : Subgroup.centralizer {d} ≃* vStab cv0) (Φ : Shat →* G)
    (hΦ : ∀ a : vStab cv0, Φ a = psiInvHom ψ a)
    (hDM : conjugatesOf d ∩ (Φ.range : Set G) = dZero Φ.range d) (hGold : GoldschmidtTheorem)
    {s : Shat} (hs : orderOf s = 2) (hrk : rankS s = 2158) :
    Subgroup.centralizer {Φ s} ≤ Φ.range :=
  centralizer_le_range_of_rankS_eq_2158_of_twoB hd ψ Φ hΦ hDM
    (centralizer_le_range_of_rankS_eq_2048 hd ψ Φ hΦ hDM hGold) hs hrk


end CFSG.Monster.B.GSide
