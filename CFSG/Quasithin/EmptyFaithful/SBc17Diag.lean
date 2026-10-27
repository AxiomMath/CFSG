module

public import CFSG.Quasithin.EmptyFaithful.SBc17In
public import CFSG.Quasithin.EmptyFaithful.SBc13JM5Rank
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits
open scoped commutatorElement

namespace SBc17

variable {G : Type} [Group G]

theorem exists_fixed_mem_coset [Finite G] {E W : Subgroup G} (hE : IsPGroup 5 E)
    (hW : IsPGroup 2 W) (hEW : E ≤ Subgroup.normalizer (W : Set G)) {y : G}
    (hy : ∀ e ∈ E, ∃ w ∈ W, e * y * e⁻¹ = y * w) :
    ∃ w ∈ W, ∀ e ∈ E, e * (y * w) * e⁻¹ = y * w := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hconj : ∀ (e : E) (x : G), y⁻¹ * x ∈ W → y⁻¹ * ((e : G) * x * (e : G)⁻¹) ∈ W := by
    intro e x hx
    obtain ⟨w, hw, hyw⟩ := hy e e.2
    have h1 : y⁻¹ * ((e : G) * x * (e : G)⁻¹) =
        w * ((e : G) * (y⁻¹ * x) * (e : G)⁻¹) := by
      calc y⁻¹ * ((e : G) * x * (e : G)⁻¹)
          = (y⁻¹ * ((e : G) * y * (e : G)⁻¹)) * ((e : G) * (y⁻¹ * x) * (e : G)⁻¹) := by group
        _ = w * ((e : G) * (y⁻¹ * x) * (e : G)⁻¹) := by rw [hyw]; group
    rw [h1]
    exact W.mul_mem hw ((Subgroup.mem_normalizer_iff.mp (hEW e.2) _).mp hx)
  let S : Type := {x : G // y⁻¹ * x ∈ W}
  let _inst : MulAction E S :=
    { smul := fun e s => ⟨(e : G) * s.1 * (e : G)⁻¹, hconj e s.1 s.2⟩
      one_smul := fun s => by
        apply Subtype.ext
        change ((1 : E) : G) * s.1 * ((1 : E) : G)⁻¹ = s.1
        simp
      mul_smul := fun a b s => by
        apply Subtype.ext
        change ((a * b : E) : G) * s.1 * ((a * b : E) : G)⁻¹ =
          (a : G) * ((b : G) * s.1 * (b : G)⁻¹) * (a : G)⁻¹
        simp [mul_assoc] }
  have hcard : Nat.card S = Nat.card W :=
    Nat.card_congr
      { toFun := fun s => ⟨y⁻¹ * s.1, s.2⟩
        invFun := fun w => ⟨y * w.1, by simp⟩
        left_inv := fun s => Subtype.ext (by simp)
        right_inv := fun w => Subtype.ext (by simp) }
  have hnd : ¬ 5 ∣ Nat.card S := by
    rw [hcard]
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hW
    rw [hn]
    intro h
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_five h
    omega
  obtain ⟨s, hs⟩ := hE.nonempty_fixed_point_of_prime_not_dvd_card S hnd
  refine ⟨y⁻¹ * s.1, s.2, fun e he => ?_⟩
  have h2 := congrArg Subtype.val (MulAction.mem_fixedPoints.mp hs ⟨e, he⟩)
  change e * s.1 * e⁻¹ = s.1 at h2
  simpa using h2

theorem exists_five_part_of_coprime {Z : Subgroup G} {x : G} (hx5 : x ^ 5 ∈ Z) (hxZ : x ∉ Z)
    (hcop : Nat.Coprime (orderOf (x ^ 5)) 5) :
    ∃ n : ℕ, orderOf (x ^ n) = 5 ∧ x ^ n * x⁻¹ ∈ Z := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨n, hn5, hn0⟩ := Nat.chineseRemainder hcop.symm 1 0
  have hdecomp : x ^ n = (x ^ 5) ^ (n / 5) * x := by
    have hn : n = 5 * (n / 5) + 1 := by
      have h1 : n % 5 = 1 := hn5
      omega
    conv_lhs => rw [hn]
    rw [pow_add, pow_mul, pow_one]
  have hpow : (x ^ n) ^ 5 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]
    exact orderOf_dvd_iff_pow_eq_one.mp (Nat.modEq_zero_iff_dvd.mp hn0)
  have hne : x ^ n ≠ 1 := by
    intro h1
    apply hxZ
    rw [hdecomp] at h1
    rw [eq_inv_of_mul_eq_one_right h1]
    exact Z.inv_mem (Z.pow_mem hx5 _)
  refine ⟨n, orderOf_eq_prime hpow hne, ?_⟩
  rw [hdecomp, mul_inv_cancel_right]
  exact Z.pow_mem hx5 _

theorem exists_five_part {W : Subgroup G} (hW : IsPGroup 2 W) {x : G} (hx5 : x ^ 5 ∈ W)
    (hxW : x ∉ W) : ∃ n : ℕ, orderOf (x ^ n) = 5 ∧ x ^ n * x⁻¹ ∈ W := by
  refine exists_five_part_of_coprime hx5 hxW ?_
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hW ⟨x ^ 5, hx5⟩
  have h2 : orderOf (x ^ 5) = 2 ^ k := by
    rw [← hk]
    exact Subgroup.orderOf_coe (⟨x ^ 5, hx5⟩ : W)
  rw [h2]
  exact Nat.Coprime.pow_left k (by norm_num)

theorem pCoreOf_le_cMod (J : Subgroup G) : pCoreOf 2 J ≤ cMod J := by
  intro w hw
  refine ⟨Subgroup.le_normalizer (pCoreOf_le 2 J hw), fun x hx => ?_⟩
  have h1 : x * w * x⁻¹ ∈ pCoreOf 2 J :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 J hx) w).mp hw
  have h2 : ⁅x, w⁆ = (x * w * x⁻¹) * w⁻¹ := rfl
  rw [h2]
  exact mul_mem h1 (inv_mem hw)

theorem exists_five_of_mem_innerSub [Finite G] {J : Subgroup G}
    (h5Z : ∀ z ∈ J, z ∈ cMod J → orderOf z ≠ 5) {k : G} (hk5 : orderOf k = 5)
    (hk : k ∈ innerSub J) (hknc : k ∉ cMod J) :
    ∃ a ∈ J, orderOf a = 5 ∧ a⁻¹ * k ∈ cMod J := by
  obtain ⟨j, hj, c, hc, rfl⟩ := mem_innerSub_iff.mp hk
  have hjN : j ∈ Subgroup.normalizer (cMod J : Set G) :=
    normalizer_le_normalizer_cMod J (Subgroup.le_normalizer hj)
  obtain ⟨c', hc', h⟩ := exists_pow_mul_eq hjN hc 5
  have h1 : (j * c) ^ 5 = 1 := by
    have := pow_orderOf_eq_one (j * c)
    rwa [hk5] at this
  rw [h1] at h
  have hj5 : j ^ 5 ∈ cMod J := by
    rw [eq_inv_of_mul_eq_one_left h.symm]
    exact inv_mem hc'
  have hjnc : j ∉ cMod J := fun hjc => hknc (mul_mem hjc hc)
  have hcop : Nat.Coprime (orderOf (j ^ 5)) 5 := by
    refine ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).mpr fun hd => ?_).symm
    exact h5Z _ (pow_mem (pow_mem hj 5) _) (pow_mem hj5 _)
      (orderOf_pow_orderOf_div (orderOf_pos _).ne' hd)
  obtain ⟨n, hn5, hna⟩ := exists_five_part_of_coprime hj5 hjnc hcop
  refine ⟨j ^ n, pow_mem hj n, hn5, ?_⟩
  have h2 : (j ^ n)⁻¹ * (j * c) = (j ^ n * j⁻¹)⁻¹ * c := by
    group
  rw [h2]
  exact mul_mem (inv_mem hna) hc

def cosetStab (J : Subgroup G) (a : G) : Subgroup G where
  carrier := {s | s ∈ Subgroup.normalizer (J : Set G) ∧ a⁻¹ * (s * a * s⁻¹) ∈ pCoreOf 2 J}
  one_mem' := ⟨one_mem _, by simp⟩
  mul_mem' := by
    rintro s t ⟨hs, hs'⟩ ⟨ht, ht'⟩
    refine ⟨mul_mem hs ht, ?_⟩
    have h1 := conj_mem_pCoreOf hs ht'
    have h2 : a⁻¹ * (s * t * a * (s * t)⁻¹) =
        (a⁻¹ * (s * a * s⁻¹)) * (s * (a⁻¹ * (t * a * t⁻¹)) * s⁻¹) := by
      group
    rw [h2]
    exact mul_mem hs' h1
  inv_mem' := by
    rintro s ⟨hs, hs'⟩
    refine ⟨inv_mem hs, ?_⟩
    have h1 := conj_mem_pCoreOf (inv_mem hs) hs'
    have h2 : a⁻¹ * (s⁻¹ * a * s⁻¹⁻¹) = (s⁻¹ * (a⁻¹ * (s * a * s⁻¹)) * s⁻¹⁻¹)⁻¹ := by
      group
    rw [h2]
    exact inv_mem h1

theorem self_mem_cosetStab {J : Subgroup G} {a : G} (ha : a ∈ J) : a ∈ cosetStab J a := by
  refine ⟨Subgroup.le_normalizer ha, ?_⟩
  have : a⁻¹ * (a * a * a⁻¹) = 1 := by group
  rw [this]
  exact one_mem _

theorem cMod_le_cosetStab {J : Subgroup G} {a : G} (ha : a ∈ J) : cMod J ≤ cosetStab J a := by
  intro c hc
  refine ⟨hc.1, ?_⟩
  have : a⁻¹ * (c * a * c⁻¹) = ⁅a⁻¹, c⁆ := by
    simp only [commutatorElement_def]
    group
  rw [this]
  exact hc.2 a⁻¹ (inv_mem ha)

theorem exists_five_fixing [Finite G] {J S : Subgroup G} (hS : IsPGroup 5 S) {a : G} (haJ : a ∈ J)
    (ha5 : orderOf a = 5) (hanc : a ∉ cMod J) (hSa : S ≤ cosetStab J a) :
    ∃ b ∈ J, orderOf b = 5 ∧ a⁻¹ * b ∈ pCoreOf 2 J ∧ ∀ s ∈ S, Commute s b := by
  have hW2 : IsPGroup 2 (pCoreOf 2 J) := pCoreOf_isPGroup 2 J
  have haN : a ∈ Subgroup.normalizer (pCoreOf 2 J : Set G) := le_normalizer_pCoreOf 2 J haJ
  obtain ⟨w, hwW, hfix⟩ := exists_fixed_mem_coset (E := S) (W := pCoreOf 2 J) hS hW2
    (fun s hs => normalizer_le_normalizer_pCoreOf 2 J (hSa hs).1) (y := a)
    (fun s hs => ⟨a⁻¹ * (s * a * s⁻¹), (hSa hs).2, by group⟩)
  have ha₁J : a * w ∈ J := J.mul_mem haJ (pCoreOf_le 2 J hwW)
  have ha₁5 : (a * w) ^ 5 ∈ pCoreOf 2 J := by
    obtain ⟨w', hw', h⟩ := exists_pow_mul_eq haN hwW 5
    have h5 : a ^ 5 = 1 := ha5 ▸ pow_orderOf_eq_one a
    rw [h, h5, one_mul]
    exact hw'
  have ha₁W : a * w ∉ pCoreOf 2 J := by
    intro h
    apply hanc
    have : a = (a * w) * w⁻¹ := by group
    rw [this]
    exact mul_mem (pCoreOf_le_cMod J h) (inv_mem (pCoreOf_le_cMod J hwW))
  obtain ⟨n, hn5, hnW⟩ := exists_five_part hW2 ha₁5 ha₁W
  refine ⟨(a * w) ^ n, pow_mem ha₁J n, hn5, ?_, fun s hs => ?_⟩
  · have h1 := conj_mem_pCoreOf (Subgroup.le_normalizer (J.inv_mem haJ)) hnW
    generalize (a * w) ^ n = b at h1 ⊢
    have h2 : a⁻¹ * b = (a⁻¹ * (b * (a * w)⁻¹) * a⁻¹⁻¹) * w := by group
    rw [h2]
    exact mul_mem h1 hwW
  · have h1 : s * (a * w) = (a * w) * s := mul_inv_eq_iff_eq_mul.mp (hfix s hs)
    exact Commute.pow_right h1 n

theorem isElemAbelian_zpowers_sup [Finite G] {k₁ k₂ : G} (hk₁ : orderOf k₁ = 5)
    (hk₂ : orderOf k₂ = 5) (hcomm : k₁ * k₂ = k₂ * k₁)
    (hind : Subgroup.zpowers k₁ ⊓ Subgroup.zpowers k₂ = ⊥) :
    IsElemAbelian 5 (Subgroup.zpowers k₁ ⊔ Subgroup.zpowers k₂) ∧
      Nat.card ↥(Subgroup.zpowers k₁ ⊔ Subgroup.zpowers k₂) = 25 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hE1 : IsElemAbelian 5 (Subgroup.zpowers k₁) := by
    refine ⟨inferInstance, fun x hx => ?_⟩
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have h5 : k₁ ^ 5 = 1 := hk₁ ▸ pow_orderOf_eq_one k₁
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h5, one_zpow]
  have hk₂E : k₂ ∉ Subgroup.zpowers k₁ := by
    intro h
    have h1 : k₂ ∈ Subgroup.zpowers k₁ ⊓ Subgroup.zpowers k₂ := ⟨h, Subgroup.mem_zpowers k₂⟩
    rw [hind, Subgroup.mem_bot] at h1
    rw [h1, orderOf_one] at hk₂
    omega
  obtain ⟨hA, hAcard⟩ := exists_elemAbelian_sup_zpowers hE1 hk₂
    (fun e he => by
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp he
      exact Commute.zpow_left hcomm m) hk₂E
  refine ⟨hA, ?_⟩
  rw [hAcard, Nat.card_zpowers, hk₁]

theorem exists_diag_mem [Finite G] {X J : Subgroup G} (hX : CFSG.Open.pRank 5 X ≤ 2) (hJX : J ≤ X)
    {k₁ k₂ : G} (hk₁X : k₁ ∈ X) (hk₂X : k₂ ∈ X) (hk₁ : orderOf k₁ = 5) (hk₂ : orderOf k₂ = 5)
    (hcomm : k₁ * k₂ = k₂ * k₁) (hind : Subgroup.zpowers k₁ ⊓ Subgroup.zpowers k₂ = ⊥)
    (hk₂c : k₂ ∈ cMod J) (hk₁in : k₁ ∈ innerSub J) (hk₁nc : k₁ ∉ cMod J)
    (h5Z : ∀ z ∈ J, z ∈ cMod J → orderOf z ≠ 5) : ∃ l : ℕ, k₁ * k₂ ^ l ∈ J := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨a₀, ha₀J, ha₀5, ha₀k⟩ := exists_five_of_mem_innerSub h5Z hk₁ hk₁in hk₁nc
  have ha₀nc : a₀ ∉ cMod J := fun h => hk₁nc (by simpa using mul_mem h ha₀k)
  obtain ⟨hSab, hScard⟩ := isElemAbelian_zpowers_sup hk₁ hk₂ hcomm hind
  have hk₁S : k₁ ∈ cosetStab J a₀ := by
    have h := mul_mem (self_mem_cosetStab ha₀J) (cMod_le_cosetStab ha₀J ha₀k)
    simpa using h
  have hk₂S : k₂ ∈ cosetStab J a₀ := cMod_le_cosetStab ha₀J hk₂c
  have hSle : Subgroup.zpowers k₁ ⊔ Subgroup.zpowers k₂ ≤ cosetStab J a₀ :=
    sup_le (Subgroup.zpowers_le.mpr hk₁S) (Subgroup.zpowers_le.mpr hk₂S)
  obtain ⟨a₂, ha₂J, ha₂5, ha₂W, ha₂c⟩ :=
    exists_five_fixing (isPGroup_of_isElemAbelian hSab) ha₀J ha₀5 ha₀nc hSle
  have ha₂S : a₂ ∈ Subgroup.zpowers k₁ ⊔ Subgroup.zpowers k₂ := by
    by_contra hna
    obtain ⟨hA, hAcard⟩ := exists_elemAbelian_sup_zpowers hSab ha₂5 ha₂c hna
    have hAX : (Subgroup.zpowers k₁ ⊔ Subgroup.zpowers k₂) ⊔ Subgroup.zpowers a₂ ≤ X :=
      sup_le (sup_le (Subgroup.zpowers_le.mpr hk₁X) (Subgroup.zpowers_le.mpr hk₂X))
        (Subgroup.zpowers_le.mpr (hJX ha₂J))
    have h3 := CFSG.Quasithin.le_pRank Nat.prime_five hAX hA (k := 3)
      (by rw [hAcard, hScard]; norm_num)
    omega
  have hnorm : Subgroup.zpowers k₁ ≤ Subgroup.normalizer (Subgroup.zpowers k₂ : Set G) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    refine Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr fun g hg => ?_)
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    exact Commute.zpow_left (show Commute k₂ k₁ from hcomm.symm) j
  have hmem : a₂ ∈ ((Subgroup.zpowers k₁ ⊔ Subgroup.zpowers k₂ : Subgroup G) : Set G) := ha₂S
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnorm] at hmem
  obtain ⟨u, hu, v, hv, huv⟩ := Set.mem_mul.mp hmem
  have hvc : v ∈ cMod J := (Subgroup.zpowers_le.mpr hk₂c) hv
  have h1 : a₂⁻¹ * k₁ ∈ cMod J := by
    have h2 : a₂⁻¹ * k₁ = (a₀⁻¹ * a₂)⁻¹ * (a₀⁻¹ * k₁) := by group
    rw [h2]
    exact mul_mem (inv_mem (pCoreOf_le_cMod J ha₂W)) ha₀k
  have h3 : u⁻¹ * k₁ ∈ cMod J := by
    have h4 : u⁻¹ * k₁ = v * (a₂⁻¹ * k₁) := by rw [← huv]; group
    rw [h4]
    exact mul_mem hvc h1
  have h5 : u⁻¹ * k₁ ∈ Subgroup.zpowers k₁ := mul_mem (inv_mem hu) (Subgroup.mem_zpowers k₁)
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp h5
  have h6 : u⁻¹ * k₁ = 1 := by
    rw [← hm]
    exact SBc13.zpow_mem_eq_one_of_prime_order hk₁ hk₁nc (hm ▸ h3)
  have hu1 : u = k₁ := inv_mul_eq_one.mp h6
  obtain ⟨l, hl⟩ := Submonoid.mem_powers_iff _ _ |>.mp (mem_powers_iff_mem_zpowers.mpr hv)
  refine ⟨l, ?_⟩
  rw [hl, ← hu1, huv]
  exact ha₂J

end SBc17

end CFSG.Quasithin
