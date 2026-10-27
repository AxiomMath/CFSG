module

public import CFSG.RankThree.PartTwo.Sec21.Item211ProofList
public import CFSG.RankThree.PartTwo.Sec21.Item211ProofQuot

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open scoped Pointwise commutatorElement

namespace Item211Proof

section Abstract

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem isElemAbelian_sup_zpowers {A : Subgroup X} (hA : IsElemAbelian 3 A) {u : X}
    (hu3 : u ^ 3 = 1) (hc : ∀ a ∈ A, a * u = u * a) :
    IsElemAbelian 3 (A ⊔ Subgroup.zpowers u) := by
  have hN : Subgroup.zpowers u ≤ Subgroup.normalizer (A : Set X) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      rw [← hc a ha, mul_inv_cancel_right]
      exact ha
    · intro ha
      have hyu : (u * a * u⁻¹) * u = u * (u * a * u⁻¹) := hc _ ha
      have h1 : a = u * a * u⁻¹ := by
        calc a = u⁻¹ * ((u * a * u⁻¹) * u) := by group
          _ = u⁻¹ * (u * (u * a * u⁻¹)) := by rw [hyu]
          _ = u * a * u⁻¹ := by group
      rw [h1]
      exact ha
  have hset := Subgroup.coe_mul_of_right_le_normalizer_left A (Subgroup.zpowers u) hN
  have key : ∀ x ∈ A ⊔ Subgroup.zpowers u, ∃ a ∈ A, ∃ k : ℤ, x = a * u ^ k := by
    intro x hx
    have hx' : x ∈ ((A ⊔ Subgroup.zpowers u : Subgroup X) : Set X) := hx
    rw [hset] at hx'
    obtain ⟨a, ha, y, ⟨k, rfl⟩, rfl⟩ := hx'
    exact ⟨a, ha, k, rfl⟩
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨a, ha, k, hx⟩ := key x x.2
    obtain ⟨b, hb, l, hy⟩ := key y y.2
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [hx, hy]
    have hab : Commute a b := hcomm a ha b hb
    have hau : Commute a (u ^ l) := Commute.zpow_right (hc a ha) l
    have hub : Commute (u ^ k) b := Commute.zpow_left (hc b hb).symm k
    have huu : Commute (u ^ k) (u ^ l) := Commute.zpow_zpow_self u k l
    exact (Commute.mul_left (Commute.mul_right hab hau) (Commute.mul_right hub huu)).eq
  · obtain ⟨a, ha, k, rfl⟩ := key x hx
    have h1 : Commute a (u ^ k) := Commute.zpow_right (hc a ha) k
    rw [h1.mul_pow, hA.2 a ha, one_mul, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, hu3, one_zpow]

theorem three_mul_card_le_of_lt {K K' : Subgroup X} (hK' : IsPGroup 3 K') (hle : K ≤ K')
    (hne : K ≠ K') : 3 * Nat.card K ≤ Nat.card K' := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hle
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hK'
  have hm1 : m ≠ 1 := by
    rintro rfl
    exact hne (Subgroup.eq_of_le_of_card_ge hle (by rw [hm, mul_one]))
  have hmd : m ∣ 3 ^ n := hn ▸ (Dvd.intro_left _ hm.symm)
  obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hmd
  have hj : j ≠ 0 := by
    rintro rfl
    exact hm1 rfl
  have h3 : 3 ≤ 3 ^ j := Nat.le_self_pow hj 3
  rw [hm]
  nlinarith [Nat.card_pos (α := K)]

omit [Finite X] in
theorem card_sup_mul_card_inf_of_normal' (A L : Subgroup X) [L.Normal] :
    Nat.card (A ⊔ L : Subgroup X) * Nat.card (A ⊓ L : Subgroup X) = Nat.card A * Nat.card L := by
  have h1 := Subgroup.relIndex_mul_card (H := L) (K := A ⊔ L)
  have h2 := Subgroup.relIndex_mul_card (H := L) (K := A)
  rw [Subgroup.relIndex_sup_right, inf_of_le_left (le_sup_right : L ≤ A ⊔ L)] at h1
  rw [inf_comm] at h2
  rw [← h1, ← h2]
  ring

theorem autIn_heis {U L₁ A₁ : Subgroup X} (hUL : U ⊔ L₁ = ⊤)
    (hcomm : ∀ u ∈ U, ∀ v ∈ L₁, u * v = v * u) (hU : Sec4.IsHeisThree U)
    (hZ3 : Nat.card (U ⊓ L₁ : Subgroup X) = 3) (hLn : L₁.Normal)
    (hAe : IsElemAbelian 3 A₁)
    (hAmax : ∀ B : Subgroup X, IsElemAbelian 3 B → A₁ ≤ B → B ≤ A₁)
    (hA27 : Nat.card A₁ = 27)
    (hAC : Nat.card (A₁ ⊓ Subgroup.centralizer (L₁ : Set X) : Subgroup X) = 3) :
    IsElemAbelian 3 (Sec4.autIn L₁ A₁) ∧ Nat.card (Sec4.autIn L₁ A₁) = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Z : Subgroup X := U ⊓ L₁ with hZdef
  have hU27 : Nat.card U = 27 := hU.2.1
  have hUp : IsPGroup 3 U := IsPGroup.of_card (n := 3) (by rw [hU27]; norm_num)
  have hU3 : ∀ u ∈ U, u ^ 3 = 1 := by
    intro x hx
    have h1 := Monoid.pow_exponent_eq_one (⟨x, hx⟩ : U)
    rw [hU.2.2] at h1
    simpa using congrArg Subtype.val h1
  have hUN : U ≤ Subgroup.normalizer (L₁ : Set X) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hLn]
    exact le_top
  have hdec : ∀ x : X, ∃ u ∈ U, ∃ v ∈ L₁, x = u * v := by
    intro x
    have hx : x ∈ ((U ⊔ L₁ : Subgroup X) : Set X) := by rw [hUL]; trivial
    rw [Subgroup.coe_mul_of_left_le_normalizer_right U L₁ hUN] at hx
    obtain ⟨u, hu, v, hv, rfl⟩ := hx
    exact ⟨u, hu, v, hv, rfl⟩
  have hZc : ∀ z ∈ Z, ∀ x : X, z * x = x * z := by
    intro z hz x
    obtain ⟨u, hu, v, hv, rfl⟩ := hdec x
    have h1 : z * u = u * z := (hcomm u hu z hz.2).symm
    have h2 : z * v = v * z := hcomm z hz.1 v hv
    calc z * (u * v) = u * (z * v) := by rw [← mul_assoc, h1, mul_assoc]
      _ = u * v * z := by rw [h2, mul_assoc]
  have hmaxu : ∀ u : X, u ^ 3 = 1 → (∀ a ∈ A₁, a * u = u * a) → u ∈ A₁ := fun u hu3 hc =>
    hAmax _ (isElemAbelian_sup_zpowers hAe hu3 hc) le_sup_left
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers u))
  have hAcomm : ∀ a ∈ A₁, ∀ b ∈ A₁, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hZA : Z ≤ A₁ := fun z hz => hmaxu z (hU3 z hz.1) (fun a _ => (hZc z hz a).symm)
  have hAU : A₁ ⊓ U = Z := by
    have hle1 : Z ≤ A₁ ⊓ U := le_inf hZA inf_le_left
    have hle2 : A₁ ⊓ U ≤ A₁ ⊓ Subgroup.centralizer (L₁ : Set X) :=
      inf_le_inf_left _ fun u hu =>
        Subgroup.mem_centralizer_iff.mpr fun v hv => (hcomm u hu v hv).symm
    have h1 := Subgroup.card_le_of_le hle2
    exact (Subgroup.eq_of_le_of_card_ge hle1 (by rw [hZ3]; omega)).symm
  set S : Subgroup X := U ⊓ (A₁ ⊔ L₁) with hSdef
  have hSdec : ∀ a ∈ A₁, ∃ s ∈ S, ∃ v ∈ L₁, a = s * v := by
    intro a ha
    obtain ⟨u, hu, v, hv, rfl⟩ := hdec a
    refine ⟨u, ⟨hu, ?_⟩, v, hv, rfl⟩
    have : u = u * v * v⁻¹ := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right (L₁.inv_mem hv))
  have hSL : S ⊓ L₁ = Z := by
    ext x
    constructor
    · rintro ⟨⟨hxU, -⟩, hxL⟩
      exact ⟨hxU, hxL⟩
    · rintro ⟨hxU, hxL⟩
      exact ⟨⟨hxU, Subgroup.mem_sup_right hxL⟩, hxL⟩
  have hSsup : S ⊔ L₁ = A₁ ⊔ L₁ := by
    refine le_antisymm (sup_le inf_le_right le_sup_right) (sup_le (fun a ha => ?_) le_sup_right)
    obtain ⟨s, hs, v, hv, rfl⟩ := hSdec a ha
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hs) (Subgroup.mem_sup_right hv)
  have hcardS : Nat.card S * Nat.card (A₁ ⊓ L₁ : Subgroup X) = 81 := by
    have h1 := card_sup_mul_card_inf_of_normal' S L₁
    have h2 := card_sup_mul_card_inf_of_normal' A₁ L₁
    rw [hSsup, hSL, hZ3] at h1
    rw [hA27] at h2
    have hLpos : 0 < Nat.card L₁ := Nat.card_pos
    have h3 : Nat.card S * Nat.card (A₁ ⊓ L₁ : Subgroup X) * Nat.card L₁ = 81 * Nat.card L₁ := by
      calc Nat.card S * Nat.card (A₁ ⊓ L₁ : Subgroup X) * Nat.card L₁
          = (Nat.card S * Nat.card L₁) * Nat.card (A₁ ⊓ L₁ : Subgroup X) := by ring
        _ = (Nat.card (A₁ ⊔ L₁ : Subgroup X) * 3) * Nat.card (A₁ ⊓ L₁ : Subgroup X) := by rw [h1]
        _ = 3 * (Nat.card (A₁ ⊔ L₁ : Subgroup X) * Nat.card (A₁ ⊓ L₁ : Subgroup X)) := by ring
        _ = 81 * Nat.card L₁ := by rw [h2]; ring
    exact Nat.eq_of_mul_eq_mul_right hLpos h3
  have hSnc : ¬ ∀ s ∈ S, ∀ t ∈ S, s * t = t * s := by
    intro hab
    set CU : Subgroup X := U ⊓ Subgroup.centralizer (S : Set X) with hCU
    have hSCU : S ≤ CU := fun s hs =>
      ⟨hs.1, Subgroup.mem_centralizer_iff.mpr fun t ht => hab t ht s hs⟩
    have hZS : Z ≤ S := by rw [← hSL]; exact inf_le_left
    have h9 : 9 ≤ Nat.card CU := by
      by_cases hSZ : S ≤ Z
      · have hUCU : U ≤ CU := fun u hu =>
          ⟨hu, Subgroup.mem_centralizer_iff.mpr fun s hs => hZc s (hSZ hs) u⟩
        have := Subgroup.card_le_of_le hUCU
        omega
      · have hne : Z ≠ S := fun h => hSZ (h ▸ le_rfl)
        have h1 : 3 * Nat.card Z ≤ Nat.card S :=
          three_mul_card_le_of_lt (hUp.to_le inf_le_left) hZS hne
        have h2 := Subgroup.card_le_of_le hSCU
        rw [hZ3] at h1
        omega
    obtain ⟨u, hu, huA⟩ : ∃ u ∈ CU, u ∉ A₁ := by
      by_contra hcon
      push Not at hcon
      have hle : CU ≤ A₁ ⊓ U := fun u hu => ⟨hcon u hu, hu.1⟩
      have := Subgroup.card_le_of_le hle
      rw [hAU, hZ3] at this
      omega
    apply huA
    refine hmaxu u (hU3 u hu.1) fun a ha => ?_
    obtain ⟨s, hs, v, hv, rfl⟩ := hSdec a ha
    have h1 : s * u = u * s := Subgroup.mem_centralizer_iff.mp hu.2 s hs
    have h2 : v * u = u * v := (hcomm u hu.1 v hv).symm
    calc s * v * u = s * (u * v) := by rw [mul_assoc, h2]
      _ = u * (s * v) := by rw [← mul_assoc, h1, mul_assoc]
  have hSU : S = U := by
    by_contra hne
    apply hSnc
    have hSle : S ≤ U := inf_le_left
    have h1 := three_mul_card_le_of_lt hUp hSle hne
    have hSp : IsPGroup 3 S := hUp.to_le hSle
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hSp
    have hk2 : k ≤ 2 := by
      by_contra hk2
      have : 3 ^ 3 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hcomm' : IsMulCommutative S := by
      interval_cases k
      · have : Subsingleton S := Finite.card_le_one_iff_subsingleton.mp (by rw [hk]; norm_num)
        exact ⟨⟨fun a b => Subsingleton.elim _ _⟩⟩
      · have := isCyclic_of_prime_card (p := 3) (by rw [hk, pow_one])
        exact IsCyclic.isMulCommutative
      · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq hk
    intro s hs t ht
    exact congrArg Subtype.val (hcomm'.is_comm.comm ⟨s, hs⟩ ⟨t, ht⟩)
  have hAL : A₁ ⊓ L₁ = Z := by
    have h1 : Nat.card (A₁ ⊓ L₁ : Subgroup X) = 3 := by
      rw [hSU, hU27] at hcardS
      omega
    exact (Subgroup.eq_of_le_of_card_ge (le_inf hZA inf_le_right) (by rw [h1, hZ3])).symm
  obtain ⟨s₁, hs₁, s₂, hs₂, hs₁₂⟩ : ∃ s₁ ∈ S, ∃ s₂ ∈ S, s₁ * s₂ ≠ s₂ * s₁ := by
    by_contra h
    push Not at h
    exact hSnc h
  have hAN : L₁ ≤ Subgroup.normalizer (L₁ : Set X) := Subgroup.le_normalizer
  have hset : ((A₁ ⊔ L₁ : Subgroup X) : Set X) = (A₁ : Set X) * (L₁ : Set X) :=
    Subgroup.coe_mul_of_left_le_normalizer_right A₁ L₁
      (by rw [Subgroup.normalizer_eq_top_iff.mpr hLn]; exact le_top)
  have hlift : ∀ s ∈ S, ∃ v ∈ L₁, s * v ∈ A₁ := by
    intro s hs
    have h1 : s ∈ ((A₁ ⊔ L₁ : Subgroup X) : Set X) := hs.2
    rw [hset] at h1
    obtain ⟨a, ha, w, hw, hsaw⟩ := h1
    refine ⟨w⁻¹, L₁.inv_mem hw, ?_⟩
    rw [← hsaw]
    simpa using ha
  obtain ⟨v₁, hv₁, ha₁⟩ := hlift s₁ hs₁
  obtain ⟨v₂, hv₂, ha₂⟩ := hlift s₂ hs₂
  have hs₁U : s₁ ∈ U := hs₁.1
  have hs₂U : s₂ ∈ U := hs₂.1
  have hkey : ∀ s ∈ U, ∀ v ∈ L₁, s * v ∈ A₁ → ∀ t ∈ U, ∀ w ∈ L₁, t * w ∈ A₁ →
      t⁻¹ * s⁻¹ * t * s ∈ Z ∧ v * (t * w) * v⁻¹ = (t⁻¹ * s⁻¹ * t * s) * (t * w) := by
    intro s hs v hv hsv t ht w hw htw
    have hab := hAcomm _ hsv _ htw
    have hvt : v * t = t * v := (hcomm t ht v hv).symm
    have hws : w * s = s * w := (hcomm s hs w hw).symm
    have e1 : s * t * (v * w) = t * s * (w * v) := by
      calc s * t * (v * w) = s * (t * v) * w := by group
        _ = s * (v * t) * w := by rw [hvt]
        _ = (s * v) * (t * w) := by group
        _ = (t * w) * (s * v) := hab
        _ = t * (w * s) * v := by group
        _ = t * (s * w) * v := by rw [hws]
        _ = t * s * (w * v) := by group
    have e2 : t⁻¹ * s⁻¹ * t * s = v * w * v⁻¹ * w⁻¹ := by
      have : (t * s)⁻¹ * (s * t) = (w * v) * (v * w)⁻¹ := by
        calc (t * s)⁻¹ * (s * t) = (t * s)⁻¹ * (s * t * (v * w)) * (v * w)⁻¹ := by group
          _ = (t * s)⁻¹ * (t * s * (w * v)) * (v * w)⁻¹ := by rw [e1]
          _ = (w * v) * (v * w)⁻¹ := by group
      calc t⁻¹ * s⁻¹ * t * s = ((t * s)⁻¹ * (s * t))⁻¹ := by group
        _ = ((w * v) * (v * w)⁻¹)⁻¹ := by rw [this]
        _ = v * w * v⁻¹ * w⁻¹ := by group
    have hκU : t⁻¹ * s⁻¹ * t * s ∈ U :=
      U.mul_mem (U.mul_mem (U.mul_mem (U.inv_mem ht) (U.inv_mem hs)) ht) hs
    have hκL : t⁻¹ * s⁻¹ * t * s ∈ L₁ := by
      rw [e2]
      exact L₁.mul_mem (L₁.mul_mem (L₁.mul_mem hv hw) (L₁.inv_mem hv)) (L₁.inv_mem hw)
    refine ⟨⟨hκU, hκL⟩, ?_⟩
    have hκc := hZc _ ⟨hκU, hκL⟩ t
    calc v * (t * w) * v⁻¹ = t * (v * w * v⁻¹ * w⁻¹) * w := by
          calc v * (t * w) * v⁻¹ = (v * t) * w * v⁻¹ := by group
            _ = (t * v) * w * v⁻¹ := by rw [hvt]
            _ = t * (v * w * v⁻¹ * w⁻¹) * w := by group
      _ = t * (t⁻¹ * s⁻¹ * t * s) * w := by rw [e2]
      _ = (t⁻¹ * s⁻¹ * t * s) * t * w := by rw [← hκc]
      _ = (t⁻¹ * s⁻¹ * t * s) * (t * w) := by group
  have hvN : ∀ s ∈ U, ∀ v ∈ L₁, s * v ∈ A₁ → v ∈ Subgroup.normalizer (A₁ : Set X) := by
    intro s hs v hv hsv
    refine Subgroup.mem_normalizer_fintype fun b hb => ?_
    obtain ⟨t, ht, w, hw, rfl⟩ := hdec b
    obtain ⟨hκ, heq⟩ := hkey s hs v hv hsv t ht w hw hb
    rw [heq]
    exact A₁.mul_mem (hZA hκ) hb
  have hσ : ∀ σ ∈ Sec4.autIn L₁ A₁, (∀ a : A₁, ((a⁻¹ * σ a : A₁) : X) ∈ Z) ∧
      ∀ z : A₁, (z : X) ∈ Z → σ z = z := by
    intro σ hσ
    obtain ⟨n, hnN, hnL, rfl⟩ := Sec4.mem_autIn_iff.mp hσ
    refine ⟨fun a => ?_, fun z hz => Subtype.ext ?_⟩
    · rw [← hAL]
      refine ⟨SetLike.coe_mem _, ?_⟩
      change (a : X)⁻¹ * (n * a * n⁻¹) ∈ L₁
      have h1 : (a : X)⁻¹ * n * a ∈ L₁ := by
        have := hLn.conj_mem n hnL (a : X)⁻¹
        simpa using this
      have : (a : X)⁻¹ * (n * a * n⁻¹) = (a : X)⁻¹ * n * a * n⁻¹ := by group
      rw [this]
      exact L₁.mul_mem h1 (L₁.inv_mem hnL)
    · rw [Sec4.normalizerMonoidHom_apply_coe, ← hZc _ hz n, mul_inv_cancel_right]
  set ZA : Subgroup A₁ := Z.subgroupOf A₁ with hZA_def
  have hZAcard : Nat.card ZA = 3 := by
    rw [hZA_def, ← Subgroup.card_map_of_injective A₁.subtype_injective,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hZA, hZ3]
  set b₁ : A₁ := ⟨s₁ * v₁, ha₁⟩ with hb₁
  set b₂ : A₁ := ⟨s₂ * v₂, ha₂⟩ with hb₂
  have hmemZA : ∀ σ ∈ Sec4.autIn L₁ A₁, ∀ a : A₁, a⁻¹ * σ a ∈ ZA := fun σ hσ' a =>
    Subgroup.mem_subgroupOf.mpr ((hσ σ hσ').1 a)
  let φ : Sec4.autIn L₁ A₁ →* ZA × ZA :=
    { toFun := fun σ => (⟨b₁⁻¹ * σ.1 b₁, hmemZA σ.1 σ.2 b₁⟩, ⟨b₂⁻¹ * σ.1 b₂, hmemZA σ.1 σ.2 b₂⟩)
      map_one' := by
        ext <;> simp
      map_mul' := fun σ τ => by
        have hfix : ∀ b : A₁, σ.1 (b * (b⁻¹ * τ.1 b)) = σ.1 b * (b⁻¹ * τ.1 b) := fun b => by
          rw [map_mul, (hσ σ.1 σ.2).2 _ ((hσ τ.1 τ.2).1 b)]
        ext
        · change ((b₁⁻¹ * σ.1 (τ.1 b₁) : A₁) : X) = ((b₁⁻¹ * σ.1 b₁ * (b₁⁻¹ * τ.1 b₁) : A₁) : X)
          have : τ.1 b₁ = b₁ * (b₁⁻¹ * τ.1 b₁) := by group
          rw [this, hfix b₁]
          congr 1
          group
        · change ((b₂⁻¹ * σ.1 (τ.1 b₂) : A₁) : X) = ((b₂⁻¹ * σ.1 b₂ * (b₂⁻¹ * τ.1 b₂) : A₁) : X)
          have : τ.1 b₂ = b₂ * (b₂⁻¹ * τ.1 b₂) := by group
          rw [this, hfix b₂]
          congr 1
          group }
  have hφ : ∀ σ : Sec4.autIn L₁ A₁, φ σ =
      (⟨b₁⁻¹ * σ.1 b₁, hmemZA σ.1 σ.2 b₁⟩, ⟨b₂⁻¹ * σ.1 b₂, hmemZA σ.1 σ.2 b₂⟩) := fun _ => rfl
  have hb₁Z : (b₁ : X) ∉ Z := by
    intro hb
    apply hs₁₂
    have hv₁Z : v₁ ∈ Z := by
      have : v₁ = s₁⁻¹ * (s₁ * v₁) := by group
      exact ⟨this ▸ U.mul_mem (U.inv_mem hs₁U) hb.1, hv₁⟩
    have hs₁Z : s₁ ∈ Z := by
      have : s₁ = (s₁ * v₁) * v₁⁻¹ := by group
      rw [this]
      exact Z.mul_mem hb (Z.inv_mem hv₁Z)
    exact hZc s₁ hs₁Z s₂
  set H₁ : Subgroup X := Z ⊔ Subgroup.zpowers (b₁ : X) with hH₁
  have hZN : ∀ x : X, x ∈ Subgroup.normalizer (Z : Set X) := fun x => by
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      rw [← hZc z hz x, mul_inv_cancel_right]
      exact hz
    · intro hz
      have := hZc _ hz x⁻¹
      have h2 : z = x⁻¹ * (x * z * x⁻¹) * x⁻¹⁻¹ := by group
      rw [h2]
      rw [show x⁻¹ * (x * z * x⁻¹) * x⁻¹⁻¹ = x * z * x⁻¹ * x⁻¹ * x⁻¹⁻¹ by
        rw [← this]]
      simpa using hz
  have hH₁set : (H₁ : Set X) = (Z : Set X) * (Subgroup.zpowers (b₁ : X) : Set X) :=
    Subgroup.coe_mul_of_right_le_normalizer_left Z _ fun x _ => hZN x
  have hb₂H₁ : (b₂ : X) ∉ H₁ := by
    intro hb
    rw [← SetLike.mem_coe, hH₁set] at hb
    obtain ⟨z, hz, y, ⟨k, rfl⟩, hzy⟩ := hb
    apply hs₁₂
    have hcv : Commute s₁ v₁ := hcomm s₁ hs₁U v₁ hv₁
    have hpow : (s₁ * v₁) ^ k = s₁ ^ k * v₁ ^ k := hcv.mul_zpow k
    have hzy' : z * (s₁ ^ k * v₁ ^ k) = s₂ * v₂ := by
      rw [← hpow]
      exact hzy
    have hw : (z * s₁ ^ k)⁻¹ * s₂ ∈ Z := by
      have e : (z * s₁ ^ k)⁻¹ * s₂ = v₁ ^ k * v₂⁻¹ := by
        calc (z * s₁ ^ k)⁻¹ * s₂ = (z * s₁ ^ k)⁻¹ * (s₂ * v₂) * v₂⁻¹ := by group
          _ = (z * s₁ ^ k)⁻¹ * (z * (s₁ ^ k * v₁ ^ k)) * v₂⁻¹ := by rw [hzy']
          _ = v₁ ^ k * v₂⁻¹ := by group
      refine ⟨?_, ?_⟩
      · exact U.mul_mem (U.inv_mem (U.mul_mem hz.1 (U.zpow_mem hs₁U k))) hs₂U
      · rw [e]
        exact L₁.mul_mem (L₁.zpow_mem hv₁ k) (L₁.inv_mem hv₂)
    set z' := (z * s₁ ^ k)⁻¹ * s₂ with hz'
    have hs₂eq : s₂ = z * s₁ ^ k * z' := by rw [hz']; group
    rw [hs₂eq]
    have h1 : Commute s₁ z := (hZc z hz s₁).symm
    have h2 : Commute s₁ z' := (hZc z' hw s₁).symm
    have h3 : Commute s₁ (s₁ ^ k) := Commute.self_zpow s₁ k
    exact (Commute.mul_right (Commute.mul_right h1 h3) h2).eq
  set H : Subgroup X := H₁ ⊔ Subgroup.zpowers (b₂ : X) with hH
  have hHA : H ≤ A₁ :=
    sup_le (sup_le hZA (Subgroup.zpowers_le.mpr b₁.2)) (Subgroup.zpowers_le.mpr b₂.2)
  have hAp : IsPGroup 3 A₁ := fun a => ⟨1, Subtype.ext (by simpa using hAe.2 a a.2)⟩
  have hHeq : H = A₁ := by
    have h1 : 3 * Nat.card Z ≤ Nat.card H₁ :=
      three_mul_card_le_of_lt (hAp.to_le (hHA.trans' le_sup_left)) le_sup_left
        fun h => hb₁Z (h ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
    have h2 : 3 * Nat.card H₁ ≤ Nat.card H :=
      three_mul_card_le_of_lt (hAp.to_le hHA) le_sup_left
        fun h => hb₂H₁ (h ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
    rw [hZ3] at h1
    exact Subgroup.eq_of_le_of_card_ge hHA (by rw [hA27]; omega)
  have hHset : (H : Set X) = (H₁ : Set X) * (Subgroup.zpowers (b₂ : X) : Set X) :=
    Subgroup.coe_mul_of_right_le_normalizer_left H₁ _ (by
      rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
      intro x
      have hxA : ∀ y ∈ H₁, (b₂ : X) * y * (b₂ : X)⁻¹ = y := fun y hy => by
        rw [hAcomm _ b₂.2 _ (hHA.trans' le_sup_left hy), mul_inv_cancel_right]
      constructor
      · intro hx
        rw [hxA x hx]
        exact hx
      · intro hx
        have hxA' : (b₂ : X) * x * (b₂ : X)⁻¹ ∈ A₁ := hHA.trans' le_sup_left hx
        have hx'' : x ∈ A₁ := by
          have := A₁.mul_mem (A₁.mul_mem (A₁.inv_mem b₂.2) hxA') b₂.2
          simpa [mul_assoc] using this
        rw [hAcomm _ b₂.2 _ hx'', mul_inv_cancel_right] at hx
        exact hx)
  have hgen : ∀ a : A₁, ∃ z ∈ Z, ∃ i j : ℤ, (a : X) = z * (b₁ : X) ^ i * (b₂ : X) ^ j := by
    intro a
    have ha : (a : X) ∈ (H : Set X) := by rw [hHeq]; exact a.2
    rw [hHset] at ha
    obtain ⟨y, hy, x, ⟨j, rfl⟩, hyx⟩ := ha
    rw [hH₁set] at hy
    obtain ⟨z, hz, x', ⟨i, rfl⟩, rfl⟩ := hy
    exact ⟨z, hz, i, j, hyx.symm⟩
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro σ hσ1
    rw [MonoidHom.mem_ker, hφ] at hσ1
    have e1 : σ.1 b₁ = b₁ := by
      have := congrArg (fun p => ((p.1 : A₁) : X)) hσ1
      simp only [Prod.fst_one, OneMemClass.coe_one] at this
      have h2 : b₁⁻¹ * σ.1 b₁ = 1 := Subtype.ext this
      exact (inv_mul_eq_one.mp h2).symm
    have e2 : σ.1 b₂ = b₂ := by
      have := congrArg (fun p => ((p.2 : A₁) : X)) hσ1
      simp only [Prod.snd_one, OneMemClass.coe_one] at this
      have h2 : b₂⁻¹ * σ.1 b₂ = 1 := Subtype.ext this
      exact (inv_mul_eq_one.mp h2).symm
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    ext a
    obtain ⟨z, hz, i, j, ha⟩ := hgen a
    have ha' : a = (⟨z, hZA hz⟩ : A₁) * b₁ ^ i * b₂ ^ j := Subtype.ext (by
      rw [ha]
      simp)
    rw [ha', map_mul, map_mul, map_zpow, map_zpow, e1, e2,
      (hσ σ.1 σ.2).2 ⟨z, hZA hz⟩ hz]
    rfl
  have hσv : ∀ s (hs : s ∈ U) v (hv : v ∈ L₁) (hsv : s * v ∈ A₁),
      A₁.normalizerMonoidHom ⟨v, hvN s hs v hv hsv⟩ ∈ Sec4.autIn L₁ A₁ := by
    intro s hs v hv hsv
    exact Sec4.mem_autIn_iff.mpr ⟨v, _, hv, rfl⟩
  have hact : ∀ s (hs : s ∈ U) v (hv : v ∈ L₁) (hsv : s * v ∈ A₁) (b : A₁) (t : X) (ht : t ∈ U)
      (w : X) (hw : w ∈ L₁) (htw : (b : X) = t * w),
      ((b⁻¹ * A₁.normalizerMonoidHom ⟨v, hvN s hs v hv hsv⟩ b : A₁) : X) =
        t⁻¹ * s⁻¹ * t * s := by
    intro s hs v hv hsv b t ht w hw htw
    obtain ⟨hκ, heq⟩ := hkey s hs v hv hsv t ht w hw (htw ▸ b.2)
    change (b : X)⁻¹ * (v * b * v⁻¹) = _
    rw [htw, heq]
    have := hZc _ hκ (t * w)
    calc (t * w)⁻¹ * ((t⁻¹ * s⁻¹ * t * s) * (t * w))
        = (t * w)⁻¹ * ((t * w) * (t⁻¹ * s⁻¹ * t * s)) := by rw [this]
      _ = t⁻¹ * s⁻¹ * t * s := by group
  set σ₁ : Sec4.autIn L₁ A₁ := ⟨_, hσv s₁ hs₁U v₁ hv₁ ha₁⟩ with hσ₁
  set σ₂ : Sec4.autIn L₁ A₁ := ⟨_, hσv s₂ hs₂U v₂ hv₂ ha₂⟩ with hσ₂
  have hκ₁ : ((φ σ₁).2 : A₁) =
      ⟨s₂⁻¹ * s₁⁻¹ * s₂ * s₁, hZA (hkey s₁ hs₁U v₁ hv₁ ha₁ s₂ hs₂U v₂ hv₂ ha₂).1⟩ :=
    Subtype.ext (hact s₁ hs₁U v₁ hv₁ ha₁ b₂ s₂ hs₂U v₂ hv₂ rfl)
  have hκ₁' : ((φ σ₁).1 : A₁) = 1 := by
    apply Subtype.ext
    change _ = (1 : X)
    rw [show (((φ σ₁).1 : A₁) : X) = s₁⁻¹ * s₁⁻¹ * s₁ * s₁ from
      hact s₁ hs₁U v₁ hv₁ ha₁ b₁ s₁ hs₁U v₁ hv₁ rfl]
    group
  have hκ₂ : ((φ σ₂).1 : A₁) =
      ⟨s₁⁻¹ * s₂⁻¹ * s₁ * s₂, hZA (hkey s₂ hs₂U v₂ hv₂ ha₂ s₁ hs₁U v₁ hv₁ ha₁).1⟩ :=
    Subtype.ext (hact s₂ hs₂U v₂ hv₂ ha₂ b₁ s₁ hs₁U v₁ hv₁ rfl)
  have hκ₂' : ((φ σ₂).2 : A₁) = 1 := by
    apply Subtype.ext
    change _ = (1 : X)
    rw [show (((φ σ₂).2 : A₁) : X) = s₂⁻¹ * s₂⁻¹ * s₂ * s₂ from
      hact s₂ hs₂U v₂ hv₂ ha₂ b₂ s₂ hs₂U v₂ hv₂ rfl]
    group
  have hgenZA : ∀ x : ZA, x ≠ 1 → Subgroup.zpowers x = ⊤ := by
    intro x hx
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, hZAcard]
    have hdvd : orderOf x ∣ 3 := hZAcard ▸ orderOf_dvd_natCard x
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hx
    · exact h
  have hne₁ : (φ σ₁).2 ≠ 1 := by
    intro h
    apply hs₁₂
    have := congrArg (fun x : ZA => ((x : A₁) : X)) h
    simp only [OneMemClass.coe_one] at this
    rw [hκ₁] at this
    have h2 : s₂⁻¹ * s₁⁻¹ * s₂ * s₁ = 1 := this
    calc s₁ * s₂ = s₂ * s₁ * (s₂⁻¹ * s₁⁻¹ * s₂ * s₁)⁻¹ := by group
      _ = s₂ * s₁ := by rw [h2, inv_one, mul_one]
  have hne₂ : (φ σ₂).1 ≠ 1 := by
    intro h
    apply hs₁₂
    have := congrArg (fun x : ZA => ((x : A₁) : X)) h
    simp only [OneMemClass.coe_one] at this
    rw [hκ₂] at this
    have h2 : s₁⁻¹ * s₂⁻¹ * s₁ * s₂ = 1 := this
    calc s₁ * s₂ = s₂ * s₁ * (s₁⁻¹ * s₂⁻¹ * s₁ * s₂) := by group
      _ = s₂ * s₁ := by rw [h2, mul_one]
  have hsurj : Function.Surjective φ := by
    rintro ⟨x, y⟩
    obtain ⟨i, hi⟩ : x ∈ Subgroup.zpowers (φ σ₂).1 := by rw [hgenZA _ hne₂]; trivial
    obtain ⟨j, hj⟩ : y ∈ Subgroup.zpowers (φ σ₁).2 := by rw [hgenZA _ hne₁]; trivial
    refine ⟨σ₂ ^ i * σ₁ ^ j, ?_⟩
    rw [map_mul, map_zpow, map_zpow]
    ext
    · simp only [Prod.fst_mul, Prod.pow_fst]
      have h1 : ((φ σ₁).1) = 1 := Subtype.ext hκ₁'
      rw [h1, one_zpow, mul_one, ← hi]
    · simp only [Prod.snd_mul, Prod.pow_snd]
      have h2 : ((φ σ₂).2) = 1 := Subtype.ext hκ₂'
      rw [h2, one_zpow, one_mul, ← hj]
  have hbij : Function.Bijective φ := ⟨hinj, hsurj⟩
  have hZAc : ∀ x y : ZA, x * y = y * x := fun x y => Subtype.ext (Subtype.ext
    (hAcomm _ (x : A₁).2 _ (y : A₁).2))
  have hZA3 : ∀ x : ZA, x ^ 3 = 1 := fun x => Subtype.ext (Subtype.ext (by
    simpa using hAe.2 _ (x : A₁).2))
  refine ⟨⟨⟨⟨fun σ τ => hinj ?_⟩⟩, fun σ hσ' => ?_⟩, ?_⟩
  · rw [map_mul, map_mul]
    exact Prod.ext (hZAc _ _) (hZAc _ _)
  · have : φ ⟨σ, hσ'⟩ ^ 3 = 1 := Prod.ext (hZA3 _) (hZA3 _)
    rw [← map_pow] at this
    have h1 : (⟨σ, hσ'⟩ : Sec4.autIn L₁ A₁) ^ 3 = 1 := hinj (by rw [this, map_one])
    simpa using congrArg Subtype.val h1
  · rw [Nat.card_congr (Equiv.ofBijective φ hbij), Nat.card_prod, hZAcard]

omit [Finite X] in
theorem isElemAbelian_of_mulEquiv {Y : Type} [Group Y] {P : Subgroup X} {Q : Subgroup Y}
    (e : P ≃* Q) (hP : IsElemAbelian 3 P) : IsElemAbelian 3 Q := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun y hy => ?_⟩
  · obtain ⟨a, rfl⟩ := e.surjective x
    obtain ⟨b, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, hP.1.is_comm.comm a b]
  · obtain ⟨a, ha⟩ := e.surjective ⟨y, hy⟩
    have h1 : a ^ 3 = 1 := Subtype.ext (hP.2 _ a.2)
    have h2 : (⟨y, hy⟩ : Q) ^ 3 = 1 := by rw [← ha, ← map_pow, h1, map_one]
    simpa using congrArg Subtype.val h2

end Abstract

end Item211Proof

open Item211Proof in
theorem item211HeisStar_of (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6) : Item211HeisStar := by
  intro G _ _ A E U c L hpair h27 hH _
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hcA : c ∈ A := hpair.mem_E.2 hpairs.1.1
  have hc1 : c ≠ 1 := hpairs.2.1
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have hA : IsPGroup 3 A := fun a => ⟨1, Subtype.ext (by simpa using hAe.2 a a.2)⟩
  have hLc : L ∈ thetaComponentsAt 3 c := (lZeroStarAt_subset A c) hpairs.2.2.1
  have hLC : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hLc
  have hAC : A ≤ Subgroup.centralizer ({c} : Set G) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hAe.1.is_comm.comm ⟨a, ha⟩ ⟨c, hcA⟩))
  have hAL : A ≤ Subgroup.normalizer (L : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hpair.standing.toTheoremFourHyp hAe hcA hc1
      L hLc
  have hq : IsQuasisimple (lBar L) := by
    obtain ⟨L', hL', hLL'⟩ := hLc
    rw [← hLL']
    exact LocalCores.isQuasisimple_of_mulEquiv (Sec13.thetaQuotEquivSub _ L') hL'.2.2
  have hCA : A ⊓ Sec4.thetaQuotCentralizer L = Subgroup.zpowers c := by
    have hsc := Item211Proof.sectionCentralizer_eq h45 h66 hpair
    rw [Sec13.sectionCentralizer_eq_inf hAL] at hsc
    exact SetLike.coe_injective hsc
  obtain ⟨Φ₀, -⟩ := exists_lEquiv hAL
  obtain ⟨eAut⟩ := nonempty_autIn_lOne_equiv hA hAL
  obtain ⟨eX⟩ := nonempty_quotX_equiv_lBarA hLc hAC hA hAL
  obtain ⟨U, V, hUV, hcomm, hU, ⟨eV⟩, hcard⟩ := Sec13.isHeisCentral_of_mulEquiv eX.symm Φ₀ hH
  have hZU : (Subgroup.center U).map U.subtype = U ⊓ V := by
    symm
    apply Subgroup.eq_of_le_of_card_ge
    · rintro w ⟨hwU, hwV⟩
      refine ⟨⟨w, hwU⟩, Subgroup.mem_center_iff.mpr fun u => Subtype.ext ?_, rfl⟩
      exact hcomm u u.2 w hwV
    · rw [hcard, Subgroup.card_map_of_injective U.subtype_injective, hU.1.2.2.2]
  let ψ : U × V →* QuotX L A := MonoidHom.noncommCoprod U.subtype V.subtype
    (fun u v => hcomm u u.2 v v.2)
  have hψapp : ∀ y : U × V, ψ y = (y.1 : QuotX L A) * y.2 := fun y => rfl
  have hψ : ∀ x : QuotX L A, ∃ y : U × V, ψ y = x := by
    have hrange : ψ.range = ⊤ := by
      rw [eq_top_iff, ← hUV, sup_le_iff]
      constructor
      · intro u hu
        exact ⟨(⟨u, hu⟩, 1), by rw [hψapp]; simp⟩
      · intro v hv
        exact ⟨(1, ⟨v, hv⟩), by rw [hψapp]; simp⟩
    intro x
    exact MonoidHom.mem_range.mp (hrange ▸ Subgroup.mem_top x)
  have hcommV : commutator (QuotX L A) ≤ V := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    obtain ⟨⟨u, v⟩, rfl⟩ := hψ x
    obtain ⟨⟨u', v'⟩, rfl⟩ := hψ y
    rw [← map_commutatorElement, hψapp]
    have h1 : ((⁅(u, v), (u', v')⁆ : U × V).1 : QuotX L A) ∈ V := by
      have h2 : (⁅u, u'⁆ : U) ∈ commutator U :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
      rw [hU.1.2.1] at h2
      have h3 : ((⁅u, u'⁆ : U) : QuotX L A) ∈ (Subgroup.center U).map U.subtype :=
        ⟨_, h2, rfl⟩
      rw [hZU] at h3
      exact h3.2
    exact V.mul_mem h1 (⁅(u, v), (u', v')⁆ : U × V).2.2
  have hLperf : Group.IsPerfect ↥(lOne L A) := (LocalCores.isQuasisimple_of_mulEquiv Φ₀ hq).1
  have hLV : lOne L A ≤ V := by
    have h1 : (⊤ : Subgroup ↥(lOne L A)).map (lOne L A).subtype = lOne L A := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    calc lOne L A = (commutator ↥(lOne L A)).map (lOne L A).subtype := by
          rw [hLperf.commutator_eq_top, h1]
      _ = ⁅lOne L A, lOne L A⁆ := by rw [commutator_def, Subgroup.map_commutator, h1]
      _ ≤ commutator (QuotX L A) := Subgroup.commutator_mono le_top le_top
      _ ≤ V := hcommV
  have hLVeq : lOne L A = V :=
    Subgroup.eq_of_le_of_card_ge hLV (le_of_eq (Nat.card_congr eV.toEquiv))
  subst hLVeq
  have hmax := maximal_aOne (L := L) hAe hpair.mem_S.1.2.1
  have hA27 : Nat.card (aOne L A) = 27 := by
    rw [← Nat.card_congr (aEquiv (L := L) hA).toEquiv, h27]
    norm_num
  have hc₁ : orderOf (piX L A ⟨c, Subgroup.mem_sup_right hcA⟩) = 3 := by
    have h1 : (piX L A ⟨c, Subgroup.mem_sup_right hcA⟩) =
        ((aEquiv (L := L) hA ⟨c, hcA⟩ : aOne L A) : QuotX L A) := rfl
    rw [h1, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    exact orderOf_eq_prime (hAe.2 c hcA) hc1
  have hAC₁ : Nat.card (aOne L A ⊓ Subgroup.centralizer (lOne L A : Set (QuotX L A)) :
      Subgroup (QuotX L A)) = 3 := by
    rw [aOne_inf_centralizer hA hAL hcA hCA, Nat.card_zpowers, hc₁]
  obtain ⟨hab, h9⟩ := autIn_heis hUV hcomm hU hcard (normal_lOne hAL) hmax.prop
    (fun B hB hAB => hmax.2 hB hAB) hA27 hAC₁
  exact ⟨isElemAbelian_of_mulEquiv eAut hab, by rw [← Nat.card_congr eAut.toEquiv, h9]⟩

end CFSG.RankThree.PartTwo.Sec21
