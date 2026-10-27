module

public import CFSG.Walter.W67.Section6.Core62C
public import CFSG.Walter.W67.Section5.Lemma54

public section

namespace CFSG.Walter.W67.Sec64

open Sec6

variable {G : Type} [Group G] [Finite G]

theorem card_modEq_card_inf_centralizer {ℓ : ℕ} [Fact ℓ.Prime] {S : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (S : Set G)) {k : ℕ} (hgk : g ^ ℓ ^ k = 1) :
    Nat.card S ≡ Nat.card ↥(S ⊓ Subgroup.centralizer ({g} : Set G)) [MOD ℓ] := by
  have hσ : conjAut hg ^ ℓ ^ k = 1 := by
    refine MulEquiv.ext fun s => Subtype.ext ?_
    rw [conjAut_pow_apply, hgk, one_mul, inv_one, mul_one]
    rfl
  have h := Huppert.card_fixedSubgroup_modEq hσ
  have heq : Nat.card (Huppert.fixedSubgroup (conjAut hg)) =
      Nat.card ↥(S ⊓ Subgroup.centralizer ({g} : Set G)) := by
    refine Nat.card_congr
      { toFun := fun v => ⟨v.1.1, Subgroup.mem_inf.mpr ⟨v.1.2, ?_⟩⟩
        invFun := fun v => ⟨⟨v.1, (Subgroup.mem_inf.mp v.2).1⟩, ?_⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    · have h1 : g * (v.1 : G) * g⁻¹ = v.1 := congrArg Subtype.val v.2
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (v.1 : G) * g = g * v.1 * g⁻¹ * g := by rw [h1]
        _ = g * v.1 := by group
    · apply Subtype.ext
      change g * (v : G) * g⁻¹ = v
      have h1 := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp v.2).2
      rw [← h1]
      group
  rwa [heq] at h

omit [Finite G] in
theorem conj_pow_of_inv {x y : G} (h : y * x * y⁻¹ = x⁻¹) (n : ℕ) :
    y ^ n * x * (y ^ n)⁻¹ = x ^ ((-1 : ℤ) ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_inv_rev, show y * y ^ n * x * ((y ^ n)⁻¹ * y⁻¹) =
      y * (y ^ n * x * (y ^ n)⁻¹) * y⁻¹ by group, ih, ← conj_zpow, h, inv_zpow', pow_succ]
    congr 1
    ring

theorem exists_two_pow_inv {x y : G} (h : y * x * y⁻¹ = x⁻¹) :
    ∃ t : G, (∃ k : ℕ, t ^ 2 ^ k = 1) ∧ t ∈ Subgroup.zpowers y ∧ t * x * t⁻¹ = x⁻¹ := by
  obtain ⟨k, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y).ne'
  refine ⟨y ^ m, ⟨k, ?_⟩, Subgroup.pow_mem _ (Subgroup.mem_zpowers y) m, ?_⟩
  · rw [← pow_mul, mul_comm, ← hn, pow_orderOf_eq_one]
  · rw [conj_pow_of_inv h m, hm.neg_one_pow, zpow_neg_one]

omit [Finite G] in
theorem inv_of_not_comm {Q : Subgroup G} {t x : G} (ht : t * t = 1)
    (htQ : t ∈ Subgroup.normalizer (Q : Set G)) (hx : x ∈ Q) (htx : t * x * t⁻¹ ≠ x) :
    (t * x * t⁻¹)⁻¹ * x ∈ Q ∧ (t * x * t⁻¹)⁻¹ * x ≠ 1 ∧
      t * ((t * x * t⁻¹)⁻¹ * x) * t⁻¹ = ((t * x * t⁻¹)⁻¹ * x)⁻¹ := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  refine ⟨Q.mul_mem (Q.inv_mem ((Subgroup.mem_normalizer_iff.mp htQ x).mp hx)) hx, ?_, ?_⟩
  · intro h1
    rw [inv_mul_eq_one] at h1
    exact htx h1
  · calc t * ((t * x * t⁻¹)⁻¹ * x) * t⁻¹ = (t * t) * x⁻¹ * t⁻¹ * x * t⁻¹ := by group
      _ = x⁻¹ * t⁻¹ * x * t⁻¹ := by rw [ht, one_mul]
      _ = x⁻¹ * t * x * t⁻¹ := by rw [htinv]
      _ = ((t * x * t⁻¹)⁻¹ * x)⁻¹ := by group

structure InvFacts (G : Type) [Group G] (r : ℕ) : Prop where
  two_comm : ∀ T : Subgroup G, IsPGroup 2 T → ∀ a ∈ T, ∀ b ∈ T, a * b = b * a
  two_sq : ∀ T : Subgroup G, IsPGroup 2 T → ∀ a ∈ T, a * a = 1
  no_real : ∀ u x t : G, orderOf u = 2 → x ∈ Subgroup.centralizer ({u} : Set G) →
    t ∈ Subgroup.centralizer ({u} : Set G) → t * t = 1 → t * x * t⁻¹ = x⁻¹ →
    IsPGroup r (Subgroup.zpowers x) → x = 1

namespace InvFacts

variable {r : ℕ} (h : InvFacts G r)
include h

omit [Finite G] in
theorem comm_of_mem_centralizer {Q : Subgroup G} (hQ : IsPGroup r Q) {u v : G}
    (hu : u * u = 1) (hv : orderOf v = 2) (huv : u * v = v * u)
    (huQ : u ∈ Subgroup.normalizer (Q : Set G)) {x : G} (hx : x ∈ Q)
    (hxv : x ∈ Subgroup.centralizer ({v} : Set G)) : u * x = x * u := by
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  set y := (u * x * u⁻¹)⁻¹ * x with hy
  have hyQ : y ∈ Q := Q.mul_mem (Q.inv_mem ((Subgroup.mem_normalizer_iff.mp huQ x).mp hx)) hx
  have huC : u ∈ Subgroup.centralizer ({v} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr huv
  have hyC : y ∈ Subgroup.centralizer ({v} : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ huC hxv)
      (Subgroup.inv_mem _ huC))) hxv
  have hyinv : u * y * u⁻¹ = y⁻¹ := by
    rw [hy]
    calc u * ((u * x * u⁻¹)⁻¹ * x) * u⁻¹ = (u * u) * x⁻¹ * u⁻¹ * x * u⁻¹ := by group
      _ = x⁻¹ * u⁻¹ * x * u⁻¹ := by rw [hu, one_mul]
      _ = x⁻¹ * u * x * u⁻¹ := by rw [huinv]
      _ = ((u * x * u⁻¹)⁻¹ * x)⁻¹ := by group
  have hyr : IsPGroup r (Subgroup.zpowers y) := hQ.to_le (Subgroup.zpowers_le.mpr hyQ)
  have hy1 := h.no_real v y u hv hyC huC hu hyinv hyr
  rw [hy, inv_mul_eq_one] at hy1
  have : u * x * u⁻¹ = x := hy1
  calc u * x = u * x * u⁻¹ * u := by group
    _ = x * u := by rw [this]

theorem le_centralizer_of_four [Fact r.Prime] (hr2 : r ≠ 2) {Q : Subgroup G}
    (hQ : IsPGroup r Q) {u v : G} (hu : orderOf u = 2) (hv : orderOf v = 2)
    (huv : u * v = v * u) (hne : u ≠ v) (huQ : u ∈ Subgroup.normalizer (Q : Set G))
    (hvQ : v ∈ Subgroup.normalizer (Q : Set G)) : u ∈ Subgroup.centralizer (Q : Set G) := by
  have huu : u * u = 1 := by rw [← pow_two, ← hu, pow_orderOf_eq_one]
  have hvv : v * v = 1 := by rw [← pow_two, ← hv, pow_orderOf_eq_one]
  have hodd : Odd (Nat.card Q) := by
    obtain ⟨k, hk⟩ := hQ.exists_card_eq
    rw [hk]
    exact ((Fact.out : r.Prime).odd_of_ne_two hr2).pow
  have hN : ProperTwoGeneratedCore.LocalCriterionDenominator.denominatorFourGroup u v ≤
      Subgroup.normalizer (Q : Set G) := by
    rw [ProperTwoGeneratedCore.LocalCriterionDenominator.denominatorFourGroup,
      Subgroup.closure_le]
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl
    · exact huQ
    · exact hvQ
  have hgen :=
    ProperTwoGeneratedCore.LocalCriterionDenominator.four_group_odd_centralizer_generation Q u v
      hu hv huv hne hodd hN
  have huv2 : orderOf (u * v) = 2 := by
    apply orderOf_eq_prime
    · calc (u * v) ^ 2 = (u * v) * (u * v) := pow_two _
        _ = (u * u) * (v * v) := by
          calc (u * v) * (u * v) = u * (v * u) * v := by group
            _ = u * (u * v) * v := by rw [huv]
            _ = (u * u) * (v * v) := by group
        _ = 1 := by rw [huu, hvv, one_mul]
    · intro h1
      apply hne
      calc u = u * (v * v) := by rw [hvv, mul_one]
        _ = (u * v) * v := by group
        _ = v := by rw [h1, one_mul]
  have hle : Q ≤ Subgroup.centralizer ({u} : Set G) := by
    rw [hgen]
    refine sup_le (sup_le inf_le_right ?_) ?_
    · intro x hx
      obtain ⟨hxQ, hxv⟩ := Subgroup.mem_inf.mp hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (h.comm_of_mem_centralizer hQ huu hv huv huQ hxQ hxv).symm
    · intro x hx
      obtain ⟨hxQ, hxuv⟩ := Subgroup.mem_inf.mp hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      have huuv : u * (u * v) = (u * v) * u := by
        calc u * (u * v) = u * (v * u) := by rw [huv]
          _ = (u * v) * u := by group
      exact (h.comm_of_mem_centralizer hQ huu huv2 huuv huQ hxQ hxuv).symm
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hx)

theorem factorization_two_le [Fact r.Prime] (hr2 : r ≠ 2) {Q : Subgroup G}
    (hQ : IsPGroup r Q) (hnc : ∀ t ∈ Subgroup.centralizer (Q : Set G), t * t = 1 → t = 1)
    {N : Subgroup G} (hN : N ≤ Subgroup.normalizer (Q : Set G)) :
    (Nat.card N).factorization 2 ≤ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hlt
  push Not at hlt
  obtain ⟨T⟩ := (inferInstance : Nonempty (Sylow 2 N))
  have hT4 : 4 ∣ Nat.card (T : Subgroup N) := by
    rw [Sylow.card_eq_multiplicity]
    have h2le : 2 ≤ (Nat.card N).factorization 2 := hlt
    exact (show 4 ∣ 2 ^ 2 by norm_num).trans (pow_dvd_pow 2 h2le)
  set T' := (T : Subgroup N).map N.subtype with hT'
  have hT'2 : IsPGroup 2 T' := T.isPGroup'.map _
  have hT'card : 4 ∣ Nat.card T' := by
    rw [hT', Subgroup.card_map_of_injective N.subtype_injective]
    exact hT4
  have hinv : ∀ a ∈ T', a ≠ 1 → orderOf a = 2 := fun a ha ha1 =>
    orderOf_eq_prime (by rw [pow_two]; exact h.two_sq T' hT'2 a ha) ha1
  obtain ⟨a, ha, ha1⟩ : ∃ a ∈ T', a ≠ 1 := by
    by_contra h1
    push Not at h1
    have : T' = ⊥ := eq_bot_iff.mpr fun x hx => (Subgroup.mem_bot).mpr (h1 x hx)
    rw [this, Subgroup.card_bot] at hT'card
    norm_num at hT'card
  obtain ⟨b, hb, hb1, hba⟩ : ∃ b ∈ T', b ≠ 1 ∧ b ≠ a := by
    by_contra h1
    push Not at h1
    have hsub : (T' : Set G) ⊆ {1, a} := fun x hx => by
      by_cases hx1 : x = 1
      · exact Or.inl hx1
      · exact Or.inr (h1 x hx hx1)
    have hle : Nat.card T' ≤ 2 := by
      have := Set.ncard_le_ncard hsub (Set.toFinite _)
      rw [Set.ncard_pair ha1.symm] at this
      rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq]
      exact this
    have := Nat.le_of_dvd Nat.card_pos hT'card
    omega
  have hTN : T' ≤ N := Subgroup.map_subtype_le _
  have haC := h.le_centralizer_of_four hr2 hQ (hinv a ha ha1) (hinv b hb hb1)
    (h.two_comm T' hT'2 a ha b hb) hba.symm (hN (hTN ha)) (hN (hTN hb))
  exact ha1 (hnc a haC (h.two_sq T' hT'2 a ha))

theorem exists_sylow [Fact r.Prime] (hr2 : r ≠ 2) {J : G} (hJ : orderOf J = 2)
    {Q₀ : Subgroup G} (hQ₀ : IsPGroup r Q₀) (hJQ₀ : J ∈ Subgroup.normalizer (Q₀ : Set G))
    (hnc : ∀ t ∈ Subgroup.centralizer (Q₀ : Set G), t * t = 1 → t = 1) :
    ∃ S : Subgroup G, Q₀ ≤ S ∧ IsPGroup r S ∧
      Nat.card S = r ^ (Nat.card G).factorization r ∧ J ∈ Subgroup.normalizer (S : Set G) := by
  classical
  have hJJ : J * J = 1 := by rw [← pow_two, ← hJ, pow_orderOf_eq_one]
  obtain ⟨S, ⟨hQS, hSr, hJS⟩, hmax⟩ := Set.Finite.exists_maximalFor (fun S : Subgroup G =>
      Nat.card S) {S : Subgroup G | Q₀ ≤ S ∧ IsPGroup r S ∧
        J ∈ Subgroup.normalizer (S : Set G)} (Set.toFinite _) ⟨Q₀, le_rfl, hQ₀, hJQ₀⟩
  refine ⟨S, hQS, hSr, ?_, hJS⟩
  refine card_eq_of_normalizer hSr fun Q hQ hSQ hQN => ?_
  set N := Subgroup.normalizer (S : Set G) with hNdef
  have hN2 : (Nat.card N).factorization 2 = 1 := by
    have hle := h.factorization_two_le hr2 hSr (fun t ht ht2 =>
      hnc t (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hQS) ht) ht2) (le_refl N)
    have hge : 1 ≤ (Nat.card N).factorization 2 := by
      have hJ2 : 2 ∣ Nat.card N := by
        have := Subgroup.orderOf_dvd_natCard N hJS
        rwa [hJ] at this
      exact (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two Nat.card_pos.ne').mp hJ2
    omega
  obtain ⟨R, hR⟩ := exists_sylow_mem_normalizer_of_two (X := N) (ℓ := r) hr2 hN2
    (j := ⟨J, hJS⟩) (fun h1 => by
      have h2 : J = 1 := congrArg Subtype.val h1
      have h3 := hJ
      rw [h2, orderOf_one] at h3
      exact absurd h3 (by norm_num))
    (Subtype.ext hJJ)
  set R' := (R : Subgroup N).map N.subtype with hR'
  have hSn : (S.subgroupOf N).Normal := Subgroup.normal_in_normalizer
  have : (S.comap N.subtype).Normal := hSn
  have hSR : S ≤ R' := by
    intro x hx
    have := (hSr.comap_subtype (K := N)).le_sylow_of_normal R
    exact ⟨⟨x, Subgroup.le_normalizer hx⟩, this hx, rfl⟩
  have hR'r : IsPGroup r R' := R.isPGroup'.map _
  have hJR' : J ∈ Subgroup.normalizer (R' : Set G) := by
    apply JT.mem_normalizer_of_conj_mem
    rintro _ ⟨y, hy, rfl⟩
    have := (Subgroup.mem_normalizer_iff.mp hR y).mp hy
    exact ⟨_, this, rfl⟩
  have hmax' := hmax ⟨hQS.trans hSR, hR'r, hJR'⟩
  have hQR : Nat.card Q ≤ Nat.card R' := by
    rw [hR', Subgroup.card_map_of_injective N.subtype_injective, Sylow.card_eq_multiplicity]
    obtain ⟨k, hk⟩ := hQ.exists_card_eq
    have h1 : r ^ k ∣ Nat.card N := by
      have := Subgroup.card_dvd_of_le hQN
      rwa [hk] at this
    have h2 := (Nat.Prime.pow_dvd_iff_le_factorization Fact.out Nat.card_pos.ne').mp h1
    rw [hk]
    exact Nat.pow_le_pow_right (Fact.out : r.Prime).pos h2
  have hcard := hmax' (Subgroup.card_le_of_le hSR)
  exact (Subgroup.eq_of_le_of_card_ge hSQ (hQR.trans hcard)).symm.le

end InvFacts

structure L168 (L S : Subgroup G) : Prop where
  S_le : S ≤ L
  card_S : Nat.card S = 8
  card_L : Nat.card L = 168
  L_le_N : L ≤ Subgroup.normalizer (S : Set G)
  C_le : L ⊓ Subgroup.centralizer (S : Set G) ≤ S

namespace L168

variable {L S : Subgroup G} (hL : L168 L S)
include hL

theorem mem_S_of_pow {w : G} (hw : w ∈ L) {k : ℕ} (hwk : w ^ 2 ^ k = 1) : w ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W := Subgroup.zpowers w with hWdef
  have hWN : W ≤ Subgroup.normalizer (S : Set G) := Subgroup.zpowers_le.mpr (hL.L_le_N hw)
  have h1 := Sec52.card_sup_mul_card_inf hWN
  have hW2 : IsPGroup 2 W := Huppert.isPGroup_zpowers hwk
  obtain ⟨a, ha⟩ := hW2.exists_card_eq
  rw [hL.card_S, ha] at h1
  have hdvd : Nat.card (W ⊔ S : Subgroup G) ∣ 2 ^ (3 + a) := by
    rw [pow_add, show (2 : ℕ) ^ 3 = 8 by norm_num, ← h1]
    exact Dvd.intro _ rfl
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hle : W ⊔ S ≤ L := sup_le (Subgroup.zpowers_le.mpr hw) hL.S_le
  have hdvd' : Nat.card (W ⊔ S : Subgroup G) ∣ 168 := hL.card_L ▸ Subgroup.card_dvd_of_le hle
  rw [hj] at hdvd'
  have hj3 : j ≤ 3 := by
    by_contra hj3
    have h16 : 2 ^ 4 ∣ 2 ^ j := pow_dvd_pow 2 (by omega)
    have := h16.trans hdvd'
    norm_num at this
  have hcard : Nat.card (W ⊔ S : Subgroup G) ≤ Nat.card S := by
    rw [hj, hL.card_S]
    calc 2 ^ j ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hj3
      _ = 8 := by norm_num
  have heq : S = W ⊔ S := Subgroup.eq_of_le_of_card_ge le_sup_right hcard
  rw [heq]
  exact Subgroup.mem_sup_left (Subgroup.mem_zpowers w)

theorem inf_centralizer_seven {u : G} (hu : u ∈ L) (hu7 : orderOf u = 7) :
    S ⊓ Subgroup.centralizer ({u} : Set G) = ⊥ := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hmod := card_modEq_card_inf_centralizer (ℓ := 7) (hL.L_le_N hu) (k := 1)
    (by rw [pow_one, ← hu7, pow_orderOf_eq_one])
  rw [hL.card_S] at hmod
  have hdvd : Nat.card ↥(S ⊓ Subgroup.centralizer ({u} : Set G)) ∣ 8 :=
    hL.card_S ▸ Subgroup.card_dvd_of_le inf_le_left
  have hne8 : Nat.card ↥(S ⊓ Subgroup.centralizer ({u} : Set G)) ≠ 8 := by
    intro h8
    have heq : S ⊓ Subgroup.centralizer ({u} : Set G) = S :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h8, hL.card_S])
    have huC : u ∈ Subgroup.centralizer (S : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      have hs' : s ∈ S ⊓ Subgroup.centralizer ({u} : Set G) := by rw [heq]; exact hs
      exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hs').2
    have huS := hL.C_le (Subgroup.mem_inf.mpr ⟨hu, huC⟩)
    have := Subgroup.orderOf_dvd_natCard S huS
    rw [hu7, hL.card_S] at this
    norm_num at this
  apply Subgroup.eq_bot_of_card_eq
  have hle : Nat.card ↥(S ⊓ Subgroup.centralizer ({u} : Set G)) ≤ 8 := Nat.le_of_dvd (by norm_num)
    hdvd
  unfold Nat.ModEq at hmod
  interval_cases h : Nat.card ↥(S ⊓ Subgroup.centralizer ({u} : Set G)) <;> simp_all

theorem not_comm {u x : G} (hu : u ∈ L) (hu7 : orderOf u = 7) (hx : x ∈ L)
    (hx3 : orderOf x = 3) : u * x ≠ x * u := by
  intro hux
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C := S ⊓ Subgroup.centralizer ({x} : Set G) with hCdef
  have huxC : u ∈ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hux
  have huN : u ∈ Subgroup.normalizer (C : Set G) :=
    Sec54.mem_normalizer_inf (hL.L_le_N hu) (Subgroup.le_normalizer huxC)
  have hmod7 := card_modEq_card_inf_centralizer (ℓ := 7) huN (k := 1)
    (by rw [pow_one, ← hu7, pow_orderOf_eq_one])
  have hbot : C ⊓ Subgroup.centralizer ({u} : Set G) = ⊥ := by
    rw [eq_bot_iff, ← hL.inf_centralizer_seven hu hu7]
    exact inf_le_inf_right _ inf_le_left
  rw [hbot, Subgroup.card_bot] at hmod7
  have hdvd : Nat.card C ∣ 8 := hL.card_S ▸ Subgroup.card_dvd_of_le inf_le_left
  have hne8 : Nat.card C ≠ 8 := by
    intro h8
    have heq : C = S := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h8, hL.card_S])
    have hxC : x ∈ Subgroup.centralizer (S : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      have hs' : s ∈ C := by rw [heq]; exact hs
      exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hs').2
    have hxS := hL.C_le (Subgroup.mem_inf.mpr ⟨hx, hxC⟩)
    have := Subgroup.orderOf_dvd_natCard S hxS
    rw [hx3, hL.card_S] at this
    norm_num at this
  have hmod3 := card_modEq_card_inf_centralizer (ℓ := 3) (hL.L_le_N hx) (k := 1)
    (by rw [pow_one, ← hx3, pow_orderOf_eq_one])
  rw [hL.card_S] at hmod3
  have hle : Nat.card C ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd
  unfold Nat.ModEq at hmod7 hmod3
  rw [← hCdef] at hmod3
  interval_cases h : Nat.card C <;> simp_all

theorem not_inv {l t : G} (hl : l ∈ L) (hl1 : l ≠ 1) (hl7 : l ^ 7 = 1) (ht : t ∈ L)
    (htl : t * l * t⁻¹ = l⁻¹) : False := by
  obtain ⟨w, ⟨k, hwk⟩, hwt, hwl⟩ := exists_two_pow_inv htl
  have hwL : w ∈ L := (Subgroup.zpowers_le.mpr ht) hwt
  have hwS := hL.mem_S_of_pow hwL hwk
  have h1 : w * l * w⁻¹ * l⁻¹ ∈ S := by
    rw [show w * l * w⁻¹ * l⁻¹ = w * (l * w⁻¹ * l⁻¹) by group]
    exact S.mul_mem hwS ((Subgroup.mem_normalizer_iff.mp (hL.L_le_N hl) _).mp (S.inv_mem hwS))
  rw [hwl] at h1
  have h8 : (l⁻¹ * l⁻¹) ^ 8 = 1 := by
    have := Subgroup.orderOf_dvd_natCard S h1
    rw [hL.card_S] at this
    exact orderOf_dvd_iff_pow_eq_one.mp this
  have h7 : (l⁻¹ * l⁻¹) ^ 7 = 1 := by
    rw [← pow_two, ← pow_mul, mul_comm, pow_mul, inv_pow, hl7, inv_one, one_pow]
  have h1' : l⁻¹ * l⁻¹ = 1 := by
    have := pow_gcd_eq_one.mpr ⟨h8, h7⟩
    norm_num at this
    exact this
  apply hl1
  calc l = l ^ 7 * (l⁻¹ * l⁻¹) ^ 3 := by group
    _ = 1 := by rw [hl7, h1', one_pow, one_mul]

omit [Finite G] in
theorem factorization_seven : (Nat.card L).factorization 7 = 1 := by
  rw [hL.card_L, show (168 : ℕ) = 7 * 24 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_self (by norm_num),
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 7 ∣ 24)]

theorem exists_three {u : G} (hu : u ∈ L) (hu7 : orderOf u = 7) :
    ∃ ρ ∈ L, orderOf ρ = 3 ∧
      ρ ∈ Subgroup.normalizer ((Subgroup.zpowers u : Subgroup G) : Set G) ∧ ρ * u ≠ u * ρ := by
  classical
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have huL : Subgroup.zpowers u ≤ L := Subgroup.zpowers_le.mpr hu
  set Q := (Subgroup.zpowers u).subgroupOf L with hQdef
  have hQc : Nat.card Q = 7 ^ (Nat.card L).factorization 7 := by
    rw [hL.factorization_seven, pow_one, hQdef,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe huL).toEquiv, Nat.card_zpowers, hu7]
  set P : Sylow 7 L := Sylow.ofCard Q hQc with hPdef
  have hPQ : (P : Subgroup L) = Q := Sylow.coe_ofCard _ _
  have hidx : (P : Subgroup L).index = 24 := by
    have h := (P : Subgroup L).card_mul_index
    rw [Sylow.card_eq_multiplicity, hL.factorization_seven, pow_one, hL.card_L] at h
    omega
  have hn1 := card_sylow_modEq_one 7 L
  have hn2 := Sylow.card_eq_index_normalizer P
  have hn3 : Nat.card (Sylow 7 L) ∣ 24 := hidx ▸ Sylow.card_dvd_index P
  have hn8 : Nat.card (Sylow 7 L) = 8 := by
    have hle : Nat.card (Sylow 7 L) ≤ 24 := Nat.le_of_dvd (by norm_num) hn3
    have hne1 : Nat.card (Sylow 7 L) ≠ 1 := by
      intro h1
      rw [h1] at hn2
      have hNtop : Subgroup.normalizer ((P : Subgroup L) : Set L) = ⊤ :=
        Subgroup.index_eq_one.mp hn2.symm
      have huC : u ∈ Subgroup.centralizer (S : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro s hs
        have hsL : s ∈ L := hL.S_le hs
        have hsN : (⟨s, hsL⟩ : L) ∈ Subgroup.normalizer ((P : Subgroup L) : Set L) := by
          rw [hNtop]; exact Subgroup.mem_top _
        have hc1 : s * u * s⁻¹ * u⁻¹ ∈ Subgroup.zpowers u := by
          have h2 : (⟨s, hsL⟩ : L) * ⟨u, hu⟩ * (⟨s, hsL⟩ : L)⁻¹ ∈ (P : Subgroup L) :=
            (Subgroup.mem_normalizer_iff.mp hsN _).mp (by
              rw [hPQ]; exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers u))
          rw [hPQ, Subgroup.mem_subgroupOf] at h2
          exact Subgroup.mul_mem _ h2 (Subgroup.inv_mem _ (Subgroup.mem_zpowers u))
        have hc2 : s * u * s⁻¹ * u⁻¹ ∈ S := by
          rw [show s * u * s⁻¹ * u⁻¹ = s * (u * s⁻¹ * u⁻¹) by group]
          exact S.mul_mem hs ((Subgroup.mem_normalizer_iff.mp (hL.L_le_N hu) _).mp
            (S.inv_mem hs))
        have hbot : Subgroup.zpowers u ⊓ S = ⊥ := by
          apply inf_eq_bot_of_coprime
          rw [Nat.card_zpowers, hu7, hL.card_S]
          norm_num
        have hc3 : s * u * s⁻¹ * u⁻¹ ∈ Subgroup.zpowers u ⊓ S := Subgroup.mem_inf.mpr ⟨hc1, hc2⟩
        rw [hbot, Subgroup.mem_bot] at hc3
        calc s * u = s * u * s⁻¹ * u⁻¹ * (u * s) := by group
          _ = u * s := by rw [hc3, one_mul]
      have huS := hL.C_le (Subgroup.mem_inf.mpr ⟨hu, huC⟩)
      have := Subgroup.orderOf_dvd_natCard S huS
      rw [hu7, hL.card_S] at this
      norm_num at this
    have key : ∀ n : ℕ, n ≤ 24 → n ∣ 24 → n % 7 = 1 → n ≠ 1 → n = 8 := by decide
    exact key _ hle hn3 hn1 hne1
  set N := Subgroup.normalizer ((P : Subgroup L) : Set L) with hNdef
  have hNcard : Nat.card N = 21 := by
    have h := N.card_mul_index
    have hNidx : N.index = 8 := by
      rw [hn8] at hn2
      exact hn2.symm
    rw [hNidx, hL.card_L] at h
    omega
  obtain ⟨⟨⟨ρ, hρL⟩, hρN⟩, hρo⟩ :=
    exists_prime_orderOf_dvd_card' (G := N) 3 (by rw [hNcard]; norm_num)
  rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk] at hρo
  refine ⟨ρ, hρL, hρo, ?_, fun h => hL.not_comm hu hu7 hρL hρo h.symm⟩
  apply Sec53.mem_normalizer_of_conj_le
  intro x hx
  have hxL : x ∈ L := huL hx
  have h2 : (⟨ρ, hρL⟩ : L) * ⟨x, hxL⟩ * (⟨ρ, hρL⟩ : L)⁻¹ ∈ (P : Subgroup L) :=
    (Subgroup.mem_normalizer_iff.mp hρN _).mp (by
      rw [hPQ]; exact Subgroup.mem_subgroupOf.mpr hx)
  rw [hPQ, Subgroup.mem_subgroupOf] at h2
  exact h2

theorem inf_centralizer_eq {u : G} (hu : u ∈ L) (hu7 : orderOf u = 7) :
    L ⊓ Subgroup.centralizer ({u} : Set G) = Subgroup.zpowers u := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C := L ⊓ Subgroup.centralizer ({u} : Set G) with hCdef
  have hle : Subgroup.zpowers u ≤ C := Subgroup.zpowers_le.mpr
    (Subgroup.mem_inf.mpr ⟨hu, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩)
  have h2 : ¬ 2 ∣ Nat.card C := by
    intro h2
    obtain ⟨⟨w, hw⟩, hwo⟩ := exists_prime_orderOf_dvd_card' (G := C) 2 h2
    rw [Subgroup.orderOf_mk] at hwo
    obtain ⟨hwL, hwu⟩ := Subgroup.mem_inf.mp hw
    have hwS := hL.mem_S_of_pow hwL (k := 1) (by rw [pow_one, ← hwo, pow_orderOf_eq_one])
    have hwuC : w ∈ S ⊓ Subgroup.centralizer ({u} : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨hwS, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hwu ⊢
      exact hwu
    rw [hL.inf_centralizer_seven hu hu7, Subgroup.mem_bot] at hwuC
    rw [hwuC, orderOf_one] at hwo
    norm_num at hwo
  have h3 : ¬ 3 ∣ Nat.card C := by
    intro h3
    obtain ⟨⟨x, hx⟩, hxo⟩ := exists_prime_orderOf_dvd_card' (G := C) 3 h3
    rw [Subgroup.orderOf_mk] at hxo
    obtain ⟨hxL, hxu⟩ := Subgroup.mem_inf.mp hx
    exact hL.not_comm hu hu7 hxL hxo (Subgroup.mem_centralizer_singleton_iff.mp hxu).symm
  have hdvd : Nat.card C ∣ 168 := hL.card_L ▸ Subgroup.card_dvd_of_le inf_le_left
  have h7 : Nat.card C ∣ 7 := by
    have hc : Nat.Coprime (Nat.card C) 24 := by
      rw [show (24 : ℕ) = 2 ^ 3 * 3 by norm_num]
      exact Nat.Coprime.mul_right
        (Nat.Coprime.pow_right 3 ((Nat.coprime_comm.mp
          ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2))))
        (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3))
    exact hc.dvd_of_dvd_mul_left (by rw [show (24 : ℕ) * 7 = 168 by norm_num]; exact hdvd)
  have hcard : Nat.card C ≤ Nat.card (Subgroup.zpowers u) := by
    rw [Nat.card_zpowers, hu7]
    exact Nat.le_of_dvd (by norm_num) h7
  exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm

end L168

end CFSG.Walter.W67.Sec64
