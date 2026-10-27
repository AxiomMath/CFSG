module

public import CFSG.Walter.W67.Section6.Core62B
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorNontrivial
public import CFSG.Walter.W67.Section6.Core62A

public section

namespace CFSG.Walter.W67.Sec6

variable {G : Type} [Group G] [Finite G]

open BenderSuzuki.External BenderSuzuki.PFchapter1section1

theorem card_eq_of_normalizer {r : ℕ} [Fact r.Prime] {P : Subgroup G} (hP : IsPGroup r P)
    (h : ∀ Q : Subgroup G, IsPGroup r Q → P ≤ Q → Q ≤ Subgroup.normalizer (P : Set G) →
      Q ≤ P) : Nat.card P = r ^ (Nat.card G).factorization r := by
  obtain ⟨T, hT⟩ := hP.exists_le_sylow
  have := eq_of_le_of_normalizer_le T.isPGroup' hT h
  rw [this, Sylow.card_eq_multiplicity]

theorem weaklyClosedIn_self {r : ℕ} [Fact r.Prime] (P : Sylow r G) :
    WeaklyClosedIn (P : Subgroup G) (P : Subgroup G) := by
  refine ⟨le_rfl, fun g hg => ?_⟩
  have hc : Nat.card (rightConjugate (P : Subgroup G) g) = Nat.card (P : Subgroup G) :=
    card_cj g⁻¹ (P : Subgroup G)
  exact Subgroup.eq_of_le_of_card_ge hg hc.ge

theorem false_of_sylow_P₀ {r : ℕ} [Fact r.Prime] {P₀ M M₁ : Subgroup G} {x₀ : G}
    (hperf : commutator G = ⊤) (hr3 : 3 ≤ r) (hP₀c : IsCyclic P₀) (hP₀r : IsPGroup r P₀)
    (hx₀ : x₀ ∈ P₀) (hxo : orderOf x₀ = r)
    (hM : Subgroup.normalizer ((Subgroup.zpowers x₀ : Subgroup G) : Set G) = M)
    (hcard : Nat.card P₀ = r ^ (Nat.card M).factorization r)
    (hMpow : ∀ m ∈ M, m ^ Nat.card P₀ ∈ M₁) (hP₀M₁ : P₀ ⊓ M₁ = ⊥) : False := by
  have hNM : Subgroup.normalizer (P₀ : Set G) ≤ M := by
    rw [← hM]
    intro g hg
    have h1 : g * x₀ * g⁻¹ ∈ P₀ := (Subgroup.mem_normalizer_iff.mp hg x₀).mp hx₀
    have hz := zpowers_eq_of_cyclic hP₀c h1 hx₀ (orderOf_conj_mul g x₀)
    apply JT.mem_normalizer_of_conj_mem
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← conj_zpow, ← hz]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k
  have hP₀M : P₀ ≤ M := Subgroup.le_normalizer.trans hNM
  have hsyl : Nat.card P₀ = r ^ (Nat.card G).factorization r := by
    refine card_eq_of_normalizer hP₀r fun Q hQ hP₀Q hQN => ?_
    have hQM : Q ≤ M := hQN.trans hNM
    obtain ⟨k, hk⟩ := hQ.exists_card_eq
    have h1 : r ^ k ∣ Nat.card M := hk ▸ Subgroup.card_dvd_of_le hQM
    have h2 := (Nat.Prime.pow_dvd_iff_le_factorization Fact.out Nat.card_pos.ne').mp h1
    have h3 : Nat.card Q ≤ Nat.card P₀ := by
      rw [hk, hcard]
      exact Nat.pow_le_pow_right (Fact.out : r.Prime).pos h2
    exact (Subgroup.eq_of_le_of_card_ge hP₀Q h3).symm.le
  set P : Sylow r G := Sylow.ofCard P₀ hsyl with hP
  have hPP₀ : (P : Subgroup G) = P₀ := Sylow.coe_ofCard _ _
  have hab : ∀ a ∈ (P : Subgroup G), ∀ b ∈ (P : Subgroup G), a * b = b * a := by
    rw [hPP₀]
    exact comm_of_isCyclic hP₀c
  have htop := hallPResidual_normalizer_eq_top hperf P (weaklyClosedIn_self P)
    (Or.inl (engelSymbol_eq_one_of_comm hr3 hab))
  rw [hPP₀] at htop
  have hx1 : x₀ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hxo
    exact (Fact.out : r.Prime).one_lt.ne hxo
  refine hallPResidual_ne_top (K₀ := ⊥) (H := M) (H₃ := M₁) (P₀ := P₀)
    (fun _ _ => by rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top _) bot_le
    (fun x hx => Subgroup.mem_sup_left ⟨hx, hNM hx⟩) hMpow
    (fun x hx => by
      have : x ∈ (⊥ : Subgroup G) := hx.2
      rw [Subgroup.mem_bot] at this
      rw [this]
      exact M₁.one_mem)
    (fun x hx => ⟨Subgroup.le_normalizer hx, hP₀M hx⟩) hP₀M₁
    (fun h => hx1 (by
      have : x₀ ∈ (⊥ : Subgroup G) := h ▸ hx₀
      exact (Subgroup.mem_bot).mp this)) hP₀r htop

namespace Hyp62

variable {r : ℕ} [Fact r.Prime] {J d x₀ y₀ : G} {P₀ P₁ M M₁ H₃ : Subgroup G}
  (h : Hyp62 r J d x₀ y₀ P₀ P₁ M M₁ H₃)
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

theorem le_centralizer_of_four {Q : Subgroup G} (hQ : IsPGroup r Q) {u v : G}
    (hu : orderOf u = 2) (hv : orderOf v = 2) (huv : u * v = v * u) (hne : u ≠ v)
    (huQ : u ∈ Subgroup.normalizer (Q : Set G)) (hvQ : v ∈ Subgroup.normalizer (Q : Set G)) :
    u ∈ Subgroup.centralizer (Q : Set G) := by
  have huu : u * u = 1 := by rw [← pow_two, ← hu, pow_orderOf_eq_one]
  have hvv : v * v = 1 := by rw [← pow_two, ← hv, pow_orderOf_eq_one]
  have hodd : Odd (Nat.card Q) := by
    obtain ⟨k, hk⟩ := hQ.exists_card_eq
    rw [hk]
    exact h.r_odd.pow
  have hN : ProperTwoGeneratedCore.LocalCriterionDenominator.denominatorFourGroup u v ≤
      Subgroup.normalizer (Q : Set G) := by
    rw [ProperTwoGeneratedCore.LocalCriterionDenominator.denominatorFourGroup, Subgroup.closure_le]
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

theorem factorization_two_le_of {Q : Subgroup G} (hQ : IsPGroup r Q)
    (hnc : ∀ t ∈ Subgroup.centralizer (Q : Set G), t * t = 1 → t = 1)
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
  have haC := h.le_centralizer_of_four hQ (hinv a ha ha1) (hinv b hb hb1)
    (h.two_comm T' hT'2 a ha b hb) hba.symm (hN (hTN ha)) (hN (hTN hb))
  exact ha1 (hnc a haC (h.two_sq T' hT'2 a ha))

theorem factorization_two_le {Q : Subgroup G} (hQ : IsPGroup r Q) (hPQ : P₀ ⊔ P₁ ≤ Q)
    {N : Subgroup G} (hN : N ≤ Subgroup.normalizer (Q : Set G)) :
    (Nat.card N).factorization 2 ≤ 1 :=
  h.factorization_two_le_of hQ (fun t ht ht2 =>
    h.CP t (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hPQ) ht) ht2) hN

theorem inf_centralizer_J {S : Subgroup G} (hS : IsPGroup r S) (hPS : P₀ ⊔ P₁ ≤ S) :
    S ⊓ Subgroup.centralizer ({J} : Set G) = P₀ := by
  have hle : P₀ ≤ S ⊓ Subgroup.centralizer ({J} : Set G) :=
    le_inf (le_sup_left.trans hPS) h.P₀_le
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  obtain ⟨k, hk⟩ := (hS.to_le (inf_le_left : S ⊓ Subgroup.centralizer ({J} : Set G) ≤ S)
    ).exists_card_eq
  have h1 : r ^ k ∣ Nat.card (Subgroup.centralizer ({J} : Set G)) :=
    hk ▸ Subgroup.card_dvd_of_le inf_le_right
  have h2 := (Nat.Prime.pow_dvd_iff_le_factorization Fact.out Nat.card_pos.ne').mp h1
  obtain ⟨a, ha⟩ := h.P₀_r.exists_card_eq
  rw [h.H_card, ha, Nat.factorization_pow_self Fact.out] at h2
  rw [hk, ha]
  exact Nat.pow_le_pow_right (Fact.out : r.Prime).pos h2

theorem exists_sylow : ∃ S : Subgroup G, P₀ ⊔ P₁ ≤ S ∧ IsPGroup r S ∧
    Nat.card S = r ^ (Nat.card G).factorization r ∧ J ∈ Subgroup.normalizer (S : Set G) := by
  classical
  obtain ⟨S, ⟨hPS, hSr, hJS⟩, hmax⟩ := Set.Finite.exists_maximalFor (fun S : Subgroup G =>
      Nat.card S) {S : Subgroup G | P₀ ⊔ P₁ ≤ S ∧ IsPGroup r S ∧
        J ∈ Subgroup.normalizer (S : Set G)} (Set.toFinite _)
      ⟨P₀ ⊔ P₁, le_rfl, h.isPGroup_P, h.J_mem_normalizer⟩
  refine ⟨S, hPS, hSr, ?_, hJS⟩
  refine card_eq_of_normalizer hSr fun Q hQ hSQ hQN => ?_
  set N := Subgroup.normalizer (S : Set G) with hNdef
  have hN2 : (Nat.card N).factorization 2 = 1 := by
    have hle := h.factorization_two_le hSr hPS (le_refl N)
    have hge : 1 ≤ (Nat.card N).factorization 2 := by
      have hJ2 : 2 ∣ Nat.card N := by
        have := Subgroup.orderOf_dvd_natCard N hJS
        rwa [h.orderOf_J] at this
      exact (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two Nat.card_pos.ne').mp hJ2
    omega
  obtain ⟨R, hR⟩ := exists_sylow_mem_normalizer_of_two (X := N) (ℓ := r) h.r_ne_two hN2
    (j := ⟨J, hJS⟩) (fun h1 => by
      have h2 : J = 1 := congrArg Subtype.val h1
      have h3 := h.orderOf_J
      rw [h2, orderOf_one] at h3
      exact absurd h3 (by norm_num))
    (Subtype.ext h.J_mul_J)
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
  have hmax' := hmax ⟨hPS.trans hSR, hR'r, hJR'⟩
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

end Hyp62

end CFSG.Walter.W67.Sec6
