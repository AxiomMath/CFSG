module

public import CFSG.Quasithin.Vol2.Ch4Sec4W4414

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Quasithin.A4
open scoped IsMulCommutative Pointwise

@[expose] def E22BorelFacts : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H S MH : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → QuasithinUnique.quasithinIsQTKECat G →
    pCoreOf 2 H ≠ ⊥ → 1 < E1.nParam H → QuasithinUnique.IsSylowTwoOf S H →
    IsUniqueMaxOver H S MH →
      (∃ P : Subgroup G, QuasithinUnique.IsSylowTwoOf P (MH ⊓ oTwoUpper H) ∧
        MH ⊓ oTwoUpper H ≤ Subgroup.normalizer (P : Set G)) ∧
      ∀ B : Subgroup G, B ≤ MH → Odd (Nat.card B) → (∃ k : ℕ, B.relIndex MH = 2 ^ k) →
        IsMulCommutative ↥B

theorem e22HallAbelian_of (h : E22BorelFacts) : E22HallAbelian :=
  fun G _ _ H S MH hs hnab hK hO hn hS hU => (h G H S MH hs hnab hK hO hn hS hU).2

@[expose] def Lemma4413NA : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H S MH : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → QuasithinUnique.quasithinIsQTKECat G →
    pCoreOf 2 H ≠ ⊥ → 1 < E1.nParam H → QuasithinUnique.IsSylowTwoOf S H →
    IsUniqueMaxOver H S MH →
      ∀ B : Subgroup G, B ≤ MH → Odd (Nat.card B) → (∃ k : ℕ, B.relIndex MH = 2 ^ k) →
        ∀ (p : ℕ) (A : Subgroup G), p.Prime → A ≤ B → IsElemAbelian p A →
          (A : Set G) * (S : Set G) = (S : Set G) * (A : Set G) →
            ¬ H ⊓ Subgroup.normalizer (A : Set G) ≤ MH

variable {G : Type} [Group G] [Finite G]

namespace Lemma4413

omit [Finite G] in
theorem sup_eq {H S MH X : Subgroup G} (hU : IsUniqueMaxOver H S MH) (hXH : X ≤ H)
    (hX : ¬ X ≤ MH) : H = MH ⊔ X := by
  obtain ⟨hmax, -, -⟩ := isUniqueMaxOver_iff.mp hU
  refine (hmax.2 (MH ⊔ X) (lt_of_le_of_ne le_sup_left fun e => hX ?_)
    (_root_.sup_le hmax.1.le hXH)).symm
  rw [e]
  exact le_sup_right

omit [Finite G] in
theorem card_mul_eq {B S : Subgroup G} (hBS : B ⊓ S = ⊥) :
    Nat.card ↥((B : Set G) * (S : Set G)) = Nat.card B * Nat.card S := by
  classical
  have hinj : Function.Injective (fun p : ↥B × ↥S => (p.1 : G) * p.2) := by
    rintro ⟨b₁, s₁⟩ ⟨b₂, s₂⟩ h
    simp only at h
    have h1 : (b₂ : G)⁻¹ * b₁ = s₂ * (s₁ : G)⁻¹ := by
      calc (b₂ : G)⁻¹ * b₁ = (b₂ : G)⁻¹ * (b₁ * s₁) * (s₁ : G)⁻¹ := by group
        _ = (b₂ : G)⁻¹ * (b₂ * s₂) * (s₁ : G)⁻¹ := by rw [h]
        _ = s₂ * (s₁ : G)⁻¹ := by group
    have hmem : (b₂ : G)⁻¹ * b₁ ∈ B ⊓ S :=
      ⟨B.mul_mem (B.inv_mem b₂.2) b₁.2, h1 ▸ S.mul_mem s₂.2 (S.inv_mem s₁.2)⟩
    rw [hBS, Subgroup.mem_bot] at hmem
    have hb : b₁ = b₂ := Subtype.ext (by
      have := congrArg (fun x => (b₂ : G) * x) hmem
      simpa using this)
    have hs : s₁ = s₂ := Subtype.ext (by
      rw [hb] at h
      exact mul_left_cancel h)
    rw [hb, hs]
  have hrange : Set.range (fun p : ↥B × ↥S => (p.1 : G) * p.2) =
      (B : Set G) * (S : Set G) := by
    ext x
    constructor
    · rintro ⟨⟨b, s⟩, rfl⟩
      exact ⟨b, b.2, s, s.2, rfl⟩
    · rintro ⟨b, hb, s, hs, rfl⟩
      exact ⟨(⟨b, hb⟩, ⟨s, hs⟩), rfl⟩
  rw [← hrange, Nat.card_range_of_injective hinj, Nat.card_prod]

theorem mul_eq {B S X : Subgroup G} (hBX : B ≤ X) (hBodd : Odd (Nat.card B))
    (hBi : ∃ k : ℕ, B.relIndex X = 2 ^ k) (hS : IsSylowTwoOf S X) :
    (B : Set G) * (S : Set G) = X ∧ (S : Set G) * (B : Set G) = X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hBi
  have hB2 : ¬ 2 ∣ Nat.card B := fun h =>
    (Nat.not_even_iff_odd.mpr hBodd) (even_iff_two_dvd.mpr h)
  have hBS : B ⊓ S = ⊥ := by
    refine Subgroup.eq_bot_of_card_eq _ ?_
    have h1 := Subgroup.card_dvd_of_le (inf_le_left : B ⊓ S ≤ B)
    have h2 : IsPGroup 2 ↥(B ⊓ S) := hS.2.1.to_le inf_le_right
    obtain ⟨j, hj⟩ := h2.exists_card_eq
    rw [hj] at h1 ⊢
    rcases j with _ | j
    · simp
    · exact absurd ((dvd_pow_self 2 (Nat.succ_ne_zero j)).trans h1) hB2
  have hcardX : Nat.card X = Nat.card B * 2 ^ k := by
    have h := Subgroup.relIndex_mul_card B X
    rw [inf_eq_left.mpr hBX, hk] at h
    rw [← h, mul_comm]
  have hcardS : Nat.card S = 2 ^ k := by
    obtain ⟨j, hj⟩ := hS.2.1.exists_card_eq
    have h1 := Subgroup.relIndex_mul_card S X
    rw [inf_eq_left.mpr hS.1, hj, hcardX] at h1
    have hodd : ¬ 2 ∣ S.relIndex X := hS.2.2
    have hcopB : Nat.Coprime (2 ^ j) (Nat.card B) :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hB2)
    have hcopR : Nat.Coprime (2 ^ k) (S.relIndex X) :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd)
    have hjk : 2 ^ j ∣ 2 ^ k :=
      hcopB.dvd_of_dvd_mul_left ⟨S.relIndex X, by rw [← h1, mul_comm]⟩
    have hkj : 2 ^ k ∣ 2 ^ j :=
      hcopR.dvd_of_dvd_mul_right ⟨Nat.card B, by rw [mul_comm (2 ^ j), h1, mul_comm]⟩
    rw [hj]
    exact Nat.dvd_antisymm hjk hkj
  have hle1 : (B : Set G) * (S : Set G) ⊆ X := by
    rintro _ ⟨b, hb, s, hs, rfl⟩
    exact X.mul_mem (hBX hb) (hS.1 hs)
  have hle2 : (S : Set G) * (B : Set G) ⊆ X := by
    rintro _ ⟨s, hs, b, hb, rfl⟩
    exact X.mul_mem (hS.1 hs) (hBX hb)
  have hc1 : Nat.card ↥((B : Set G) * (S : Set G)) = Nat.card X := by
    rw [card_mul_eq hBS, hcardS, hcardX]
  have hc2 : Nat.card ↥((S : Set G) * (B : Set G)) = Nat.card X := by
    rw [card_mul_eq (inf_comm B S ▸ hBS), hcardS, hcardX, mul_comm]
  have hfin : (X : Set G).Finite := Set.toFinite _
  refine ⟨Set.eq_of_subset_of_ncard_le hle1 ?_ hfin, Set.eq_of_subset_of_ncard_le hle2 ?_ hfin⟩
  · rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, hc1]
    exact le_rfl
  · rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, hc2]
    exact le_rfl

end Lemma4413

theorem stmt4_4_13_of (hE : E22BorelFacts) (hNA : Lemma4413NA) : Stmt4_4_13 := by
  intro G _ _ H S MH hs hnab hK hO hn hS hU
  obtain ⟨h2cl, hab⟩ := hE G H S MH hs hnab hK hO hn hS hU
  refine ⟨h2cl, fun B hBM hBo hBi => ⟨fun p A hp hAB hAel hAS => ?_, ?_⟩⟩
  · have hna := hNA G H S MH hs hnab hK hO hn hS hU B hBM hBo hBi p A hp hAB hAel hAS
    exact ⟨Lemma4413.sup_eq hU inf_le_left hna, hna⟩
  ·
    intro M Mp hM hSM hMH hMp hMpM hMN
    have hBc : IsMulCommutative ↥B := hab B hBM hBo hBi
    obtain ⟨-, hSMH, -⟩ := isUniqueMaxOver_iff.mp hU
    have hSyl : IsSylowTwoOf S MH :=
      ⟨hSMH, hS.2.1, fun h => hS.2.2 (h.trans (by
        have := Subgroup.relIndex_mul_relIndex S MH H hSMH
          (isUniqueMaxOver_iff.mp hU).1.1.le
        exact Dvd.intro _ this))⟩
    have hBS : (B : Set G) * (S : Set G) = (S : Set G) * (B : Set G) := by
      obtain ⟨h1, h2⟩ := Lemma4413.mul_eq hBM hBo hBi hSyl
      rw [h1, h2]
    have hBMM : B ≤ M := hBM.trans (hMH ▸ inf_le_left)
    have hMO : M ≤ Subgroup.normalizer (pCoreOf 2 Mp : Set G) :=
      hMN.trans (normalizer_le_normalizer_pCoreOf 2 Mp)
    set D := B ⊓ centralizerSection M Mp (pCoreOf 2 Mp) with hD
    have hset : (D : Set G) = {b | b ∈ B ∧ ∀ m ∈ Mp, b * m * b⁻¹ * m⁻¹ ∈ pCoreOf 2 Mp} := by
      ext x
      constructor
      · rintro ⟨hxB, -, -, -, hx⟩
        refine ⟨hxB, fun m hm => ?_⟩
        have := (pCoreOf 2 Mp).inv_mem (hx m hm)
        have e : (m * x * m⁻¹ * x⁻¹)⁻¹ = x * m * x⁻¹ * m⁻¹ := by group
        rwa [e] at this
      · rintro ⟨hxB, hx⟩
        refine ⟨hxB, hBMM hxB, hMN (hBMM hxB), hMO (hBMM hxB), fun m hm => ?_⟩
        have := (pCoreOf 2 Mp).inv_mem (hx m hm)
        have e : (x * m * x⁻¹ * m⁻¹)⁻¹ = m * x * m⁻¹ * x⁻¹ := by group
        rwa [e] at this
    rw [← hset]
    have hS2 : IsPGroup 2 ↥S := hS.2.1
    have h444 := eq_commutator_sup_of_wielandt wielandtCoprimeProduct_holds hS2 hBo hBS
    have hBN : B ≤ Subgroup.normalizer ((pCoreOf 2 (S ⊔ B) : Subgroup G) : Set G) :=
      le_sup_right.trans (le_normalizer_pCoreOf 2 (S ⊔ B))
    refine coe_mul_comm_of_eq_sup h444 (fun d hd => mem_normalizer_commutator
        (hBN hd.1) (Subgroup.le_normalizer hd.1)) (fun x hx => ?_)
      (fun x hx => mem_normalizer_commutator
        (le_sup_left.trans (le_normalizer_pCoreOf 2 (S ⊔ B)) hx.1) hx.2)
    exact mem_normalizer_inf hx.2
      (le_normalizer_centralizerSection' hMN (hSM hx.1))

end CFSG.Quasithin.H13.Ch4
