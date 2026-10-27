module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Inputs
public import CFSG.Quasithin.Vol2.Ch1Sec3Basic
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.OrderingMax

public section

namespace CFSG.Quasithin.H13.NQCore

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

@[expose] def Prop134Dich : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H S X P : Subgroup G) (p : ℕ) [Fact p.Prime],
    CFSG.SectionRank.IsSQTKCat ↥H → pCoreOf 2 H ≠ ⊥ → IsSylowTwoOf S H → X ≤ H → IsXi S X →
    p ≠ 2 → (∀ x ∈ X, x ^ p ∈ pCoreOf 2 X) → P ≤ X → IsPGroup p P →
    Nat.card P = (pCoreOf 2 X).relIndex X →
    H ≤ Subgroup.normalizer (X : Set G) ∨
    ∃ L ∈ cComp H, CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) ∧ X ≤ conjClosure L S

end CFSG.Quasithin.H13.NQCore

namespace CFSG.Quasithin.H13.Thm137

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

theorem pCoreOf_ne_bot_of_isXi (hEven : quasithinEvenCharacteristic G) {T X : Subgroup G}
    (hT : quasithinIsSylowTwo T) (hX : IsXi T X) : pCoreOf 2 X ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hO
  set Q := pCoreOf 2 (X ⊔ T) with hQ
  have hc2 : CharTwo (X ⊔ T) :=
    charTwo_of_inH hEven (hT.1.toSylow hT.2) ⟨le_sup_right, hX.2.2.1⟩
  have hXN : X ⊔ T ≤ Subgroup.normalizer (X : Set G) := sup_le Subgroup.le_normalizer hX.2.1
  have hQN : X ⊔ T ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X ⊔ T)
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (X ⊔ T)
  have hXQ : X ⊓ Q = ⊥ := by
    have h1 : X ⊓ Q ≤ pCoreOf 2 X :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
        (fun x hx => Subgroup.inf_normalizer_le_normalizer_inf
          ⟨Subgroup.le_normalizer hx, hQN (Subgroup.mem_sup_left hx)⟩)
        (hQ2.to_le inf_le_right)
    rw [hO] at h1
    exact le_bot_iff.mp h1
  have hXC : X ≤ Subgroup.centralizer (Q : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hqX : q * x⁻¹ * q⁻¹ ∈ X :=
      (Subgroup.mem_normalizer_iff.mp (hXN (CFSG.LieType.BorelTits.pCoreOf_le 2 (X ⊔ T) hq))
        _).mp (X.inv_mem hx)
    have hxQ : x * q * x⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hQN (Subgroup.mem_sup_left hx)) q).mp hq
    have hmem : x * q * x⁻¹ * q⁻¹ ∈ X ⊓ Q :=
      ⟨by simpa [mul_assoc] using X.mul_mem hx hqX, Q.mul_mem hxQ (Q.inv_mem hq)⟩
    rw [hXQ, Subgroup.mem_bot] at hmem
    have : x * q * x⁻¹ = q := by
      calc x * q * x⁻¹ = x * q * x⁻¹ * q⁻¹ * q := by group
        _ = q := by rw [hmem, one_mul]
    calc q * x = x * q * x⁻¹ * x := by rw [this]
      _ = x * q := by group
  have hXle : X ≤ X ⊓ Q := le_inf le_rfl fun x hx => hc2 ⟨Subgroup.mem_sup_left hx, hXC hx⟩
  rw [hXQ, le_bot_iff] at hXle
  obtain ⟨-, -, -, p, hp, -, -, hidx, -⟩ := hX
  have h1 : (pCoreOf 2 X).relIndex X = 1 := by
    rw [hXle]
    exact Subgroup.relIndex_bot_right _
  have hp1 : 1 < p := hp.one_lt
  rcases hidx with h | ⟨h, -⟩
  · rw [h1] at h
    have : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp1
    omega
  · rw [h1] at h
    have : 1 < p ^ 3 := Nat.one_lt_pow (by norm_num) hp1
    omega

theorem le_normalizer_of_isXiStar (hK : LocalSQTK G) (h134 : NQCore.Prop134Dich)
    {T X H : Subgroup G} (hT : quasithinIsSylowTwo T) (hX : IsXiStar T X) (hXTH : X ⊔ T ≤ H)
    (hH : pCoreOf 2 H ≠ ⊥) : H ≤ Subgroup.normalizer (X : Set G) := by
  obtain ⟨-, -, -, p, hp, hp2, hpow, hidx, -⟩ := hX.1
  have : Fact p.Prime := ⟨hp⟩
  have hTH : T ≤ H := le_sup_right.trans hXTH
  have hXH : X ≤ H := le_sup_left.trans hXTH
  have hS : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo hT hTH
  have hpX : p ∣ Nat.card X := by
    rw [card_eq_card_pCoreOf_mul_relIndex]
    refine Dvd.dvd.mul_left ?_ _
    rcases hidx with h | ⟨h, -⟩
    · rw [h]
      exact dvd_pow_self p two_ne_zero
    · rw [h]
      exact dvd_pow_self p three_ne_zero
  obtain ⟨P, hP, -⟩ := exists_isSylowIn_ge p (bot_le : (⊥ : Subgroup G) ≤ X) IsPGroup.of_bot
  rcases h134 G H T X P p (hK H hH) hH hS hXH hX.1 hp2 hpow hP.le hP.isPGroup
      (hX.1.card_sylow hp2 hpX hP) with hN | ⟨L, hL, hq, hXL⟩
  · exact hN
  · refine absurd (sup_le (hXL.trans ?_) le_sup_right) (hX.2 L
      (isLocal_of_mem_cComp_of_sylow hS hH hL) hq)
    exact conjClosure_le fun t ht l hl =>
      (L ⊔ T).mul_mem ((L ⊔ T).mul_mem (Subgroup.mem_sup_right ht) (Subgroup.mem_sup_left hl))
        ((L ⊔ T).inv_mem (Subgroup.mem_sup_right ht))

theorem input137_of_prop134Dich (h134 : NQCore.Prop134Dich) :
    EmptyFaithfulMultiple.Input137 := by
  intro G _ _ T hs hnab hQ hT X hX
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup G := hs
  obtain ⟨hK, hEven, -⟩ := qtkeCore_of_cat hnab hQ
  have key : ∀ H : Subgroup G, X ⊔ T ≤ H → pCoreOf 2 H ≠ ⊥ →
      H ≤ Subgroup.normalizer (X : Set G) := fun H hXTH hH =>
    le_normalizer_of_isXiStar hK h134 hT hX hXTH hH
  have hXTN : X ⊔ T ≤ Subgroup.normalizer (X : Set G) :=
    sup_le Subgroup.le_normalizer hX.1.2.1
  have hO := pCoreOf_ne_bot_of_isXi hEven hT hX.1
  have hNO : Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (pCoreOf 2 X : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X
  have hNloc : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 X : Set G)) :=
    ⟨pCoreOf 2 X, hO, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X, rfl⟩
  have hNeq : Subgroup.normalizer (X : Set G) = Subgroup.normalizer (pCoreOf 2 X : Set G) :=
    le_antisymm hNO (key _ (hXTN.trans hNO) (pCoreOf_ne_bot_of_isTwoLocal hNloc))
  have hMloc : IsTwoLocal (Subgroup.normalizer (X : Set G)) := hNeq ▸ hNloc
  have hMmax : quasithinIsMaxTwoLocal (Subgroup.normalizer (X : Set G)) :=
    ⟨hMloc, fun H hH hle =>
      le_antisymm (key H (hXTN.trans hle) (pCoreOf_ne_bot_of_isTwoLocal hH)) hle⟩
  exact ⟨⟨hMmax, hXTN⟩, fun M' hM' =>
    (hM'.1.2 _ hMloc (key M' hM'.2 (pCoreOf_ne_bot_of_isTwoLocal hM'.1.1))).symm⟩

end CFSG.Quasithin.H13.Thm137
