module

public import CFSG.Quasithin.Vol2.Ch1Sec3Basic
public import CFSG.Quasithin.Vol2.Ch5Sec1L34OddAbel
public import CFSG.Quasithin.Background.RonanD33

public section

namespace CFSG.Quasithin.H13.L827X

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G]

theorem not_commutator_R_le_U [Finite G] {T X X₁ U P : Subgroup G} {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hT : quasithinIsSylowTwo T) (hX : IsXi T X)
    (hP : IsSylowIn p P X) (hpX : p ∣ Nat.card X)
    (hX₁O : pCoreOf 2 X ≤ X₁) (hX₁X : X₁ ≤ X) (hX₁ne : X₁ ≠ pCoreOf 2 X)
    (hXC : X ≤ Subgroup.centralizer (U : Set G))
    (hCT : CharTwo (X ⊔ T)) :
    ¬ ⁅pCoreOf 2 X ⊔ U, X₁ ⊓ P⁆ ≤ U := by
  classical
  intro hR
  set O : Subgroup G := pCoreOf 2 X with hOdef
  set Q : Subgroup G := pCoreOf 2 (X ⊔ T) with hQdef
  set Y₁ : Subgroup G := X₁ ⊓ P with hY₁def
  have hO2 : IsPGroup 2 ↥O := pCoreOf_isPGroup 2 X
  have hQ2 : IsPGroup 2 ↥Q := pCoreOf_isPGroup 2 (X ⊔ T)
  have hY₁p : IsPGroup p ↥Y₁ := hP.isPGroup.to_le inf_le_right
  have hXN : X ≤ Subgroup.normalizer (O : Set G) := le_normalizer_pCoreOf 2 X
  have hXQ : X ≤ Subgroup.normalizer (Q : Set G) :=
    le_sup_left.trans (le_normalizer_pCoreOf 2 (X ⊔ T))
  have hXTX : X ⊔ T ≤ Subgroup.normalizer (X : Set G) :=
    sup_le (Subgroup.le_normalizer) hX.2.1
  have hQXT : Q ≤ X ⊔ T := pCoreOf_le 2 (X ⊔ T)
  have hY₁X : Y₁ ≤ X := inf_le_left.trans hX₁X
  have hYN : Y₁ ≤ Subgroup.normalizer (O : Set G) := hY₁X.trans hXN
  have hYQ : Y₁ ≤ Subgroup.normalizer (Q : Set G) := hY₁X.trans hXQ
  have hQX : ⁅Q, X⁆ ≤ Q ⊓ X := by
    rw [Subgroup.commutator_le]
    intro q hq x hx
    have e1 : ⁅q, x⁆ = q * (x * q⁻¹ * x⁻¹) := by
      rw [commutatorElement_def]
      group
    have e2 : ⁅q, x⁆ = (q * x * q⁻¹) * x⁻¹ := by
      rw [commutatorElement_def]
    refine ⟨?_, ?_⟩
    · rw [e1]
      exact Q.mul_mem hq ((Subgroup.mem_normalizer_iff.mp (hXQ hx) q⁻¹).mp (Q.inv_mem hq))
    · rw [e2]
      have hqX : q * x * q⁻¹ ∈ X :=
        (Subgroup.mem_normalizer_iff.mp (hXTX (hQXT hq)) x).mp hx
      exact X.mul_mem hqX (X.inv_mem hx)
  have hQXO : Q ⊓ X ≤ O := by
    refine CFSG.Quasithin.RonanD33.le_pCoreOf_of_le_normalizer inf_le_right ?_
      (hQ2.to_le inf_le_left)
    intro x hx
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hXQ hx, Subgroup.le_normalizer hx⟩
  have hUY : ⁅U, Y₁⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro u hu y hy
    rw [Subgroup.mem_bot]
    have hyC : y ∈ Subgroup.centralizer (U : Set G) := hXC (hY₁X hy)
    rw [Subgroup.mem_centralizer_iff] at hyC
    have := hyC u hu
    simp only [commutatorElement_def]
    calc u * y * u⁻¹ * y⁻¹ = (y * u) * u⁻¹ * y⁻¹ := by rw [this]
      _ = 1 := by group
  have hOY : ⁅O, Y₁⁆ ≤ U := (Subgroup.commutator_mono (le_sup_left : O ≤ O ⊔ U) le_rfl).trans hR
  have hcopO : Nat.Coprime (Nat.card ↥Y₁) (Nat.card ↥O) :=
    IsPGroup.coprime_card_of_ne p 2 hp2 Y₁ O hY₁p hO2
  have hOY1 : ⁅O, Y₁⁆ = ⊥ := by
    have h1 : ⁅⁅O, Y₁⁆, Y₁⁆ ≤ ⊥ := by
      have := Subgroup.commutator_mono hOY (le_refl Y₁)
      rw [hUY] at this
      exact this
    have h2 := coprime_commutator_commutator_eq (P := O) (X := Y₁) hYN hcopO
    have h3 : ⁅O, Y₁⁆ ≤ ⊥ := by
      rw [← h2]
      exact h1
    exact le_bot_iff.mp h3
  have hQY : ⁅Q, Y₁⁆ ≤ O := (Subgroup.commutator_mono le_rfl hY₁X).trans
    (hQX.trans hQXO)
  have hcopQ : Nat.Coprime (Nat.card ↥Y₁) (Nat.card ↥Q) :=
    IsPGroup.coprime_card_of_ne p 2 hp2 Y₁ Q hY₁p hQ2
  have hQY1 : ⁅Q, Y₁⁆ = ⊥ := by
    have h1 : ⁅⁅Q, Y₁⁆, Y₁⁆ ≤ ⊥ := by
      have := Subgroup.commutator_mono hQY (le_refl Y₁)
      rw [hOY1] at this
      exact this
    have h2 := coprime_commutator_commutator_eq (P := Q) (X := Y₁) hYQ hcopQ
    have h3 : ⁅Q, Y₁⁆ ≤ ⊥ := by
      rw [← h2]
      exact h1
    exact le_bot_iff.mp h3
  have hYQ' : Y₁ ≤ Q := by
    intro y hy
    have hyXT : y ∈ X ⊔ T := (le_sup_left : X ≤ X ⊔ T) (hY₁X hy)
    have hyC : y ∈ Subgroup.centralizer (Q : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      have hc : ⁅q, y⁆ = 1 := by
        have hmem : ⁅q, y⁆ ∈ ⁅Q, Y₁⁆ := Subgroup.commutator_mem_commutator hq hy
        rw [hQY1, Subgroup.mem_bot] at hmem
        exact hmem
      simp only [commutatorElement_def] at hc
      rw [mul_inv_eq_one] at hc
      calc q * y = (q * y * q⁻¹) * q := by group
        _ = y * q := by rw [hc]
    exact hCT ⟨hyXT, hyC⟩
  have hY₁bot : Y₁ = ⊥ := by
    have hY₁2 : IsPGroup 2 ↥Y₁ := hQ2.to_le hYQ'
    obtain ⟨a, ha⟩ := (IsPGroup.iff_card).mp hY₁2
    obtain ⟨b, hb⟩ := (IsPGroup.iff_card).mp hY₁p
    rw [Subgroup.card_eq_one.symm]
    rcases Nat.eq_zero_or_pos a with h0 | h0
    · rw [ha, h0, pow_zero]
    · exfalso
      have h2dvd : 2 ∣ p ^ b := by
        rw [← hb, ha]
        exact dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp h0)
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two (Fact.out : p.Prime)).mp
        (Nat.prime_two.dvd_of_dvd_pow h2dvd)
      exact hp2 this.symm
  apply hX₁ne
  apply le_antisymm _ hX₁O
  intro x hx
  have hsup := hX.pCoreOf_sup_eq hp2 hpX hP
  have hxs : x ∈ O ⊔ P := by rw [hsup]; exact hX₁X hx
  obtain ⟨o, ho, p', hp', rfl⟩ :=
    (Ch1Sec3.mem_sup_iff_of_le_normalizer (Q := O) (P := P) (hP.le.trans hXN)).1 hxs
  have hp'X₁ : p' ∈ X₁ := by
    have := X₁.mul_mem (X₁.inv_mem (hX₁O ho)) hx
    simpa using this
  have hp'Y : p' ∈ Y₁ := ⟨hp'X₁, hp'⟩
  rw [hY₁bot, Subgroup.mem_bot] at hp'Y
  rw [hp'Y, mul_one]
  exact ho

end CFSG.Quasithin.H13.L827X
