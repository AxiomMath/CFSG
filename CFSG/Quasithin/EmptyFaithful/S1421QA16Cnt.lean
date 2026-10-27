module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Data.Nat.Totient
public import Mathlib.Tactic.IntervalCases

public section

namespace CFSG.Quasithin

namespace Q16

variable {G : Type*} [Group G]

theorem card_modEq_card_inf_centralizer {p n : ℕ} [Fact p.Prime] (P : Subgroup G) [Finite P]
    {x : G} (hx : x ∈ Subgroup.normalizer (P : Set G)) (hxp : x ^ p ^ n = 1) :
    Nat.card P ≡ Nat.card ↥(P ⊓ Subgroup.centralizer {x}) [MOD p] := by
  classical
  have := Fintype.ofFinite P
  let σ : Equiv.Perm P := MulAut.toPerm P (P.normalizerMonoidHom ⟨x, hx⟩)
  have hσ : σ ^ p ^ n = 1 := by
    have h1 : (⟨x, hx⟩ : Subgroup.normalizer (P : Set G)) ^ p ^ n = 1 :=
      Subtype.ext (by simpa using hxp)
    show (MulAut.toPerm P) (P.normalizerMonoidHom ⟨x, hx⟩) ^ p ^ n = 1
    rw [← map_pow, ← map_pow, h1, map_one, map_one]
  have hmod := Equiv.Perm.card_compl_support_modEq hσ
  have hσy : ∀ y : P, ((σ y : P) : G) = x * y * x⁻¹ := fun y =>
    P.normalizerMonoidHom_apply_apply_coe ⟨x, hx⟩ y
  have hfix : ∀ y : P, y ∈ (σ.support)ᶜ ↔ x * (y : G) * x⁻¹ = y := by
    intro y
    rw [Finset.mem_compl, Equiv.Perm.mem_support, not_not, ← hσy y]
    exact Subtype.ext_iff
  let e : {y : P // y ∈ (σ.support)ᶜ} ≃ ↥(P ⊓ Subgroup.centralizer {x}) :=
    { toFun := fun y => ⟨y.1, Subgroup.mem_inf.mpr ⟨y.1.2, by
        have h := (hfix y.1).mp y.2
        rw [Subgroup.mem_centralizer_iff]
        intro h' hh'
        rw [Set.mem_singleton_iff] at hh'
        rw [hh']
        calc x * (y.1 : G) = (x * y.1 * x⁻¹) * x := by group
          _ = y.1 * x := by rw [h]⟩⟩
      invFun := fun z => ⟨⟨z.1, (Subgroup.mem_inf.mp z.2).1⟩, by
        rw [hfix]
        have := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp z.2).2 x (Set.mem_singleton x)
        calc x * (z.1 : G) * x⁻¹ = (z.1 * x) * x⁻¹ := by rw [this]
          _ = z.1 := by group⟩
      left_inv := fun y => rfl
      right_inv := fun z => rfl }
  have hcard : ((σ.support)ᶜ).card = Nat.card ↥(P ⊓ Subgroup.centralizer {x}) := by
    rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]
  have h2 : Nat.card P = Fintype.card P := Nat.card_eq_fintype_card
  rw [h2, ← hcard]
  exact hmod.symm

theorem eq_of_modEq_five {a c : ℕ} (ha : a ∣ 32) (hlt : a < 32) (hca : c ∣ a) (hc2 : 2 ∣ c)
    (hm : a ≡ c [MOD 5]) : c = a := by
  have hapos : 0 < a := Nat.pos_of_dvd_of_pos ha (by norm_num)
  have hcle : c ≤ a := Nat.le_of_dvd hapos hca
  unfold Nat.ModEq at hm
  interval_cases a <;> first | omega | (interval_cases c <;> omega)

theorem eq_two_or_eq_thirtyTwo_of_modEq_five {c : ℕ} (hc : c ∣ 32) (hc2 : 2 ∣ c)
    (hm : 32 ≡ c [MOD 5]) : c = 2 ∨ c = 32 := by
  have hcle : c ≤ 32 := Nat.le_of_dvd (by norm_num) hc
  unfold Nat.ModEq at hm
  interval_cases c <;> omega

variable [Finite G]

theorem le_centralizer_of_ne {Z P Q : Subgroup G} {x : G} (hQ : Nat.card Q = 32)
    (hZ : Nat.card Z = 2) (hZP : Z ≤ P) (hPQ : P ≤ Q) (hne : P ≠ Q)
    (hxP : x ∈ Subgroup.normalizer (P : Set G)) (hx5 : x ^ 5 = 1)
    (hZx : Z ≤ Subgroup.centralizer {x}) : P ≤ Subgroup.centralizer {x} := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hmod := card_modEq_card_inf_centralizer (p := 5) (n := 1) P hxP (by simpa using hx5)
  have hPdvd : Nat.card P ∣ 32 := hQ ▸ Subgroup.card_dvd_of_le hPQ
  have hPlt : Nat.card P < 32 := by
    refine lt_of_le_of_ne (Nat.le_of_dvd (by norm_num) hPdvd) fun h => hne ?_
    exact Subgroup.eq_of_le_of_card_ge hPQ (by omega)
  have hC1 : Nat.card ↥(P ⊓ Subgroup.centralizer {x}) ∣ Nat.card P :=
    Subgroup.card_dvd_of_le inf_le_left
  have hC2 : 2 ∣ Nat.card ↥(P ⊓ Subgroup.centralizer {x}) :=
    hZ ▸ Subgroup.card_dvd_of_le (le_inf hZP hZx)
  have heq := eq_of_modEq_five hPdvd hPlt hC1 hC2 hmod
  have hCP : P ⊓ Subgroup.centralizer {x} = P :=
    Subgroup.eq_of_le_of_card_ge inf_le_left (by omega)
  exact inf_eq_left.mp hCP

theorem le_centralizer_of_ne_ne {Z W Q : Subgroup G} {x : G} (hQ : Nat.card Q = 32)
    (hZ : Nat.card Z = 2) (hZW : Z ≤ W) (hWQ : W ≤ Q) (hWZ : W ≠ Z) (hWQ' : W ≠ Q)
    (hxW : x ∈ Subgroup.normalizer (W : Set G)) (hxQ : x ∈ Subgroup.normalizer (Q : Set G))
    (hx5 : x ^ 5 = 1) (hZx : Z ≤ Subgroup.centralizer {x}) : Q ≤ Subgroup.centralizer {x} := by
  have hWx : W ≤ Subgroup.centralizer {x} := le_centralizer_of_ne hQ hZ hZW hWQ hWQ' hxW hx5 hZx
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hmod := card_modEq_card_inf_centralizer (p := 5) (n := 1) Q hxQ (by simpa using hx5)
  rw [hQ] at hmod
  have hC1 : Nat.card ↥(Q ⊓ Subgroup.centralizer {x}) ∣ 32 :=
    hQ ▸ Subgroup.card_dvd_of_le inf_le_left
  have hZC : Z ≤ Q ⊓ Subgroup.centralizer {x} := le_inf (hZW.trans hWQ) hZx
  have hC2 : 2 ∣ Nat.card ↥(Q ⊓ Subgroup.centralizer {x}) :=
    hZ ▸ Subgroup.card_dvd_of_le hZC
  have hW2 : 2 ∣ Nat.card W := hZ ▸ Subgroup.card_dvd_of_le hZW
  have hWpos : 0 < Nat.card W := Nat.card_pos
  have hW2' : Nat.card W ≠ 2 := fun h =>
    hWZ (Subgroup.eq_of_le_of_card_ge hZW (by omega)).symm
  have hWC : Nat.card W ≤ Nat.card ↥(Q ⊓ Subgroup.centralizer {x}) :=
    Subgroup.card_le_of_le (le_inf hWQ hWx)
  have h32 : Nat.card ↥(Q ⊓ Subgroup.centralizer {x}) = 32 := by
    rcases eq_two_or_eq_thirtyTwo_of_modEq_five hC1 hC2 hmod with h | h
    · omega
    · exact h
  have hCQ : Q ⊓ Subgroup.centralizer {x} = Q :=
    Subgroup.eq_of_le_of_card_ge inf_le_left (by omega)
  exact inf_eq_left.mp hCQ

end Q16

end CFSG.Quasithin
