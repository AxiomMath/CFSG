module

public import CFSG.Assembly.Defs
public import CFSG.RankThree.PartOne.K1214.SylowShape

public section

namespace CFSG.RankThree.PartOne.K128

open Subgroup CFSG.RankThree.PartOne.K1214

theorem pow_eq_one_of_pow_eq_one_of_not_dvd {G : Type*} [Group G] {p k e m : ℕ} (hp : p.Prime)
    {x : G} (hk : x ^ (p ^ k) = 1) (hm : x ^ m = 1) (hnd : ¬ p ^ (e + 1) ∣ m) :
    x ^ (p ^ e) = 1 := by
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 (orderOf_dvd_of_pow_eq_one hk)
  have h1 : orderOf x ∣ m := orderOf_dvd_of_pow_eq_one hm
  have hje : j ≤ e := by
    by_contra hlt
    exact hnd ((pow_dvd_pow p (by omega : e + 1 ≤ j)).trans (hj ▸ h1))
  exact orderOf_dvd_iff_pow_eq_one.1 (hj ▸ pow_dvd_pow p hje)

@[expose] def piFinTwoMulEquiv (X : Type*) [Group X] : (Fin 2 → X) ≃* X × X where
  toFun f := (f 0, f 1)
  invFun p := ![p.1, p.2]
  left_inv f := by
    funext i
    fin_cases i <;> rfl
  right_inv p := rfl
  map_mul' f g := rfl

theorem nonempty_mulEquiv_zmod_of_card {G : Type*} [Group G] [IsCyclic G] {n : ℕ}
    (h : Nat.card G = n) : Nonempty (G ≃* Multiplicative (ZMod n)) := by
  subst h
  exact ⟨(zmodCyclicMulEquiv ‹IsCyclic G›).symm⟩

theorem sylowShape_of_embeds {p e m₁ m₂ : ℕ} (hp : p.Prime) {L : Type*} [Field L] {G : Type*}
    [Group G] [Finite G] (hord : (Nat.card G).factorization p = 2 * e)
    (hm₁ : ¬ p ^ (e + 1) ∣ m₁) (hm₂ : ¬ p ^ (e + 1) ∣ m₂)
    (h : ∀ Q : Subgroup G, IsPGroup p Q → ∃ Φ : Q →* Lˣ × Lˣ, Function.Injective Φ ∧
      ∀ y, (Φ y).1 ^ m₁ = 1 ∧ (Φ y).2 ^ m₂ = 1) :
    SylowShape p 2 e G := by
  classical
  intro S hS hidx
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero (p ^ e) := ⟨pow_ne_zero _ hp.ne_zero⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hS
  have hk2 : k = 2 * e := by
    have h1 := Subgroup.card_mul_index S
    have hidx0 : S.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have h2 := congrArg (fun n => n.factorization p) h1
    rw [Nat.factorization_mul (Nat.card_pos.ne') hidx0, hk, Nat.Prime.factorization_pow hp] at h2
    simp only [Finsupp.add_apply, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd hidx, add_zero] at h2
    omega
  obtain ⟨Φ, hΦ, hΦm⟩ := h S hS
  have hpk : ∀ y : S, y ^ (p ^ k) = 1 := fun y => by
    have : Nat.card S = p ^ k := hk
    rw [← this]
    exact pow_card_eq_one'
  let R : Subgroup Lˣ := rootsOfUnity (p ^ e) L
  have hx : ∀ y : S, Φ y ^ (p ^ k) = 1 := fun y => by rw [← map_pow, hpk y, map_one]
  have h1 : ∀ y : S, (Φ y).1 ∈ R := fun y => by
    rw [mem_rootsOfUnity]
    exact pow_eq_one_of_pow_eq_one_of_not_dvd hp (k := k) (by simpa using congrArg Prod.fst (hx y))
      (hΦm y).1 hm₁
  have h2 : ∀ y : S, (Φ y).2 ∈ R := fun y => by
    rw [mem_rootsOfUnity]
    exact pow_eq_one_of_pow_eq_one_of_not_dvd hp (k := k) (by simpa using congrArg Prod.snd (hx y))
      (hΦm y).2 hm₂
  let Ψ : S →* R × R :=
    (((MonoidHom.fst Lˣ Lˣ).comp Φ).codRestrict R h1).prod
      (((MonoidHom.snd Lˣ Lˣ).comp Φ).codRestrict R h2)
  have hΨ : Function.Injective Ψ := by
    intro a b hab
    apply hΦ
    exact Prod.ext (congrArg (fun z => ((z.1 : R) : Lˣ)) hab)
      (congrArg (fun z => ((z.2 : R) : Lˣ)) hab)
  have hRle : Nat.card R ≤ p ^ e := card_rootsOfUnity L (p ^ e)
  have hSle : Nat.card S ≤ Nat.card R ^ 2 := by
    calc Nat.card S ≤ Nat.card (R × R) := Nat.card_le_card_of_injective _ hΨ
      _ = Nat.card R ^ 2 := by rw [Nat.card_prod, sq]
  have hSc : Nat.card S = p ^ (2 * e) := by rw [hk, hk2]
  have hRc : Nat.card R = p ^ e := by
    refine le_antisymm hRle ?_
    by_contra hlt
    have hlt' : Nat.card R < p ^ e := not_le.1 hlt
    have : Nat.card R ^ 2 < (p ^ e) ^ 2 := Nat.pow_lt_pow_left hlt' (by norm_num)
    rw [← pow_mul, mul_comm] at this
    omega
  have hbij : Function.Bijective Ψ := by
    refine ⟨hΨ, ?_⟩
    have hle : Nat.card (R × R) ≤ Nat.card S := by
      rw [Nat.card_prod, hRc, hSc, ← pow_add, ← two_mul, mul_comm]
    exact (Function.Injective.bijective_of_nat_card_le hΨ hle).2
  obtain ⟨eR⟩ := nonempty_mulEquiv_zmod_of_card (G := R) hRc
  exact ⟨(MulEquiv.ofBijective Ψ hbij).trans
    (((eR.prodCongr eR).trans (piFinTwoMulEquiv (Multiplicative (ZMod (p ^ e)))).symm))⟩

end CFSG.RankThree.PartOne.K128
