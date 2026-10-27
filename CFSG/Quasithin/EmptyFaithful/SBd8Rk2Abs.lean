module

public import CFSG.Quasithin.Background.GoldschmidtS146RLat
public import CFSG.Quasithin.EmptyFaithful.SBd8Mod
public import CFSG.Quasithin.EmptyFaithful.SBd8NS

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace SBd8

section Rank2

theorem not_isSolvable_of_simple_of_not_prime {Q : Type} [Group Q] [Finite Q] (hs : IsSimpleGroup Q)
    (hc : ¬ (Nat.card Q).Prime) : ¬ Group.IsSolvable Q := by
  intro hsol
  have hcomm : ∀ a b : Q, a * b = b * a := IsSimpleGroup.comm_iff_isSolvable.2 hsol
  let _ : CommGroup Q := { (inferInstance : Group Q) with mul_comm := hcomm }
  exact hc IsSimpleGroup.prime_card

theorem ordL2_not_prime {m : ℕ} (hm : 2 ≤ m) : ¬ (GoldS146R.ordL2 m).Prime := by
  intro hp
  unfold GoldS146R.ordL2 at hp
  have h4 : 4 ≤ 2 ^ m := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have h2 : 2 ∣ 2 ^ m * ((2 ^ m) ^ 2 - 1) := Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _
  have h2' := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h2
  have h5 : 2 ^ m * ((2 ^ m) ^ 2 - 1) ≥ 4 * 15 := by
    have : (2 ^ m) ^ 2 - 1 ≥ 15 := by
      have : (2 ^ m) ^ 2 ≥ 16 := by nlinarith
      omega
    nlinarith
  omega

theorem three_dvd_ordL2 (m : ℕ) : 3 ∣ GoldS146R.ordL2 m := by
  unfold GoldS146R.ordL2
  apply Dvd.dvd.mul_left
  have h4 : (2 ^ m) ^ 2 = 4 ^ m := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [h4]
  have : 4 ^ m % 3 = 1 := by rw [Nat.pow_mod]; norm_num
  have h1 : 1 ≤ 4 ^ m := Nat.one_le_pow _ _ (by norm_num)
  omega

variable {X : Type} [Group X] [Finite X]

theorem rank2_false {A : Subgroup (MulAut X)} {U K : Subgroup X} (d : OvgData X A U K)
    (hshape : GoldS146R.LatShape X U)
    (hsolv : ∀ Y : Subgroup X, U ≤ Y → Group.IsSolvable ↥Y → Y ≤ Subgroup.normalizer (U : Set X))
    (hBne : Subgroup.normalizer (U : Set X) ≠ ⊤)
    (hB : 3 ∣ Nat.card ↥(Subgroup.normalizer (U : Set X)) →
      9 ∣ Nat.card ↥(Subgroup.normalizer (U : Set X))) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKB : K ≤ Subgroup.normalizer (U : Set X) := by
    rcases hshape K d.U_le d.K_ne with h | h | ⟨m, hm, hns, Q, _, π, hπ, hker, hQ, hcard⟩
    · exact h
    ·
      obtain ⟨a, ha⟩ := (IsPGroup.iff_card (p := 2)).1 d.U_syl.2.1
      have hKs : Group.IsSolvable ↥K := by
        have := Fintype.ofFinite ↥K
        exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow (a := a)
          (b := 1) Nat.prime_two Nat.prime_three (by norm_num)
          (by rw [← Nat.card_eq_fintype_card, h, ha]; ring)
      exact hsolv K d.U_le hKs
    · exfalso
      have : Finite Q := Finite.of_surjective π hπ
      have hns' : ¬ Group.IsSolvable Q :=
        not_isSolvable_of_simple_of_not_prime hQ (by rw [hcard]; exact ordL2_not_prime hm)
      exact false_of_surjective_of_solvable_oPrime (perfectCore_le K) d.Y_solv π hπ
        (normal_solvable_eq_bot_of_simple hQ hns') (by rw [hcard]; exact three_dvd_ordL2 m)
  have hBinv : ∀ α ∈ A, (Subgroup.normalizer (U : Set X)).map α.toMonoidHom =
      Subgroup.normalizer (U : Set X) := by
    intro α hα
    rw [Subgroup.map_equiv_normalizer_eq U α, d.A_U α hα]
  have hKeq : K = Subgroup.normalizer (U : Set X) :=
    le_antisymm hKB (d.K_max _ hKB hBne hBinv)
  exact d.not_nine (hKeq ▸ hB (hKeq ▸ d.three_dvd))

end Rank2

end SBd8

end CFSG.Quasithin
