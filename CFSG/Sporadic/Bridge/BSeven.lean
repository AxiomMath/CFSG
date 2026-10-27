module

public import CFSG.Monster.B.Pinned.Primes.SixPrimes
public import CFSG.Sporadic.Bridge.BData
public import Certificates.Certificate3109
public meta import CFSG.Sporadic.Bridge.BData
public import CFSG.Certificates.Kernel.BabyMonster.Sound
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2Fast
public import CFSG.Monster.B.Cbar.SimpleBase
public import CFSG.Monster.B.Max2.Pinned
public import CFSG.Monster.B.Pinned.Primes.SeedGL
public import Certificates.Certificate3101
public import Certificates.Certificate3103
public import Certificates.Certificate3106
public import Certificates.Certificate3109Base
public import Certificates.Data.CFSGNative.MonsterB.DyadicFile

public section

namespace CFSG.Sporadic.Bridge.B

open CFSG.Blueprint CFSG.Monster.B CFSG.Monster.B.Pinned CFSG.Monster.B.Bin
  CFSG.Monster.B.Primes.Native

theorem prime_sq_dvd_card {G : Type*} [Group G] {p : ℕ} [hp : Fact p.Prime] {x y : G}
    (hx : x ^ p = 1) (hy : y ^ p = 1) (hc : x * y = y * x) (hx1 : x ≠ 1)
    (hyx : ∀ k : ℕ, k < p → y ≠ x ^ k) : p ^ 2 ∣ Nat.card G := by
  have hxo : orderOf x = p := orderOf_eq_prime hx hx1
  have hxy : ∀ m n : ℕ, y ^ n * x ^ m = x ^ m * y ^ n := fun m n =>
    ((Commute.pow_pow (Commute.symm (show Commute x y from hc)) n m)).eq
  let f : Multiplicative (ZMod p) × Multiplicative (ZMod p) →* G :=
    { toFun := fun a => x ^ (Multiplicative.toAdd a.1).val * y ^ (Multiplicative.toAdd a.2).val
      map_one' := by simp
      map_mul' := fun a b => by
        simp only [Prod.fst_mul, Prod.snd_mul, toAdd_mul, ZMod.val_add]
        rw [← pow_eq_pow_mod _ hx, ← pow_eq_pow_mod _ hy, pow_add, pow_add]
        calc x ^ (Multiplicative.toAdd a.1).val * x ^ (Multiplicative.toAdd b.1).val *
              (y ^ (Multiplicative.toAdd a.2).val * y ^ (Multiplicative.toAdd b.2).val)
            = x ^ (Multiplicative.toAdd a.1).val * (x ^ (Multiplicative.toAdd b.1).val *
              y ^ (Multiplicative.toAdd a.2).val) * y ^ (Multiplicative.toAdd b.2).val := by
              simp only [mul_assoc]
          _ = x ^ (Multiplicative.toAdd a.1).val * (y ^ (Multiplicative.toAdd a.2).val *
              x ^ (Multiplicative.toAdd b.1).val) * y ^ (Multiplicative.toAdd b.2).val := by
              rw [hxy]
          _ = _ := by simp only [mul_assoc] }
  have hf : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨a, b⟩ hab
    rw [MonoidHom.mem_ker] at hab
    change x ^ (Multiplicative.toAdd a).val * y ^ (Multiplicative.toAdd b).val = 1 at hab
    rw [Subgroup.mem_bot]
    set i := Multiplicative.toAdd a with hi
    set j := Multiplicative.toAdd b with hj
    have hip : i.val < p := ZMod.val_lt i
    have hjp : j.val < p := ZMod.val_lt j
    by_cases hj0 : j = 0
    · rw [hj0, ZMod.val_zero, pow_zero, mul_one] at hab
      have hdvd : orderOf x ∣ i.val := orderOf_dvd_of_pow_eq_one hab
      rw [hxo] at hdvd
      have hi0 : i.val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hip
      have : i = 0 := (ZMod.val_eq_zero i).1 hi0
      refine Prod.ext ?_ ?_
      · show a = 1
        apply Multiplicative.toAdd.injective
        rw [toAdd_one]; exact this
      · show b = 1
        apply Multiplicative.toAdd.injective
        rw [toAdd_one]; exact hj0
    · exfalso
      have hjv : 0 < j.val := Nat.pos_of_ne_zero (fun h => hj0 ((ZMod.val_eq_zero j).1 h))
      have hyj : y ^ j.val = x ^ (p - i.val) := by
        have h1 : x ^ (p - i.val) * x ^ i.val = 1 := by
          rw [← pow_add, Nat.sub_add_cancel hip.le, hx]
        calc y ^ j.val = (x ^ (p - i.val) * x ^ i.val) * y ^ j.val := by rw [h1, one_mul]
          _ = x ^ (p - i.val) * (x ^ i.val * y ^ j.val) := by rw [mul_assoc]
          _ = x ^ (p - i.val) := by rw [hab, mul_one]
      have hcop : Nat.Coprime j.val p :=
        ((Nat.Prime.coprime_iff_not_dvd hp.out).2 fun hd =>
          absurd (Nat.le_of_dvd hjv hd) (by omega)).symm
      obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.out.one_lt
      have hy1 : y = x ^ ((p - i.val) * m % p) := by
        calc y = y ^ 1 := (pow_one y).symm
          _ = y ^ (j.val * m % p) := by rw [hm]
          _ = y ^ (j.val * m) := (pow_eq_pow_mod _ hy).symm
          _ = (y ^ j.val) ^ m := pow_mul y _ _
          _ = (x ^ (p - i.val)) ^ m := by rw [hyj]
          _ = x ^ ((p - i.val) * m) := (pow_mul x _ _).symm
          _ = x ^ ((p - i.val) * m % p) := pow_eq_pow_mod _ hx
      exact hyx _ (Nat.mod_lt _ hp.out.pos) hy1
  have hcard : Nat.card (Multiplicative (ZMod p) × Multiplicative (ZMod p)) = p ^ 2 := by
    rw [Nat.card_prod]
    simp [Nat.card_eq_fintype_card, sq]
  have := Subgroup.card_subgroup_dvd_card f.range
  rwa [Nat.card_congr (MonoidHom.ofInjective hf).toEquiv.symm, hcard] at this

theorem prime_sq_dvd_card_subgroup {G : Type*} [Group G] (H : Subgroup G) {p : ℕ} [Fact p.Prime]
    {x y : G} (hxH : x ∈ H) (hyH : y ∈ H) (hx : x ^ p = 1) (hy : y ^ p = 1)
    (hc : x * y = y * x) (hx1 : x ≠ 1) (hyx : ∀ k : ℕ, k < p → y ≠ x ^ k) :
    p ^ 2 ∣ Nat.card H := by
  refine prime_sq_dvd_card (x := (⟨x, hxH⟩ : H)) (y := (⟨y, hyH⟩ : H)) ?_ ?_ ?_ ?_ ?_
  · exact Subtype.ext (by simpa using hx)
  · exact Subtype.ext (by simpa using hy)
  · exact Subtype.ext (by simpa using hc)
  · intro h; exact hx1 (by simpa using congrArg Subtype.val h)
  · intro k hk h
    exact hyx k hk (by simpa using congrArg Subtype.val h)

theorem sevenProg_lt : ∀ ins ∈ sevenProg, ins.lt sevenN = true := by decide +kernel

end CFSG.Sporadic.Bridge.B
