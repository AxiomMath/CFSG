module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3Sp4
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C1Blocks
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10KH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

theorem exists_lift_orderOf {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (α : X →* alternatingGroup (Fin 5)) (hαk : α.ker = CFSG.pCore 2 X) (y₀ : X)
    (hσp : (α y₀) ^ p = 1) (hσ1 : α y₀ ≠ 1) :
    ∃ k : ℕ, orderOf (y₀ ^ (2 ^ k)) = p ∧ α (y₀ ^ (2 ^ k)) = (α y₀) ^ (2 ^ k) := by
  have : Fact p.Prime := ⟨hp⟩
  have hy₀p : y₀ ^ p ∈ CFSG.pCore 2 X := by
    rw [← hαk, MonoidHom.mem_ker, map_pow]
    exact hσp
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (G := X) (p := 2)) ⟨y₀ ^ p, hy₀p⟩
  have hk' : (y₀ ^ p) ^ (2 ^ k) = 1 := congrArg Subtype.val hk
  refine ⟨k, ?_, map_pow α y₀ (2 ^ k)⟩
  have hyp : (y₀ ^ (2 ^ k)) ^ p = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]
    exact hk'
  have hy1 : y₀ ^ (2 ^ k) ≠ 1 := by
    intro h1
    have h2 : (α y₀) ^ (2 ^ k) = 1 := by rw [← map_pow, h1, map_one]
    apply hσ1
    have h3 : orderOf (α y₀) ∣ p := orderOf_dvd_of_pow_eq_one hσp
    have h4 : orderOf (α y₀) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h2
    have h5 : orderOf (α y₀) ∣ Nat.gcd p (2 ^ k) := Nat.dvd_gcd h3 h4
    have h6 : Nat.gcd p (2 ^ k) = 1 :=
      Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
    rw [h6] at h5
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h5)
  exact orderOf_eq_prime hyp hy1

theorem fixed_pow {w : Fin 5 → ZMod 2} {σ : Equiv.Perm (Fin 5)} (hσ : ∀ i, w (σ⁻¹ i) = w i) :
    ∀ m : ℕ, ∀ i, w (((σ ^ m)⁻¹ : Equiv.Perm (Fin 5)) i) = w i := by
  intro m
  induction m with
  | zero => intro i; simp
  | succ m ih =>
    intro i
    rw [pow_succ, _root_.mul_inv_rev, Equiv.Perm.mul_apply, hσ ((σ ^ m)⁻¹ i), ih i]

section Block

variable {G : Type} [Group G] [Finite G] {B : Subgroup G}

@[expose] def AltCompat (α : ↥B →* alternatingGroup (Fin 5))
    (β : ↥(blockU B) →* Multiplicative (evenWeight 5)) : Prop :=
  ∀ ℓ : ↥B, ∀ u v : ↥(blockU B), (v : G) = ℓ * u * ℓ⁻¹ → ∀ i : Fin 5,
    ((Multiplicative.toAdd (β v) : evenWeight 5) : Fin 5 → ZMod 2) i =
      ((Multiplicative.toAdd (β u) : evenWeight 5) : Fin 5 → ZMod 2)
        ((α ℓ : Equiv.Perm (Fin 5))⁻¹ i)

theorem conj_mem_blockU (ℓ : ↥B) (u : ↥(blockU B)) :
    (ℓ : G) * u * (ℓ : G)⁻¹ ∈ blockU B :=
  (Subgroup.mem_normalizer_iff.mp (C1.le_normalizer_blockU B ℓ.2) u).mp u.2

theorem conj_eq_of_fixed {α : ↥B →* alternatingGroup (Fin 5)}
    {β : ↥(blockU B) →* Multiplicative (evenWeight 5)} (hβinj : Function.Injective β)
    (hβe : AltCompat α β) (ℓ : ↥B) (u : ↥(blockU B))
    (hfix : ∀ i, ((Multiplicative.toAdd (β u) : evenWeight 5) : Fin 5 → ZMod 2)
      ((α ℓ : Equiv.Perm (Fin 5))⁻¹ i) =
        ((Multiplicative.toAdd (β u) : evenWeight 5) : Fin 5 → ZMod 2) i) :
    (ℓ : G) * u * (ℓ : G)⁻¹ = u := by
  set v : ↥(blockU B) := ⟨(ℓ : G) * u * (ℓ : G)⁻¹, conj_mem_blockU ℓ u⟩ with hv
  have h2 : β v = β u := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    funext i
    rw [hβe ℓ u v rfl i, hfix i]
  have h3 : v = u := hβinj h2
  exact congrArg Subtype.val h3

omit [Finite G] in
theorem fixed_of_conj_eq {α : ↥B →* alternatingGroup (Fin 5)}
    {β : ↥(blockU B) →* Multiplicative (evenWeight 5)} (hβe : AltCompat α β) (ℓ : ↥B)
    (u : ↥(blockU B)) (h : (ℓ : G) * u * (ℓ : G)⁻¹ = u) :
    ∀ i, ((Multiplicative.toAdd (β u) : evenWeight 5) : Fin 5 → ZMod 2)
      ((α ℓ : Equiv.Perm (Fin 5))⁻¹ i) =
        ((Multiplicative.toAdd (β u) : evenWeight 5) : Fin 5 → ZMod 2) i :=
  fun i => (hβe ℓ u u h.symm i).symm

theorem exists_three_centralizing {α : ↥B →* alternatingGroup (Fin 5)}
    (hαs : Function.Surjective α) (hαk : α.ker = CFSG.pCore 2 ↥B)
    {β : ↥(blockU B) →* Multiplicative (evenWeight 5)} (hβinj : Function.Injective β)
    (hβe : AltCompat α β) (u : ↥(blockU B)) :
    ∃ y : ↥B, orderOf y = 3 ∧ (y : G) * u * (y : G)⁻¹ = u := by
  classical
  set w : Fin 5 → ZMod 2 := ((Multiplicative.toAdd (β u) : evenWeight 5) : Fin 5 → ZMod 2)
    with hw
  have hwe : ∑ i, w i = 0 := (A5.Delta5.mem_evenWeight_iff w).1 (Multiplicative.toAdd (β u)).2
  have hσ : ∃ σ : Equiv.Perm (Fin 5), Equiv.Perm.sign σ = 1 ∧ σ ≠ 1 ∧ σ ^ 3 = 1 ∧
      ∀ i, w (σ⁻¹ i) = w i := by
    by_cases hw0 : w = 0
    · obtain ⟨σ, h1, h2, h3, -⟩ := A5.G3.exists_order_three_fixing ![1, 1, 0, 0, 0]
        (by decide) (by decide)
      exact ⟨σ, h1, h2, h3, fun i => by rw [hw0]; rfl⟩
    · exact A5.G3.exists_order_three_fixing w hwe hw0
  obtain ⟨σ, hsign, hσ1, hσ3, hσfix⟩ := hσ
  set σ' : alternatingGroup (Fin 5) := ⟨σ, Equiv.Perm.mem_alternatingGroup.mpr hsign⟩
  obtain ⟨y₀, hy₀⟩ := hαs σ'
  obtain ⟨k, hk3, hkα⟩ := exists_lift_orderOf Nat.prime_three (by norm_num) α hαk y₀
    (by rw [hy₀]; exact Subtype.ext (by simpa using hσ3))
    (by rw [hy₀]; exact fun h => hσ1 (congrArg Subtype.val h))
  refine ⟨y₀ ^ (2 ^ k), hk3, conj_eq_of_fixed hβinj hβe _ u fun i => ?_⟩
  have hαv : ((α (y₀ ^ (2 ^ k)) : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) =
      σ ^ (2 ^ k) := by
    rw [hkα, hy₀]
    rfl
  rw [hαv]
  exact fixed_pow hσfix _ i

end Block

end CFSG.Quasithin.Vol2.Ch10.SecF.C10KH
