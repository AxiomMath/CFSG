
module

public import CFSG.Sporadic.Schreier.J4SLocalNodesBase

public import CFSG.Sporadic.Schreier.J4SGLBase1
public import CFSG.Sporadic.Schreier.J4SNative
public import CFSG.Sporadic.Schreier.J4SCols
public import CFSG.Sporadic.Schreier.J4SOrbits
public meta import CFSG.Sporadic.Schreier.J4SOrbits
public import CFSG.Sporadic.J4.Local

@[expose] public noncomputable section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.J4 CFSG.Sporadic.GLQ CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
open scoped Matrix

theorem fam_J4_local_elementary_abelian_subgroup :
    (∀ j, u j ^ 2 = 1 ∧ u j ≠ 1) ∧ (∀ i j, u i * u j = u j * u i) ∧
      (∀ i k, η (i ^^^ k) = η i * η k) ∧ Set.BijOn η (Set.Iio 2048) N ∧
      (∃ e : Multiplicative (Fin 11 → ZMod 2) ≃* N,
        ∀ i, (e (Multiplicative.ofAdd (toVecD 11 i)) : J) = η i) ∧
      Nat.card N = 2048 ∧ x ∈ Subgroup.normalizer (N : Set J) ∧
      y ∈ Subgroup.normalizer (N : Set J) ∧
      (∀ j, ∃ w : List ℤ, u j = (signedWord x y w)⁻¹ * z * signedWord x y w) ∧
      N ≤ H ∧ (N.subgroupOf H).Normal := by
  refine ⟨fun j => ⟨u_sq j, u_ne_one j⟩, fun i j => u_comm i j, η_xor,
    ⟨fun i _ => η_mem_N i, fun i hi k hk h => η_injOn hi hk h, fun n hn => ?_⟩,
    ⟨eN, fun i => by rw [eN_apply, toAdd_ofAdd, etaV_toVecD]⟩, by rw [card_N]; norm_num,
    x_mem_normalizer, y_mem_normalizer, fun j => ⟨normalConjugators j, rfl⟩, N_le_H,
    N_normal_in_H⟩
  obtain ⟨i, hi, rfl⟩ := exists_η_eq hn
  exact ⟨i, hi, rfl⟩

theorem conj_mem_enum
    {pts : Array ℕ} {n : ℕ} (hc : closedOK xyInvGens pts n = true) :
    ∀ k ∈ K, ∀ t ∈ {m : J | ∃ i < n, m = η pts[i]!}, k * t * k⁻¹ ∈
      {m : J | ∃ i < n, m = η pts[i]!} := by
  refine conj_mem_of_inv_closed ?_ ?_
  · rintro _ ⟨i, hi, rfl⟩
    obtain ⟨k, hk, e⟩ := closedOK_spec hc i hi 0 (by decide)
    refine ⟨k, hk, ?_⟩
    rw [inv_inv, x_inv_conj_η, e]
    rfl
  · rintro _ ⟨i, hi, rfl⟩
    obtain ⟨k, hk, e⟩ := closedOK_spec hc i hi 1 (by decide)
    refine ⟨k, hk, ?_⟩
    rw [inv_inv, y_inv_conj_η, e]
    rfl

theorem conjOrbit_eq_enum
    {pts : Array ℕ} {n s : ℕ} (hn : 0 < n) (h0 : pts[0]! = s)
    (hc : closedOK xyInvGens pts n = true)
    (hreach : ∀ i < n, ∃ k ∈ K, k * η s * k⁻¹ = η pts[i]!) :
    conjOrbit K (η s) = {m : J | ∃ i < n, m = η pts[i]!} := by
  ext m
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact conj_mem_enum hc k hk _ ⟨0, hn, by rw [h0]⟩
  · rintro ⟨i, hi, rfl⟩
    obtain ⟨k, hk, e⟩ := hreach i hi
    exact ⟨k, hk, e.symm⟩

theorem ncard_enum
    {pts : Array ℕ} {n : ℕ} (hlt : ∀ i < n, pts[i]! < 2048)
    (hne : ∀ i < n, ∀ k < n, i ≠ k → pts[i]! ≠ pts[k]!) :
    {m : J | ∃ i < n, m = η pts[i]!}.ncard = n := by
  have hf : Function.Injective fun i : Fin n => η pts[i.val]! := by
    intro i k e
    by_contra hik
    exact hne _ i.isLt _ k.isLt (fun h => hik (Fin.ext h)) (η_injOn (hlt _ i.isLt) (hlt _ k.isLt) e)
  have e : {m : J | ∃ i < n, m = η pts[i]!} = Set.range fun i : Fin n => η pts[i.val]! := by
    ext m
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i.val, i.isLt, rfl⟩
  rw [e, Set.ncard_range_of_injective hf, Nat.card_fin]

theorem conjOrbit_one :
    conjOrbit K (η 1) = {m : J | ∃ i < 1771, m = η orb1.1[i]!} :=
  conjOrbit_eq_enum (by norm_num) (bfsOK_parts orb1_ok).1 orb1_closed reach1

theorem conjOrbit_fourteen :
    conjOrbit K (η 14) = {m : J | ∃ i < 276, m = η orb14.1[i]!} :=
  conjOrbit_eq_enum (by norm_num) (bfsOK_parts orb14_ok).1 orb14_closed reach14

end CFSG.Sporadic.J4Schreier
