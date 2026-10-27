module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Local
public import CFSG.Quasithin.Recognition.GoldschmidtFan86LocalPrime

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph Equiv

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace FanTree

variable (F : FanTree Γ G)
include F

@[expose] def localHom (v : V) : MulAction.stabilizer G v →* Perm (Γ.neighborSet v) where
  toFun g :=
    { toFun := fun w => ⟨(g : G) • (w : V), F.adj_smul_of_mem_stabilizer g.2 w.2⟩
      invFun := fun w => ⟨(g : G)⁻¹ • (w : V), F.adj_smul_of_mem_stabilizer (inv_mem g.2) w.2⟩
      left_inv := fun w => Subtype.ext (inv_smul_smul _ _)
      right_inv := fun w => Subtype.ext (smul_inv_smul _ _) }
  map_one' := by
    ext w
    exact one_smul G (w : V)
  map_mul' g h := by
    ext w
    exact mul_smul (g : G) (h : G) (w : V)

theorem localHom_apply_coe (v : V) (g : MulAction.stabilizer G v) (w : Γ.neighborSet v) :
    ((F.localHom v g w : Γ.neighborSet v) : V) = (g : G) • (w : V) := rfl

theorem localHom_pow_apply_coe (v : V) (g : MulAction.stabilizer G v) (n : ℕ)
    (w : Γ.neighborSet v) :
    (((F.localHom v g) ^ n) w : V) = (g : G) ^ n • (w : V) := by
  induction n generalizing w with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Perm.mul_apply, ih, localHom_apply_coe, pow_succ, mul_smul]

theorem mem_ker_localHom (v : V) (g : MulAction.stabilizer G v) :
    g ∈ (F.localHom v).ker ↔ (g : G) ∈ nbrStab Γ G v := by
  rw [MonoidHom.mem_ker, mem_nbrStab]
  constructor
  · intro h w hw
    have := congrArg (fun f : Perm (Γ.neighborSet v) => ((f ⟨w, hw⟩ : Γ.neighborSet v) : V)) h
    exact this
  · intro h
    ext w
    exact h w w.2

theorem localHom_frobenius (v : V) : ∀ q ∈ (F.localHom v).range, ∀ a b : Γ.neighborSet v,
    a ≠ b → q a = a → q b = b → q = 1 := by
  rintro _ ⟨g, rfl⟩ a b hab ha hb
  ext w
  have h1 : (g : G) • (a : V) = a := congrArg Subtype.val ha
  have h2 : (g : G) • (b : V) = b := congrArg Subtype.val hb
  exact F.frobenius_two v a b a.2 b.2 (fun h => hab (Subtype.ext h)) g g.2 h1 h2 w w.2

theorem not_mem_nbrStab_of_orderOf {v : V} {x : G} (hx : x ∈ MulAction.stabilizer G v)
    (hxo : orderOf x = Fan86.valence Γ v) : x ∉ nbrStab Γ G v := by
  intro hK
  obtain ⟨u, hu⟩ := F.exists_adj v
  have hmem : x ∈ MulAction.stabilizer G v ⊓ MulAction.stabilizer G u :=
    ⟨hx, MulAction.mem_stabilizer_iff.2 (hK u hu)⟩
  obtain ⟨j, hj⟩ := F.edge_two v u hu ⟨x, hmem⟩
  have hj' : x ^ 2 ^ j = 1 := congrArg Subtype.val hj
  have hdvd := orderOf_dvd_of_pow_eq_one hj'
  rw [hxo] at hdvd
  have hp := F.valence_isPrime v
  have h2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hdvd)
  have h3 : Fan86.valence Γ v = Nat.card (Γ.neighborSet v) := rfl
  rcases F.valence v with h | h <;> omega

theorem finite_neighborSet (v : V) : Finite (Γ.neighborSet v) :=
  Set.finite_coe_iff.2 (F.ncard_neighborSet_le v).2

theorem orderOf_localHom {v : V} {x : G} (hx : x ∈ MulAction.stabilizer G v)
    (hxo : orderOf x = Fan86.valence Γ v) : orderOf (F.localHom v ⟨x, hx⟩) = Fan86.valence Γ v := by
  have hp := F.valence_isPrime v
  have hdvd : orderOf (F.localHom v ⟨x, hx⟩) ∣ Fan86.valence Γ v := by
    have := orderOf_map_dvd (F.localHom v) (⟨x, hx⟩ : MulAction.stabilizer G v)
    rwa [Subgroup.orderOf_mk, hxo] at this
  rcases (Nat.dvd_prime hp).1 hdvd with h | h
  · exfalso
    have h1 : F.localHom v ⟨x, hx⟩ = 1 := orderOf_eq_one_iff.1 h
    exact F.not_mem_nbrStab_of_orderOf hx hxo
      ((F.mem_ker_localHom v ⟨x, hx⟩).1 (MonoidHom.mem_ker.2 h1))
  · exact h

theorem exists_pow_smul_eq {v : V} {x : G} (hx : x ∈ MulAction.stabilizer G v)
    (hord : orderOf x = Fan86.valence Γ v) {a b : V} (ha : Γ.Adj v a) (hb : Γ.Adj v b) :
    ∃ i : ℕ, x ^ i • a = b := by
  have := F.finite_neighborSet v
  obtain ⟨i, hi⟩ := FrobPrime.exists_pow_apply_eq (F.valence_isPrime v) rfl
    (F.orderOf_localHom hx hord) (⟨a, ha⟩ : Γ.neighborSet v) ⟨b, hb⟩
  refine ⟨i, ?_⟩
  have := congrArg Subtype.val hi
  rwa [F.localHom_pow_apply_coe] at this

theorem conj_mem_pow_mul_nbrStab {v : V} {x g : G} (hx : x ∈ MulAction.stabilizer G v)
    (hord : orderOf x = Fan86.valence Γ v) (hg : g ∈ MulAction.stabilizer G v) :
    ∃ (i : ℕ) (k : G), k ∈ nbrStab Γ G v ∧ g * x * g⁻¹ = x ^ i * k := by
  have hp := F.valence_isPrime v
  have := F.finite_neighborSet v
  let X : MulAction.stabilizer G v := ⟨x, hx⟩
  let Y : MulAction.stabilizer G v := ⟨g, hg⟩
  obtain ⟨i, hi⟩ := FrobPrime.conj_pow_of_frobenius hp rfl (F.localHom v).range
    (F.localHom_frobenius v) (MonoidHom.mem_range.2 ⟨X, rfl⟩) (F.orderOf_localHom hx hord)
    (F.localHom v Y) (MonoidHom.mem_range.2 ⟨Y, rfl⟩)
  have hk : (X ^ i)⁻¹ * (Y * X * Y⁻¹) ∈ (F.localHom v).ker := by
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv, map_pow]
    rw [hi]
    simp
  refine ⟨i, ((X ^ i)⁻¹ * (Y * X * Y⁻¹) : MulAction.stabilizer G v),
    (F.mem_ker_localHom v _).1 hk, ?_⟩
  show g * x * g⁻¹ = x ^ i * ((x ^ i)⁻¹ * (g * x * g⁻¹))
  rw [mul_inv_cancel_left]

end FanTree

end CFSG.Quasithin.Fan86
