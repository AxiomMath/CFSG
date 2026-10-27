module

public import CFSG.Quasithin.Background.RonanH43Base

public section

namespace CFSG.Quasithin.RonanH43

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.SL3Pair CFSG.Quasithin.H.SL3One CFSG.Open
  CFSG.Assembly.LowTwoRank Matrix

@[expose] def coord1 (i : Fin 3) : PV →* Multiplicative (ZMod 2) where
  toFun x := Multiplicative.ofAdd (Multiplicative.toAdd x.1 i)
  map_one' := rfl
  map_mul' _ _ := rfl

@[expose] def coord2 (i : Fin 3) : PV →* Multiplicative (ZMod 2) where
  toFun x := Multiplicative.ofAdd (Multiplicative.toAdd x.2 i)
  map_one' := rfl
  map_mul' _ _ := rfl

@[expose] def dotHom (c φ : Fin 3 → ZMod 2) : PV →* Multiplicative (ZMod 2) where
  toFun x := Multiplicative.ofAdd (φ ⬝ᵥ Multiplicative.toAdd x.1 + c ⬝ᵥ Multiplicative.toAdd x.2)
  map_one' := by
    change Multiplicative.ofAdd (φ ⬝ᵥ 0 + c ⬝ᵥ 0) = 1
    simp
  map_mul' a b := by
    change Multiplicative.ofAdd (φ ⬝ᵥ (Multiplicative.toAdd a.1 + Multiplicative.toAdd b.1) +
      c ⬝ᵥ (Multiplicative.toAdd a.2 + Multiplicative.toAdd b.2)) =
      Multiplicative.ofAdd (φ ⬝ᵥ Multiplicative.toAdd a.1 + c ⬝ᵥ Multiplicative.toAdd a.2) *
        Multiplicative.ofAdd (φ ⬝ᵥ Multiplicative.toAdd b.1 + c ⬝ᵥ Multiplicative.toAdd b.2)
    rw [← ofAdd_add, dotProduct_add, dotProduct_add]
    congr 1
    ring

@[expose] def hyper (c φ : Fin 3 → ZMod 2) : Subgroup PV := (dotHom c φ).ker

theorem mem_hyper {c φ : Fin 3 → ZMod 2} {x : PV} :
    x ∈ hyper c φ ↔ φ ⬝ᵥ Multiplicative.toAdd x.1 + c ⬝ᵥ Multiplicative.toAdd x.2 = 0 := by
  rw [hyper, MonoidHom.mem_ker]
  exact ofAdd_eq_one

@[expose] def cTarget : Subgroup PV := (coord1 1).ker ⊓ (coord1 2).ker ⊓ (coord2 0).ker

theorem mem_cTarget {x : PV} :
    x ∈ cTarget ↔ Multiplicative.toAdd x.1 1 = 0 ∧ Multiplicative.toAdd x.1 2 = 0 ∧
      Multiplicative.toAdd x.2 0 = 0 := by
  rw [cTarget, Subgroup.mem_inf, Subgroup.mem_inf, MonoidHom.mem_ker, MonoidHom.mem_ker,
    MonoidHom.mem_ker]
  exact and_assoc.trans (and_congr ofAdd_eq_one (and_congr ofAdd_eq_one ofAdd_eq_one))

@[expose] def wSet : Subgroup PV := (coord2 0).ker

theorem mem_wSet {x : PV} : x ∈ wSet ↔ Multiplicative.toAdd x.2 0 = 0 := by
  rw [wSet, MonoidHom.mem_ker]
  exact ofAdd_eq_one

@[expose] def v1R : Subgroup PV :=
  (⊤ : Subgroup (Multiplicative (Fin 3 → ZMod 2))).prod ⊥

theorem mem_v1R {x : PV} : x ∈ v1R ↔ x.2 = 1 := by
  simp [v1R, Subgroup.mem_prod]

theorem card_of_iff (S : Subgroup PV) (P : PV → Prop) [DecidablePred P] (h : ∀ x, x ∈ S ↔ P x) :
    Nat.card ↥S = (Finset.univ.filter P).card := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight h), Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem card_hyper (c φ : Fin 3 → ZMod 2) (hφ : φ ≠ 0) : Nat.card ↥(hyper c φ) = 32 := by
  rw [card_of_iff (hyper c φ) (fun x : PV => φ ⬝ᵥ Multiplicative.toAdd x.1 +
    c ⬝ᵥ Multiplicative.toAdd x.2 = 0) fun x => mem_hyper]
  revert c φ
  decide +kernel

theorem card_cTarget : Nat.card ↥cTarget = 8 := by
  rw [card_of_iff cTarget (fun x : PV => Multiplicative.toAdd x.1 1 = 0 ∧
    Multiplicative.toAdd x.1 2 = 0 ∧ Multiplicative.toAdd x.2 0 = 0) fun x => mem_cTarget]
  decide +kernel

theorem card_wSet : Nat.card ↥wSet = 32 := by
  rw [card_of_iff wSet (fun x : PV => Multiplicative.toAdd x.2 0 = 0) fun x => mem_wSet]
  decide +kernel

theorem rk_of_card {W : Type*} [Group W] {k : ℕ} (h : Nat.card W = 2 ^ k) : rk W = k := by
  unfold rk
  rw [h, padicValNat.prime_pow]

end CFSG.Quasithin.RonanH43
