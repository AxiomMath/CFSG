module

public import CFSG.Permutation.UnitaryThreeRecognition.BridgeHyp2

public section

namespace CFSG.UnitaryThreeRecognition

open MulAction CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.UnitaryThreeRecognition.Model CFSG.UnitaryThreeRecognition.WeylAlg

namespace CoordHyp

variable {G Ω : Type*} [Group G] [MulAction G Ω] {Q : Subgroup G} {a b : Ω} {j s : G}
  {p f d : ℕ} {K : Type*} [Field K] {J : HermitianForm 3 K} {φ : Q ≃* Coord J}
  (C : CoordHyp Q a b j J φ) (S : StdHyp G Q a b j s p f d)
  [Finite G] [Finite Ω] {q : ℕ} (hconj : ∀ x : K, J.conj x = x ^ q)
  (hcop : Nat.Coprime 3 (q + 1))
include C S hconj hcop

theorem symm_mem_swapFix {k : Kˣ} (hk : (k : K) ^ (q + 1) = 1) :
    (((C.torusEquiv S hconj hcop).symm k : pairStab G a b) : G) ∈ swapFix G a b s := by
  set t := (C.torusEquiv S hconj hcop).symm k with htdef
  have hσ := (C.sigmaK_fix S hconj hcop k).mpr hk
  have hct : S.conjS t = t := by
    apply (C.torusEquiv S hconj hcop).injective
    rw [torusEquiv_apply, torusEquiv_apply, ← sigmaK_apply, hσ, C.kOf_symm S hconj hcop]
  have e' : s * (t : G) * s = t := congrArg Subtype.val hct
  refine mem_swapFix.mpr ⟨t.2, ?_⟩
  calc s * (t : G) = s * t * s * s := by rw [mul_assoc _ s s, S.hs2, mul_one]
    _ = t * s := by rw [e']

theorem symm_ne_one_of_ne {k : Kˣ} (hk1 : k ≠ 1) :
    (((C.torusEquiv S hconj hcop).symm k : pairStab G a b) : G) ≠ 1 := by
  intro e
  apply hk1
  have : (C.torusEquiv S hconj hcop).symm k = 1 := Subtype.ext e
  rw [← MulEquiv.apply_symm_apply (C.torusEquiv S hconj hcop) k, this, map_one]

theorem phi_inv_mul_conj (k : Kˣ) (v : Q) (hy : ((v : G))⁻¹ *
      ((C.torusEquiv S hconj hcop).symm k : G) * v *
      ((C.torusEquiv S hconj hcop).symm k : G)⁻¹ ∈ Q) :
    φ ⟨_, hy⟩ = (φ v)⁻¹ * hermitianTorusAction J k (φ v) := by
  rw [← C.phi_conj_symm S hconj hcop k v, ← map_inv, ← map_mul]
  congr 1
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  group

theorem sMapCoord_block {u : Coord J} (hu : u.1.1 ≠ 0) {k k' : Kˣ} (hk : (k : K) ^ (q + 1) = 1)
    (hk' : (k' : K) ^ (q + 1) = 1) (hk1 : k ≠ 1) (hk'1 : k' ≠ 1) :
    (S.sMapCoord φ (u⁻¹ * hermitianTorusAction J k u)).1.1 =
      (S.sMapCoord φ (u⁻¹ * hermitianTorusAction J k' u)).1.1 := by
  obtain ⟨v, rfl⟩ := φ.surjective u
  have hvZ : (v : G) ∉ centQ Q j := fun h => hu ((C.center v).mp h)
  set w := (C.torusEquiv S hconj hcop).symm k
  set w' := (C.torusEquiv S hconj hcop).symm k'
  have hw := C.symm_mem_swapFix S hconj hcop hk
  have hw' := C.symm_mem_swapFix S hconj hcop hk'
  have hw1 := C.symm_ne_one_of_ne S hconj hcop hk1
  have hw'1 := C.symm_ne_one_of_ne S hconj hcop hk'1
  have hB := S.block v.2 hvZ hw hw1 hw' hw'1
  have mem : ∀ x : pairStab G a b, ((v : G))⁻¹ * x * v * (x : G)⁻¹ ∈ Q := fun x => by
    have := S.root.normal x x.2.1 v v.2
    have e : ((v : G))⁻¹ * x * v * (x : G)⁻¹ = (v : G)⁻¹ * (x * v * (x : G)⁻¹) := by group
    rw [e]; exact Q.mul_mem (Q.inv_mem v.2) this
  have ne : ∀ x : pairStab G a b, (x : G) ≠ 1 → (x : G) ∈ swapFix G a b s →
      ((v : G))⁻¹ * x * v * (x : G)⁻¹ ≠ 1 := by
    intro x hx1 _ e
    apply hvZ
    apply S.mem_centQ_of_commute x.2 hx1 v.2
    calc (x : G) * v = v * ((v : G)⁻¹ * x * v * (x : G)⁻¹) * x := by group
      _ = v * x := by rw [e, mul_one]
  set y : Q := ⟨_, mem w⟩ with hydef
  set y' : Q := ⟨_, mem w'⟩ with hy'def
  have hy1 : (y : G) ≠ 1 := ne w hw1 hw
  have hy'1 : (y' : G) ≠ 1 := ne w' hw'1 hw'
  rw [← C.phi_inv_mul_conj S hconj hcop k v (mem w), ← hydef,
    ← C.phi_inv_mul_conj S hconj hcop k' v (mem w'), ← hy'def,
    S.sMapCoord_apply φ y hy1, S.sMapCoord_apply φ y' hy'1]
  have hZ := (C.center ⟨_, Q.mul_mem (Q.inv_mem (S.root.sLeft_mem S.hb S.hsa S.hs2 y.2 hy1))
    (S.root.sLeft_mem S.hb S.hsa S.hs2 y'.2 hy'1)⟩).mp hB
  have e : (⟨_, Q.mul_mem (Q.inv_mem (S.root.sLeft_mem S.hb S.hsa S.hs2 y.2 hy1))
      (S.root.sLeft_mem S.hb S.hsa S.hs2 y'.2 hy'1)⟩ : Q) =
      (⟨sLeft Q a b s y, S.root.sLeft_mem S.hb S.hsa S.hs2 y.2 hy1⟩ : Q)⁻¹ *
        ⟨sLeft Q a b s y', S.root.sLeft_mem S.hb S.hsa S.hs2 y'.2 hy'1⟩ := rfl
  rw [e, map_mul, map_inv, mul_fst, inv_fst] at hZ
  linear_combination -hZ

end CoordHyp

end CFSG.UnitaryThreeRecognition
