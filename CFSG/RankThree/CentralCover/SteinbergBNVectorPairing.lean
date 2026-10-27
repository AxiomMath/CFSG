module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.Classical2.CentralLiftCommutator

public section

namespace CFSG.RankThree.CentralCover

open CFSG.RankThree.Classical2

section Vec

variable {Y H : Type*} [Group Y] [Group H] {φ : Y →* H} {r : ℕ} [NeZero r] {V : Type*}
  [AddCommGroup V] [Module (ZMod r) V] (e : Multiplicative V →* H)

theorem map_ofAdd_smul (a : ZMod r) (v : V) :
    e (.ofAdd (a • v)) = e (.ofAdd v) ^ a.val := by
  rw [← map_pow, ← ofAdd_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod r), ZMod.natCast_zmod_val]

theorem commute_map_ofAdd (v w : V) : Commute (e (.ofAdd v)) (e (.ofAdd w)) :=
  (Commute.all (Multiplicative.ofAdd v) (Multiplicative.ofAdd w)).map e

theorem liftComm_smul_left (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center Y)
    (a : ZMod r) (v w : V) :
    liftComm φ hφ (e (.ofAdd (a • v))) (e (.ofAdd w)) =
      liftComm φ hφ (e (.ofAdd v)) (e (.ofAdd w)) ^ a.val := by
  rw [map_ofAdd_smul, liftComm_pow_left hφ hker (commute_map_ofAdd e v w)]

theorem liftComm_smul_right (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center Y)
    (a : ZMod r) (v w : V) :
    liftComm φ hφ (e (.ofAdd v)) (e (.ofAdd (a • w))) =
      liftComm φ hφ (e (.ofAdd v)) (e (.ofAdd w)) ^ a.val := by
  rw [liftComm_swap, liftComm_smul_left e hφ hker, liftComm_swap, inv_pow, inv_inv]

theorem liftComm_add_left (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center Y)
    (v v' w : V) :
    liftComm φ hφ (e (.ofAdd (v + v'))) (e (.ofAdd w)) =
      liftComm φ hφ (e (.ofAdd v)) (e (.ofAdd w)) *
        liftComm φ hφ (e (.ofAdd v')) (e (.ofAdd w)) := by
  rw [ofAdd_add, map_mul, liftComm_mul_left hφ hker (commute_map_ofAdd e v' w)]

theorem liftComm_add_right (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center Y)
    (v w w' : V) :
    liftComm φ hφ (e (.ofAdd v)) (e (.ofAdd (w + w'))) =
      liftComm φ hφ (e (.ofAdd v)) (e (.ofAdd w)) *
        liftComm φ hφ (e (.ofAdd v)) (e (.ofAdd w')) := by
  rw [ofAdd_add, map_mul, liftComm_mul_right hφ hker (commute_map_ofAdd e v w')]

end Vec

section Span

variable {Y H : Type*} [Group Y] [Group H] {φ : Y →* H} {r : ℕ} [NeZero r] {V : Type*}
  [AddCommGroup V] [Module (ZMod r) V] (e : Multiplicative V →* H)

theorem liftComm_eq_one_of_mem_span (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center Y) {S T : Set V}
    (h : ∀ v ∈ S, ∀ w ∈ T, liftComm φ hφ (e (.ofAdd v)) (e (.ofAdd w)) = 1) {v w : V}
    (hv : v ∈ Submodule.span (ZMod r) S) (hw : w ∈ Submodule.span (ZMod r) T) :
    liftComm φ hφ (e (.ofAdd v)) (e (.ofAdd w)) = 1 := by
  let killL : V → Submodule (ZMod r) V := fun w =>
    { carrier := {v | liftComm φ hφ (e (.ofAdd v)) (e (.ofAdd w)) = 1}
      add_mem' := fun {a b} ha hb => by
        change liftComm φ hφ (e (.ofAdd (a + b))) _ = 1
        rw [liftComm_add_left e hφ hker, ha, hb, one_mul]
      zero_mem' := by
        change liftComm φ hφ (e (.ofAdd 0)) _ = 1
        rw [ofAdd_zero, map_one, liftComm_one_left hφ hker]
      smul_mem' := fun c a ha => by
        change liftComm φ hφ (e (.ofAdd (c • a))) _ = 1
        rw [liftComm_smul_left e hφ hker, ha, one_pow] }
  let killR : V → Submodule (ZMod r) V := fun v =>
    { carrier := {w | liftComm φ hφ (e (.ofAdd v)) (e (.ofAdd w)) = 1}
      add_mem' := fun {a b} ha hb => by
        change liftComm φ hφ _ (e (.ofAdd (a + b))) = 1
        rw [liftComm_add_right e hφ hker, ha, hb, one_mul]
      zero_mem' := by
        change liftComm φ hφ _ (e (.ofAdd 0)) = 1
        rw [ofAdd_zero, map_one, liftComm_one_right hφ hker]
      smul_mem' := fun c a ha => by
        change liftComm φ hφ _ (e (.ofAdd (c • a))) = 1
        rw [liftComm_smul_right e hφ hker, ha, one_pow] }
  have h1 : ∀ w ∈ T, Submodule.span (ZMod r) S ≤ killL w := fun w hw =>
    Submodule.span_le.2 fun v hv => h v hv w hw
  have h2 : Submodule.span (ZMod r) T ≤ killR v :=
    Submodule.span_le.2 fun w hw' => h1 w hw' hv
  exact h2 hw

end Span

end CFSG.RankThree.CentralCover
