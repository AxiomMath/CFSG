module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import Certificates.Data.S1277Struct

public section

namespace CFSG.Quasithin.H13.I1277

open CFSG.Quasithin.H13.S127.Mod Certificates.Data.S1277Struct
open scoped IsMulCommutative

structure KCod {G : Type} [Group G] (K : Subgroup G) (T : KTab) (κ : G → Nat) : Prop where
  mul : ∀ x ∈ K, ∀ y ∈ K, κ (x * y) = mulN T (κ x) (κ y)
  inj : ∀ x ∈ K, ∀ y ∈ K, κ x = κ y → x = y
  mem : ∀ x ∈ K, κ x ∈ klist T
  surj : ∀ n ∈ klist T, ∃ x ∈ K, κ x = n
  one : κ 1 = oneN T

section KCod

variable {G : Type} [Group G] {K : Subgroup G} {T : KTab} {κ : G → Nat}

theorem KCod.inv (hκ : KCod K T κ)
    (hinv : ∀ n ∈ klist T, invN T n ∈ klist T ∧ mulN T n (invN T n) = oneN T)
    {x : G} (hx : x ∈ K) : κ x⁻¹ = invN T (κ x) := by
  obtain ⟨hmem, hmul⟩ := hinv _ (hκ.mem x hx)
  obtain ⟨y, hy, hyκ⟩ := hκ.surj _ hmem
  have h1 : κ (x * y) = κ 1 := by rw [hκ.mul x hx y hy, hyκ, hmul, hκ.one]
  have h2 : x * y = 1 := hκ.inj _ (K.mul_mem hx hy) _ K.one_mem h1
  have h3 : y = x⁻¹ := eq_inv_of_mul_eq_one_right h2
  rw [← hyκ, h3]

theorem KCod.conj (hκ : KCod K T κ)
    (hinv : ∀ n ∈ klist T, invN T n ∈ klist T ∧ mulN T n (invN T n) = oneN T)
    {g x : G} (hg : g ∈ K) (hx : x ∈ K) :
    κ (g * x * g⁻¹) = mulN T (mulN T (κ g) (κ x)) (invN T (κ g)) := by
  rw [hκ.mul _ (K.mul_mem hg hx) _ (K.inv_mem hg), hκ.mul _ hg _ hx, hκ.inv hinv hg]

theorem KCod.pow2 (hκ : KCod K T κ) {x : G} (hx : x ∈ K) (k : Nat) :
    κ (x ^ 2 ^ k) = (List.range k).foldl (fun y _ => mulN T y y) (κ x) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ← ih,
      pow_succ, pow_mul, pow_two]
    have hk : x ^ 2 ^ k ∈ K := K.pow_mem hx _
    rw [hκ.mul _ hk _ hk]

theorem KCod.isTwo (hκ : KCod K T κ) {x : G} (hx : x ∈ K) (hx2 : x ^ 2 ^ 10 = 1) :
    isTwoN T (κ x) = true := by
  unfold isTwoN
  rw [← hκ.pow2 hx 10, hx2, hκ.one]
  simp

end KCod

end CFSG.Quasithin.H13.I1277

end
