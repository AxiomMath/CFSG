module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSMatrices

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def ggFDot {R : Type} [CommRing R] {N : ℕ} (a z : Vector R (N + 1)) : R :=
  ∑ l : Fin (N + 1), a.get l * z.get l

@[expose] def ggFRefl {R : Type} [CommRing R] {N : ℕ} (T : Fin N → Vector R (N + 1)) (k : Fin N)
    (z : Vector R (N + 1)) : Vector R (N + 1) :=
  Vector.ofFn fun l => if l = k.castSucc then z.get l - ggFDot (T k) z else z.get l

@[expose] def ggFWord {R : Type} [CommRing R] {N : ℕ} (T : Fin N → Vector R (N + 1))
    (ws : List (Fin N)) (z : Vector R (N + 1)) : Vector R (N + 1) :=
  ws.foldr (fun k acc => ggFRefl T k acc) z

@[expose] def ggFUnit {R : Type} [CommRing R] {N : ℕ} (k : Fin (N + 1)) : Vector R (N + 1) :=
  Vector.ofFn fun l => if l = k then 1 else 0

@[expose] def ggFDualAt {R : Type} [CommRing R] {N : ℕ} (T : Fin N → Vector R (N + 1))
    (c : Vector R N) (j : Fin N) : R :=
  ∑ o : Fin N, c.get o * (T o).get j.castSucc

@[expose] def ggFDRefl {R : Type} [CommRing R] {N : ℕ} (T : Fin N → Vector R (N + 1)) (j : Fin N)
    (c : Vector R N) : Vector R N :=
  Vector.ofFn fun o => if o = j then c.get o - ggFDualAt T c j else c.get o

@[expose] def ggFDWord {R : Type} [CommRing R] {N : ℕ} (T : Fin N → Vector R (N + 1))
    (ws : List (Fin N)) (c : Vector R N) : Vector R N :=
  ws.foldl (fun acc k => ggFDRefl T k acc) c

@[expose] def ggFDUnit {R : Type} [CommRing R] {N : ℕ} (k : Fin N) : Vector R N :=
  Vector.ofFn fun o => if o = k then 1 else 0

section Sound

variable {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
  {R : Type} [CommRing R] (φ : R →+* ZMod p) {N : ℕ}

@[expose] def ggFPi (h : Fin N → V) (x : V) (z : Vector R (N + 1)) : V :=
  ∑ l : Fin N, φ (z.get l.castSucc) • h l + φ (z.get (Fin.last N)) • x

@[expose] def GGFTable (T : Fin N → Vector R (N + 1)) (h : Fin N → V) (x : V)
    (α : Fin N → Module.Dual (ZMod p) V) : Prop :=
  (∀ k l : Fin N, α k (h l) = φ ((T k).get l.castSucc)) ∧
    ∀ k : Fin N, α k x = φ ((T k).get (Fin.last N))

@[expose] def ggFFun (α : Fin N → Module.Dual (ZMod p) V) (c : Vector R N) :
    Module.Dual (ZMod p) V :=
  ∑ o : Fin N, φ (c.get o) • α o

variable {φ}

theorem ggFPi_root {T : Fin N → Vector R (N + 1)} {h : Fin N → V} {x : V}
    {α : Fin N → Module.Dual (ZMod p) V} (hT : GGFTable φ T h x α) (k : Fin N)
    (z : Vector R (N + 1)) : α k (ggFPi φ h x z) = φ (ggFDot (T k) z) := by
  rw [ggFPi, map_add, map_sum, ggFDot, map_sum, Fin.sum_univ_castSucc]
  congr 1
  · refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_smul, hT.1, smul_eq_mul, map_mul, mul_comm]
  · rw [map_smul, hT.2, smul_eq_mul, map_mul, mul_comm]

theorem ggFPi_refl {T : Fin N → Vector R (N + 1)} {h : Fin N → V} {x : V}
    {α : Fin N → Module.Dual (ZMod p) V} (hT : GGFTable φ T h x α)
    {g : Fin N → (V ≃ₗ[ZMod p] V)} (hg : ∀ k w, g k w = w - α k w • h k) (k : Fin N)
    (z : Vector R (N + 1)) : g k (ggFPi φ h x z) = ggFPi φ h x (ggFRefl T k z) := by
  classical
  rw [hg, ggFPi_root hT]
  simp only [ggFPi, ggFRefl, Vector.get_ofFn]
  rw [if_neg (Fin.castSucc_ne_last k).symm]
  have hsum : ∑ l : Fin N, φ (if l.castSucc = k.castSucc then z.get l.castSucc - ggFDot (T k) z
      else z.get l.castSucc) • h l =
      ∑ l : Fin N, φ (z.get l.castSucc) • h l - φ (ggFDot (T k) z) • h k := by
    have hterm : ∀ l : Fin N, φ (if l.castSucc = k.castSucc then z.get l.castSucc - ggFDot (T k) z
        else z.get l.castSucc) • h l =
        φ (z.get l.castSucc) • h l - (if l = k then φ (ggFDot (T k) z) • h k else 0) := by
      intro l
      by_cases hl : l = k
      · subst hl
        simp only [if_true]
        rw [RingHom.map_sub, sub_smul]
      · rw [if_neg (fun h => hl (Fin.castSucc_injective N h)), if_neg hl, sub_zero]
    rw [Finset.sum_congr rfl fun l _ => hterm l, Finset.sum_sub_distrib, Finset.sum_ite_eq']
    simp
  rw [hsum]
  abel

theorem ggFPi_word {T : Fin N → Vector R (N + 1)} {h : Fin N → V} {x : V}
    {α : Fin N → Module.Dual (ZMod p) V} (hT : GGFTable φ T h x α)
    {g : Fin N → (V ≃ₗ[ZMod p] V)} (hg : ∀ k w, g k w = w - α k w • h k) (ws : List (Fin N))
    (z : Vector R (N + 1)) : (ws.map g).prod (ggFPi φ h x z) = ggFPi φ h x (ggFWord T ws z) := by
  induction ws with
  | nil => rfl
  | cons k ws ih =>
    rw [List.map_cons, List.prod_cons, LinearEquiv.mul_apply, ih, ggFPi_refl hT hg]
    rfl

theorem ggFPi_unit (h : Fin N → V) (x : V) (l : Fin N) :
    ggFPi φ h x (ggFUnit l.castSucc) = h l := by
  classical
  simp only [ggFPi, ggFUnit, Vector.get_ofFn]
  rw [if_neg (Fin.castSucc_ne_last l).symm, map_zero, zero_smul, add_zero]
  simp [Fin.castSucc_inj]

theorem ggFFun_unit (α : Fin N → Module.Dual (ZMod p) V) (k : Fin N) :
    ggFFun φ α (ggFDUnit k) = α k := by
  classical
  simp only [ggFFun, ggFDUnit, Vector.get_ofFn]
  rw [Finset.sum_eq_single k (fun o _ ho => by rw [if_neg ho, map_zero, zero_smul])
    (fun hk => absurd (Finset.mem_univ k) hk), if_pos rfl, map_one, one_smul]

theorem ggFFun_coroot {T : Fin N → Vector R (N + 1)} {h : Fin N → V} {x : V}
    {α : Fin N → Module.Dual (ZMod p) V} (hT : GGFTable φ T h x α) (c : Vector R N) (j : Fin N) :
    ggFFun φ α c (h j) = φ (ggFDualAt T c j) := by
  simp only [ggFFun, ggFDualAt, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, map_sum,
    map_mul, hT.1]

theorem ggFFun_refl {T : Fin N → Vector R (N + 1)} {h : Fin N → V} {x : V}
    {α : Fin N → Module.Dual (ZMod p) V} (hT : GGFTable φ T h x α)
    {g : Fin N → (V ≃ₗ[ZMod p] V)} (hg : ∀ k w, g k w = w - α k w • h k) (j : Fin N)
    (c : Vector R N) (w : V) : ggFFun φ α c (g j w) = ggFFun φ α (ggFDRefl T j c) w := by
  classical
  rw [hg, map_sub, map_smul, ggFFun_coroot hT, smul_eq_mul]
  simp only [ggFFun, ggFDRefl, Vector.get_ofFn, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul]
  have hterm : ∀ o : Fin N, φ (if o = j then c.get o - ggFDualAt T c j else c.get o) * α o w =
      φ (c.get o) * α o w - (if o = j then φ (ggFDualAt T c j) * α j w else 0) := by
    intro o
    by_cases ho : o = j
    · subst ho
      rw [if_pos rfl, if_pos rfl, RingHom.map_sub, sub_mul]
    · rw [if_neg ho, if_neg ho]
      ring
  rw [Finset.sum_congr rfl fun o _ => hterm o]
  simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

theorem ggFFun_word {T : Fin N → Vector R (N + 1)} {h : Fin N → V} {x : V}
    {α : Fin N → Module.Dual (ZMod p) V} (hT : GGFTable φ T h x α)
    {g : Fin N → (V ≃ₗ[ZMod p] V)} (hg : ∀ k w, g k w = w - α k w • h k) (ws : List (Fin N))
    (c : Vector R N) (w : V) :
    ggFFun φ α c ((ws.map g).prod w) = ggFFun φ α (ggFDWord T ws c) w := by
  induction ws generalizing c with
  | nil => rfl
  | cons k ws ih =>
    rw [List.map_cons, List.prod_cons, LinearEquiv.mul_apply, ggFFun_refl hT hg, ih]
    rfl

end Sound

end CFSG.StandardType
