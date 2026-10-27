module

public import CFSG.Quasithin.Background.FLc2Min
public import CFSG.Quasithin.EmptyFaithful.S1565A

public section

namespace CFSG.Quasithin.FLc

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {V : Type} [CommGroup V]

structure VModel (n : ℕ) (ρ : SLt n →* MulAut V) (U' Z' : Subgroup V) (A : Type) [CommGroup A]
    (act : SLt n → A → A) where
  β : ↥U' →* A
  surj : Function.Surjective β
  inv : ∀ (g : SLt n), ∀ u ∈ U', (ρ g) u ∈ U'
  ker : ∀ u : ↥U', β u = 1 → (u : V) ∈ Z'
  equiv : ∀ (g : SLt n) (u : ↥U') (hu : (ρ g) (u : V) ∈ U'), β ⟨(ρ g) u, hu⟩ = act g (β u)
  Zfix : ∀ g : SLt n, ∀ z ∈ Z', (ρ g) z = z
  act_hom : ∀ g a b, act g (a * b) = act g a * act g b
  act_one : ∀ a, act 1 a = a
  act_mul : ∀ g h a, act (g * h) a = act g (act h a)

namespace VModel

variable {n : ℕ} {ρ : SLt n →* MulAut V} {U' Z' : Subgroup V} {A : Type} [CommGroup A]
  {act : SLt n → A → A} (D : VModel n ρ U' Z' A act)

include D

@[expose] def commSub (v : V) : Subgroup (SLt n) where
  carrier := {x | (ρ x) v * v⁻¹ ∈ Z'}
  one_mem' := by simp
  mul_mem' := by
    intro x y hx hy
    obtain ⟨z', hz', e'⟩ : ∃ z' ∈ Z', (ρ y) v = z' * v := ⟨(ρ y) v * v⁻¹, hy, by group⟩
    obtain ⟨z, hz, e⟩ : ∃ z ∈ Z', (ρ x) v = z * v := ⟨(ρ x) v * v⁻¹, hx, by group⟩
    have h : (ρ (x * y)) v * v⁻¹ = z' * z := by
      rw [map_mul, MulAut.mul_apply, e', map_mul, D.Zfix x z' hz', e]
      group
    show (ρ (x * y)) v * v⁻¹ ∈ Z'
    rw [h]
    exact Z'.mul_mem hz' hz
  inv_mem' := by
    intro x hx
    obtain ⟨z, hz, e⟩ : ∃ z ∈ Z', (ρ x) v = z * v := ⟨(ρ x) v * v⁻¹, hx, by group⟩
    have e2 : v = z * (ρ x⁻¹) v := by
      have h4 : (ρ x⁻¹) ((ρ x) v) = v := by
        rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one]
        rfl
      calc v = (ρ x⁻¹) ((ρ x) v) := h4.symm
        _ = (ρ x⁻¹) (z * v) := by rw [e]
        _ = (ρ x⁻¹) z * (ρ x⁻¹) v := map_mul _ _ _
        _ = z * (ρ x⁻¹) v := by rw [D.Zfix x⁻¹ z hz]
    have e3 : (ρ x⁻¹) v = z⁻¹ * v := by
      calc (ρ x⁻¹) v = z⁻¹ * (z * (ρ x⁻¹) v) := by group
        _ = z⁻¹ * v := by rw [← e2]
    have h : (ρ x⁻¹) v * v⁻¹ = z⁻¹ := by
      rw [e3]
      group
    show (ρ x⁻¹) v * v⁻¹ ∈ Z'
    rw [h]
    exact Z'.inv_mem hz

theorem fix_reflection (hV2 : ∀ w : V, w ^ 2 = 1) (hn : 1 ≤ n) {c : ℕ}
    (hFix : ∀ a : A, (∀ g ∈ Ut n, act g a = a) → ∀ i, ∀ hi : IsNode n i, i ≠ c →
      act (reflection n (ZMod 2) i hi.1 hi.2) a = a)
    {v : V} (hv : v ∈ U') (hvf : ∀ s ∈ Ut n, (ρ s) v = v) {i : ℕ} (hi : IsNode n i) (hic : i ≠ c) :
    (ρ (reflection n (ZMod 2) i hi.1 hi.2)) v = v := by
  set r := reflection n (ZMod 2) i hi.1 hi.2 with hr
  have hbv : ∀ g ∈ Ut n, act g (D.β ⟨v, hv⟩) = D.β ⟨v, hv⟩ := by
    intro g hg
    have hu : (ρ g) v ∈ U' := D.inv g v hv
    have h1 := D.equiv g ⟨v, hv⟩ hu
    have e : (⟨(ρ g) v, hu⟩ : ↥U') = ⟨v, hv⟩ := Subtype.ext (hvf g hg)
    rw [e] at h1
    exact h1.symm
  have hrv : r ∈ D.commSub v := by
    have hu : (ρ r) v ∈ U' := D.inv r v hv
    have h1 := D.equiv r ⟨v, hv⟩ hu
    rw [hFix _ hbv i hi hic] at h1
    have h2 : D.β (⟨(ρ r) v, hu⟩ * (⟨v, hv⟩ : ↥U')⁻¹) = 1 := by
      rw [map_mul, map_inv, h1, mul_inv_cancel]
    exact D.ker _ h2
  have hUt : Ut n ≤ D.commSub v := fun s hs => by
    show (ρ s) v * v⁻¹ ∈ Z'
    rw [hvf s hs, mul_inv_cancel]
    exact Z'.one_mem
  have hrU : r ∉ Ut n := by
    intro h
    rw [Ut_eq_QI] at h
    exact (reflection_mem_QI hi).1 h hi
  have hrQ : r ∈ QI n (NodesNe n i) := by
    refine (reflection_mem_QI hi).2 fun h => h.2.2 rfl
  have hQT : QI n (NodesNe n i) ≤ D.commSub v := by
    obtain ⟨-, hmin⟩ := minimal_of_node hi
    rcases hmin (D.commSub v ⊓ QI n (NodesNe n i)) (le_inf hUt (Ut_le_QI n _)) inf_le_right with h | h
    · exact absurd (h ▸ (⟨hrv, hrQ⟩ : r ∈ D.commSub v ⊓ QI n (NodesNe n i))) hrU
    · intro g hg
      have : g ∈ D.commSub v ⊓ QI n (NodesNe n i) := by rw [h]; exact hg
      exact this.1
  set X : Subgroup (SLt n) := QI n (NodesNe n i) with hX
  let φ : ↥X →* MulAut V := ρ.comp X.subtype
  have hUtX : Ut n ≤ X := Ut_le_QI n _
  have hodd : Odd ((Ut n).subgroupOf X).index := by
    obtain ⟨P, hP⟩ := exists_sylow_unitriangular (K := ZMod 2) 2 hn
    have h1 : ((Ut n).subgroupOf X).index ∣ (Ut n).index := by
      have := Subgroup.relIndex_mul_index (H := Ut n) (K := X) hUtX
      exact ⟨X.index, this.symm⟩
    have h2 : ¬ 2 ∣ (Ut n).index := by
      have e : Ut n = (P : Subgroup (SLt n)) := hP.symm
      rw [e]
      exact P.not_dvd_index
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp fun h => h2 (h.trans h1))
  have hinv : S1565.InvSub φ (⊥ : Subgroup V) := by
    intro x a ha
    rw [Subgroup.mem_bot] at ha ⊢
    rw [ha, map_one]
  have hw'' : S1565.FixMod φ ⊤ Z' v := fun x _ => hQT x.2
  have hwB : S1565.FixMod φ ((Ut n).subgroupOf X) (⊥ : Subgroup V) v := by
    intro s hs
    rw [Subgroup.mem_bot]
    show (ρ (s : SLt n)) v * v⁻¹ = 1
    rw [hvf _ (Subgroup.mem_subgroupOf.1 hs), mul_inv_cancel]
  obtain ⟨u, hu, hfix, -⟩ := S1565.norm_step φ hV2 ((Ut n).subgroupOf X) hodd hinv hw'' hwB
  have h3 := hfix ⟨r, hrQ⟩ (Subgroup.mem_top _)
  rw [Subgroup.mem_bot] at h3
  have h4 : (ρ r) (v * u) = v * u := by
    have := mul_inv_eq_one.1 h3
    exact this
  rw [map_mul, D.Zfix r u hu] at h4
  exact mul_right_cancel h4

@[expose] def twist (g : SLt n) :
    VModel n (ρ.comp (MulAut.conj g).toMonoidHom) U' Z' A (fun h a => act (g * h * g⁻¹) a) where
  β := D.β
  surj := D.surj
  inv := fun h u hu => D.inv (g * h * g⁻¹) u hu
  ker := D.ker
  equiv := fun h u hu => D.equiv (g * h * g⁻¹) u hu
  Zfix := fun h z hz => D.Zfix (g * h * g⁻¹) z hz
  act_hom := fun h a b => D.act_hom _ a b
  act_one := fun a => by simpa using D.act_one a
  act_mul := fun h k a => by
    show act (g * (h * k) * g⁻¹) a = act (g * h * g⁻¹) (act (g * k * g⁻¹) a)
    rw [← D.act_mul]
    congr 1
    group

theorem fix_reflection_conj (hV2 : ∀ w : V, w ^ 2 = 1) (hn : 1 ≤ n) {c : ℕ}
    (hFix : ∀ a : A, (∀ h ∈ Ut n, act h a = a) → ∀ i, ∀ hi : IsNode n i, i ≠ c →
      act (reflection n (ZMod 2) i hi.1 hi.2) a = a)
    (g : SLt n) {v : V} (hv : v ∈ U') (hvf : ∀ s ∈ Ut n, (ρ (g * s * g⁻¹)) v = v) {i : ℕ}
    (hi : IsNode n i) (hic : i ≠ c) :
    (ρ (g * reflection n (ZMod 2) i hi.1 hi.2 * g⁻¹)) v = v := by
  have hFix' : ∀ a : A, (∀ h ∈ Ut n, act (g * h * g⁻¹) a = a) → ∀ i, ∀ hi : IsNode n i, i ≠ c →
      act (g * reflection n (ZMod 2) i hi.1 hi.2 * g⁻¹) a = a := by
    intro a ha i hi hic
    have ha' : ∀ h ∈ Ut n, act h (act g⁻¹ a) = act g⁻¹ a := by
      intro h hh
      have e1 : act (g⁻¹ * (g * h * g⁻¹)) a = act h (act g⁻¹ a) := by
        rw [show g⁻¹ * (g * h * g⁻¹) = h * g⁻¹ by group, D.act_mul]
      have e2 : act (g⁻¹ * (g * h * g⁻¹)) a = act g⁻¹ a := by
        rw [D.act_mul, ha h hh]
      rw [← e1, e2]
    have h1 := hFix _ ha' i hi hic
    have e3 : act (g * reflection n (ZMod 2) i hi.1 hi.2 * g⁻¹) a =
        act g (act (reflection n (ZMod 2) i hi.1 hi.2) (act g⁻¹ a)) := by
      rw [← D.act_mul, ← D.act_mul]
    rw [e3, h1, ← D.act_mul, mul_inv_cancel, D.act_one]
  exact (D.twist g).fix_reflection hV2 hn hFix' hv hvf hi hic

end VModel

end CFSG.Quasithin.FLc
