module

public import CFSG.Quasithin.Background.D2Basic
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin Subgroup

variable {W : Type*} [CommGroup W] [Finite W]

theorem w16g_fixV_sup (X Y : Subgroup (MulAut W)) : fixV (X ⊔ Y) = fixV X ⊓ fixV Y := by
  ext w
  simp only [mem_fixV, Subgroup.mem_inf]
  constructor
  · intro h
    exact ⟨fun x hx => h x (Subgroup.mem_sup_left hx),
      fun y hy => h y (Subgroup.mem_sup_right hy)⟩
  · rintro ⟨hX, hY⟩ z hz
    have hle : X ⊔ Y ≤ MulAction.stabilizer (MulAut W) w :=
      sup_le (fun x hx => MulAction.mem_stabilizer_iff.mpr (hX x hx))
        (fun y hy => MulAction.mem_stabilizer_iff.mpr (hY y hy))
    exact MulAction.mem_stabilizer_iff.mp (hle hz)

theorem w16g_rk_finsetSup_eq_sum (hW : ∀ w : W, w ^ 2 = 1) {ι : Type*} (F : ι → Subgroup W)
    (s : Finset ι) (h : s.SupIndep F) : rk ↥(s.sup F) = ∑ i ∈ s, rk (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sup_empty, rk_bot, Finset.sum_empty]
  | insert a s ha ih =>
      rw [Finset.sup_insert, Finset.sum_insert ha]
      have hs : s.SupIndep F := h.subset (Finset.subset_insert a s)
      have hdisj : Disjoint (F a) (s.sup F) := by
        have h1 := (Finset.supIndep_iff_disjoint_erase).mp h a (Finset.mem_insert_self a s)
        rwa [Finset.erase_insert ha] at h1
      have hinf : F a ⊓ s.sup F = ⊥ := hdisj.eq_bot
      have h1 := rk_sup_add_rk_inf (F a) (s.sup F)
      rw [hinf, rk_bot, add_zero] at h1
      rw [h1, ih hs]

theorem w16g_rk_iSup_eq_sum (hW : ∀ w : W, w ^ 2 = 1) {ι : Type*} [Fintype ι]
    (F : ι → Subgroup W) (h : iSupIndep F) : rk ↥(⨆ i, F i) = ∑ i, rk (F i) := by
  have hs : (Finset.univ : Finset ι).SupIndep F := (iSupIndep_iff_supIndep_univ).mp h
  have h1 := w16g_rk_finsetSup_eq_sum hW F Finset.univ hs
  rw [Finset.sup_eq_iSup] at h1
  have h2 : (⨆ a ∈ Finset.univ, F a) = ⨆ i, F i := by
    apply le_antisymm
    · exact iSup_le fun a => iSup_le fun _ => le_iSup F a
    · exact iSup_le fun a =>
        le_iSup₂ (f := fun i (_ : i ∈ Finset.univ) => F i) a (Finset.mem_univ a)
  rw [h2] at h1
  exact h1

theorem w16g_conj_inv_of_mem_zpowers {A : Type*} [Group A] {t x : A}
    (h : t * x * t⁻¹ = x⁻¹) {a : A} (ha : a ∈ Subgroup.zpowers x) :
    t * a * t⁻¹ = a⁻¹ := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  have hc : MulAut.conj t x = x⁻¹ := by rw [MulAut.conj_apply, h]
  calc t * x ^ k * t⁻¹ = MulAut.conj t (x ^ k) := (MulAut.conj_apply t (x ^ k)).symm
    _ = (MulAut.conj t x) ^ k := map_zpow (MulAut.conj t) x k
    _ = (x⁻¹) ^ k := by rw [hc]
    _ = (x ^ k)⁻¹ := by rw [inv_zpow]

theorem w16g_conj_zpow_self {A : Type*} [Group A] {y z : A} (hyz : y * z = z * y) (n : ℕ) :
    y ^ n * z * (y ^ n)⁻¹ = z := by
  have h : y * z * y⁻¹ = z := by rw [hyz]; group
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ,
        show y ^ n * y * z * (y ^ n * y)⁻¹ = y ^ n * (y * z * y⁻¹) * (y ^ n)⁻¹ by group,
        h, ih]

theorem w16g_conj_zpow_x {A : Type*} [Group A] {y x z : A} (hyx : y * x * y⁻¹ = x * z)
    (hyz : y * z = z * y) (n : ℕ) : y ^ n * x * (y ^ n)⁻¹ = x * z ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hz : y ^ n * z * (y ^ n)⁻¹ = z := w16g_conj_zpow_self hyz n
      rw [pow_succ,
        show y ^ n * y * x * (y ^ n * y)⁻¹ = y ^ n * (y * x * y⁻¹) * (y ^ n)⁻¹ by group,
        hyx,
        show y ^ n * (x * z) * (y ^ n)⁻¹
          = (y ^ n * x * (y ^ n)⁻¹) * (y ^ n * z * (y ^ n)⁻¹) by group,
        ih, hz, pow_succ, mul_assoc]

end CFSG.LocalAnalysis.WeakClosure81
