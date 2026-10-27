module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3SL24ModelNBBA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.GH74.KGroups CFSG.Open CFSG.Quasithin CFSG.Quasithin.H
open scoped Matrix

theorem s16h_orth3L_faithful_quotient {γ : MulAut Orth3} (hγ : γ ∈ orth3L)
    (h : ∀ v : Orth3, γ v * v⁻¹ ∈ orth3Z) : γ = 1 := by
  rw [s16h_orth3L_eq_range] at hγ
  obtain ⟨δ, rfl⟩ := hγ
  have hA : ((δ : Matrix.GeneralLinearGroup (Fin 2) GF4) :
      Matrix (Fin 2) (Fin 2) GF4) = 1 := by
    apply s16h_orth3ActM_eq_one_of_same_quotient
    intro x
    have hx := h (Multiplicative.ofAdd x)
    simp only [s16h_orth3AutHom_apply, toAdd_ofAdd, s16h_orth3Act_eq] at hx
    exact (s16h_ofAdd_mul_inv_mem_orth3Z_iff _ _).mp hx
  apply MulEquiv.ext
  intro v
  show s16h_orth3AutHom δ v = v
  rw [s16h_orth3AutHom_apply, s16h_orth3Act_eq, hA, s16h_orth3ActM_one]
  exact ofAdd_toAdd v

private def s16h_quotK : Subgroup (MulAut Orth3) where
  carrier := {w | ∀ v : Orth3, w v * v⁻¹ ∈ orth3Z}
  one_mem' := by
    intro v
    simp
  mul_mem' := by
    intro a b ha hb v
    have h1 := ha (b v)
    have h2 := hb v
    rw [MulAut.mul_apply]
    have heq : a (b v) * v⁻¹ = (a (b v) * (b v)⁻¹) * ((b v) * v⁻¹) := by group
    rw [heq]
    exact orth3Z.mul_mem h1 h2
  inv_mem' := by
    intro a ha v
    have h := ha (a⁻¹ v)
    have h' : v * (a⁻¹ v)⁻¹ ∈ orth3Z := by simpa using h
    have hinv := orth3Z.inv_mem h'
    simpa [mul_inv_rev, inv_inv] using hinv

private theorem s16h_orth3L_fix_Z {γ : MulAut Orth3} (hγ : γ ∈ orth3L) {z : Orth3}
    (hz : z ∈ orth3Z) : γ z = z := by
  rw [s16h_orth3L_eq_range] at hγ
  obtain ⟨δ, rfl⟩ := hγ
  exact s16h_orth3Aut_fix_Z δ hz

private theorem s16h_conj_quotK {γ : MulAut Orth3} (hγ : γ ∈ orth3L)
    {w : MulAut Orth3} (hw : w ∈ s16h_quotK) : γ * w * γ⁻¹ ∈ s16h_quotK := by
  intro v
  have hwv := hw (γ⁻¹ v)
  have hZ : γ (w (γ⁻¹ v) * (γ⁻¹ v)⁻¹) ∈ orth3Z := by
    rw [s16h_orth3L_fix_Z hγ hwv]
    exact hwv
  have hgoal : (γ * w * γ⁻¹) v * v⁻¹ = γ (w (γ⁻¹ v) * (γ⁻¹ v)⁻¹) := by
    simp [MulAut.mul_apply]
  rw [hgoal]
  exact hZ

theorem s16h_orth3_normalizer_quotient_faithful {n m : MulAut Orth3}
    (hn : n ∈ Subgroup.normalizer (orth3L : Set (MulAut Orth3)))
    (hm : m ∈ Subgroup.normalizer (orth3L : Set (MulAut Orth3)))
    (h : ∀ v : Orth3, n v * (m v)⁻¹ ∈ orth3Z) : n = m := by
  have hm_inv : m⁻¹ ∈ Subgroup.normalizer (orth3L : Set (MulAut Orth3)) :=
    (Subgroup.normalizer (orth3L : Set (MulAut Orth3))).inv_mem hm
  have hu_mem : n * m⁻¹ ∈ Subgroup.normalizer (orth3L : Set (MulAut Orth3)) :=
    (Subgroup.normalizer (orth3L : Set (MulAut Orth3))).mul_mem hn hm_inv
  have hq : ∀ w : Orth3, (n * m⁻¹) w * w⁻¹ ∈ orth3Z := by
    intro w
    have hw := h (m.symm w)
    simpa [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.apply_symm_apply] using hw
  have hc : ∀ γ ∈ orth3L, (n * m⁻¹) * γ = γ * (n * m⁻¹) := by
    intro γ hγ
    have hu_inv : (n * m⁻¹)⁻¹ ∈ s16h_quotK := s16h_quotK.inv_mem hq
    have hconj : γ * (n * m⁻¹)⁻¹ * γ⁻¹ ∈ s16h_quotK := s16h_conj_quotK hγ hu_inv
    have hδK : (n * m⁻¹) * γ * (n * m⁻¹)⁻¹ * γ⁻¹ ∈ s16h_quotK := by
      have h := s16h_quotK.mul_mem hq hconj
      convert h using 1 <;> group
    have hδL : (n * m⁻¹) * γ * (n * m⁻¹)⁻¹ * γ⁻¹ ∈ orth3L := by
      have h1 : (n * m⁻¹) * γ * (n * m⁻¹)⁻¹ ∈ orth3L :=
        ((Subgroup.mem_normalizer_iff).mp hu_mem γ).mp hγ
      exact orth3L.mul_mem h1 (orth3L.inv_mem hγ)
    have hδ_one : (n * m⁻¹) * γ * (n * m⁻¹)⁻¹ * γ⁻¹ = 1 :=
      s16h_orth3L_faithful_quotient hδL (fun v => hδK v)
    have h2 : (n * m⁻¹) * γ * (n * m⁻¹)⁻¹ = γ := by
      have := congrArg (fun x => x * γ) hδ_one
      simpa [mul_assoc] using this
    calc (n * m⁻¹) * γ = (n * m⁻¹) * γ * (n * m⁻¹)⁻¹ * (n * m⁻¹) := by group
      _ = γ * (n * m⁻¹) := by rw [h2]
  have hu : n * m⁻¹ = 1 := s16h_orth3_centralizes_trivial hc hq
  rw [mul_inv_eq_one] at hu
  exact hu

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
