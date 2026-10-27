module

public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityM6
public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityLang
public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialitySL2Pair

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
open CFSG.RankThree.PartTwo.Sec11

namespace CFSG.RankThree.PartTwo.Sec19

section Generic

variable {K : Type*} [Group K]

theorem planeGen_of_AB {A B : Subgroup K}
    (hmax : ∀ N : Subgroup K, A ⊔ B ≤ N → N = A ⊔ B ∨ N = ⊤) {E : Subgroup (MulAut K)}
    (hA : A ≤ planeClosure E) (hB : B ≤ planeClosure E) (hnot : ¬ planeClosure E ≤ A ⊔ B) :
    PlaneGen E :=
  eq_top_of_maximal_pair hmax hA hB hnot


theorem lang_fixed_identity (τ : MulAut K) {a h y : K} (hlang : a = h * (τ h)⁻¹) (hy : τ y = y) :
    a * τ (h * y * h⁻¹) = (h * y * h⁻¹) * a := by
  rw [map_mul, map_mul, map_inv, hy, hlang]
  group

theorem lang_ne_fix (τ : MulAut K) {a h : K} (hlang : a = h * (τ h)⁻¹) (ha1 : a ≠ 1) :
    τ h ≠ h := fun h1 => ha1 (by rw [hlang, h1, mul_inv_cancel])

theorem lang_not_comm (τ : MulAut K) {a h : K} (hlang : a = h * (τ h)⁻¹) (ha1 : a ≠ 1) :
    a * τ h ≠ h * a := by
  intro hc
  have h2 : a * τ h = h := by rw [hlang]; group
  rw [h2] at hc
  apply ha1
  have : h * a = h * 1 := by rw [mul_one]; exact hc.symm
  exact mul_left_cancel this

end Generic

section EbN4


variable {n : ℕ} {X : Type} [Field X] [Finite X] {σ : X ≃+* X}

theorem planeGen_Eb (hgold : CFSG.Goldschmidt.TopStatement) (P : D4Par n X σ) (hn : 2 ≤ n)
    {a b : C0 σ} (ha : a ∈ Asub σ) (hb : b ∈ Bsub σ) (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) :
    PlaneGen (Subgroup.closure ({MulAut.conj a, MulAut.conj b} : Set (MulAut (C0 σ)))) := by
  set E := Subgroup.closure ({MulAut.conj a, MulAut.conj b} : Set (MulAut (C0 σ))) with hE
  have hca : (MulAut.conj a : MulAut (C0 σ)) ∈ E := Subgroup.subset_closure (by simp)
  have hcb : (MulAut.conj b : MulAut (C0 σ)) ∈ E := Subgroup.subset_closure (by simp)
  have hca1 := conj_ne_one P ha1
  have hcb1 := conj_ne_one P hb1
  refine planeGen_of_AB (ab_maximal hgold P hn) ?_ ?_ ?_
  · intro x hx
    exact centralizer_le_planeClosure hcb hcb1
      (Subgroup.mem_centralizer_singleton_iff.mpr (Asub_Bsub_commute hx hb))
  · intro y hy
    exact centralizer_le_planeClosure hca hca1
      (Subgroup.mem_centralizer_singleton_iff.mpr (Asub_Bsub_commute ha hy).symm)
  · exact fun hle => centralizer_a_not_le_AB P hn ha ha3 ha1
      ((centralizer_le_planeClosure hca hca1).trans hle)

theorem planeGen_N4 (hgold : CFSG.Goldschmidt.TopStatement) (P : D4Par n X σ) (hn : 2 ≤ n)
    {b : C0 σ} (hb : b ∈ Bsub σ) (hb3 : b ^ 3 = 1) (hb1 : b ≠ 1) :
    PlaneGen (Subgroup.closure ({MulAut.conj b, tauAut σ} : Set (MulAut (C0 σ)))) := by
  set E := Subgroup.closure ({MulAut.conj b, tauAut σ} : Set (MulAut (C0 σ))) with hE
  have hcb : (MulAut.conj b : MulAut (C0 σ)) ∈ E := Subgroup.subset_closure (by simp)
  have hτE : (tauAut σ : MulAut (C0 σ)) ∈ E := Subgroup.subset_closure (by simp)
  have hcb1 := conj_ne_one P hb1
  have hτ1 := tauAut_ne_one P
  have hG : Gsub σ ≤ planeClosure E := fun x hx =>
    mem_planeClosure_of_fixed hτE hτ1 (show tauAut σ x = x from hx)
  refine planeGen_of_AB (ab_maximal hgold P hn) ?_ ?_ ?_
  · intro x hx
    exact centralizer_le_planeClosure hcb hcb1
      (Subgroup.mem_centralizer_singleton_iff.mpr (Asub_Bsub_commute hx hb))
  · exact fun y hy => hG (Bsub_le_Gsub P hy)
  · exact fun hle => Gsub_not_le_AB P (hG.trans hle)

end EbN4

section N3Nreg


variable {n : ℕ} {X : Type} [Field X] [Finite X] {σ : X ≃+* X}

theorem planeGen_N3 (hgold : CFSG.Goldschmidt.TopStatement) (P : D4Par n X σ) (hn : 2 ≤ n)
    {a : C0 σ} (ha : a ∈ A0sub σ) (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1) :
    PlaneGen (Subgroup.closure ({MulAut.conj a, tauAut σ} : Set (MulAut (C0 σ)))) := by
  set E := Subgroup.closure ({MulAut.conj a, tauAut σ} : Set (MulAut (C0 σ))) with hE
  have haA : a ∈ Asub σ := ha.1
  have hca : (MulAut.conj a : MulAut (C0 σ)) ∈ E := Subgroup.subset_closure (by simp)
  have hτE : (tauAut σ : MulAut (C0 σ)) ∈ E := Subgroup.subset_closure (by simp)
  have hca1 := conj_ne_one P ha1
  have hτ1 := tauAut_ne_one P
  obtain ⟨h, hhA, hlang⟩ := exists_lang_A0 P ha ha3
  have hnotfix := lang_ne_fix (tauAut σ) hlang ha1
  have hh0 : h ∉ A0sub σ := fun hh => hnotfix (show tauAut σ h = h from hh.2)
  have he : (MulAut.conj a * tauAut σ : MulAut (C0 σ)) ∈ E := E.mul_mem hca hτE
  have he1 : (MulAut.conj a * tauAut σ : MulAut (C0 σ)) ≠ 1 := by
    intro h1
    have h3 : (MulAut.conj a * tauAut σ : MulAut (C0 σ)) h = h := by rw [h1]; rfl
    exact lang_not_comm (tauAut σ) hlang ha1 ((conj_tau_fixed σ a h).mp h3)
  have hA0 : A0sub σ ≤ planeClosure E := fun x hx =>
    mem_planeClosure_of_fixed hτE hτ1 (show tauAut σ x = x from hx.2)
  have hfix : ∀ y ∈ A0sub σ, h * y * h⁻¹ ∈ planeClosure E := by
    intro y hy
    refine mem_planeClosure_of_fixed he he1 ((conj_tau_fixed σ a _).mpr ?_)
    exact lang_fixed_identity (tauAut σ) hlang (show tauAut σ y = y from hy.2)
  have hA : Asub σ ≤ planeClosure E := A_le_of_pair P hn hA0 hhA hh0 hfix
  refine planeGen_of_AB (ab_maximal hgold P hn) hA ?_ ?_
  · intro y hy
    exact centralizer_le_planeClosure hca hca1
      (Subgroup.mem_centralizer_singleton_iff.mpr (Asub_Bsub_commute haA hy).symm)
  · exact fun hle => centralizer_a_not_le_AB P hn haA ha3 ha1
      ((centralizer_le_planeClosure hca hca1).trans hle)

theorem planeGen_Nreg (hgold : CFSG.Goldschmidt.TopStatement) (P : D4Par n X σ) (hn : 2 ≤ n)
    {a b : C0 σ} (ha : a ∈ A0sub σ) (hb : b ∈ Bsub σ) (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) :
    PlaneGen (Subgroup.closure
      ({MulAut.conj a, MulAut.conj b * tauAut σ} : Set (MulAut (C0 σ)))) := by
  set E := Subgroup.closure
    ({MulAut.conj a, MulAut.conj b * tauAut σ} : Set (MulAut (C0 σ))) with hE
  have haA : a ∈ Asub σ := ha.1
  have hca : (MulAut.conj a : MulAut (C0 σ)) ∈ E := Subgroup.subset_closure (by simp)
  have hβE : (MulAut.conj b * tauAut σ : MulAut (C0 σ)) ∈ E := Subgroup.subset_closure (by simp)
  have hca1 := conj_ne_one P ha1
  obtain ⟨h, hhA, hlang⟩ := exists_lang_A0 P ha ha3
  have hnotfix := lang_ne_fix (tauAut σ) hlang ha1
  have hh0 : h ∉ A0sub σ := fun hh => hnotfix (show tauAut σ h = h from hh.2)
  have hbA : ∀ x ∈ Asub σ, b * x = x * b := fun x hx => (Asub_Bsub_commute hx hb).symm
  have hτhA : tauAut σ h ∈ Asub σ := tau_mem_Asub P hhA
  have hβ1 : (MulAut.conj b * tauAut σ : MulAut (C0 σ)) ≠ 1 := by
    intro h1
    have h3 : (MulAut.conj b * tauAut σ : MulAut (C0 σ)) h = h := by rw [h1]; rfl
    have h4 := (conj_tau_fixed σ b h).mp h3
    rw [hbA _ hτhA] at h4
    exact hnotfix (mul_right_cancel h4)
  have hγE : (MulAut.conj (a * b) * tauAut σ : MulAut (C0 σ)) ∈ E := by
    have e : (MulAut.conj (a * b) * tauAut σ : MulAut (C0 σ)) =
        MulAut.conj a * (MulAut.conj b * tauAut σ) := by
      rw [map_mul, mul_assoc]
    rw [e]
    exact E.mul_mem hca hβE
  have hγ1 : (MulAut.conj (a * b) * tauAut σ : MulAut (C0 σ)) ≠ 1 := by
    intro h1
    have h3 : (MulAut.conj (a * b) * tauAut σ : MulAut (C0 σ)) h = h := by rw [h1]; rfl
    have h4 := (conj_tau_fixed σ (a * b) h).mp h3
    have h5 : a * tauAut σ h * b = h * a * b := by
      calc a * tauAut σ h * b = a * (tauAut σ h * b) := by rw [mul_assoc]
        _ = a * (b * tauAut σ h) := by rw [hbA _ hτhA]
        _ = a * b * tauAut σ h := by rw [mul_assoc]
        _ = h * (a * b) := h4
        _ = h * a * b := by rw [mul_assoc]
    exact lang_not_comm (tauAut σ) hlang ha1 (mul_right_cancel h5)
  have hA0 : A0sub σ ≤ planeClosure E := by
    intro y hy
    have hyA : y ∈ Asub σ := hy.1
    have hτy : tauAut σ y = y := hy.2
    refine mem_planeClosure_of_fixed hβE hβ1 ((conj_tau_fixed σ b y).mpr ?_)
    rw [hτy]
    exact hbA y hyA
  have hfix : ∀ y ∈ A0sub σ, h * y * h⁻¹ ∈ planeClosure E := by
    intro y hy
    have hyA : y ∈ Asub σ := hy.1
    have hτy : tauAut σ y = y := hy.2
    have hkA : h * y * h⁻¹ ∈ Asub σ := Asub σ |>.mul_mem (Asub σ |>.mul_mem hhA hyA)
      (Asub σ |>.inv_mem hhA)
    have hτkA : tauAut σ (h * y * h⁻¹) ∈ Asub σ := tau_mem_Asub P hkA
    refine mem_planeClosure_of_fixed hγE hγ1 ((conj_tau_fixed σ (a * b) _).mpr ?_)
    have hid := lang_fixed_identity (tauAut σ) hlang hτy
    set k : C0 σ := h * y * h⁻¹ with hk
    calc a * b * tauAut σ k = a * (b * tauAut σ k) := mul_assoc a b _
      _ = a * (tauAut σ k * b) := by rw [hbA _ hτkA]
      _ = a * tauAut σ k * b := (mul_assoc a _ b).symm
      _ = k * a * b := by rw [hid]
      _ = k * (a * b) := mul_assoc k a b
  have hA : Asub σ ≤ planeClosure E := A_le_of_pair P hn hA0 hhA hh0 hfix
  refine planeGen_of_AB (ab_maximal hgold P hn) hA ?_ ?_
  · intro y hy
    exact centralizer_le_planeClosure hca hca1
      (Subgroup.mem_centralizer_singleton_iff.mpr (Asub_Bsub_commute haA hy).symm)
  · exact fun hle => centralizer_a_not_le_AB P hn haA ha3 ha1
      ((centralizer_le_planeClosure hca hca1).trans hle)

end N3Nreg

end CFSG.RankThree.PartTwo.Sec19
