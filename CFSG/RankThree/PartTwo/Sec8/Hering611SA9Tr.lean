module

public import CFSG.RankThree.PartTwo.Sec8.Hering611SA9Rec
public import CFSG.RankThree.PartTwo.Sec8.Hering611SA9Fus
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

open Equiv Equiv.Perm Subgroup

theorem mem_range_conj_of_pow_three_alt9 {M : Type*} [Group M]
    (e : M ≃* alternatingGroup (Fin 9)) {γ : MulAut M} (hγ : γ ^ 3 = 1) :
    γ ∈ (MulAut.conj : M →* MulAut M).range := by
  have hγ' : (MulAut.congr e γ) ^ 3 = 1 := by
    rw [← map_pow, hγ, map_one]
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 9
    (by norm_num) (by norm_num)
  obtain ⟨σ, hσ⟩ := hbij.2 (MulAut.congr e γ)
  have hσ3 : σ ^ 3 = 1 := by
    apply hbij.1
    rw [map_pow, hσ, hγ', map_one]
  have hsign : Perm.sign σ = 1 := by
    have h := congrArg Perm.sign hσ3
    rw [map_pow, map_one] at h
    rcases Int.units_eq_one_or (Perm.sign σ) with h1 | h1
    · exact h1
    · rw [h1] at h
      exact absurd h (by decide)
  obtain ⟨q, hq⟩ : ∃ q : alternatingGroup (Fin 9), (q : Perm (Fin 9)) = σ :=
    ⟨⟨σ, Perm.mem_alternatingGroup.mpr hsign⟩, rfl⟩
  have hconj : MulAut.congr e γ = MulAut.conj q := by
    rw [← hσ, ← hq]
    exact MulAut.conjNormal_val
  rw [MonoidHom.mem_range]
  refine ⟨e.symm q, ?_⟩
  apply MulEquiv.ext
  intro m
  have h1 : γ m = e.symm (MulAut.congr e γ (e m)) := by
    simp [MulAut.congr_apply]
  rw [MulAut.conj_apply, h1, hconj, MulAut.conj_apply]
  simp [map_mul, map_inv]

theorem alt9_fusion {M : Type*} [Group M] (e : M ≃* alternatingGroup (Fin 9)) {x : M}
    (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) {P : Subgroup M} (hP : Group.IsPerfect P)
    (hPc : ∀ p ∈ P, p * x = x * p) (h360 : 360 ∣ Nat.card P) {Eb : Subgroup M} (hEP : Eb ≤ P)
    (hE9 : Nat.card Eb = 9) :
    ∃ w : M, (∀ y ∈ Subgroup.zpowers x ⊔ Eb, w * y * w⁻¹ ∈ Subgroup.zpowers x ⊔ Eb) ∧
      w * x * w⁻¹ ∈ Eb ∧ w * x * w⁻¹ ≠ 1 := by
  haveI : Finite M := Finite.of_injective e e.injective
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h5 : 5 ∣ Nat.card P := (by norm_num : (5 : ℕ) ∣ 360).trans h360
  obtain ⟨p, hp5⟩ := exists_prime_orderOf_dvd_card' (G := ↥P) 5 h5
  have hy5 : orderOf (e (p : M)) = 5 := by
    rw [MulEquiv.orderOf_eq e, Subgroup.orderOf_coe, hp5]
  have hc : e x * e (p : M) = e (p : M) * e x := by
    have h := congrArg e (hPc (p : M) p.2)
    rw [map_mul, map_mul] at h
    exact h.symm
  have hx'3 : e x ^ 3 = 1 := by
    rw [← map_pow, hx3, map_one]
  have hx'1 : e x ≠ 1 := fun h => hx1 (e.injective (by rw [h, map_one]))
  obtain ⟨q, hq⟩ := exists_conj_a9T0 (isThreeCycle_of_commute_order_five hx'3 hx'1 hy5 hc)
  obtain ⟨e', he'x⟩ : ∃ e' : M ≃* alternatingGroup (Fin 9), e' x = a9fT0 :=
    ⟨e.trans (MulAut.conj q), by rw [MulEquiv.trans_apply, MulAut.conj_apply, hq]⟩
  have hfx : e'.toMonoidHom x = a9fT0 := he'x
  have hP' : Group.IsPerfect (P.map e'.toMonoidHom) := Group.IsPerfect.map e'.toMonoidHom
  have hPc' : ∀ p' ∈ P.map e'.toMonoidHom, p' * a9fT0 = a9fT0 * p' := by
    intro p' hp'
    obtain ⟨p0, hp0, rfl⟩ := Subgroup.mem_map.mp hp'
    rw [← he'x]
    show e' p0 * e' x = e' x * e' p0
    rw [← map_mul, ← map_mul, hPc p0 hp0]
  have hEP' : Eb.map e'.toMonoidHom ≤ P.map e'.toMonoidHom := Subgroup.map_mono hEP
  have hE9' : Nat.card (Eb.map e'.toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective (f := e'.toMonoidHom) e'.injective, hE9]
  obtain ⟨w', hw1, hw2, hw3⟩ := a9_fusion_std hP' hPc' hEP' hE9'
  have hmap : (Subgroup.zpowers x ⊔ Eb).map e'.toMonoidHom =
      Subgroup.zpowers a9fT0 ⊔ Eb.map e'.toMonoidHom := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, hfx]
  have hconj : ∀ z : M, e'.symm w' * z * (e'.symm w')⁻¹ = e'.symm (w' * e' z * w'⁻¹) := by
    intro z
    simp [map_mul, map_inv]
  refine ⟨e'.symm w', ?_, ?_, ?_⟩
  · intro y hy
    have hy' : e' y ∈ Subgroup.zpowers a9fT0 ⊔ Eb.map e'.toMonoidHom := by
      rw [← hmap]
      exact Subgroup.mem_map_of_mem _ hy
    have h := hw1 (e' y) hy'
    rw [← hmap, Subgroup.mem_map_equiv] at h
    rw [hconj]
    exact h
  · have h : w' * e' x * w'⁻¹ ∈ Eb.map e'.toMonoidHom := by
      rw [he'x]
      exact hw2
    rw [hconj]
    exact Subgroup.mem_map_equiv.mp h
  · rw [hconj]
    intro h
    apply hw3
    have h' : w' * e' x * w'⁻¹ = 1 := by
      have h2 := congrArg e' h
      rwa [MulEquiv.apply_symm_apply, map_one] at h2
    rw [he'x] at h'
    exact h'

end CFSG.RankThree.PartTwo.Sec8.Hering611
