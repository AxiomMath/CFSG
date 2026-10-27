module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.Quasithin.H13.KG3312

open Equiv
open scoped Pointwise

@[expose] def pa : Perm (Fin 5) := swap 0 1 * swap 2 3

@[expose] def pa2 : Perm (Fin 5) := swap 0 2 * swap 1 3

@[expose] def pa3 : Perm (Fin 5) := swap 0 3 * swap 1 2

@[expose] def pb : Perm (Fin 5) := swap 1 2 * swap 2 4

@[expose] def kleinL : List (Perm (Fin 5)) := [1, pa, pa2, pa3]

@[expose] def a5Word {G : Type*} [Group G] (x y : G) : G := y * x * y⁻¹ * x * y * x * y⁻¹ * x * y

theorem map_a5Word {G H : Type*} [Group G] [Group H] (f : G →* H) (x y : G) :
    f (a5Word x y) = a5Word (f x) (f y) := by
  simp [a5Word]

theorem a5_forced : ∀ y : Perm (Fin 5), y * y * y = 1 → (pa * y) ^ 5 = 1 → a5Word pa y = pa2 →
    ∃ w ∈ kleinL, y = w * pb * w⁻¹ := by
  decide +kernel

theorem kleinL_mul : ∀ p ∈ kleinL, ∀ q ∈ kleinL, p * q ∈ kleinL := by decide +kernel

theorem kleinL_inv : ∀ p ∈ kleinL, p⁻¹ ∈ kleinL := by decide +kernel

theorem kleinL_sq : ∀ p ∈ kleinL, p * p = 1 := by decide +kernel

theorem kleinL_comm : ∀ p ∈ kleinL, p * pa * p⁻¹ = pa := by decide +kernel

theorem kleinL_sign : ∀ p ∈ kleinL, Perm.sign p = 1 := by decide +kernel

theorem gens_rel : pb * pb * pb = 1 ∧ (pa * pb) ^ 5 = 1 ∧ a5Word pa pb = pa2 := by decide +kernel

theorem gens_ne : pa * pa = 1 ∧ pa ≠ 1 ∧ pb ≠ 1 ∧ pa * pb ≠ 1 := by decide +kernel

theorem sign_pb : Perm.sign pb = 1 := by decide +kernel

@[expose] def kleinA5 : Subgroup (alternatingGroup (Fin 5)) where
  carrier := {x | (x : Perm (Fin 5)) ∈ kleinL}
  mul_mem' {_ _} hx hy := kleinL_mul _ hx _ hy
  one_mem' := by decide
  inv_mem' {_} hx := kleinL_inv _ hx

@[expose] def aA : alternatingGroup (Fin 5) :=
  ⟨pa, Perm.mem_alternatingGroup.mpr (kleinL_sign pa (by decide))⟩

@[expose] def a2A : alternatingGroup (Fin 5) :=
  ⟨pa2, Perm.mem_alternatingGroup.mpr (kleinL_sign pa2 (by decide))⟩

@[expose] def bA : alternatingGroup (Fin 5) := ⟨pb, Perm.mem_alternatingGroup.mpr sign_pb⟩

theorem card_alt5' : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [Nat.card_eq_fintype_card]
  rfl

theorem isPGroup_kleinA5 : IsPGroup 2 kleinA5 := fun x => ⟨1, by
  apply Subtype.ext
  apply Subtype.ext
  have h := kleinL_sq _ x.2
  simpa [pow_two] using h⟩

theorem closure_a5Gens : Subgroup.closure ({aA, bA} : Set (alternatingGroup (Fin 5))) = ⊤ := by
  set H := Subgroup.closure ({aA, bA} : Set (alternatingGroup (Fin 5))) with hH
  have haH : aA ∈ H := Subgroup.subset_closure (by simp)
  have hbH : bA ∈ H := Subgroup.subset_closure (by simp)
  obtain ⟨hb3, hab5, -⟩ := gens_rel
  obtain ⟨haa, ha1, hb1, hab1⟩ := gens_ne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hoa : orderOf aA = 2 := orderOf_eq_prime (by
      apply Subtype.ext
      simpa [pow_two, aA] using haa) (fun h => ha1 (congrArg Subtype.val h))
  have hob : orderOf bA = 3 := orderOf_eq_prime (by
      apply Subtype.ext
      simpa [pow_three, bA, mul_assoc] using hb3) (fun h => hb1 (congrArg Subtype.val h))
  have hoab : orderOf (aA * bA) = 5 := orderOf_eq_prime (by
      apply Subtype.ext
      simpa [aA, bA] using hab5) (fun h => hab1 (congrArg Subtype.val h))
  have h2 : 2 ∣ Nat.card H := by
    have := orderOf_dvd_natCard (⟨aA, haH⟩ : H)
    rwa [Subgroup.orderOf_mk, hoa] at this
  have h3 : 3 ∣ Nat.card H := by
    have := orderOf_dvd_natCard (⟨bA, hbH⟩ : H)
    rwa [Subgroup.orderOf_mk, hob] at this
  have h5 : 5 ∣ Nat.card H := by
    have := orderOf_dvd_natCard (⟨aA * bA, H.mul_mem haH hbH⟩ : H)
    rwa [Subgroup.orderOf_mk, hoab] at this
  have h60 : Nat.card H ∣ 60 := card_alt5' ▸ Subgroup.card_subgroup_dvd_card H
  have hle : Nat.card H ≤ 60 := Nat.le_of_dvd (by norm_num) h60
  have hcases : Nat.card H = 30 ∨ Nat.card H = 60 := by
    obtain ⟨k, hk⟩ := h60
    have hpos : 0 < Nat.card H := Nat.card_pos
    omega
  rcases hcases with h | h
  · exfalso
    have hidx : H.index = 2 := by
      have := Subgroup.card_mul_index H
      rw [h, card_alt5'] at this
      omega
    have : H.Normal := Subgroup.normal_of_index_eq_two hidx
    have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal H with hb | ht
    · rw [hb, Subgroup.card_bot] at h
      omega
    · rw [ht, Subgroup.card_top, card_alt5'] at h
      omega
  · exact Subgroup.eq_top_of_card_eq H (h.trans card_alt5'.symm)

theorem aut_kleinA5 (ψ : MulAut (alternatingGroup (Fin 5))) (hψ : ∀ k ∈ kleinA5, ψ k = k) :
    ∃ w ∈ kleinA5, ∀ y, ψ y = w * y * w⁻¹ := by
  obtain ⟨hb3, hab5, hword⟩ := gens_rel
  have ha : ψ aA = aA := hψ aA (show pa ∈ kleinL by decide)
  have ha2 : ψ a2A = a2A := hψ a2A (show pa2 ∈ kleinL by decide)
  set y : Perm (Fin 5) := ((ψ bA : alternatingGroup (Fin 5)) : Perm (Fin 5)) with hy
  have hy3 : y * y * y = 1 := by
    have h1 : bA * bA * bA = 1 := Subtype.ext hb3
    have h2 := congrArg (fun z => ((ψ z : alternatingGroup (Fin 5)) : Perm (Fin 5))) h1
    simpa [map_mul] using h2
  have hy5 : (pa * y) ^ 5 = 1 := by
    have h1 : (aA * bA) ^ 5 = 1 := Subtype.ext hab5
    have h2 := congrArg (fun z => ((ψ z : alternatingGroup (Fin 5)) : Perm (Fin 5))) h1
    simp only [map_pow, map_mul, ha, map_one] at h2
    simpa [aA] using h2
  have hyw : a5Word pa y = pa2 := by
    have h1 : a5Word aA bA = a2A := Subtype.ext hword
    have h2 := congrArg (fun z => ((ψ z : alternatingGroup (Fin 5)) : Perm (Fin 5))) h1
    simp only [show ∀ z, ψ z = ψ.toMonoidHom z from fun _ => rfl] at h2
    rw [map_a5Word, show ψ.toMonoidHom aA = aA from ha, show ψ.toMonoidHom a2A = a2A from ha2]
      at h2
    simpa [a5Word, aA, a2A] using h2
  obtain ⟨w, hwL, hwy⟩ := a5_forced y hy3 hy5 hyw
  let wA : alternatingGroup (Fin 5) :=
    ⟨w, Perm.mem_alternatingGroup.mpr (kleinL_sign w hwL)⟩
  refine ⟨wA, hwL, fun z => ?_⟩
  have heq : ψ.toMonoidHom = (MulAut.conj wA).toMonoidHom := by
    refine MonoidHom.eq_of_eqOn_dense closure_a5Gens ?_
    intro x hx
    rcases hx with rfl | rfl
    · show ψ aA = wA * aA * wA⁻¹
      rw [ha]
      exact Subtype.ext (kleinL_comm w hwL).symm
    · show ψ bA = wA * bA * wA⁻¹
      exact Subtype.ext hwy
  exact congrArg (fun F : alternatingGroup (Fin 5) →* alternatingGroup (Fin 5) => F z) heq

theorem aut_alt5_fix_four {B : Type} [Group B] (f : B ≃* alternatingGroup (Fin 5))
    {W : Subgroup B} (hW : Nat.card W = 4) (φ : MulAut B) (hφ : ∀ w ∈ W, φ w = w) :
    ∃ w ∈ W, ∀ y, φ y = w * y * w⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W' : Subgroup (alternatingGroup (Fin 5)) := W.map f.toMonoidHom with hW'
  have hW'4 : Nat.card W' = 4 := by rw [hW', Subgroup.card_map_of_injective f.injective, hW]
  have hW'p : IsPGroup 2 W' := IsPGroup.of_card (n := 2) (by rw [hW'4]; norm_num)
  have hW'i : ¬ 2 ∣ W'.index := by
    have := Subgroup.card_mul_index W'
    rw [hW'4, card_alt5'] at this
    omega
  obtain ⟨P, hP⟩ := isPGroup_kleinA5.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 5)) (hW'p.toSylow hW'i) P
  have hKle : kleinA5 ≤ MulAut.conj g • W' := by
    have := congrArg
      (fun Q : Sylow 2 (alternatingGroup (Fin 5)) => (Q : Subgroup (alternatingGroup (Fin 5)))) hg
    simp only [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe] at this
    rw [this]
    exact hP
  set χ : MulAut (alternatingGroup (Fin 5)) := MulAut.congr f φ with hχ
  have hχW : ∀ x ∈ W', χ x = x := by
    rintro _ ⟨w, hw, rfl⟩
    simp [hχ, MulAut.congr_apply, hφ w hw]
  set ψ : MulAut (alternatingGroup (Fin 5)) := MulAut.conj g * χ * (MulAut.conj g)⁻¹ with hψ
  have hψK : ∀ k ∈ kleinA5, ψ k = k := by
    intro k hk
    have hk' := hKle hk
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hk'
    have h1 := hχW _ hk'
    simp only [MulAut.smul_def] at h1
    simp only [hψ, MulAut.mul_apply, h1, MulAut.apply_inv_self]
  obtain ⟨w, hwK, hw⟩ := aut_kleinA5 ψ hψK
  set c := g⁻¹ * w * g with hc
  have hcW : c ∈ W' := by
    have := hKle hwK
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at this
    simpa [MulAut.smul_def, MulAut.conj_inv_apply, hc, mul_assoc] using this
  have hχc : ∀ x, χ x = c * x * c⁻¹ := by
    intro x
    have h1 := hw (g * x * g⁻¹)
    have h2 : χ x = g⁻¹ * ψ (g * x * g⁻¹) * g := by
      simp [hψ, MulAut.mul_apply, MulAut.conj_apply, mul_assoc]
    rw [h2, h1]
    simp [hc, mul_assoc]
  have hχf : ∀ y, χ (f y) = f (φ y) := fun y => by simp [hχ, MulAut.congr_apply]
  obtain ⟨w₁, hw₁, hcw⟩ := hcW
  refine ⟨w₁, hw₁, fun y => ?_⟩
  apply f.injective
  have h1 := hχc (f y)
  rw [hχf] at h1
  have hcw' : f w₁ = c := hcw
  rw [h1, map_mul, map_mul, map_inv, hcw']

end CFSG.Quasithin.H13.KG3312
