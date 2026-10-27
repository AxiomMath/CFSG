module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K47d

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.FFModules (fixSub)
open CFSG.LocalAnalysis.UniquenessCase.UC6
open scoped MatrixGroups

section Central

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem central_involution_false_uc6 (ρ : Representation (ZMod 2) G V) (hρ : Function.Injective ρ)
    [ρ.IsIrreducible] {z : G} (hz : z ∈ Subgroup.center G) (hz2 : z ^ 2 = 1) : z = 1 := by
  obtain ⟨n, hn⟩ : ∃ n : Module.End (ZMod 2) V, n = ρ z - 1 := ⟨_, rfl⟩
  have hzz : ρ z * ρ z = 1 := by rw [← map_mul, ← sq, hz2, map_one]
  have hn2 : n * n = 0 := by
    have h2 : n * n = ρ z * ρ z - (ρ z + ρ z) + 1 := by
      rw [hn]
      noncomm_ring
    have h3 := end_add_self_eq_zero_uc6 (ρ z)
    have h4 := end_add_self_eq_zero_uc6 (1 : Module.End (ZMod 2) V)
    rw [h2, hzz, h3, sub_zero, h4]
  have hcomm : ∀ (g : G) (v : V), n (ρ g v) = ρ g (n v) := by
    intro g v
    have h1 : ρ z * ρ g = ρ g * ρ z := by
      rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hz g).symm]
    have := congrArg (fun f : Module.End (ZMod 2) V => f v) h1
    rw [hn]
    simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub]
    simp only [Module.End.mul_apply] at this
    rw [this]
  have hnt : Nontrivial V :=
    IsSimpleModule.nontrivial (MonoidAlgebra (ZMod 2) G) ρ.asModule
  let f : Representation.IntertwiningMap ρ ρ :=
    LinearMap.intertwiningMap_of_isIntertwiningMap ρ ρ n hcomm
  have hfn : ∀ v, f v = n v := fun v => rfl
  rcases Representation.IsIrreducible.injective_or_eq_zero f with hinj | h0
  · exfalso
    obtain ⟨u, hu⟩ := exists_ne (0 : V)
    have h1 : n (n u) = 0 := by
      have := congrArg (fun g : Module.End (ZMod 2) V => g u) hn2
      simp only [Module.End.mul_apply, LinearMap.zero_apply] at this
      exact this
    have h2 : n u = 0 := by
      apply hinj
      show f (n u) = f 0
      rw [hfn, map_zero]
      exact h1
    exact hu (by
      apply hinj
      show f u = f 0
      rw [map_zero, hfn]
      exact h2)
  · apply hρ
    rw [map_one]
    ext v
    have h3 : f v = 0 := by rw [h0]; rfl
    rw [hfn, hn] at h3
    simpa [sub_eq_zero] using h3

end Central

section SL2

theorem exists_central_involution_sl2_uc6 {F : Type} [Field F] [Finite F]
    (hF : Odd (Nat.card F)) :
    ∃ z : SL(2, F), z ∈ Subgroup.center SL(2, F) ∧ z ^ 2 = 1 ∧ z ≠ 1 := by
  haveI : Fintype F := Fintype.ofFinite F
  have hchar : (2 : F) ≠ 0 := by
    intro h2
    haveI : CharP F 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
    obtain ⟨k, hk⟩ := FiniteField.card F 2
    rw [Nat.card_eq_fintype_card, hk.2] at hF
    have : Even (2 ^ (k : ℕ)) := (Nat.even_pow.2 ⟨even_two, k.ne_zero⟩)
    exact (Nat.not_even_iff_odd.2 hF) this
  have hdet : (-1 : Matrix (Fin 2) (Fin 2) F).det = 1 := by
    simp [Matrix.det_neg]
  let z : SL(2, F) := ⟨-1, hdet⟩
  refine ⟨z, ?_, ?_, ?_⟩
  · rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    show (g : Matrix (Fin 2) (Fin 2) F) * (-1) = (-1) * (g : Matrix (Fin 2) (Fin 2) F)
    simp
  · apply Subtype.ext
    show (-1 : Matrix (Fin 2) (Fin 2) F) ^ 2 = 1
    simp [pow_two]
  · intro h
    have h1 : (-1 : Matrix (Fin 2) (Fin 2) F) 0 0 = (1 : Matrix (Fin 2) (Fin 2) F) 0 0 :=
      congrArg (fun x : SL(2, F) => (x : Matrix (Fin 2) (Fin 2) F) 0 0) h
    simp only [Matrix.neg_apply, Matrix.one_apply_eq] at h1
    apply hchar
    linear_combination -h1

end SL2

section KleinAlg

variable {R : Type*} [Ring R]

theorem klein_core_uc6 (h2 : ∀ x : R, x + x = 0) (A B C T : R) (hAA : A * A = 0)
    (hC : C = A + B + A * B) (hAB : A * B = B * A) (hBT : B * T = T * A) (hCT : C * T = T * B)
    (hT3 : T * T * T = 1) (hN : 1 + T + T * T = 0) : A * B = 0 := by
  have hneg : ∀ x : R, -x = x := fun x => neg_eq_iff_add_eq_zero.2 (h2 x)
  have hT2 : T * T = 1 + T := by
    have : T * T = -(1 + T) := eq_neg_of_add_eq_zero_right hN
    rw [this, hneg]
  have hB' : B = T * A * (T * T) := by
    calc B = B * (T * T * T) := by rw [hT3, mul_one]
      _ = (B * T) * (T * T) := by simp only [mul_assoc]
      _ = (T * A) * (T * T) := by rw [hBT]
  have hC' : C = A * T + T * A * T := by
    calc C = C * (T * T * T) := by rw [hT3, mul_one]
      _ = (C * T) * (T * T) := by simp only [mul_assoc]
      _ = (T * B) * (T * T) := by rw [hCT]
      _ = T * (T * A * (T * T)) * (T * T) := by rw [← hB']
      _ = (T * T) * A * ((T * T) * (T * T)) := by simp only [mul_assoc]
      _ = (T * T) * A * T := by
          have : (T * T) * (T * T) = T := by
            calc (T * T) * (T * T) = (T * T * T) * T := by simp only [mul_assoc]
              _ = T := by rw [hT3, one_mul]
          rw [this]
      _ = (1 + T) * A * T := by rw [hT2]
      _ = A * T + T * A * T := by noncomm_ring
  have hB'' : B = T * A + T * A * T := by
    rw [hB', hT2]
    noncomm_ring
  have hAB' : A * B = A + T * A + A * T := by
    have h1 : A * B = C + A + B := by
      calc A * B = A * B + (A + A) + (B + B) := by rw [h2 A, h2 B, add_zero, add_zero]
        _ = (A + B + A * B) + A + B := by abel
        _ = C + A + B := by rw [hC]
    rw [h1, hC', hB'']
    have h3 := h2 (T * A * T)
    calc A * T + T * A * T + A + (T * A + T * A * T)
        = A + T * A + A * T + (T * A * T + T * A * T) := by abel
      _ = A + T * A + A * T := by rw [h3, add_zero]
  have hATA : A * T * A = 0 := by
    have h1 : A * (A * B) = 0 := by rw [← mul_assoc, hAA, zero_mul]
    rw [hAB'] at h1
    have h4 : A * (A + T * A + A * T) = A * A + A * T * A + A * A * T := by noncomm_ring
    rw [h4, hAA] at h1
    simpa using h1
  have hBA : B * A = 0 := by
    calc B * A = T * A * (T * T) * A := by rw [← hB']
      _ = T * (A * A) + T * (A * T * A) := by rw [hT2]; noncomm_ring
      _ = 0 := by rw [hAA, hATA]; simp
  rw [hAB, hBA]

end KleinAlg

section KleinGroup

variable {G : Type} [Group G] [Finite G]

theorem exists_klein_basis_uc6 {d : G} (hd3 : orderOf d = 3) {S : Subgroup G}
    (hS : CFSG.Open.IsElemAbelian 2 S) (hS4 : Nat.card S = 4)
    (hdS : d ∈ normalizer (S : Set G)) (hcomm : ⁅Subgroup.zpowers d, S⁆ = S) :
    ∃ a b : G, a ∈ S ∧ b ∈ S ∧ a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b ∧ b = d * a * d⁻¹ ∧
      d * b * d⁻¹ = a * b ∧ (∀ x ∈ S, x = 1 ∨ x = a ∨ x = b ∨ x = a * b) ∧ a * b = b * a ∧
      a ^ 2 = 1 ∧ b ^ 2 = 1 := by
  have hSab : IsMulCommutative ↥S := hS.1
  have hS2 : ∀ x ∈ S, x ^ 2 = 1 := hS.2
  have hd3pow : d ^ 3 = 1 := hd3 ▸ pow_orderOf_eq_one d
  have hd3' : d * (d * d) = 1 := by rw [← pow_three]; exact hd3pow
  have hconjS : ∀ x ∈ S, d * x * d⁻¹ ∈ S := fun x hx => (mem_normalizer_iff.1 hdS x).1 hx
  obtain ⟨a, haS, hda⟩ : ∃ a ∈ S, d * a * d⁻¹ ≠ a := by
    by_contra hcon
    push Not at hcon
    have hbot : ⁅Subgroup.zpowers d, S⁆ ≤ ⊥ := by
      rw [Subgroup.commutator_le]
      intro g₁ hg₁ g₂ hg₂
      rw [Subgroup.mem_bot]
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg₁
      have hc : Commute d g₂ := mul_inv_eq_iff_eq_mul.1 (hcon g₂ hg₂)
      exact commutatorElement_eq_one_iff_mul_comm.2 (Commute.zpow_left hc n).eq
    have hSbot : S = ⊥ := le_bot_iff.1 (hcomm ▸ hbot)
    rw [hSbot, Subgroup.card_bot] at hS4
    omega
  have ha1 : a ≠ 1 := by
    rintro rfl
    exact hda (by simp)
  obtain ⟨b, hb⟩ : ∃ b : G, b = d * a * d⁻¹ := ⟨_, rfl⟩
  have hbS : b ∈ S := hb ▸ hconjS a haS
  have hb1 : b ≠ 1 := by
    intro h
    apply ha1
    calc a = d⁻¹ * (d * a * d⁻¹) * d := by group
      _ = d⁻¹ * b * d := by rw [← hb]
      _ = 1 := by rw [h]; group
  have hab : a ≠ b := fun h => hda (hb ▸ h.symm)
  have hb2 : b ^ 2 = 1 := hS2 b hbS
  have ha2 : a ^ 2 = 1 := hS2 a haS
  have hcomm_ab : a * b = b * a := congrArg Subtype.val (hSab.is_comm.comm ⟨a, haS⟩ ⟨b, hbS⟩)
  have hcS : a * b ∈ S := S.mul_mem haS hbS
  have hc1 : a * b ≠ 1 := by
    intro h
    have h1 : a = b⁻¹ := eq_inv_of_mul_eq_one_left h
    have h2 : b⁻¹ = b := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hb2)
    exact hab (h1.trans h2)
  have hca : a * b ≠ a := by
    intro h
    apply hb1
    exact mul_left_cancel (h.trans (mul_one a).symm)
  have hcb : a * b ≠ b := by
    intro h
    apply ha1
    exact mul_right_cancel (h.trans (one_mul b).symm)
  have hlist : ∀ x ∈ S, x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by
    classical
    haveI : Fintype ↥S := Fintype.ofFinite _
    let T : Finset ↥S := {1, ⟨a, haS⟩, ⟨b, hbS⟩, ⟨a * b, hcS⟩}
    have hT1 : (1 : ↥S) ∉ ({⟨a, haS⟩, ⟨b, hbS⟩, ⟨a * b, hcS⟩} : Finset ↥S) := by
      simp [Subtype.ext_iff, Ne.symm ha1, Ne.symm hb1, Ne.symm hc1]
    have hT2 : (⟨a, haS⟩ : ↥S) ∉ ({⟨b, hbS⟩, ⟨a * b, hcS⟩} : Finset ↥S) := by
      simp [Subtype.ext_iff, hab, Ne.symm hca]
    have hT3 : (⟨b, hbS⟩ : ↥S) ≠ ⟨a * b, hcS⟩ := by
      simp [Subtype.ext_iff, Ne.symm hcb]
    have hcard : T.card = Fintype.card ↥S := by
      rw [← Nat.card_eq_fintype_card, hS4]
      simp only [T]
      rw [Finset.card_insert_of_notMem hT1, Finset.card_insert_of_notMem hT2, Finset.card_pair hT3]
    intro x hx
    have hmem : (⟨x, hx⟩ : ↥S) ∈ T := by
      rw [Finset.eq_univ_of_card T hcard]
      exact Finset.mem_univ _
    simpa [T, Subtype.ext_iff] using hmem
  refine ⟨a, b, haS, hbS, ha1, hb1, hab, hb, ?_, hlist, hcomm_ab, ha2, hb2⟩
  have hdbS : d * b * d⁻¹ ∈ S := hconjS b hbS
  rcases hlist _ hdbS with h1 | h1 | h1 | h1
  · exfalso
    apply hb1
    calc b = d⁻¹ * (d * b * d⁻¹) * d := by group
      _ = 1 := by rw [h1]; group
  · exfalso
    apply hda
    calc d * a * d⁻¹ = d * (d * b * d⁻¹) * d⁻¹ := by rw [h1]
      _ = d * (d * (d * a * d⁻¹) * d⁻¹) * d⁻¹ := by rw [← hb]
      _ = (d * (d * d)) * a * (d * (d * d))⁻¹ := by group
      _ = a := by rw [hd3']; group
  · exfalso
    apply hab
    calc a = d⁻¹ * (d * a * d⁻¹) * d := by group
      _ = d⁻¹ * b * d := by rw [← hb]
      _ = d⁻¹ * (d * b * d⁻¹) * d := by rw [h1]
      _ = b := by group
  · exact h1

end KleinGroup

section Quadratic

variable {G : Type} [Group G] [Finite G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem quadratic_of_fixSub_bot_uc6 (ρ : Representation (ZMod 2) G V) {D S : Subgroup G}
    (hD : Nat.card D = 3) (hfix : fixSub ρ D = ⊥) (hS : CFSG.Open.IsElemAbelian 2 S)
    (hS4 : Nat.card S = 4) (hDS : D ≤ normalizer (S : Set G)) (hcomm : ⁅D, S⁆ = S) :
    ∀ s ∈ S, ∀ t ∈ S, ∀ v : V, ρ t (ρ s v - v) = ρ s v - v := by
  obtain ⟨d, hdD, hdord⟩ := exists_generator_uc6 Nat.prime_three hD
  have hdmem : d ∈ D := hdD ▸ Subgroup.mem_zpowers d
  obtain ⟨a, b, haS, hbS, ha1, hb1, hab, hb, hdb, hlist, hcab, ha2, hb2⟩ :=
    exists_klein_basis_uc6 hdord hS hS4 (hDS hdmem) (hdD ▸ hcomm)
  have hd3 : d * d * d = 1 := by rw [← pow_three', ← hdord]; exact pow_orderOf_eq_one d
  have hT3 : ρ d * ρ d * ρ d = 1 := by rw [← map_mul, ← map_mul, hd3, map_one]
  have h2 : ∀ x : Module.End (ZMod 2) V, x + x = 0 := end_add_self_eq_zero_uc6
  have hN : 1 + ρ d + ρ d * ρ d = 0 := by
    apply LinearMap.ext
    intro v
    have hw : (v + ρ d v + ρ d (ρ d v)) ∈ fixSub ρ D := by
      rw [hdD, mem_fixSub_zpowers_uc6]
      have h3 := congrArg (fun f : Module.End (ZMod 2) V => f v) hT3
      simp only [Module.End.mul_apply, Module.End.one_apply] at h3
      rw [map_add, map_add, h3]
      abel
    rw [hfix] at hw
    simpa using (Submodule.mem_bot (ZMod 2)).1 hw
  have hra : ρ a * ρ a = 1 := by rw [← map_mul, ← pow_two, ha2, map_one]
  have hrb : ρ b * ρ b = 1 := by rw [← map_mul, ← pow_two, hb2, map_one]
  have hAA : (ρ a - 1) * (ρ a - 1) = 0 := by
    have h3 := h2 (ρ a)
    have h4 := h2 (1 : Module.End (ZMod 2) V)
    calc (ρ a - 1) * (ρ a - 1) = ρ a * ρ a - (ρ a + ρ a) + 1 := by noncomm_ring
      _ = 0 := by rw [hra, h3, sub_zero, h4]
  have hBB : (ρ b - 1) * (ρ b - 1) = 0 := by
    have h3 := h2 (ρ b)
    have h4 := h2 (1 : Module.End (ZMod 2) V)
    calc (ρ b - 1) * (ρ b - 1) = ρ b * ρ b - (ρ b + ρ b) + 1 := by noncomm_ring
      _ = 0 := by rw [hrb, h3, sub_zero, h4]
  have hC : ρ (a * b) - 1 = (ρ a - 1) + (ρ b - 1) + (ρ a - 1) * (ρ b - 1) := by
    rw [map_mul]
    noncomm_ring
  have hAB : (ρ a - 1) * (ρ b - 1) = (ρ b - 1) * (ρ a - 1) := by
    have : ρ a * ρ b = ρ b * ρ a := by rw [← map_mul, ← map_mul, hcab]
    calc (ρ a - 1) * (ρ b - 1) = ρ a * ρ b - ρ a - ρ b + 1 := by noncomm_ring
      _ = ρ b * ρ a - ρ b - ρ a + 1 := by rw [this]; abel
      _ = (ρ b - 1) * (ρ a - 1) := by noncomm_ring
  have hBT : (ρ b - 1) * ρ d = ρ d * (ρ a - 1) := by
    have : ρ b * ρ d = ρ d * ρ a := by
      rw [← map_mul, ← map_mul, hb]
      congr 1
      group
    calc (ρ b - 1) * ρ d = ρ b * ρ d - ρ d := by noncomm_ring
      _ = ρ d * ρ a - ρ d := by rw [this]
      _ = ρ d * (ρ a - 1) := by noncomm_ring
  have hCT : (ρ (a * b) - 1) * ρ d = ρ d * (ρ b - 1) := by
    have : ρ (a * b) * ρ d = ρ d * ρ b := by
      rw [← map_mul, ← map_mul, ← hdb]
      congr 1
      group
    calc (ρ (a * b) - 1) * ρ d = ρ (a * b) * ρ d - ρ d := by noncomm_ring
      _ = ρ d * ρ b - ρ d := by rw [this]
      _ = ρ d * (ρ b - 1) := by noncomm_ring
  have hAB0 : (ρ a - 1) * (ρ b - 1) = 0 :=
    klein_core_uc6 h2 _ _ _ _ hAA hC hAB hBT hCT hT3 hN
  have hBA0 : (ρ b - 1) * (ρ a - 1) = 0 := hAB ▸ hAB0
  have key : ∀ X Y : Module.End (ZMod 2) V,
      (X = 0 ∨ X = ρ a - 1 ∨ X = ρ b - 1 ∨ X = (ρ a - 1) + (ρ b - 1)) →
      (Y = 0 ∨ Y = ρ a - 1 ∨ Y = ρ b - 1 ∨ Y = (ρ a - 1) + (ρ b - 1)) → X * Y = 0 := by
    intro X Y hX hY
    rcases hX with rfl | rfl | rfl | rfl <;> rcases hY with rfl | rfl | rfl | rfl <;>
      simp [add_mul, mul_add, hAA, hAB0, hBA0, hBB]
  have hP : ∀ x ∈ S, ρ x - 1 = 0 ∨ ρ x - 1 = ρ a - 1 ∨ ρ x - 1 = ρ b - 1 ∨
      ρ x - 1 = (ρ a - 1) + (ρ b - 1) := by
    intro x hx
    rcases hlist x hx with rfl | rfl | rfl | rfl
    · left
      simp
    · right; left; rfl
    · right; right; left; rfl
    · right; right; right
      rw [hC, hAB0, add_zero]
  intro s hs t ht v
  have h3 := congrArg (fun f : Module.End (ZMod 2) V => f v) (key _ _ (hP t ht) (hP s hs))
  simp only [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply, LinearMap.zero_apply] at h3
  exact sub_eq_zero.1 h3

end Quadratic

end CFSG.LocalAnalysis.UniquenessCase.UCK
