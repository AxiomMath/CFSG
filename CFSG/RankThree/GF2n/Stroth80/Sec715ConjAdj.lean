module

public import CFSG.RankThree.GF2n.Stroth80.Sec7TailChevalleyWarning
public import Mathlib.Algebra.Module.ZMod
import CFSG.RankThree.GF2n.Stroth80.Sec717PairingCore

public section

namespace CFSG.RankThree.GF2n.Stroth80

open Subgroup
open scoped commutatorElement

theorem exists_ne_zero_quadMap_eq_zero {W U : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [Finite W] [AddCommGroup U] [Module (ZMod 2) U] [Finite U] (q : W → U) (hq0 : q 0 = 0)
    (β : W → W → U) (hβl : ∀ a a' b, β (a + a') b = β a b + β a' b)
    (hβr : ∀ a b b', β a (b + b') = β a b + β a b')
    (hq : ∀ a b, q (a + b) = q a + q b + β a b) (hcard : Nat.card U ^ 2 < Nat.card W) :
    ∃ w : W, w ≠ 0 ∧ q w = 0 := by
  classical
  haveI : Module.Finite (ZMod 2) W := Module.Finite.of_finite
  haveI : Module.Finite (ZMod 2) U := Module.Finite.of_finite
  haveI : Fintype W := Fintype.ofFinite W
  haveI : Fintype U := Fintype.ofFinite U
  set f := Module.finrank (ZMod 2) U with hf
  let bU := Module.finBasis (ZMod 2) U
  have hU : Nat.card U = 2 ^ f := by
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2) (V := U), ZMod.card]
  have hW : Nat.card W = 2 ^ Module.finrank (ZMod 2) W := by
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2) (V := W), ZMod.card]
  have hdim : 2 * f < Module.finrank (ZMod 2) W := by
    rw [hU, hW, ← pow_mul] at hcard
    have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hcard
    linarith [mul_comm f 2]
  let Bf : Fin f → W → W → ZMod 2 := fun i a b => bU.repr (β a b) i
  have hBl : ∀ i a a' b, Bf i (a + a') b = Bf i a b + Bf i a' b := fun i a a' b => by
    simp only [Bf, hβl, map_add, Finsupp.add_apply]
  have hBr : ∀ i a b b', Bf i a (b + b') = Bf i a b + Bf i a b' := fun i a b b' => by
    simp only [Bf, hβr, map_add, Finsupp.add_apply]
  have hc2 : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  have hB0l : ∀ i b, Bf i 0 b = 0 := fun i b => by
    have h := hBl i 0 0 b
    rw [add_zero] at h
    exact left_eq_add.mp h
  have hB0r : ∀ i a, Bf i a 0 = 0 := fun i a => by
    have h := hBr i a 0 0
    rw [add_zero] at h
    exact left_eq_add.mp h
  let B : Fin f → W →ₗ[ZMod 2] W →ₗ[ZMod 2] ZMod 2 := fun i =>
    LinearMap.mk₂ (ZMod 2) (Bf i) (hBl i)
      (fun c a b => by
        rcases hc2 c with rfl | rfl
        · rw [zero_smul, zero_smul, hB0l]
        · rw [one_smul, one_smul])
      (hBr i)
      (fun c a b => by
        rcases hc2 c with rfl | rfl
        · rw [zero_smul, zero_smul, hB0r]
        · rw [one_smul, one_smul])
  obtain ⟨w, hw, hz⟩ := exists_nonzero_zero_of_quadratic hdim (fun i w => bU.repr (q w) i)
    (fun i => by simp [hq0]) fun i =>
      ⟨B i, fun a b => by simp only [B, LinearMap.mk₂_apply, Bf, hq, map_add, Finsupp.add_apply]⟩
  refine ⟨w, hw, bU.repr.injective ?_⟩
  ext i
  simpa using hz i

section Group

variable {X : Type*} [Group X]

private theorem comm_mul_right_eq_sec715 (y n n' : X) :
    ⁅y, n * n'⁆ = ⁅y, n⁆ * ⁅n, ⁅y, n'⁆⁆ * ⁅y, n'⁆ := by
  simp only [commutatorElement_def]
  group

private theorem comm_mul_of_comm_sec715 {y c : X} (hc : y * c = c * y) (n : X) :
    ⁅y, n * c⁆ = ⁅y, n⁆ := by
  have hc' : y⁻¹ * c = c * y⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hc, mul_assoc, mul_inv_cancel, mul_one]
  simp only [commutatorElement_def, mul_inv_rev]
  calc y * (n * c) * y⁻¹ * (c⁻¹ * n⁻¹) = y * n * (c * y⁻¹) * c⁻¹ * n⁻¹ := by group
    _ = y * n * (y⁻¹ * c) * c⁻¹ * n⁻¹ := by rw [hc']
    _ = y * n * y⁻¹ * n⁻¹ := by group

end Group

theorem exists_comm_mem_of_card_lt {X : Type} [Group X] [Finite X]
    {N V L K₂ Ker : Subgroup X} {y : X}
    (hVN : V ≤ N) (hVL : V ≤ L) (hVc : ∀ z ∈ V, ∀ n ∈ N, z * n = n * z)
    (hVsq : ∀ z ∈ V, z * z = 1) (hNc : ∀ a ∈ N, ∀ b ∈ N, ⁅a, b⁆ ∈ V)
    (hNsq : ∀ a ∈ N, a * a ∈ V) (hLc : ∀ a ∈ L, ∀ b ∈ L, a * b = b * a)
    (hyL : ∀ n ∈ N, ⁅y, n⁆ ∈ L) (hyN : ∀ n ∈ N, ⁅y, n⁆ ∈ N) (hyV : ∀ z ∈ V, y * z = z * y)
    (hKerV : ∀ z ∈ V, z ∈ Ker → z = 1) (hK₂N : K₂ ≤ N)
    (hCK₂ : ∀ c ∈ N, y * c = c * y → c ∈ K₂)
    (hK₂ : ∀ n ∈ K₂, ∃ z ∈ V, ⁅y, n⁆ * z⁻¹ ∈ Ker)
    (hcard : Nat.card V ^ 2 * Nat.card ↥(centralizer ({y} : Set X) ⊓ N) < Nat.card K₂) :
    ∃ n ∈ K₂, y * n ≠ n * y ∧ ⁅y, n⁆ ∈ Ker := by
  classical
  set C := centralizer ({y} : Set X) ⊓ N with hCdef
  have hmemC : ∀ c, c ∈ C ↔ y * c = c * y ∧ c ∈ N := fun c => by
    rw [hCdef, mem_inf, mem_centralizer_singleton_iff]
    exact ⟨fun h => ⟨h.1.symm, h.2⟩, fun h => ⟨h.1.symm, h.2⟩⟩
  have hCK₂' : C ≤ K₂ := fun c hc => hCK₂ c ((hmemC c).1 hc).2 ((hmemC c).1 hc).1
  have hVC : V ≤ C := fun z hz => (hmemC z).2 ⟨hyV z hz, hVN hz⟩
  choose vf hvV hvK using hK₂
  have huniq : ∀ n (hn : n ∈ K₂) z, z ∈ V → ⁅y, n⁆ * z⁻¹ ∈ Ker → z = vf n hn := by
    intro n hn z hz hzK
    have h1 : (⁅y, n⁆ * z⁻¹)⁻¹ * (⁅y, n⁆ * (vf n hn)⁻¹) ∈ Ker :=
      Ker.mul_mem (Ker.inv_mem hzK) (hvK n hn)
    have e : (⁅y, n⁆ * z⁻¹)⁻¹ * (⁅y, n⁆ * (vf n hn)⁻¹) = z * (vf n hn)⁻¹ := by group
    rw [e] at h1
    have := hKerV _ (V.mul_mem hz (V.inv_mem (hvV n hn))) h1
    rw [mul_inv_eq_one] at this
    exact this
  have hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb => hVc a ha b (hVN hb)
  have hβV : ∀ n ∈ N, ∀ n' ∈ N, ⁅n, ⁅y, n'⁆⁆ ∈ V := fun n hn n' hn' => hNc n hn _ (hyN n' hn')
  have hvmul : ∀ n (hn : n ∈ K₂) n' (hn' : n' ∈ K₂),
      vf (n * n') (K₂.mul_mem hn hn') = vf n hn * vf n' hn' * ⁅n, ⁅y, n'⁆⁆ := by
    intro n hn n' hn'
    have hnN := hK₂N hn
    have hn'N := hK₂N hn'
    refine (huniq _ (K₂.mul_mem hn hn') _ (V.mul_mem (V.mul_mem (hvV n hn) (hvV n' hn'))
      (hβV n hnN n' hn'N)) ?_).symm
    set a := ⁅y, n⁆ with ha
    set b := ⁅y, n'⁆ with hb
    set β := ⁅n, b⁆ with hβ
    set u := vf n hn with hu
    set u' := vf n' hn' with hu'
    have haL : a ∈ L := hyL n hnN
    have hbL : b ∈ L := hyL n' hn'N
    have hβL : β ∈ L := hVL (hβV n hnN n' hn'N)
    have huL : u ∈ L := hVL (hvV n hn)
    have hu'L : u' ∈ L := hVL (hvV n' hn')
    have key : ⁅y, n * n'⁆ * (u * u' * β)⁻¹ = (a * u⁻¹) * (b * u'⁻¹) := by
      rw [comm_mul_right_eq_sec715]
      have h1 : β * b = b * β := hLc β hβL b hbL
      have h2 : b * u'⁻¹ = u'⁻¹ * b := hLc b hbL _ (L.inv_mem hu'L)
      have h3 : u⁻¹ * u'⁻¹ = u'⁻¹ * u⁻¹ := hLc _ (L.inv_mem huL) _ (L.inv_mem hu'L)
      have h4 : β * u'⁻¹ = u'⁻¹ * β := hLc β hβL _ (L.inv_mem hu'L)
      have h5 : β * u⁻¹ = u⁻¹ * β := hLc β hβL _ (L.inv_mem huL)
      have h6 : b * u⁻¹ = u⁻¹ * b := hLc b hbL _ (L.inv_mem huL)
      calc a * β * b * (u * u' * β)⁻¹ = a * (β * b) * (β⁻¹ * u'⁻¹ * u⁻¹) := by group
        _ = a * (b * β) * (β⁻¹ * u'⁻¹ * u⁻¹) := by rw [h1]
        _ = a * (b * u'⁻¹) * u⁻¹ := by group
        _ = a * (u'⁻¹ * b) * u⁻¹ := by rw [h2]
        _ = a * u'⁻¹ * (b * u⁻¹) := by group
        _ = a * u'⁻¹ * (u⁻¹ * b) := by rw [h6]
        _ = a * (u'⁻¹ * u⁻¹) * b := by group
        _ = a * (u⁻¹ * u'⁻¹) * b := by rw [h3]
        _ = (a * u⁻¹) * (u'⁻¹ * b) := by group
        _ = (a * u⁻¹) * (b * u'⁻¹) := by rw [h2]
    rw [key]
    exact Ker.mul_mem (hvK n hn) (hvK n' hn')
  have hvC : ∀ n (hn : n ∈ K₂) c (hc : c ∈ C),
      vf (n * c) (K₂.mul_mem hn (hCK₂' hc)) = vf n hn := by
    intro n hn c hc
    refine (huniq _ (K₂.mul_mem hn (hCK₂' hc)) _ (hvV n hn) ?_).symm
    rw [comm_mul_of_comm_sec715 ((hmemC c).1 hc).1]
    exact hvK n hn
  have hβsymm : ∀ n (hn : n ∈ K₂) n' (hn' : n' ∈ K₂), ⁅n, ⁅y, n'⁆⁆ = ⁅n', ⁅y, n⁆⁆ := by
    intro n hn n' hn'
    have hζ : (n * n')⁻¹ * (n' * n) ∈ C := by
      have e : (n * n')⁻¹ * (n' * n) = ⁅n'⁻¹, n⁻¹⁆ := by
        rw [commutatorElement_def]
        group
      rw [e]
      exact hVC (hNc _ (N.inv_mem (hK₂N hn')) _ (N.inv_mem (hK₂N hn)))
    have h1 := hvC (n * n') (K₂.mul_mem hn hn') _ hζ
    have e2 : n * n' * ((n * n')⁻¹ * (n' * n)) = n' * n := by group
    have h2 : vf (n' * n) (K₂.mul_mem hn' hn) = vf (n * n') (K₂.mul_mem hn hn') := by
      rw [← h1]
      congr 1
      exact e2.symm
    rw [hvmul n' hn' n hn, hvmul n hn n' hn'] at h2
    have hu := hvV n hn
    have hu' := hvV n' hn'
    have hcomm : vf n' hn' * vf n hn = vf n hn * vf n' hn' := hVab _ hu' _ hu
    rw [hcomm] at h2
    exact (mul_left_cancel h2).symm
  have hβmul : ∀ n₁ (h₁ : n₁ ∈ N) n₂ (h₂ : n₂ ∈ N) e (he : e ∈ N),
      ⁅n₁ * n₂, e⁆ = ⁅n₁, e⁆ * ⁅n₂, e⁆ := by
    intro n₁ h₁ n₂ h₂ e he
    have hz : ⁅n₂, e⁆ ∈ V := hNc n₂ h₂ e he
    have hcomm : n₁ * ⁅n₂, e⁆ = ⁅n₂, e⁆ * n₁ := (hVc _ hz n₁ h₁).symm
    have e1 : ⁅n₁ * n₂, e⁆ = n₁ * ⁅n₂, e⁆ * e * n₁⁻¹ * e⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e1, hcomm]
    have e2 : ⁅n₂, e⁆ * n₁ * e * n₁⁻¹ * e⁻¹ = ⁅n₂, e⁆ * ⁅n₁, e⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e2]
    exact hVab _ hz _ (hNc n₁ h₁ e he)
  have hβC : ∀ c (hc : c ∈ C) n' (hn' : n' ∈ K₂), ⁅c, ⁅y, n'⁆⁆ = 1 := by
    intro c hc n' hn'
    rw [hβsymm c (hCK₂' hc) n' hn']
    have : ⁅y, c⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact ((hmemC c).1 hc).1
    rw [this, commutatorElement_one_right]
  set D : Subgroup ↥K₂ := C.subgroupOf K₂ with hD
  have hmemD : ∀ k : ↥K₂, k ∈ D ↔ (k : X) ∈ C := fun k => mem_subgroupOf
  haveI hDn : D.Normal := by
    refine ⟨fun c hc k => (hmemD _).2 ?_⟩
    have hc' : (c : X) ∈ C := (hmemD c).1 hc
    have e : (k : X) * c * (k : X)⁻¹ = ⁅(k : X), (c : X)⁆ * c := by
      rw [commutatorElement_def]
      group
    show (k : X) * c * (k : X)⁻¹ ∈ C
    rw [e]
    exact C.mul_mem (hVC (hNc _ (hK₂N k.2) _ ((hmemC c).1 hc').2)) hc'
  have hWcomm : ∀ a b : ↥K₂ ⧸ D, a * b = b * a := by
    intro a b
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, hmemD]
    have e : ((a * b)⁻¹ * (b * a) : ↥K₂) = (⁅(b : X)⁻¹, (a : X)⁻¹⁆ : X) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
      group
    show (((a * b)⁻¹ * (b * a) : ↥K₂) : X) ∈ C
    rw [e]
    exact hVC (hNc _ (N.inv_mem (hK₂N b.2)) _ (N.inv_mem (hK₂N a.2)))
  letI : CommGroup (↥K₂ ⧸ D) := sec717CommGroup hWcomm
  have hWsq : ∀ x : Additive (↥K₂ ⧸ D), 2 • x = 0 := by
    intro x
    obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (Additive.toMul x)
    rw [← Additive.toMul.injective.eq_iff, toMul_nsmul, toMul_zero, ← ha, ← QuotientGroup.mk_pow,
      QuotientGroup.eq_one_iff, hmemD, pow_two]
    exact hVC (hNsq _ (hK₂N a.2))
  letI : Module (ZMod 2) (Additive (↥K₂ ⧸ D)) := AddCommGroup.zmodModule hWsq
  letI : CommGroup ↥V := sec717CommGroup fun a b => Subtype.ext (hVab a a.2 b b.2)
  have hUsq : ∀ x : Additive ↥V, 2 • x = 0 := by
    intro x
    rw [← Additive.toMul.injective.eq_iff, toMul_nsmul, toMul_zero, pow_two]
    exact Subtype.ext (hVsq _ (Additive.toMul x).2)
  letI : Module (ZMod 2) (Additive ↥V) := AddCommGroup.zmodModule hUsq
  let v' : ↥K₂ → ↥V := fun n => ⟨vf n n.2, hvV n n.2⟩
  let β' : ↥K₂ → ↥K₂ → ↥V := fun n n' =>
    ⟨⁅(n : X), ⁅y, (n' : X)⁆⁆, hβV n (hK₂N n.2) n' (hK₂N n'.2)⟩
  have hv'C : ∀ n : ↥K₂, ∀ d ∈ D, v' (n * d) = v' n := fun n d hd =>
    Subtype.ext (hvC n n.2 d ((hmemD d).1 hd))
  have hβ'Cl : ∀ n n' : ↥K₂, ∀ d ∈ D, β' (n * d) n' = β' n n' := by
    intro n n' d hd
    apply Subtype.ext
    show ⁅(n : X) * d, ⁅y, (n' : X)⁆⁆ = ⁅(n : X), ⁅y, (n' : X)⁆⁆
    rw [hβmul _ (hK₂N n.2) _ (hK₂N d.2) _ (hyN _ (hK₂N n'.2)), hβC _ ((hmemD d).1 hd) _ n'.2,
      mul_one]
  have hβ'Cr : ∀ n n' : ↥K₂, ∀ d ∈ D, β' n (n' * d) = β' n n' := by
    intro n n' d hd
    apply Subtype.ext
    show ⁅(n : X), ⁅y, (n' : X) * d⁆⁆ = ⁅(n : X), ⁅y, (n' : X)⁆⁆
    rw [comm_mul_of_comm_sec715 ((hmemC d).1 ((hmemD d).1 hd)).1]
  let q : Additive (↥K₂ ⧸ D) → Additive ↥V := fun w =>
    Additive.ofMul (v' (Quotient.out (Additive.toMul w)))
  let βq : Additive (↥K₂ ⧸ D) → Additive (↥K₂ ⧸ D) → Additive ↥V := fun a b =>
    Additive.ofMul (β' (Quotient.out (Additive.toMul a)) (Quotient.out (Additive.toMul b)))
  have hout : ∀ k : ↥K₂, ∃ d ∈ D, Quotient.out (QuotientGroup.mk k : ↥K₂ ⧸ D) = k * d := by
    intro k
    obtain ⟨d, hd⟩ := QuotientGroup.mk_out_eq_mul D k
    exact ⟨d, d.2, hd⟩
  have hv'q : ∀ k : ↥K₂, v' (Quotient.out (QuotientGroup.mk k : ↥K₂ ⧸ D)) = v' k := by
    intro k
    obtain ⟨d, hd, he⟩ := hout k
    rw [he, hv'C k d hd]
  have hβ'q : ∀ k k' : ↥K₂, β' (Quotient.out (QuotientGroup.mk k : ↥K₂ ⧸ D))
      (Quotient.out (QuotientGroup.mk k' : ↥K₂ ⧸ D)) = β' k k' := by
    intro k k'
    obtain ⟨d, hd, he⟩ := hout k
    obtain ⟨d', hd', he'⟩ := hout k'
    rw [he, he', hβ'Cl k _ d hd, hβ'Cr k k' d' hd']
  have hmk : ∀ w : Additive (↥K₂ ⧸ D), ∃ k : ↥K₂, Additive.toMul w = QuotientGroup.mk k :=
    fun w => (QuotientGroup.mk_surjective (Additive.toMul w)).imp fun k hk => hk.symm
  have hq0 : q 0 = 0 := by
    show Additive.ofMul (v' (Quotient.out (1 : ↥K₂ ⧸ D))) = 0
    rw [← QuotientGroup.mk_one, hv'q]
    apply Additive.toMul.injective
    show v' 1 = 1
    apply Subtype.ext
    show vf 1 K₂.one_mem = 1
    exact (huniq 1 K₂.one_mem 1 V.one_mem (by simp)).symm
  have hβl : ∀ a a' b, βq (a + a') b = βq a b + βq a' b := by
    intro a a' b
    obtain ⟨k, hk⟩ := hmk a
    obtain ⟨k', hk'⟩ := hmk a'
    obtain ⟨l, hl⟩ := hmk b
    show Additive.ofMul (β' (Quotient.out (Additive.toMul a * Additive.toMul a'))
        (Quotient.out (Additive.toMul b))) =
      Additive.ofMul (β' (Quotient.out (Additive.toMul a)) (Quotient.out (Additive.toMul b)) *
        β' (Quotient.out (Additive.toMul a')) (Quotient.out (Additive.toMul b)))
    rw [hk, hk', hl, ← QuotientGroup.mk_mul, hβ'q, hβ'q, hβ'q]
    apply congrArg Additive.ofMul
    apply Subtype.ext
    show ⁅(k : X) * k', ⁅y, (l : X)⁆⁆ = ⁅(k : X), ⁅y, (l : X)⁆⁆ * ⁅(k' : X), ⁅y, (l : X)⁆⁆
    exact hβmul _ (hK₂N k.2) _ (hK₂N k'.2) _ (hyN _ (hK₂N l.2))
  have hβsymm' : ∀ a b, βq a b = βq b a := by
    intro a b
    obtain ⟨k, hk⟩ := hmk a
    obtain ⟨l, hl⟩ := hmk b
    show Additive.ofMul (β' (Quotient.out (Additive.toMul a)) (Quotient.out (Additive.toMul b))) =
      Additive.ofMul (β' (Quotient.out (Additive.toMul b)) (Quotient.out (Additive.toMul a)))
    rw [hk, hl, hβ'q, hβ'q]
    apply congrArg Additive.ofMul
    exact Subtype.ext (hβsymm k k.2 l l.2)
  have hβr : ∀ a b b', βq a (b + b') = βq a b + βq a b' := by
    intro a b b'
    rw [hβsymm' a (b + b'), hβl, hβsymm' b a, hβsymm' b' a]
  have hq : ∀ a b, q (a + b) = q a + q b + βq a b := by
    intro a b
    obtain ⟨k, hk⟩ := hmk a
    obtain ⟨l, hl⟩ := hmk b
    show Additive.ofMul (v' (Quotient.out (Additive.toMul a * Additive.toMul b))) =
      Additive.ofMul (v' (Quotient.out (Additive.toMul a)) * v' (Quotient.out (Additive.toMul b)) *
        β' (Quotient.out (Additive.toMul a)) (Quotient.out (Additive.toMul b)))
    rw [hk, hl, ← QuotientGroup.mk_mul, hv'q, hv'q, hv'q, hβ'q]
    apply congrArg Additive.ofMul
    exact Subtype.ext (hvmul k k.2 l l.2)
  have hcardW : Nat.card (Additive ↥V) ^ 2 < Nat.card (Additive (↥K₂ ⧸ D)) := by
    have hDcard : Nat.card D = Nat.card C :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCK₂').toEquiv
    have hidx : Nat.card D * D.index = Nat.card ↥K₂ := D.card_mul_index
    have hW : Nat.card (Additive (↥K₂ ⧸ D)) = D.index := rfl
    rw [hW, show Nat.card (Additive ↥V) = Nat.card V from rfl]
    have hC0 : 0 < Nat.card C := Nat.card_pos
    by_contra hle
    push Not at hle
    have : Nat.card ↥K₂ ≤ Nat.card V ^ 2 * Nat.card C := by
      rw [← hidx, hDcard, mul_comm]
      exact Nat.mul_le_mul_right _ hle
    exact absurd hcard (not_lt.mpr this)
  obtain ⟨w, hw0, hqw⟩ := exists_ne_zero_quadMap_eq_zero q hq0 βq hβl hβr hq hcardW
  set n : ↥K₂ := Quotient.out (Additive.toMul w) with hn
  have hnD : n ∉ D := by
    intro hnD
    apply hw0
    apply Additive.toMul.injective
    show Additive.toMul w = 1
    rw [← QuotientGroup.out_eq' (Additive.toMul w), ← hn]
    exact (QuotientGroup.eq_one_iff n).mpr hnD
  have hvn : vf n n.2 = 1 := by
    have : v' n = 1 := Additive.toMul.injective (by exact hqw)
    exact congrArg Subtype.val this
  refine ⟨n, n.2, fun hyn => hnD ((hmemD n).2 ((hmemC n).2 ⟨hyn, hK₂N n.2⟩)), ?_⟩
  have h := hvK n n.2
  rw [hvn, inv_one, mul_one] at h
  exact h

end CFSG.RankThree.GF2n.Stroth80
