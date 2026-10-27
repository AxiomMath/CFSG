module

public import CFSG.Open.LocalVocabulary
public import CFSG.Quasithin.Background.D2Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem w172_two_pow_le_card_monoidHom {V W : Type*} [CommGroup V] [CommGroup W]
    [Finite V] [Finite W] (hV : ∀ v : V, v * v = 1) (hW : ∀ w : W, w * w = 1) :
    2 ^ (rk W * rk V) ≤ Nat.card (V →* W) := by
  have hV2 : ∀ x : Additive V, (2 : ℕ) • x = 0 := fun x => by
    apply Additive.toMul.injective
    rw [two_nsmul, toMul_add, toMul_zero]
    exact hV x.toMul
  have hW2 : ∀ x : Additive W, (2 : ℕ) • x = 0 := fun x => by
    apply Additive.toMul.injective
    rw [two_nsmul, toMul_add, toMul_zero]
    exact hW x.toMul
  letI : Module (ZMod 2) (Additive V) := AddCommGroup.zmodModule hV2
  letI : Module (ZMod 2) (Additive W) := AddCommGroup.zmodModule hW2
  haveI : Module.Finite (ZMod 2) (Additive V) := Module.Finite.of_finite
  haveI : Module.Finite (ZMod 2) (Additive W) := Module.Finite.of_finite
  have hcardV : Nat.card V = 2 ^ rk V :=
    card_eq_two_pow_of_isPGroup (isPGroup_two_of_sq_eq_one fun v => by
      rw [pow_two]; exact hV v)
  have hcardW : Nat.card W = 2 ^ rk W :=
    card_eq_two_pow_of_isPGroup (isPGroup_two_of_sq_eq_one fun w => by
      rw [pow_two]; exact hW w)
  have hcardV' : Nat.card (Additive V) = Nat.card V := Nat.card_congr Additive.toMul
  have hcardW' : Nat.card (Additive W) = Nat.card W := Nat.card_congr Additive.toMul
  have hfinV : Module.finrank (ZMod 2) (Additive V) = rk V := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V)
    rw [Nat.card_zmod, hcardV', hcardV] at h
    exact Nat.pow_right_injective (le_refl 2) h.symm
  have hfinW : Module.finrank (ZMod 2) (Additive W) = rk W := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive W)
    rw [Nat.card_zmod, hcardW', hcardW] at h
    exact Nat.pow_right_injective (le_refl 2) h.symm
  have hcardLin : Nat.card (Additive V →ₗ[ZMod 2] Additive W) = 2 ^ (rk W * rk V) := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2)
      (V := Additive V →ₗ[ZMod 2] Additive W)
    rw [Nat.card_zmod, Module.finrank_linearMap, hfinV, hfinW, Nat.mul_comm] at h
    exact h
  exact (calc 2 ^ (rk W * rk V) = Nat.card (Additive V →ₗ[ZMod 2] Additive W) :=
          hcardLin.symm
        _ = Nat.card (Additive V →+ Additive W) :=
          (Nat.card_congr (AddMonoidHom.toZModLinearMapEquiv 2).toEquiv).symm
        _ = Nat.card (V →* W) := (Nat.card_congr MonoidHom.toAdditive).symm).le

theorem w172_two_pow_le_relIndex_centralizer {R N V₀ : Subgroup G}
    (hV₀ : IsElemAbelian 2 V₀) (hN : IsElemAbelian 2 N)
    (hNV₀ : ∀ n ∈ N, ∀ v ∈ V₀, n * v = v * n)
    (hcomm : ∀ t ∈ R, ∀ n ∈ N, ⁅n, t⁆ ∈ V₀)
    (hcent : ∀ t ∈ R, ∀ v ∈ V₀, t * v = v * t)
    (hsurj : ∀ f : ↥N →* ↥V₀, ∃ t ∈ R, ∀ n : ↥N, ⁅(n : G), t⁆ = (f n : G)) :
    2 ^ (rk ↥V₀ * rk ↥N) ≤ (Subgroup.centralizer (N : Set G)).relIndex R := by
  letI : CommGroup ↥V₀ := { (inferInstance : Group ↥V₀) with
    mul_comm := fun a b => hV₀.1.is_comm.comm a b }
  letI : CommGroup ↥N := { (inferInstance : Group ↥N) with
    mul_comm := fun a b => hN.1.is_comm.comm a b }
  haveI : IsMulCommutative ↥V₀ := hV₀.1
  have hN2 : ∀ x : ↥N, x * x = 1 := fun x => Subtype.ext (by
    simpa [pow_two] using hN.2 (x : G) x.2)
  have hV2 : ∀ x : ↥V₀, x * x = 1 := fun x => Subtype.ext (by
    simpa [pow_two] using hV₀.2 (x : G) x.2)
  let ψt : ↥R → ↥N →* ↥V₀ := fun t =>
    MonoidHom.mk' (fun n => ⟨⁅(n : G), (t : G)⁆, hcomm t.1 t.2 n.1 n.2⟩) (by
      intro a b
      apply Subtype.ext
      show ⁅((a * b : ↥N) : G), (t : G)⁆ =
        ⁅(a : G), (t : G)⁆ * ⁅(b : G), (t : G)⁆
      rw [Subgroup.coe_mul, commutatorElement_mul_left_eq_conj_mul]
      have hb : ⁅(b : G), (t : G)⁆ ∈ V₀ := hcomm t.1 t.2 b.1 b.2
      have ha : ⁅(a : G), (t : G)⁆ ∈ V₀ := hcomm t.1 t.2 a.1 a.2
      have hconj : (a : G) * ⁅(b : G), (t : G)⁆ * (a : G)⁻¹ = ⁅(b : G), (t : G)⁆ := by
        rw [hNV₀ (a : G) a.2 ⁅(b : G), (t : G)⁆ hb, mul_inv_cancel_right]
      rw [hconj, Subgroup.mul_comm_of_mem_isMulCommutative V₀ hb ha])
  let ψ : ↥R →* (↥N →* ↥V₀) :=
    MonoidHom.mk' ψt (by
      intro t t'
      ext n
      show ⁅(n : G), ((t * t' : ↥R) : G)⁆ =
        ⁅(n : G), (t : G)⁆ * ⁅(n : G), (t' : G)⁆
      rw [Subgroup.coe_mul, commutatorElement_mul_right_eq_mul_conj]
      have hb : ⁅(n : G), (t' : G)⁆ ∈ V₀ := hcomm t'.1 t'.2 n.1 n.2
      have ht : (t : G) * ⁅(n : G), (t' : G)⁆ = ⁅(n : G), (t' : G)⁆ * (t : G) :=
        hcent t.1 t.2 ⁅(n : G), (t' : G)⁆ hb
      rw [mul_assoc ⁅(n : G), (t : G)⁆ (t : G) ⁅(n : G), (t' : G)⁆, ht,
        ← mul_assoc ⁅(n : G), (t : G)⁆ ⁅(n : G), (t' : G)⁆ (t : G),
        mul_inv_cancel_right])
  have hψrange : ψ.range = ⊤ := by
    rw [Subgroup.eq_top_iff']
    intro f
    obtain ⟨t, htR, ht⟩ := hsurj f
    exact ⟨⟨t, htR⟩, MonoidHom.ext fun n => Subtype.ext (ht n)⟩
  have hker : ψ.ker = (Subgroup.centralizer (N : Set G)).subgroupOf R := by
    ext t
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    constructor
    · intro h n hn
      have h1 : (ψ t) ⟨n, hn⟩ = (1 : ↥N →* ↥V₀) ⟨n, hn⟩ :=
        congrArg (fun g : ↥N →* ↥V₀ => g ⟨n, hn⟩) h
      exact commutatorElement_eq_one_iff_mul_comm.mp (Subtype.ext_iff.mp h1)
    · intro h
      ext n
      show ⁅(n : G), (t : G)⁆ = 1
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact h (n : G) n.2
  calc 2 ^ (rk ↥V₀ * rk ↥N)
      ≤ Nat.card (↥N →* ↥V₀) := w172_two_pow_le_card_monoidHom hN2 hV2
    _ = Nat.card ψ.range := by rw [hψrange]; exact (Subgroup.card_top).symm
    _ = ψ.ker.index := (Subgroup.index_ker ψ).symm
    _ = (Subgroup.centralizer (N : Set G)).relIndex R := by rw [hker, Subgroup.relIndex]

end CFSG.LocalAnalysis.WeakClosure81

end
