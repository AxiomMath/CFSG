module

public import Mathlib.GroupTheory.PGroup
import CFSG.LieType.Chevalley.GraphFixedF4Canonical

public section

namespace CFSG.RankThree.PartTwo.Sec15.Proof1521T

variable {G : Type} [Group G] [Finite G]

theorem isMulCommutative_of_le_normalizer_of_inner {p : ℕ} [Fact p.Prime] {L Q P : Subgroup G}
    (hZ : Subgroup.center ↥L = ⊥)
    (hab : ∀ S : Subgroup ↥L, IsPGroup p S → IsMulCommutative S)
    (hinn : ∀ (φ : MulAut ↥L) (k : ℕ), φ ^ p ^ k = 1 → ∃ x : ↥L, φ = MulAut.conj x)
    (hQ : IsPGroup p Q) (hQL : Q ≤ Subgroup.normalizer (L : Set G)) (hPL : P ≤ L)
    (hΩ : ∀ x ∈ Q, x ^ p = 1 → (∀ y ∈ P, y * x = x * y) → x ∈ P) :
    IsMulCommutative Q := by
  let ρ : ↥Q →* MulAut ↥L :=
    L.normalizerMonoidHom.comp (Subgroup.inclusion hQL)
  have hconj : Function.Injective (MulAut.conj : ↥L → MulAut ↥L) :=
    CFSG.LieType.Chevalley.mulAut_conj_injective_of_center_eq_bot hZ
  have hchoice : ∀ q : ↥Q, ∃ x : ↥L, ρ q = MulAut.conj x := by
    intro q
    obtain ⟨k, hk⟩ := hQ q
    have hq : ρ q ^ p ^ k = 1 := by
      have := congrArg ρ hk
      simpa [map_pow] using this
    exact hinn (ρ q) k hq
  let R : Subgroup (MulAut ↥L) := ρ.range
  have hRle : R ≤ (MulAut.conj : ↥L →* MulAut ↥L).range := by
    intro φ hφ
    obtain ⟨q, rfl⟩ := MonoidHom.mem_range.mp hφ
    obtain ⟨x, hx⟩ := hchoice q
    exact MonoidHom.mem_range.mpr ⟨x, hx.symm⟩
  let S : Subgroup ↥L := R.comap (MulAut.conj : ↥L →* MulAut ↥L)
  have hR : IsPGroup p R := by
    let ρR : ↥Q →* ↥R :=
      { toFun := fun q => ⟨ρ q, MonoidHom.mem_range.mpr ⟨q, rfl⟩⟩
        map_one' := by ext; simp
        map_mul' := by intro a b; ext; simp }
    refine IsPGroup.of_surjective hQ ρR ?_
    intro φ
    obtain ⟨q, hq⟩ := MonoidHom.mem_range.mp (show (φ : MulAut ↥L) ∈ ρ.range from φ.2)
    exact ⟨q, Subtype.ext hq⟩
  let conjS : ↥S →* ↥R :=
    { toFun := fun x => ⟨(MulAut.conj : ↥L →* MulAut ↥L) (x : ↥L), x.2⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp }
  have hS : IsPGroup p S := by
    refine IsPGroup.of_injective hR conjS ?_
    intro a b hab
    have h : (a : ↥L) = (b : ↥L) := hconj (congrArg Subtype.val hab)
    exact Subtype.ext h
  have hSab : IsMulCommutative ↥S := hab S hS
  have hker : ρ.ker = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    by_contra hxne
    have hxone : ρ x = 1 := MonoidHom.mem_ker.mp hx
    have hpdiv : p ∣ orderOf x := hQ.dvd_orderOf hxne
    let y : ↥Q := x ^ (orderOf x / p)
    have hyord : orderOf y = p := by
      dsimp [y]
      exact orderOf_pow_orderOf_div (orderOf_pos x).ne' hpdiv
    have hyne : y ≠ 1 := by
      intro hy
      have hp1 : p = 1 := by rw [← hyord, hy, orderOf_one]
      exact (Fact.out : p.Prime).ne_one hp1
    have hyp : y ^ p = 1 := by
      rw [← hyord]
      exact pow_orderOf_eq_one y
    have hyker : ρ y = 1 := by
      dsimp [y]
      rw [map_pow, hxone]
      simp
    have hycent : (y : G) ∈ Subgroup.centralizer (L : Set G) := by
      have hmem : Subgroup.inclusion hQL y ∈ L.normalizerMonoidHom.ker := by
        rw [MonoidHom.mem_ker]
        simpa [ρ] using hyker
      rw [Subgroup.normalizerMonoidHom_ker] at hmem
      rwa [Subgroup.mem_subgroupOf] at hmem
    have hypG : (y : G) ^ p = 1 := by
      simpa using congrArg Subtype.val hyp
    have hcommP : ∀ z ∈ P, z * (y : G) = (y : G) * z := by
      intro z hz
      exact (Subgroup.mem_centralizer_iff.mp hycent) z (hPL hz)
    have hyP : (y : G) ∈ P := hΩ (y : G) y.2 hypG hcommP
    have hyL : (y : G) ∈ L := hPL hyP
    have hyZ : (⟨(y : G), hyL⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro z
      ext
      exact (Subgroup.mem_centralizer_iff.mp hycent) z.1 z.2
    have hybot : (⟨(y : G), hyL⟩ : ↥L) = 1 := by
      exact Subgroup.mem_bot.mp (hZ ▸ hyZ)
    have hyone : (y : G) = 1 := congrArg Subtype.val hybot
    exact hyne (Subtype.ext hyone)
  have hρinj : Function.Injective ρ := by
    intro a b hab
    have hmem : a⁻¹ * b ∈ ρ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hab, inv_mul_cancel]
    have h1 : a⁻¹ * b = 1 := by
      simpa [hker] using hmem
    have hba : b = a := by
      calc b = a * (a⁻¹ * b) := by group
        _ = a * 1 := by rw [h1]
        _ = a := by rw [mul_one]
    exact hba.symm
  refine isMulCommutative_iff.mpr fun q₁ q₂ => ?_
  obtain ⟨x₁, hx₁⟩ := hchoice q₁
  obtain ⟨x₂, hx₂⟩ := hchoice q₂
  have hx₁S : x₁ ∈ S := by
    rw [Subgroup.mem_comap]
    change MulAut.conj x₁ ∈ ρ.range
    rw [← hx₁]
    exact MonoidHom.mem_range.mpr ⟨q₁, rfl⟩
  have hx₂S : x₂ ∈ S := by
    rw [Subgroup.mem_comap]
    change MulAut.conj x₂ ∈ ρ.range
    rw [← hx₂]
    exact MonoidHom.mem_range.mpr ⟨q₂, rfl⟩
  have hcommS :
      (⟨x₁, hx₁S⟩ : ↥S) * ⟨x₂, hx₂S⟩ = ⟨x₂, hx₂S⟩ * ⟨x₁, hx₁S⟩ :=
    (isMulCommutative_iff.mp hSab) _ _
  have hcommL : x₁ * x₂ = x₂ * x₁ := congrArg Subtype.val hcommS
  have hρcomm : ρ q₁ * ρ q₂ = ρ q₂ * ρ q₁ := by
    rw [hx₁, hx₂, ← map_mul, ← map_mul, hcommL]
  exact hρinj (by rw [map_mul, map_mul]; exact hρcomm)

end CFSG.RankThree.PartTwo.Sec15.Proof1521T
