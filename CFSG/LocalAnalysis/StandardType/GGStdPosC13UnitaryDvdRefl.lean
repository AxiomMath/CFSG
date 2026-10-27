module

public import CFSG.LocalAnalysis.StandardType.GGStdPosC13UnitaryDvdNorm
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRestTypeA

public section

namespace CFSG.StandardType

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.StandardType.LineU CFSG.StandardType.UnitTB CFSG.Assembly TableB

theorem unitDvd_swap_mem_reflSet {K : Type} [Field K] {n d p : ℕ} {L' : Type} [Group L']
    [Finite L'] {φ : ↥(unitarySU 2 n K d) →* L'} (hM : UnitTB.Model φ) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n + 1) (hd : 3 ≤ d) {A : Subgroup (MulAut L')}
    (hA : IsElemAbelian p A) (hsc : GGTorusSelfCent p A)
    (hdiag : ∀ a ∈ A, ∃ t : Fin d → K, ActsDiagU φ a t)
    (hN : ∀ σ, MulAut.conj (φ (permSU hM.field σ)) ∈ Subgroup.normalizer (A : Set (MulAut L')))
    {i j : Fin d} (hij : i ≠ j) :
    ggConjAut A (hN (Equiv.swap i j)) ∈ ggTorusReflSet p A := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Finite (MulAut L') :=
    Finite.of_injective (fun f : MulAut L' => (f : L' → L')) DFunLike.coe_injective
  haveI : Finite ↥A := Subtype.finite
  have hc : ∀ a b : ↥A, a * b = b * a := fun a b => Subtype.ext (hA.comm a.2 b.2)
  refine ⟨φ (permSU hM.field (Equiv.swap i j)), hN (Equiv.swap i j),
    weyl_W_prop hM.field hd hM.ker hA.2 hdiag _ ⟨Equiv.swap i j, rfl⟩, rfl, ?_, ?_⟩
  · have hg2 : (MulAut.conj (φ (permSU hM.field (Equiv.swap i j)))) ^ 2 = 1 := by
      rw [← map_pow, ← map_pow, sq, ← UnitAct.permSU_mul, Equiv.swap_mul_self,
        UnitAct.permSU_one, map_one, map_one]
    refine MulEquiv.ext fun b => Subtype.ext ?_
    rw [ggConjAut_pow_apply, hg2]
    simp
  · obtain ⟨ζ, hζ⟩ := CFSG.RankThree.PartOne.KFU.exists_isPrimitiveRoot hM.field hp hpq
    have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
    have hζinv : ζ ≠ ζ⁻¹ := TypeA.ne_inv_of_isPrimitiveRoot hζ hp hp2
    have ht₁p : ∀ k, TypeA.ggPairVec i j ζ k ^ p = 1 := fun k =>
      TypeA.pow_ggPairVec hζ.pow_eq_one k
    obtain ⟨D₁, hD₁⟩ := exists_diagSU hM.field hpq ht₁p (TypeA.prod_ggPairVec ζ hζ0)
    let a₁ : ↥A := ⟨MulAut.conj (φ D₁), conj_mem_of_selfCent hsc hdiag hD₁ ht₁p⟩
    have ha₁acts : ActsDiagU φ (a₁ : MulAut L') (TypeA.ggPairVec i j ζ) := actsDiagU_conj hD₁
    have ha₁p : a₁ ^ p = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hA.2 _ a₁.2)
    have hact : ∀ (a : ↥A) (t : Fin d → K), ActsDiagU φ (a : MulAut L') t →
        ActsDiagU φ ((a * (ggConjAut A (hN (Equiv.swap i j)) a)⁻¹ : ↥A) : MulAut L')
          (TypeA.ggPairVec i j (t i * (t j)⁻¹)) := by
      intro a t hat
      have h1 := actsDiagU_mul hat (actsDiagU_inv (hat.conj_perm hM.field (Equiv.swap i j)))
      rw [Equiv.swap_inv] at h1
      rw [Subgroup.coe_mul, Subgroup.coe_inv, ggConjAut_apply,
        ← TypeA.mul_inv_comp_swap (fun k => hat.ne_zero k) hij]
      exact h1
    have hδ : ∀ a : ↥A, ∃ e : ℕ, a * (ggConjAut A (hN (Equiv.swap i j)) a)⁻¹ = a₁ ^ e := by
      intro a
      obtain ⟨t, hat⟩ := hdiag (a : MulAut L') a.2
      obtain ⟨e, -, he⟩ := hζ.eq_pow_of_pow_eq_one
        (hat.ratio_pow hM.field hd hM.ker (hA.2 _ a.2) i j)
      have h1 : ActsDiagU φ ((a * (ggConjAut A (hN (Equiv.swap i j)) a)⁻¹ : ↥A) : MulAut L')
          (TypeA.ggPairVec i j (ζ ^ e)) := by
        have := hact a t hat
        rwa [← he] at this
      have h2 : ActsDiagU φ ((a₁ ^ e : ↥A) : MulAut L') (TypeA.ggPairVec i j (ζ ^ e)) := by
        rw [Subgroup.coe_pow]
        have := ha₁acts.pow e
        rwa [TypeA.ggPairVec_pow] at this
      exact ⟨e, Subtype.ext (actsDiagU_unique hM.surj h1 h2)⟩
    have h₁ : a₁ * (ggConjAut A (hN (Equiv.swap i j)) a₁)⁻¹ ≠ 1 := by
      intro hcontra
      have hi : TypeA.ggPairVec i j ζ i = ζ := by simp [TypeA.ggPairVec_apply, hij]
      have hj : TypeA.ggPairVec i j ζ j = ζ⁻¹ := by simp [TypeA.ggPairVec_apply, hij.symm]
      have h := hact a₁ _ ha₁acts
      rw [hi, hj, inv_inv] at h
      have h1 : ((a₁ * (ggConjAut A (hN (Equiv.swap i j)) a₁)⁻¹ : ↥A) : MulAut L') = 1 := by
        rw [hcontra]
        rfl
      rw [h1] at h
      obtain ⟨m, hmi, hmj⟩ := exists_not_mem_two hd i j
      have hr := h.ratio_eq hM.field hd hM.ker (actsDiagU_one φ) i m
      simp [TypeA.ggPairVec_apply, hij, hmi, hmj] at hr
      exact hζinv (eq_inv_of_mul_eq_one_left hr)
    exact card_fix_mul_of_le_zpowers hp hc _ (a₁ := a₁) ha₁p hδ h₁

end CFSG.StandardType
