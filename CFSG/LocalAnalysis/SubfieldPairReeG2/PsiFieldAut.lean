module

public import CFSG.LocalAnalysis.SubfieldPairReeG2.PsiBasics
public import CFSG.LieType.Ree.SmallReeOuterThreeKernel
public import CFSG.Walter.Ree.Model.Cells

public section

open CFSG CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.RankThree.PartOne.CTP
open CFSG.HardMathSupport.Seitz.TrialityOdd.Proving (sl2Range)
open CFSG.Walter.Ree.Model (smallReeU)

namespace CFSG.LocalAnalysis.SubfieldPairReeG2

section Ree


variable {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K G2.prime]

theorem reeGammaFieldAut_psi (hK : Nat.card K = 3 ^ (2 * a + 1))
    {ψ : SL2 K →* G2.reeGamma K a}
    (huψ : ∀ b : K, (ψ (uSL b) : ModGL G2.tag K) = smallReeU a K 0 b 0)
    (hwψ : ∀ w₀ : WeylGroup G2.tag,
      (∀ w, (coxeterSystem G2.tag).length w ≤ (coxeterSystem G2.tag).length w₀) →
        (ψ WSL : ModGL G2.tag K) = canonicalRep (coxeterSystem G2.tag) K w₀)
    (σ : K ≃+* K) (g : SL2 K) :
    G2.reeGammaFieldAut K a σ (ψ g) = ψ (Matrix.SpecialLinearGroup.map σ.toRingHom g) := by
  classical
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element G2.tag
  set α := G2.reeGammaFieldAut K a σ with hα
  have hu : ∀ c : K, α (ψ (uSL c)) = ψ (uSL (σ c)) := by
    intro c
    apply Subtype.ext
    rw [hα, ReeTag.coe_reeGammaFieldAut, huψ, huψ]
    have := CFSG.LieType.Ree.entrywise_smallReeCoord (a := a) (K := K) σ.toRingHom 0 c 0
    rw [map_zero] at this
    exact this
  have hW : α (ψ WSL) = ψ WSL := by
    apply Subtype.ext
    rw [hα, ReeTag.coe_reeGammaFieldAut, hwψ w₀ hw₀]
    exact entrywise_canonicalRep σ w₀
  have hmapu : ∀ c : K, Matrix.SpecialLinearGroup.map σ.toRingHom (uSL c) = uSL (σ c) := by
    intro c
    apply SL2_ext <;> simp [coe_uSL]
  have hmapv : ∀ c : K, Matrix.SpecialLinearGroup.map σ.toRingHom (vSL c) = vSL (σ c) := by
    intro c
    apply SL2_ext <;> simp [coe_vSL]
  have hvW : ∀ c : K, (WSL : SL2 K) * vSL c = uSL (-c) * WSL := by
    intro c
    apply SL2_ext <;> simp [coe_vSL, coe_uSL, coe_WSL, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_apply, Fin.sum_univ_two]
  have key := MonoidHom.eq_of_eqOn_dense
    (CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower (K := K))
    (f := (α.toMonoidHom).comp ψ)
    (g := ψ.comp (Matrix.SpecialLinearGroup.map σ.toRingHom)) (by
      rintro M (⟨c, rfl⟩ | ⟨c, rfl⟩)
      · show α (ψ (uSL c)) = ψ (Matrix.SpecialLinearGroup.map σ.toRingHom (uSL c))
        rw [hmapu, hu]
      · show α (ψ (vSL c)) = ψ (Matrix.SpecialLinearGroup.map σ.toRingHom (vSL c))
        rw [hmapv]
        have h1 : ψ WSL * ψ (vSL c) = ψ (uSL (-c)) * ψ WSL := by
          rw [← map_mul, ← map_mul, hvW]
        have h2 : ψ WSL * ψ (vSL (σ c)) = ψ (uSL (-σ c)) * ψ WSL := by
          rw [← map_mul, ← map_mul, hvW]
        have h3 := congrArg α h1
        rw [map_mul, map_mul, hW, hu, map_neg] at h3
        exact mul_left_cancel (h3.trans h2.symm))
  exact DFunLike.congr_fun key g

theorem psi_mem_fixedSubgroup_iff {ψ : SL2 K →* G2.reeGamma K a}
    (hker : ∀ g, ψ g = 1 ↔ g = 1 ∨ g = -1)
    (hequiv : ∀ (σ : K ≃+* K) (g : SL2 K),
      G2.reeGammaFieldAut K a σ (ψ g) = ψ (Matrix.SpecialLinearGroup.map σ.toRingHom g))
    {β : K ≃+* K} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hβ : orderOf β = p) (g : SL2 K) :
    ψ g ∈ fixedSubgroup (G2.reeGammaFieldAut K a β) ↔ g ∈ sl2Range (fixSubfield β) K := by
  rw [mem_sl2Range_fixSubfield_iff]
  show G2.reeGammaFieldAut K a β (ψ g) = ψ g ↔ _
  rw [hequiv β g]
  constructor
  · intro h
    have h1 : ψ ((Matrix.SpecialLinearGroup.map β.toRingHom g) * g⁻¹) = 1 := by
      rw [map_mul, map_inv, h, mul_inv_cancel]
    rcases (hker _).1 h1 with h2 | h2
    · exact mul_inv_eq_one.1 h2
    · exfalso
      have h3 : Matrix.SpecialLinearGroup.map β.toRingHom g = -g := by
        have := mul_inv_eq_iff_eq_mul.1 h2
        simpa using this
      have h2K : (2 : K) ≠ 0 := by
        intro h0
        have := (CharP.cast_eq_zero_iff K G2.prime 2).1 (by exact_mod_cast h0)
        have h3' : G2.prime = 3 := rfl
        rw [h3'] at this
        omega
      have hall : ∀ i j, (g : Matrix (Fin 2) (Fin 2) K) i j = 0 := by
        intro i j
        refine eq_zero_of_apply_eq_neg h2K (hp.odd_of_ne_two hp2) hβ ?_
        have := congrArg (fun m : SL2 K => (m : Matrix (Fin 2) (Fin 2) K) i j) h3
        simpa using this
      have h0 : (g : Matrix (Fin 2) (Fin 2) K) = 0 := by ext i j; exact hall i j
      have := g.2
      rw [h0, Matrix.det_zero] at this
      exact zero_ne_one this
  · intro h; rw [h]

end Ree

end CFSG.LocalAnalysis.SubfieldPairReeG2
