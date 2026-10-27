module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6FourFacts
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourAutomorphisms
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6FourWith
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6L34Aut
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6L34Inv
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6L34Wit4
import CFSG.GroupTheory.ConjKerCenter
import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCoverAutBase

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch6.L34

open CFSG.ComponentClassification.PSL3Four CFSG.ComponentClassification.GrSLit.L34Facts

private lemma C₄_le_S : C₄ ≤ S := by
  change Subgroup.centralizer {r₄} ⊓ S ≤ S
  exact inf_le_right

private def P1 : S := ⟨p₁, C₄_le_S (derived_le_C₄ p₁_mem)⟩

private def P2 : S := ⟨p₂, C₄_le_S (derived_le_C₄ p₂_mem)⟩

private def xS : S := ⟨x₃, wordPerm_mem _⟩

private def kS : S := ⟨k₃, wordPerm_mem _⟩

private lemma mem_commY_of_mem_derived
    {B : Subgroup (MulAut S)} (hB2 : ∀ b ∈ B, b * b = 1)
    (hβ : conjAutS r₄R ∈ B) {t : S} (ht : MulAut.conj t ∈ B) (ht1 : t ≠ 1)
    {p : Equiv.Perm (Fin 42)} (hpS : p ∈ S) (hp : p ∈ ambientDerived C₄ 2)
    (hp3 : p ^ 3 = 1) :
    (⟨p, hpS⟩ : S) ∈ commY B (conjAutS r₄R) := by
  let β : MulAut S := conjAutS r₄R
  let tR : R := ⟨t, S_le_R t.2⟩
  have htR : conjAutS tR ∈ B := by
    change conjAutS ⟨t, S_le_R t.2⟩ ∈ B
    rw [conjAutS_mk t]
    exact ht
  have hpC : p ∈ C₄ := derived_le_C₄ hp
  have hpcent : p ∈ Subgroup.centralizer {r₄} := by
    have h := hpC
    change p ∈ Subgroup.centralizer {r₄} ⊓ S at h
    exact h.1
  have htC : (t : Equiv.Perm (Fin 42)) ∈ C₄ := by
    change (t : Equiv.Perm (Fin 42)) ∈ Subgroup.centralizer {r₄} ⊓ S
    refine ⟨?_, t.2⟩
    change (t : Equiv.Perm (Fin 42)) ∈ Subgroup.centralizer {r₄}
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    simpa [r₄R, tR] using commute_of_mem hB2 hβ htR
  have ht2 : (t : Equiv.Perm (Fin 42)) * t = 1 := by
    simpa using mul_self_of_mem hB2 htR
  have ht1' : (t : Equiv.Perm (Fin 42)) ≠ 1 := by
    intro h
    exact ht1 (Subtype.ext h)
  let P : S := ⟨p, hpS⟩
  have hcomm : r₄ * p = p * r₄ :=
    Subgroup.mem_centralizer_iff.mp hpcent r₄ (by simp)
  have hfix : β P = P := by
    apply Subtype.ext
    simp only [β, P, conjAutS_apply]
    change r₄ * p * r₄⁻¹ = p
    rw [hcomm]
    group
  have hsq : P ^ 2 ∈ commY B β := by
    refine sq_mem_commY (β := β) hfix ht ?_
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    simpa using conj_eq_inv_of_mem_derived htC ht2 ht1' hp
  have h3 : P ^ 3 = 1 := Subtype.ext hp3
  have h4 : P ^ 4 = P := by
    rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_succ, h3, one_mul]
  have h := pow_mem hsq 2
  rw [← pow_mul, show (2 * 2 : ℕ) = 4 by norm_num, h4] at h
  exact h

private lemma sup_map_conj_eq_top
    {B : Subgroup (MulAut S)} (hP1 : P1 ∈ commY B (conjAutS r₄R))
    (hP2 : P2 ∈ commY B (conjAutS r₄R)) :
    commY B (conjAutS r₄R) ⊔
      (commY B (conjAutS r₄R)).map (MulAut.conj kS).toMonoidHom = ⊤ := by
  let H : Subgroup S := commY B (conjAutS r₄R)
  let K : Subgroup S := H ⊔ H.map (MulAut.conj kS).toMonoidHom
  have hK1 : P1 ∈ K := Subgroup.mem_sup_left hP1
  have hK2 : P2 ∈ K := Subgroup.mem_sup_left hP2
  have hK2i : P2⁻¹ ∈ K := Subgroup.inv_mem K hK2
  have hKk1 : MulAut.conj kS P1 ∈ K :=
    Subgroup.mem_sup_right (Subgroup.mem_map_of_mem _ hP1)
  have hKk2 : MulAut.conj kS P2 ∈ K :=
    Subgroup.mem_sup_right (Subgroup.mem_map_of_mem _ hP2)
  have hKk1i : (MulAut.conj kS P1)⁻¹ ∈ K := Subgroup.inv_mem K hKk1
  have hKk2i : (MulAut.conj kS P2)⁻¹ ∈ K := Subgroup.inv_mem K hKk2
  have hg1 : (⟨g₁, g₁_mem_S⟩ : S) ∈ K := by
    have hEq : (⟨g₁, g₁_mem_S⟩ : S) = P1⁻¹ * P2⁻¹ := by
      apply Subtype.ext
      simpa [P1, P2] using g₁_eq_of_p
    rw [hEq]
    exact Subgroup.mul_mem K (Subgroup.inv_mem K hK1) (Subgroup.inv_mem K hK2)
  have hg2mem : P2 * (MulAut.conj kS P1) * (MulAut.conj kS P2) * P2⁻¹ *
      (MulAut.conj kS P1)⁻¹ * (MulAut.conj kS P2)⁻¹ * P2 ∈ K :=
    Subgroup.mul_mem K
      (Subgroup.mul_mem K
        (Subgroup.mul_mem K
          (Subgroup.mul_mem K
            (Subgroup.mul_mem K
              (Subgroup.mul_mem K hK2 hKk1) hKk2) hK2i) hKk1i) hKk2i) hK2
  have hg2 : (⟨g₂, g₂_mem_S⟩ : S) ∈ K := by
    have hEq : (⟨g₂, g₂_mem_S⟩ : S) = P2 * (MulAut.conj kS P1) *
        (MulAut.conj kS P2) * P2⁻¹ * (MulAut.conj kS P1)⁻¹ *
        (MulAut.conj kS P2)⁻¹ * P2 := by
      apply Subtype.ext
      simpa only [P1, P2, kS, Subgroup.coe_mul, Subgroup.coe_inv,
        MulAut.conj_apply] using g₂_eq_of_p
    rw [hEq]
    exact hg2mem
  have hg3mem : P2 * (MulAut.conj kS P1) * (MulAut.conj kS P2) * P2 *
      (MulAut.conj kS P1)⁻¹ * (MulAut.conj kS P2)⁻¹ ∈ K :=
    Subgroup.mul_mem K
      (Subgroup.mul_mem K
        (Subgroup.mul_mem K
          (Subgroup.mul_mem K
            (Subgroup.mul_mem K hK2 hKk1) hKk2) hK2) hKk1i) hKk2i
  have hg3 : (⟨g₃, g₃_mem_S⟩ : S) ∈ K := by
    have hEq : (⟨g₃, g₃_mem_S⟩ : S) = P2 * (MulAut.conj kS P1) *
        (MulAut.conj kS P2) * P2 * (MulAut.conj kS P1)⁻¹ *
        (MulAut.conj kS P2)⁻¹ := by
      apply Subtype.ext
      simpa only [P1, P2, kS, Subgroup.coe_mul, Subgroup.coe_inv,
        MulAut.conj_apply] using g₃_eq_of_p
    rw [hEq]
    exact hg3mem
  have hgen : H ⊔ H.map (MulAut.conj kS).toMonoidHom = ⊤ := by
    change K = ⊤
    exact eq_top_of_mem hg1 hg2 hg3
  exact hgen

theorem fourGen_r₄ {B : Subgroup (MulAut S)}
    (hB2 : ∀ b ∈ B, b * b = 1) (hβ : conjAutS r₄R ∈ B) {t : S} (ht : MulAut.conj t ∈ B)
    (ht1 : t ≠ 1) :
    ∃ x : S, orderOf (conjAutS r₄R * (MulAut.conj x * conjAutS r₄R * (MulAut.conj x)⁻¹)) = 4 ∧
      FourGen B (conjAutS r₄R) x ∧ FourGen B (conjAutS r₄R) x⁻¹ := by
  let β : MulAut S := conjAutS r₄R
  have hβ2 : β * β = 1 := by
    have h : r₄R * r₄R = 1 := Subtype.ext r₄_mul_self
    change conjAutS r₄R * conjAutS r₄R = 1
    rw [← map_mul, h, map_one]
  have hP1 : P1 ∈ commY B β := by
    simpa only [P1, β] using
      (mem_commY_of_mem_derived hB2 hβ ht ht1
        (C₄_le_S (derived_le_C₄ p₁_mem)) p₁_mem p₁_pow_three)
  have hP2 : P2 ∈ commY B β := by
    simpa only [P2, β] using
      (mem_commY_of_mem_derived hB2 hβ ht ht1
        (C₄_le_S (derived_le_C₄ p₂_mem)) p₂_mem p₂_pow_three)
  have hordw : orderOf (β xS * xS⁻¹) = 4 := by
    rw [(Subgroup.orderOf_coe (β xS * xS⁻¹)).symm]
    have hc : ((β xS * xS⁻¹ : S) : Equiv.Perm (Fin 42)) =
        r₄ * x₃ * r₄⁻¹ * x₃⁻¹ := by
      simp only [β, xS, r₄R, conjAutS_apply, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hc]
    exact orderOf_r₄_x₃
  have hinj : Function.Injective (MulAut.conj : S →* MulAut S) := by
    rw [← MonoidHom.ker_eq_bot_iff, CFSG.GroupTheory.ker_conj_eq_center, center_eq_bot]
  have hord : orderOf (β * (MulAut.conj xS * β * (MulAut.conj xS)⁻¹)) = 4 := by
    rw [mul_conj_mul_conj_inv hβ2 xS]
    exact (orderOf_injective (MulAut.conj : S →* MulAut S) hinj (β xS * xS⁻¹)).trans hordw
  have hk : kS * (β kS)⁻¹ =
      β ((β xS * xS⁻¹) ^ (orderOf (β xS * xS⁻¹) / 2)) := by
    apply Subtype.ext
    have hL : ((kS * (β kS)⁻¹ : S) : Equiv.Perm (Fin 42)) =
        k₃ * (r₄ * k₃ * r₄⁻¹)⁻¹ := by
      simp only [β, kS, r₄R, conjAutS_apply, Subgroup.coe_mul, Subgroup.coe_inv]
    have hR : ((β ((β xS * xS⁻¹) ^ (orderOf (β xS * xS⁻¹) / 2)) : S) :
        Equiv.Perm (Fin 42)) = r₄ * (r₄ * x₃ * r₄⁻¹ * x₃⁻¹) ^ 2 * r₄⁻¹ := by
      rw [hordw, show (4 : ℕ) / 2 = 2 by norm_num]
      simp only [β, xS, r₄R, conjAutS_apply, Subgroup.coe_mul, Subgroup.coe_inv,
        Subgroup.coe_pow]
    rw [hL, hR]
    exact k₃_mul_inv_r₄
  have hgen : commY B β ⊔ (commY B β).map (MulAut.conj kS).toMonoidHom = ⊤ := by
    simpa only [β] using sup_map_conj_eq_top hP1 hP2
  have hfour : FourGenWith (commY B β) β xS :=
    fourGenWith_of center_eq_bot hβ2 hk hgen
  have hxx : xS * xS = 1 := Subtype.ext x₃_mul_self
  have hxinv : xS⁻¹ = xS := inv_eq_of_mul_eq_one_right hxx
  refine ⟨xS, ?_, ?_, ?_⟩
  · simpa only [β] using hord
  · exact hfour
  · rw [hxinv]
    exact hfour

end CFSG.LocalAnalysis.WeakClosure81.Asch6.L34

end
