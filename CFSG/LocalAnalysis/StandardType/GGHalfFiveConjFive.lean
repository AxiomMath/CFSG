module

public import CFSG.LocalAnalysis.StandardType.GGHalfAlpha
public import CFSG.LocalAnalysis.StandardType.GGHalfFiveRes

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.SpecialLinear Matrix GGHalf

theorem eq_of_pComponents_of_common_derived {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {X A A' P : Subgroup G}
    (hA : LargeEvenPComponent p X A) (hA' : LargeEvenPComponent p X A')
    (hPA : P ≤ A) (hPA' : P ≤ A') {g : G} (hg : g ∈ ⁅P, P⁆) (hg1 : g ≠ 1) (hgp : g ^ p = 1) :
    A = A' := by
  by_contra hne
  have hcomm : (⁅A, A'⁆ : Subgroup G) ≤ CFSG.Open.lBalancePrimeCore p X :=
    commutator_le_lBalancePrimeCore_of_ne hA hA' hne
  have hP : ⁅P, P⁆ ≤ CFSG.Open.lBalancePrimeCore p X :=
    (Subgroup.commutator_mono hPA hPA').trans hcomm
  have hgmem : g ∈ CFSG.Open.lBalancePrimeCore p X := hP hg
  have hdvd : p ∣ Nat.card (CFSG.Open.lBalancePrimeCore p X) := by
    have h := orderOf_dvd_natCard (⟨g, hgmem⟩ : CFSG.Open.lBalancePrimeCore p X)
    rwa [Subgroup.orderOf_mk, orderOf_eq_prime hgp hg1] at h
  have hcop : Nat.Coprime p (Nat.card (CFSG.Open.lBalancePrimeCore p X)) :=
    CFSG.ComponentClassification.LBalance.primeCore_coprime p X
  exact (Fact.out : Nat.Prime p).not_dvd_one
    (hcop.gcd_eq_one ▸ Nat.dvd_gcd (dvd_refl p) hdvd)

private theorem one_add_one_f2 : (1 : F2) + 1 = 0 := by
  linear_combination gf2_two

private theorem transvection_self_mul_f2 {N : ℕ} {i j : Fin N} (hij : i ≠ j) :
    SpecialLinearGroup.transvection hij (1 : F2) *
      SpecialLinearGroup.transvection hij 1 = 1 := by
  rw [← SpecialLinearGroup.transvection_add, one_add_one_f2]
  exact SpecialLinearGroup.transvection_coeff_zero hij

private theorem omegaBlock_eq_transvections (n : ℕ) (k : Fin n) :
    omegaBlock n k =
      SpecialLinearGroup.transvection (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne 1 *
      SpecialLinearGroup.transvection
        ((show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne).symm 1 := by
  rw [omegaBlock, ← slPerm_swap_castSucc_succ gf2_two k,
    slPerm_swap_eq_transvections gf2_two
      (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne,
    mul_assoc, transvection_self_mul_f2, mul_one]

private theorem transvection_commutator_eq_omegaBlock_sq (n : ℕ) (k : Fin n) :
    SpecialLinearGroup.transvection
        (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne (1 : F2) *
      SpecialLinearGroup.transvection
        ((show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne).symm (1 : F2) *
      (SpecialLinearGroup.transvection
        (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne (1 : F2))⁻¹ *
      (SpecialLinearGroup.transvection
        ((show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne).symm (1 : F2))⁻¹ =
      omegaBlock n k ^ 2 := by
  set t : SpecialLinearGroup (Fin (n + 1)) F2 :=
    SpecialLinearGroup.transvection (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne 1
  set t' : SpecialLinearGroup (Fin (n + 1)) F2 :=
    SpecialLinearGroup.transvection
      ((show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne).symm 1
  have hxy : omegaBlock n k = t * t' := omegaBlock_eq_transvections n k
  have ht : t * t = 1 := transvection_self_mul_f2 _
  have ht' : t' * t' = 1 := transvection_self_mul_f2 _
  have hinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hinv' : (t')⁻¹ = t' := inv_eq_of_mul_eq_one_right ht'
  rw [hinv, hinv']
  calc t * t' * t * t' = (t * t') * (t * t') := by group
    _ = omegaBlock n k ^ 2 := by rw [hxy, sq]

namespace GGHalfCtx

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J K : Subgroup G} {y : G} {φ₁ φ₂ : SpecialLinearGroup (Fin 6) F2 →* G}
  (h : GGHalfCtx p B Bs x L D J 3 y K φ₁ φ₂)

include h

theorem conj_eq_five :
    K.map (MulAut.conj (gElt φ₁)).toMonoidHom = L.map (MulAut.conj (hElt φ₂)).toMonoidHom := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let k : Fin 3 := ⟨2, by omega⟩
  let S : Subgroup (SpecialLinearGroup (Fin 4) F2) := slOn 4 {j : Fin 4 | 2 ≤ j.val}
  let f : SpecialLinearGroup (Fin 4) F2 →* G := φ₁.comp (slLower2Hom 3)
  let Q : Subgroup G := S.map f
  let a : SpecialLinearGroup (Fin 4) F2 :=
    SpecialLinearGroup.transvection (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne 1
  let b : SpecialLinearGroup (Fin 4) F2 :=
    SpecialLinearGroup.transvection
      ((show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne).symm 1
  let u : G := f (a * b * a⁻¹ * b⁻¹)
  have haS : a ∈ S :=
    transvection_mem_slOn (S := {j : Fin 4 | 2 ≤ j.val})
      (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne (1 : F2)
      (by show (2 : ℕ) ≤ (k.castSucc).val; simp [k])
      (by show (2 : ℕ) ≤ (k.succ).val; simp [k])
  have hbS : b ∈ S :=
    transvection_mem_slOn (S := {j : Fin 4 | 2 ≤ j.val})
      ((show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne).symm (1 : F2)
      (by show (2 : ℕ) ≤ (k.succ).val; simp [k])
      (by show (2 : ℕ) ≤ (k.castSucc).val; simp [k])
  have hucomm : u ∈ ⁅Q, Q⁆ := by
    have hmem : f a ∈ Q := Subgroup.mem_map_of_mem f haS
    have hmem' : f b ∈ Q := Subgroup.mem_map_of_mem f hbS
    have hc := Subgroup.commutator_mem_commutator hmem hmem'
    rw [commutatorElement_def (f a) (f b)] at hc
    rw [show u = f a * f b * (f a)⁻¹ * (f b)⁻¹ by simp [u, map_mul, map_inv]]
    exact hc
  have hf_inj : Function.Injective f := h.coords.inj₁.comp (slLower2Hom_injective 3)
  have hω : a * b * a⁻¹ * b⁻¹ = omegaBlock 3 k ^ 2 :=
    transvection_commutator_eq_omegaBlock_sq 3 k
  have hu1 : u ≠ 1 := by
    intro hu
    have h2 : omegaBlock 3 k ^ 2 = 1 := by
      apply hf_inj
      rw [← hω, map_one]
      exact hu
    have h3 : omegaBlock 3 k = 1 := by
      calc omegaBlock 3 k = omegaBlock 3 k * omegaBlock 3 k ^ 2 := by rw [h2, mul_one]
        _ = omegaBlock 3 k ^ 3 := by group
        _ = 1 := omegaBlock_pow_three 3 k
    exact omegaBlock_ne_one 3 k h3
  have hu3 : u ^ 3 = 1 := by
    have hpow : (omegaBlock 3 k ^ 2) ^ 3 = 1 := by
      calc (omegaBlock 3 k ^ 2) ^ 3 = (omegaBlock 3 k ^ 3) ^ 2 := by group
        _ = 1 := by rw [omegaBlock_pow_three, one_pow]
    show (f (a * b * a⁻¹ * b⁻¹)) ^ 3 = 1
    rw [hω, ← map_pow, hpow, map_one]
  have hzw : Subgroup.zpowers (gElt φ₁ * y * (gElt φ₁)⁻¹) =
      Subgroup.zpowers (hElt φ₂ * x * (hElt φ₂)⁻¹) := by
    rw [zpowers_conj_gElt_y h, zpowers_conj_hElt_x h]
  have hQA : Q ≤ K.map (MulAut.conj (gElt φ₁)).toMonoidHom := levi4_le_conj_g h
  have hQA' : Q ≤ L.map (MulAut.conj (hElt φ₂)).toMonoidHom := levi4_le_conj_h h
  have hA : LargeEvenPComponent 3
      (Subgroup.centralizer ({gElt φ₁ * y * (gElt φ₁)⁻¹} : Set G))
      (K.map (MulAut.conj (gElt φ₁)).toMonoidHom) :=
    largeEvenPComponent_conj_centralizer_singleton h.pComponent_K (gElt φ₁)
  have hA' : LargeEvenPComponent 3
      (Subgroup.centralizer ({hElt φ₂ * x * (hElt φ₂)⁻¹} : Set G))
      (L.map (MulAut.conj (hElt φ₂)).toMonoidHom) :=
    largeEvenPComponent_conj_centralizer_singleton h.pComponent_L (hElt φ₂)
  rw [centralizer_singleton_eq_of_zpowers_eq hzw.symm] at hA'
  exact eq_of_pComponents_of_common_derived hA hA' hQA hQA' hucomm hu1 hu3

theorem exists_alpha_five :
    ∃ α : MulAut (SpecialLinearGroup (Fin 6) F2), ∀ s,
      hElt φ₂ * φ₁ (α s) * (hElt φ₂)⁻¹ = gElt φ₁ * φ₂ s * (gElt φ₁)⁻¹ := by
  let ψ : SpecialLinearGroup (Fin 6) F2 →* G :=
    (MulAut.conj (gElt φ₁)).toMonoidHom.comp φ₂
  let ψ' : SpecialLinearGroup (Fin 6) F2 →* G :=
    (MulAut.conj (hElt φ₂)).toMonoidHom.comp φ₁
  have hψ : Function.Injective ψ := by
    intro a b hab
    exact h.coords.inj₂ ((MulEquiv.injective (MulAut.conj (gElt φ₁))) hab)
  have hψ' : Function.Injective ψ' := by
    intro a b hab
    exact h.coords.inj₁ ((MulEquiv.injective (MulAut.conj (hElt φ₂))) hab)
  have hrange : ψ.range = ψ'.range := by
    simp only [ψ, ψ', MonoidHom.range_comp, h.coords.range₂, h.coords.range₁]
    exact h.conj_eq_five
  obtain ⟨α, hα⟩ := exists_mulAut_of_range_eq hψ hψ' hrange
  refine ⟨α, fun s => ?_⟩
  have hs := hα s
  simp only [ψ, ψ'] at hs
  simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hs

end GGHalfCtx

end CFSG.StandardType

end
