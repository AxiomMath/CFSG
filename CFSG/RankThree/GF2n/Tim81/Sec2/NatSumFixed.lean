module

public import CFSG.RankThree.GF2n.Tim81.Sec2.SL2Sec5

public section

namespace CFSG.RankThree.GF2n.Tim81.Sec2

open scoped MatrixGroups
open Matrix
open CFSG.CGT.Timmesfeld75
open CFSG.QuasithinUnique.Setup.X7
open CFSG.QuasithinUnique.Setup.SL2Modules
open NatSumModel

variable {F : Type} [Field F] [Fintype F] [CharP F 2]

theorem IsNatSumModule.commSub_le_fixedSub {N : Type} [AddCommGroup N] [Module (ZMod 2) N]
    {σ : Representation (ZMod 2) SL(2, F) N} (hσ : IsNatSumModule σ) {A : Subgroup SL(2, F)}
    (hA2 : ∀ a ∈ A, a * a = 1) (hA : Nat.card A = Fintype.card F) :
    commSub σ A ≤ fixedSub σ A := by
  refine iSup₂_le fun a ha => ?_
  rcases eq_or_ne a 1 with rfl | ha1
  · simp
  · rw [← (hσ.fixedSub_zpowers_eq hA2 hA ha ha1).2]
    exact range_le_commSub (Subgroup.mem_zpowers a)

private theorem borel_mulVec_second_zero {t : SL(2, F)} (ht : t ∈ borel F) {v : Fin 2 → F}
    (hv : v 1 = 0) : (t : Matrix (Fin 2) (Fin 2) F) *ᵥ v = ![t 0 0 * v 0, 0] := by
  have ht10 : t 1 0 = 0 := ht
  funext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hv, ht10]

private theorem eq_one_of_mem_borel_of_odd_orderOf_of_entry {t : SL(2, F)}
    (htb : t ∈ borel F) (hto : Odd (orderOf t)) (ht00 : t 0 0 = 1) : t = 1 := by
  have ht10 : t 1 0 = 0 := htb
  have ht : t ∈ utri F := mem_utri_entries.2 ⟨ht10, ht00⟩
  have h2 : t ^ 2 = 1 := (isElemAbelian_utri (F := F)).2 t ht
  have hdvd : orderOf t ∣ 2 := orderOf_dvd_of_pow_eq_one h2
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
  · exact orderOf_eq_one_iff.mp h
  · obtain ⟨k, hk⟩ := hto
    omega

private theorem inf_fixedSub_utri_eq_bot_of_mem_borel (k : ℕ) {T' : Subgroup SL(2, F)}
    {t : SL(2, F)} (htT : t ∈ T') (htb : t ∈ borel F) (ht00 : t 0 0 ≠ 1) :
    fixedSub (natSumRep F k) (utri F) ⊓ fixedSub (natSumRep F k) T' = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro v hv
  rw [Submodule.mem_inf] at hv
  have hv1 : ∀ i, v i 1 = 0 := (mem_fixedSub_utri_natSumRep_iff k).1 hv.1
  have hvt : natSumRep F k t v = v := mem_fixedSub.1 hv.2 t htT
  funext i j
  have hi : (t : Matrix (Fin 2) (Fin 2) F) *ᵥ (v i) = v i := by
    have h := congrFun hvt i
    simpa [natSumRep_apply, Pi.smul_apply, smul_eq_mulVec'] using h
  rw [borel_mulVec_second_zero htb (hv1 i)] at hi
  have h0 : t 0 0 * v i 0 = v i 0 := by simpa using congrFun hi 0
  have hz : (t 0 0 - 1) * v i 0 = 0 := by rw [sub_mul, one_mul, h0, sub_self]
  have hv0 : v i 0 = 0 := by
    rcases mul_eq_zero.mp hz with h | h
    · exact absurd (sub_eq_zero.mp h) ht00
    · exact h
  fin_cases j <;> simp [hv0, hv1 i]

private theorem exists_conj_utri_and_borel_entry {A T : Subgroup SL(2, F)}
    (hA2 : ∀ a ∈ A, a * a = 1) (hA : Nat.card A = Fintype.card F)
    (hTA : T ≤ Subgroup.normalizer (A : Set SL(2, F))) (hT : Odd (Nat.card T))
    (hT1 : T ≠ ⊥) :
    ∃ (x t' : SL(2, F)), A = conjSubgroup x (utri F) ∧
      t' ∈ conjSubgroup x⁻¹ T ∧ t' ∈ borel F ∧ t' 0 0 ≠ 1 := by
  classical
  obtain ⟨x, hAx⟩ := exists_conj_utri_of_exp_two A hA2 hA
  obtain ⟨t, htne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hT1
  have htGne : (t : SL(2, F)) ≠ 1 := fun h => htne (Subtype.ext h)
  have hto : Odd (orderOf (t : SL(2, F))) :=
    Odd.of_dvd_nat hT (Subgroup.orderOf_dvd_natCard T t.2)
  let t' : SL(2, F) := x⁻¹ * (t : SL(2, F)) * x
  have ht'mem : t' ∈ conjSubgroup x⁻¹ T := by
    dsimp [t']
    rw [mem_conjSubgroup]
    simpa [mul_assoc] using t.2
  have hNA : (borel F).map (MulAut.conj x).toMonoidHom =
      Subgroup.normalizer (A : Set SL(2, F)) := by
    rw [← normalizer_utri, Subgroup.map_equiv_normalizer_eq,
      show (utri F).map (MulAut.conj x).toMonoidHom = A from by
        simpa [conjSubgroup] using hAx.symm]
  have ht'borel : t' ∈ borel F := by
    have hmem : (t : SL(2, F)) ∈ (borel F).map (MulAut.conj x).toMonoidHom := by
      rw [hNA]
      exact hTA t.2
    have hpre := (Subgroup.mem_map_equiv (f := MulAut.conj x) (K := borel F)).1 hmem
    rw [MulAut.conj_symm_apply] at hpre
    simpa [t'] using hpre
  have ht'odd : Odd (orderOf t') := by
    have horder : orderOf t' = orderOf (t : SL(2, F)) := by
      simpa [t', MulAut.conj_apply] using
        (MulAut.conj x⁻¹).orderOf_eq (t : SL(2, F))
    rwa [horder]
  have ht'ne : t' ≠ 1 := by
    intro h
    apply htGne
    have := congrArg (MulAut.conj x) h
    simpa [t', MulAut.conj_apply, mul_assoc] using this
  have ht'00 : t' 0 0 ≠ 1 := fun h00 =>
    ht'ne (eq_one_of_mem_borel_of_odd_orderOf_of_entry ht'borel ht'odd h00)
  exact ⟨x, t', hAx, ht'mem, ht'borel, ht'00⟩

theorem IsNatSumModule.fixedSub_inf_fixedSub_eq_bot {N : Type} [AddCommGroup N]
    [Module (ZMod 2) N] {σ : Representation (ZMod 2) SL(2, F) N} (hσ : IsNatSumModule σ)
    {A : Subgroup SL(2, F)} (hA2 : ∀ a ∈ A, a * a = 1) (hA : Nat.card A = Fintype.card F)
    {T : Subgroup SL(2, F)} (hTA : T ≤ Subgroup.normalizer (A : Set SL(2, F)))
    (hT : Odd (Nat.card T)) (hT1 : T ≠ ⊥) : fixedSub σ A ⊓ fixedSub σ T = ⊥ := by
  classical
  obtain ⟨k, φ, hφ⟩ := hσ
  let e := natSumRep F k
  let φl : N ≃ₗ[ZMod 2] (Fin k → Fin 2 → F) :=
    LinearEquiv.ofBijective (AddMonoidHom.toZModLinearMap 2 φ.toAddMonoidHom) φ.bijective
  have hφ' : ∀ g n, φl (σ g n) = e g (φl n) := by
    intro g n
    funext i
    rw [natSumRep_apply, Pi.smul_apply, smul_eq_mulVec']
    exact hφ g n i
  obtain ⟨x, t', hAx, ht'mem, ht'borel, ht'00⟩ :=
    exists_conj_utri_and_borel_entry hA2 hA hTA hT hT1
  let T' : Subgroup SL(2, F) := conjSubgroup x⁻¹ T
  have hinf' : fixedSub e (utri F) ⊓ fixedSub e T' = ⊥ :=
    inf_fixedSub_utri_eq_bot_of_mem_borel k ht'mem ht'borel ht'00
  have hAcoord : fixedSub e A = (fixedSub e (utri F)).map (e x) := by
    rw [hAx]
    simpa [conjSubgroup] using fixedSub_map_conj e x (utri F)
  have hTcoord : fixedSub e T = (fixedSub e T').map (e x) := by
    have hconj : conjSubgroup x T' = T := by
      dsimp [T']
      rw [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]
    rw [← hconj]
    simpa [conjSubgroup] using fixedSub_map_conj e x T'
  have hinf : fixedSub e A ⊓ fixedSub e T = ⊥ := by
    have hinj : Function.Injective (e x) := fun u v huv => by
      have h := congrArg (e x⁻¹) huv
      simpa [e, natSumRep_mul_apply] using h
    rw [hAcoord, hTcoord, ← Submodule.map_inf (e x) hinj, hinf']
    simp
  apply Submodule.map_injective_of_injective φl.injective
  rw [Submodule.map_inf φl.toLinearMap φl.injective,
    map_fixedSub_eq_of_intertwines φl hφ' A,
    map_fixedSub_eq_of_intertwines φl hφ' T, hinf, Submodule.map_bot]
