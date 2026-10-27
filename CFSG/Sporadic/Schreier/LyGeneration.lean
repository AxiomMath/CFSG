module

public import CFSG.Sporadic.Schreier.LyLocalAutQ
public import CFSG.Sporadic.SchreierLemmas.InvolutionCosetIndex
public import CFSG.LocalAnalysis.LyonsUnitaryFour.Fusion

public noncomputable section

namespace CFSG.Sporadic.LySchreier

open CFSG.Sporadic.Ly CFSG.Sporadic.Ly.Native CFSG.Sporadic.LySchreier.Native
open CFSG.Sporadic.He.Native CFSG.Sporadic.SchreierLemmas CFSG.LyonsUnitaryFour

theorem index_centralizer_lyz :
    (Subgroup.centralizer ({lyz} : Set J)).index = 1296826875 := by
  have h1 := full_involution_centralizer.2
  have h2 := card_J
  have h := Subgroup.card_mul_index (Subgroup.centralizer ({lyz} : Set J))
  rw [h1, h2] at h
  omega

theorem divisor_table :
    ∀ a : Fin 4, ∀ b : Fin 5, ∀ c : Fin 2, ∀ e : Fin 2, ∀ f : Fin 2,
    (3 ^ a.val * 5 ^ b.val * 31 ^ c.val * 37 ^ e.val * 67 ^ f.val) % 256 = 1 →
      a.val = 0 ∧ b.val = 0 ∧ c.val = 0 ∧ e.val = 0 ∧ f.val = 0 := by
  decide

theorem dvd_prime_eq {d p : ℕ} (hp : p.Prime) (h : d ∣ p) : ∃ c ≤ 1, d = p ^ c := by
  rcases (Nat.dvd_prime hp).1 h with rfl | rfl
  · exact ⟨0, by norm_num, by simp⟩
  · exact ⟨1, le_rfl, by simp⟩

theorem divisor_check
    (d : ℕ) (hd : 0 < d) (hdvd : d ∣ 1296826875) (hmod : d ≡ 1 [MOD 256]) :
    d = 1 := by
  have hfac : (1296826875 : ℕ) = 3 ^ 3 * 5 ^ 4 * 31 * 37 * 67 := by norm_num
  rw [hfac] at hdvd
  obtain ⟨d4, f, h4, hf, rfl⟩ := Nat.dvd_mul.1 hdvd
  obtain ⟨d3, e, h3, he, rfl⟩ := Nat.dvd_mul.1 h4
  obtain ⟨d2, c, h2, hc, rfl⟩ := Nat.dvd_mul.1 h3
  obtain ⟨da, db, ha, hb, rfl⟩ := Nat.dvd_mul.1 h2
  obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow (by norm_num)).1 ha
  obtain ⟨j, hj, rfl⟩ := (Nat.dvd_prime_pow (by norm_num)).1 hb
  obtain ⟨k, hk, rfl⟩ := dvd_prime_eq (by norm_num) hc
  obtain ⟨l, hl, rfl⟩ := dvd_prime_eq (by norm_num) he
  obtain ⟨m, hm, rfl⟩ := dvd_prime_eq (by norm_num) hf
  have hm' : (3 ^ i * 5 ^ j * 31 ^ k * 37 ^ l * 67 ^ m) % 256 = 1 := hmod
  obtain ⟨e0, e1, e2, e3, e4⟩ := divisor_table ⟨i, by omega⟩ ⟨j, by omega⟩ ⟨k, by omega⟩
    ⟨l, by omega⟩ ⟨m, by omega⟩ hm'
  simp only at e0 e1 e2 e3 e4
  subst e0 e1 e2 e3 e4
  norm_num

theorem lyz_comm_S :
    ∀ s ∈ (lySylow : Subgroup J), s * lyz = lyz * s := by
  intro s hs
  have hc : zS ∈ Subgroup.center lyS := by rw [center_lyS]; exact Subgroup.mem_zpowers zS
  have h := congrArg Subtype.val (Subgroup.mem_center_iff.1 hc ⟨s, hs⟩)
  rw [Subgroup.coe_mul, Subgroup.coe_mul] at h
  exact h

theorem conj_to_f
    {t : J} (htS : t ∈ lyS) (ht : orderOf t = 2)
    (hnc : ¬∀ s ∈ lyS, s * t = t * s) : ∃ c ∈ lyC, c * lyf * c⁻¹ = t := by
  obtain ⟨i, hi, hit⟩ := exists_sE ⟨t, htS⟩
  have hti : sTree i = t := by
    rw [← sE_val hi, hit]
  have hi0 : i ≠ 0 := by
    rintro rfl
    rw [sTree_zero] at hti
    rw [← hti, orderOf_one] at ht
    exact absurd ht (by norm_num)
  have hsq : stm i i = 0 := by
    apply sTree_inj (mulTab_parts.1 i hi i hi) (by norm_num)
    rw [← sTree_mul i hi i hi, sTree_zero, hti, ← pow_two, ← ht, pow_orderOf_eq_one]
  have hi6 : i ≠ 6 := by
    rintro rfl
    apply hnc
    intro s hs
    rw [← hti, ← sE_val (by norm_num : 6 < 256), sE_six]
    exact lyz_comm_S s hs
  have hmem : i ∈ invConjugators.map (·.1) := by
    rw [localFacts.invList, List.mem_filter]
    refine ⟨List.mem_range.2 hi, ?_⟩
    rw [Bool.and_eq_true_iff, bne_iff_ne]
    refine ⟨?_, hi6⟩
    unfold isInv
    rw [Bool.and_eq_true_iff, bne_iff_ne, beq_iff_eq]
    exact ⟨hi0, hsq⟩
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hmem
  have hW := repM_evalWordM (fun i => (repM_csArr i).1) (fun i => (repM_csArr i).2) e.2
  have h1 := hW.mul (repM_sTree fIndex (tableFacts.qLt _ tableFacts.fMem)).1
  have h2 := (repM_sTree e.1 hi).1.mul hW
  rw [localFacts.conj e he] at h1
  have heq := h1.unique h2
  refine ⟨evalWord cStar e.2, evalWord_mem fun l _ => cStar_mem _, ?_⟩
  rw [lyf_eq, sE_val (tableFacts.qLt _ tableFacts.fMem), heq, ← hti, mul_inv_cancel_right]

@[expose] def lyx :
    J := evalWord seedFam fusionWord * lyz * (evalWord seedFam fusionWord)⁻¹

theorem RepM.pow {X : Mat} {g : J} (hX : RepM X g) (n : ℕ) :
    RepM (powM 5 111 X n) (g ^ n) := by
  unfold RepM at *
  rw [toMat_powM, hX, mat_pow']

theorem repM_wArr : RepM wArr (evalWord seedFam fusionWord) :=
  repM_evalWordM repM_seedM repM_seedMInv _

theorem repM_xArr :
    RepM xArr lyx := by
  have hwi := repM_wArr.inv_of_check localFacts.wInv
  exact (repM_wArr.mul repM_matA).mul hwi

theorem fusion_parts :

    (lyz * lyx) ^ (2 * 4 + 1) = 1 ∧ (lyx * lyf) ^ (2 * 7 + 1) = 1 := by
  have hf : RepM sPts[fIndex]! lyf := by
    rw [lyf_eq, sE_val (tableFacts.qLt _ tableFacts.fMem)]
    exact (repM_sTree fIndex (tableFacts.qLt _ tableFacts.fMem)).1
  have h9 := (repM_matA.mul repM_xArr).pow 9
  have h15 := (repM_xArr.mul hf).pow 15
  rw [localFacts.zx9] at h9
  rw [localFacts.xf15] at h15
  exact ⟨h9.unique repM_id, h15.unique repM_id⟩

theorem lyz_sq : lyz * lyz = 1 := by
  rw [← pow_two, ← orderOf_dvd_iff_pow_eq_one, lyz, orderOf_a]

theorem lyx_sq : lyx * lyx = 1 := by
  rw [lyx]
  calc _ = evalWord seedFam fusionWord * (lyz * lyz) * (evalWord seedFam fusionWord)⁻¹ := by
        group
    _ = 1 := by rw [lyz_sq, mul_one, mul_inv_cancel]

theorem lyf_sq :
    lyf * lyf = 1 := lyf_mul_self

theorem conj_z_f :
    ∃ g : J, g * lyz * g⁻¹ = lyf := by
  obtain ⟨h9, h15⟩ := fusion_parts
  have e1 := conj_eq_of_odd_order (G := J) (by exact lyz_sq) (by exact lyx_sq) (by exact h9)
  have e2 := conj_eq_of_odd_order (G := J) (by exact lyx_sq) (by exact lyf_sq) (by exact h15)
  refine ⟨(lyx * lyf) ^ 7 * (lyz * lyx) ^ 4, ?_⟩
  calc (lyx * lyf) ^ 7 * (lyz * lyx) ^ 4 * lyz * ((lyx * lyf) ^ 7 * (lyz * lyx) ^ 4)⁻¹ =
        (lyx * lyf) ^ 7 * ((lyz * lyx) ^ 4 * lyz * ((lyz * lyx) ^ 4)⁻¹) * ((lyx * lyf) ^ 7)⁻¹ := by
        group
    _ = lyf := by rw [e1, e2]

theorem lyf_comm_Q :
    ∀ q ∈ lyQ, q * lyf = lyf * q := fun q hq =>
  Subgroup.mem_centralizer_iff.1 lyf_mem_lyCQ q hq

theorem conj_z_f_in_N :
    ∃ n ∈ lyN, n * lyz * n⁻¹ = lyf := by
  obtain ⟨g, hg⟩ := conj_z_f
  exact weak_closure_central_fusion (G := J) lySylow (by exact lyQ_le)
    (by exact lyQ_weakly_closed) (by exact lyz_comm_S) (by exact lyf_comm_Q) (by exact hg)

theorem intrinsic_local_generation :
    (∀ t ∈ lyS, orderOf t = 2 → (¬∀ s ∈ lyS, s * t = t * s) → ∃ c ∈ lyC, c * lyf * c⁻¹ = t) ∧
    (∃ n ∈ lyN, n * lyz * n⁻¹ = lyf) ∧ lyC ⊔ lyN = ⊤ := by
  refine ⟨fun t ht h2 hnc => conj_to_f ht h2 hnc, conj_z_f_in_N, ?_⟩
  have hSL : (lySylow : Subgroup J) ≤ lyC ⊔ lyN := le_trans lyS_le_lyC le_sup_left
  have hCL : Subgroup.centralizer {lyz} ≤ lyC ⊔ lyN := by
    rw [← full_involution_centralizer.1]; exact le_sup_left
  have hconj : ∀ t ∈ lyC ⊔ lyN, orderOf t = 2 → ∃ l ∈ lyC ⊔ lyN, l * lyz * l⁻¹ = t := by
    intro t htL ht2
    obtain ⟨l, hl, hlt⟩ : ∃ l ∈ lyC ⊔ lyN, l * t * l⁻¹ ∈ lyS := by
      have hp : IsPGroup 2 (Subgroup.zpowers (⟨t, htL⟩ : ↥(lyC ⊔ lyN))) := by
        apply IsPGroup.of_card (n := 1)
        rw [Nat.card_zpowers, pow_one, Subgroup.orderOf_mk]
        exact ht2
      obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
      obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥(lyC ⊔ lyN) Q (lySylow.subtype hSL)
      have hmem := Subgroup.smul_mem_pointwise_smul (⟨t, htL⟩ : ↥(lyC ⊔ lyN)) (MulAut.conj g)
        (Q : Subgroup ↥(lyC ⊔ lyN)) (hQ (Subgroup.mem_zpowers _))
      rw [← Sylow.coe_subgroup_smul, hg, Sylow.coe_subtype, Subgroup.mem_subgroupOf] at hmem
      refine ⟨g, g.2, ?_⟩
      simpa [MulAut.smul_def, lySylow_coe] using hmem
    have hs2 : orderOf (l * t * l⁻¹) = 2 := by
      have := MulEquiv.orderOf_eq (MulAut.conj l) t
      rw [MulAut.conj_apply] at this
      rw [this, ht2]
    by_cases hc : ∀ x ∈ lyS, x * (l * t * l⁻¹) = (l * t * l⁻¹) * x
    ·
      have hcen : (⟨l * t * l⁻¹, hlt⟩ : lyS) ∈ Subgroup.center lyS := by
        rw [Subgroup.mem_center_iff]
        intro g
        apply Subtype.ext
        rw [Subgroup.coe_mul, Subgroup.coe_mul]
        exact hc g.1 g.2
      rw [center_lyS, mem_zpowers_zS] at hcen
      rcases hcen with h | h
      · exfalso
        have h0 := congrArg Subtype.val h
        rw [Subgroup.coe_one] at h0
        have h1 : l * t * l⁻¹ = 1 := h0
        rw [h1, orderOf_one] at hs2
        exact absurd hs2 (by norm_num)
      · have h0 := congrArg Subtype.val h
        have h1 : l * t * l⁻¹ = lyz := h0
        refine ⟨l⁻¹, (lyC ⊔ lyN).inv_mem hl, ?_⟩
        rw [← h1]
        group
    · obtain ⟨c, hcC, hcs⟩ := conj_to_f hlt hs2 hc
      obtain ⟨n, hnN, hnz⟩ := conj_z_f_in_N
      refine ⟨l⁻¹ * c * n, (lyC ⊔ lyN).mul_mem ((lyC ⊔ lyN).mul_mem ((lyC ⊔ lyN).inv_mem hl)
        (le_sup_left (a := lyC) hcC)) (le_sup_right (b := lyN) hnN), ?_⟩
      calc l⁻¹ * c * n * lyz * (l⁻¹ * c * n)⁻¹ = l⁻¹ * (c * (n * lyz * n⁻¹) * c⁻¹) * l := by
            group
        _ = l⁻¹ * (l * t * l⁻¹) * l := by rw [hnz, hcs]
        _ = t := by group
  have key := involution_coset_index_generation (G := J) lySylow (by exact hSL) (by exact hCL)
    (by exact hconj)
  have hS : Nat.card ↥(lySylow : Subgroup J) = 256 := card_lyS
  refine key.2.2 fun d hd hdvd hmod => divisor_check d hd ?_ ?_
  · rwa [index_centralizer_lyz] at hdvd
  · rwa [hS] at hmod

end CFSG.Sporadic.LySchreier
