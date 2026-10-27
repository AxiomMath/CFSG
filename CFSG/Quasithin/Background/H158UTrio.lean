module

public import CFSG.Quasithin.Background.H158TNF
public import CFSG.Quasithin.Background.HLUCoc24

public section

namespace CFSG.Quasithin.H158U

open CFSG.Quasithin.H158T CFSG.Quasithin.H.Coc24 CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.LU
  CFSG.Monster.Code CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.ZTrans
open scoped Pointwise

@[expose] def blk (j : Fin 3) : Finset (Fin 24) := Finset.univ.filter fun x => lab x = j

theorem lab_o0F : ∀ x : Fin 24, x ∈ o0F ↔ lab x = 0 := by
  intro x
  rw [mem_o0F]
  revert x
  decide +kernel

theorem lab_o1F : ∀ x : Fin 24, x ∈ o1F ↔ lab x = 1 := by
  intro x
  rw [mem_o1F]
  revert x
  decide +kernel

theorem lab_o2F : ∀ x : Fin 24, x ∈ o2F ↔ lab x = 2 := by
  intro x
  rw [mem_o2F]
  revert x
  decide +kernel

theorem blk_zero : blk 0 = o0F := by
  ext x
  simp [blk, lab_o0F]

theorem blk_one : blk 1 = o1F := by
  ext x
  simp [blk, lab_o1F]

theorem blk_two : blk 2 = o2F := by
  ext x
  simp [blk, lab_o2F]

theorem blk_mem_labTrio (j : Fin 3) : blk j ∈ labTrio := by
  fin_cases j
  · rw [show ((⟨0, by norm_num⟩ : Fin 3)) = 0 from rfl, blk_zero]
    simp [labTrio]
  · rw [show ((⟨1, by norm_num⟩ : Fin 3)) = 1 from rfl, blk_one]
    simp [labTrio]
  · rw [show ((⟨2, by norm_num⟩ : Fin 3)) = 2 from rfl, blk_two]
    simp [labTrio]

theorem smul_blk {σ : Equiv.Perm (Fin 24)} (hσ : σ ∈ trioP) (r : Fin 24) :
    σ • blk (lab r) = blk (lab (σ r)) := by
  ext x
  have h1 := mem_smul_perm_iff σ (blk (lab r)) (σ⁻¹ x)
  rw [perm_apply_inv] at h1
  rw [h1]
  have h2 := (inv_mem hσ : σ⁻¹ ∈ trioP) x (σ r)
  rw [perm_inv_apply] at h2
  simp only [blk, Finset.mem_filter, Finset.mem_univ, true_and]
  exact h2

theorem smul_labTrio {σ : Equiv.Perm (Fin 24)} (hσ : σ ∈ trioP) : σ • labTrio = labTrio := by
  have hsub : σ • labTrio ⊆ labTrio := by
    intro X hX
    obtain ⟨Y, hY, rfl⟩ := Finset.mem_smul_finset.1 hX
    simp only [labTrio, Finset.mem_insert, Finset.mem_singleton] at hY
    rcases hY with rfl | rfl | rfl
    · have h := smul_blk hσ 0
      rw [show lab 0 = 0 from by decide, blk_zero] at h
      rw [h]
      exact blk_mem_labTrio _
    · have h := smul_blk hσ 3
      rw [show lab 3 = 1 from by decide, blk_one] at h
      rw [h]
      exact blk_mem_labTrio _
    · have h := smul_blk hσ 8
      rw [show lab 8 = 2 from by decide, blk_two] at h
      rw [h]
      exact blk_mem_labTrio _
  exact Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_smul_finset])

theorem stab_facts :
    Nat.card ↥stabUTP = 64512 ∧ stabUTP ≤ trioP ∧ Nat.card ↥trQ = 10752 := by
  have : Finite (MulAut W11) := finite_mulAut_z (V := W11)
  have hS : Nat.card ↥stabUTP ≤ 64512 := card_stabUTP.trans_le card_stab_UT_le
  have hC64 := le_card_cent
  have hCK := card_cent_mul_le
  have hQ : 10752 ≤ Nat.card ↥trQ := by
    rw [← card_img11_trQ]
    omega
  have h1 : 6 * Nat.card ↥trQ ≤ Nat.card ↥genT :=
    mul_card_le_of_cosets trQ_le_genT twP tw_mem_genT
      fun i j h => tw_distinct i j (trQ_le_trioP0 h)
  have heq : genT = stabUTP :=
    Subgroup.eq_of_le_of_card_ge (genT_le.trans inf_le_left) (by omega)
  obtain ⟨-, hQc⟩ := perfectCore_stabUTP hS hQ
  refine ⟨?_, heq ▸ genT_le.trans inf_le_right, hQc⟩
  have : Nat.card ↥genT = Nat.card ↥stabUTP := by rw [heq]
  omega

theorem stabUTP_le_autPerm : stabUTP ≤ AutPerm := by
  rintro _ ⟨x, -, rfl⟩
  exact x.2

theorem trio_conj_form
    (T : Subgroup (Equiv.Perm (Fin 24))) (hT : CFSG.Quasithin.IsSylowIn 2 T AutPerm)
    (Tr : Finset (Finset (Fin 24))) (hcard : Tr.card = 3) (hblk : ∀ O ∈ Tr, O.card = 8)
    (hdisj : ∀ O ∈ Tr, ∀ O' ∈ Tr, O ≠ O' → Disjoint O O')
    (hcov : Tr.biUnion id = Finset.univ) (hst : ∀ g ∈ T, g • Tr = Tr) :
    ∃ h ∈ AutPerm, Tr = h • labTrio ∧ ∀ t ∈ T, h⁻¹ * t * h ∈ stabUTP := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h₀, hh₀, hTr⟩ := trio_normal_form T hT Tr hcard hblk hdisj hcov hst
  obtain ⟨hcS, hSP, -⟩ := stab_facts
  set P : Subgroup (Equiv.Perm (Fin 24)) :=
    AutPerm ⊓ MulAction.stabilizer (Equiv.Perm (Fin 24)) labTrio with hP
  have hPA : P ≤ AutPerm := inf_le_left
  have hmemP : ∀ σ, σ ∈ P ↔ σ ∈ AutPerm ∧ σ • labTrio = labTrio := fun σ => by
    rw [hP, Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 2 (G := ↥stabUTP) (n := 10)
    (by rw [hcS]; norm_num)
  set Q₀ : Subgroup (Equiv.Perm (Fin 24)) := K.map stabUTP.subtype with hQ₀
  have hQ₀card : Nat.card ↥Q₀ = 2 ^ 10 := by
    rw [hQ₀, Subgroup.card_map_of_injective stabUTP.subtype_injective, hK]
  have hQ₀S : Q₀ ≤ stabUTP := Subgroup.map_subtype_le K
  have hQ₀P : Q₀ ≤ P := fun σ hσ =>
    (hmemP σ).2 ⟨stabUTP_le_autPerm (hQ₀S hσ), smul_labTrio (hSP (hQ₀S hσ))⟩
  set T₁ : Subgroup (Equiv.Perm (Fin 24)) := T.map (MulAut.conj h₀⁻¹).toMonoidHom with hT₁
  have hmemT₁ : ∀ t ∈ T, h₀⁻¹ * t * h₀ ∈ T₁ := fun t ht =>
    ⟨t, ht, by simp [MulAut.conj_apply]⟩
  have hTcard : Nat.card ↥T = 2 ^ 10 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT.1).toEquiv.symm, card_sylow_two hT,
      factor_AutPerm]
  have hT₁card : Nat.card ↥T₁ = 2 ^ 10 := by
    rw [hT₁, Subgroup.card_map_of_injective (MulAut.conj h₀⁻¹).injective, hTcard]
  have hT₁P : T₁ ≤ P := by
    rintro _ ⟨t, ht, rfl⟩
    refine (hmemP _).2 ⟨?_, ?_⟩
    · have := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hh₀) (hT.1 ht)) hh₀
      simpa [MulAut.conj_apply] using this
    · have e : ((MulAut.conj h₀⁻¹).toMonoidHom t) • labTrio = labTrio := by
        have h1 : t • Tr = Tr := hst t ht
        calc ((MulAut.conj h₀⁻¹).toMonoidHom t) • labTrio
            = h₀⁻¹ • (t • (h₀ • labTrio)) := by
              simp [MulAut.conj_apply, mul_smul]
          _ = labTrio := by rw [← hTr, h1, hTr, inv_smul_smul]
      exact e
  have hPdvd : Nat.card ↥P ∣ Nat.card ↥AutPerm := Subgroup.card_dvd_of_le hPA
  have hPfac : (Nat.card ↥P).factorization 2 = 10 := by
    have hP0 : Nat.card ↥P ≠ 0 := Nat.card_pos.ne'
    have hA0 : Nat.card ↥AutPerm ≠ 0 := Nat.card_pos.ne'
    refine le_antisymm ?_ ?_
    · rw [← factor_AutPerm]
      exact (Nat.factorization_le_iff_dvd hP0 hA0).2 hPdvd 2
    · refine (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hP0).1 ?_
      rw [← hQ₀card]
      exact Subgroup.card_dvd_of_le hQ₀P
  have hH : IsPGroup 2 ↥(T₁.subgroupOf P) :=
    IsPGroup.of_card (n := 10)
      (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT₁P).toEquiv, hT₁card])
  obtain ⟨g, hg⟩ := exists_conj_le_range (p := 2) (Subgroup.inclusion hQ₀P)
    (Subgroup.inclusion_injective hQ₀P) (by rw [hQ₀card, hPfac]) hH
  have hgP : (g : Equiv.Perm (Fin 24)) ∈ P := g.2
  have hgT : (g : Equiv.Perm (Fin 24)) • labTrio = labTrio := ((hmemP _).1 hgP).2
  refine ⟨h₀ * (g : Equiv.Perm (Fin 24))⁻¹,
    Subgroup.mul_mem _ hh₀ (Subgroup.inv_mem _ (hPA hgP)), ?_, fun t ht => ?_⟩
  · rw [mul_smul, inv_smul_eq_iff.2 hgT.symm, hTr]
  · have hy : (⟨h₀⁻¹ * t * h₀, hT₁P (hmemT₁ t ht)⟩ : ↥P) ∈ T₁.subgroupOf P :=
      Subgroup.mem_subgroupOf.2 (hmemT₁ t ht)
    obtain ⟨q, hq⟩ := hg _ hy
    have hq' : (q : Equiv.Perm (Fin 24)) =
        (g : Equiv.Perm (Fin 24)) * (h₀⁻¹ * t * h₀) * (g : Equiv.Perm (Fin 24))⁻¹ :=
      congrArg Subtype.val hq
    have e : (h₀ * (g : Equiv.Perm (Fin 24))⁻¹)⁻¹ * t * (h₀ * (g : Equiv.Perm (Fin 24))⁻¹) =
        (q : Equiv.Perm (Fin 24)) := by
      rw [hq']
      group
    rw [e]
    exact hQ₀S q.2

end CFSG.Quasithin.H158U
