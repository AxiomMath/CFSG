module

public import Certificates.Kernel.Co2Census.S0

public section

namespace CertificateChecks.KernelCo2Census

open CFSG.Sporadic.Co2Smith CFSG.KC.Co2InvS CFSG.KC.Co2Census

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

@[expose] noncomputable def gT (l : ℕ) : K := sElt (TGt l)

theorem T_misc_spec : TPt 0 = IDP ∧ ∀ l < 9, TGRt l = SK (TGt l) := by
  have h := T_misc
  simp only [Bool.and_eq_true, Nat.beq_eq, List.all_eq_true, List.mem_range] at h
  exact ⟨h.1, h.2⟩

theorem mulSteps_T :
    MulSteps repK (rmStep TGRt) 9 gT := by
  intro l hl x M hx
  have e : rmStep TGRt l M = mulV M (SK (TGt l)) := by
    rw [rmStep, T_misc_spec.2 l hl]
  rw [e]
  exact repK_mul hx (repK_sElt _)

theorem T_pts :
    {y | ∃ i < 512, repK y (TPt i)} = (gensSub gT 9 : Set K) :=
  mul_record (fun _ _ _ h h' => repK_fun h h') mulSteps_T T_tree T_clos (by norm_num)
    (fun i hi => Nat.eq_of_beq_eq_true (T_root i hi)) (by rw [T_misc_spec.1]; exact repK_one)

theorem T_card :
    Nat.card (gensSub gT 9) = 512 := by
  have tf := treeK_sound T_tree
  have h1 : repK 1 (TPt 0) := by
    rw [T_misc_spec.1]
    exact repK_one
  change Nat.card ((gensSub gT 9 : Set K)) = 512
  rw [Nat.card_coe_set_eq, ← T_pts]
  refine pts_ncard (fun _ _ _ h h' => repK_fun h h') (fun _ _ _ h h' => repK_unique h h')
    (fun i hi => ?_) tf.2
  obtain ⟨-, -, hr⟩ := tf.1 i hi
  rw [Nat.eq_of_beq_eq_true (T_root i hi)] at hr
  obtain ⟨w, -, hw⟩ := reach_mul mulSteps_T hr h1
  exact ⟨_, hw⟩

theorem T_le :
    gensSub gT 9 ≤ S0 := by
  rw [gensSub, Subgroup.closure_le]
  rintro _ ⟨l, -, rfl⟩
  exact sElt_mem_S0 _

theorem factorization_S0 : (1451520 : ℕ).factorization 2 = 9 := by
  have e : (1451520 : ℕ) = 2 ^ 9 * 2835 := by norm_num
  rw [e, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.factorization_pow, Finsupp.smul_apply, Nat.Prime.factorization_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  rfl

theorem L_roots_spec {i : ℕ} (hi : i < 5104) : ∃ j < 5, rtOf LXt i = Lrt j := by
  have h := L_roots i hi
  rw [List.any_eq_true] at h
  obtain ⟨j, hj, he⟩ := h
  exact ⟨j, List.mem_range.1 hj, Nat.eq_of_beq_eq_true he⟩

theorem L_mem_class
    {i : ℕ} (hi : i < 5104) {y : K} (hy : repK y (LPt i)) :
    ∃ j < 5, rtOf LXt i = Lrt j ∧ ∃ w ∈ S0, y = w * s0Rep j * w⁻¹ := by
  obtain ⟨j, hj, hrt⟩ := L_roots_spec hi
  have hmem : y ∈ segSet repK 5104 LPt LXt (Lrt j) := ⟨i, hi, hrt, hy⟩
  rw [(s0_class hj).1] at hmem
  exact ⟨j, hj, hrt, hmem⟩

theorem s0_inv_mem
    {s : K} (hs : s ∈ S0)
    (h2 : s * s = 1) : ∃ i < 5104, repK s (LPt i) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let T' : Subgroup S0 := (gensSub gT 9).subgroupOf S0
  have hT' : Nat.card T' = 2 ^ (Nat.card S0).factorization 2 := by
    rw [card_S0, factorization_S0,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe T_le).toEquiv, T_card]
    norm_num
  let P0 : Sylow 2 S0 := Sylow.ofCard T' hT'
  let s' : S0 := ⟨s, hs⟩
  have hs2 : s' ^ 2 = 1 := Subtype.ext (by
    change s ^ 2 = 1
    rw [sq, h2])
  have hp : IsPGroup 2 (Subgroup.zpowers s') := by
    rcases (Nat.dvd_prime Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hs2) with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h]; rfl)
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h]; rfl)
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq S0 P0 Q
  have hsQ : s' ∈ (Q : Subgroup S0) := hQ (Subgroup.mem_zpowers s')
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hsQ
  have e : (MulAut.conj g)⁻¹ • s' = g⁻¹ * s' * g := by
    rw [MulAut.smul_def, ← map_inv, MulAut.conj_apply, inv_inv]
  rw [e] at hsQ
  have htK : ((g⁻¹ * s' * g : S0) : K) ∈ gensSub gT 9 := Subgroup.mem_subgroupOf.1 hsQ
  rw [← SetLike.mem_coe, ← T_pts] at htK
  obtain ⟨j, hj, hrep⟩ := htK
  have ht : ((g⁻¹ * s' * g : S0) : K) = (g : K)⁻¹ * s * g := rfl
  have htt : ((g⁻¹ * s' * g : S0) : K) * ((g⁻¹ * s' * g : S0) : K) = 1 := by
    rw [ht]
    calc (g : K)⁻¹ * s * g * ((g : K)⁻¹ * s * g) = (g : K)⁻¹ * (s * s) * g := by group
      _ = 1 := by rw [h2]; group
  have hsq : mulV (TPt j) (TPt j) = IDP :=
    repK_unique (repK_mul hrep hrep) (htt ▸ repK_one)
  obtain ⟨hpos, hpe⟩ := posK_sound T_pos j hj (by
    change Nat.beq (mulV (TPt j) (TPt j)) IDP = true
    rw [hsq]
    exact Nat.beq_refl IDP)
  have hrepL : repK ((g⁻¹ * s' * g : S0) : K) (LPt (TPOSt j)) := hpe ▸ hrep
  obtain ⟨j', hj', hrt, w, hw, hwt⟩ := L_mem_class hpos hrepL
  have hcls : s ∈ {y | ∃ w ∈ S0, y = w * s0Rep j' * w⁻¹} := by
    refine ⟨(g : K) * w, S0.mul_mem g.2 hw, ?_⟩
    have e2 : s = (g : K) * ((g⁻¹ * s' * g : S0) : K) * (g : K)⁻¹ := by
      rw [ht]
      group
    rw [e2, hwt]
    group
  rw [← (s0_class hj').1] at hcls
  obtain ⟨i, hi, -, hi'⟩ := hcls
  exact ⟨i, hi, hi'⟩

theorem s0Rep_sq
    {j : ℕ} (hj : j < 5) :
    s0Rep j ∈ S0 ∧ s0Rep j * s0Rep j = 1 := by
  obtain ⟨-, -, -, -, -, -, -, h7⟩ := L_misc_spec
  by_cases h0 : j = 0
  · subst h0
    rw [s0Rep, if_pos rfl, one_mul]
    exact ⟨S0.one_mem, rfl⟩
  · obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero h0
    rw [s0Rep, if_neg h0, Nat.succ_sub_one]
    refine ⟨sElt_mem_S0 _, ?_⟩
    have hr := repK_sElt (s0Reps.getD j' 0)
    have h := (h7 j' (by omega))
    rw [← h.1] at hr
    exact repK_fun (repK_mul hr hr) (h.2 ▸ repK_one)

theorem s0_inv_iff
    {s : K} :
    (s ∈ S0 ∧ s * s = 1) ↔ ∃ i < 5104, repK s (LPt i) := by
  constructor
  · rintro ⟨hs, h2⟩
    exact s0_inv_mem hs h2
  · rintro ⟨i, hi, hy⟩
    obtain ⟨j, hj, -, w, hw, rfl⟩ := L_mem_class hi hy
    obtain ⟨hr, hr2⟩ := s0Rep_sq hj
    refine ⟨S0.mul_mem (S0.mul_mem hw hr) (S0.inv_mem hw), ?_⟩
    calc w * s0Rep j * w⁻¹ * (w * s0Rep j * w⁻¹) = w * (s0Rep j * s0Rep j) * w⁻¹ := by group
      _ = 1 := by rw [hr2]; group

end CertificateChecks.KernelCo2Census

end
