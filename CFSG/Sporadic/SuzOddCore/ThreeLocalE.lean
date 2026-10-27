module

public import CFSG.Sporadic.SuzOddCore.ThreeLocalD
public import CFSG.Sporadic.SuzOddCore.OddCoreLines

public noncomputable section

namespace CFSG.Sporadic.SuzOddCore

open CFSG.Certificates CFSG.Certificates.RawSchreierDatum CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
  CFSG.Certificates.Native

@[expose] def cbar :
    Equiv.Perm (Fin 280) := suzRho cH0

theorem cbar_pow_three :
    cbar ^ 3 = 1 := by
  rw [cbar, ← map_pow]
  have : cH0 ^ 3 = 1 := Subtype.ext (by
    rw [SubgroupClass.coe_pow]
    exact centerFullPerm_three_pow)
  rw [this, map_one]

theorem orderOf_cbar :

    orderOf cbar = 3 := orderOf_eq_prime cbar_pow_three rho_c_ne_one

theorem orderOf_conj3 {G : Type*} [Group G] (u x : G) (hx : orderOf x = 3) :
    orderOf (u * x * u⁻¹) = 3 := by
  rw [orderOf_conj_eq, hx]

@[expose] def normConjPerm
    (k : ℕ) : Equiv.Perm (Fin 280) :=
  normWordPerm k * cbar * (normWordPerm k)⁻¹

theorem rep_normConj
    {k : ℕ} (hk : k < 39) : Rep 280 (normConj k) (normConjPerm k) := by
  have hinv := rep_inv_of_isInvA (rep_normWordPerm k) (fusionNormChecks_facts.2.2.2.2.2.1 k hk)
  have h := rep_compA (rep_normWordPerm k) (rep_compA tabRep_rho_c.2 hinv)
  rwa [← mul_assoc] at h

theorem mem_zpowers_three {G : Type*} [Group G] {x y : G} (hx : orderOf x = 3)
    (hy : y ∈ Subgroup.zpowers x) : y = 1 ∨ y = x ∨ y = x * x := by
  classical
  have hfin : IsOfFinOrder x := by
    rw [← orderOf_pos_iff, hx]
    norm_num
  rw [hfin.mem_zpowers_iff_mem_range_orderOf, hx] at hy
  simp only [Finset.mem_image, Finset.mem_range] at hy
  obtain ⟨k, hk, rfl⟩ := hy
  interval_cases k
  · exact Or.inl (pow_zero _)
  · exact Or.inr (Or.inl (pow_one _))
  · exact Or.inr (Or.inr (pow_two _))

theorem normConjPerm_order
    {k : ℕ} : orderOf (normConjPerm k) = 3 :=
  orderOf_conj3 _ _ orderOf_cbar

theorem normConjPerm_not_mem
    {k k' : ℕ} (hk : k < 39) (hk' : k' < 39) (hne : k ≠ k') :
    normConjPerm k' ∉ Subgroup.zpowers (normConjPerm k) := by
  intro h
  rcases mem_zpowers_three normConjPerm_order h with h1 | h1 | h1
  · have := normConjPerm_order (k := k')
    rw [h1, orderOf_one] at this
    norm_num at this
  · rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have := (fusionNormChecks_facts.2.2.2.2.2.2.2 k hk k' hk' hlt).1
      rw [(eqA_iff (rep_normConj hk) (rep_normConj hk')).2 h1.symm] at this
      exact Bool.false_ne_true this.symm
    · have := (fusionNormChecks_facts.2.2.2.2.2.2.2 k' hk' k hk hlt).1
      rw [(eqA_iff (rep_normConj hk') (rep_normConj hk)).2 h1] at this
      exact Bool.false_ne_true this.symm
  · rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    ·
      have hx : normConjPerm k = normConjPerm k' * normConjPerm k' := by
        rw [h1]
        have h3 : normConjPerm k ^ 3 = 1 := by
          rw [← normConjPerm_order (k := k)]
          exact pow_orderOf_eq_one _
        calc normConjPerm k = normConjPerm k ^ 3 * normConjPerm k := by rw [h3, one_mul]
          _ = normConjPerm k * normConjPerm k * (normConjPerm k * normConjPerm k) := by
            rw [pow_succ, pow_two]; simp only [mul_assoc]
      have := (fusionNormChecks_facts.2.2.2.2.2.2.2 k hk k' hk' hlt).2
      rw [(eqA_iff (rep_normConj hk) (rep_compA (rep_normConj hk') (rep_normConj hk'))).2 hx]
        at this
      exact Bool.false_ne_true this.symm
    · have := (fusionNormChecks_facts.2.2.2.2.2.2.2 k' hk' k hk hlt).2
      rw [(eqA_iff (rep_normConj hk') (rep_compA (rep_normConj hk) (rep_normConj hk))).2 h1]
        at this
      exact Bool.false_ne_true this.symm

@[expose] def cbarNorm :
    Subgroup (Equiv.Perm (Fin 280)) :=
  localChain.originalSubgroup ⊓ Subgroup.normalizer
    (Subgroup.zpowers cbar : Set (Equiv.Perm (Fin 280)))

@[expose] def normH0 (e : Equiv.Perm (Fin 22880)) : Subgroup (Equiv.Perm (Fin 22880)) :=
  suzH0 ⊓ Subgroup.normalizer (Subgroup.zpowers e : Set (Equiv.Perm (Fin 22880)))

@[expose] def normP (e : Equiv.Perm (Fin 22880)) : Subgroup (Equiv.Perm (Fin 22880)) :=
  suzP ⊓ Subgroup.normalizer (Subgroup.zpowers e : Set (Equiv.Perm (Fin 22880)))

theorem card_normalizer_cbar :
    39 * Nat.card cbarNorm ≤ 6531840 := by
  set N' := cbarNorm.subgroupOf localChain.originalSubgroup
  let f : Fin 39 → localChain.originalSubgroup ⧸ N' := fun k =>
    QuotientGroup.mk (⟨normWordPerm k, normWordPerm_mem k⟩ : localChain.originalSubgroup)
  have hf : Function.Injective f := by
    intro k k' hkk
    by_contra hne
    have hne' : (k : ℕ) ≠ k' := fun h => hne (Fin.ext h)
    rw [QuotientGroup.eq] at hkk
    rw [Subgroup.mem_subgroupOf] at hkk
    obtain ⟨-, hnorm⟩ := hkk
    set u := (normWordPerm k)⁻¹ * normWordPerm k'
    have hu : u = ((⟨normWordPerm k, normWordPerm_mem k⟩ : localChain.originalSubgroup)⁻¹ *
        ⟨normWordPerm k', normWordPerm_mem k'⟩ : localChain.originalSubgroup) := by simp [u]
    rw [← hu] at hnorm
    have hc : u * cbar * u⁻¹ ∈ Subgroup.zpowers cbar :=
      (Subgroup.mem_normalizer_iff.1 hnorm cbar).1 (Subgroup.mem_zpowers cbar)
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hc
    apply normConjPerm_not_mem k.2 k'.2 hne'
    refine Subgroup.mem_zpowers_iff.2 ⟨m, ?_⟩
    have e : normConjPerm k ^ m = normWordPerm k * cbar ^ m * (normWordPerm k)⁻¹ := by
      rw [normConjPerm, ← MulAut.conj_apply, ← MulAut.conj_apply, map_zpow]
    rw [e, hm, normConjPerm]
    simp only [u]
    group
  have hcard := Nat.card_le_card_of_injective f hf
  rw [Nat.card_eq_fintype_card, Fintype.card_fin, ← Subgroup.index_eq_card] at hcard
  have h := N'.card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (show cbarNorm ≤ localChain.originalSubgroup from inf_le_left)).toEquiv, card_localGroup] at h
  rw [← h, mul_comm]
  exact Nat.mul_le_mul_left _ hcard

theorem card_subgroupOf_le {G : Type*} [Group G] [Finite G] (H K : Subgroup G) :
    Nat.card (H.subgroupOf K) ≤ Nat.card H := by
  rw [← Subgroup.card_map_of_injective K.subtype_injective, Subgroup.subgroupOf_map_subtype]
  exact Subgroup.card_le_of_le inf_le_left

theorem card_normalizer_H0
    {e : Equiv.Perm (Fin 22880)} (he : e ∈ suzH0)
    (hρ : suzRho ⟨e, he⟩ = cbar) : Nat.card (normH0 e) ≤ 3 * Nat.card cbarNorm := by
  set K := (normH0 e).subgroupOf suzH0
  have hK : Nat.card K = Nat.card (normH0 e) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [← hK, card_eq_map_mul_ker suzRho K]
  have hker : Nat.card (suzRho.ker.subgroupOf K) ≤ 3 :=
    (card_subgroupOf_le _ _).trans card_ker_suzRho.le
  have hmap : K.map suzRho ≤ cbarNorm := by
    rintro _ ⟨k, hk, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hk
    refine ⟨range_suzRho ▸ ⟨k, rfl⟩, mem_normalizer_of_conj_mem fun y hy => ?_⟩
    have hke : (k : Equiv.Perm (Fin 22880)) * e * (k : Equiv.Perm (Fin 22880))⁻¹ ∈
        Subgroup.zpowers e := (Subgroup.mem_normalizer_iff.1 hk.2 e).1 (Subgroup.mem_zpowers e)
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hke
    have hj' : k * ⟨e, he⟩ * k⁻¹ = (⟨e, he⟩ : suzH0) ^ j :=
      Subtype.ext (by rw [SubgroupClass.coe_zpow]; exact hj.symm)
    have hc : suzRho k * cbar * (suzRho k)⁻¹ = cbar ^ j := by
      rw [← hρ, ← map_inv, ← map_mul, ← map_mul, hj', map_zpow]
    exact conj_mem_zpowers hc hy
  calc Nat.card (K.map suzRho) * Nat.card (suzRho.ker.subgroupOf K)
      ≤ Nat.card cbarNorm * 3 := Nat.mul_le_mul (Subgroup.card_le_of_le hmap) hker
    _ = _ := mul_comm _ _

theorem card_normalizer_P
    {e : Equiv.Perm (Fin 22880)} (he : e ∈ suzS3)
    (hfix : {x : Fin 22880 | e x = x}.ncard = 38) :
    Nat.card (normP e) ≤ 38 * Nat.card (normH0 e) := by
  set NP := normP e
  have h := (MulAction.stabilizer NP (0 : Fin 22880)).card_mul_index
  rw [MulAction.index_stabilizer] at h
  have horb : (MulAction.orbit NP (0 : Fin 22880)).ncard ≤ 38 := by
    rw [← hfix]
    refine Set.ncard_le_ncard ?_ (Set.toFinite _)
    rintro _ ⟨n, rfl⟩
    have hn := n.2
    have hq : (n : Equiv.Perm (Fin 22880))⁻¹ * e * n ∈ Subgroup.zpowers e :=
      (Subgroup.mem_normalizer_iff''.1 hn.2 e).1 (Subgroup.mem_zpowers e)
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hq
    have he0 : e 0 = 0 := (mem_suzH0_iff.1 (suzS3_le_suzH0 he)).2
    have hfix0 : (e ^ j) 0 = 0 := Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self he0 j
    rw [hj, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply] at hfix0
    change e ((n : Equiv.Perm (Fin 22880)) 0) = (n : Equiv.Perm (Fin 22880)) 0
    have := congrArg (n : Equiv.Perm (Fin 22880)) hfix0
    rwa [perm_apply_inv_self] at this
  have hstab : MulAction.stabilizer NP (0 : Fin 22880) = (normH0 e).subgroupOf NP := by
    ext n
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, normH0, Subgroup.mem_inf,
      mem_suzH0_iff]
    exact ⟨fun h => ⟨⟨n.2.1, h⟩, n.2.2⟩, fun h => h.1.2⟩
  have hle : normH0 e ≤ NP := inf_le_inf_right _ suzH0_le_suzP
  rw [hstab, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv] at h
  rw [← h, mul_comm]
  exact Nat.mul_le_mul_right _ horb

theorem normalizer_bound
    {e : Equiv.Perm (Fin 22880)} (he : e ∈ suzS3)
    (hfix : {x : Fin 22880 | e x = x}.ncard = 38) (hρ : suzRho ⟨e, suzS3_le_suzH0 he⟩ = cbar) :
    39 * Nat.card (normP e) ≤ 38 * Nat.card suzH0 := by
  have h1 := card_normalizer_P he hfix
  have h2 := card_normalizer_H0 (suzS3_le_suzH0 he) hρ
  have h3 := card_normalizer_cbar
  rw [card_suzH0]
  calc 39 * Nat.card (normP e)
      ≤ 39 * (38 * (3 * Nat.card cbarNorm)) :=
        Nat.mul_le_mul_left _ (h1.trans (Nat.mul_le_mul_left _ h2))
    _ = 38 * 3 * (39 * Nat.card cbarNorm) := by ring
    _ ≤ 38 * 3 * 6531840 := Nat.mul_le_mul_left _ h3
    _ = 38 * 19595520 := by norm_num

theorem fixed_centerFull {r : ℕ} (hr : r < 9) :
    {x : Fin 22880 | centerFullPerm r x = x}.ncard = fixedCountN 22880 (centerFull r) :=
  ncard_fixed_eq (rep_centerFull hr)

theorem rho_e3 :

    suzRho ⟨centerFullPerm 3, suzS3_le_suzH0 (centerFullPerm_mem (by norm_num))⟩ =
    cbar := rfl

theorem rho_e4 :

    suzRho ⟨centerFullPerm 4, suzS3_le_suzH0 (centerFullPerm_mem (by norm_num))⟩ =
    cbar := by
  have e : (⟨centerFullPerm 4, suzS3_le_suzH0 (centerFullPerm_mem (by norm_num))⟩ : suzH0) =
      cH0 * zH0 := by
    apply Subtype.ext
    change centerFullPerm 4 = centerFullPerm 3 * suzZ
    rw [centerFullPerm_eq (by norm_num)]
    simp
  have hz : suzRho zH0 = 1 := by
    rw [← MonoidHom.mem_ker, ker_suzRho, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_zpowers _
  rw [e, map_mul, hz, mul_one]
  rfl

theorem CTUC_Suz_three_local_normalizer_and_Sylow_center :
    orderOf suzZ = 3 ∧ {x : Fin 22880 | suzZ x = x} = insert 0 suzDeltaΩ ∧
    (∀ x, x ∈ suzDeltaΩ ↔ (x : ℕ) ∈ localDomain) ∧
    suzDeltaΩ = MulAction.orbit suzH0 (localDomain_points.pt 0) ∧ suzDeltaΩ.ncard = 280 ∧
    suzP ⊓ Subgroup.normalizer (suzQ : Set (Equiv.Perm (Fin 22880))) = suzH0 ∧
    suzH0 = suzP ⊓ MulAction.stabilizer (Equiv.Perm (Fin 22880)) (0 : Fin 22880) ∧
    Nat.card suzH0 = 19595520 ∧
    (∀ (g : suzH0) (i : Fin 280),
      localDomain_points.pt (suzRho g i) = (g : Equiv.Perm (Fin 22880)) (localDomain_points.pt i)) ∧
    suzRho.ker = suzQ.subgroupOf suzH0 ∧ suzRho.range = localChain.originalSubgroup ∧
    Nat.card suzRho.range = 6531840 ∧ ValidSchreier localChain ∧
    suzS3 ≤ suzP ∧ Nat.card suzS3 = 2187 ∧
    (∃ T : Sylow 3 suzP, (T : Subgroup suzP) = suzS3.subgroupOf suzP) ∧
    ((Subgroup.center suzS3).map suzS3.subtype : Set (Equiv.Perm (Fin 22880))) =
      Set.range (fun r : Fin 9 => centerFullPerm r) ∧
    Nat.card (Subgroup.center suzS3) = 9 ∧
    (∀ x ∈ Subgroup.center suzS3, x ^ 3 = 1) ∧
    (∀ D : Subgroup (Equiv.Perm (Fin 22880)),
      (D : Set (Equiv.Perm (Fin 22880))) ⊆ (Subgroup.center suzS3).map suzS3.subtype →
        Nat.card D = 3 → D = suzLine 1 ∨ D = suzLine 3 ∨ D = suzLine 4 ∨ D = suzLine 5) ∧
    (∀ r ∈ [1, 3, 4, 5], (suzLine r : Set (Equiv.Perm (Fin 22880))) ⊆
      (Subgroup.center suzS3).map suzS3.subtype ∧ Nat.card (suzLine r) = 3) ∧
    (suzLine 1 ≠ suzLine 3 ∧ suzLine 1 ≠ suzLine 4 ∧ suzLine 1 ≠ suzLine 5 ∧
      suzLine 3 ≠ suzLine 4 ∧ suzLine 3 ≠ suzLine 5 ∧ suzLine 4 ≠ suzLine 5) ∧
    fusionEntries.map (fun e => e.1) = [1, 5] ∧ normEntries = [3, 4] ∧
    suzLine 1 = suzQ ∧ suzFusionG ∈ suzP ∧
    suzQ.map (MulAut.conj suzFusionG).toMonoidHom = suzLine 5 ∧
    (∀ r ∈ normEntries,
      {x : Fin 22880 | ∀ d ∈ suzLine r, d x = x}.ncard = 38 ∧
      39 * Nat.card (normP (centerFullPerm r)) ≤ 38 * Nat.card suzH0 ∧
      Nat.card (normP (centerFullPerm r)) < Nat.card suzH0) := by
  have hcenter : ∀ x, x ∈ (Subgroup.center suzS3).map suzS3.subtype ↔ x ∈ suzZS :=
    fun x => mem_center_map_iff
  have hnorm : ∀ r ∈ normEntries,
      {x : Fin 22880 | ∀ d ∈ suzLine r, d x = x}.ncard = 38 ∧
      39 * Nat.card (normP (centerFullPerm r)) ≤ 38 * Nat.card suzH0 := by
    intro r hr
    have hr' : r = 3 ∨ r = 4 := by simpa [normEntries] using hr
    obtain ⟨-, -, -, h3, h4, -⟩ := fusionNormChecks_facts
    rcases hr' with rfl | rfl
    · have hfix : {x : Fin 22880 | centerFullPerm 3 x = x}.ncard = 38 := by
        rw [fixed_centerFull (by norm_num), h3]
      exact ⟨by rw [suzLine, fixedSet_zpowers, hfix],
        normalizer_bound (centerFullPerm_mem (by norm_num)) hfix rho_e3⟩
    · have hfix : {x : Fin 22880 | centerFullPerm 4 x = x}.ncard = 38 := by
        rw [fixed_centerFull (by norm_num), h4]
      exact ⟨by rw [suzLine, fixedSet_zpowers, hfix],
        normalizer_bound (centerFullPerm_mem (by norm_num)) hfix rho_e4⟩
  refine ⟨orderOf_suzZ, fix_suzZ, mem_suzDeltaΩ_iff, suzDeltaΩ_eq_orbit, ncard_suzDeltaΩ,
    suzP_inf_normalizer_Q, suzH0_eq_stab, card_suzH0, pt_suzRho, ker_suzRho, range_suzRho,
    card_range_suzRho, localChain_valid, suzS3_le_suzP, card_suzS3,
    ⟨suzSylowThree, suzSylowThree_coe⟩, ?_, card_center_suzS3,
    fun x hx => center_pow_three hx, fun D hD h3 => order_three_subgroups D
      (fun x hx => (hcenter x).1 (hD hx)) h3, fun r hr => ?_, suzLines_ne, rfl, rfl,
    fusion_lines.1, suzFusionG_mem, fusion_lines.2, fun r hr => ⟨(hnorm r hr).1,
      (hnorm r hr).2, ?_⟩⟩
  · ext x
    rw [SetLike.mem_coe, hcenter, suzS3_center_eq]
  · have hr' : r = 1 ∨ r = 3 ∨ r = 4 ∨ r = 5 := by simpa using hr
    have hr9 : r < 9 := by omega
    have hr0 : r ≠ 0 := by omega
    exact ⟨fun x hx => (hcenter x).2 (suzLine_le hr9 hx), card_suzLine hr9 hr0⟩
  · have h := (hnorm r hr).2
    rw [card_suzH0] at h ⊢
    omega

end CFSG.Sporadic.SuzOddCore
