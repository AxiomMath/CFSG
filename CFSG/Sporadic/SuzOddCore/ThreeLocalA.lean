module

public import CFSG.Sporadic.SuzOddCore.ThreeLocalCheck
public import CFSG.Sporadic.SuzOddCore.Restrict
public import CFSG.Sporadic.SuzOddCore.GammaBase

public noncomputable section

namespace CFSG.Sporadic.SuzOddCore

open CFSG.Certificates CFSG.Certificates.RawSchreierDatum CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
  CFSG.Certificates.Native

theorem threeLocal_parts :
    zChecks = true ∧ localChecks fullExtArrs = true ∧
    sylowCenterChecks (tFullOf fullExtArrs) (compactEnum (tFullOf fullExtArrs)) = true ∧
    fusionNormChecks = true := by
  have h := threeLocal_check
  simp only [threeChecks, Bool.and_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem zChecks_facts :
    eqA 22880 (compA 22880 zArr (compA 22880 zArr zArr)) (idA 22880) = true ∧
    eqA 22880 zArr (idA 22880) = false ∧ zArr[0]! = 0 ∧
    (∀ j ∈ certStabIdx,
      eqA 22880 (compA 22880 certStrongArrs[j]! (compA 22880 zArr certStrongInvs[j]!)) zArr =
        true ∨
      eqA 22880 (compA 22880 certStrongArrs[j]! (compA 22880 zArr certStrongInvs[j]!))
        (compA 22880 zArr zArr) = true) ∧
    deltaOf zArr = localDomain := by
  have h := threeLocal_parts.1
  simp only [zChecks, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, List.all_eq_true,
    Bool.or_eq_true, and_assoc] at h
  exact h

theorem suzZ_pow_three :
    suzZ ^ 3 = 1 := by
  have h := eq_of_eqA (rep_compA rep_zArr (rep_compA rep_zArr rep_zArr)) rep_idA zChecks_facts.1
  calc suzZ ^ 3 = suzZ * (suzZ * suzZ) := by rw [pow_succ, pow_two, mul_assoc]
    _ = 1 := h

theorem suzZ_ne_one :
    suzZ ≠ 1 := by
  intro h
  have := (eqA_iff rep_zArr rep_idA).2 h
  rw [zChecks_facts.2.1] at this
  exact Bool.false_ne_true this

theorem orderOf_suzZ :
    orderOf suzZ = 3 := orderOf_eq_prime suzZ_pow_three suzZ_ne_one

theorem suzZ_zero :
    suzZ 0 = 0 :=
  Fin.ext ((rep_zArr 0).symm.trans zChecks_facts.2.2.1)

theorem fix_suzZ :
    {x : Fin 22880 | suzZ x = x} = insert 0 suzDeltaΩ := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff]
  constructor
  · intro h
    by_cases hx : x = 0
    · exact Or.inl hx
    · exact Or.inr ⟨h, hx⟩
  · rintro (rfl | h)
    · exact suzZ_zero
    · exact h.1

theorem mem_suzDeltaΩ_iff
    (x : Fin 22880) : x ∈ suzDeltaΩ ↔ (x : ℕ) ∈ localDomain := by
  rw [← mem_deltaOf, zChecks_facts.2.2.2.2]

theorem localChecks_facts :
    fullExtArrs.size = 14 ∧ localDomain.length = 280 ∧
    (∀ k < 8, restrictArr localDomain certStrongArrs[localStrongIdx.getD k 0]! =
      localGenArrs[k]!) ∧
    (∀ j < 14, isInvA 22880 fullExtArrs[j]! (invCand 22880 fullExtArrs[j]!) = true ∧
      restrictArr localDomain fullExtArrs[j]! = localStrongArrs[j]!) ∧
    rawChainOK 280 localGenArrs localStrongArrs localBaseNat.toArray localDerivs 4 = true ∧
    (rawOrbitSizes 280 localStrongArrs localBaseNat.toArray).prod = 6531840 ∧
    (rawOrbitSizes 280 localStrongArrs localBaseNat.toArray).head? = some 280 := by
  have h := threeLocal_parts.2.1
  simp only [localChecks, Bool.and_eq_true, beq_iff_eq, allLt_iff, and_assoc] at h
  exact h

theorem localDomain_points : PointsList 22880 280 localDomain where
  len := localChecks_facts.2.1
  lt x hx := by
    rw [← zChecks_facts.2.2.2.2, deltaOf, List.mem_filter, List.mem_range] at hx
    exact hx.1
  nodup := by
    rw [← zChecks_facts.2.2.2.2, deltaOf]
    exact List.nodup_range.filter _

theorem ncard_suzDeltaΩ :
    suzDeltaΩ.ncard = 280 := by
  have e : suzDeltaΩ = Set.range localDomain_points.pt := by
    ext x
    rw [mem_suzDeltaΩ_iff]
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := localDomain_points.exists_pt hx
      exact ⟨i, hi⟩
    · rintro ⟨i, rfl⟩
      exact localDomain_points.pt_mem i
  rw [e, Set.ncard_range_of_injective localDomain_points.pt_injective, Nat.card_eq_fintype_card,
    Fintype.card_fin]

theorem suzS_mem_suzP
    {j : ℕ} (hj : j < 10) : suzS j ∈ suzP := by
  rw [← certChain_originalSubgroup]
  have := certChain_eqns.strong_mem ⟨j, hj⟩
  rwa [certChain_strong_get] at this

theorem certStabIdx_lt {j : ℕ} (hj : j ∈ certStabIdx) : j < 10 := by
  simp only [certStabIdx, List.mem_cons, List.not_mem_nil, or_false] at hj
  omega

theorem suzH0_le_suzP :
    suzH0 ≤ suzP := by
  rw [suzH0, Subgroup.closure_le]
  rintro _ ⟨j, hj, rfl⟩
  exact suzS_mem_suzP (certStabIdx_lt hj)

theorem suzS_zero_iff
    {j : ℕ} (hj : j < 10) : suzS j 0 = 0 ↔ j ∈ certStabIdx := by
  have hidx := certChain_check.2.2.2.1 1 (by norm_num)
  have e : certLevelIdx 1 = certStabIdx := rfl
  rw [← e, ← hidx, levelIdx, List.mem_filter, List.mem_range, certStrongArrs_size, fixesFirst,
    allLt_iff]
  have h0 : certBaseNat.toArray[0]! = 0 := rfl
  constructor
  · intro h
    refine ⟨hj, fun k hk => ?_⟩
    have hk0 : k = 0 := by omega
    subst hk0
    rw [beq_iff_eq, h0, (rep_certStrong hj).apply (by norm_num)]
    exact congrArg Fin.val h
  · rintro ⟨-, h⟩
    have := h 0 (by norm_num)
    rw [beq_iff_eq, h0, (rep_certStrong hj).apply (by norm_num)] at this
    exact Fin.ext this

theorem suzH0_eq_levelSubgroup :
    suzH0 = certChain.levelSubgroup 1 := by
  rw [suzH0, RawSchreierDatum.levelSubgroup]
  congr 1
  ext s
  simp only [Set.mem_ofPred_eq, certChain.mem_levelGenerators_iff, certChain_base_toList]
  constructor
  · rintro ⟨j, hj, rfl⟩
    have hj10 := certStabIdx_lt hj
    refine ⟨?_, fun b hb => ?_⟩
    · rw [← certChain_strong_get ⟨j, hj10⟩]
      exact schreier_vector_get_mem_toList _ _
    · simp only [List.take_succ_cons, List.take_zero, List.mem_singleton] at hb
      rw [hb]
      exact (suzS_zero_iff hj10).2 hj
  · rintro ⟨hs, hfix⟩
    obtain ⟨j, rfl⟩ := (schreier_vector_mem_toList_iff_get certChain.strong s).1 hs
    rw [certChain_strong_get] at hfix ⊢
    have hj10 : (j : ℕ) < 10 := j.2
    exact ⟨j, (suzS_zero_iff hj10).1 (hfix 0 (by simp)), rfl⟩

theorem suzH0_eq_stab :
    suzH0 = suzP ⊓ MulAction.stabilizer (Equiv.Perm (Fin 22880)) (0 : Fin 22880) := by
  have hb : 0 < certChain.baseCount := by rw [certChain_baseCount]; norm_num
  have h := certChain.levelSubgroup_succ_eq_stabilizer certChain_valid ⟨0, hb⟩
  rw [certChain.levelSubgroup_zero_eq_original certChain_valid, certChain_originalSubgroup] at h
  rw [suzH0_eq_levelSubgroup, h]
  congr 2

theorem mem_suzH0_iff
    {g : Equiv.Perm (Fin 22880)} : g ∈ suzH0 ↔ g ∈ suzP ∧ g 0 = 0 := by
  rw [suzH0_eq_stab, Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
  rfl

theorem mem_normalizer_of_conj_mem {G : Type*} [Group G] [Finite G] {H : Subgroup G} {g : G}
    (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) : g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  let f : H → H := fun y => ⟨g * y * g⁻¹, h y y.2⟩
  have hf : Function.Injective f := fun a b hab => by
    have := congrArg Subtype.val hab
    simp only [f, mul_left_inj, mul_right_inj] at this
    exact Subtype.ext this
  obtain ⟨y, hy⟩ := Finite.surjective_of_injective hf ⟨g * x * g⁻¹, hx⟩
  have hyx : (y : G) = x := by
    have := congrArg Subtype.val hy
    simp only [f, mul_left_inj, mul_right_inj] at this
    exact this
  rw [← hyx]
  exact y.2

theorem conj_mem_zpowers {G : Type*} [Group G] {g x : G} {k : ℤ} (h : g * x * g⁻¹ = x ^ k)
    {y : G} (hy : y ∈ Subgroup.zpowers x) : g * y * g⁻¹ ∈ Subgroup.zpowers x := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  have e : g * x ^ m * g⁻¹ = (g * x * g⁻¹) ^ m := by
    rw [← MulAut.conj_apply, ← MulAut.conj_apply, map_zpow]
  rw [e, h, ← zpow_mul]
  exact Subgroup.zpow_mem_zpowers x _

theorem suzS_conj_suzZ
    {j : ℕ} (hj : j ∈ certStabIdx) :
    suzS j * suzZ * (suzS j)⁻¹ = suzZ ^ (1 : ℤ) ∨ suzS j * suzZ * (suzS j)⁻¹ = suzZ ^ (2 : ℤ) := by
  have hj10 := certStabIdx_lt hj
  have hrep := rep_compA (rep_certStrong hj10) (rep_compA rep_zArr (rep_certStrongInv hj10))
  rcases zChecks_facts.2.2.2.1 j hj with h | h
  · left
    rw [zpow_one, ← mul_assoc] at *
    exact (eqA_iff hrep rep_zArr).1 h
  · right
    have := (eqA_iff hrep (rep_compA rep_zArr rep_zArr)).1 h
    rw [← mul_assoc] at this
    rw [this, zpow_two]

theorem suzH0_le_normalizer :
    suzH0 ≤ Subgroup.normalizer (suzQ : Set (Equiv.Perm (Fin 22880))) := by
  rw [suzH0, Subgroup.closure_le]
  rintro _ ⟨j, hj, rfl⟩
  refine mem_normalizer_of_conj_mem fun y hy => ?_
  rcases suzS_conj_suzZ hj with h | h
  · exact conj_mem_zpowers h hy
  · exact conj_mem_zpowers h hy

theorem evalWord_mem {M S : Type*} [Group M] {ι : S → M} {H : Subgroup M} (h : ∀ s, ι s ∈ H)
    (w : List (S × Bool)) : Quiver.SchreierGraph.evalWord ι w ∈ H :=
  (Subgroup.closure_le H).2 (Set.range_subset_iff.2 h)
    (Quiver.SchreierGraph.evalWord_mem_closure ι w)

theorem strongWord_mem_suzP
    (w : List ℤ) : strongWord w ∈ suzP :=
  evalWord_mem (fun h : Fin 10 => suzS_mem_suzP h.2) _

theorem suzZ_mem_suzP :
    suzZ ∈ suzP := suzP.pow_mem (strongWord_mem_suzP _) _

theorem suzZ_mem_suzH0 :
    suzZ ∈ suzH0 := mem_suzH0_iff.2 ⟨suzZ_mem_suzP, suzZ_zero⟩

theorem suzQ_le_suzH0 :
    suzQ ≤ suzH0 := by
  rw [suzQ, Subgroup.zpowers_le]
  exact suzZ_mem_suzH0

theorem card_suzQ :
    Nat.card suzQ = 3 := by
  rw [suzQ, Nat.card_zpowers, orderOf_suzZ]

theorem card_suzH0 :
    Nat.card suzH0 = 19595520 := by
  have := suzP_isPreprimitive
  have horb : MulAction.orbit suzP (0 : Fin 22880) = Set.univ :=
    MulAction.orbit_eq_univ suzP 0
  have h := (MulAction.stabilizer suzP (0 : Fin 22880)).card_mul_index
  rw [MulAction.index_stabilizer, horb, Set.ncard_univ,
    show Nat.card (Fin 22880) = 22880 by simp, suzP_card] at h
  have e : MulAction.stabilizer suzP (0 : Fin 22880) = suzH0.subgroupOf suzP := by
    ext g
    rw [Subgroup.mem_subgroupOf, mem_suzH0_iff, MulAction.mem_stabilizer_iff]
    exact ⟨fun h => ⟨g.2, h⟩, fun h => h.2⟩
  rw [e, Nat.card_congr (Subgroup.subgroupOfEquivOfLe suzH0_le_suzP).toEquiv] at h
  rw [Nat.eq_div_of_mul_eq_left (by norm_num) h]

theorem suzP_inf_normalizer_Q :
    suzP ⊓ Subgroup.normalizer (suzQ : Set (Equiv.Perm (Fin 22880))) = suzH0 := by
  have := suzP_isPreprimitive
  have hcoatom := MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive
    (G := suzP) (X := Fin 22880) 0
  refine le_antisymm ?_ (le_inf suzH0_le_suzP suzH0_le_normalizer)
  set N := (Subgroup.normalizer (suzQ : Set (Equiv.Perm (Fin 22880)))).subgroupOf suzP
  have hstab : MulAction.stabilizer suzP (0 : Fin 22880) ≤ N := by
    intro g hg
    rw [Subgroup.mem_subgroupOf]
    exact suzH0_le_normalizer (mem_suzH0_iff.2 ⟨g.2, hg⟩)
  rcases hcoatom.le_iff.1 hstab with h | h
  · exfalso
    have hn : (suzQ.subgroupOf suzP).Normal := by
      constructor
      intro q hq g
      have hg : (g : Equiv.Perm (Fin 22880)) ∈ Subgroup.normalizer
          (suzQ : Set (Equiv.Perm (Fin 22880))) := by
        have : g ∈ N := h ▸ Subgroup.mem_top g
        rwa [Subgroup.mem_subgroupOf] at this
      rw [Subgroup.mem_subgroupOf] at hq ⊢
      simpa using (Subgroup.mem_normalizer_iff.1 hg q).1 hq
    have := suzP_isSimpleGroup
    rcases hn.eq_bot_or_eq_top with hb | ht
    · have hz : (⟨suzZ, suzZ_mem_suzP⟩ : suzP) ∈ suzQ.subgroupOf suzP := by
        rw [Subgroup.mem_subgroupOf]
        exact Subgroup.mem_zpowers suzZ
      rw [hb, Subgroup.mem_bot] at hz
      exact suzZ_ne_one (congrArg Subtype.val hz)
    · have hle : suzP ≤ suzQ := by
        intro g hg
        have : (⟨g, hg⟩ : suzP) ∈ suzQ.subgroupOf suzP := ht ▸ Subgroup.mem_top _
        rwa [Subgroup.mem_subgroupOf] at this
      have := Subgroup.card_le_of_le hle
      rw [suzP_card, card_suzQ] at this
      norm_num at this
  · intro g hg
    have hgN : (⟨g, hg.1⟩ : suzP) ∈ N := by
      rw [Subgroup.mem_subgroupOf]
      exact hg.2
    rw [h, MulAction.mem_stabilizer_iff] at hgN
    exact mem_suzH0_iff.2 ⟨hg.1, hgN⟩

end CFSG.Sporadic.SuzOddCore
