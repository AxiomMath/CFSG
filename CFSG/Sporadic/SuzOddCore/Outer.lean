module

public import CFSG.Sporadic.SuzOddCore.OuterCheck
public import CFSG.Sporadic.SuzOddCore.CharClassC
public import CFSG.Sporadic.SuzOddCore.SmallModel
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public noncomputable section

namespace CFSG.Sporadic.SuzOddCore

open CFSG.Certificates CFSG.Certificates.RawSchreierDatum CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem suzOuter_sq :
    suzOuter * suzOuter = 1 :=
  (eqA_iff (rep_compA rep_suzOuter rep_suzOuter) rep_idA).1 outer_check.1

theorem suzOuter_ne_one :
    suzOuter ≠ 1 := by
  intro h
  have := (eqA_iff rep_suzOuter rep_idA).2 h
  rw [outer_check.2.1] at this
  exact Bool.false_ne_true this

theorem suzOuter_inv :
    suzOuter⁻¹ = suzOuter := by
  rw [inv_eq_iff_mul_eq_one, suzOuter_sq]

theorem zpow_two_cycle {σ : Equiv.Perm (Fin 22880)} {a : Fin 22880} (h : σ (σ a) = a) :
    ∀ k : ℤ, (σ ^ k) a = a ∨ (σ ^ k) a = σ a := by
  have hinv : σ⁻¹ a = σ a := by
    have := congrArg (⇑σ⁻¹) h
    rw [perm_inv_apply_self] at this
    exact this.symm
  intro k
  induction k using Int.induction_on with
  | zero => left; rfl
  | succ k ih =>
    rw [add_comm, zpow_add, zpow_one, Equiv.Perm.mul_apply]
    rcases ih with h1 | h1
    · right; rw [h1]
    · left; rw [h1, h]
  | pred k ih =>
    rw [sub_eq_neg_add, zpow_add, zpow_neg_one, Equiv.Perm.mul_apply]
    rcases ih with h1 | h1
    · right; rw [h1, hinv]
    · left; rw [h1, ← h, perm_inv_apply_self, h]

theorem suzS_fix3
    {j : ℕ} (hj : j < 10) (h0 : suzS j 0 = 0) (h1 : suzS j 1 = 1)
    (h2 : suzS j 2 = 2) : j = 9 := by
  have hidx := certChain_check.2.2.2.1 3 (by norm_num)
  have hmem : j ∈ levelIdx certStrongArrs certBaseNat.toArray 3 := by
    rw [levelIdx, List.mem_filter, List.mem_range, certStrongArrs_size, fixesFirst, allLt_iff]
    refine ⟨hj, fun k hk => ?_⟩
    rw [beq_iff_eq]
    interval_cases k
    · rw [show certBaseNat.toArray[0]! = 0 from rfl, (rep_certStrong hj).apply (by norm_num)]
      exact congrArg Fin.val h0
    · rw [show certBaseNat.toArray[1]! = 1 from rfl, (rep_certStrong hj).apply (by norm_num)]
      exact congrArg Fin.val h1
    · rw [show certBaseNat.toArray[2]! = 2 from rfl, (rep_certStrong hj).apply (by norm_num)]
      exact congrArg Fin.val h2
  rw [hidx] at hmem
  simpa [certLevelIdx] using hmem

theorem levelSubgroup_three_le :
    certChain.levelSubgroup 3 ≤ Subgroup.zpowers (suzS 9) := by
  rw [RawSchreierDatum.levelSubgroup, Subgroup.closure_le]
  intro s hs
  obtain ⟨hstrong, hfix⟩ := (certChain.mem_levelGenerators_iff 3 s).1 hs
  obtain ⟨j, rfl⟩ := (schreier_vector_mem_toList_iff_get _ s).1 hstrong
  rw [certChain_strong_get] at hfix ⊢
  rw [certChain_base_toList] at hfix
  have hj : (j : ℕ) < 10 := j.2
  have h9 := suzS_fix3 hj (hfix 0 (by simp)) (hfix 1 (by simp)) (hfix 2 (by simp))
  rw [SetLike.mem_coe, h9]
  exact Subgroup.mem_zpowers _

theorem suzOuter_not_mem :
    suzOuter ∉ suzP := by
  intro hu
  obtain ⟨-, -, hw, h0, h1, h2, h3, h9, h9', -⟩ := outer_check
  have hrep := rep_compA (rep_strongWord hw) rep_suzOuter
  set r := strongWord uRejectWord * suzOuter
  have hr : r ∈ suzP := suzP.mul_mem (strongWord_mem_suzP _) hu
  have hfix : ∀ b ∈ certChain.base.toList.take 3, r b = b := by
    rw [certChain_base_toList]
    intro b hb
    simp only [List.take_succ_cons, List.take_zero, List.mem_cons, List.not_mem_nil,
      or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact Fin.ext ((hrep 0).symm.trans h0)
    · exact Fin.ext ((hrep 1).symm.trans h1)
    · exact Fin.ext ((hrep 2).symm.trans h2)
  have hlev : r ∈ certChain.levelSubgroup 3 :=
    (certChain.mem_levelSubgroup_iff certChain_valid 3 (by rw [certChain_baseCount]; norm_num)
      r).2 ⟨by rw [certChain_originalSubgroup]; exact hr, hfix⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (levelSubgroup_three_le hlev)
  have hr9 := rep_certStrong (by norm_num : 9 < 10)
  have e1 : ((suzS 9 3 : Fin 22880) : ℕ) = (certStrongArrs[9]!)[3]! := (hr9 3).symm
  have hs9 : suzS 9 (suzS 9 3) = 3 := by
    apply Fin.ext
    have e2 : ((suzS 9 (suzS 9 3) : Fin 22880) : ℕ) =
        (certStrongArrs[9]!)[((suzS 9 3 : Fin 22880) : ℕ)]! := (hr9 _).symm
    rw [e2, e1, h9]
    rfl
  have h3' : ((r 3 : Fin 22880) : ℕ) = 2862 := (hrep 3).symm.trans h3
  rcases zpow_two_cycle hs9 k with h | h
  · rw [hk] at h
    rw [h] at h3'
    have : ((3 : Fin 22880) : ℕ) = 3 := rfl
    omega
  · rw [hk] at h
    rw [h, e1] at h3'
    exact h9' h3'

theorem suzOuter_conj_gen
    {i : ℕ} (hi : i < 2) :
    suzOuter * (if i = 0 then suzA0 else suzA1) * suzOuter⁻¹ ∈ suzP := by
  have h := (outer_check.2.2.2.2.2.2.2.2.2.1 i hi)
  have hrepi : Rep 22880 (certArr i) (if i = 0 then suzA0 else suzA1) := by
    interval_cases i
    · exact rep_suzA0
    · exact rep_suzA1
  have := (eqA_iff (rep_compA rep_suzOuter (rep_compA hrepi rep_suzOuter))
    (rep_strongWord h.1)).1 h.2
  rw [suzOuter_inv, mul_assoc, this]
  exact strongWord_mem_suzP _

theorem suzOuter_conj_mem
    {p : Equiv.Perm (Fin 22880)} (hp : p ∈ suzP) :
    suzOuter * p * suzOuter⁻¹ ∈ suzP := by
  induction hp using Subgroup.closure_induction with
  | mem g hg =>
    rcases hg with rfl | rfl
    · exact suzOuter_conj_gen (i := 0) (by norm_num)
    · exact suzOuter_conj_gen (i := 1) (by norm_num)
  | one => simp
  | mul g h _ _ hg hh =>
    have : suzOuter * (g * h) * suzOuter⁻¹ =
        (suzOuter * g * suzOuter⁻¹) * (suzOuter * h * suzOuter⁻¹) := by group
    rw [this]
    exact suzP.mul_mem hg hh
  | inv g _ hg =>
    have : suzOuter * g⁻¹ * suzOuter⁻¹ = (suzOuter * g * suzOuter⁻¹)⁻¹ := by group
    rw [this]
    exact suzP.inv_mem hg

theorem suzOuter_conj_eq :
    suzP.map (MulAut.conj suzOuter).toMonoidHom = suzP := by
  apply le_antisymm
  · rintro _ ⟨p, hp, rfl⟩
    exact suzOuter_conj_mem hp
  · intro p hp
    refine ⟨suzOuter * p * suzOuter⁻¹, suzOuter_conj_mem hp, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, suzOuter_inv]
    rw [show suzOuter * (suzOuter * p * suzOuter) * suzOuter = (suzOuter * suzOuter) * p *
      (suzOuter * suzOuter) by group, suzOuter_sq, one_mul, mul_one]

theorem suzOuter_mem_suzR : suzOuter ∈ suzR := Subgroup.subset_closure (Set.mem_insert _ _)

theorem suzP_le_suzR : suzP ≤ suzR := fun _ hp =>
  Subgroup.subset_closure (Set.mem_insert_of_mem _ hp)

theorem mem_suzR_iff
    (g : Equiv.Perm (Fin 22880)) : g ∈ suzR ↔ g ∈ suzP ∨ suzOuter * g ∈ suzP := by
  constructor
  · intro hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      rcases hg with rfl | hg
      · right; rw [suzOuter_sq]; exact suzP.one_mem
      · left; exact hg
    | one => left; exact suzP.one_mem
    | mul g h _ _ hg hh =>
      rcases hg with hg | hg <;> rcases hh with hh | hh
      · left; exact suzP.mul_mem hg hh
      · right
        rw [show suzOuter * (g * h) = suzOuter * g * suzOuter⁻¹ * (suzOuter * h) by group]
        exact suzP.mul_mem (suzOuter_conj_mem hg) hh
      · right; rw [← mul_assoc]; exact suzP.mul_mem hg hh
      · left
        have e : g * h = suzOuter * (suzOuter * g) * suzOuter⁻¹ * (suzOuter * h) := by
          rw [show suzOuter * (suzOuter * g) * suzOuter⁻¹ * (suzOuter * h) =
            (suzOuter * suzOuter) * g * (suzOuter⁻¹ * suzOuter) * h by group, suzOuter_sq,
            inv_mul_cancel, one_mul, mul_one]
        rw [e]
        exact suzP.mul_mem (suzOuter_conj_mem hg) hh
    | inv g _ hg =>
      rcases hg with hg | hg
      · left; exact suzP.inv_mem hg
      · right
        have e : suzOuter * g⁻¹ = suzOuter * (suzOuter * g)⁻¹ * suzOuter⁻¹ := by
          rw [show suzOuter * (suzOuter * g)⁻¹ * suzOuter⁻¹ = suzOuter * g⁻¹ *
            (suzOuter * suzOuter)⁻¹ by group, suzOuter_sq, inv_one, mul_one]
        rw [e]
        exact suzOuter_conj_mem (suzP.inv_mem hg)
  · rintro (h | h)
    · exact suzP_le_suzR h
    · have := suzR.mul_mem suzOuter_mem_suzR (suzP_le_suzR h)
      rwa [← mul_assoc, suzOuter_sq, one_mul] at this

theorem suzR_conj_mem
    {r : Equiv.Perm (Fin 22880)} (hr : r ∈ suzR) {p : Equiv.Perm (Fin 22880)}
    (hp : p ∈ suzP) : r * p * r⁻¹ ∈ suzP := by
  rcases (mem_suzR_iff r).1 hr with h | h
  · exact suzP.mul_mem (suzP.mul_mem h hp) (suzP.inv_mem h)
  · have e : r * p * r⁻¹ = suzOuter⁻¹ * ((suzOuter * r) * p * (suzOuter * r)⁻¹) * suzOuter := by
      group
    rw [e, suzOuter_inv]
    have := suzOuter_conj_mem (suzP.mul_mem (suzP.mul_mem h hp) (suzP.inv_mem h))
    rwa [suzOuter_inv] at this

theorem suzP_normal_R :
    (suzP.subgroupOf suzR).Normal := by
  constructor
  intro n hn g
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  exact suzR_conj_mem g.2 hn

theorem suzP_index_R :
    (suzP.subgroupOf suzR).index = 2 := by
  rw [Subgroup.index_eq_two_iff]
  refine ⟨⟨suzOuter, suzOuter_mem_suzR⟩, fun b => ?_⟩
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
  change Xor ((b : Equiv.Perm (Fin 22880)) * suzOuter ∈ suzP) ((b : Equiv.Perm (Fin 22880)) ∈ suzP)
  rcases (mem_suzR_iff b).1 b.2 with hb | hb
  · right
    refine ⟨hb, fun hbv => suzOuter_not_mem ?_⟩
    have := suzP.mul_mem (suzP.inv_mem hb) hbv
    rwa [inv_mul_cancel_left] at this
  · left
    refine ⟨?_, fun hbm => suzOuter_not_mem ?_⟩
    · have e : (b : Equiv.Perm (Fin 22880)) * suzOuter =
          suzOuter * (suzOuter * b) * suzOuter⁻¹ := by
        rw [show suzOuter * (suzOuter * b) * suzOuter⁻¹ = (suzOuter * suzOuter) * b * suzOuter⁻¹ by
          group, suzOuter_sq, one_mul, suzOuter_inv]
      rw [e]
      exact suzOuter_conj_mem hb
    · have := suzP.mul_mem hb (suzP.inv_mem hbm)
      rwa [mul_inv_cancel_right] at this

theorem suzR_card :
    Nat.card suzR = 896690995200 := by
  have h := (suzP.subgroupOf suzR).card_mul_index
  rw [suzP_index_R, Nat.card_congr (Subgroup.subgroupOfEquivOfLe suzP_le_suzR).toEquiv,
    suzP_card] at h
  rw [← h]

theorem suzR_semidirect :
    Subgroup.zpowers suzOuter ⊓ suzP = ⊥ ∧ suzP ⊔ Subgroup.zpowers suzOuter = suzR := by
  refine ⟨?_, le_antisymm (sup_le suzP_le_suzR (Subgroup.zpowers_le.2 suzOuter_mem_suzR)) ?_⟩
  · rw [eq_bot_iff]
    rintro g ⟨hg, hgP⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    rw [Subgroup.mem_bot]
    have hord : orderOf suzOuter = 2 :=
      orderOf_eq_prime (by rw [pow_two]; exact suzOuter_sq) suzOuter_ne_one
    rw [zpow_eq_zpow_emod' k (show suzOuter ^ 2 = 1 by rw [pow_two]; exact suzOuter_sq)] at hgP ⊢
    have hk : k % (2 : ℕ) = 0 ∨ k % (2 : ℕ) = 1 := by omega
    rcases hk with hk | hk
    · rw [hk, zpow_zero]
    · rw [hk, zpow_one] at hgP
      exact absurd hgP suzOuter_not_mem
  · rw [suzR, Subgroup.closure_le]
    rintro g (rfl | hg)
    · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    · exact Subgroup.mem_sup_left hg

theorem suzP_centralizer :
    Subgroup.centralizer (suzP : Set (Equiv.Perm (Fin 22880))) = ⊥ := by
  rw [eq_bot_iff]
  intro c hc
  rw [Subgroup.mem_bot]
  have hcm : ∀ m ∈ suzP, m * c = c * m := fun m hm => Subgroup.mem_centralizer_iff.1 hc m hm
  have h0 : c 0 = 0 := by
    by_contra hne
    obtain ⟨j, hj, hmove⟩ := outer_check.2.2.2.2.2.2.2.2.2.2 (c 0) (c 0).2
      (fun h => hne (Fin.ext h))
    have hj10 := certStabIdx_lt hj
    have hfix : suzS j 0 = 0 := (suzS_zero_iff hj10).2 hj
    apply hmove
    rw [(rep_certStrong hj10) (c 0)]
    have := congrArg (fun σ : Equiv.Perm (Fin 22880) => σ 0) (hcm _ (suzS_mem_suzP hj10))
    simp only [Equiv.Perm.mul_apply, hfix] at this
    rw [this]
  ext d
  obtain ⟨m, hm, rfl⟩ := suzP_exists_smul 0 d
  have := congrArg (fun σ : Equiv.Perm (Fin 22880) => σ 0) (hcm m hm)
  simp only [Equiv.Perm.mul_apply, h0] at this
  rw [Equiv.Perm.one_apply, ← this]

@[expose] def suzConjR :
    suzR →* MulAut suzP where
  toFun r :=
    { toFun := fun p => ⟨r * p * r⁻¹, suzR_conj_mem r.2 p.2⟩
      invFun := fun p => ⟨(r : Equiv.Perm (Fin 22880))⁻¹ * p * r, by
        have := suzR_conj_mem (suzR.inv_mem r.2) p.2
        rwa [inv_inv] at this⟩
      left_inv := fun p => Subtype.ext (by simp [mul_assoc])
      right_inv := fun p => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun p q => Subtype.ext (by simp [mul_assoc]) }
  map_one' := by
    ext p
    simp
  map_mul' r s := by
    ext p
    simp [mul_assoc]

theorem suzConjR_apply
    (r : suzR) (p : suzP) :
    ((suzConjR r p : suzP) : Equiv.Perm (Fin 22880)) = r * p * (r : Equiv.Perm (Fin 22880))⁻¹ :=
  rfl

theorem suzConjR_injective :
    Function.Injective suzConjR := by
  rw [injective_iff_map_eq_one]
  intro r hr
  have hc : (r : Equiv.Perm (Fin 22880)) ∈
      Subgroup.centralizer (suzP : Set (Equiv.Perm (Fin 22880))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    have := congrArg (fun α : MulAut suzP => ((α ⟨p, hp⟩ : suzP) : Equiv.Perm (Fin 22880))) hr
    simp only [suzConjR_apply, MulAut.one_apply] at this
    calc p * r = r * p * (r : Equiv.Perm (Fin 22880))⁻¹ * r := by rw [this]
      _ = r * p := by group
  rw [suzP_centralizer, Subgroup.mem_bot] at hc
  exact Subtype.ext hc

instance :
    Finite (MulAut suzP) := Finite.of_injective suzGraphPhi suzGraphPhi_injective

theorem card_mulAut_suzP_le :
    Nat.card (MulAut suzP) ≤ 896690995200 :=
  CTUC_Suz_characteristic_three_class_and_faithful_graph_action.2.2.2.2.2.2.trans
    CTUC_Suz_graph_automorphism_order_bound.1

theorem suzConjR_bijective :
    Function.Bijective suzConjR :=
  suzConjR_injective.bijective_of_nat_card_le (by rw [suzR_card]; exact card_mulAut_suzP_le)

theorem card_mulAut_suzP :
    Nat.card (MulAut suzP) = 896690995200 := by
  rw [← suzR_card]
  exact (Nat.card_congr (Equiv.ofBijective _ suzConjR_bijective)).symm

theorem suzConjR_map_suzP :
    (suzP.subgroupOf suzR).map suzConjR = (MulAut.conj : suzP →* MulAut suzP).range := by
  ext α
  constructor
  · rintro ⟨r, hr, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hr
    refine ⟨⟨r, hr⟩, ?_⟩
    ext p
    simp [suzConjR_apply, MulAut.conj_apply]
  · rintro ⟨p, rfl⟩
    refine ⟨⟨p, suzP_le_suzR p.2⟩, by rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]; exact p.2, ?_⟩
    ext q
    simp [suzConjR_apply, MulAut.conj_apply]

theorem center_eq_bot_of_simple {G : Type*} [Group G] [IsSimpleGroup G]
    (h : ∃ a b : G, a * b ≠ b * a) : Subgroup.center G = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h1 | h1
  · exact h1
  · exfalso
    obtain ⟨a, b, hab⟩ := h
    have hb : b ∈ Subgroup.center G := h1 ▸ Subgroup.mem_top b
    exact hab (Subgroup.mem_center_iff.1 hb a)

theorem card_inn {G : Type*} [Group G] (h : Subgroup.center G = ⊥) :
    Nat.card (ComponentClassification.OuterAutomorphisms.inner G) = Nat.card G := by
  have hinj : Function.Injective (MulAut.conj : G →* MulAut G) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hc : g ∈ Subgroup.center G := Subgroup.mem_center_iff.2 fun x => by
      have := congrArg (fun α : MulAut G => α x) hg
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc x * g = g * x * g⁻¹ * g := by rw [this]
        _ = g * x := by group
    rw [h, Subgroup.mem_bot] at hc
    exact hc
  rw [ComponentClassification.OuterAutomorphisms.inner, MonoidHom.range_eq_map,
    Subgroup.card_map_of_injective hinj, Subgroup.card_top]

theorem suzP_not_comm :
    ∃ a b : suzP, a * b ≠ b * a := by
  obtain ⟨x, y, hxy⟩ := suzM_not_comm
  refine ⟨suzTheta.symm x, suzTheta.symm y, fun h => hxy ?_⟩
  have := congrArg suzTheta h
  simpa using this

theorem card_out_eq_two {G : Type*} [Group G] (hpos : 0 < Nat.card G)
    (h : Subgroup.center G = ⊥) (hc : Nat.card (MulAut G) = 2 * Nat.card G) :
    Nat.card (Outer G) = 2 := by
  have h1 := (ComponentClassification.OuterAutomorphisms.inner G).card_mul_index
  rw [card_inn h, hc, Subgroup.index_eq_card] at h1
  have : Nat.card G * Nat.card (Outer G) = Nat.card G * 2 := by rw [h1]; ring
  exact Nat.eq_of_mul_eq_mul_left hpos this

theorem suzP_center :
    Subgroup.center suzP = ⊥ := by
  have := suzP_isSimpleGroup
  exact center_eq_bot_of_simple suzP_not_comm

theorem card_out_suzP :
    Nat.card (Outer suzP) = 2 :=
  card_out_eq_two (by rw [suzP_card]; norm_num) suzP_center (by rw [card_mulAut_suzP, suzP_card])

theorem isCyclic_solvable_of_card_two {G : Type*} [Group G] (h : Nat.card G = 2) :
    IsCyclic G ∧ Group.IsSolvable G := by
  have hc : IsCyclic G := isCyclic_of_prime_card h
  refine ⟨hc, Group.isSolvable_of_comm fun a b => ?_⟩
  obtain ⟨g, hg⟩ := hc.exists_generator
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hg a)
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hg b)
  exact (Commute.zpow_zpow_self g m n).eq

noncomputable abbrev suzFieldMonoid : Monoid (Matrix (Fin 64) (Fin 64) (ZMod 3)) :=
  @Semiring.toMonoid _ (@Matrix.semiring (Fin 64) (ZMod 3)
    (@CommSemiring.toSemiring (ZMod 3) (@Semifield.toCommSemiring (ZMod 3)
      (@Field.toSemifield (ZMod 3) (@ZMod.instField 3 Nat.fact_prime_three)))) _ _)

noncomputable abbrev suzGroupStr : Group Blueprint.NativeSporadic.Suz :=
  @Units.instGroup _ (@Submonoid.toMonoid _ suzFieldMonoid
    (Blueprint.NativeSporadic.seedMonoid 3 64 1 Blueprint.NativeSporadic.SuzSeed1
      Blueprint.NativeSporadic.SuzSeed2))

theorem out_suz :
    Nat.card (@Outer Blueprint.NativeSporadic.Suz suzGroupStr) = 2 ∧
    @IsCyclic (@Outer Blueprint.NativeSporadic.Suz suzGroupStr) _ ∧
    Group.IsSolvable (@Outer Blueprint.NativeSporadic.Suz suzGroupStr) := by
  let _ : Group Blueprint.NativeSporadic.Suz := suzGroupStr
  let e : @MulEquiv Blueprint.NativeSporadic.Suz suzP (@MulOneClass.toMul _
      (@Monoid.toMulOneClass _ (@DivInvMonoid.toMonoid _ (@Group.toDivInvMonoid _ suzGroupStr))))
      _ := suzEquivP
  have hcard : Nat.card Blueprint.NativeSporadic.Suz = 448345497600 := by
    rw [Nat.card_congr e.toEquiv, suzP_card]
  have hsimple : @IsSimpleGroup Blueprint.NativeSporadic.Suz suzGroupStr := by
    have := suzP_isSimpleGroup
    exact e.isSimpleGroup
  have hcen : @Subgroup.center Blueprint.NativeSporadic.Suz suzGroupStr = ⊥ := by
    refine @center_eq_bot_of_simple Blueprint.NativeSporadic.Suz suzGroupStr hsimple ?_
    obtain ⟨a, b, hab⟩ := suzP_not_comm
    refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
    have := congrArg e h
    simpa using this
  have h2 : Nat.card (@Outer Blueprint.NativeSporadic.Suz suzGroupStr) = 2 := by
    refine @card_out_eq_two Blueprint.NativeSporadic.Suz suzGroupStr (by rw [hcard]; norm_num)
      hcen ?_
    rw [Nat.card_congr (MulAut.congr e).toEquiv, card_mulAut_suzP, hcard]
  exact ⟨h2, (isCyclic_solvable_of_card_two h2).1, (isCyclic_solvable_of_card_two h2).2⟩

theorem outer_carrier_suz :
    Nat.card (Outer (Blueprint.NativeSporadic.Carrier .Suz)) = 2 ∧
    IsCyclic (Outer (Blueprint.NativeSporadic.Carrier .Suz)) ∧
    Group.IsSolvable (Outer (Blueprint.NativeSporadic.Carrier .Suz)) :=
  out_suz

theorem CTUC_Suz_full_automorphism_permutation_model :
    suzOuter * suzOuter = 1 ∧ suzOuter ≠ 1 ∧ suzOuter ∉ suzP ∧
    suzP.map (MulAut.conj suzOuter).toMonoidHom = suzP ∧
    Function.Bijective suzConjR ∧
    (∀ (r : suzR) (p : suzP),
      ((suzConjR r p : suzP) : Equiv.Perm (Fin 22880)) = r * p * (r : Equiv.Perm (Fin 22880))⁻¹) ∧
    (suzP.subgroupOf suzR).map suzConjR = (MulAut.conj : suzP →* MulAut suzP).range ∧
    suzP ≤ suzR ∧ (suzP.subgroupOf suzR).Normal ∧
    Subgroup.zpowers suzOuter ⊓ suzP = ⊥ ∧ suzP ⊔ Subgroup.zpowers suzOuter = suzR ∧
    Nat.card suzR = 896690995200 ∧
    Nonempty (Outer suzP ≃* Multiplicative (ZMod 2)) ∧
    Nat.card (Outer Blueprint.NativeSporadic.Suz) = 2 ∧
    IsCyclic (Outer Blueprint.NativeSporadic.Suz) ∧
    Group.IsSolvable (Outer Blueprint.NativeSporadic.Suz) :=
  ⟨suzOuter_sq, suzOuter_ne_one, suzOuter_not_mem, suzOuter_conj_eq, suzConjR_bijective,
    suzConjR_apply, suzConjR_map_suzP, suzP_le_suzR, suzP_normal_R, suzR_semidirect.1,
    suzR_semidirect.2, suzR_card, ⟨mulEquivOfPrimeCardEq card_out_suzP (by simp)⟩, out_suz.1,
    out_suz.2.1, out_suz.2.2⟩

end CFSG.Sporadic.SuzOddCore
