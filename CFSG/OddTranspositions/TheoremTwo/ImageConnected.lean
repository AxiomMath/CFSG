module

public import CFSG.OddTranspositions.O4CloseReduction
import CFSG.OddTranspositions.O4PairTriple
import CFSG.OddTranspositions.PSL2InvolutionTriple
import CFSG.OddTranspositions.WreathBase
import CFSG.OddTranspositions.WreathBaseMinimal
import CFSG.OddTranspositions.WidthTwoNoProduct
public import CFSG.Fischer.Classification.WidthTwoAssembly
import CFSG.GroupTheory.PermFiveOverNormal
public import CFSG.OddTranspositions.BenderMeetsSq
public import CFSG.Timmesfeld.Bridge.Asc72ZMain

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge
open CFSG.Timmesfeld.Bridge.Asc72 CFSG.OddTranspositions.QZ

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem false_of_l2Wreath_of_localSecond (hS : Setup G D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hL : LocalSecond D) {f n : ℕ} (hf : 2 ≤ f) (hn : 2 ≤ n) (e : G ≃* L2Wreath f n) :
    False := by
  have hbase : Asc72.IsMinimalNormal (l2WreathBase f n) := by
    simpa [l2WreathBase] using base_isMinimalNormal f n hf hn
  obtain ⟨W⟩ := nonempty_wreathData hS hrad (IsMinimalNormal.comap_mulEquiv e hbase)
    (not_isSimpleGroup_comap_mulEquiv e (l2WreathBase_not_isSimpleGroup hf hn))
  exact localSecond_fails_of_wreathData hS W hL

theorem almostSimpleCase_of_disconnected
    (hS : Setup G D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hL : LocalSecond D) (hns : ¬ ∃ u ∈ D, ∃ v ∈ D, u ≠ v ∧ Commute u v ∧ u * v ∈ D)
    (hdisc : Disconnected D) : AlmostSimpleCase G D := by
  obtain ⟨H, hHtop, ⟨u, hu, huH⟩, hC⟩ := exists_subgroup_of_disconnected hS hdisc
  rcases theoremOne G D hS.isClass hS.oddT.1 hS.oddT.2 hS.gen hrad
      ⟨H, hHtop, ⟨u, hu, huH⟩, hC⟩ with hB | ⟨f, n, hf, hn, ⟨φ⟩⟩ | hAS
  · exact absurd (bender_meetsSq hB hS.isClass hS.oddT.1) hns
  · exact (false_of_l2Wreath_of_localSecond hS hrad hL hf (by omega) φ).elim
  · exact hAS

section Subpair

variable {K : Subgroup G} {Λ : Set K}

omit [Finite G] in
theorem commute_coe_iff_of_subgroup {x y : K} : Commute (x : G) (y : G) ↔ Commute x y :=
  ⟨fun h => Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul]; exact h.eq),
    fun h => h.map K.subtype⟩

omit [Finite G] in
theorem localSecond_of_coe_mem (hΛ : ∀ x ∈ Λ, (x : G) ∈ D) (hL : LocalSecond D) :
    LocalSecond Λ := by
  intro d hd x y t hx hy ht htri
  obtain ⟨hxΛ, htΛ, hyΛ, hxt, hcxt, hcxy, hcty⟩ := htri
  have h := hL d (hΛ d hd) x y t (commute_coe_iff_of_subgroup.mpr hx)
    (commute_coe_iff_of_subgroup.mpr hy) (commute_coe_iff_of_subgroup.mpr ht)
    ⟨hΛ x hxΛ, hΛ t htΛ, hΛ y hyΛ, fun h => hxt (Subtype.ext h),
      commute_coe_iff_of_subgroup.mpr hcxt, fun h => hcxy (commute_coe_iff_of_subgroup.mp h),
      fun h => hcty (commute_coe_iff_of_subgroup.mp h)⟩
  rw [← Subgroup.orderOf_coe]
  simpa using h

omit [Finite G] in
theorem widthLe_of_coe_mem (hΛ : ∀ x ∈ Λ, (x : G) ∈ D) {n : ℕ} (hW : WidthLe D n) :
    WidthLe Λ n := by
  classical
  intro S hS hcomm
  have h := hW (S.map (Function.Embedding.subtype _)) ?_ ?_
  · simpa using h
  · intro x hx
    obtain ⟨s, hs, rfl⟩ := Finset.mem_map.mp hx
    exact hΛ s (hS hs)
  · intro x hx y hy hxy
    obtain ⟨s, hs, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨t, ht, rfl⟩ := Finset.mem_map.mp hy
    exact commute_coe_iff_of_subgroup.mpr (hcomm s hs t ht fun h => hxy (by rw [h]))

end Subpair

section SimpleNormal

variable {M K : Subgroup G} [hMn : M.Normal]

omit [Finite G] in
theorem isMinimalNormal_subgroupOf (hMK : M ≤ K) (hMs : IsSimpleGroup M) :
    Asc72.IsMinimalNormal (M.subgroupOf K) := by
  refine ⟨inferInstance, ?_, fun N hN hNle => ?_⟩
  · intro h
    obtain ⟨x, hx⟩ := exists_ne (1 : M)
    have hmem : (⟨x, hMK x.2⟩ : K) ∈ M.subgroupOf K := x.2
    rw [h, Subgroup.mem_bot] at hmem
    have h1 : ((x : M) : G) = 1 := by simpa using congrArg (fun y : K => (y : G)) hmem
    exact hx (Subtype.ext h1)
  · let P : Subgroup M := (N.map K.subtype).subgroupOf M
    have hP : P.Normal := by
      refine ⟨fun p hp m => ?_⟩
      obtain ⟨n, hn, hnp⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hp)
      have hnp' : (n : G) = ((p : M) : G) := hnp
      refine Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map.mpr ⟨⟨m, hMK m.2⟩ * n *
        (⟨m, hMK m.2⟩ : K)⁻¹, hN.conj_mem n hn _, ?_⟩)
      simp [hnp']
    have := hP
    rcases hMs.eq_bot_or_eq_top_of_normal P with hbot | htop
    · left
      rw [eq_bot_iff]
      intro n hn
      have hnM : ((n : K) : G) ∈ M := Subgroup.mem_subgroupOf.mp (hNle hn)
      have hmem : (⟨(n : G), hnM⟩ : M) ∈ P :=
        Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map.mpr ⟨n, hn, rfl⟩)
      rw [hbot, Subgroup.mem_bot] at hmem
      have h1 : ((n : K) : G) = 1 := by simpa using congrArg (fun y : M => (y : G)) hmem
      exact Subgroup.mem_bot.mpr (Subtype.ext h1)
    · right
      refine le_antisymm hNle fun x hx => ?_
      have hmem : (⟨(x : G), Subgroup.mem_subgroupOf.mp hx⟩ : M) ∈ P := htop ▸ Subgroup.mem_top _
      obtain ⟨n, hn, hnx⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hmem)
      have : n = x := Subtype.ext hnx
      exact this ▸ hn

omit [Finite G] hMn in
theorem not_commute_of_centralizer_eq_bot (hC : Subgroup.centralizer (M : Set G) = ⊥)
    (hM1 : M ≠ ⊥) : ¬ ∀ a b : M, a * b = b * a := by
  intro h
  apply hM1
  rw [eq_bot_iff, ← hC]
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact congrArg Subtype.val (h ⟨y, hy⟩ ⟨x, hx⟩)

omit [Finite G] in
theorem solvable_normal_eq_bot_of_le (hMK : M ≤ K) (hMs : IsSimpleGroup M)
    (hC : Subgroup.centralizer (M : Set G) = ⊥) (hM1 : M ≠ ⊥) :
    ∀ N : Subgroup K, N.Normal → Group.IsSolvable N → N = ⊥ := by
  intro N hN hNs
  let N' : Subgroup G := N.map K.subtype
  have hN'mem : ∀ m ∈ M, ∀ x ∈ N', m * x * m⁻¹ ∈ N' := by
    intro m hm x hx
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hx
    exact Subgroup.mem_map.mpr ⟨⟨m, hMK hm⟩ * n * (⟨m, hMK hm⟩ : K)⁻¹,
      hN.conj_mem n hn _, by simp⟩
  let P : Subgroup M := N'.subgroupOf M
  have hP : P.Normal :=
    ⟨fun p hp m => Subgroup.mem_subgroupOf.mpr (by
      simpa using hN'mem m m.2 p (Subgroup.mem_subgroupOf.mp hp))⟩
  have hN's : Group.IsSolvable N' :=
    Group.isSolvable_of_isSolvable_injective
      (f := (N.equivMapOfInjective K.subtype K.subtype_injective).symm.toMonoidHom)
      (MulEquiv.injective _)
  let f : P →* N' :=
    { toFun := fun p => ⟨((p : M) : G), Subgroup.mem_subgroupOf.mp p.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hPs : Group.IsSolvable P :=
    Group.isSolvable_of_isSolvable_injective (f := f)
      (fun a b h => by
        have h' := congrArg (fun y : N' => (y : G)) h
        exact Subtype.ext (Subtype.ext h'))
  have hPbot : P = ⊥ := by
    have := hP
    rcases hMs.eq_bot_or_eq_top_of_normal P with h | h
    · exact h
    · exfalso
      have hMsolv : Group.IsSolvable M := by
        rw [h] at hPs
        exact Group.isSolvable_of_isSolvable_injective
          (f := (Subgroup.topEquiv : (⊤ : Subgroup M) ≃* M).symm.toMonoidHom)
          (MulEquiv.injective _)
      exact not_commute_of_centralizer_eq_bot hC hM1
        (IsSimpleGroup.comm_iff_isSolvable.mpr hMsolv)
  have hle : N' ≤ Subgroup.centralizer (M : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    have hcM : x * m * x⁻¹ * m⁻¹ ∈ M :=
      M.mul_mem (hMn.conj_mem m hm x) (M.inv_mem hm)
    have hcN : x * m * x⁻¹ * m⁻¹ ∈ N' := by
      have h1 := hN'mem m hm x⁻¹ (N'.inv_mem hx)
      have h2 : x * (m * x⁻¹ * m⁻¹) ∈ N' := N'.mul_mem hx h1
      simpa [mul_assoc] using h2
    have hc1 : (⟨_, hcM⟩ : M) ∈ P := Subgroup.mem_subgroupOf.mpr hcN
    rw [hPbot, Subgroup.mem_bot] at hc1
    have hc : x * m * x⁻¹ * m⁻¹ = 1 := congrArg Subtype.val hc1
    have : x * m = m * x := by
      have := mul_inv_eq_one.mp hc
      calc x * m = x * m * x⁻¹ * x := by group
        _ = m * x := by rw [this]
    exact this.symm
  rw [hC] at hle
  rw [eq_bot_iff]
  intro n hn
  have : (n : G) ∈ N' := Subgroup.mem_map.mpr ⟨n, hn, rfl⟩
  have h1 : (n : G) = 1 := Subgroup.mem_bot.mp (hle this)
  exact Subgroup.mem_bot.mpr (Subtype.ext h1)

end SimpleNormal

theorem relIndex_sup_zpowers_le_two {M : Subgroup G} [M.Normal] {u : G} (hu : u * u = 1) :
    M.relIndex (M ⊔ Subgroup.zpowers u) ≤ 2 := by
  rw [Subgroup.relIndex_sup_left]
  calc M.relIndex (Subgroup.zpowers u) ≤ Nat.card (Subgroup.zpowers u) :=
        Nat.le_of_dvd Nat.card_pos (Subgroup.relIndex_dvd_card _ _)
    _ = orderOf u := Nat.card_zpowers u
    _ ≤ 2 := orderOf_le_of_pow_eq_one (by norm_num) (by rw [pow_two]; exact hu)

omit [Finite G] in
theorem subgroupOf_sup_zpowers_eq_top {M : Subgroup G} [M.Normal] (u : G) :
    M.subgroupOf (M ⊔ Subgroup.zpowers u) ⊔
      Subgroup.zpowers (⟨u, Subgroup.mem_sup_right (Subgroup.mem_zpowers u)⟩ :
        ↥(M ⊔ Subgroup.zpowers u)) = ⊤ := by
  apply Subgroup.map_injective (M ⊔ Subgroup.zpowers u).subtype_injective
  rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, MonoidHom.map_zpowers,
    ← MonoidHom.range_eq_map, Subgroup.range_subtype, Subgroup.coe_subtype,
    inf_eq_left.mpr le_sup_left]

theorem false_of_almostSimpleCase_of_smallerTwoStar
    (hS : Setup G D) (hL : LocalSecond D) (hW : WidthLe D 2) {m : ℕ}
    (hmin : SmallerTwoStar m) (hcard : Nat.card G < m) (hAS : AlmostSimpleCase G D) :
    False := by
  classical
  obtain ⟨M, hMn, hMmin, -, hMs, hC, hindex, -, hcls⟩ := hAS
  obtain ⟨u, hu⟩ := hS.nonempty
  have hu2 : u * u = 1 := hS.oddT.mul_self_eq_one hu
  have hM1 : M ≠ ⊥ := hMmin.2.1
  have hMK : M ≤ M ⊔ Subgroup.zpowers u := le_sup_left
  have hΛD : ∀ x ∈ conjSet M u, (x : G) ∈ D := by
    rintro x ⟨m, -, hx⟩
    rw [hx]
    exact hS.normal m u hu
  obtain ⟨hΛcls, hΛodd, hΛgen⟩ := hcls u hu
  have hSΛ : Setup ↥(M ⊔ Subgroup.zpowers u) (conjSet M u) := ⟨hΛcls, hΛodd, hΛgen⟩
  have hradK := solvable_normal_eq_bot_of_le hMK hMs hC hM1
  have hLΛ : LocalSecond (conjSet M u) := localSecond_of_coe_mem hΛD hL
  have hWΛ : WidthLe (conjSet M u) 2 := widthLe_of_coe_mem hΛD hW
  have hnsΛ := not_exists_mul_mem_of_widthLe_two hWΛ fun d hd h1 => by
    have h2 := hΛodd.1 d hd
    rw [h1, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  have hM0 : Asc72.IsMinimalNormal (M.subgroupOf (M ⊔ Subgroup.zpowers u)) :=
    isMinimalNormal_subgroupOf hMK hMs
  have hidx : (M.subgroupOf (M ⊔ Subgroup.zpowers u)).index ≤ 2 :=
    relIndex_sup_zpowers_le_two hu2
  have hconn : ¬ Disconnected (conjSet M u) := by
    intro hdisc
    obtain ⟨M', -, -, huniq, -, -, hidx', -⟩ :=
      almostSimpleCase_of_disconnected hSΛ hradK hLΛ hnsΛ hdisc
    rw [← huniq _ hM0] at hidx'
    omega
  have hcardK : Nat.card ↥(M ⊔ Subgroup.zpowers u) < m :=
    (Subgroup.card_le_card_group _).trans_lt hcard
  have h3 : ∀ d ∈ conjSet M u, ∀ e ∈ conjSet M u, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ) := by
    rcases hmin _ _ hcardK hSΛ hconn hradK hLΛ with h | h
    · exact h
    · exact (not_O4PairData_of_widthLe_two h hWΛ).elim
  have hP : CFSG.Blueprint.Fischer.Pair ↥(M ⊔ Subgroup.zpowers u) (conjSet M u) :=
    ⟨inferInstance, hΛcls, hΛodd.1, h3, hΛgen⟩
  have hZ : Subgroup.center ↥(M ⊔ Subgroup.zpowers u) = ⊥ :=
    hradK _ inferInstance (Group.isSolvable_of_comm fun a b =>
      Subtype.ext (Subgroup.mem_center_iff.mp a.2 b).symm)
  have hnc := not_commute_of_centralizer_eq_bot hC hM1
  have hns : ¬ Group.IsSolvable ↥(M ⊔ Subgroup.zpowers u) := by
    intro hKs
    have : Group.IsSolvable M :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hMK)
    exact hnc (IsSimpleGroup.comm_iff_isSolvable.mpr this)
  have hM0n : (M.subgroupOf (M ⊔ Subgroup.zpowers u)).Normal := hMn.subgroupOf _
  have hcomm_le : commutator ↥(M ⊔ Subgroup.zpowers u) ≤
      M.subgroupOf (M ⊔ Subgroup.zpowers u) :=
    Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top
      (subgroupOf_sup_zpowers_eq_top u) inferInstance
  have hcomm : commutator ↥(M ⊔ Subgroup.zpowers u) =
      M.subgroupOf (M ⊔ Subgroup.zpowers u) := by
    rcases hM0.2.2 _ inferInstance hcomm_le with h | h
    · exfalso
      apply hnc
      intro a b
      have hab : (⊤ : Subgroup ↥(M ⊔ Subgroup.zpowers u)) ≤
          Subgroup.centralizer ((⊤ : Subgroup ↥(M ⊔ Subgroup.zpowers u)) :
            Set ↥(M ⊔ Subgroup.zpowers u)) := by
        rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, ← commutator_def]
        exact h
      have := Subgroup.mem_centralizer_iff.mp (hab (Subgroup.mem_top
        (⟨a, hMK a.2⟩ : ↥(M ⊔ Subgroup.zpowers u)))) ⟨b, hMK b.2⟩ (Subgroup.mem_top _)
      exact Subtype.ext (congrArg (fun y : ↥(M ⊔ Subgroup.zpowers u) => (y : G)) this.symm)
    · exact h
  have hsimple : IsSimpleGroup (commutator ↥(M ⊔ Subgroup.zpowers u)) := by
    rw [hcomm]
    exact (Subgroup.subgroupOfEquivOfLe hMK).isSimpleGroup
  obtain ⟨e, -⟩ :=
    CFSG.Fischer.Classification.width_two_fischer_pair_is_S5 hP hZ hsimple hWΛ hns
  have htop : M ⊔ Subgroup.zpowers u = ⊤ :=
    CFSG.GroupTheory.eq_top_of_mulEquiv_perm_five e hMn hMK hC
  have hle : M.index ≤ 2 := by
    rw [← Subgroup.relIndex_top_right, ← htop]
    exact relIndex_sup_zpowers_le_two hu2
  omega

theorem not_disconnected_of_smallerTwoStar
    {Y : Type} [Group Y] [Finite Y] {Θ : Set Y} (hS : Setup Y Θ)
    (hrad : ∀ N : Subgroup Y, N.Normal → Group.IsSolvable N → N = ⊥)
    (hL : LocalSecond Θ) (hW : WidthLe Θ 2) {m : ℕ} (hmin : SmallerTwoStar m)
    (hcard : Nat.card Y < m) : ¬ Disconnected Θ := by
  intro hdisc
  have hns := not_exists_mul_mem_of_widthLe_two hW fun d hd h1 => by
    have h2 := hS.oddT.1 d hd
    rw [h1, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  exact false_of_almostSimpleCase_of_smallerTwoStar hS hL hW hmin hcard
    (almostSimpleCase_of_disconnected hS hrad hL hns hdisc)

end CFSG.OddTranspositions

end
