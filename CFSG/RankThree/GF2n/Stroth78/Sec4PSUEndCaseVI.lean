module

public import CFSG.RankThree.GF2n.Stroth78.Sec4PSUEnd

import CFSG.GH74.Exceptional.UnitaryFourTwo
import CFSG.GroupTheory.ElemTwoDiffFour
import CFSG.RankThree.GF2n.Stroth78.Sec3Five
import CFSG.RankThree.GF2n.Stroth78.Sec4PSUEndCases
import CFSG.RankThree.GF2n.Stroth78.Sec4PSUEndCenter
import CFSG.RankThree.GF2n.Stroth78.Sec4PSUEndInv
import CFSG.RankThree.GF2n.Stroth78.Sec4PSUEndOmega
import CFSG.RankThree.GF2n.Stroth78.Sec4PSUEndRho

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open CFSG.RankThree.OrthogonalInvolutions CFSG.GroupTheory.ThreeTranspositions
open CFSG.Blueprint.Fischer CFSG.Fischer.Classification CFSG.Fischer.Classification.Unitary
open scoped Matrix commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

attribute [local instance] Xsub_normal

namespace Sec4PSUEnd

theorem rhoZ_Lbar_eq_self_of_mem_QaOf (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    {v : ↥(ZQ z)} (hv : (v : G) ∈ QaOf a) {l : Hbar z} (hl : l ∈ Lbar S a) :
    rhoZ S l v = v := by
  have hvQ : (v : G) ∈ Q z := (Subgroup.mem_inf.mp v.2).1
  have hvC : ∀ q ∈ Q z, q * (v : G) = (v : G) * q := fun q hq =>
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp v.2).2 q hq
  suffices hLa : La S a ≤ Subgroup.centralizer ({(v : G)} : Set G) by
    obtain ⟨x, hx, rfl⟩ := hl
    apply Subtype.ext
    rw [QuotientGroup.mk'_apply, rhoZ_mk]
    have hxv := Subgroup.mem_centralizer_singleton_iff.mp (hLa (Subgroup.mem_subgroupOf.mp hx))
    calc (x : G) * (v : G) * (x : G)⁻¹ = (v : G) * (x : G) * (x : G)⁻¹ := by rw [hxv]
      _ = v := by group
  refine sup_le (fun q hq => Subgroup.mem_centralizer_singleton_iff.mpr (hvC q hq)) ?_
  rintro y ⟨hyQa, hyH⟩
  obtain ⟨g, hg⟩ := isConj_iff.mp h.isConj
  have hcomm_mem : ⁅y, (v : G)⁆ ∈ Subgroup.zpowers a := by
    rw [← commutator_QaOf_eq_zpowers S hg]
    exact Subgroup.commutator_mem_commutator hyQa hv
  have hyvQ : y * (v : G) * y⁻¹ ∈ Q z := fStar_normal (M := H z) hyH hvQ
  have hyvZ : y * (v : G) * y⁻¹ ∈ ZQ z := by
    refine Subgroup.mem_inf.mpr ⟨hyvQ, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hq' : y⁻¹ * q * y ∈ Q z := by
      have := fStar_normal (M := H z) (inv_mem hyH) hq
      rwa [inv_inv] at this
    have := hvC _ hq'
    calc q * (y * (v : G) * y⁻¹) = y * ((y⁻¹ * q * y) * v) * y⁻¹ := by group
      _ = y * (v * (y⁻¹ * q * y)) * y⁻¹ := by rw [this]
      _ = y * (v : G) * y⁻¹ * q := by group
  have hcommZ : ⁅y, (v : G)⁆ ∈ ZQ z := by
    rw [commutatorElement_def]
    exact mul_mem hyvZ (inv_mem v.2)
  have ha2 : a ^ 2 = 1 := sq_eq_one_of_isConj S h.isConj
  have hcomm1 : ⁅y, (v : G)⁆ = 1 := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hcomm_mem
    obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
    · rw [← hk, zpow_mul]
      simp [ha2]
    · exfalso
      apply h.not_mem_ZQ
      have : a ^ (2 * m + 1) = a := by
        rw [zpow_add, zpow_mul]
        simp [ha2]
      rw [← this, hk]
      exact hcommZ
  exact Subgroup.mem_centralizer_singleton_iff.mpr (commutatorElement_eq_one_iff_mul_comm.mp hcomm1)

private theorem pCore_le_centralizer_of_isSimpleGroup {Y : Type*} [Group Y] {p : ℕ}
    {X : Subgroup Y} [X.Normal] (hX : IsSimpleGroup ↥X) (hXp : ¬ IsPGroup p ↥X) :
    pCore p Y ≤ Subgroup.centralizer (X : Set Y) := by
  have := hX
  have hPn : (pCore p Y).Normal := pCore_normal
  have hPX : ((pCore p Y).subgroupOf X).Normal := hPn.subgroupOf X
  have hinf : pCore p Y ⊓ X = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((pCore p Y).subgroupOf X) with hb | ht
    · exact disjoint_iff.mp (Subgroup.subgroupOf_eq_bot.mp hb)
    · exact absurd (pCore_isPGroup.to_le (Subgroup.subgroupOf_eq_top.mp ht)) hXp
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
  exact eq_bot_iff.mpr ((Subgroup.commutator_le_inf _ _).trans hinf.le)

private theorem index_inf_QaOf_le (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w) :
    ((ZQ z ⊓ QaOf a).subgroupOf (ZQ z)).index ≤ Nat.card ↥(Rbar S a) := by
  have hKcard : Nat.card ↥((ZQ z ⊓ QaOf a).subgroupOf (ZQ z)) =
      Nat.card (ZQ z ⊓ QaOf a : Subgroup G) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : ZQ z ⊓ QaOf a ≤ ZQ z)).toEquiv
  have hsubcard : Nat.card (ZQ z ⊓ QaOf a : Subgroup G) =
      Nat.card ↥((ZQ z).subgroupOf (QaOf a)) := by
    rw [← Subgroup.inf_subgroupOf_right (ZQ z) (QaOf a)]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_right : ZQ z ⊓ QaOf a ≤ QaOf a)).toEquiv).symm
  have hmul := Subgroup.card_mul_index ((ZQ z ⊓ QaOf a).subgroupOf (ZQ z))
  rw [hKcard, hsubcard, card_ZQ_eq S h, Nat.mul_comm (Nat.card ↥(Rbar S a))] at hmul
  exact (Nat.mul_left_cancel Nat.card_pos hmul).le

private theorem card_closure_commutator_eq_four (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h3 : ∀ α ∈ Eset S a, ∀ α' ∈ Eset S a, orderOf (α * α') ≤ 3)
    {α : Hbar z} (hα : α ∈ Tset S a)
    (hpsu : fischerCentralQuotientModel
      (threeResidualClass (⟨α, subset_Xsub S a (Tset_subset_Eset S a hα)⟩ : ↥(Xsub S a)))
      (fischerMatrixGroup fun A => A.det = 1 ∧
        ∀ x y, fischerHermitianF4 4 (A *ᵥ x) (A *ᵥ y) = fischerHermitianF4 4 x y)
      (fischerTransvections (fischerHermitianF4 4) fun v => v ≠ 0 ∧ fischerHermitianF4 4 v v = 0))
    (hw : w = 4) {ρ : G} (hρH : ρ ∈ H z) (hρo : orderOf ρ = 3)
    (hρP : (QuotientGroup.mk (⟨ρ, hρH⟩ : ↥(H z)) : Hbar z) ∈ pCore 3 (Hbar z)) :
    Nat.card (Subgroup.closure {y : G | ∃ x ∈ ZQ z, y = ρ * x * ρ⁻¹ * x⁻¹}) = 4 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨φ⟩ := nonempty_Xsub_mulEquiv_U2 S h h217 h3 hα hpsu (by omega)
  have hX3 : ¬ IsPGroup 3 ↥(Xsub S a) := by
    intro hp
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hp
    rw [Nat.card_congr φ.toEquiv, CFSG.GH74.Exceptional.card_U2_four] at hn
    have h2 : 2 ∣ 3 ^ n := by
      rw [← hn]
      norm_num
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2
    norm_num at this
  have hρC := pCore_le_centralizer_of_isSimpleGroup
    (isSimpleGroup_Xsub S h h217 h3 hα hpsu (by omega)) hX3 hρP
  have hρ1 : (QuotientGroup.mk (⟨ρ, hρH⟩ : ↥(H z)) : Hbar z) ≠ 1 := by
    intro h1
    have hQ : ρ ∈ Q z := Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h1)
    obtain ⟨k, hk⟩ := Q_isPGroup S ⟨ρ, hQ⟩
    have hk' : ρ ^ 2 ^ k = 1 := by
      simpa using congrArg Subtype.val hk
    have h3d : 3 ∣ 2 ^ k := by
      rw [← hρo]
      exact orderOf_dvd_of_pow_eq_one hk'
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3d
    norm_num at this
  obtain ⟨hρo', -⟩ := orderOf_eq_three_and_zpowers_eq_centralizer_Xsub S h h217 h3 hα hpsu
    (by omega) hρC hρ1
  obtain ⟨l, hl, hlρ⟩ := exists_mem_Lbar_mul_inv_eq S h h217 h3 hα hpsu (by omega) hρC hρ1
  have hcommV : ∀ x y : ↥(ZQ z), x * y = y * x := fun x y =>
    Subtype.ext (IsElemAbelian.comm (isElemAbelian_ZQ S) x.2 y.2)
  have hexpV : ∀ x : ↥(ZQ z), x * x = 1 := fun x => Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_one, ← pow_two]
    exact (isElemAbelian_ZQ S).2 _ x.2)
  have hτ3 : rhoZ S (QuotientGroup.mk (⟨ρ, hρH⟩ : ↥(H z))) ^ 3 = 1 := by
    rw [← map_pow, ← hρo', pow_orderOf_eq_one, map_one]
  have hστ : rhoZ S l * rhoZ S (QuotientGroup.mk (⟨ρ, hρH⟩ : ↥(H z))) * (rhoZ S l)⁻¹ =
      (rhoZ S (QuotientGroup.mk (⟨ρ, hρH⟩ : ↥(H z))))⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul, hlρ, map_inv]
  have h4 := CFSG.GroupTheory.card_closure_range_apply_mul_inv_eq_four hcommV hexpV hτ3
    (rhoZ_ne_one S h h217 h3 hα hpsu hw hρC hρ1) hστ
    ((index_inf_QaOf_le S h).trans (card_Rbar_eq_two S h h217 h3).le)
    (fun d hd => rhoZ_Lbar_eq_self_of_mem_QaOf S h (Subgroup.mem_subgroupOf.mp hd).2 hl)
  have hval : ∀ v : ↥(ZQ z),
      (ZQ z).subtype (rhoZ S (QuotientGroup.mk (⟨ρ, hρH⟩ : ↥(H z))) v * v⁻¹) =
        ρ * v * ρ⁻¹ * (v : G)⁻¹ := by
    intro v
    change ((rhoZ S (QuotientGroup.mk (⟨ρ, hρH⟩ : ↥(H z))) v : ↥(ZQ z)) : G) * (v : G)⁻¹ = _
    rw [rhoZ_mk]
  have hset : {y : G | ∃ x ∈ ZQ z, y = ρ * x * ρ⁻¹ * x⁻¹} = (ZQ z).subtype ''
      Set.range fun v : ↥(ZQ z) => rhoZ S (QuotientGroup.mk (⟨ρ, hρH⟩ : ↥(H z))) v * v⁻¹ := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨_, ⟨⟨x, hx⟩, rfl⟩, hval ⟨x, hx⟩⟩
    · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
      exact ⟨v, v.2, hval v⟩
  rw [hset, ← MonoidHom.map_closure,
    Subgroup.card_map_of_injective (Subgroup.subtype_injective _), h4]

theorem caseVI (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h3 : ∀ α ∈ Eset S a, ∀ α' ∈ Eset S a, orderOf (α * α') ≤ 3)
    {α : Hbar z} (hα : α ∈ Tset S a)
    (hpsu : fischerCentralQuotientModel
      (threeResidualClass (⟨α, subset_Xsub S a (Tset_subset_Eset S a hα)⟩ : ↥(Xsub S a)))
      (fischerMatrixGroup fun A => A.det = 1 ∧
        ∀ x y, fischerHermitianF4 4 (A *ᵥ x) (A *ᵥ y) = fischerHermitianF4 4 x y)
      (fischerTransvections (fischerHermitianF4 4) fun v => v ≠ 0 ∧ fischerHermitianF4 4 v v = 0))
    (hw : w = 4) {ρ : Hbar z} (hρC : ρ ∈ Subgroup.centralizer (Xsub S a : Set (Hbar z)))
    (hρ1 : ρ ≠ 1) :
    StrothCaseVI z w := by
  classical
  obtain ⟨φ⟩ := nonempty_Xsub_mulEquiv_U2 S h h217 h3 hα hpsu (by omega)
  have hZ := rhoZ_Xsub_eq_one S h h217 h3 hα hpsu
  have hcen := center_Xsub_eq_bot S h h217 h3 hα hpsu (by omega)
  obtain ⟨hρo, hρC'⟩ :=
    orderOf_eq_three_and_zpowers_eq_centralizer_Xsub S h h217 h3 hα hpsu (by omega) hρC hρ1
  obtain ⟨l, hl, hlρ⟩ := exists_mem_Lbar_mul_inv_eq S h h217 h3 hα hpsu (by omega) hρC hρ1
  have hl2 : l * l = 1 := by
    rw [← pow_two]
    exact sq_eq_one_of_mem_Lbar S h.mem_Q h.isConj hl
  have hder2 := commutator_commutator_le_of_mulEquiv_U2 φ hcen hρo hρC' hl2 hlρ
  refine ⟨hw, ⟨inferInstance, isOmegaMinusSixByThree_of_mulEquiv_U2 φ
    (commutator_Xsub S h h217 h3 hα hpsu) hcen hρo hρC' hl2 hlρ,
    fun ρ' hρ' hρ'o hρ'P => card_closure_commutator_eq_four S h h217 h3 hα hpsu hw hρ' hρ'o hρ'P⟩,
    ?_⟩
  intro x hx y hy
  let T : Subgroup ↥(H z) := ⊤
  have hT : T.map (H z).subtype = H z := by
    rw [show T = ⊤ from rfl, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hx' : x ∈ (⁅⁅T, T⁆, ⁅T, T⁆⁆ : Subgroup ↥(H z)).map (H z).subtype := by
    rw [Subgroup.map_commutator, Subgroup.map_commutator, hT]
    exact hx
  obtain ⟨x', hx'm, rfl⟩ := hx'
  have hmem : (QuotientGroup.mk x' : Hbar z) ∈ ⁅commutator (Hbar z), commutator (Hbar z)⁆ := by
    have h1 : QuotientGroup.mk' ((Q z).subgroupOf (H z)) x' ∈
        (⁅⁅T, T⁆, ⁅T, T⁆⁆ : Subgroup ↥(H z)).map (QuotientGroup.mk' ((Q z).subgroupOf (H z))) :=
      Subgroup.mem_map_of_mem _ hx'm
    rw [Subgroup.map_commutator, Subgroup.map_commutator] at h1
    rw [commutator_def]
    exact Subgroup.commutator_mono (Subgroup.commutator_mono le_top le_top)
      (Subgroup.commutator_mono le_top le_top) h1
  exact commute_of_rhoZ_mk_eq_one S (hZ _ (hder2 hmem)) hy

end Sec4PSUEnd

end CFSG.RankThree.GF2n.Stroth78
