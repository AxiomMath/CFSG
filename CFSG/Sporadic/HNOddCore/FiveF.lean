module

public import CFSG.Sporadic.HNOddCore.FiveE
public import Certificates.Certificate2085
public import Certificates.Certificate2096
public import Certificates.Certificate2097
public import Certificates.Certificate2100
public import Certificates.Certificate2102
public import Certificates.Certificate2104
public import Certificates.Certificate16041
public import Certificates.Certificate2107

public noncomputable section

namespace CFSG.Sporadic.HNOddCore

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier
open CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore.Native Equiv Equiv.Perm
open scoped commutatorElement

theorem fiveNat_formPerm : fiveNat = List.formPerm [(0 : Fin 12), 1, 2, 3, 4] := by
  unfold fiveNat
  decide

theorem fiveNat_cycle : fiveNat.IsCycle := by
  rw [fiveNat_formPerm]
  exact List.isCycle_formPerm (by decide) (by decide)

theorem fiveNat_support : fiveNat.support.card = 5 := by
  unfold fiveNat
  decide

theorem fiveNat_type : fiveNat.cycleType = {5} := by
  rw [fiveNat_cycle.cycleType, fiveNat_support]

theorem card_centralizer_five : Nat.card (Subgroup.centralizer {fiveNat}) = 25200 := by
  rw [Perm.nat_card_centralizer, fiveNat_type]
  decide

theorem card_altCentralizer_five :
    Nat.card (Subgroup.centralizer {fiveNat} ⊓ alternatingGroup (Fin 12) :
      Subgroup (Perm (Fin 12))) = 12600 :=
  card_alt_of_mem (a := 5) (b := 6) (by decide)
    (Subgroup.mem_centralizer_singleton_iff.2 (by unfold fiveNat; decide))
    (by rw [card_centralizer_five])

theorem orderOf_fiveNat : orderOf fiveNat = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact orderOf_eq_prime (by unfold fiveNat; decide) (by unfold fiveNat; decide)

theorem sub_orderOf_mk {G0 : Type*} [Group G0] {J : Subgroup G0} {V : Subgroup J} (a : J)
    (ha : a ∈ V) : orderOf (⟨a, ha⟩ : V) = orderOf a :=
  Subgroup.orderOf_mk a ha

theorem sub_orderOf_mulEquiv {G0 P : Type*} [Group G0] [Group P] {J : Subgroup G0}
    {V : Subgroup J} {Q : Subgroup P} (θ : V ≃* Q) (x : V) :
    orderOf ((θ x : Q) : P) = orderOf x := by
  rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]

theorem orderOf_fJ :
    orderOf fJ = 5 := by
  rw [← sub_orderOf_mk fJ fJ_mem, ← sub_orderOf_mulEquiv thetaJ, thetaJ_fJ]
  exact orderOf_fiveNat

abbrev CF : Subgroup JH := Subgroup.centralizer {fJ}

@[expose] def stabFH :
    MulAction.stabilizer CF x0 →* HJ :=
  (CF.subtype.comp (MulAction.stabilizer CF x0).subtype).codRestrict HJ fun s =>
    (mem_HJ_iff_fix _).2 (MulAction.mem_stabilizer_iff.1 s.2)

@[expose] def stabFHom :
    MulAction.stabilizer CF x0 →*
    ↥(Subgroup.centralizer {fiveNat} ⊓ alternatingGroup (Fin 12) : Subgroup (Perm (Fin 12))) :=
  (thetaHom.comp stabFH).codRestrict _ fun s => by
    rw [MonoidHom.comp_apply, thetaHom_apply]
    refine Subgroup.mem_inf.2 ⟨?_, (thetaJ _).2⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← thetaJ_fJ]
    have hc : ((s : CF) : JH) * fJ = fJ * (s : CF) := sub_mem_centralizer_iff.1 (s : CF).2
    have e : stabFH s * ⟨fJ, fJ_mem⟩ = ⟨fJ, fJ_mem⟩ * stabFH s := Subtype.ext hc
    have e2 := congrArg (fun h => (thetaJ h : Perm (Fin 12))) e
    simp only [map_mul, Subgroup.coe_mul] at e2
    exact e2

theorem stabFHom_injective :
    Function.Injective stabFHom := by
  intro a b h
  have e1 := Subtype.ext_iff.1 h
  have e2 : thetaJ (stabFH a) = thetaJ (stabFH b) := Subtype.ext e1
  have e3 := Subtype.ext_iff.1 (thetaJ.injective e2)
  apply Subtype.ext
  apply Subtype.ext
  exact e3

theorem card_stab_CF :
    Nat.card (MulAction.stabilizer CF x0) ≤ 12600 := by
  rw [← card_altCentralizer_five]
  exact Nat.card_le_card_of_injective _ stabFHom_injective

theorem orbit_CF_sub :
    MulAction.orbit CF x0 ⊆ Set.range omPt := by
  rintro _ ⟨c, rfl⟩
  exact mem_omega_of_comm c.2 ⟨⟨0, by norm_num⟩, x0_eq_pt0⟩

theorem card_CF_le :
    Nat.card CF ≤ 630000 := by
  have hidx := MulAction.index_stabilizer CF x0
  have hmul := (MulAction.stabilizer CF x0).card_mul_index
  have horb : (MulAction.orbit CF x0).ncard ≤ 50 := by
    calc (MulAction.orbit CF x0).ncard ≤ (Set.range omPt).ncard :=
          Set.ncard_le_ncard orbit_CF_sub (Set.toFinite _)
      _ = 50 := by
          rw [Set.ncard_range_of_injective omPt_injective, Nat.card_eq_fintype_card,
            Fintype.card_fin]
  rw [hidx] at hmul
  have hs := card_stab_CF
  rw [← hmul]
  calc Nat.card (MulAction.stabilizer CF x0) * (MulAction.orbit CF x0).ncard
      ≤ 12600 * 50 := Nat.mul_le_mul hs horb
    _ = 630000 := by norm_num

theorem fJ_mem_CF : fJ ∈ CF := (Subgroup.mem_centralizer_singleton_iff (g := fJ) (k := fJ)).2 rfl

theorem sub_comm_zpow {G0 : Type*} [Group G0] {J : Subgroup G0} {a b : J} (h : a * b = b * a)
    (k : ℤ) : a ^ k * b = b * a ^ k :=
  (Commute.zpow_left h k).eq

theorem zpowers_comm_IJ :
    ∀ a ∈ Subgroup.zpowers fJ, ∀ b ∈ IJ, a * b = b * a := by
  rintro _ ⟨k, rfl⟩ b hb
  have hbf : b * fJ = fJ * b := sub_mem_centralizer_iff.1 (IJ_le_CJ hb)
  exact sub_comm_zpow hbf.symm k

theorem zpowers_inf_IJ :
    Subgroup.zpowers fJ ⊓ IJ = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxz, hxI⟩
  rw [Subgroup.mem_bot]
  refine IJ_faithful hxI fun k => ?_
  have hf : fJ ∈ MulAction.stabilizer JH (omPt k) := (fix_fJ _).2 ⟨k, rfl⟩
  exact (Subgroup.zpowers_le.2 hf) hxz

theorem card_zpowers_fJ :
    Nat.card (Subgroup.zpowers fJ) = 5 := by
  rw [Nat.card_zpowers, orderOf_fJ]

theorem CF_eq :
    Subgroup.zpowers fJ ⊔ IJ = CF := by
  have hle : Subgroup.zpowers fJ ⊔ IJ ≤ CF :=
    sup_le (Subgroup.zpowers_le.2 fJ_mem_CF) IJ_le_CJ
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [card_sup_of_comm zpowers_comm_IJ zpowers_inf_IJ, card_zpowers_fJ, card_IJ]
  exact card_CF_le

theorem card_CF :
    Nat.card CF = 630000 := by
  rw [← CF_eq, card_sup_of_comm zpowers_comm_IJ zpowers_inf_IJ, card_zpowers_fJ, card_IJ]

theorem sub_perfect_of_simple {G : Type*} [Group G] {S : Subgroup G} (hs : IsSimpleGroup S)
    (h : ¬ (Nat.card S).Prime) : ⁅S, S⁆ = S := by
  have := hs
  have h1 := commutator_eq_top_of_simple (G := S) h
  have e := congrArg (Subgroup.map S.subtype) h1
  rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] at e
  exact e

theorem AJ_perfect :
    ⁅AJ, AJ⁆ = AJ :=
  sub_perfect_of_simple AJ_simple (by rw [card_AJ]; norm_num)

theorem commutator_central {G0 : Type*} [Group G0] {J : Subgroup G0} {z a i : J}
    (hza : z * a = a * z) : a⁻¹ * (z * i)⁻¹ * a * (z * i) = ⁅a⁻¹, i⁻¹⁆ := by
  rw [commutatorElement_def, inv_inv, inv_inv]
  calc a⁻¹ * (z * i)⁻¹ * a * (z * i) = a⁻¹ * i⁻¹ * (z⁻¹ * (a * z)) * i := by group
    _ = a⁻¹ * i⁻¹ * (z⁻¹ * (z * a)) * i := by rw [hza]
    _ = a⁻¹ * i⁻¹ * a * i := by group

theorem commJ_mem :
    commJ ∈ ⁅IJ, IJ⁆ := by
  have hg5 : g5J ∈ CF :=
    (Subgroup.mem_centralizer_singleton_iff (g := fJ) (k := g5J)).2 fJ_comm_g5.symm
  rw [← CF_eq] at hg5
  obtain ⟨z, hz, i, hi, hzi⟩ := mem_sup_of_comm zpowers_comm_IJ hg5
  have ha : aGenJ 0 ∈ IJ := AJ_le_IJ (by rw [AJ_eq]; exact Subgroup.subset_closure ⟨0, rfl⟩)
  have h1 := zpowers_comm_IJ z hz _ ha
  rw [commJ, show FAData.iCommIdx = 0 from rfl, hzi, commutator_central h1]
  exact Subgroup.commutator_mem_commutator (IJ.inv_mem ha) (IJ.inv_mem hi)

theorem IJ_perfect :
    ⁅IJ, IJ⁆ = IJ := by
  apply le_antisymm
  · exact Subgroup.commutator_le.2 fun a ha b hb =>
      IJ.mul_mem (IJ.mul_mem (IJ.mul_mem ha hb) (IJ.inv_mem ha)) (IJ.inv_mem hb)
  · conv_lhs => rw [IJ]
    rw [Subgroup.closure_le]
    rintro x (hx | hx)
    · have h := Subgroup.commutator_mono AJ_le_IJ AJ_le_IJ
      rw [AJ_perfect] at h
      exact h hx
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact commJ_mem

theorem commutator_shift {G0 : Type*} [Group G0] {J : Subgroup G0} {z1 z2 a b : J}
    (h1a : z1 * a = a * z1)
    (h1b : z1 * b = b * z1) (h12 : z1 * z2 = z2 * z1) (h2a : z2 * a = a * z2)
    (h2b : z2 * b = b * z2) : ⁅z1 * a, z2 * b⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  have h1ai : z1 * a⁻¹ = a⁻¹ * z1 := by
    rw [mul_inv_eq_iff_eq_mul, mul_assoc, h1a, ← mul_assoc, inv_mul_cancel, one_mul]
  have h2ai : z2 * a⁻¹ = a⁻¹ * z2 := by
    rw [mul_inv_eq_iff_eq_mul, mul_assoc, h2a, ← mul_assoc, inv_mul_cancel, one_mul]
  have h2bi : z2 * b⁻¹ = b⁻¹ * z2 := by
    rw [mul_inv_eq_iff_eq_mul, mul_assoc, h2b, ← mul_assoc, inv_mul_cancel, one_mul]
  calc z1 * a * (z2 * b) * (z1 * a)⁻¹ * (z2 * b)⁻¹
      = z1 * a * z2 * b * a⁻¹ * z1⁻¹ * b⁻¹ * z2⁻¹ := by group
    _ = a * (z1 * z2) * b * a⁻¹ * z1⁻¹ * b⁻¹ * z2⁻¹ := by rw [h1a]; group
    _ = a * z2 * (z1 * b) * a⁻¹ * z1⁻¹ * b⁻¹ * z2⁻¹ := by rw [h12]; group
    _ = a * z2 * b * (z1 * a⁻¹) * z1⁻¹ * b⁻¹ * z2⁻¹ := by rw [h1b]; group
    _ = a * (z2 * b) * a⁻¹ * b⁻¹ * z2⁻¹ := by rw [h1ai]; group
    _ = a * b * (z2 * a⁻¹) * b⁻¹ * z2⁻¹ := by rw [h2b]; group
    _ = a * b * a⁻¹ * (z2 * b⁻¹) * z2⁻¹ := by rw [h2ai]; group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [h2bi]; group

theorem CF_derived :
    ⁅CF, CF⁆ = IJ := by
  apply le_antisymm
  · refine Subgroup.commutator_le.2 fun x hx y hy => ?_
    rw [← CF_eq] at hx hy
    obtain ⟨z1, hz1, a, ha, rfl⟩ := mem_sup_of_comm zpowers_comm_IJ hx
    obtain ⟨z2, hz2, b, hb, rfl⟩ := mem_sup_of_comm zpowers_comm_IJ hy
    have h12 : z1 * z2 = z2 * z1 := by
      obtain ⟨k, rfl⟩ := hz1
      obtain ⟨l, rfl⟩ := hz2
      rw [← zpow_add, ← zpow_add, add_comm]
    rw [commutator_shift (zpowers_comm_IJ z1 hz1 a ha) (zpowers_comm_IJ z1 hz1 b hb) h12
      (zpowers_comm_IJ z2 hz2 a ha) (zpowers_comm_IJ z2 hz2 b hb)]
    exact IJ.mul_mem (IJ.mul_mem (IJ.mul_mem ha hb) (IJ.inv_mem ha)) (IJ.inv_mem hb)
  · have h := Subgroup.commutator_mono IJ_le_CJ IJ_le_CJ
    rwa [IJ_perfect] at h

end CFSG.Sporadic.HNOddCore
