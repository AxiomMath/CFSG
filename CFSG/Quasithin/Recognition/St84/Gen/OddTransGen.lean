module

import CFSG.GF2Type.Smith1980Orth.IdentArith
import CFSG.LocalAnalysis.SeitzReduction.F4PilotNonsplitSL2
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Recognition.St84.EdgeStabB
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

private theorem exists_orderOf_eq_two_pow_add_one_psl2 (n : ℕ) (hn : 1 ≤ n) :
    ∃ s : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n),
      orderOf s = 2 ^ n + 1 := by
  obtain ⟨A, hA⟩ :=
    CFSG.SeitzReduction.F4Pilot.exists_orderOf_eq_natCard_add_one (K := GaloisField 2 n)
  have hcard : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  let π : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n) →*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n) :=
    QuotientGroup.mk' (Subgroup.center
      (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)))
  have hker : MonoidHom.ker π = ⊥ := by
    rw [show π = QuotientGroup.mk' (Subgroup.center
      (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))) from rfl,
      QuotientGroup.ker_mk', CFSG.Walter.sl2_center_eq_bot_of_charTwo]
  have hinj : Function.Injective π := (MonoidHom.ker_eq_bot_iff π).mp hker
  exact ⟨π A, by rw [orderOf_injective π hinj A, hA, hcard]⟩

private theorem phi_eq_one_of_mem_zpowers_of_fixes
    {v : V} {L : Subgroup G} (h : Hyp30 Γ G) (hN : IsLocL2 Γ G v (nOf Γ v) L)
    {x : G} (hxL : x ∈ L) (hxord : orderOf (hN.phi ⟨x, hxL⟩) = 2 ^ nOf Γ v + 1)
    {a : V} (ha : Γ.Adj v a)
    {g : G} (hg : g ∈ Subgroup.zpowers x) (hga : g • a = a) :
    hN.phi ⟨g, Subgroup.zpowers_le.mpr hxL hg⟩ = 1 := by
  classical
  have hgL : g ∈ L := Subgroup.zpowers_le.mpr hxL hg
  have hmem_point : hN.phi ⟨g, hgL⟩ ∈ hN.pointBorel a :=
    Subgroup.mem_map_of_mem hN.phi (by
      rw [IsLocL2.pointSubgroup, Subgroup.mem_subgroupOf]
      exact Subgroup.mem_inf.mpr
        ⟨hgL, MulAction.mem_stabilizer_iff.mpr hga⟩)
  let xL : ↥L := ⟨x, hxL⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hg
  have hxL_eq : (⟨g, hgL⟩ : ↥L) = xL ^ k := by
    apply Subtype.ext
    rw [Subgroup.coe_zpow]
    exact hk.symm
  have hphi_eq : hN.phi ⟨g, hgL⟩ = (hN.phi xL) ^ k := by
    rw [hxL_eq, map_zpow]
  have hmem_zpow : hN.phi ⟨g, hgL⟩ ∈ Subgroup.zpowers (hN.phi xL) := by
    rw [hphi_eq]
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩
  have hdvd1 : orderOf (hN.phi ⟨g, hgL⟩) ∣ Nat.card (hN.pointBorel a) :=
    Subgroup.orderOf_dvd_natCard (hN.pointBorel a) hmem_point
  have hdvd2 : orderOf (hN.phi ⟨g, hgL⟩) ∣ 2 ^ nOf Γ v + 1 := by
    have h := orderOf_dvd_of_mem_zpowers hmem_zpow
    rwa [show orderOf (hN.phi xL) = 2 ^ nOf Γ v + 1 from hxord] at h
  have hBcard : Nat.card (hN.pointBorel a) =
      2 ^ nOf Γ v * (2 ^ nOf Γ v - 1) :=
    hN.card_pointBorel h.adj_smul (h.finite_stab v) (h.valency v).2
      (h.valency v).1 ha
  have hcopB : Nat.Coprime (Nat.card (hN.pointBorel a)) (2 ^ nOf Γ v + 1) := by
    rw [hBcard]
    have hn : 1 ≤ nOf Γ v := (h.valency v).1
    have hq : Nat.Coprime (2 ^ nOf Γ v) (2 ^ nOf Γ v + 1) := by
      rw [Nat.coprime_self_add_right]
      exact Nat.coprime_one_right _
    have hqm1 : Nat.Coprime (2 ^ nOf Γ v - 1) (2 ^ nOf Γ v + 1) := by
      have h1 : 1 ≤ 2 ^ nOf Γ v := Nat.one_le_two_pow
      rw [show 2 ^ nOf Γ v + 1 = (2 ^ nOf Γ v - 1) + 2 by omega]
      rw [Nat.coprime_self_add_right]
      exact (CFSG.GF2Type.Smith1980Orth.odd_two_pow_sub_one_of_pos hn).coprime_two_right
    exact Nat.Coprime.mul_left hq hqm1
  have hdvd : orderOf (hN.phi ⟨g, hgL⟩) ∣
      Nat.gcd (Nat.card (hN.pointBorel a)) (2 ^ nOf Γ v + 1) :=
    Nat.dvd_gcd hdvd1 hdvd2
  rw [hcopB.gcd_eq_one] at hdvd
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd)

private theorem stabilizer_zpowers_eq_bot
    {v : V} {L : Subgroup G} (h : Hyp30 Γ G) (hN : IsLocL2 Γ G v (nOf Γ v) L)
    {x : G} (hxL : x ∈ L) (hxodd : Odd (orderOf x))
    (hxord : orderOf (hN.phi ⟨x, hxL⟩) = 2 ^ nOf Γ v + 1)
    {a : V} (ha : Γ.Adj v a) :
    MulAction.stabilizer ↥(Subgroup.zpowers x) a = ⊥ := by
  classical
  rw [eq_bot_iff]
  rintro ⟨g, hg⟩ hga
  rw [Subgroup.mem_bot]
  have hga' : g • a = a := by
    simpa [MulAction.subgroup_smul_def] using MulAction.mem_stabilizer_iff.mp hga
  have hgL : g ∈ L := Subgroup.zpowers_le.mpr hxL hg
  have hphi : hN.phi ⟨g, hgL⟩ = 1 :=
    phi_eq_one_of_mem_zpowers_of_fixes h hN hxL hxord ha hg hga'
  have hgQ : g ∈ pCoreOf 2 (MulAction.stabilizer G v) :=
    (hN.phi_ker ⟨g, hgL⟩).mp hphi
  have hgodd : Odd (orderOf g) :=
    Odd.of_dvd_nat hxodd (orderOf_dvd_of_mem_zpowers hg)
  have hQp : IsPGroup 2 (pCoreOf 2 (MulAction.stabilizer G v)) := pCoreOf_isPGroup' _
  have hzP : IsPGroup 2 (Subgroup.zpowers g) :=
    hQp.to_le (Subgroup.zpowers_le.mpr hgQ)
  obtain ⟨j, hj⟩ := hzP.exists_orderOf_eq_pow ⟨g, Subgroup.mem_zpowers g⟩
  rw [Subgroup.orderOf_mk] at hj
  have hj0 : j = 0 := by
    cases j with
    | zero => rfl
    | succ j =>
      exfalso
      have heven : Even (2 ^ (j + 1)) := by
        rw [pow_succ]
        exact even_two.mul_left _
      exact (Nat.not_even_iff_odd.mpr (hj ▸ hgodd)) heven
  have horder : orderOf g = 1 := by rw [hj, hj0, pow_zero]
  exact Subtype.ext (orderOf_eq_one_iff.mp horder)

private theorem orbit_zpowers_eq_neighborSet
    {v : V} {L : Subgroup G} (h : Hyp30 Γ G) (hN : IsLocL2 Γ G v (nOf Γ v) L)
    (hLle : L ≤ MulAction.stabilizer G v)
    {x : G} (hxL : x ∈ L) (hxodd : Odd (orderOf x))
    (hxord : orderOf (hN.phi ⟨x, hxL⟩) = 2 ^ nOf Γ v + 1)
    {a : V} (ha : Γ.Adj v a) :
    MulAction.orbit ↥(Subgroup.zpowers x) a = Γ.neighborSet v := by
  classical
  let O : Set V := MulAction.orbit ↥(Subgroup.zpowers x) a
  have hOsub : O ⊆ Γ.neighborSet v := by
    rintro w ⟨g, rfl⟩
    have hgL : (g : G) ∈ L := Subgroup.zpowers_le.mpr hxL g.2
    have hgv : (g : G) • v = v := MulAction.mem_stabilizer_iff.mp (hLle hgL)
    rw [SimpleGraph.mem_neighborSet]
    have hadj := (h.adj_smul (g : G) v a).2 ha
    simpa [hgv, MulAction.subgroup_smul_def] using hadj
  have hstab_bot : MulAction.stabilizer ↥(Subgroup.zpowers x) a = ⊥ :=
    stabilizer_zpowers_eq_bot h hN hxL hxodd hxord ha
  haveI : Finite ↥(Subgroup.zpowers x) :=
    finite_of_le_stabilizer h ((Subgroup.zpowers_le.mpr hxL).trans hLle)
  haveI : Fintype ↥(Subgroup.zpowers x) := Fintype.ofFinite _
  haveI : Finite (MulAction.orbit ↥(Subgroup.zpowers x) a) :=
    Finite.of_surjective
      (fun g : ↥(Subgroup.zpowers x) =>
        (⟨g • a, MulAction.mem_orbit a g⟩ : MulAction.orbit ↥(Subgroup.zpowers x) a))
      (by
        rintro ⟨b, g, hg⟩
        exact ⟨g, Subtype.ext hg⟩)
  haveI : Fintype (MulAction.orbit ↥(Subgroup.zpowers x) a) := Fintype.ofFinite _
  haveI : Fintype (MulAction.stabilizer ↥(Subgroup.zpowers x) a) := Fintype.ofFinite _
  have hmul :=
    MulAction.card_orbit_mul_card_stabilizer_eq_card_group
      (G := ↥(Subgroup.zpowers x)) a
  have hcardOrb : Fintype.card (MulAction.orbit ↥(Subgroup.zpowers x) a) = O.ncard := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  have hstab1 : Fintype.card (MulAction.stabilizer ↥(Subgroup.zpowers x) a) = 1 := by
    rw [← Nat.card_eq_fintype_card, hstab_bot, Subgroup.card_bot]
  have hcardH : Fintype.card ↥(Subgroup.zpowers x) = orderOf x := by
    rw [← Nat.card_eq_fintype_card, Nat.card_zpowers]
  rw [hcardOrb, hstab1, hcardH] at hmul
  have hOcard : O.ncard = orderOf x := by simpa using hmul
  have hdvd : 2 ^ nOf Γ v + 1 ∣ O.ncard := by
    rw [hOcard]
    have h := orderOf_map_dvd hN.phi ⟨x, hxL⟩
    rwa [hxord, Subgroup.orderOf_mk] at h
  have hneighbor : (Γ.neighborSet v).ncard = 2 ^ nOf Γ v + 1 := by
    simpa [Nat.card_coe_set_eq] using (h.valency v).2
  have hOle : O.ncard ≤ 2 ^ nOf Γ v + 1 := by
    rw [← hneighbor]
    exact Set.ncard_le_ncard hOsub (h.finite_neighborSet v)
  have hposO : 0 < O.ncard := by
    rw [Set.ncard_pos]
    exact ⟨a, ⟨1, by simp⟩⟩
  have hOncard : O.ncard = 2 ^ nOf Γ v + 1 :=
    le_antisymm hOle (Nat.le_of_dvd hposO hdvd)
  refine Set.eq_of_subset_of_ncard_le hOsub ?_ (h.finite_neighborSet v)
  rw [hneighbor, hOncard]

theorem Hyp30.exists_odd_transitive_gen (h : Hyp30 Γ G) (v : V) :
    ∃ x ∈ MulAction.stabilizer G v, Odd (orderOf x) ∧
      ∀ a b : V, Γ.Adj v a → Γ.Adj v b → ∃ k : ℤ, x ^ k • a = b := by
  classical
  let n := nOf Γ v
  let L : Subgroup G := oTwoPrime (MulAction.stabilizer G v)
  have hN : IsLocL2 Γ G v n L := h.isLocL2_oTwoPrime v
  have hLle : L ≤ MulAction.stabilizer G v := oTwoPrime_le _
  have hn : 1 ≤ n := (h.valency v).1
  haveI : Finite ↥L := finite_of_le_stabilizer (h := h) (α := v) (H := L) hLle
  obtain ⟨s, hsord⟩ := exists_orderOf_eq_two_pow_add_one_psl2 n hn
  obtain ⟨y, hy⟩ := hN.phi_surjective s
  have hyne : orderOf y ≠ 0 := (orderOf_pos y).ne'
  obtain ⟨b, m, hm_odd, hy_eq⟩ := Nat.exists_eq_two_pow_mul_odd hyne
  let xL : ↥L := y ^ 2 ^ b
  let x : G := (xL : G)
  have hxL : x ∈ L := xL.2
  have hxL_card : orderOf xL = m := by
    rw [show xL = y ^ 2 ^ b from rfl,
      orderOf_pow_of_dvd (pow_pos (by norm_num) b).ne'
        (by rw [hy_eq]; exact dvd_mul_right _ _), hy_eq]
    exact Nat.mul_div_right m (pow_pos (by norm_num) b)
  have hxord : orderOf x = m := by
    rw [show x = (xL : G) from rfl, Subgroup.orderOf_coe, hxL_card]
  have hxodd : Odd (orderOf x) := by
    rw [hxord]
    exact hm_odd
  have hphix : hN.phi xL = s ^ 2 ^ b := by
    rw [show xL = y ^ 2 ^ b from rfl, map_pow, hy]
  have hcop : Nat.Coprime (orderOf s) (2 ^ b) := by
    rw [hsord]
    exact Nat.Coprime.pow_right b
      (CFSG.GF2Type.Smith1980Orth.odd_two_pow_add_one_of_pos hn).coprime_two_right
  have hphiord : orderOf (hN.phi xL) = 2 ^ n + 1 := by
    rw [hphix, hcop.orderOf_pow, hsord]
  have hxord_phi : orderOf (hN.phi ⟨x, hxL⟩) = 2 ^ n + 1 := by
    have hxLeq : (⟨x, hxL⟩ : ↥L) = xL := Subtype.ext rfl
    rw [hxLeq, hphiord]
  refine ⟨x, hLle hxL, hxodd, ?_⟩
  intro a b ha hb
  have hOeq := orbit_zpowers_eq_neighborSet h hN hLle hxL hxodd hxord_phi ha
  have hbO : b ∈ MulAction.orbit ↥(Subgroup.zpowers x) a := by
    rw [hOeq]
    exact (SimpleGraph.mem_neighborSet (G := Γ) v b).mpr hb
  obtain ⟨g, hga⟩ := hbO
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp g.2
  refine ⟨k, ?_⟩
  rw [hk]
  simpa [MulAction.subgroup_smul_def] using hga

end CFSG.Quasithin.St84
