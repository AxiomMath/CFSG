module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ4
public import CFSG.Quasithin.EmptyFaithful.S151CLJ4Tr

public section

namespace CFSG.Quasithin.J4Local

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.QuasithinUnique.Vol2Native.L239.J4Pairs
open scoped commutatorElement

theorem hj_minimal :
    ∀ D : Subgroup ↥J, D ≤ Eg uJ 11 → (∀ h ∈ Hj, ∀ d ∈ D, h * d * h⁻¹ ∈ D) →
      D = ⊥ ∨ D = Eg uJ 11 := by
  have hM := j4Facts.mat
  intro D hDE hD
  exact minimal_of_orbits (elem_uJ hM) Hj XJ act letters (fun ℓ hℓ => XJ_mem hℓ)
    (fun ℓ hℓ c => hX_all hM hℓ c) orbits orbit_words orbit_cover orbit_span D hDE hD

theorem commutator_eq_top_of_simple {Q : Type*} [Group Q] [IsSimpleGroup Q]
    (hp : ¬ (Nat.card Q).Prime) : commutator Q = ⊤ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator Q) with h | h
  · exfalso
    have hc : Subgroup.center Q = ⊤ := (commutator_eq_bot_iff_center_eq_top Q).1 h
    have : IsMulCommutative Q := Subgroup.center_eq_top_iff.1 hc
    exact hp (Group.is_simple_iff_prime_card.1 inferInstance)
  · exact h

theorem hj_perfect :
    ⁅Hj, Hj⁆ = Hj := by
  have hM := j4Facts.mat
  have hEC : Eg uJ 11 ≤ ⁅Hj, Hj⁆ := by
    have hD : ∀ h ∈ Hj, ∀ d ∈ Eg uJ 11 ⊓ ⁅Hj, Hj⁆, h * d * h⁻¹ ∈ Eg uJ 11 ⊓ ⁅Hj, Hj⁆ := by
      intro h hh d hd
      refine ⟨Hj_normalizes_Eg hM h hh d hd.1, ?_⟩
      have h1 : ⁅h, d⁆ ∈ ⁅Hj, Hj⁆ := Subgroup.commutator_mem_commutator hh (Eg_le_Hj hd.1)
      have h2 : h * d * h⁻¹ = ⁅h, d⁆ * d := by
        rw [commutatorElement_def]
        group
      rw [h2]
      exact ⁅Hj, Hj⁆.mul_mem h1 hd.2
    rcases hj_minimal (Eg uJ 11 ⊓ ⁅Hj, Hj⁆) inf_le_left hD with h0 | h0
    · exfalso
      have hcent : ∀ h ∈ Hj, ∀ y ∈ Eg uJ 11, h * y = y * h := by
        intro h hh y hy
        have hmem : ⁅h, y⁆ ∈ Eg uJ 11 ⊓ ⁅Hj, Hj⁆ := by
          refine ⟨?_, Subgroup.commutator_mem_commutator hh (Eg_le_Hj hy)⟩
          have h1 : h * y * h⁻¹ ∈ Eg uJ 11 := Hj_normalizes_Eg hM h hh y hy
          rw [commutatorElement_def]
          exact (Eg uJ 11).mul_mem h1 ((Eg uJ 11).inv_mem hy)
        rw [h0, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
        exact hmem
      have hHE : Hj ≤ Eg uJ 11 := fun h hh => centralizer_Hj hM j4Facts h hh (hcent h hh)
      have h1 := Subgroup.card_le_of_le hHE
      rw [card_Hj j4Facts, card_Eg_uJ hM] at h1
      norm_num at h1
    · rw [← h0]
      exact inf_le_right
  have hQs : IsSimpleGroup (↥Hj ⧸ (Eg uJ 11).subgroupOf Hj) := isSimpleGroup_Hj_quotient
  have hQp : commutator (↥Hj ⧸ (Eg uJ 11).subgroupOf Hj) = ⊤ := by
    refine commutator_eq_top_of_simple ?_
    rw [card_Hj_quotient]
    norm_num
  let π : ↥Hj →* ↥Hj ⧸ (Eg uJ 11).subgroupOf Hj := QuotientGroup.mk' _
  have hCsub : (commutator ↥Hj).map Hj.subtype = ⁅Hj, Hj⁆ := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
  have hπC : (commutator ↥Hj).map π = ⊤ := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top,
      MonoidHom.range_eq_top.2 (QuotientGroup.mk'_surjective _), ← commutator_def]
    exact hQp
  refine le_antisymm (Subgroup.commutator_le.2 fun a ha b hb => ?_) fun x hx => ?_
  · rw [commutatorElement_def]
    exact Hj.mul_mem (Hj.mul_mem (Hj.mul_mem ha hb) (Hj.inv_mem ha)) (Hj.inv_mem hb)
  · have hπx : π ⟨x, hx⟩ ∈ (commutator ↥Hj).map π := hπC ▸ Subgroup.mem_top _
    obtain ⟨y, hy, hyx⟩ := hπx
    have hyC : (y : ↥J) ∈ ⁅Hj, Hj⁆ := hCsub ▸ Subgroup.mem_map_of_mem Hj.subtype hy
    have hker : y⁻¹ * ⟨x, hx⟩ ∈ (Eg uJ 11).subgroupOf Hj := by
      rw [← QuotientGroup.eq_one_iff]
      change π (y⁻¹ * ⟨x, hx⟩) = 1
      rw [map_mul, map_inv, hyx, inv_mul_cancel]
    have hE : ((y⁻¹ * ⟨x, hx⟩ : ↥Hj) : ↥J) ∈ Eg uJ 11 := hker
    have h1 : x = (y : ↥J) * ((y⁻¹ * ⟨x, hx⟩ : ↥Hj) : ↥J) := by
      simp
    rw [h1]
    exact ⁅Hj, Hj⁆.mul_mem hyC (hEC hE)

theorem hj_canonical :
    CanonicalOver P0 Hj :=
  fun α hα => map_eq_of_forall_iff (Hj_forall_iff α (forall_iff_of_map_eq hα))

theorem p0_isPGroup :
    IsPGroup 2 ↥P0 := by
  have hM := j4Facts.mat
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Sylow 2 ↥J := Sylow.ofCard P0 (by rw [card_P0 hM j4Facts, card_J_factorization j4Facts])
  have hP : (P : Subgroup ↥J) = P0 := Sylow.coe_ofCard _ _
  rw [← hP]
  exact P.isPGroup'

theorem p0_index_odd :
    ¬ 2 ∣ P0.index := by
  have hM := j4Facts.mat
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Sylow 2 ↥J := Sylow.ofCard P0 (by rw [card_P0 hM j4Facts, card_J_factorization j4Facts])
  have hP : (P : Subgroup ↥J) = P0 := Sylow.coe_ofCard _ _
  rw [← hP]
  exact P.not_dvd_index

theorem eq_one_or_eq_zJ_of_mem_centerOf
    {x : ↥J} (hx : x ∈ centerOf P0) : x = 1 ∨ x = zJ := by
  have hM := j4Facts.mat
  have hx1 : x ∈ Zc 1 := by
    refine ⟨hx.1, fun y hy => ?_⟩
    have h1 : y * x = x * y := Subgroup.mem_centralizer_iff.1 hx.2 y hy
    have h2 : x * y * x⁻¹ * y⁻¹ = 1 := by
      rw [← h1]
      group
    rw [h2]
    exact rfl
  rw [Zc_eq hM j4Facts 1 (by norm_num)] at hx1
  obtain ⟨c, hc, hcx⟩ := hx1
  simp only [ucsMasks, List.getD_cons_succ, List.getD_cons_zero, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · left
    rw [hcx, eta_zero]
  · right
    exact hcx

theorem hgen_J4
    (W : Subgroup ↥J) (hW : W ≤ centerOf P0) : ¬ Subgroup.centralizer (W : Set ↥J) ≤ Hj := by
  intro hle
  obtain ⟨g, hgz, hgH⟩ := exists_centralizer_zJ_not_mem_Hj
  apply hgH
  apply hle
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  rcases eq_one_or_eq_zJ_of_mem_centerOf (hW hw) with rfl | rfl
  · simp
  · exact hgz.symm

theorem hjQuot_equiv :
    Nonempty ((↥Hj ⧸ (Eg uJ 11).subgroupOf Hj) ≃* ↥CFSG.Blueprint.NativeSporadic.M24) :=
  ⟨((QuotientGroup.quotientMulEquivOfEq ker_starHom.symm).trans
    (QuotientGroup.quotientKerEquivRange starHom)).trans
      (MulEquiv.subgroupCongr range_starHom_eq)⟩

end CFSG.Quasithin.J4Local
