module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22uc
public import CFSG.Quasithin.Background.C2PushBlocks
public import CFSG.RankThree.PartOne.KFOUT3.KtyGen
public import CFSG.RankThree.PartOne.S12.PerfectOddPrime
public import CFSG.GroupTheory.Commutator.SubgroupOf

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise commutatorElement BigOperators

variable {G : Type} [Group G] [Finite G]

theorem barImage_injOn_calC {M K K' : Subgroup G} (hK : K ∈ calC M) (hK' : K' ∈ calC M)
    (h : barImage M K = barImage M K') : K = K' := by
  by_contra hne
  have hcomm : ⁅barImage M K, barImage M K'⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (uc22p22l_barImage_commute hK hK' hne a ha b hb).symm
  have hperf : ⁅barImage M K, barImage M K⁆ = barImage M K := by
    change ⁅(K.subgroupOf M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥M)),
        (K.subgroupOf M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥M))⁆ =
      (K.subgroupOf M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥M))
    rw [← Subgroup.map_commutator,
      CFSG.GroupTheory.commutator_subgroupOf_eq hK.1.le hK.1.le, hK.2.1]
  rw [h] at hcomm hperf
  have hbot : barImage M K = ⊥ := by
    rw [h, ← hperf, hcomm]
  obtain ⟨e, -⟩ := uc22p22l_barImage_equiv hK
  have hcard : 1 < Nat.card ↥(barImage M K) := by
    rw [← Nat.card_congr e.toEquiv]
    exact Finite.one_lt_card_iff_nontrivial.mpr
      (CFSG.LocalCores.isQuasisimple_nontrivial
        (CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hK.2.2))
  exact (Subgroup.one_lt_card_iff_ne_bot (barImage M K)).mp hcard hbot

theorem normal_of_barImage_normal {M K : Subgroup G} (hK : K ∈ calC M)
    (h : (barImage M K).Normal) : (K.subgroupOf M).Normal := by
  haveI := h
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hK.1.le]
  intro m hm
  have hKm : CFSG.Open.uniqueFourConj m K ∈ calC M :=
    uc22p22u_calC_conj Subgroup.le_normalizer hK hm
  have hconj : barImage M (CFSG.Open.uniqueFourConj m K) =
      (barImage M K).map
        (MulAut.conj (QuotientGroup.mk ⟨m⁻¹, M.inv_mem hm⟩ : Bar2 M)).toMonoidHom := by
    simpa [CFSG.Open.uniqueFourConj, CFSG.Quasithin.conjByElt, barImage,
      CFSG.Quasithin.imageOTwoQuot]
      using CFSG.Quasithin.C2Push.imageOTwoQuot_conjByElt (M := M) (X := K) (m := m⁻¹)
        (M.inv_mem hm) hK.1.le
  have hmap : (barImage M K).map
      (MulAut.conj (QuotientGroup.mk ⟨m⁻¹, M.inv_mem hm⟩ : Bar2 M)).toMonoidHom =
        barImage M K := by
    refine Subgroup.mem_normalizer_iff_map_conj_eq.mp ?_
    rw [Subgroup.normalizer_eq_top_iff.mpr h]
    exact Subgroup.mem_top _
  have hbar : barImage M (CFSG.Open.uniqueFourConj m K) = barImage M K := by
    rw [hconj, hmap]
  have heq : CFSG.Open.uniqueFourConj m K = K := barImage_injOn_calC hKm hK hbar
  have hmnorm : m⁻¹ ∈ Subgroup.normalizer (K : Set G) := by
    simpa [CFSG.Open.uniqueFourConj] using
      (Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq)
  simpa using (Subgroup.normalizer (K : Set G)).inv_mem hmnorm

private theorem normal_opp_layer (M : Subgroup G) (p : ℕ) :
    (Opp p (CFSG.layer (Bar2 M))).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have hchar : CFSG.RankThree.PartOne.conjBy g (CFSG.layer (Bar2 M)) =
      CFSG.layer (Bar2 M) := by
    simpa [CFSG.RankThree.PartOne.conjBy] using
      (Subgroup.characteristic_iff_map_eq.mp
        (CFSG.LocalCores.layer_characteristic (G := Bar2 M)) (MulAut.conj g))
  have hconj : CFSG.RankThree.PartOne.conjBy g (Opp p (CFSG.layer (Bar2 M))) =
      Opp p (CFSG.layer (Bar2 M)) := by
    change CFSG.RankThree.PartOne.conjBy g
      (CFSG.RankThree.PartOne.pElementSubgroup p (CFSG.layer (Bar2 M))) =
      CFSG.RankThree.PartOne.pElementSubgroup p (CFSG.layer (Bar2 M))
    rw [← CFSG.RankThree.PartOne.Equivariance.pElementSubgroup_conjBy p g
      (CFSG.layer (Bar2 M)), hchar]
  have hmem : g * n * g⁻¹ ∈ CFSG.RankThree.PartOne.conjBy g
      (Opp p (CFSG.layer (Bar2 M))) := by
    simpa [CFSG.RankThree.PartOne.conjBy, MulAut.conj_apply] using
      Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hn
  rwa [hconj] at hmem

theorem normal_of_barImage_eq_opp_layer {M K : Subgroup G} (hK : K ∈ calC M) {p : ℕ}
    (h : barImage M K = Opp p (CFSG.layer (Bar2 M))) : (K.subgroupOf M).Normal := by
  apply normal_of_barImage_normal hK
  rw [h]
  exact normal_opp_layer M p

theorem dvd_card_iff_dvd_card_bar2 {L : Subgroup G} {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) :
    r ∣ Nat.card L ↔ r ∣ Nat.card (Bar2 L) := by
  have hcard : Nat.card ↥L = Nat.card (Bar2 L) * Nat.card ↥(CFSG.pCore 2 ↥L) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥L)
  have hnot : ¬ r ∣ Nat.card ↥(CFSG.pCore 2 ↥L) := by
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).exists_card_eq
    rw [hk]
    intro h
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp
      (Nat.Prime.dvd_of_dvd_pow hr h))
  constructor
  · intro h
    rw [hcard] at h
    exact (Nat.Prime.dvd_mul hr).1 h |>.resolve_right hnot
  · intro h
    rw [hcard]
    exact dvd_mul_of_dvd_left h _

private theorem coprime_three_orderOf_layerMul_update {Q : Type} [Group Q] [Finite Q]
    (y : ∀ K : CFSG.LocalCores.ComponentIndex Q, K.1)
    (K₀ : CFSG.LocalCores.ComponentIndex Q)
    (h : ∀ K : CFSG.LocalCores.ComponentIndex Q, K ≠ K₀ → ¬ 3 ∣ Nat.card K.1) :
    Nat.Coprime 3 (orderOf (CFSG.LocalCores.layerMul Q (Function.update y K₀ 1))) := by
  classical
  let N : ℕ := (Finset.univ.erase K₀).prod (fun K => Nat.card K.1)
  have hN3 : ¬ 3 ∣ N := by
    intro h3
    obtain ⟨K, hKmem, hK3⟩ := (Prime.dvd_finsetProd_iff Nat.prime_three.prime _).1 h3
    exact h K (Finset.mem_erase.mp hKmem).1 hK3
  have hzN : (Function.update y K₀ 1) ^ N = 1 := by
    funext K
    by_cases hK : K = K₀
    · subst hK
      simp
    · have hdvd : Nat.card K.1 ∣ N :=
        Finset.dvd_prod_of_mem (fun K => Nat.card K.1)
          (Finset.mem_erase.mpr ⟨hK, Finset.mem_univ K⟩)
      have hord : orderOf (y K) ∣ Nat.card K.1 := by
        rw [← Subgroup.orderOf_coe (y K)]
        exact Subgroup.orderOf_dvd_natCard K.1 (y K).2
      have hpow : (y K) ^ N = 1 := orderOf_dvd_iff_pow_eq_one.mp (hord.trans hdvd)
      simpa [Function.update_of_ne hK] using hpow
  have hsN : (CFSG.LocalCores.layerMul Q (Function.update y K₀ 1)) ^ N = 1 := by
    rw [← map_pow, hzN, map_one]
  have hcop3N : Nat.Coprime 3 N := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hN3
  exact Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hsN) hcop3N

theorem mem_component_of_mem_layer_of_three_power {Q : Type} [Group Q] [Finite Q]
    {C₀ : Subgroup Q} (hC₀ : CFSG.IsComponent C₀)
    (hother : ∀ C : Subgroup Q, CFSG.IsComponent C → C ≠ C₀ → ¬ 3 ∣ Nat.card C)
    {x : Q} (hx : x ∈ CFSG.layer Q) (hx3 : ∃ j : ℕ, orderOf x = 3 ^ j) :
    x ∈ C₀ := by
  classical
  obtain ⟨j, hj⟩ := hx3
  obtain ⟨y, rfl⟩ := CFSG.LocalCores.exists_layerMul_eq hx
  let K₀ : CFSG.LocalCores.ComponentIndex Q := ⟨C₀, hC₀⟩
  let k : Q := (y K₀ : Q)
  let s : Q := CFSG.LocalCores.layerMul Q (Function.update y K₀ 1)
  have hks : k * s = CFSG.LocalCores.layerMul Q y :=
    (CFSG.LocalCores.layerMul_eq_mul_update y K₀).symm
  have hcomm : Commute k s := CFSG.LocalCores.commute_layerMul_update y K₀ (y K₀).2
  have hcop3 : Nat.Coprime 3 (orderOf s) :=
    coprime_three_orderOf_layerMul_update y K₀
      (fun K hK => hother K.1 K.2 (fun hC => hK (Subtype.ext hC)))
  have hcop : Nat.Coprime (3 ^ j) (orderOf s) := hcop3.pow_left j
  have hxpow : (k * s) ^ (3 ^ j) = 1 := by
    rw [hks, ← hj]
    exact pow_orderOf_eq_one _
  have hspow : s ^ (3 ^ j) = (k ^ (3 ^ j))⁻¹ := by
    have h1 : k ^ (3 ^ j) * s ^ (3 ^ j) = 1 := by
      rw [← hcomm.mul_pow, hxpow]
    exact eq_inv_of_mul_eq_one_right h1
  have hspow_mem : s ^ (3 ^ j) ∈ C₀ := by
    rw [hspow]
    exact C₀.inv_mem (C₀.pow_mem (y K₀).2 _)
  have hsC : s ∈ C₀ :=
    (Subgroup.zpowers_le.mpr hspow_mem) (mem_zpowers_pow_iff.mpr hcop)
  rw [← hks]
  exact C₀.mul_mem (y K₀).2 hsC

private theorem opp_mono {X Y : Subgroup G} (h : X ≤ Y) (p : ℕ) : Opp p X ≤ Opp p Y := by
  unfold Opp CFSG.RankThree.PartOne.pElementSubgroup
  exact Subgroup.closure_mono fun x hx => ⟨h hx.1, hx.2⟩

private theorem not_three_dvd_card_barImage_of_calC {M K K' : Subgroup G} (hK' : K' ∈ calC M)
    (hK'ne : K' ≠ K) (hother : ∀ K' ∈ calC M, K' ≠ K → ¬ 3 ∣ Nat.card K') :
    ¬ 3 ∣ Nat.card (barImage M K') := by
  have hnotK' : ¬ 3 ∣ Nat.card K' := hother K' hK' hK'ne
  have hcard : Nat.card ↥(K'.subgroupOf M) = Nat.card K' :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK'.1.le).toEquiv
  have hdvd : Nat.card (barImage M K') ∣ Nat.card K' := by
    have h1 : Nat.card (barImage M K') ∣ Nat.card ↥(K'.subgroupOf M) :=
      Subgroup.card_map_dvd (K'.subgroupOf M) _
    rwa [hcard] at h1
  exact fun h3 => hnotK' (h3.trans hdvd)

theorem barImage_eq_opp_three_layer {M K : Subgroup G} (hK : K ∈ calC M)
    (hother : ∀ K' ∈ calC M, K' ≠ K → ¬ 3 ∣ Nat.card K')
    (h3 : 3 ∣ Nat.card (Bar2 K ⧸ Subgroup.center (Bar2 K))) :
    barImage M K = Opp 3 (CFSG.layer (Bar2 M)) := by
  let Q := Bar2 M
  let Kbar : Subgroup Q := barImage M K
  have hKbar : CFSG.IsComponent Kbar :=
    CFSG.Quasithin.C2Push.isComponent_imageOTwoQuot_of_isSubnormal hK.1
      (CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hK.2.2)
  have h3bar : 3 ∣ Nat.card (↥Kbar ⧸ Subgroup.center ↥Kbar) := by
    obtain ⟨e, -⟩ := uc22p22l_barImage_equiv hK
    have hc : Subgroup.map (↑e) (Subgroup.center (Bar2 K)) = Subgroup.center ↥Kbar :=
      Subgroup.map_center_eq e
    let e' := QuotientGroup.congr (Subgroup.center (Bar2 K)) (Subgroup.center ↥Kbar) e hc
    rw [← Nat.card_congr e'.toEquiv]
    exact h3
  have h3Kbar : 3 ∣ Nat.card ↥Kbar :=
    h3bar.trans (Subgroup.card_quotient_dvd_card (Subgroup.center ↥Kbar))
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨z, hzpow, hzcenter⟩ :=
    CFSG.RankThree.PartOne.exists_pow_eq_one_not_mem_center_of_isPerfect
      (p := 3) (by norm_num) hKbar.1.1 h3Kbar
  have hzord : orderOf z = 3 := by
    refine orderOf_eq_prime hzpow ?_
    intro hz1
    exact hzcenter (by simpa [hz1] using Subgroup.one_mem (Subgroup.center ↥Kbar))
  have hOppKbar : Opp 3 Kbar = Kbar :=
    CFSG.RankThree.PartOne.KFOUT3.pElementSubgroup_eq_of_quasisimple hKbar.1 z.2
      (by rw [Subgroup.orderOf_coe]; exact hzord) (by simpa using hzcenter)
  have hle : Kbar ≤ Opp 3 (CFSG.layer Q) :=
    hOppKbar ▸ opp_mono (CFSG.LocalCores.component_le_layer hKbar) 3
  have hother' : ∀ C : Subgroup Q, CFSG.IsComponent C → C ≠ Kbar → ¬ 3 ∣ Nat.card C := by
    intro C hC hCne
    obtain ⟨K', hK', hK'bar⟩ := uc22p21c_exists_calC_of_component M hC
    have hK'ne : K' ≠ K := by
      intro hEq
      exact hCne (by rw [← hK'bar, hEq])
    rw [← hK'bar]
    exact not_three_dvd_card_barImage_of_calC hK' hK'ne hother
  have hge : Opp 3 (CFSG.layer Q) ≤ Kbar := by
    unfold Opp CFSG.RankThree.PartOne.pElementSubgroup
    refine (Subgroup.closure_le Kbar).mpr ?_
    rintro x ⟨hxlayer, j, hxord⟩
    exact mem_component_of_mem_layer_of_three_power hKbar hother' hxlayer ⟨j, hxord⟩
  exact le_antisymm hle hge
