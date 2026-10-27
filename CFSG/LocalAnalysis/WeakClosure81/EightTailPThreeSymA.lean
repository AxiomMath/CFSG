module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step211NatTot
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveGapFivePerm
public import CFSG.Timmesfeld.Bridge.Asc72Defs
public import CFSG.LocalAnalysis.WeakClosure81.FiveSixPart
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Lemma64
import CFSG.Mathlib.GroupTheory.PermCenter
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Equiv Equiv.Perm Subgroup
open CFSG.Open
open CFSG.Timmesfeld.Bridge.Asc72
open CFSG.CharacterTheory.SteinbergBY.AlternatingSix
open CFSG.ComponentClassification.AS81.Hexa

theorem w85g_totalPermHom_injective : Function.Injective totalPermHom := by
  rw [← MonoidHom.ker_eq_bot_iff]
  have hKA : totalPermHom.ker ⊓ alternatingGroup (Fin 6) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro σ hσ
    obtain ⟨hσK, hσA⟩ := Subgroup.mem_inf.mp hσ
    have h1 : totalPermAlt ⟨σ, hσA⟩ = 1 := by
      apply Subtype.ext
      rw [coe_totalPermAlt]
      exact hσK
    have h2 : (⟨σ, hσA⟩ : alternatingGroup (Fin 6)) = 1 :=
      totalPermAlt_bijective.1 (by rw [h1, map_one])
    exact Subtype.ext_iff.mp h2
  have hKsq : ∀ y ∈ totalPermHom.ker, y * y = 1 := by
    intro y hy
    have hmem : y * y ∈ totalPermHom.ker ⊓ alternatingGroup (Fin 6) := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · rw [MonoidHom.mem_ker, map_mul, MonoidHom.mem_ker.mp hy, one_mul]
      · rw [Perm.mem_alternatingGroup, map_mul]
        rcases Int.units_eq_one_or (Perm.sign y) with h | h <;> rw [h] <;> decide
    rw [hKA, Subgroup.mem_bot] at hmem
    exact hmem
  have hKcenter : totalPermHom.ker ≤ Subgroup.center (Perm (Fin 6)) := by
    intro x hx
    by_cases hx1 : x = 1
    · rw [hx1]
      exact Subgroup.one_mem _
    rw [Subgroup.mem_center_iff]
    intro y
    have hconj : y * x * y⁻¹ ∈ totalPermHom.ker :=
      (MonoidHom.normal_ker totalPermHom).conj_mem x hx y
    have hconj1 : totalPermHom (y * x * y⁻¹) = 1 := MonoidHom.mem_ker.mp hconj
    by_cases hc1 : y * x * y⁻¹ = 1
    · have hkey : y⁻¹ * (y * x * y⁻¹) * y = x := by group
      have h := congrArg (fun w => y⁻¹ * w * y) hc1
      rw [hkey] at h
      exact absurd (by simpa using h) hx1
    have hxodd : Perm.sign x = -1 := by
      rcases Int.units_eq_one_or (Perm.sign x) with h | h
      · exfalso
        have hxA : x ∈ alternatingGroup (Fin 6) := Perm.mem_alternatingGroup.mpr h
        have hmem : x ∈ totalPermHom.ker ⊓ alternatingGroup (Fin 6) :=
          Subgroup.mem_inf.mpr ⟨hx, hxA⟩
        rw [hKA, Subgroup.mem_bot] at hmem
        exact hx1 hmem
      · exact h
    have hcodd : Perm.sign (y * x * y⁻¹) = -1 := by
      rw [map_mul, map_mul, map_inv, hxodd, mul_comm (Perm.sign y) (-1), mul_assoc,
        mul_inv_cancel, mul_one]
    have heven : (x * (y * x * y⁻¹)) ∈ alternatingGroup (Fin 6) := by
      rw [Perm.mem_alternatingGroup, map_mul, hxodd, hcodd]
      decide
    have hbot : x * (y * x * y⁻¹) = 1 := by
      have hmem : x * (y * x * y⁻¹) ∈ totalPermHom.ker ⊓ alternatingGroup (Fin 6) := by
        refine Subgroup.mem_inf.mpr ⟨?_, heven⟩
        rw [MonoidHom.mem_ker, map_mul, MonoidHom.mem_ker.mp hx, hconj1]
        simp
      rw [hKA, Subgroup.mem_bot] at hmem
      exact hmem
    have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hKsq x hx)
    have hxconj : x = y * x * y⁻¹ := by
      have h1 : x = (y * x * y⁻¹)⁻¹ := mul_eq_one_iff_eq_inv.mp hbot
      conv_lhs => rw [h1]
      rw [mul_inv_rev, mul_inv_rev, hxinv, inv_inv]
      group
    conv_rhs => rw [hxconj]
    group
  have hbot : totalPermHom.ker ≤ ⊥ := by
    refine hKcenter.trans ?_
    rw [CFSG.center_perm_eq_bot_of_three_le_card (by simp)]
  exact le_antisymm hbot bot_le

noncomputable def w85g_totalPermEquiv : Perm (Fin 6) ≃* Perm (Fin 6) :=
  MulEquiv.ofBijective totalPermHom
    ⟨w85g_totalPermHom_injective,
      Finite.injective_iff_surjective.mp w85g_totalPermHom_injective⟩

def w85g_zero : Perm (Fin 6) :=
  Equiv.swap 0 1 * Equiv.swap 2 3 * Equiv.swap 4 5

theorem w85g_totalPerm_zero_swap : (totalPermHom w85g_zero).IsSwap := by
  apply Equiv.Perm.card_support_eq_two.mp
  decide +kernel

theorem w85g_zero_cycleType : w85g_zero.cycleType = Multiset.replicate 3 2 := by
  have h01 : (Equiv.swap 0 1 : Perm (Fin 6)).cycleType = {2} :=
    isSwap_iff_cycleType.mp (Equiv.Perm.swap_isSwap_iff.mpr (by decide : (0 : Fin 6) ≠ 1))
  have h23 : (Equiv.swap 2 3 : Perm (Fin 6)).cycleType = {2} :=
    isSwap_iff_cycleType.mp (Equiv.Perm.swap_isSwap_iff.mpr (by decide : (2 : Fin 6) ≠ 3))
  have h45 : (Equiv.swap 4 5 : Perm (Fin 6)).cycleType = {2} :=
    isSwap_iff_cycleType.mp (Equiv.Perm.swap_isSwap_iff.mpr (by decide : (4 : Fin 6) ≠ 5))
  have hd1 : Disjoint (Equiv.swap 0 1 : Perm (Fin 6)) (Equiv.swap 2 3) :=
    disjoint_swap_swap (by decide : ([0, 1, 2, 3] : List (Fin 6)).Nodup)
  have hd2 : Disjoint ((Equiv.swap 0 1 : Perm (Fin 6)) * Equiv.swap 2 3)
      (Equiv.swap 4 5) :=
    (disjoint_swap_swap (by decide : ([0, 1, 4, 5] : List (Fin 6)).Nodup)).mul_left
      (disjoint_swap_swap (by decide : ([2, 3, 4, 5] : List (Fin 6)).Nodup))
  rw [w85g_zero, hd2.cycleType_mul, hd1.cycleType_mul, h01, h23, h45]
  rfl

theorem w85g_totalPerm_card {z : Perm (Fin 6)} (hz : z * z = 1) (hz1 : z ≠ 1)
    (hcard : z.support.card = 6) : (totalPermHom z).IsSwap := by
  have hzord : orderOf z = 2 := orderOf_eq_prime (by rwa [pow_two]) hz1
  obtain ⟨n, hn⟩ := cycleType_prime_order (σ := z) (by rw [hzord]; norm_num)
  have hsum : (n + 1) * 2 = 6 := by
    have h := congrArg Multiset.sum hn
    rw [sum_cycleType, hcard, Multiset.sum_replicate, smul_eq_mul, hzord] at h
    exact h.symm
  have hn3 : n + 1 = 3 := by omega
  have hct : z.cycleType = w85g_zero.cycleType := by
    rw [hn, hn3, hzord, w85g_zero_cycleType]
  obtain ⟨β, hβ⟩ : ∃ β : Perm (Fin 6), β * z * β⁻¹ = w85g_zero :=
    isConj_iff.mp (isConj_iff_cycleType_eq.mpr hct)
  have hconj : totalPermHom z =
      (totalPermHom β)⁻¹ * totalPermHom w85g_zero * totalPermHom β := by
    have h := congrArg totalPermHom hβ
    rw [map_mul, map_mul, map_inv] at h
    rw [← h]
    group
  rw [hconj]
  simpa [inv_inv] using
    (b5_FiveSixPart_isSwap_conj_iff (totalPermHom β)⁻¹ (totalPermHom w85g_zero)).mp
      w85g_totalPerm_zero_swap

@[expose] def w85g_symPi {Y : Type} [Group Y] {m : ℕ}
    (e : Y ⧸ fusionOddCore Y ≃* Perm (Fin m)) : Y →* Perm (Fin m) :=
  e.toMonoidHom.comp (QuotientGroup.mk' (fusionOddCore Y))

theorem w85g_symPi_surjective {Y : Type} [Group Y] {m : ℕ}
    (e : Y ⧸ fusionOddCore Y ≃* Perm (Fin m)) : Function.Surjective (w85g_symPi e) := by
  intro σ
  obtain ⟨x, hx⟩ := e.surjective σ
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (fusionOddCore Y) x
  exact ⟨y, hx⟩

theorem w85g_sign_symPi {Y : Type} [Group Y] [Finite Y] {m : ℕ}
    (e : Y ⧸ fusionOddCore Y ≃* Perm (Fin m)) {t : Y}
    (hD : IsOddTranspClass {y : Y | IsConj t y}) (hm : 2 ≤ m) :
    Perm.sign (w85g_symPi e t) = -1 := by
  by_contra hne
  have h1 : Perm.sign (w85g_symPi e t) = 1 := by
    rcases Int.units_eq_one_or (Perm.sign (w85g_symPi e t)) with h1 | h1
    · exact h1
    · exact absurd h1 hne
  have hDsub : {y : Y | IsConj t y} ⊆ (alternatingGroup (Fin m)).comap (w85g_symPi e) := by
    intro y hy
    refine Subgroup.mem_comap.mpr ?_
    obtain ⟨u, rfl⟩ := isConj_iff.mp hy
    have h2 : w85g_symPi e (u * t * u⁻¹) =
        w85g_symPi e u * w85g_symPi e t * (w85g_symPi e u)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
    rw [mem_alternatingGroup, h2]
    simp only [map_mul, map_inv, h1]
    group
  have htop : (⊤ : Subgroup Y) ≤ (alternatingGroup (Fin m)).comap (w85g_symPi e) := by
    rw [← hD.2.2]
    exact (Subgroup.closure_le _).mpr hDsub
  have hs := w85g_symPi_surjective e
  have hall : alternatingGroup (Fin m) = ⊤ := by
    rw [eq_top_iff]
    intro σ _
    obtain ⟨y, rfl⟩ := hs σ
    exact Subgroup.mem_comap.mp (htop (Subgroup.mem_top y))
  have hcard : 1 < Fintype.card (Fin m) := by rw [Fintype.card_fin]; omega
  obtain ⟨a, c, hac⟩ := Fintype.exists_pair_of_one_lt_card (α := Fin m) hcard
  have hsa : Equiv.swap a c ∈ alternatingGroup (Fin m) := by
    rw [hall]
    exact Subgroup.mem_top _
  rw [mem_alternatingGroup, Equiv.Perm.sign_swap hac] at hsa
  exact absurd hsa (by decide)

theorem w85g_exists_equiv_isSwap {Y : Type} [Group Y] [Finite Y] {m : ℕ} (hm : 6 ≤ m)
    (e : Y ⧸ fusionOddCore Y ≃* Perm (Fin m)) {t : Y} (ht : t * t = 1)
    (hD : IsOddTranspClass {y : Y | IsConj t y}) :
    ∃ e' : Y ⧸ fusionOddCore Y ≃* Perm (Fin m), (w85g_symPi e' t).IsSwap := by
  have hz2 : w85g_symPi e t * w85g_symPi e t = 1 := by
    rw [← map_mul, ht, map_one]
  rcases Nat.lt_or_ge m 7 with hm7 | hm7
  ·
    have hm6 : m = 6 := by omega
    subst hm6
    by_cases hswap : (w85g_symPi e t).IsSwap
    · exact ⟨e, hswap⟩
    · obtain ⟨j, hoddj, hj⟩ :=
        w85g_exists_odd_card_support hz2 (w85g_sign_symPi e hD (by omega))
      have hz1 : w85g_symPi e t ≠ 1 := by
        intro h1
        have hsign := w85g_sign_symPi e hD (by omega)
        rw [h1, Perm.sign_one] at hsign
        exact absurd hsign (by decide)
      have hcard6 : (w85g_symPi e t).support.card = 6 := by
        have h2 : j ≠ 1 := by
          intro hj1
          exact hswap (Equiv.Perm.card_support_eq_two.mp (by rw [hj, hj1, mul_one]))
        obtain ⟨k, hk⟩ := hoddj
        have hle : (w85g_symPi e t).support.card ≤ 6 := by
          simpa using Finset.card_le_univ (w85g_symPi e t).support
        omega
      refine ⟨e.trans w85g_totalPermEquiv, ?_⟩
      show (w85g_totalPermEquiv (w85g_symPi e t)).IsSwap
      exact w85g_totalPerm_card hz2 hz1 hcard6
  ·
    have hswap : (w85g_symPi e t).IsSwap := by
      by_contra hns
      have hns' : ∀ i j : Fin m, i ≠ j → w85g_symPi e t ≠ Equiv.swap i j := by
        intro i j hij hh
        exact hns ⟨i, j, hij, hh⟩
      obtain ⟨σ, hσ⟩ := gap5Perm_exists_conj_orderOf_eq_six (n := m) hm7 hz2
        (w85g_sign_symPi e hD (by omega)) hns'
      obtain ⟨y, hy⟩ := w85g_symPi_surjective e σ
      have htD : t ∈ {z : Y | IsConj t z} := IsConj.refl t
      have hyD : y * t * y⁻¹ ∈ {z : Y | IsConj t z} := isConj_iff.mpr ⟨y, rfl⟩
      have hπy : w85g_symPi e (y * t * y⁻¹) = σ * w85g_symPi e t * σ⁻¹ := by
        rw [map_mul, map_mul, map_inv, hy]
      have hπw : w85g_symPi e (t * (y * t * y⁻¹)) =
          w85g_symPi e t * (σ * w85g_symPi e t * σ⁻¹) := by
        rw [map_mul, hπy]
      have h6 : 6 ∣ orderOf (t * (y * t * y⁻¹)) := by
        have h1 := orderOf_map_dvd (w85g_symPi e) (t * (y * t * y⁻¹))
        rw [hπw, hσ] at h1
        exact h1
      have h2 : 2 ∣ orderOf (t * (y * t * y⁻¹)) := dvd_trans (by decide : 2 ∣ 6) h6
      rcases hD.2.1.2 t htD (y * t * y⁻¹) hyD with hdvd | hodd
      · have h1 : 6 ∣ 2 := dvd_trans h6 hdvd
        norm_num at h1
      · exact absurd h2 hodd.not_two_dvd_nat
    exact ⟨e, hswap⟩

theorem w85g_fusionOddCore_map_mulEquiv {A B : Type} [Group A] [Finite A] [Group B]
    [Finite B] (e : A ≃* B) :
    (fusionOddCore A).map e.toMonoidHom = fusionOddCore B := by
  apply le_antisymm
  · have : ((fusionOddCore A).map e.toMonoidHom).Normal :=
      Subgroup.Normal.map inferInstance e.toMonoidHom e.surjective
    have hodd : Odd (Nat.card ((fusionOddCore A).map e.toMonoidHom)) := by
      rw [Subgroup.card_map_of_injective e.injective]
      exact CFSG.EvenSporadicStandard.Fin76b.odd_natCard_fusionOddCore A
    exact CFSG.EvenSporadicStandard.Fin76b.le_fusionOddCore hodd
  · have : ((fusionOddCore B).map e.symm.toMonoidHom).Normal :=
      Subgroup.Normal.map inferInstance e.symm.toMonoidHom e.symm.surjective
    have hodd : Odd (Nat.card ((fusionOddCore B).map e.symm.toMonoidHom)) := by
      rw [Subgroup.card_map_of_injective e.symm.injective]
      exact CFSG.EvenSporadicStandard.Fin76b.odd_natCard_fusionOddCore B
    have hle := CFSG.EvenSporadicStandard.Fin76b.le_fusionOddCore
      (N := (fusionOddCore B).map e.symm.toMonoidHom) hodd
    calc fusionOddCore B
        = ((fusionOddCore B).map e.symm.toMonoidHom).map e.toMonoidHom := by
          rw [Subgroup.map_map]
          simp
      _ ≤ (fusionOddCore A).map e.toMonoidHom := Subgroup.map_mono hle

theorem w85g_isSymGp_quot_fusionOddCore_of_mulEquiv {A B : Type} [Group A] [Finite A]
    [Group B] [Finite B] (e : A ≃* B) {m : ℕ} (h : IsSymGp (A ⧸ fusionOddCore A) m) :
    IsSymGp (B ⧸ fusionOddCore B) m := by
  obtain ⟨e'⟩ := h
  exact ⟨(QuotientGroup.congr (fusionOddCore A) (fusionOddCore B) e
    (w85g_fusionOddCore_map_mulEquiv e)).symm.trans e'⟩

theorem w85g_isSymGp_quot_fusionOddCore_of_surjective {X Y : Type} [Group X] [Finite X]
    [Group Y] [Finite Y] (ψ : X →* Y) (hψ : Function.Surjective ψ)
    (hodd : Odd (Nat.card ψ.ker)) {m : ℕ} (h : IsSymGp (Y ⧸ fusionOddCore Y) m) :
    IsSymGp (X ⧸ fusionOddCore X) m := by
  have hkerle : ψ.ker ≤ fusionOddCore X :=
    CFSG.EvenSporadicStandard.Fin76b.le_fusionOddCore hodd
  let H : Subgroup X := (fusionOddCore Y).comap ψ
  have hHnormal : H.Normal := by
    dsimp [H]; infer_instance
  have hHodd : Odd (Nat.card H) := by
    let f : ↥H →* Y := ψ.comp H.subtype
    have hrange : f.range = fusionOddCore Y := by
      dsimp [f, H]
      rw [MonoidHom.range_comp, Subgroup.range_subtype,
        Subgroup.map_comap_eq_self_of_surjective hψ]
    have hkerleH : ψ.ker ≤ H := by
      intro x hx
      exact Subgroup.mem_comap.mpr (by rw [MonoidHom.mem_ker.mp hx]; exact one_mem _)
    have hker : Nat.card f.ker = Nat.card ψ.ker := by
      have h1 : f.ker = (ψ.ker).subgroupOf H := by
        ext x
        rfl
      rw [h1]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hkerleH).toEquiv
    have hcard := Subgroup.card_ker_mul_card_range f
    rw [hrange, hker] at hcard
    rw [← hcard]
    exact hodd.mul (CFSG.EvenSporadicStandard.Fin76b.odd_natCard_fusionOddCore Y)
  have hHle : H ≤ fusionOddCore X :=
    CFSG.EvenSporadicStandard.Fin76b.le_fusionOddCore hHodd
  have hOle : fusionOddCore X ≤ H := by
    have : ((fusionOddCore X).map ψ).Normal :=
      Subgroup.Normal.map inferInstance ψ hψ
    have hodd' : Odd (Nat.card ((fusionOddCore X).map ψ)) :=
      Odd.of_dvd_nat (CFSG.EvenSporadicStandard.Fin76b.odd_natCard_fusionOddCore X)
        (Subgroup.card_map_dvd (fusionOddCore X) ψ)
    have hle := CFSG.EvenSporadicStandard.Fin76b.le_fusionOddCore
      (N := (fusionOddCore X).map ψ) hodd'
    intro x hx
    exact Subgroup.mem_comap.mpr (hle (Subgroup.mem_map_of_mem ψ hx))
  have hHeq : H = fusionOddCore X := le_antisymm hHle hOle
  let π : X →* Y ⧸ fusionOddCore Y := (QuotientGroup.mk' (fusionOddCore Y)).comp ψ
  have hπsurj : Function.Surjective π :=
    (QuotientGroup.mk'_surjective (fusionOddCore Y)).comp hψ
  have hπker : π.ker = fusionOddCore X := by
    change (QuotientGroup.mk' (fusionOddCore Y)).ker.comap ψ = fusionOddCore X
    rw [QuotientGroup.ker_mk']
    exact hHeq
  obtain ⟨e'⟩ := h
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hπker.symm).trans
    ((QuotientGroup.quotientKerEquivOfSurjective (φ := π) hπsurj).trans e')⟩

theorem w85g_conj_pow_mul_eq_inv {G : Type*} [Group G] {a b : G}
    (ha : a * a = 1) (hb : b * b = 1) (n : ℕ) :
    a * (a * b) ^ n * a⁻¹ = ((a * b) ^ n)⁻¹ := by
  have hconj : a * (a * b) * a⁻¹ = (a * b)⁻¹ := by
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right ha, inv_eq_of_mul_eq_one_right hb]
    calc a * (a * b) * a = (a * a) * (b * a) := by group
      _ = b * a := by rw [ha, one_mul]
  have h := conj_pow (a := a) (b := a * b) (i := n)
  rw [hconj, inv_pow] at h
  exact h.symm

theorem w85g_exists_conj_mem_fusionOddCore {Y : Type} [Group Y] [Finite Y] {t b : Y}
    (ht : t * t = 1) (hb : b * b = 1) (hc : t * b ∈ fusionOddCore Y) :
    ∃ o ∈ fusionOddCore Y, o * t * o⁻¹ = b := by
  have hodd : Odd (orderOf (t * b)) :=
    Odd.of_dvd_nat (CFSG.EvenSporadicStandard.Fin76b.odd_natCard_fusionOddCore Y)
      (Subgroup.orderOf_dvd_natCard (fusionOddCore Y) hc)
  obtain ⟨m, hm⟩ := hodd
  set c := t * b with hc_def
  have hcmem : c ∈ fusionOddCore Y := hc
  have hc_pow : c ^ (2 * m + 1) = 1 := hm ▸ pow_orderOf_eq_one c
  have h1 : t * c ^ (m + 1) * t⁻¹ = (c ^ (m + 1))⁻¹ := w85g_conj_pow_mul_eq_inv ht hb (m + 1)
  have h2 : t * c ^ (m + 1) = (c ^ (m + 1))⁻¹ * t := by
    calc t * c ^ (m + 1) = (t * c ^ (m + 1) * t⁻¹) * t := by group
      _ = (c ^ (m + 1))⁻¹ * t := by rw [h1]
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  refine ⟨(c ^ (m + 1))⁻¹,
    (fusionOddCore Y).inv_mem ((fusionOddCore Y).pow_mem hcmem (m + 1)), ?_⟩
  calc (c ^ (m + 1))⁻¹ * t * (c ^ (m + 1))⁻¹⁻¹
      = (c ^ (m + 1))⁻¹ * (t * c ^ (m + 1)) := by group
    _ = (c ^ (m + 1) * c ^ (m + 1))⁻¹ * t := by rw [h2, mul_inv_rev, mul_assoc]
    _ = c⁻¹ * t := by
        rw [← pow_add, show m + 1 + (m + 1) = 2 * m + 1 + 1 by ring, pow_succ, hc_pow, one_mul]
    _ = b := by rw [hc_def, mul_inv_rev, inv_mul_cancel_right, hbinv]

end CFSG.LocalAnalysis.WeakClosure81

end
