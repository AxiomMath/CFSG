module

public import CFSG.RankThree.PartTwo.KFacts.KS166J2A5V
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalJ2

public section

namespace CFSG.RankThree.PartTwo.KFacts.KS166

open Subgroup CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 CFSG.ComponentClassification.J2Cover

private theorem exists_orderOf_eq_five {K : Subgroup GJ}
    (hKA : Nonempty (↥K ≃* alternatingGroup (Fin 5))) :
    ∃ y ∈ K, orderOf y = 5 := by
  obtain ⟨φ⟩ := hKA
  have hcard : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    norm_num
  have hdvd : 5 ∣ Nat.card (alternatingGroup (Fin 5)) := by
    rw [hcard]
    norm_num
  obtain ⟨τ, hτ⟩ := exists_prime_orderOf_dvd_card' (G := alternatingGroup (Fin 5)) 5 hdvd
  refine ⟨((φ.symm τ : ↥K) : GJ), (φ.symm τ).2, ?_⟩
  rw [Subgroup.orderOf_coe]
  calc orderOf (φ.symm τ) = orderOf (φ (φ.symm τ)) :=
        (MulEquiv.orderOf_eq φ (φ.symm τ)).symm
    _ = orderOf τ := by rw [φ.apply_symm_apply]
    _ = 5 := hτ

private theorem exists_odd_part {K : Subgroup GJ}
    {r : Equiv.Perm (Fin 315)} (hr : r ∈ R) (hrNotP : r ∉ P)
    (hrK : ∀ k ∈ K, r * (k : Equiv.Perm (Fin 315)) =
      (k : Equiv.Perm (Fin 315)) * r) :
    ∃ s : Equiv.Perm (Fin 315),
      s ∈ R ∧ s ∉ P ∧
        (∀ k ∈ K, s * (k : Equiv.Perm (Fin 315)) =
          (k : Equiv.Perm (Fin 315)) * s) ∧
        s ^ 2 ∈ P ∧ s ^ 2 ^ 8 = 1 := by
  classical
  let rR : R := ⟨r, hr⟩
  have hne : orderOf rR ≠ 0 := by
    intro h
    have hdvd : orderOf rR ∣ Nat.card R := by
      rw [← Subgroup.orderOf_coe]
      exact Subgroup.orderOf_dvd_natCard R hr
    rw [h, card_R] at hdvd
    exact absurd (Nat.zero_dvd.mp hdvd) (by norm_num)
  obtain ⟨a, m, hm, hord⟩ := Nat.exists_eq_two_pow_mul_odd hne
  let sR : R := rR ^ m
  have hidx : (P.subgroupOf R).index = 2 := by
    have h := Subgroup.card_mul_index (P.subgroupOf R)
    have hcard : Nat.card (P.subgroupOf R) = Nat.card P :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe P_le_R).toEquiv
    rw [hcard, card_P, card_R] at h
    omega
  have hrNotH : rR ∉ P.subgroupOf R := fun h => hrNotP h
  have hsNotH : sR ∉ P.subgroupOf R := by
    intro h
    apply hrNotH
    have hpow : (rR ^ 2) ^ (m / 2) ∈ P.subgroupOf R :=
      (P.subgroupOf R).pow_mem (Subgroup.sq_mem_of_index_two hidx rR) _
    have hm' : m = 2 * (m / 2) + 1 := by
      have h := Nat.div_two_mul_two_add_one_of_odd hm
      omega
    have hs_eq : sR = (rR ^ 2) ^ (m / 2) * rR := by
      dsimp only [sR]
      conv_lhs => rw [hm']
      rw [pow_add, pow_one, pow_mul]
    rw [hs_eq] at h
    have h' := (P.subgroupOf R).mul_mem ((P.subgroupOf R).inv_mem hpow) h
    rw [show ((rR ^ 2) ^ (m / 2))⁻¹ * ((rR ^ 2) ^ (m / 2) * rR) = rR by group] at h'
    exact h'
  have hsComm : ∀ k ∈ K, (sR : Equiv.Perm (Fin 315)) *
      (k : Equiv.Perm (Fin 315)) = (k : Equiv.Perm (Fin 315)) *
        (sR : Equiv.Perm (Fin 315)) := by
    intro k hk
    have hcomm : Commute (rR : Equiv.Perm (Fin 315)) (k : Equiv.Perm (Fin 315)) :=
      hrK k hk
    have := hcomm.pow_left m
    simpa [sR] using this.eq
  have hs_pow : sR ^ 2 ^ a = 1 := by
    show (rR ^ m) ^ 2 ^ a = 1
    rw [← pow_mul]
    rw [show m * 2 ^ a = orderOf rR by rw [hord, Nat.mul_comm]]
    exact pow_orderOf_eq_one rR
  have hsqP : (sR : Equiv.Perm (Fin 315)) ^ 2 ∈ P := by
    have h := Subgroup.sq_mem_of_index_two hidx sR
    rw [Subgroup.mem_subgroupOf] at h
    simpa using h
  exact ⟨(sR : Equiv.Perm (Fin 315)), sR.2, fun h => hsNotH (Subgroup.mem_subgroupOf.mpr h),
    hsComm, hsqP, pow256_R (r := sR) ⟨a, hs_pow⟩⟩

private theorem conj_mem_VJ
    {s : Equiv.Perm (Fin 315)} {u : GJ}
    (hsR : s ∈ R) (hu : u ∈ VJ)
    (hsx : s * (xJ : Equiv.Perm (Fin 315)) = (xJ : Equiv.Perm (Fin 315)) * s) :
    ∃ a : GJ, a ∈ VJ ∧
      (a : Equiv.Perm (Fin 315)) = s * (u : Equiv.Perm (Fin 315)) * s⁻¹ := by
  have hsN : s ∈ Subgroup.normalizer (P : Set (Equiv.Perm (Fin 315))) := R_le_normalizer hsR
  have husP : s * (u : Equiv.Perm (Fin 315)) * s⁻¹ ∈ P :=
    (Subgroup.mem_normalizer_iff.mp hsN (u : Equiv.Perm (Fin 315))).mp u.2
  let a : GJ := ⟨s * (u : Equiv.Perm (Fin 315)) * s⁻¹, husP⟩
  have ha_coe : (a : Equiv.Perm (Fin 315)) =
      s * (u : Equiv.Perm (Fin 315)) * s⁻¹ := rfl
  have hux : (u : Equiv.Perm (Fin 315)) * (xJ : Equiv.Perm (Fin 315)) =
      (xJ : Equiv.Perm (Fin 315)) * (u : Equiv.Perm (Fin 315)) :=
    congrArg Subtype.val (mem_centralizer_singleton_iff.mp (V_le_C hu))
  have haC : a ∈ centralizer ({xJ} : Set GJ) := by
    rw [mem_centralizer_singleton_iff]
    apply Subtype.ext
    change (a : Equiv.Perm (Fin 315)) * (xJ : Equiv.Perm (Fin 315)) =
      (xJ : Equiv.Perm (Fin 315)) * (a : Equiv.Perm (Fin 315))
    rw [ha_coe]
    have hsx' : s⁻¹ * (xJ : Equiv.Perm (Fin 315)) =
        (xJ : Equiv.Perm (Fin 315)) * s⁻¹ := by
      calc s⁻¹ * (xJ : Equiv.Perm (Fin 315))
          = s⁻¹ * ((xJ : Equiv.Perm (Fin 315)) * s) * s⁻¹ := by group
        _ = s⁻¹ * (s * (xJ : Equiv.Perm (Fin 315))) * s⁻¹ := by rw [← hsx]
        _ = (xJ : Equiv.Perm (Fin 315)) * s⁻¹ := by group
    calc s * (u : Equiv.Perm (Fin 315)) * s⁻¹ * (xJ : Equiv.Perm (Fin 315))
        = s * (u : Equiv.Perm (Fin 315)) * (s⁻¹ * (xJ : Equiv.Perm (Fin 315))) := by
          group
      _ = s * (u : Equiv.Perm (Fin 315)) * ((xJ : Equiv.Perm (Fin 315)) * s⁻¹) := by
          rw [hsx']
      _ = s * ((u : Equiv.Perm (Fin 315)) * (xJ : Equiv.Perm (Fin 315))) * s⁻¹ := by
          group
      _ = s * ((xJ : Equiv.Perm (Fin 315)) * (u : Equiv.Perm (Fin 315))) * s⁻¹ := by
          rw [hux]
      _ = (s * (xJ : Equiv.Perm (Fin 315))) * (u : Equiv.Perm (Fin 315)) * s⁻¹ := by
          group
      _ = ((xJ : Equiv.Perm (Fin 315)) * s) * (u : Equiv.Perm (Fin 315)) * s⁻¹ := by
          rw [hsx]
      _ = (xJ : Equiv.Perm (Fin 315)) *
          (s * (u : Equiv.Perm (Fin 315)) * s⁻¹) := by group
  have ha2 : a ^ 2 ^ 7 = 1 := by
    apply Subtype.ext
    change (s * (u : Equiv.Perm (Fin 315)) * s⁻¹) ^ 2 ^ 7 = 1
    have huu : (u : Equiv.Perm (Fin 315)) * (u : Equiv.Perm (Fin 315)) = 1 := by
      simpa using congrArg Subtype.val (mul_self_of_mem_kleinSub hu)
    have hsq : (s * (u : Equiv.Perm (Fin 315)) * s⁻¹) ^ 2 = 1 := by
      rw [pow_two,
        show s * (u : Equiv.Perm (Fin 315)) * s⁻¹ *
            (s * (u : Equiv.Perm (Fin 315)) * s⁻¹) =
          s * ((u : Equiv.Perm (Fin 315)) * (u : Equiv.Perm (Fin 315))) * s⁻¹ by group,
        huu, mul_one, mul_inv_cancel]
    rw [show 2 ^ 7 = 2 * 2 ^ 6 by norm_num, pow_mul, hsq, one_pow]
  exact ⟨a, mem_V_of_two haC ha2, ha_coe⟩

private theorem exists_mem_VJ_decomposition
    {K : Subgroup GJ} {s : Equiv.Perm (Fin 315)}
    (hsR : s ∈ R) (hsNotP : s ∉ P)
    (hsComm : ∀ k ∈ K, s * (k : Equiv.Perm (Fin 315)) =
      (k : Equiv.Perm (Fin 315)) * s)
    (hKz : K ≤ centralizer ({zJ} : Set GJ))
    (hcent : ∀ u ∈ VJ, s * (u : Equiv.Perm (Fin 315)) * s⁻¹ =
      (u : Equiv.Perm (Fin 315)))
    (hCV : centralizer (K : Set GJ) ⊓ centralizer (VJ : Set GJ) = VJ) :
    ∃ t ∈ VJ,
      s = ((zJ : Equiv.Perm (Fin 315)) * s * (zJ : Equiv.Perm (Fin 315))⁻¹) *
        (t : Equiv.Perm (Fin 315)) ∧
      (t : Equiv.Perm (Fin 315)) *
          ((zJ : Equiv.Perm (Fin 315)) * s * (zJ : Equiv.Perm (Fin 315))⁻¹) =
        ((zJ : Equiv.Perm (Fin 315)) * s * (zJ : Equiv.Perm (Fin 315))⁻¹) *
          (t : Equiv.Perm (Fin 315)) := by
  let s' : Equiv.Perm (Fin 315) :=
    (zJ : Equiv.Perm (Fin 315)) * s * (zJ : Equiv.Perm (Fin 315))⁻¹
  have hs'R : s' ∈ R := by
    have hzR : (zJ : Equiv.Perm (Fin 315)) ∈ R := P_le_R zJ.2
    exact R.mul_mem (R.mul_mem hzR hsR) (R.inv_mem hzR)
  have hs'NotP : s' ∉ P := by
    intro h
    apply hsNotP
    have hzP : (zJ : Equiv.Perm (Fin 315)) ∈ P := zJ.2
    have hmem : (zJ : Equiv.Perm (Fin 315))⁻¹ * s' *
        (zJ : Equiv.Perm (Fin 315)) ∈ P :=
      P.mul_mem (P.mul_mem (P.inv_mem hzP) h) hzP
    rwa [show (zJ : Equiv.Perm (Fin 315))⁻¹ * s' *
      (zJ : Equiv.Perm (Fin 315)) = s by dsimp [s']; group] at hmem
  have hs'Comm : ∀ k ∈ K, s' * (k : Equiv.Perm (Fin 315)) =
      (k : Equiv.Perm (Fin 315)) * s' := by
    intro k hk
    have hzk : Commute (zJ : Equiv.Perm (Fin 315)) (k : Equiv.Perm (Fin 315)) := by
      have h := congrArg Subtype.val (mem_centralizer_singleton_iff.mp (hKz hk))
      exact h.symm
    have hz'k : (zJ : Equiv.Perm (Fin 315))⁻¹ * (k : Equiv.Perm (Fin 315)) =
        (k : Equiv.Perm (Fin 315)) * (zJ : Equiv.Perm (Fin 315))⁻¹ := by
      calc (zJ : Equiv.Perm (Fin 315))⁻¹ * (k : Equiv.Perm (Fin 315))
          = (zJ : Equiv.Perm (Fin 315))⁻¹ *
              ((k : Equiv.Perm (Fin 315)) * (zJ : Equiv.Perm (Fin 315))) *
              (zJ : Equiv.Perm (Fin 315))⁻¹ := by group
        _ = (zJ : Equiv.Perm (Fin 315))⁻¹ *
              ((zJ : Equiv.Perm (Fin 315)) * (k : Equiv.Perm (Fin 315))) *
              (zJ : Equiv.Perm (Fin 315))⁻¹ := by rw [← hzk.eq]
        _ = (k : Equiv.Perm (Fin 315)) * (zJ : Equiv.Perm (Fin 315))⁻¹ := by group
    have hsk : Commute s (k : Equiv.Perm (Fin 315)) := hsComm k hk
    calc s' * (k : Equiv.Perm (Fin 315))
        = (zJ : Equiv.Perm (Fin 315)) * s *
            ((zJ : Equiv.Perm (Fin 315))⁻¹ * (k : Equiv.Perm (Fin 315))) := by
          dsimp [s']; group
      _ = (zJ : Equiv.Perm (Fin 315)) * s *
            ((k : Equiv.Perm (Fin 315)) * (zJ : Equiv.Perm (Fin 315))⁻¹) := by rw [hz'k]
      _ = (zJ : Equiv.Perm (Fin 315)) * (s * (k : Equiv.Perm (Fin 315))) *
            (zJ : Equiv.Perm (Fin 315))⁻¹ := by group
      _ = (zJ : Equiv.Perm (Fin 315)) * ((k : Equiv.Perm (Fin 315)) * s) *
            (zJ : Equiv.Perm (Fin 315))⁻¹ := by rw [hsk.eq]
      _ = ((zJ : Equiv.Perm (Fin 315)) * (k : Equiv.Perm (Fin 315))) * s *
            (zJ : Equiv.Perm (Fin 315))⁻¹ := by group
      _ = ((k : Equiv.Perm (Fin 315)) * (zJ : Equiv.Perm (Fin 315))) * s *
            (zJ : Equiv.Perm (Fin 315))⁻¹ := by rw [hzk.eq]
      _ = (k : Equiv.Perm (Fin 315)) * s' := by dsimp [s']; group
  have hs'Cent : ∀ u ∈ VJ, s' * (u : Equiv.Perm (Fin 315)) * s'⁻¹ =
      (u : Equiv.Perm (Fin 315)) := by
    intro u hu
    have hzInv : (zJ : GJ)⁻¹ ∈ normalizer (VJ : Set GJ) :=
      (normalizer (VJ : Set GJ)).inv_mem zJ_mem_normalizer_VJ
    have hvV : (zJ : GJ)⁻¹ * u * (zJ : GJ) ∈ VJ :=
      (Subgroup.mem_normalizer_iff.mp hzInv u).mp hu
    have hsv : s * (((zJ : GJ)⁻¹ * u * (zJ : GJ) : GJ) : Equiv.Perm (Fin 315)) * s⁻¹ =
        (((zJ : GJ)⁻¹ * u * (zJ : GJ) : GJ) : Equiv.Perm (Fin 315)) := hcent _ hvV
    dsimp [s']
    calc (zJ : Equiv.Perm (Fin 315)) * s * (zJ : Equiv.Perm (Fin 315))⁻¹ *
          (u : Equiv.Perm (Fin 315)) *
          ((zJ : Equiv.Perm (Fin 315)) * s * (zJ : Equiv.Perm (Fin 315))⁻¹)⁻¹
        = (zJ : Equiv.Perm (Fin 315)) *
            (s * (((zJ : GJ)⁻¹ * u * (zJ : GJ) : GJ) : Equiv.Perm (Fin 315)) * s⁻¹) *
            (zJ : Equiv.Perm (Fin 315))⁻¹ := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
      _ = (zJ : Equiv.Perm (Fin 315)) *
            (((zJ : GJ)⁻¹ * u * (zJ : GJ) : GJ) : Equiv.Perm (Fin 315)) *
            (zJ : Equiv.Perm (Fin 315))⁻¹ := by rw [hsv]
      _ = (u : Equiv.Perm (Fin 315)) := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
  have htP : s'⁻¹ * s ∈ P := by
    have hs_cos : permU⁻¹ * s ∈ P := (mem_P_or_coset hsR).resolve_left hsNotP
    have hs'_cos : permU⁻¹ * s' ∈ P := (mem_P_or_coset hs'R).resolve_left hs'NotP
    have h := P.mul_mem (P.inv_mem hs'_cos) hs_cos
    rwa [show (permU⁻¹ * s')⁻¹ * (permU⁻¹ * s) = s'⁻¹ * s by group] at h
  let t : GJ := ⟨s'⁻¹ * s, htP⟩
  have ht_coe : (t : Equiv.Perm (Fin 315)) = s'⁻¹ * s := rfl
  have htK : t ∈ centralizer (K : Set GJ) := by
    rw [mem_centralizer_iff]
    intro k hk
    apply Subtype.ext
    change (k : Equiv.Perm (Fin 315)) * (t : Equiv.Perm (Fin 315)) =
      (t : Equiv.Perm (Fin 315)) * (k : Equiv.Perm (Fin 315))
    rw [ht_coe]
    have hsk : s * (k : Equiv.Perm (Fin 315)) = (k : Equiv.Perm (Fin 315)) * s :=
      hsComm k hk
    have hs'k : s' * (k : Equiv.Perm (Fin 315)) = (k : Equiv.Perm (Fin 315)) * s' :=
      hs'Comm k hk
    have hs'k_inv : (s'⁻¹) * (k : Equiv.Perm (Fin 315)) =
        (k : Equiv.Perm (Fin 315)) * (s'⁻¹) := by
      calc (s'⁻¹) * (k : Equiv.Perm (Fin 315))
          = (s'⁻¹) * ((k : Equiv.Perm (Fin 315)) * s') * s'⁻¹ := by group
        _ = (s'⁻¹) * (s' * (k : Equiv.Perm (Fin 315))) * s'⁻¹ := by rw [← hs'k]
        _ = (k : Equiv.Perm (Fin 315)) * (s'⁻¹) := by group
    calc (k : Equiv.Perm (Fin 315)) * (s'⁻¹ * s)
        = ((k : Equiv.Perm (Fin 315)) * s'⁻¹) * s := by group
      _ = ((s'⁻¹) * (k : Equiv.Perm (Fin 315))) * s := by rw [hs'k_inv]
      _ = (s'⁻¹) * ((k : Equiv.Perm (Fin 315)) * s) := by group
      _ = (s'⁻¹) * (s * (k : Equiv.Perm (Fin 315))) := by rw [hsk]
      _ = (s'⁻¹ * s) * (k : Equiv.Perm (Fin 315)) := by group
  have htV : t ∈ centralizer (VJ : Set GJ) := by
    rw [mem_centralizer_iff]
    intro u hu
    apply Subtype.ext
    change (u : Equiv.Perm (Fin 315)) * (t : Equiv.Perm (Fin 315)) =
      (t : Equiv.Perm (Fin 315)) * (u : Equiv.Perm (Fin 315))
    rw [ht_coe]
    have hsu : s * (u : Equiv.Perm (Fin 315)) = (u : Equiv.Perm (Fin 315)) * s := by
      have h := hcent u hu
      calc s * (u : Equiv.Perm (Fin 315))
          = (s * (u : Equiv.Perm (Fin 315)) * s⁻¹) * s := by group
        _ = (u : Equiv.Perm (Fin 315)) * s := by rw [h]
    have hs'u : s' * (u : Equiv.Perm (Fin 315)) = (u : Equiv.Perm (Fin 315)) * s' := by
      have h := hs'Cent u hu
      calc s' * (u : Equiv.Perm (Fin 315))
          = (s' * (u : Equiv.Perm (Fin 315)) * s'⁻¹) * s' := by group
        _ = (u : Equiv.Perm (Fin 315)) * s' := by rw [h]
    have hs'u_inv : (s'⁻¹) * (u : Equiv.Perm (Fin 315)) =
        (u : Equiv.Perm (Fin 315)) * (s'⁻¹) := by
      calc (s'⁻¹) * (u : Equiv.Perm (Fin 315))
          = (s'⁻¹) * ((u : Equiv.Perm (Fin 315)) * s') * s'⁻¹ := by group
        _ = (s'⁻¹) * (s' * (u : Equiv.Perm (Fin 315))) * s'⁻¹ := by rw [← hs'u]
        _ = (u : Equiv.Perm (Fin 315)) * (s'⁻¹) := by group
    calc (u : Equiv.Perm (Fin 315)) * (s'⁻¹ * s)
        = ((u : Equiv.Perm (Fin 315)) * s'⁻¹) * s := by group
      _ = ((s'⁻¹) * (u : Equiv.Perm (Fin 315))) * s := by rw [hs'u_inv]
      _ = (s'⁻¹) * ((u : Equiv.Perm (Fin 315)) * s) := by group
      _ = (s'⁻¹) * (s * (u : Equiv.Perm (Fin 315))) := by rw [hsu]
      _ = (s'⁻¹ * s) * (u : Equiv.Perm (Fin 315)) := by group
  have htVJ : t ∈ VJ := by
    have hmem : t ∈ centralizer (K : Set GJ) ⊓ centralizer (VJ : Set GJ) := ⟨htK, htV⟩
    rwa [hCV] at hmem
  have hs_eq : s = s' * (t : Equiv.Perm (Fin 315)) := by
    rw [ht_coe]
    dsimp only [s']
    group
  have hts' : (t : Equiv.Perm (Fin 315)) * s' = s' * (t : Equiv.Perm (Fin 315)) := by
    have h := hs'Cent t htVJ
    calc (t : Equiv.Perm (Fin 315)) * s'
        = (s' * (t : Equiv.Perm (Fin 315)) * s'⁻¹) * s' := by rw [h]
      _ = s' * (t : Equiv.Perm (Fin 315)) := by group
  exact ⟨t, htVJ, hs_eq, hts'⟩

private theorem false_of_centralizes
    {K : Subgroup GJ} {s : Equiv.Perm (Fin 315)} {w : GJ}
    (hsR : s ∈ R) (hsNotP : s ∉ P)
    (hsComm : ∀ k ∈ K, s * (k : Equiv.Perm (Fin 315)) =
      (k : Equiv.Perm (Fin 315)) * s)
    (hKz : K ≤ centralizer ({zJ} : Set GJ))
    (hcent : ∀ u ∈ VJ, s * (u : Equiv.Perm (Fin 315)) * s⁻¹ =
      (u : Equiv.Perm (Fin 315)))
    (hwV : w ∈ VJ) (hw_ne : w ≠ 1)
    (hw : (w : Equiv.Perm (Fin 315)) = s ^ 2)
    (hCV : centralizer (K : Set GJ) ⊓ centralizer (VJ : Set GJ) = VJ) : False := by
  obtain ⟨t, htV, hs_eq, hts'⟩ :=
    exists_mem_VJ_decomposition hsR hsNotP hsComm hKz hcent hCV
  let s' : Equiv.Perm (Fin 315) :=
    (zJ : Equiv.Perm (Fin 315)) * s * (zJ : Equiv.Perm (Fin 315))⁻¹
  have hs_eq' : s = s' * (t : Equiv.Perm (Fin 315)) := hs_eq
  have ht2 : (t : Equiv.Perm (Fin 315)) * (t : Equiv.Perm (Fin 315)) = 1 := by
    have h := mul_self_of_mem_kleinSub htV
    simpa using congrArg Subtype.val h
  have hsq : s ^ 2 = s' ^ 2 := by
    rw [hs_eq', pow_two, pow_two]
    calc (s' * (t : Equiv.Perm (Fin 315))) * (s' * (t : Equiv.Perm (Fin 315)))
        = s' * ((t : Equiv.Perm (Fin 315)) * s') * (t : Equiv.Perm (Fin 315)) := by
          group
      _ = s' * (s' * (t : Equiv.Perm (Fin 315))) * (t : Equiv.Perm (Fin 315)) := by
          rw [hts']
      _ = s' * s' * ((t : Equiv.Perm (Fin 315)) * (t : Equiv.Perm (Fin 315))) := by
          group
      _ = s' * s' := by rw [ht2, mul_one]
  have hs'_sq : s' ^ 2 = (zJ : Equiv.Perm (Fin 315)) * s ^ 2 *
      (zJ : Equiv.Perm (Fin 315))⁻¹ := by
    dsimp [s']
    rw [pow_two, pow_two]
    group
  have hwfix : (zJ : Equiv.Perm (Fin 315)) * (w : Equiv.Perm (Fin 315)) *
      (zJ : Equiv.Perm (Fin 315))⁻¹ = (w : Equiv.Perm (Fin 315)) := by
    rw [hw]
    exact hs'_sq.symm.trans hsq.symm
  have hwCz : w ∈ centralizer ({zJ} : Set GJ) := by
    rw [mem_centralizer_singleton_iff]
    apply Subtype.ext
    change (w : Equiv.Perm (Fin 315)) * (zJ : Equiv.Perm (Fin 315)) =
      (zJ : Equiv.Perm (Fin 315)) * (w : Equiv.Perm (Fin 315))
    calc (w : Equiv.Perm (Fin 315)) * (zJ : Equiv.Perm (Fin 315))
        = ((zJ : Equiv.Perm (Fin 315)) * (w : Equiv.Perm (Fin 315)) *
            (zJ : Equiv.Perm (Fin 315))⁻¹) * (zJ : Equiv.Perm (Fin 315)) := by
          rw [hwfix]
      _ = (zJ : Equiv.Perm (Fin 315)) * (w : Equiv.Perm (Fin 315)) := by group
  have hmem : w ∈ VJ ⊓ centralizer ({zJ} : Set GJ) := ⟨hwV, hwCz⟩
  rw [VJ_inf_centralizer_z] at hmem
  exact hw_ne (Subgroup.mem_bot.mp hmem)

private theorem false_of_not_centralizes
    {K : Subgroup GJ} {s : Equiv.Perm (Fin 315)} {w : GJ}
    (hK5 : ∃ y ∈ K, orderOf y = 5)
    (hsR : s ∈ R) (hsNotP : s ∉ P)
    (hsComm : ∀ k ∈ K, s * (k : Equiv.Perm (Fin 315)) =
      (k : Equiv.Perm (Fin 315)) * s)
    (hwV : w ∈ VJ) (hw_ne : w ≠ 1)
    (hw : (w : Equiv.Perm (Fin 315)) = s ^ 2)
    (hVK : VJ ≤ centralizer (K : Set GJ))
    (hconjV : ∀ u ∈ VJ, ∃ a : GJ, a ∈ VJ ∧
      (a : Equiv.Perm (Fin 315)) = s * (u : Equiv.Perm (Fin 315)) * s⁻¹)
    (hex : ∃ u ∈ VJ, s * (u : Equiv.Perm (Fin 315)) * s⁻¹ ≠
      (u : Equiv.Perm (Fin 315))) : False := by
  obtain ⟨u, huV, hu_ne⟩ := hex
  obtain ⟨a, haV, ha_coe⟩ := hconjV u huV
  have hsw : s * (w : Equiv.Perm (Fin 315)) * s⁻¹ =
      (w : Equiv.Perm (Fin 315)) := by rw [hw]; group
  have hu1 : u ≠ 1 := by
    intro h
    apply hu_ne
    rw [h]
    simp
  have ha1 : a ≠ 1 := by
    intro h
    apply hu1
    have hmem : (u : Equiv.Perm (Fin 315)) = 1 := by
      calc (u : Equiv.Perm (Fin 315))
          = s⁻¹ * (s * (u : Equiv.Perm (Fin 315)) * s⁻¹) * s := by group
        _ = s⁻¹ * 1 * s := by rw [← ha_coe, h]; simp
        _ = 1 := by simp
    exact Subtype.ext hmem
  have hwcomm : (w : Equiv.Perm (Fin 315)) * s = s * (w : Equiv.Perm (Fin 315)) := by
    calc (w : Equiv.Perm (Fin 315)) * s
        = (s * (w : Equiv.Perm (Fin 315)) * s⁻¹) * s := by rw [hsw]
      _ = s * (w : Equiv.Perm (Fin 315)) := by group
  have hconjW : s⁻¹ * (w : Equiv.Perm (Fin 315)) * s = (w : Equiv.Perm (Fin 315)) := by
    calc s⁻¹ * (w : Equiv.Perm (Fin 315)) * s
        = s⁻¹ * ((w : Equiv.Perm (Fin 315)) * s) := by group
      _ = s⁻¹ * (s * (w : Equiv.Perm (Fin 315))) := by rw [hwcomm]
      _ = (w : Equiv.Perm (Fin 315)) := by group
  have huw : u ≠ w := by
    intro h
    apply hu_ne
    rw [h, hsw]
  have haw : a ≠ w := by
    intro h
    apply huw
    have hmem : (u : Equiv.Perm (Fin 315)) = (w : Equiv.Perm (Fin 315)) := by
      calc (u : Equiv.Perm (Fin 315))
          = s⁻¹ * (s * (u : Equiv.Perm (Fin 315)) * s⁻¹) * s := by group
        _ = s⁻¹ * (w : Equiv.Perm (Fin 315)) * s := by rw [← ha_coe, h]
        _ = (w : Equiv.Perm (Fin 315)) := hconjW
    exact Subtype.ext hmem
  have hau : a ≠ u := by
    intro h
    apply hu_ne
    rw [← ha_coe, h]
  have ha_eq : a = w * u :=
    eq_mul_of_mem_VJ (u := u) (v := w) (w := a) huV hwV haV hu1 hw_ne ha1 huw
      (fun h => hau h.symm) (fun h => haw h.symm)
  have ha_perm : s * (u : Equiv.Perm (Fin 315)) * s⁻¹ =
      (w : Equiv.Perm (Fin 315)) * (u : Equiv.Perm (Fin 315)) := by
    rw [← ha_coe]
    simpa using congrArg Subtype.val ha_eq
  have hsq : (s * (u : Equiv.Perm (Fin 315))) ^ 2 = 1 := by
    rw [pow_two]
    calc (s * (u : Equiv.Perm (Fin 315))) * (s * (u : Equiv.Perm (Fin 315)))
        = (s * (u : Equiv.Perm (Fin 315)) * s⁻¹) * s ^ 2 *
            (u : Equiv.Perm (Fin 315)) := by group
      _ = ((w : Equiv.Perm (Fin 315)) * (u : Equiv.Perm (Fin 315))) *
            (w : Equiv.Perm (Fin 315)) * (u : Equiv.Perm (Fin 315)) := by
          rw [ha_perm, hw]
      _ = ((w : Equiv.Perm (Fin 315)) * (u : Equiv.Perm (Fin 315))) *
            ((w : Equiv.Perm (Fin 315)) * (u : Equiv.Perm (Fin 315))) := by group
      _ = 1 := by
        have h1 : (w * u) * (w * u) = 1 :=
          mul_self_of_mem_kleinSub (mul_mem hwV huV)
        have h2 : (((w * u : GJ) : Equiv.Perm (Fin 315))) *
            (((w * u : GJ) : Equiv.Perm (Fin 315))) = 1 := by
          simpa using congrArg (fun z : GJ => (z : Equiv.Perm (Fin 315))) h1
        simpa [Subgroup.coe_mul] using h2
  have hsuR : s * (u : Equiv.Perm (Fin 315)) ∈ R :=
    R.mul_mem hsR (P_le_R u.2)
  have hsuNotP : s * (u : Equiv.Perm (Fin 315)) ∉ P := by
    intro h
    apply hsNotP
    have h' : (s * (u : Equiv.Perm (Fin 315))) *
        (u : Equiv.Perm (Fin 315))⁻¹ ∈ P := P.mul_mem h (P.inv_mem u.2)
    rwa [mul_assoc, mul_inv_cancel, mul_one] at h'
  obtain ⟨y, hyK, hy5⟩ := hK5
  have hy5' : orderOf (y : Equiv.Perm (Fin 315)) = 5 := by
    rw [Subgroup.orderOf_coe, hy5]
  have hsuCommY : (s * (u : Equiv.Perm (Fin 315))) *
      (y : Equiv.Perm (Fin 315)) = (y : Equiv.Perm (Fin 315)) *
        (s * (u : Equiv.Perm (Fin 315))) := by
    have hsy : s * (y : Equiv.Perm (Fin 315)) = (y : Equiv.Perm (Fin 315)) * s :=
      hsComm y hyK
    have huy : (u : Equiv.Perm (Fin 315)) * (y : Equiv.Perm (Fin 315)) =
        (y : Equiv.Perm (Fin 315)) * (u : Equiv.Perm (Fin 315)) := by
      have h := mem_centralizer_iff.mp (hVK huV) y hyK
      exact (congrArg Subtype.val h).symm
    calc (s * (u : Equiv.Perm (Fin 315))) * (y : Equiv.Perm (Fin 315))
        = s * ((u : Equiv.Perm (Fin 315)) * (y : Equiv.Perm (Fin 315))) := by group
      _ = s * ((y : Equiv.Perm (Fin 315)) * (u : Equiv.Perm (Fin 315))) := by rw [huy]
      _ = (s * (y : Equiv.Perm (Fin 315))) * (u : Equiv.Perm (Fin 315)) := by group
      _ = ((y : Equiv.Perm (Fin 315)) * s) * (u : Equiv.Perm (Fin 315)) := by rw [hsy]
      _ = (y : Equiv.Perm (Fin 315)) * (s * (u : Equiv.Perm (Fin 315))) := by group
  exact hsuNotP
    (CFSG.ComponentClassification.RankTwoClassical.J2Std.mem_P_of_commute
      hsuR hsq y.2 hy5' hsuCommY)

theorem mem_P_of_commute_K
    {K : Subgroup GJ}
    (hKA : Nonempty (↥K ≃* alternatingGroup (Fin 5))) (hxK : xJ ∈ K)
    (hKz : K ≤ centralizer ({zJ} : Set GJ)) (hVK : VJ ≤ centralizer (K : Set GJ))
    (hCV : centralizer (K : Set GJ) ⊓ centralizer (VJ : Set GJ) = VJ)
    {r : Equiv.Perm (Fin 315)} (hr : r ∈ R)
    (hrK : ∀ k ∈ K, r * (k : Equiv.Perm (Fin 315)) = (k : Equiv.Perm (Fin 315)) * r) :
    r ∈ P := by
  classical
  by_contra hrNotP
  obtain ⟨s, hsR, hsNotP, hsComm, hsqP, h256⟩ := exists_odd_part hr hrNotP hrK
  obtain ⟨y, hyK, hy5⟩ := exists_orderOf_eq_five hKA
  have hy5' : orderOf (y : Equiv.Perm (Fin 315)) = 5 := by
    rw [Subgroup.orderOf_coe, hy5]
  let w : GJ := ⟨s ^ 2, hsqP⟩
  have hw_val : (w : Equiv.Perm (Fin 315)) = s ^ 2 := rfl
  have hsx : s * (xJ : Equiv.Perm (Fin 315)) = (xJ : Equiv.Perm (Fin 315)) * s :=
    hsComm xJ hxK
  have hwV : w ∈ VJ := by
    refine mem_V_of_two ?_ ?_
    · rw [mem_centralizer_singleton_iff]
      apply Subtype.ext
      change s ^ 2 * (xJ : Equiv.Perm (Fin 315)) =
        (xJ : Equiv.Perm (Fin 315)) * s ^ 2
      exact (Commute.pow_left (show Commute s (xJ : Equiv.Perm (Fin 315)) from hsx) 2).eq
    · apply Subtype.ext
      change (s ^ 2) ^ 2 ^ 7 = 1
      rw [← pow_mul, show 2 * 2 ^ 7 = 2 ^ 8 by norm_num]
      exact h256
  have hw_ne : w ≠ 1 := by
    intro hw1
    have hs2 : s ^ 2 = 1 := by rw [← hw_val, hw1]; rfl
    exact hsNotP
      (CFSG.ComponentClassification.RankTwoClassical.J2Std.mem_P_of_commute
        hsR hs2 y.2 hy5' (hsComm y hyK))
  have hconjV : ∀ u ∈ VJ, ∃ a : GJ, a ∈ VJ ∧
      (a : Equiv.Perm (Fin 315)) = s * (u : Equiv.Perm (Fin 315)) * s⁻¹ :=
    fun u hu => conj_mem_VJ hsR hu hsx
  by_cases hcent : ∀ u ∈ VJ, s * (u : Equiv.Perm (Fin 315)) * s⁻¹ =
      (u : Equiv.Perm (Fin 315))
  · exact false_of_centralizes hsR hsNotP hsComm hKz hcent hwV hw_ne hw_val hCV
  · push Not at hcent
    exact false_of_not_centralizes ⟨y, hyK, hy5⟩ hsR hsNotP hsComm hwV hw_ne hw_val hVK
      hconjV hcent

theorem eq_conj_of_forall_apply_eq
    {K : Subgroup GJ}
    (hKA : Nonempty (↥K ≃* alternatingGroup (Fin 5))) (hxK : xJ ∈ K)
    (hKz : K ≤ centralizer ({zJ} : Set GJ)) (hVK : VJ ≤ centralizer (K : Set GJ))
    (hCV : centralizer (K : Set GJ) ⊓ centralizer (VJ : Set GJ) = VJ)
    (α : MulAut GJ) (hα : ∀ k ∈ K, α k = k) :
    ∃ g ∈ centralizer (K : Set GJ), α = MulAut.conj g := by
  classical
  let r : R := rAutEquiv.symm α
  have hrConj : rConj r = α := by
    rw [← rAutEquiv_apply r]
    exact MulEquiv.apply_symm_apply rAutEquiv α
  have hrK : ∀ k ∈ K, (r : Equiv.Perm (Fin 315)) *
      (k : Equiv.Perm (Fin 315)) = (k : Equiv.Perm (Fin 315)) *
        (r : Equiv.Perm (Fin 315)) := by
    intro k hk
    have h1 : rConj r k = k := by rw [hrConj]; exact hα k hk
    have h2 : (r : Equiv.Perm (Fin 315)) * (k : Equiv.Perm (Fin 315)) *
        (r : Equiv.Perm (Fin 315))⁻¹ = (k : Equiv.Perm (Fin 315)) :=
      congrArg Subtype.val h1
    calc (r : Equiv.Perm (Fin 315)) * (k : Equiv.Perm (Fin 315))
        = ((r : Equiv.Perm (Fin 315)) * (k : Equiv.Perm (Fin 315)) *
            (r : Equiv.Perm (Fin 315))⁻¹) * (r : Equiv.Perm (Fin 315)) := by group
      _ = (k : Equiv.Perm (Fin 315)) * (r : Equiv.Perm (Fin 315)) := by rw [h2]
  have hrP : (r : Equiv.Perm (Fin 315)) ∈ P :=
    mem_P_of_commute_K hKA hxK hKz hVK hCV r.2 hrK
  refine ⟨⟨(r : Equiv.Perm (Fin 315)), hrP⟩, ?_, ?_⟩
  · rw [mem_centralizer_iff]
    intro k hk
    apply Subtype.ext
    exact (hrK k hk).symm
  · calc α = rConj r := hrConj.symm
      _ = MulAut.conj (⟨(r : Equiv.Perm (Fin 315)), hrP⟩ : GJ) := rConj_eq_conj hrP

end CFSG.RankThree.PartTwo.KFacts.KS166
