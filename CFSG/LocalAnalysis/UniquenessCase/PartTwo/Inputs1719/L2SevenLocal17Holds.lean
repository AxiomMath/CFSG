module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.L2SevenS4
public import CFSG.Quasithin.Vol2.Ch10SecBCoord
public import CFSG.Quasithin.Vol2.Ch10SecBCoordPsi
public import CFSG.Quasithin.Vol2.Ch10SecBL32Xi
public import CFSG.Quasithin.Background.HTriPermute
public import CFSG.GroupTheory.SteinbergCBFTFactorization
public import CFSG.GroupTheory.PermutingProducts
public import CFSG.Quasithin.EmptyFaithful.T1531In68b
public import CFSG.Quasithin.Recognition.GoldschmidtF112RTransport
public import CFSG.Adapters.StatedPSLTwoSeven
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.L2SevenLocal17
public import CFSG.Quasithin.Vol2.Ch10SecBL32O2
public import CFSG.Quasithin.Vol2.Ch10SecBL32Prod

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise

open CFSG.Quasithin.Vol2.Ch10.SecB
open CFSG.Quasithin.Vol2.Ch10.SecB.L32

private theorem l32_exists_ka_order_three :
    ∃ X : Subgroup Γ, Nat.card X = 3 ∧ X ≤ Ka := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : 3 ∣ Nat.card ↥Ka := by rw [card_Ka']; norm_num
  obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' (G := ↥Ka) 3 h3
  refine ⟨Subgroup.zpowers (k : Γ), ?_, ?_⟩
  · rw [Nat.card_zpowers, Subgroup.orderOf_coe, hk]
  · rw [Subgroup.zpowers_le]
    exact k.2

private theorem l32_exists_kb_order_three :
    ∃ X : Subgroup Γ, Nat.card X = 3 ∧ X ≤ Kb := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : 3 ∣ Nat.card ↥Kb := by rw [card_Kb']; norm_num
  obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' (G := ↥Kb) 3 h3
  refine ⟨Subgroup.zpowers (k : Γ), ?_, ?_⟩
  · rw [Nat.card_zpowers, Subgroup.orderOf_coe, hk]
  · rw [Subgroup.zpowers_le]
    exact k.2

private theorem l32_permutes_of_le_pa {X : Subgroup Γ} (hX : Nat.card X = 3) (hXPa : X ≤ Pa) :
    Permutes X U3 := by
  have hinf : X ⊓ U3 = ⊥ := by
    apply Subgroup.inf_eq_bot_of_coprime
    rw [hX, CFSG.Quasithin.Vol2.Ch10.SecB.card_U3]
    norm_num
  have hsetcard : Nat.card ↥((X : Set Γ) * (U3 : Set Γ)) = 24 := by
    have h := CFSG.GroupTheory.FT63ChII.card_setMul_mul_card_inf X U3
    rw [hX, CFSG.Quasithin.Vol2.Ch10.SecB.card_U3, hinf, Subgroup.card_bot] at h
    omega
  have hsetcard' : Nat.card ↥((U3 : Set Γ) * (X : Set Γ)) = 24 := by
    have h := CFSG.GroupTheory.FT63ChII.card_setMul_mul_card_inf U3 X
    rw [CFSG.Quasithin.Vol2.Ch10.SecB.card_U3, hX, inf_comm, hinf, Subgroup.card_bot] at h
    omega
  have hsetA : (X : Set Γ) * (U3 : Set Γ) = (Pa : Set Γ) := by
    have : Fintype ↥((X : Set Γ) * (U3 : Set Γ)) := Fintype.ofFinite _
    have : Fintype ↥(Pa : Set Γ) := Fintype.ofFinite _
    refine Set.eq_of_subset_of_card_le (Subgroup.mul_subset hXPa u3_le_pa) ?_
    have hP : Fintype.card ↥(Pa : Set Γ) = 24 := by
      change Fintype.card ↥Pa = 24
      rw [← card_Pa]
      exact Fintype.card_subtype (· ∈ Pa)
    have hS : Fintype.card ↥((X : Set Γ) * (U3 : Set Γ)) = 24 := by
      rw [← Nat.card_eq_fintype_card]; exact hsetcard
    rw [hP, hS]
  have hsetB : (U3 : Set Γ) * (X : Set Γ) = (Pa : Set Γ) := by
    have : Fintype ↥((U3 : Set Γ) * (X : Set Γ)) := Fintype.ofFinite _
    have : Fintype ↥(Pa : Set Γ) := Fintype.ofFinite _
    refine Set.eq_of_subset_of_card_le (Subgroup.mul_subset u3_le_pa hXPa) ?_
    have hP : Fintype.card ↥(Pa : Set Γ) = 24 := by
      change Fintype.card ↥Pa = 24
      rw [← card_Pa]
      exact Fintype.card_subtype (· ∈ Pa)
    have hS : Fintype.card ↥((U3 : Set Γ) * (X : Set Γ)) = 24 := by
      rw [← Nat.card_eq_fintype_card]; exact hsetcard'
    rw [hP, hS]
  exact hsetA.trans hsetB.symm

private theorem l32_permutes_of_le_ka {X : Subgroup Γ} (hX : Nat.card X = 3) (hXKa : X ≤ Ka) :
    Permutes X U3 :=
  l32_permutes_of_le_pa hX (by intro x hx; exact (hXKa hx).1)

private theorem l32_permutes_of_le_kb {X : Subgroup Γ} (hX : Nat.card X = 3) (hXKb : X ≤ Kb) :
    Permutes X U3 := by
  have hinf : X ⊓ U3 = ⊥ := by
    apply Subgroup.inf_eq_bot_of_coprime
    rw [hX, CFSG.Quasithin.Vol2.Ch10.SecB.card_U3]
    norm_num
  have hXPb : X ≤ Pb := by intro x hx; exact (hXKb hx).1
  have hsetcard : Nat.card ↥((X : Set Γ) * (U3 : Set Γ)) = 24 := by
    have h := CFSG.GroupTheory.FT63ChII.card_setMul_mul_card_inf X U3
    rw [hX, CFSG.Quasithin.Vol2.Ch10.SecB.card_U3, hinf, Subgroup.card_bot] at h
    omega
  have hsetcard' : Nat.card ↥((U3 : Set Γ) * (X : Set Γ)) = 24 := by
    have h := CFSG.GroupTheory.FT63ChII.card_setMul_mul_card_inf U3 X
    rw [CFSG.Quasithin.Vol2.Ch10.SecB.card_U3, hX, inf_comm, hinf, Subgroup.card_bot] at h
    omega
  have hsetA : (X : Set Γ) * (U3 : Set Γ) = (Pb : Set Γ) := by
    have : Fintype ↥((X : Set Γ) * (U3 : Set Γ)) := Fintype.ofFinite _
    have : Fintype ↥(Pb : Set Γ) := Fintype.ofFinite _
    refine Set.eq_of_subset_of_card_le (Subgroup.mul_subset hXPb u3_le_pb) ?_
    have hP : Fintype.card ↥(Pb : Set Γ) = 24 := by
      change Fintype.card ↥Pb = 24
      rw [← card_Pb]
      exact Fintype.card_subtype (· ∈ Pb)
    have hS : Fintype.card ↥((X : Set Γ) * (U3 : Set Γ)) = 24 := by
      rw [← Nat.card_eq_fintype_card]; exact hsetcard
    rw [hP, hS]
  have hsetB : (U3 : Set Γ) * (X : Set Γ) = (Pb : Set Γ) := by
    have : Fintype ↥((U3 : Set Γ) * (X : Set Γ)) := Fintype.ofFinite _
    have : Fintype ↥(Pb : Set Γ) := Fintype.ofFinite _
    refine Set.eq_of_subset_of_card_le (Subgroup.mul_subset u3_le_pb hXPb) ?_
    have hP : Fintype.card ↥(Pb : Set Γ) = 24 := by
      change Fintype.card ↥Pb = 24
      rw [← card_Pb]
      exact Fintype.card_subtype (· ∈ Pb)
    have hS : Fintype.card ↥((U3 : Set Γ) * (X : Set Γ)) = 24 := by
      rw [← Nat.card_eq_fintype_card]; exact hsetcard'
    rw [hP, hS]
  exact hsetA.trans hsetB.symm


private theorem l32_permutesS3 {X : Subgroup Γ} (hX : Nat.card X = 3)
    (hperm : Permutes X U3) :
    Nat.card ↥(X ⊔ U3) = 24 ∧
      Nat.card ↥(CFSG.Open.pCoreOf 2 (X ⊔ U3)) = 4 ∧
      Nonempty (Bar2 (X ⊔ U3) ≃* Equiv.Perm (Fin 3)) ∧
      ∃ d ∈ U3, d ∉ CFSG.Open.pCoreOf 2 (X ⊔ U3) ∧
        ∀ x ∈ X, d * x * d⁻¹ * x ∈ CFSG.Open.pCoreOf 2 (X ⊔ U3) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinf : X ⊓ U3 = ⊥ := by
    apply Subgroup.inf_eq_bot_of_coprime
    rw [hX, CFSG.Quasithin.Vol2.Ch10.SecB.card_U3]
    norm_num
  have hcard : Nat.card ↥(X ⊔ U3) = 24 := by
    rw [CFSG.Quasithin.H.Tri.card_sup_eq_mul hperm hinf, hX, CFSG.Quasithin.Vol2.Ch10.SecB.card_U3]
  have hclass : X ⊔ U3 = Pa ∨ X ⊔ U3 = Pb := by
    have hO := overgroups (X ⊔ U3) (le_sup_right : U3 ≤ X ⊔ U3)
    rcases hO with h | h | h | h
    · rw [h, CFSG.Quasithin.Vol2.Ch10.SecB.card_U3] at hcard
      norm_num at hcard
    · exact Or.inl h
    · exact Or.inr h
    · rw [h, Subgroup.card_top, CFSG.Quasithin.Vol2.Ch10.SecB.card_Γ] at hcard
      norm_num at hcard
  have hUA : U3 ≤ X ⊔ U3 := le_sup_right
  have hsubcard : Nat.card ↥(U3.subgroupOf (X ⊔ U3)) = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUA).toEquiv,
      CFSG.Quasithin.Vol2.Ch10.SecB.card_U3]
  have hidx : (U3.subgroupOf (X ⊔ U3)).index = 3 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (U3.subgroupOf (X ⊔ U3))
    rw [← Subgroup.index_eq_card, hsubcard, hcard] at h
    omega
  have hsyl : CFSG.QuasithinUnique.IsSylowTwoOf U3 (X ⊔ U3) :=
    ⟨hUA, IsPGroup.of_card (n := 3) (by rw [CFSG.Quasithin.Vol2.Ch10.SecB.card_U3]; norm_num), by
      rw [hidx]; norm_num⟩
  have hXne : X ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hX
    norm_num at hX
  have hN : ¬ (X ⊔ U3) ≤ Subgroup.normalizer (U3 : Set Γ) := by
    intro hle
    have hXleN : X ≤ Subgroup.normalizer (U3 : Set Γ) := le_sup_left.trans hle
    have hXleU : X ≤ U3 := by
      rw [← normalizer_U3]
      exact hXleN
    have hXbot : X = ⊥ := by
      rw [← inf_eq_left.mpr hXleU, hinf]
    exact hXne hXbot
  have hbar : Nonempty (Bar2 (X ⊔ U3) ≃* Equiv.Perm (Fin 3)) :=
    CFSG.Quasithin.nonempty_quotient_pCore_of_relIndex_eq_three' hsyl hidx hN
  have hquot : Nat.card (Bar2 (X ⊔ U3)) = 6 := by
    obtain ⟨e⟩ := hbar
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm]
    norm_num
  have hOcard : Nat.card ↥(CFSG.Open.pCoreOf 2 (X ⊔ U3)) = 4 := by
    have hpc : Nat.card (CFSG.Open.pCore 2 ↥(X ⊔ U3)) = 4 := by
      have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
        (CFSG.Open.pCore 2 ↥(X ⊔ U3))
      rw [hquot, hcard] at h
      omega
    rw [CFSG.Open.pCoreOf, Subgroup.card_subtype]
    exact hpc
  refine ⟨hcard, hOcard, hbar, ?_⟩
  rcases hclass with hA | hA
  ·
    have hXPa : X ≤ Pa := by
      rw [← hA]
      exact le_sup_left
    have hOcardPa : Nat.card ↥(CFSG.Open.pCoreOf 2 Pa) = 4 := by
      rw [← hA]
      exact hOcard
    have hEa_le : Ea ≤ CFSG.Open.pCoreOf 2 Pa := by
      apply CFSG.LieType.BorelTits.le_pCoreOf
      · intro x hx
        exact (ea_le x hx).1.1
      · refine Subgroup.Normal.mk fun n hn g => ?_
        exact ea_normal (g : Γ) (n : Γ) g.2 hn
      · exact IsPGroup.of_card (n := 2) (by rw [card_Ea']; norm_num)
    have hpCoreEq : CFSG.Open.pCoreOf 2 Pa = Ea := by
      symm
      exact Subgroup.eq_of_le_of_card_ge hEa_le (by rw [hOcardPa, card_Ea'])
    obtain ⟨d, hdmem, hdinv⟩ := ka_inv
    have hdU : d ∈ U3 := (mem_uList_iff d).mp hdmem
    have hdPa : IsPa d := isPa_of_isU hdU
    obtain ⟨x, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hXne
    have hxord : orderOf (x : Γ) = 3 := by
      have hdvd : orderOf (x : Γ) ∣ Nat.card X := Subgroup.orderOf_dvd_natCard X x.2
      rw [hX] at hdvd
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
      · exact absurd (orderOf_eq_one_iff.mp h1) (fun h => hx1 (Subtype.ext h))
      · exact h3
    have hxKa : IsKa (x : Γ) :=
      isKa_of_odd (hXPa x.2) (by rw [hxord]; norm_num)
    have hxEa : (x : Γ) ∉ Ea := by
      intro hxE
      have hdvd : orderOf (x : Γ) ∣ Nat.card ↥Ea := Subgroup.orderOf_dvd_natCard Ea hxE
      rw [hxord, card_Ea'] at hdvd
      norm_num at hdvd
    have hx3 : (x : Γ) ^ 3 = 1 := by
      have := pow_orderOf_eq_one (x : Γ)
      rwa [hxord] at this
    have hx2_not : (x : Γ) * (x : Γ) ∉ Ea := by
      rw [← pow_two]
      intro h2
      apply hxEa
      have h4 : ((x : Γ) ^ 2) ^ 2 = (x : Γ) := by
        rw [← pow_mul]
        norm_num
        calc (x : Γ) ^ 4 = (x : Γ) ^ 3 * (x : Γ) := by group
          _ = (x : Γ) := by rw [hx3, one_mul]
      rw [← h4]
      exact Ea.pow_mem h2 2
    have hdEa : d ∉ Ea := by
      intro hdE
      have hnorm : (x : Γ) * d⁻¹ * (x : Γ)⁻¹ ∈ Ea :=
        (mem_Ea).mpr (ea_normal (x : Γ) d⁻¹ (hXPa x.2) (Ea.inv_mem hdE))
      have hA : d * ((x : Γ) * d⁻¹ * (x : Γ)⁻¹) ∈ Ea := Ea.mul_mem hdE hnorm
      have hinv : d * (x : Γ) * d⁻¹ * (x : Γ) ∈ Ea :=
        (mem_Ea).mpr (hdinv (x : Γ) hxKa)
      have hEq : d * (x : Γ) * d⁻¹ * (x : Γ) =
          (d * ((x : Γ) * d⁻¹ * (x : Γ)⁻¹)) * ((x : Γ) * (x : Γ)) := by group
      rw [hEq] at hinv
      have hx2E : (x : Γ) * (x : Γ) ∈ Ea := by
        have hm := Ea.mul_mem (Ea.inv_mem hA) hinv
        have heq : (d * ((x : Γ) * d⁻¹ * (x : Γ)⁻¹))⁻¹ *
            (d * ((x : Γ) * d⁻¹ * (x : Γ)⁻¹) * ((x : Γ) * (x : Γ))) =
            (x : Γ) * (x : Γ) := by group
        rwa [heq] at hm
      exact hx2_not hx2E
    refine ⟨d, hdU, ?_, ?_⟩
    · rw [hA, hpCoreEq]
      exact hdEa
    · intro x hxX
      have hxPa : IsPa x := hXPa hxX
      have hxodd : Odd (orderOf x) := by
        have hdvd : orderOf x ∣ Nat.card X := Subgroup.orderOf_dvd_natCard X hxX
        rw [hX] at hdvd
        rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
        · rw [h1]; norm_num
        · rw [h3]; norm_num
      have hxKa : IsKa x := isKa_of_odd hxPa hxodd
      rw [hA, hpCoreEq]
      exact hdinv x hxKa
  ·
    have hXPb : X ≤ Pb := by
      rw [← hA]
      exact le_sup_left
    have hOcardPb : Nat.card ↥(CFSG.Open.pCoreOf 2 Pb) = 4 := by
      rw [← hA]
      exact hOcard
    have hEb_le : Eb ≤ CFSG.Open.pCoreOf 2 Pb := by
      apply CFSG.LieType.BorelTits.le_pCoreOf
      · intro x hx
        exact (eb_le x hx).1.1
      · refine Subgroup.Normal.mk fun n hn g => ?_
        exact eb_normal (g : Γ) (n : Γ) g.2 hn
      · exact IsPGroup.of_card (n := 2) (by rw [card_Eb']; norm_num)
    have hpCoreEq : CFSG.Open.pCoreOf 2 Pb = Eb := by
      symm
      exact Subgroup.eq_of_le_of_card_ge hEb_le (by rw [hOcardPb, card_Eb'])
    obtain ⟨d, hdmem, hdinv⟩ := kb_inv
    have hdU : d ∈ U3 := (mem_uList_iff d).mp hdmem
    have hdPb : IsPb d := isPb_of_isU hdU
    obtain ⟨x, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hXne
    have hxord : orderOf (x : Γ) = 3 := by
      have hdvd : orderOf (x : Γ) ∣ Nat.card X := Subgroup.orderOf_dvd_natCard X x.2
      rw [hX] at hdvd
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
      · exact absurd (orderOf_eq_one_iff.mp h1) (fun h => hx1 (Subtype.ext h))
      · exact h3
    have hxKb : IsKb (x : Γ) :=
      isKb_of_odd (hXPb x.2) (by rw [hxord]; norm_num)
    have hxEb : (x : Γ) ∉ Eb := by
      intro hxE
      have hdvd : orderOf (x : Γ) ∣ Nat.card ↥Eb := Subgroup.orderOf_dvd_natCard Eb hxE
      rw [hxord, card_Eb'] at hdvd
      norm_num at hdvd
    have hx3 : (x : Γ) ^ 3 = 1 := by
      have := pow_orderOf_eq_one (x : Γ)
      rwa [hxord] at this
    have hx2_not : (x : Γ) * (x : Γ) ∉ Eb := by
      rw [← pow_two]
      intro h2
      apply hxEb
      have h4 : ((x : Γ) ^ 2) ^ 2 = (x : Γ) := by
        rw [← pow_mul]
        norm_num
        calc (x : Γ) ^ 4 = (x : Γ) ^ 3 * (x : Γ) := by group
          _ = (x : Γ) := by rw [hx3, one_mul]
      rw [← h4]
      exact Eb.pow_mem h2 2
    have hdEb : d ∉ Eb := by
      intro hdE
      have hnorm : (x : Γ) * d⁻¹ * (x : Γ)⁻¹ ∈ Eb :=
        (mem_Eb).mpr (eb_normal (x : Γ) d⁻¹ (hXPb x.2) (Eb.inv_mem hdE))
      have hA : d * ((x : Γ) * d⁻¹ * (x : Γ)⁻¹) ∈ Eb := Eb.mul_mem hdE hnorm
      have hinv : d * (x : Γ) * d⁻¹ * (x : Γ) ∈ Eb :=
        (mem_Eb).mpr (hdinv (x : Γ) hxKb)
      have hEq : d * (x : Γ) * d⁻¹ * (x : Γ) =
          (d * ((x : Γ) * d⁻¹ * (x : Γ)⁻¹)) * ((x : Γ) * (x : Γ)) := by group
      rw [hEq] at hinv
      have hx2E : (x : Γ) * (x : Γ) ∈ Eb := by
        have hm := Eb.mul_mem (Eb.inv_mem hA) hinv
        have heq : (d * ((x : Γ) * d⁻¹ * (x : Γ)⁻¹))⁻¹ *
            (d * ((x : Γ) * d⁻¹ * (x : Γ)⁻¹) * ((x : Γ) * (x : Γ))) =
            (x : Γ) * (x : Γ) := by group
        rwa [heq] at hm
      exact hx2_not hx2E
    refine ⟨d, hdU, ?_, ?_⟩
    · rw [hA, hpCoreEq]
      exact hdEb
    · intro x hxX
      have hxPb : IsPb x := hXPb hxX
      have hxodd : Odd (orderOf x) := by
        have hdvd : orderOf x ∣ Nat.card X := Subgroup.orderOf_dvd_natCard X hxX
        rw [hX] at hdvd
        rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
        · rw [h1]; norm_num
        · rw [h3]; norm_num
      have hxKb : IsKb x := isKb_of_odd hxPb hxodd
      rw [hA, hpCoreEq]
      exact hdinv x hxKb


private theorem l32_local :
    ∃ X₁ X₂ : Subgroup Γ, Nat.card X₁ = 3 ∧ Nat.card X₂ = 3 ∧ X₁ ≠ X₂ ∧
      Permutes X₁ U3 ∧ Permutes X₂ U3 ∧ X₁ ⊔ X₂ ⊔ U3 = ⊤ ∧
      Nonempty (Bar2 (X₁ ⊔ U3) ≃* Equiv.Perm (Fin 3)) ∧
      Nonempty (Bar2 (X₂ ⊔ U3) ≃* Equiv.Perm (Fin 3)) := by
  obtain ⟨X₁, hX₁, hX₁Ka⟩ := l32_exists_ka_order_three
  obtain ⟨X₂, hX₂, hX₂Kb⟩ := l32_exists_kb_order_three
  have hX₁Pa : X₁ ≤ Pa := by
    intro x hx
    exact (hX₁Ka hx).1
  have hX₂Pb : X₂ ≤ Pb := by
    intro x hx
    exact (hX₂Kb hx).1
  have hperm₁ : Permutes X₁ U3 := l32_permutes_of_le_ka hX₁ hX₁Ka
  have hperm₂ : Permutes X₂ U3 := l32_permutes_of_le_kb hX₂ hX₂Kb
  have hX₁X₂ : X₁ ≠ X₂ := by
    intro h
    have hsub : X₁ ≤ Ka ⊓ Kb := by
      intro x hx
      exact ⟨hX₁Ka hx, hX₂Kb (h ▸ hx)⟩
    have hleU : X₁ ≤ U3 := hsub.trans (by
      intro x hx
      exact pa_pb x hx.1.1 hx.2.1)
    have hdvd : Nat.card X₁ ∣ Nat.card U3 := Subgroup.card_dvd_of_le hleU
    rw [hX₁, CFSG.Quasithin.Vol2.Ch10.SecB.card_U3] at hdvd
    norm_num at hdvd
  have hjoin : X₁ ⊔ X₂ ⊔ U3 = ⊤ := by
    have hU : U3 ≤ X₁ ⊔ X₂ ⊔ U3 := le_sup_right
    have hO := overgroups (X₁ ⊔ X₂ ⊔ U3) hU
    rcases hO with h | h | h | h
    · exfalso
      have hX₁leY : X₁ ≤ X₁ ⊔ X₂ ⊔ U3 := le_sup_left.trans le_sup_left
      have hX₁le : X₁ ≤ U3 := h ▸ hX₁leY
      have hdvd : Nat.card X₁ ∣ Nat.card U3 := Subgroup.card_dvd_of_le hX₁le
      rw [hX₁, CFSG.Quasithin.Vol2.Ch10.SecB.card_U3] at hdvd
      norm_num at hdvd
    · exfalso
      have hX₂leY : X₂ ≤ X₁ ⊔ X₂ ⊔ U3 := le_sup_right.trans le_sup_left
      have hX₂lePa : X₂ ≤ Pa := h ▸ hX₂leY
      have hX₂leU : X₂ ≤ U3 := by
        intro x hx
        exact pa_pb x (hX₂lePa hx) (hX₂Pb hx)
      have hdvd : Nat.card X₂ ∣ Nat.card U3 := Subgroup.card_dvd_of_le hX₂leU
      rw [hX₂, CFSG.Quasithin.Vol2.Ch10.SecB.card_U3] at hdvd
      norm_num at hdvd
    · exfalso
      have hX₁leY : X₁ ≤ X₁ ⊔ X₂ ⊔ U3 := le_sup_left.trans le_sup_left
      have hX₁lePb : X₁ ≤ Pb := h ▸ hX₁leY
      have hX₁leU : X₁ ≤ U3 := by
        intro x hx
        exact pa_pb x (hX₁Pa hx) (hX₁lePb hx)
      have hdvd : Nat.card X₁ ∣ Nat.card U3 := Subgroup.card_dvd_of_le hX₁leU
      rw [hX₁, CFSG.Quasithin.Vol2.Ch10.SecB.card_U3] at hdvd
      norm_num at hdvd
    · exact h
  exact ⟨X₁, X₂, hX₁, hX₂, hX₁X₂, hperm₁, hperm₂, hjoin,
    (l32_permutesS3 hX₁ hperm₁).2.2.1, (l32_permutesS3 hX₂ hperm₂).2.2.1⟩


private theorem permutesS3_of_equiv {Y : Type} [Group Y] (ψ : Y ≃* Γ)
    {S X : Subgroup Y} (hS : S.map ψ.toMonoidHom = U3)
    (hX : Nat.card X = 3) (hperm : Permutes X S) :
    Nat.card ↥(X ⊔ S) = 24 ∧
      Nat.card ↥(CFSG.Open.pCoreOf 2 (X ⊔ S)) = 4 ∧
      Nonempty (Bar2 (X ⊔ S) ≃* Equiv.Perm (Fin 3)) ∧
      ∃ d ∈ S, d ∉ CFSG.Open.pCoreOf 2 (X ⊔ S) ∧
        ∀ x ∈ X, d * x * d⁻¹ * x ∈ CFSG.Open.pCoreOf 2 (X ⊔ S) := by
  classical
  have hψinj : Function.Injective ψ.toMonoidHom := fun a b h => ψ.injective h
  let X0 : Subgroup Γ := X.map ψ.toMonoidHom
  have hX0 : Nat.card X0 = 3 := by
    change Nat.card ↥(X.map ψ.toMonoidHom) = 3
    rw [Subgroup.card_map_of_injective (f := ψ.toMonoidHom) hψinj, hX]
  have hperm0 : Permutes X0 U3 := by
    change Permutes (X.map ψ.toMonoidHom) U3
    have := CFSG.GroupTheory.map_permutes_map ψ.toMonoidHom hperm
    rwa [hS] at this
  obtain ⟨hcard0, hOcard0, hbar0, d0, hd0U, hd0O, hd0inv⟩ := l32_permutesS3 hX0 hperm0
  have hmapA : (X ⊔ S).map ψ.toMonoidHom = X0 ⊔ U3 := by
    rw [Subgroup.map_sup, hS]
  let eA : ↥(X ⊔ S) ≃* ↥(X0 ⊔ U3) :=
    (Subgroup.equivMapOfInjective (X ⊔ S) ψ.toMonoidHom hψinj).trans
      (MulEquiv.subgroupCongr hmapA)
  have heA_apply (a : ↥(X ⊔ S)) :
      ((eA a : ↥(X0 ⊔ U3)) : Γ) = ψ (a : Y) := by
    have h1 : eA a = (MulEquiv.subgroupCongr hmapA)
        ((Subgroup.equivMapOfInjective (X ⊔ S) ψ.toMonoidHom hψinj) a) := rfl
    rw [h1, MulEquiv.subgroupCongr_apply, Subgroup.coe_equivMapOfInjective_apply]
    rfl
  have hcard : Nat.card ↥(X ⊔ S) = 24 := by
    rw [← Subgroup.card_map_of_injective (f := ψ.toMonoidHom) (K := X ⊔ S) ψ.injective, hmapA]
    exact hcard0
  have hOcard : Nat.card ↥(CFSG.Open.pCoreOf 2 (X ⊔ S)) = 4 := by
    rw [CFSG.Quasithin.F112R.card_pCoreOf_of_mulEquiv eA 2]
    exact hOcard0
  have hbar : Nonempty (Bar2 (X ⊔ S) ≃* Equiv.Perm (Fin 3)) := by
    obtain ⟨e⟩ := hbar0
    exact ⟨(quotO2Equiv eA).trans e⟩
  have hdS : ψ.symm d0 ∈ S := by
    rw [← Subgroup.mem_map_iff_mem (f := ψ.toMonoidHom) hψinj (K := S)]
    rw [hS]
    simpa using hd0U
  have hdO : ψ.symm d0 ∉ CFSG.Open.pCoreOf 2 (X ⊔ S) := by
    intro hd
    have hmem : ((eA ⟨ψ.symm d0, Subgroup.mem_sup_right hdS⟩ : ↥(X0 ⊔ U3)) : Γ) ∈
        CFSG.Open.pCoreOf 2 (X0 ⊔ U3) :=
      (CFSG.Quasithin.F112R.mem_pCoreOf_iff_of_mulEquiv eA 2
        ⟨ψ.symm d0, Subgroup.mem_sup_right hdS⟩).mp hd
    rw [heA_apply] at hmem
    simp only [Subgroup.coe_mk, MulEquiv.apply_symm_apply] at hmem
    exact hd0O hmem
  refine ⟨hcard, hOcard, hbar, ψ.symm d0, hdS, hdO, ?_⟩
  intro x hxX
  have hx0 : ψ x ∈ X0 := by
    change ψ x ∈ X.map ψ.toMonoidHom
    exact ⟨x, hxX, rfl⟩
  have hmodel := hd0inv (ψ x) hx0
  have hdA : ψ.symm d0 ∈ X ⊔ S := Subgroup.mem_sup_right hdS
  have hxA : x ∈ X ⊔ S := Subgroup.mem_sup_left hxX
  have hmulA : ψ.symm d0 * x * (ψ.symm d0)⁻¹ * x ∈ X ⊔ S :=
    (X ⊔ S).mul_mem ((X ⊔ S).mul_mem ((X ⊔ S).mul_mem hdA hxA) ((X ⊔ S).inv_mem hdA)) hxA
  have hmem : ((eA ⟨ψ.symm d0 * x * (ψ.symm d0)⁻¹ * x, hmulA⟩ : ↥(X0 ⊔ U3)) : Γ) ∈
      CFSG.Open.pCoreOf 2 (X0 ⊔ U3) := by
    rw [heA_apply]
    simpa [map_mul, map_inv] using hmodel
  exact (CFSG.Quasithin.F112R.mem_pCoreOf_iff_of_mulEquiv eA 2
    ⟨ψ.symm d0 * x * (ψ.symm d0)⁻¹ * x, hmulA⟩).mpr hmem


theorem k_L27PermutesS3_holds : K_L27PermutesS3 := by
  intro Y _ _ hL S hS X hX hperm
  have hclass := CFSG.Blueprint.LieModel.statedClassicalModel hL (by decide)
  obtain ⟨e⟩ := CFSG.Open.StatedAPI.nonempty_mulEquiv_sl_three_two_of_psl_two_seven hclass
  have hS' : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤ := by
    simpa [CFSG.Quasithin.IsSylowIn, CFSG.QuasithinUnique.IsSylowTwoOf,
      Subgroup.relIndex] using hS
  obtain ⟨ψ, hψ⟩ := CFSG.Quasithin.Vol2.Ch10.SecB.exists_equiv_map_eq_U3 e hS'
  exact permutesS3_of_equiv ψ hψ hX hperm

theorem k_L27Local_holds : K_L27Local := by
  intro Y _ _ hL S hS
  have hclass := CFSG.Blueprint.LieModel.statedClassicalModel hL (by decide)
  obtain ⟨e⟩ := CFSG.Open.StatedAPI.nonempty_mulEquiv_sl_three_two_of_psl_two_seven hclass
  have hS' : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤ := by
    simpa [CFSG.Quasithin.IsSylowIn, CFSG.QuasithinUnique.IsSylowTwoOf,
      Subgroup.relIndex] using hS
  obtain ⟨ψ, hψ⟩ := CFSG.Quasithin.Vol2.Ch10.SecB.exists_equiv_map_eq_U3 e hS'
  have hψinj : Function.Injective ψ.toMonoidHom := fun a b h => ψ.injective h
  have hψsymminj : Function.Injective ψ.symm.toMonoidHom := fun a b h => ψ.symm.injective h
  have hSsymm : U3.map ψ.symm.toMonoidHom = S := by
    rw [← hψ]
    simpa using (Subgroup.map_symm_eq_iff_map_eq (K := S) (H := S.map ψ.toMonoidHom)
      (e := ψ)).mpr rfl
  have hcenter : Subgroup.center Y = ⊥ := by
    have hmap : (Subgroup.center Y).map ψ.toMonoidHom = Subgroup.center Γ := by
      simpa using (Subgroup.map_center_eq ψ)
    rw [CFSG.LocalAnalysis.ComponentInitial.center_SL_three_zmod_two_eq_bot] at hmap
    exact (Subgroup.map_eq_bot_iff_of_injective (H := Subgroup.center Y)
      (f := ψ.toMonoidHom) hψinj).mp hmap
  obtain ⟨X₁, X₂, hX₁, hX₂, hX₁X₂, hperm₁, hperm₂, hjoin, hbar₁, hbar₂⟩ := l32_local
  set Y₁ : Subgroup Y := X₁.map ψ.symm.toMonoidHom with hY₁def
  set Y₂ : Subgroup Y := X₂.map ψ.symm.toMonoidHom with hY₂def
  have hcardY₁ : Nat.card Y₁ = 3 := by
    rw [hY₁def, Subgroup.card_map_of_injective (f := ψ.symm.toMonoidHom) hψsymminj, hX₁]
  have hcardY₂ : Nat.card Y₂ = 3 := by
    rw [hY₂def, Subgroup.card_map_of_injective (f := ψ.symm.toMonoidHom) hψsymminj, hX₂]
  have hpermY₁ : Permutes Y₁ S := by
    rw [hY₁def]
    have := CFSG.GroupTheory.map_permutes_map ψ.symm.toMonoidHom hperm₁
    rwa [hSsymm] at this
  have hpermY₂ : Permutes Y₂ S := by
    rw [hY₂def]
    have := CFSG.GroupTheory.map_permutes_map ψ.symm.toMonoidHom hperm₂
    rwa [hSsymm] at this
  have hY₁map : Y₁.map ψ.toMonoidHom = X₁ := by
    rw [hY₁def]
    simpa using (Subgroup.map_symm_eq_iff_map_eq (K := X₁) (H := X₁.map ψ.symm.toMonoidHom)
      (e := ψ.symm)).mpr rfl
  have hY₂map : Y₂.map ψ.toMonoidHom = X₂ := by
    rw [hY₂def]
    simpa using (Subgroup.map_symm_eq_iff_map_eq (K := X₂) (H := X₂.map ψ.symm.toMonoidHom)
      (e := ψ.symm)).mpr rfl
  have hY₁Y₂ : Y₁ ≠ Y₂ := by
    intro h
    apply hX₁X₂
    have hmap := congrArg (Subgroup.map ψ.toMonoidHom) h
    rwa [hY₁map, hY₂map] at hmap
  have hjoinY : S ⊔ Y₁ ⊔ Y₂ = ⊤ := by
    have hmodel : U3 ⊔ X₁ ⊔ X₂ = ⊤ := by
      rw [show U3 ⊔ X₁ ⊔ X₂ = X₁ ⊔ X₂ ⊔ U3 by ac_rfl]
      exact hjoin
    have hmap : (S ⊔ Y₁ ⊔ Y₂).map ψ.toMonoidHom = U3 ⊔ X₁ ⊔ X₂ := by
      rw [Subgroup.map_sup, Subgroup.map_sup, hψ, hY₁map, hY₂map]
    have htop : (⊤ : Subgroup Y).map ψ.toMonoidHom = ⊤ := by
      rw [Subgroup.map_top, MonoidHom.range_eq_top.mpr ψ.surjective]
    exact Subgroup.map_injective hψinj (hmap.trans (hmodel.trans htop.symm))
  have hbarY₁ : Nonempty (Bar2 (S ⊔ Y₁) ≃* Equiv.Perm (Fin 3)) := by
    have h := (permutesS3_of_equiv ψ hψ hcardY₁ hpermY₁).2.2.1
    rwa [sup_comm] at h
  have hbarY₂ : Nonempty (Bar2 (S ⊔ Y₂) ≃* Equiv.Perm (Fin 3)) := by
    have h := (permutesS3_of_equiv ψ hψ hcardY₂ hpermY₂).2.2.1
    rwa [sup_comm] at h
  constructor
  · refine ⟨Y₁, hcardY₁, hpermY₁, ?_⟩
    intro hle
    rw [hcenter] at hle
    have hY₁ne : Y₁ ≠ ⊥ := by
      intro h
      rw [h, Subgroup.card_bot] at hcardY₁
      norm_num at hcardY₁
    exact hY₁ne (le_bot_iff.mp hle)
  · exact ⟨Y₁, Y₂, hcardY₁, hcardY₂, hY₁Y₂, hpermY₁, hpermY₂, hjoinY, hbarY₁, hbarY₂⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
