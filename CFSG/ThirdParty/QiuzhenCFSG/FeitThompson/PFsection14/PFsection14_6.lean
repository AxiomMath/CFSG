module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection14.PFsection14_5
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection14.PFsection14_2_Quotient

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 14: theorem (14.6)
-/

noncomputable section

open scoped BigOperators Pointwise

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section14

universe u v w

/-! ## (14.6) -/


public theorem section14_no_prime_divisor_half_with_pm_congruence
    {p r : ℕ}
    (h3p : 3 < p)
    (hr : Nat.Prime r)
    (hr_dvd : r ∣ (p - 1) / 2)
    (hcong : p ∣ r - 1 ∨ p ∣ r + 1) :
    False := by
  have hhalf_pos : 0 < (p - 1) / 2 := by omega
  have hr_le_half : r ≤ (p - 1) / 2 := Nat.le_of_dvd hhalf_pos hr_dvd
  have hhalf_lt_p : (p - 1) / 2 < p := by omega
  have hr_lt_p : r < p := lt_of_le_of_lt hr_le_half hhalf_lt_p
  rcases hcong with hdiv | hdiv
  · rcases hdiv with ⟨k, hk⟩
    have hsub_lt : r - 1 < p := by omega
    by_cases hk0 : k = 0
    · rw [hk0, Nat.mul_zero] at hk
      have hr_le_one : r ≤ 1 := by omega
      exact (not_le_of_gt hr.one_lt) hr_le_one
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
      have hp_le : p ≤ r - 1 := by
        calc
          p ≤ p * k := Nat.le_mul_of_pos_right p hkpos
          _ = r - 1 := hk.symm
      omega
  · rcases hdiv with ⟨k, hk⟩
    have hsum_lt : r + 1 < p := by omega
    by_cases hk0 : k = 0
    · rw [hk0, Nat.mul_zero] at hk
      omega
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
      have hp_le : p ≤ r + 1 := by
        calc
          p ≤ p * k := Nat.le_mul_of_pos_right p hkpos
          _ = r + 1 := hk.symm
      omega

public theorem section14_exists_prime_dvd_half_of_prime_gt_three
    {p : ℕ}
    (hp : Nat.Prime p)
    (h3p : 3 < p) :
    ∃ r, Nat.Prime r ∧ r ∣ (p - 1) / 2 := by
  have hpge4 : 4 ≤ p := by omega
  have hpne4 : p ≠ 4 := by
    intro hp4
    subst p
    exact (by decide : ¬ Nat.Prime 4) hp
  have hpge5 : 5 ≤ p := by omega
  have hhalf_ne_one : (p - 1) / 2 ≠ 1 := by omega
  exact Nat.exists_prime_and_dvd hhalf_ne_one

public theorem section14_square_div_four_eq_half_mul_succ_half
    (n : ℕ) :
    n ^ 2 / 4 = (n / 2) * ((n + 1) / 2) := by
  rcases Nat.mod_two_eq_zero_or_one n with hn | hn
  · have hEven : Even n := Nat.even_iff.mpr hn
    rcases hEven with ⟨k, hk⟩
    subst n
    have hk2 : k + k = 2 * k := by omega
    rw [hk2]
    have h1 : (2 * k) ^ 2 / 4 = k * k := by
      rw [pow_two]
      ring_nf
      rw [Nat.mul_comm]
      exact Nat.mul_div_right (k ^ 2) (by decide : 0 < 4)
    have h2 : (2 * k) / 2 = k := by omega
    have h3 : (2 * k + 1) / 2 = k := by omega
    rw [h1, h2, h3]
  · have hOdd : Odd n := Nat.odd_iff.mpr hn
    rcases hOdd with ⟨k, hk⟩
    subst n
    have h1 : (2 * k + 1) ^ 2 / 4 = k * (k + 1) := by
      have hcalc : (2 * k + 1) ^ 2 = 4 * (k * (k + 1)) + 1 := by ring
      rw [hcalc]
      omega
    have h2 : (2 * k + 1) / 2 = k := by omega
    have h3 : (2 * k + 1 + 1) / 2 = k + 1 := by omega
    rw [h1, h2, h3]

public theorem section14_dvd_square_div_four_of_dvd_half
    {n r : ℕ}
    (hr_dvd : r ∣ n / 2) :
    r ∣ n ^ 2 / 4 := by
  rw [section14_square_div_four_eq_half_mul_succ_half]
  exact dvd_mul_of_dvd_left hr_dvd ((n + 1) / 2)

public theorem section14_sylow_map_to_overgroup_sylow
    {H : Type*} [Group H] [Finite H] {π : Set Nat.Primes} {K : Subgroup H}
    (hKHall : IsHallSubgroup π K) {p : Nat.Primes} (hpπ : p ∈ π)
    (P : Sylow p.val K) :
    ∃ PH : Sylow p.val H, (PH : Subgroup H) = (P : Subgroup K).map K.subtype := by
  classical
  haveI : Fact p.val.Prime := ⟨p.property⟩
  let Psub : Subgroup H := (P : Subgroup K).map K.subtype
  have hPsubp : IsPGroup p.val Psub :=
    IsPGroup.map (p := p.val) (H := (P : Subgroup K)) P.isPGroup' K.subtype
  have hnot_index : ¬ p.val ∣ Psub.index := by
    intro hpidx
    have hidx : Psub.index = (P : Subgroup K).index * K.index := by
      simpa [Psub] using
        (Subgroup.index_map_subtype (H := K) (K := (P : Subgroup K)))
    have hp_prod : p.val ∣ (P : Subgroup K).index * K.index := by
      simpa [hidx] using hpidx
    rcases p.property.dvd_or_dvd hp_prod with hpPidx | hpKidx
    · exact P.not_dvd_index hpPidx
    · exact (hKHall.p_in_pi_of_p_dvd_index p hpKidx) hpπ
  let PH : Sylow p.val H := hPsubp.toSylow hnot_index
  exact ⟨PH, by simp [PH, Psub, IsPGroup.toSylow_coe]⟩

public theorem section14_complement_isHall_compl_of_isHall
    {R : Type*} [Group R] [Finite R] {π : Set Nat.Primes}
    {K D : Subgroup R}
    (hKHall : IsHallSubgroup π K)
    (hcomp : K.IsComplement' D) :
    IsHallSubgroup πᶜ D := by
  classical
  refine isHallSubgroup_of (G := R) (π := πᶜ) (H := D) ?_ ?_
  · intro q hqD hqπ
    have hqKidx : q.val ∣ K.index := by
      simpa [hcomp.symm.index_eq_card] using hqD
    exact (hKHall.p_in_pi_of_p_dvd_index q hqKidx) hqπ
  · intro q hqπc hqDidx
    have hqK : q.val ∣ Nat.card K := by
      simpa [hcomp.index_eq_card] using hqDidx
    exact hqπc (hKHall.p_in_pi_of_p_dvd_card q hqK)

public theorem section14_mf_hallSubgroup_in_ambientDerived
    {G : Type u} [Group G] [Finite G]
    {M MF : Subgroup G}
    (hMF : section16MFSubgroup M MF)
    (hMFleD : MF ≤ ambientDerivedSubgroup M) :
    IsHallSubgroup (subgroupPrimeSet MF)
      (MF.subgroupOf (ambientDerivedSubgroup M)) := by
  classical
  let D : Subgroup G := ambientDerivedSubgroup M
  rcases hMF.1 with ⟨hMFM, _hMFnormM, _hMFnil, hMFHallM⟩
  have hMFleD' : MF ≤ D := by
    simpa [D] using hMFleD
  let Dsub : Subgroup M := D.subgroupOf M
  have hMFcardM : Nat.card (MF.subgroupOf M) = Nat.card MF :=
    natCard_subgroupOf_eq MF M hMFM
  have hMFcardD : Nat.card (MF.subgroupOf D) = Nat.card MF :=
    natCard_subgroupOf_eq MF D hMFleD'
  have hDleM : D ≤ M := section12_ambientDerivedSubgroup_le
  have hMFsub_le_Dsub : MF.subgroupOf M ≤ Dsub := by
    intro x hx
    exact hMFleD' hx
  refine isHallSubgroup_of (G := D) (π := subgroupPrimeSet MF)
    (H := MF.subgroupOf D) ?_ ?_
  · intro p hp
    have hpMF : p.val ∣ Nat.card MF := by
      exact hMFcardD ▸ hp
    exact hMFHallM.p_in_pi_of_p_dvd_card p
      (hMFcardM.symm ▸ hpMF)
  · intro p hpπ hpidx
    have hrel_eq :
        (MF.subgroupOf D).index = (MF.subgroupOf M).relIndex Dsub := by
      have hsub :=
        Subgroup.relIndex_subgroupOf (H := MF) (K := D) (L := M) hDleM
      simpa [Dsub, Subgroup.relIndex] using hsub.symm
    have hidx_dvd :
        (MF.subgroupOf D).index ∣ (MF.subgroupOf M).index := by
      have hrel_dvd :
          (MF.subgroupOf M).relIndex Dsub ∣ (MF.subgroupOf M).index :=
        Subgroup.relIndex_dvd_index_of_le hMFsub_le_Dsub
      simpa [hrel_eq] using hrel_dvd
    exact (hMFHallM.p_in_pi_of_p_dvd_index p (hpidx.trans hidx_dvd)) hpπ

public theorem section14_hall_ambientSylow_to_overgroup
    {G : Type u} [Group G] [Finite G]
    {H K : Subgroup G} (hKH : K ≤ H) {π : Set Nat.Primes}
    (hKHall : IsHallSubgroup π (K.subgroupOf H))
    {p : Nat.Primes} (hpπ : p ∈ π) (P : Sylow p.val K) :
    ∃ PH : Sylow p.val H,
      section10AmbientSylowSubgroup H PH = section10AmbientSylowSubgroup K P := by
  classical
  haveI : Fact p.val.Prime := ⟨p.property⟩
  let Kloc : Subgroup H := K.subgroupOf H
  let e : Kloc ≃* K := Subgroup.subgroupOfEquivOfLe (H := K) (K := H) hKH
  let Ploc : Sylow p.val Kloc :=
    P.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  rcases section14_sylow_map_to_overgroup_sylow
      (H := H) (π := π) (K := Kloc) hKHall hpπ Ploc with
    ⟨PH, hPH⟩
  refine ⟨PH, ?_⟩
  ext x
  constructor
  · intro hx
    change x ∈ (PH : Subgroup H).map H.subtype at hx
    have hx' :
        x ∈ (((Ploc : Subgroup Kloc).map Kloc.subtype : Subgroup H).map H.subtype) := by
      simpa [section10AmbientSylowSubgroup, hPH] using hx
    rcases Subgroup.mem_map.mp hx' with ⟨yH, hyH, rfl⟩
    rcases Subgroup.mem_map.mp hyH with ⟨yKloc, hyPloc, hyKloc_eq⟩
    have hyPloc' : yKloc ∈ (P : Subgroup K).map e.symm.toMonoidHom := by
      simpa [Ploc, Sylow.coe_mapSurjective] using hyPloc
    rcases Subgroup.mem_map.mp hyPloc' with ⟨yK, hyP, hyK_eq⟩
    have hyPamb : ((yK : K) : G) ∈ (P : Subgroup K).map K.subtype :=
      Subgroup.mem_map.mpr ⟨yK, hyP, rfl⟩
    change ((yH : H) : G) ∈ (P : Subgroup K).map K.subtype
    rw [← hyKloc_eq, ← hyK_eq]
    simpa [e, Subgroup.subgroupOfEquivOfLe] using hyPamb
  · intro hx
    change x ∈ (P : Subgroup K).map K.subtype at hx
    rcases Subgroup.mem_map.mp hx with ⟨yK, hyP, rfl⟩
    have hyPloc : (e.symm yK : Kloc) ∈ Ploc := by
      change (e.symm yK : Kloc) ∈
        ((P : Subgroup K).map e.symm.toMonoidHom : Subgroup Kloc)
      exact Subgroup.mem_map.mpr ⟨yK, hyP, rfl⟩
    change ((yK : K) : G) ∈ (PH : Subgroup H).map H.subtype
    have hyH :
        ((e.symm yK : Kloc) : H) ∈
          ((Ploc : Subgroup Kloc).map Kloc.subtype : Subgroup H) :=
      Subgroup.mem_map.mpr ⟨(e.symm yK : Kloc), hyPloc, rfl⟩
    have hyMap :
        ((yK : K) : G) ∈
          (((Ploc : Subgroup Kloc).map Kloc.subtype : Subgroup H).map H.subtype) := by
      refine Subgroup.mem_map.mpr ⟨((e.symm yK : Kloc) : H), hyH, ?_⟩
      simp [e, Subgroup.subgroupOfEquivOfLe]
    simpa [section10AmbientSylowSubgroup, hPH] using hyMap

public theorem section14_exists_nontrivial_pSubgroup_of_prime_dvd_card_subgroup
    {G : Type u} [Group G] [Finite G]
    {A : Subgroup G}
    {r : ℕ}
    (hr : Nat.Prime r)
    (hrA : r ∣ Nat.card A) :
    ∃ R : Subgroup G, R ≤ A ∧ IsPGroup r R ∧ R ≠ ⊥ ∧
      ∃ RA : Sylow r A, R = (RA : Subgroup A).map A.subtype := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  let RA : Sylow r A := Classical.choice (Sylow.nonempty (p := r) (G := A))
  have hRA_ne : (RA : Subgroup A) ≠ ⊥ :=
    Sylow.ne_bot_of_dvd_card (G := A) RA hrA
  let R : Subgroup G := (RA : Subgroup A).map A.subtype
  have hR_le_A : R ≤ A := by
    intro x hx
    change x ∈ (RA : Subgroup A).map A.subtype at hx
    rw [Subgroup.mem_map] at hx
    rcases hx with ⟨a, _ha, rfl⟩
    exact a.property
  have hRp : IsPGroup r R := by
    simpa [R] using
      IsPGroup.map (p := r) (H := (RA : Subgroup A)) RA.isPGroup' A.subtype
  have hR_ne : R ≠ ⊥ := by
    intro hR_bot
    have hRA_bot : (RA : Subgroup A) = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective (H := (RA : Subgroup A))
        (f := A.subtype) A.subtype_injective).1 (by simpa [R] using hR_bot)
    exact hRA_ne hRA_bot
  exact ⟨R, hR_le_A, hRp, hR_ne, RA, rfl⟩

public theorem section14_exists_ambient_sylow_containing_pSubgroup
    {G : Type u} [Group G] [Finite G]
    {A R0 : Subgroup G}
    {r : ℕ}
    (hR0A : R0 ≤ A)
    (hR0p : IsPGroup r R0) :
    ∃ R : Subgroup G, R0 ≤ R ∧ R ≤ A ∧ IsPGroup r R ∧
      ∃ RA : Sylow r A, R = (RA : Subgroup A).map A.subtype := by
  classical
  let R0A : Subgroup A := R0.subgroupOf A
  have hR0A_p : IsPGroup r R0A :=
    hR0p.of_equiv (Subgroup.subgroupOfEquivOfLe (H := R0) (K := A) hR0A).symm
  obtain ⟨RA, hR0A_le_RA⟩ := hR0A_p.exists_le_sylow
  let R : Subgroup G := (RA : Subgroup A).map A.subtype
  have hR0_le_R : R0 ≤ R := by
    intro x hx
    change x ∈ (RA : Subgroup A).map A.subtype
    rw [Subgroup.mem_map]
    refine ⟨⟨x, hR0A hx⟩, ?_, rfl⟩
    exact hR0A_le_RA (by simpa [R0A, Subgroup.mem_subgroupOf] using hx)
  have hR_le_A : R ≤ A := by
    intro x hx
    change x ∈ (RA : Subgroup A).map A.subtype at hx
    rw [Subgroup.mem_map] at hx
    rcases hx with ⟨a, _ha, rfl⟩
    exact a.property
  have hRp : IsPGroup r R := by
    simpa [R] using
      IsPGroup.map (p := r) (H := (RA : Subgroup A)) RA.isPGroup' A.subtype
  exact ⟨R, hR0_le_R, hR_le_A, hRp, RA, rfl⟩

public theorem section14_caseA_prime_dvd_barU_card_of_u_formula
    {G : Type u} [Group G] [Finite G]
    {Smax P U W1 W2 C : Subgroup G}
    {p q u r : ℕ}
    (hcaseA : Section13.case_9_7_a_sourceDataForSection13 Smax P U W1 W2 C p q u)
    (hr_dvd : r ∣ (p - 1) / 2)
    (hu : u = (p - 1) ^ 2 / 4) :
    ∃ _hCU : C ≤ U, ∃ hnormal : (C.subgroupOf U).Normal,
      letI : (C.subgroupOf U).Normal := hnormal
      r ∣ Nat.card (U ⧸ C.subgroupOf U) := by
  rcases hcaseA with ⟨hbarU, _hcaseAdata⟩
  rcases hbarU with ⟨hCU, hnormal, hcard⟩
  have hr_dvd_u : r ∣ u := by
    rw [hu]
    exact section14_dvd_square_div_four_of_dvd_half hr_dvd
  refine ⟨hCU, hnormal, ?_⟩
  letI : (C.subgroupOf U).Normal := hnormal
  rw [hcard]
  exact hr_dvd_u

public theorem section14_caseA_prime_dvd_U_card_of_u_formula
    {G : Type u} [Group G] [Finite G]
    {Smax P U W1 W2 C : Subgroup G}
    {p q u r : ℕ}
    (hcaseA : Section13.case_9_7_a_sourceDataForSection13 Smax P U W1 W2 C p q u)
    (hr_dvd : r ∣ (p - 1) / 2)
    (hu : u = (p - 1) ^ 2 / 4) :
    r ∣ Nat.card U := by
  rcases section14_caseA_prime_dvd_barU_card_of_u_formula hcaseA hr_dvd hu with
    ⟨_hCU, hnormal, hbarU_r_dvd⟩
  letI : (C.subgroupOf U).Normal := hnormal
  exact hbarU_r_dvd.trans (Subgroup.card_quotient_dvd_card (s := C.subgroupOf U))

public theorem section14_caseA_exists_nontrivial_rSubgroup_U_of_u_formula
    {G : Type u} [Group G] [Finite G]
    {Smax P U W1 W2 C : Subgroup G}
    {p q u r : ℕ}
    (hr : Nat.Prime r)
    (hcaseA : Section13.case_9_7_a_sourceDataForSection13 Smax P U W1 W2 C p q u)
    (hr_dvd : r ∣ (p - 1) / 2)
    (hu : u = (p - 1) ^ 2 / 4) :
    ∃ R0 : Subgroup G, R0 ≤ U ∧ IsPGroup r R0 ∧ R0 ≠ ⊥ ∧
      ∃ R0U : Sylow r U, R0 = (R0U : Subgroup U).map U.subtype :=
  section14_exists_nontrivial_pSubgroup_of_prime_dvd_card_subgroup hr
    (section14_caseA_prime_dvd_U_card_of_u_formula hcaseA hr_dvd hu)

public theorem section14_prime_dvd_pm_of_dvd_square_sub_one
    {p r : ℕ}
    (hp : Nat.Prime p)
    (hr : Nat.Prime r)
    (hdiv : p ∣ r ^ 2 - 1) :
    p ∣ r - 1 ∨ p ∣ r + 1 := by
  have hfac : r ^ 2 - 1 = (r - 1) * (r + 1) := by
    apply Nat.cast_injective (R := ℤ)
    have hr1 : 1 ≤ r := hr.one_le
    have hr2 : 1 ≤ r ^ 2 := by nlinarith [hr1]
    rw [Nat.cast_sub hr2, Nat.cast_mul, Nat.cast_sub hr1]
    norm_num [pow_two]
    ring
  rw [hfac] at hdiv
  exact hp.dvd_or_dvd hdiv

public theorem section14_square_sub_one_eq_mul_pred_succ
    {r : ℕ} (hr1 : 1 ≤ r) :
    r ^ 2 - 1 = (r - 1) * (r + 1) := by
  apply Nat.cast_injective (R := ℤ)
  have hr2 : 1 ≤ r ^ 2 := by nlinarith
  rw [Nat.cast_sub hr2, Nat.cast_mul, Nat.cast_sub hr1]
  norm_num [pow_two]
  ring

public theorem section14_fixedPointFree_card_prime_square_congruence
    {A E : Type*} [Group A] [Finite A] [Group E] [Finite E]
    [MulDistribMulAction A E]
    {p r : ℕ}
    (hcardA : Nat.card A = p)
    (hr : Nat.Prime r)
    (hcardE : Nat.card E = r ∨ Nat.card E = r ^ 2)
    (hfree : ∀ a : A, a ≠ 1 → ∀ e : E, a • e = e → e = 1) :
    p ∣ r ^ 2 - 1 := by
  classical
  letI : Fintype A := Fintype.ofFinite A
  letI : Fintype E := Fintype.ofFinite E
  have hdivAE : Nat.card A ∣ Nat.card E - 1 := by
    let α := {e : E // e ≠ 1}
    letI : MulAction A α :=
      { smul := fun a e => ⟨a • (e : E), by
          intro h
          apply e.2
          have h' := congrArg (fun x : E => a⁻¹ • x) h
          simpa using h'⟩
        one_smul := by
          intro e
          apply Subtype.ext
          change (1 : A) • (e : E) = (e : E)
          simp
        mul_smul := by
          intro a b e
          apply Subtype.ext
          change (a * b) • (e : E) = a • (b • (e : E))
          rw [mul_smul] }
    have hstab : ∀ e : α, MulAction.stabilizer A e = ⊥ := by
      intro e
      rw [eq_bot_iff]
      intro a ha
      have hae : a • e = e := by
        simpa [MulAction.mem_stabilizer_iff] using ha
      by_contra ha_not_bot
      have ha_ne : a ≠ 1 := by
        intro ha1
        apply ha_not_bot
        simp [ha1]
      have hfix : a • (e : E) = (e : E) := congrArg Subtype.val hae
      exact e.2 (hfree a ha_ne (e : E) hfix)
    have hcard_equiv := Nat.card_congr (MulAction.selfEquivOrbitsQuotientProd hstab)
    have hcardα : Nat.card α = Nat.card E - 1 := by
      letI : Fintype E := Fintype.ofFinite E
      letI : Fintype α := Fintype.ofFinite α
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
      change Fintype.card {e : E // e ≠ 1} = Fintype.card E - 1
      simp
    rw [hcardα, Nat.card_prod] at hcard_equiv
    exact ⟨Nat.card (Quotient (MulAction.orbitRel A α)), by
      rw [mul_comm]
      exact hcard_equiv⟩
  have hcardA_fintype : Fintype.card A = p := by
    simpa [Nat.card_eq_fintype_card] using hcardA
  have hdiv : p ∣ Fintype.card E - 1 := by
    simpa [hcardA_fintype] using hdivAE
  rcases hcardE with hcardE | hcardE
  · have hdiv_r : p ∣ r - 1 := by
      have hcardE_fintype : Fintype.card E = r := by
        simpa [Nat.card_eq_fintype_card] using hcardE
      simpa [hcardE_fintype] using hdiv
    rw [section14_square_sub_one_eq_mul_pred_succ hr.one_le]
    exact dvd_mul_of_dvd_left hdiv_r (r + 1)
  · have hcardE_fintype : Fintype.card E = r ^ 2 := by
      simpa [Nat.card_eq_fintype_card] using hcardE
    simpa [hcardE_fintype] using hdiv

public theorem section14_frobeniusWithKernel_invariant_subgroup_fixedPointFree_action
    {G : Type u} [Group G] [Finite G]
    {L H A Ω : Subgroup G}
    (hfrob : Section7.frobeniusWithKernel L H)
    (hA_le_L : A ≤ L)
    (hA_not_H : ∀ a : A, a ≠ 1 → (a : G) ∉ H)
    (hΩ_le_H : Ω ≤ H)
    (hA_norm_Ω : A ≤ Subgroup.normalizer (Ω : Set G)) :
    ∃ _hAction : MulDistribMulAction A Ω,
      ∀ a : A, a ≠ 1 → ∀ e : Ω, a • e = e → e = 1 := by
  classical
  letI : Subgroup.Normalizes A Ω := ⟨hA_norm_Ω⟩
  refine ⟨inferInstance, ?_⟩
  intro a ha e hfix
  have hconj : (a : G) * (e : G) * (a : G)⁻¹ = (e : G) := by
    simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using
      congrArg Subtype.val hfix
  have hcomm : (a : G) * (e : G) = (e : G) * (a : G) := by
    have h := congrArg (fun t : G => t * (a : G)) hconj
    simpa [mul_assoc] using h
  have hcent_eq : Section2.centralizerIn H (a : G) = ⊥ :=
    Section13.section13_frobeniusWithKernel_centralizerIn_eq_bot_of_not_mem
      hfrob (a : G) (hA_le_L a.property) (hA_not_H a ha)
  have he_cent : (e : G) ∈ Section2.centralizerIn H (a : G) := by
    refine ⟨hΩ_le_H e.property, ?_⟩
    change (e : G) ∈ Subgroup.centralizer ({(a : G)} : Set G)
    exact Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm
  have he_bot : (e : G) ∈ (⊥ : Subgroup G) := by
    simpa [hcent_eq] using he_cent
  exact Subtype.ext (by simpa using he_bot)


public theorem section14_U_card_eq_u_of_pf13_12_source
    {G : Type u} [Group G] [Finite G]
    {Smax Tmax W W1 W2 P Q U V C D : Subgroup G}
    {Sfam : Finset (Section1.ClassFunction Smax)}
    {Tfam : Finset (Section1.ClassFunction Tmax)}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {p q u v c d : ℕ}
    (hsource : Section13.hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    Nat.card U = u := by
  have hc_one : c = 1 :=
    Section13.theorem_13_12 Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d hsource
  rcases hsource with
    ⟨_hcase, _hSTypeP, _hTTypeP, _hp, _hq, _hC, _hD, _hc, _hd, hUcard,
      _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hNotation, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau, _hChoice, _hMin, _hFourSixS, _hFourSixT⟩
  rw [hUcard, hc_one, Nat.mul_one]

public theorem section14_caseA_quotient_embedding_data
    {G : Type u} [Group G] [Finite G]
    {Smax P U W1 W2 C : Subgroup G}
    {p q u : ℕ}
    (hcaseA : Section13.case_9_7_a_sourceDataForSection13 Smax P U W1 W2 C p q u) :
    ∃ a : ℕ, a ∣ p - 1 ∧ C ≤ U ∧
      ∃ hnormal : (C.subgroupOf U).Normal,
        letI : (C.subgroupOf U).Normal := hnormal
        ∃ φ : (U ⧸ C.subgroupOf U) →* (Fin (q - 1) → Multiplicative (ZMod a)),
          Function.Injective φ := by
  rcases hcaseA with ⟨_hbarU, a, hcaseAdata⟩
  rcases hcaseAdata with
    ⟨_h92, _hH0le, _hquot, _hp, _hq, _hred, _hH, _hcard, ha, hembed⟩
  rcases hembed with ⟨hCU, hnormal, φ, hφinj⟩
  exact ⟨a, ha, hCU, hnormal, φ, hφinj⟩

public theorem section14_natCard_fin_fun_multiplicative_zmod_q3
    {a q : ℕ}
    (ha0 : a ≠ 0)
    (hq3 : q = 3) :
    Nat.card (Fin (q - 1) → Multiplicative (ZMod a)) = a ^ 2 := by
  haveI : NeZero a := ⟨ha0⟩
  subst q
  rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin]
  rw [show Fintype.card (Multiplicative (ZMod a)) = a by simp [ZMod.card]]

public theorem section14_caseA_quotient_card_le_square_of_q_eq_three
    {G : Type u} [Group G] [Finite G]
    {Smax P U W1 W2 C : Subgroup G}
    {p q u : ℕ}
    (hcaseA : Section13.case_9_7_a_sourceDataForSection13 Smax P U W1 W2 C p q u)
    (hq3 : q = 3) :
    ∃ a : ℕ, a ∣ p - 1 ∧ u ≤ a ^ 2 := by
  rcases hcaseA with ⟨hbarU, a, hcaseAdata⟩
  rcases hcaseAdata with
    ⟨_h92, _hH0le, _hquot, hp, _hq, _hred, _hH, _hcard, ha, hembed⟩
  rcases hbarU with ⟨_hCUbar, _hnormalBar, hcardBar⟩
  rcases hembed with ⟨_hCUinj, hnormalInj, φ, hφinj⟩
  have ha_pos : 0 < a := by
    by_contra hnot
    have ha0 : a = 0 := Nat.eq_zero_of_not_pos hnot
    rw [ha0, Nat.zero_dvd] at ha
    exact (not_le_of_gt hp.one_lt) (Nat.sub_eq_zero_iff_le.mp ha)
  haveI : NeZero a := ⟨ha_pos.ne'⟩
  letI : (C.subgroupOf U).Normal := hnormalInj
  have hquot_le :
      Nat.card (U ⧸ C.subgroupOf U) ≤
        Nat.card (Fin (q - 1) → Multiplicative (ZMod a)) :=
    Nat.card_le_card_of_injective φ hφinj
  have htarget :
      Nat.card (Fin (q - 1) → Multiplicative (ZMod a)) = a ^ 2 :=
    section14_natCard_fin_fun_multiplicative_zmod_q3 ha_pos.ne' hq3
  refine ⟨a, ha, ?_⟩
  rw [← hcardBar]
  exact hquot_le.trans_eq htarget

public theorem section14_omegaOneCenter_ne_bot_of_nontrivial_pSubgroup
    {G : Type u} [Group G] [Finite G]
    {p : Nat.Primes} {P : Subgroup G}
    (hPp : IsPGroup p.val P) [Nontrivial P] :
    section10OmegaOneCenter p P ≠ ⊥ := by
  classical
  haveI : Fact p.val.Prime := ⟨p.property⟩
  have hZ_nontrivial : Nontrivial (Subgroup.center P) := hPp.center_nontrivial
  have hpdvd_center : p.val ∣ Nat.card (Subgroup.center P) := by
    have hcenter_p : IsPGroup p.val (Subgroup.center P) :=
      hPp.to_subgroup (Subgroup.center P)
    rcases (IsPGroup.nontrivial_iff_card
        (p := p.val) (G := Subgroup.center P) (hG := hcenter_p)).1 hZ_nontrivial with
      ⟨n, hn, hcard⟩
    rw [hcard]
    exact dvd_pow_self p.val (Nat.ne_of_gt hn)
  have hΩlocal_ne_bot : Ω₁Z p.val P ≠ ⊥ := by
    simpa [Ω₁Z] using
      omega₁_map_subtype_ne_bot (M := Subgroup.center P) (p := p.val) hpdvd_center
  simpa [section10OmegaOneCenter] using
    section10_map_subtype_ne_bot_of_ne_bot (G := G) (M := P) hΩlocal_ne_bot

public theorem section14_omegaOneCenter_card_eq_prime_or_prime_sq_of_le_square
    {G : Type u} [Group G] [Finite G]
    {R0 R : Subgroup G} {rp : Nat.Primes}
    (hR0_ne : R0 ≠ ⊥)
    (hR0R : R0 ≤ R)
    (hRp : IsPGroup rp.val R)
    (hcard_le : Nat.card (section10OmegaOneCenter rp R) ≤ rp.val ^ 2) :
    Nat.card (section10OmegaOneCenter rp R) = rp.val ∨
      Nat.card (section10OmegaOneCenter rp R) = rp.val ^ 2 := by
  classical
  haveI : Fact rp.val.Prime := ⟨rp.property⟩
  have hR_ne : R ≠ ⊥ := by
    intro hRbot
    exact hR0_ne (le_bot_iff.mp (by simpa [hRbot] using hR0R))
  haveI : Nontrivial R := (Subgroup.nontrivial_iff_ne_bot R).2 hR_ne
  let Z : Subgroup G := section10OmegaOneCenter rp R
  have hZne : Z ≠ ⊥ :=
    section14_omegaOneCenter_ne_bot_of_nontrivial_pSubgroup hRp
  have hZelem : IsElementaryAbelian rp.val Z := by
    have hΩelem : IsElementaryAbelian rp.val (Ω₁Z rp.val R) :=
      omega1Z_isElementaryAbelian (p := rp.val) (R := R)
    letI : IsElementaryAbelian rp.val (Ω₁Z rp.val R) := hΩelem
    exact section10_isElementaryAbelian_map_pre
      (G := R) (p := rp.val) (A := Ω₁Z rp.val R) (G' := G) R.subtype
  have hZp : IsPGroup rp.val Z := by
    letI : IsElementaryAbelian rp.val Z := hZelem
    exact IsElementaryAbelian.isPGroup rp.val Z
  rcases hZp.exists_card_eq with ⟨k, hk⟩
  have hk_pos : 0 < k := by
    by_contra hk_not
    have hk0 : k = 0 := by omega
    have hZcard_one : Nat.card Z = 1 := by
      simpa [hk0] using hk
    exact hZne ((Subgroup.card_eq_one (H := Z)).1 hZcard_one)
  have hk_le_two : k ≤ 2 := by
    have hcard_le_Z : Nat.card Z ≤ rp.val ^ 2 := by
      simpa [Z] using hcard_le
    rw [hk] at hcard_le_Z
    exact (Nat.pow_le_pow_iff_right rp.property.one_lt).1 hcard_le_Z
  have hk_cases : k = 1 ∨ k = 2 := by omega
  rcases hk_cases with hk1 | hk2
  · left
    simpa [Z, hk1] using hk
  · right
    simpa [Z, hk2] using hk

public theorem section14_characteristicSubgroupIn_of_mf_sylow
    {G : Type u} [Group G] [Finite G]
    {L H R : Subgroup G} {r : ℕ}
    (hr : Nat.Prime r)
    (hLHMf : section16MFSubgroup L H)
    (hRH : R ≤ H)
    (hR_sylow : ∃ RH : Sylow r H, R = (RH : Subgroup H).map H.subtype) :
    characteristicSubgroupIn R H := by
  haveI : Fact (Nat.Prime r) := ⟨hr⟩
  rcases hLHMf.1 with ⟨_hHL, _hHnormal, hHnil, _hHall⟩
  rcases hR_sylow with ⟨RH, hR_eq⟩
  have hRH_normal : (RH : Subgroup H).Normal := by
    letI : Group.IsNilpotent H := hHnil
    exact Group.IsNilpotent.sylow_normal (p := r) inferInstance RH
  have hRH_char : (RH : Subgroup H).Characteristic :=
    Sylow.characteristic_of_normal RH hRH_normal
  have hRsub_eq : R.subgroupOf H = (RH : Subgroup H) := by
    apply Subgroup.map_injective (f := H.subtype) H.subtype_injective
    calc
      (R.subgroupOf H).map H.subtype = R := Subgroup.map_subgroupOf_eq_of_le hRH
      _ = (RH : Subgroup H).map H.subtype := hR_eq
  refine ⟨hRH, ?_⟩
  rw [hRsub_eq]
  exact hRH_char

public theorem section14_caseA_omegaOneCenter_normalizer_of_mf_sylow
    {G : Type u} [Group G] [Finite G]
    {L H W1 W2 R : Subgroup G}
    {r : ℕ} {y : G} {rp : Nat.Primes}
    (hr : Nat.Prime r)
    (hLHMf : section16MFSubgroup L H)
    (hsemi : Section2.IsInternalSemidirectProduct L H (W1 ⊔ W2.conjBy y))
    (hRH : R ≤ H)
    (hR_sylow : ∃ RH : Sylow r H, R = (RH : Subgroup H).map H.subtype) :
    W2.conjBy y ≤
      Subgroup.normalizer (section10OmegaOneCenter rp R : Set G) := by
  have hRchar : characteristicSubgroupIn R H :=
    section14_characteristicSubgroupIn_of_mf_sylow hr hLHMf hRH hR_sylow
  have hjoin_norm_R :
      W1 ⊔ W2.conjBy y ≤ Subgroup.normalizer (R : Set G) :=
    section14_semidirect_right_le_normalizer_of_characteristic hsemi hRchar
  have hW2normR : W2.conjBy y ≤ Subgroup.normalizer (R : Set G) :=
    le_sup_right.trans hjoin_norm_R
  exact hW2normR.trans (section11_normalizer_le_normalizer_omegaOneCenter rp R)

public theorem section14_omegaOneCenter_card_bound_of_le_rank_two
    {G : Type u} [Group G] [Finite G]
    {R0 R : Subgroup G} {rp : Nat.Primes}
    (hΩR0 : section10OmegaOneCenter rp R ≤ R0)
    (hR0_rank : groupRank R0 ≤ 2) :
    Nat.card (section10OmegaOneCenter rp R) ≤ rp.val ^ 2 := by
  classical
  haveI : Fact rp.val.Prime := ⟨rp.property⟩
  let Ω : Subgroup G := section10OmegaOneCenter rp R
  let Ω0 : Subgroup R0 := Ω.subgroupOf R0
  have hΩcard : Nat.card Ω0 = Nat.card Ω :=
    natCard_subgroupOf_eq Ω R0 hΩR0
  have hΩelem : IsElementaryAbelian rp.val Ω := by
    have hΩlocal : IsElementaryAbelian rp.val (Ω₁Z rp.val R) :=
      omega1Z_isElementaryAbelian (p := rp.val) (R := R)
    letI : IsElementaryAbelian rp.val (Ω₁Z rp.val R) := hΩlocal
    exact section10_isElementaryAbelian_map_pre
      (G := R) (p := rp.val) (A := Ω₁Z rp.val R) (G' := G) R.subtype
  have hΩ0elem : IsElementaryAbelian rp.val Ω0 := by
    letI : IsElementaryAbelian rp.val Ω := hΩelem
    exact IsElementaryAbelian.subgroupOf hΩR0
  letI : IsElementaryAbelian rp.val Ω0 := hΩ0elem
  have hΩ0p : IsPGroup rp.val Ω0 := IsElementaryAbelian.isPGroup rp.val Ω0
  have hΩ0comm : IsMulCommutative Ω0 := inferInstance
  have hΩ0rank : generatorRank Ω0 ≤ 2 :=
    (generatorRank_le_groupRank_of_isPGroup_abelian_subgroup
      (R := R0) (q := rp.val) hΩ0p hΩ0comm).trans hR0_rank
  have hΩ0exp : Monoid.exponent Ω0 ∣ rp.val :=
    IsElementaryAbelian.exponent_dvd_p rp.val Ω0
  have hΩ0card : Nat.card Ω0 ≤ rp.val ^ 2 :=
    natCard_abelian_subgroup_le_p_sq_of_rank_le_two_and_exponent_dvd_p
      (R := R0) (p := rp.val) hΩ0p hΩ0comm hΩ0rank hΩ0exp
  rw [← hΩcard]
  exact hΩ0card

public theorem section14_omegaOneCenter_le_center_map
    {G : Type u} [Group G] [Finite G]
    {R : Subgroup G} {rp : Nat.Primes} :
    section10OmegaOneCenter rp R ≤ (Subgroup.center R).map R.subtype := by
  simpa [section10OmegaOneCenter] using
    (Subgroup.map_mono (f := R.subtype) (omega1Z_le_center rp.val R))

public theorem section14_generatorRank_le_two_of_injective_to_fin_two_cyclic
    {A C : Type*} [Group A] [Finite A] [Group C] [Finite C] [IsCyclic C]
    (φ : A →* (Fin 2 → C)) (hφ : Function.Injective φ) :
    generatorRank A ≤ 2 := by
  classical
  let π0 : A →* C :=
    { toFun := fun a => φ a 0
      map_one' := by simp
      map_mul' := by intro a b; simp }
  let K : Subgroup A := π0.ker
  have hKcyc : IsCyclic K := by
    let π1K : K →* C :=
      { toFun := fun k => φ (k : A) 1
        map_one' := by simp
        map_mul' := by intro a b; simp }
    have hπ1K_inj : Function.Injective π1K := by
      intro x y hxy
      apply Subtype.ext
      apply hφ
      funext i
      fin_cases i
      · have hxker : (x : A) ∈ π0.ker := by simp [K]
        have hx0' : π0 (x : A) = 1 := hxker
        have hx0 : φ (x : A) 0 = 1 := by simpa [π0] using hx0'
        have hyker : (y : A) ∈ π0.ker := by simp [K]
        have hy0' : π0 (y : A) = 1 := hyker
        have hy0 : φ (y : A) 0 = 1 := by simpa [π0] using hy0'
        exact hx0.trans hy0.symm
      · exact hxy
    exact isCyclic_of_injective π1K hπ1K_inj
  have hquotcyc : IsCyclic (A ⧸ K) := by
    let e : A ⧸ π0.ker ≃* π0.range := QuotientGroup.quotientKerEquivRange π0
    have hrange_cyc : IsCyclic π0.range :=
      isCyclic_of_injective π0.range.subtype π0.range.subtype_injective
    have : IsCyclic (A ⧸ π0.ker) := (MulEquiv.isCyclic e).2 hrange_cyc
    simpa [K] using this
  exact generatorRank_le_two_of_isCyclic_subgroup_quotient hKcyc hquotcyc

public theorem section14_groupRank_le_two_of_injective_to_fin_two_cyclic
    {A C : Type*} [Group A] [Finite A] [Group C] [Finite C] [IsCyclic C]
    (φ : A →* (Fin 2 → C)) (hφ : Function.Injective φ) :
    groupRank A ≤ 2 := by
  classical
  rw [groupRank]
  refine csSup_le ?_ ?_
  · exact ⟨0, 2, by decide, Nat.zero_le _⟩
  · intro n hn
    rcases hn with ⟨q, _hq, hnq⟩
    have hprimeRank_le : primeRank q A ≤ 2 := by
      rw [primeRank]
      refine csSup_le ?_ ?_
      · exact ⟨0, ⊥, IsPGroup.of_bot (p := q) (G := A), inferInstance, Nat.zero_le _⟩
      · intro m hm
        rcases hm with ⟨B, _hBp, _hBcomm, hmB⟩
        let φB : B →* (Fin 2 → C) := φ.comp B.subtype
        have hφB_inj : Function.Injective φB := by
          intro x y hxy
          apply Subtype.ext
          exact hφ hxy
        exact hmB.trans
          (section14_generatorRank_le_two_of_injective_to_fin_two_cyclic φB hφB_inj)
    exact hnq.trans hprimeRank_le

public theorem section14_natCard_dvd_of_isCyclic_injective_to_fin_two_zmod
    {A : Type*} [Group A] [Finite A] [IsCyclic A]
    {a : ℕ} (φ : A →* (Fin 2 → Multiplicative (ZMod a)))
    (hφ : Function.Injective φ) :
    Nat.card A ∣ a := by
  have hExpA :
      Monoid.exponent A ∣ Monoid.exponent (Fin 2 → Multiplicative (ZMod a)) :=
    Monoid.exponent_dvd_of_monoidHom φ hφ
  have hExpTarget :
      Monoid.exponent (Fin 2 → Multiplicative (ZMod a)) ∣ a := by
    refine Monoid.exponent_dvd_of_forall_pow_eq_one ?_
    intro f
    ext i
    simp
  rw [← IsCyclic.exponent_eq_card (α := A)]
  exact hExpA.trans hExpTarget

public theorem section14_caseA_R0_groupRank_le_two_of_quotient_embedding
    {G : Type u} [Group G] [Finite G]
    {Smax Tmax W W1 W2 P Q U V C D R0 : Subgroup G}
    {Sfam : Finset (Section1.ClassFunction Smax)}
    {Tfam : Finset (Section1.ClassFunction Tmax)}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {p q u v c d : ℕ}
    (hsource : Section13.hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hcaseA : Section13.case_9_7_a_sourceDataForSection13 Smax P U W1 W2 C p q u)
    (hq3 : q = 3)
    (hR0U : R0 ≤ U) :
    groupRank R0 ≤ 2 := by
  classical
  subst q
  have hCbot : C = ⊥ :=
    section14_C_eq_bot_of_pf13_12_source hsource
  rcases section14_caseA_quotient_embedding_data hcaseA with
    ⟨a, ha, _hCU, hnormal, φ, hφinj⟩
  have hp : Nat.Prime p := by
    rcases hcaseA with ⟨_hbarU, _a, hcaseAdata⟩
    rcases hcaseAdata with
      ⟨_h92, _hH0le, _hquot, hp, _hq, _hred, _hH, _hcard, _ha, _hembed⟩
    exact hp
  have ha_pos : 0 < a := by
    by_contra hnot
    have ha0 : a = 0 := Nat.eq_zero_of_not_pos hnot
    rw [ha0, Nat.zero_dvd] at ha
    exact (not_le_of_gt hp.one_lt) (Nat.sub_eq_zero_iff_le.mp ha)
  haveI : NeZero a := ⟨ha_pos.ne'⟩
  haveI : IsCyclic (Multiplicative (ZMod a)) := by infer_instance
  letI : (C.subgroupOf U).Normal := hnormal
  have hCsub_bot : C.subgroupOf U = ⊥ :=
    section14_subgroupOf_eq_bot_of_eq_bot hCbot
  let eU : U ⧸ C.subgroupOf U ≃* U :=
    (QuotientGroup.quotientMulEquivOfEq hCsub_bot).trans
      (QuotientGroup.quotientBot (G := U))
  let iR0U : R0 →* U :=
    { toFun := fun x => ⟨(x : G), hR0U x.property⟩
      map_one' := rfl
      map_mul' := by intro x y; rfl }
  let φR0 : R0 →* (Fin 2 → Multiplicative (ZMod a)) :=
    φ.comp (eU.symm.toMonoidHom.comp iR0U)
  have hφR0_inj : Function.Injective φR0 := by
    intro x y hxy
    have hquot : eU.symm (iR0U x) = eU.symm (iR0U y) := hφinj hxy
    have hUeq : iR0U x = iR0U y := eU.symm.injective hquot
    apply Subtype.ext
    exact congrArg (fun z : U => (z : G)) hUeq
  exact section14_groupRank_le_two_of_injective_to_fin_two_cyclic φR0 hφR0_inj

public theorem section14_caseA_R0_card_dvd_embedding_of_isCyclic
    {G : Type u} [Group G] [Finite G]
    {Smax Tmax W W1 W2 P Q U V C D R0 : Subgroup G}
    {Sfam : Finset (Section1.ClassFunction Smax)}
    {Tfam : Finset (Section1.ClassFunction Tmax)}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {p q u v c d : ℕ}
    (hsource : Section13.hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hcaseA : Section13.case_9_7_a_sourceDataForSection13 Smax P U W1 W2 C p q u)
    (hq3 : q = 3)
    (hR0U : R0 ≤ U)
    (hR0cyc : IsCyclic R0) :
    ∃ a : ℕ, a ∣ p - 1 ∧ Nat.card R0 ∣ a := by
  classical
  subst q
  have hCbot : C = ⊥ :=
    section14_C_eq_bot_of_pf13_12_source hsource
  rcases section14_caseA_quotient_embedding_data hcaseA with
    ⟨a, ha, _hCU, hnormal, φ, hφinj⟩
  have hp : Nat.Prime p := by
    rcases hcaseA with ⟨_hbarU, _a, hcaseAdata⟩
    rcases hcaseAdata with
      ⟨_h92, _hH0le, _hquot, hp, _hq, _hred, _hH, _hcard, _ha, _hembed⟩
    exact hp
  have ha_pos : 0 < a := by
    by_contra hnot
    have ha0 : a = 0 := Nat.eq_zero_of_not_pos hnot
    rw [ha0, Nat.zero_dvd] at ha
    exact (not_le_of_gt hp.one_lt) (Nat.sub_eq_zero_iff_le.mp ha)
  haveI : NeZero a := ⟨ha_pos.ne'⟩
  letI : (C.subgroupOf U).Normal := hnormal
  have hCsub_bot : C.subgroupOf U = ⊥ :=
    section14_subgroupOf_eq_bot_of_eq_bot hCbot
  let eU : U ⧸ C.subgroupOf U ≃* U :=
    (QuotientGroup.quotientMulEquivOfEq hCsub_bot).trans
      (QuotientGroup.quotientBot (G := U))
  let iR0U : R0 →* U :=
    { toFun := fun x => ⟨(x : G), hR0U x.property⟩
      map_one' := rfl
      map_mul' := by intro x y; rfl }
  let φR0 : R0 →* (Fin 2 → Multiplicative (ZMod a)) :=
    φ.comp (eU.symm.toMonoidHom.comp iR0U)
  have hφR0_inj : Function.Injective φR0 := by
    intro x y hxy
    have hquot : eU.symm (iR0U x) = eU.symm (iR0U y) := hφinj hxy
    have hUeq : iR0U x = iR0U y := eU.symm.injective hquot
    apply Subtype.ext
    exact congrArg (fun z : U => (z : G)) hUeq
  haveI : IsCyclic R0 := hR0cyc
  exact ⟨a, ha, section14_natCard_dvd_of_isCyclic_injective_to_fin_two_zmod
    φR0 hφR0_inj⟩

public theorem section14_R0_sylow_factorization_eq_U
    {G : Type u} [Group G] [Finite G]
    {U R0 : Subgroup G} {r : ℕ}
    (hr : Nat.Prime r)
    (hR0_sylow : ∃ R0U : Sylow r U, R0 = (R0U : Subgroup U).map U.subtype) :
    Nat.factorization (Nat.card R0) r = Nat.factorization (Nat.card U) r := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  rcases hR0_sylow with ⟨R0U, hR0_eq⟩
  have hcard : Nat.card R0 = Nat.card (R0U : Subgroup U) := by
    rw [hR0_eq]
    exact Subgroup.card_map_of_injective (K := (R0U : Subgroup U)) (f := U.subtype)
      U.subtype_injective
  rw [hcard]
  exact section8_factorization_card_sylow R0U

public theorem section14_sylow_square_half_cyclic_arithmetic_contra
    {b r a n : ℕ}
    (hr : Nat.Prime r)
    (hb_pos : 0 < b)
    (hr_dvd_b : r ∣ b)
    (hb_odd : Odd b)
    (hn_fact : Nat.factorization n r = Nat.factorization (b ^ 2) r)
    (hn_ne : n ≠ 0)
    (hn_dvd_a : n ∣ a)
    (ha_dvd_two_b : a ∣ 2 * b) :
    False := by
  have hr_ne_two : r ≠ 2 := by
    intro hr2
    subst r
    have htwo_dvd_b : 2 ∣ b := hr_dvd_b
    exact (Nat.not_even_iff_odd.mpr hb_odd) (even_iff_two_dvd.mpr htwo_dvd_b)
  have ha_ne : a ≠ 0 := by
    intro ha0
    rcases ha_dvd_two_b with ⟨k, hk⟩
    rw [ha0, Nat.zero_mul] at hk
    omega
  have hle_na : Nat.factorization n r ≤ Nat.factorization a r :=
    Nat.factorization_le_factorization_of_dvd_right hn_dvd_a hn_ne ha_ne
  have hle_atwob : Nat.factorization a r ≤ Nat.factorization (2 * b) r :=
    Nat.factorization_le_factorization_of_dvd_right ha_dvd_two_b ha_ne (by omega)
  have hle : Nat.factorization n r ≤ Nat.factorization (2 * b) r :=
    hle_na.trans hle_atwob
  have hfact_twob : Nat.factorization (2 * b) r = Nat.factorization b r := by
    rw [Nat.factorization_mul (by decide : 2 ≠ 0) (Nat.ne_of_gt hb_pos)]
    have hnot : ¬ r ∣ 2 := by
      intro h
      have hrle2 : r ≤ 2 := Nat.le_of_dvd (by decide : 0 < 2) h
      have h2le : 2 ≤ r := hr.two_le
      exact hr_ne_two (le_antisymm hrle2 h2le)
    have hfac2 : Nat.factorization 2 r = 0 :=
      Nat.factorization_eq_zero_of_not_dvd hnot
    simp [hfac2]
  have hfact_b_pos : 0 < Nat.factorization b r := by
    exact (Nat.Prime.dvd_iff_one_le_factorization hr (Nat.ne_of_gt hb_pos)).1 hr_dvd_b
  rw [hn_fact] at hle
  rw [show Nat.factorization (b ^ 2) r = 2 * Nat.factorization b r by
    simp [Nat.factorization_pow]] at hle
  rw [hfact_twob] at hle
  omega

public theorem section14_subgroup_le_sylow_image_of_le_pSubgroup_intermediate
    {G : Type u} [Group G] [Finite G]
    {A P R Z : Subgroup G} {p : ℕ}
    (hPR : P ≤ R)
    (hRp : IsPGroup p R)
    (hP_sylow : ∃ PA : Sylow p A, P = (PA : Subgroup A).map A.subtype)
    (hZA : Z ≤ A)
    (hZR : Z ≤ R) :
    Z ≤ P := by
  classical
  rcases hP_sylow with ⟨PA, hP_eq⟩
  let Iamb : Subgroup G := R ⊓ A
  let IA : Subgroup A := Iamb.subgroupOf A
  let IR : Subgroup R := Iamb.subgroupOf R
  have hIRp : IsPGroup p IR :=
    hRp.to_subgroup IR
  have hIAp : IsPGroup p IA := by
    let eR : IR ≃* Iamb :=
      Subgroup.subgroupOfEquivOfLe (H := Iamb) (K := R) inf_le_left
    let eA : IA ≃* Iamb :=
      Subgroup.subgroupOfEquivOfLe (H := Iamb) (K := A) inf_le_right
    exact hIRp.of_equiv (eR.trans eA.symm)
  have hPA_le_IA : (PA : Subgroup A) ≤ IA := by
    intro a ha
    have hmemP : (a : G) ∈ P := by
      rw [hP_eq]
      rw [Subgroup.mem_map]
      exact ⟨a, ha, rfl⟩
    exact ⟨hPR hmemP, a.property⟩
  have hIA_eq : IA = (PA : Subgroup A) :=
    PA.is_maximal' hIAp hPA_le_IA
  intro z hz
  have hzIA : (⟨z, hZA hz⟩ : A) ∈ IA :=
    ⟨hZR hz, hZA hz⟩
  have hzPA : (⟨z, hZA hz⟩ : A) ∈ (PA : Subgroup A) := by
    simpa [hIA_eq] using hzIA
  rw [hP_eq]
  rw [Subgroup.mem_map]
  exact ⟨⟨z, hZA hz⟩, hzPA, rfl⟩


public theorem section14_center_map_le_centralizer_singleton_of_mem
    {G : Type u} [Group G]
    {R : Subgroup G} {x : G}
    (hxR : x ∈ R) :
    (Subgroup.center R).map R.subtype ≤ Subgroup.centralizer ({x} : Set G) := by
  intro z hz
  rw [Subgroup.mem_map] at hz
  rcases hz with ⟨zc, hzc, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  let xR : R := ⟨x, hxR⟩
  have hcomm : xR * zc = zc * xR := (Subgroup.mem_center_iff.mp hzc) xR
  simpa [xR] using congrArg Subtype.val hcomm.symm

public theorem section14_mem_normalizer_of_conjugateSet_eq
    {G : Type u} [Group G]
    {X : Set G} {g : G}
    (hX : section16ConjugateSet X g = X) :
    g ∈ Subgroup.normalizer X := by
  change ∀ y : G, y ∈ X ↔ g * y * g⁻¹ ∈ X
  intro y
  constructor
  · intro hy
    rw [← hX]
    exact ⟨y, hy, rfl⟩
  · intro hy
    have hmem : g * y * g⁻¹ ∈ section16ConjugateSet X g := by
      simpa [hX] using hy
    rcases hmem with ⟨x, hx, hxy⟩
    have hyx : y = x := by
      calc
        y = g⁻¹ * (g * y * g⁻¹) * g := by group
        _ = g⁻¹ * (g * x * g⁻¹) * g := by rw [hxy]
        _ = x := by group
    simpa [hyx] using hx

public theorem section14_centralizer_singleton_le_of_tiWithNormalizer_mem
    {G : Type u} [Group G]
    {X : Set G} {N : Subgroup G} {x : G}
    (hXti : section16TISubsetWithNormalizer X N)
    (hxX : x ∈ X)
    (hxne : x ≠ 1) :
    Subgroup.centralizer ({x} : Set G) ≤ N := by
  intro c hc
  rcases hXti with ⟨hTI, hNorm⟩
  have hxConj : x ∈ section16ConjugateSet X c := by
    refine ⟨x, hxX, ?_⟩
    have hcomm : c * x = x * c :=
      Subgroup.mem_centralizer_singleton_iff.mp hc
    have hfix : c * x * c⁻¹ = x := by
      rw [hcomm]
      simp [mul_assoc]
    exact hfix.symm
  have hcNorm : c ∈ Subgroup.normalizer X := by
    rcases hTI c with hsame | hsmall
    · exact section14_mem_normalizer_of_conjugateSet_eq hsame
    · have hxone : x ∈ ({1} : Set G) := hsmall ⟨hxX, hxConj⟩
      exact False.elim (hxne (by simpa using hxone))
  simpa [hNorm] using hcNorm

public theorem section14_normalizer_nonidentityElements_eq
    {G : Type u} [Group G]
    (H : Subgroup G) :
    Subgroup.normalizer (section16NonidentityElements (H : Set G)) =
      Subgroup.normalizer (H : Set G) := by
  apply le_antisymm
  · intro g hg
    change ∀ x : G, x ∈ section16NonidentityElements (H : Set G) ↔
      g * x * g⁻¹ ∈ section16NonidentityElements (H : Set G) at hg
    change ∀ x : G, x ∈ H ↔ g * x * g⁻¹ ∈ H
    intro x
    constructor
    · intro hxH
      by_cases hx1 : x = 1
      · simp [hx1]
      · have hxSharp : x ∈ section16NonidentityElements (H : Set G) :=
          ⟨hxH, hx1⟩
        exact ((hg x).1 hxSharp).1
    · intro hxConjH
      by_cases hx1 : x = 1
      · simp [hx1]
      · have hxConj_ne : g * x * g⁻¹ ≠ 1 := by
          intro h
          apply hx1
          have h' := congrArg (fun y : G => g⁻¹ * y * g) h
          simpa [mul_assoc] using h'
        have hxConjSharp :
            g * x * g⁻¹ ∈ section16NonidentityElements (H : Set G) :=
          ⟨hxConjH, hxConj_ne⟩
        exact ((hg x).2 hxConjSharp).1
  · intro g hg
    change ∀ x : G, x ∈ H ↔ g * x * g⁻¹ ∈ H at hg
    change ∀ x : G, x ∈ section16NonidentityElements (H : Set G) ↔
      g * x * g⁻¹ ∈ section16NonidentityElements (H : Set G)
    intro x
    constructor
    · intro hx
      refine ⟨(hg x).1 hx.1, ?_⟩
      intro h
      exact hx.2 (by
        have h' := congrArg (fun y : G => g⁻¹ * y * g) h
        simpa [mul_assoc] using h')
    · intro hx
      refine ⟨(hg x).2 hx.1, ?_⟩
      intro hx1
      exact hx.2 (by simp [hx1])

public theorem section14_center_map_le_Smax_of_centralizer_source
    {G : Type u} [Group G]
    {Smax R0 R : Subgroup G}
    (hR0R : R0 ≤ R)
    (hcentralizer : ∃ x : G, x ∈ R0 ∧ x ≠ 1 ∧
      Subgroup.centralizer ({x} : Set G) ≤ Smax) :
    (Subgroup.center R).map R.subtype ≤ Smax := by
  rcases hcentralizer with ⟨x, hxR0, _hx_ne, hxcentS⟩
  exact (section14_center_map_le_centralizer_singleton_of_mem
    (R := R) (x := x) (hR0R hxR0)).trans hxcentS


public theorem section14_mem_hatMsigma_of_centralizerIn_ne_bot
    {G : Type u} [Group G] [Finite G]
    {Smax P : Subgroup G} {x : G}
    (hPσ : P ≤ section10Msigma Smax)
    (hxS : x ∈ Smax)
    (hcentP : elementCentralizerIn P x ≠ ⊥) :
    x ∈ section16HatMsigmaSet Smax := by
  refine ⟨hxS, ?_⟩
  have hle : elementCentralizerIn P x ≤
      elementCentralizerIn (section10Msigma Smax) x := by
    intro y hy
    exact ⟨hPσ hy.1, hy.2⟩
  intro hbot
  apply hcentP
  exact le_bot_iff.mp (by
    intro y hy
    simpa [hbot] using hle hy)


public theorem section14_exists_elementCentralizerIn_of_BG116
    {G : Type u} [Group G] [Finite G]
    {P R0 : Subgroup G} {r : ℕ}
    (hr : Nat.Prime r)
    (hR0normP : R0 ≤ Subgroup.normalizer (P : Set G))
    (hR0comm : IsMulCommutative R0)
    (hR0p : IsPGroup r R0)
    (hR0noncyc : ¬ IsCyclic R0)
    (hcop : Nat.Coprime r (Nat.card P))
    (hPne : P ≠ ⊥) :
    ∃ x : G, x ∈ R0 ∧ x ≠ 1 ∧ elementCentralizerIn P x ≠ ⊥ := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  letI : MulDistribMulAction (↥R0) (↥P) :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer (G := G) R0 P hR0normP
  have htop :
      (⨆ (a : R0) (_ : a ≠ 1),
        fixedPointSubgroup (↥(Subgroup.zpowers a)) P) = ⊤ := by
    let commR0 : CommGroup (↥R0) := IsMulCommutative.instCommGroup
    letI : CommGroup (↥R0) := commR0
    letI : Group (↥R0) := commR0.toGroup
    have hR0p' : IsPGroup r (↥R0) := by
      intro a
      obtain ⟨k, hk⟩ := hR0p a
      refine ⟨k, ?_⟩
      exact Subtype.ext (congrArg Subtype.val hk)
    haveI : Fact (IsPGroup r (↥R0)) := ⟨hR0p'⟩
    have hR0noncyc' : ¬ @IsCyclic (↥R0) ZPow.toPow := by
      intro h
      apply hR0noncyc
      rcases h with ⟨a, ha⟩
      constructor
      refine ⟨a, fun x => ?_⟩
      obtain ⟨n, hn⟩ := ha x
      refine ⟨n, ?_⟩
      exact Subtype.ext (congrArg Subtype.val hn)
    simpa using proposition_1_16_a (G := (↥P)) (A := (↥R0)) r hcop hR0noncyc'
  by_contra hnone
  have hfix_bot :
      ∀ a : R0, ∀ ha : a ≠ 1,
        fixedPointSubgroup (↥(Subgroup.zpowers a)) P = ⊥ := by
    intro a ha
    have hcent_bot : elementCentralizerIn P (a : G) = ⊥ := by
      by_contra hcent_ne
      apply hnone
      exact ⟨(a : G), a.property, (by intro h; exact ha (Subtype.ext h)), hcent_ne⟩
    have hfix_eq := fixedPointSubgroup_zpowers_subgroup_conj_eq_elementCentralizerIn
      P R0 hR0normP a
    rw [hfix_eq]
    ext z
    constructor
    · intro hz
      have hzcent : (z : G) ∈ elementCentralizerIn P (a : G) := by
        simpa [Subgroup.mem_subgroupOf] using hz
      have hzbot : (z : G) ∈ (⊥ : Subgroup G) := by
        simpa [hcent_bot] using hzcent
      have hzone : (z : G) = 1 := by simpa using hzbot
      exact Subtype.ext hzone
    · intro hz
      have hzone : z = 1 := by simpa using hz
      rw [hzone]
      exact Subgroup.one_mem ((elementCentralizerIn P (a : G)).subgroupOf P)
  have hiSup_bot :
      (⨆ (a : R0) (_ : a ≠ 1),
        fixedPointSubgroup (↥(Subgroup.zpowers a)) P) = ⊥ := by
    apply le_antisymm
    · exact iSup_le fun a => iSup_le fun ha => by
        rw [hfix_bot a ha]
    · exact bot_le
  apply hPne
  rw [eq_bot_iff]
  intro p hp
  have hpbot : (⟨p, hp⟩ : P) ∈ (⊥ : Subgroup P) := by
    have hptop : (⟨p, hp⟩ : P) ∈ (⊤ : Subgroup P) := trivial
    simpa [← htop, hiSup_bot] using hptop
  have hpone : (⟨p, hp⟩ : P) = 1 := by simpa using hpbot
  simpa using congrArg Subtype.val hpone

public theorem section14_caseA_P_le_Msigma_source_adapter
    {G : Type u} [Group G] [Finite G]
    {Smax Tmax W W1 W2 P Q U V C D : Subgroup G}
    {Sfam : Finset (Section1.ClassFunction Smax)}
    {Tfam : Finset (Section1.ClassFunction Tmax)}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {p q u v c d : ℕ}
    (hsource : Section13.hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    P ≤ section10Msigma Smax := by
  rcases hsource with
    ⟨hcase, hSTypeP, _hTTypeP, _hp, _hq, _hC, _hD, _hc, _hd, _hUcard,
      _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hNotation, _hDadeDiff,
      _hZeroDegree, _hConjIndex, _hConjBetaTau, _hChoice,
      hmin, _hFourSixS, _hFourSixT⟩
  rcases hcase with
    ⟨_hprod, _hcyc, _hW1ne, _hW2ne, _hnorm, hSmax, _hTmax, _hSMF,
      _hTMF, _hSeq, _hTeq, _hSdisj, _hTdisj, _hST, _hTypeII, _hSType,
      _hTType, _hCover⟩
  rcases hSTypeP with
    ⟨hSmaxMF, _hW1cyc, _hW1ne, _hW1hall, _hW1comp, _hUleDer, _hUnil,
      _hW1normU, _hcompPU, _hPnoncyc, _hSecond, _hFitEq, _hFitLe, _hW2le,
      _hW2cyc, _hW2ne, _hCentralizer, _hHatNorm⟩
  letI : IsMinCE G := hmin
  have hMF15 : section15MFSubgroup Smax P := by
    simpa [section16MFSubgroup, section16NilpotentNormalHallIn,
      section15MFSubgroup, section15NilpotentNormalHallIn] using hSmaxMF
  exact (theorem_15_2_chain (G := G) (M := Smax) (MF := P) hSmax hMF15).2.1

public theorem section14_caseA_r_coprime_card_P_source_adapter
    {G : Type u} [Group G] [Finite G]
    {Smax Tmax W W1 W2 P Q U V C D : Subgroup G}
    {Sfam : Finset (Section1.ClassFunction Smax)}
    {Tfam : Finset (Section1.ClassFunction Tmax)}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {p q u v c d r : ℕ}
    (hsource : Section13.hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hq3 : q = 3)
    (hqp : q < p)
    (hr : Nat.Prime r)
    (hr_dvd : r ∣ (p - 1) / 2) :
    Nat.Coprime r (Nat.card P) := by
  have hctx : hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d := ⟨hsource, hqp⟩
  rcases section14_context_primes_of_sourceData hctx with ⟨hp, _hq⟩
  rcases Section13.theorem_13_2 Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d hsource with
    ⟨_hSmaxMF, _htypeS, _htypeII, _hUcomm, _hUfrob, hPelem, _hPcard,
      _huBound, _hSfamCoh, _hA0TI, _hTauS⟩
  have hr_ne_p : r ≠ p := by
    have h3p : 3 < p := by
      simpa [hq3] using hqp
    have hhalf_pos : 0 < (p - 1) / 2 := by omega
    have hr_le_half : r ≤ (p - 1) / 2 := Nat.le_of_dvd hhalf_pos hr_dvd
    have hhalf_lt_p : (p - 1) / 2 < p := by omega
    exact ne_of_lt (lt_of_le_of_lt hr_le_half hhalf_lt_p)
  letI : IsElementaryAbelian p P := hPelem
  exact section14_coprime_card_of_isElementaryAbelian_of_ne
    (Q := P) hr hp hr_ne_p

public theorem section14_caseA_R0_sylow_in_Smax_source_adapter
    {G : Type u} [Group G] [Finite G]
    {Smax Tmax W W1 W2 P Q U V C D R0 : Subgroup G}
    {Sfam : Finset (Section1.ClassFunction Smax)}
    {Tfam : Finset (Section1.ClassFunction Tmax)}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {p q u v c d r : ℕ} {rp : Nat.Primes}
    (hsource : Section13.hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hrp : rp.val = r)
    (hR0U : R0 ≤ U)
    (hR0p : IsPGroup r R0)
    (hR0_ne : R0 ≠ ⊥)
    (hR0_sylow : ∃ R0U : Sylow r U, R0 = (R0U : Subgroup U).map U.subtype) :
    ∃ R0S : Sylow rp.val Smax,
      R0 = section10AmbientSylowSubgroup Smax R0S := by
  classical
  subst r
  let D0 : Subgroup G := ambientDerivedSubgroup Smax
  rcases hsource with
    ⟨hcase, hSTypeP, _hTTypeP, _hp, _hq, _hC, _hD, _hc, _hd, _hUcard,
      _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hNotation, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau, _hChoice, _hMin, _hFourSixS, _hFourSixT⟩
  rcases hcase with
    ⟨_hprod, _hcyc, _hW1ne_case, _hW2ne_case, _hnorm, hSmax, _hTmax,
      _hSMF_case, _hTMF_case, _hSeq, _hTeq, _hSdisj, _hTdisj, _hST,
      _hTypeII, _hSType, _hTType, _hCover⟩
  have hSTypeP_orig := hSTypeP
  rcases hSTypeP with
    ⟨hSmaxMF, _hW1cyc, _hW1ne, hW1Hall, hScompW1, hUleDer, _hUnil,
      _hW1normU, hcompPU, _hPnoncyc, _hSecond, _hFitEq, _hFitLe, _hW2le,
      _hW2cyc, _hW2ne, _hCentralizer, _hHatNorm⟩
  have hPHallD :
      IsHallSubgroup (subgroupPrimeSet P) (P.subgroupOf D0) := by
    simpa [D0] using
      section14_mf_hallSubgroup_in_ambientDerived (G := G) hSmaxMF hcompPU.1
  have hPnormD : section10NormalIn P D0 := by
    simpa [D0] using
      Section13.section13_mf_normalIn_ambientDerived_of_typeP
        (M := Smax) (MF := P) (U := U) (W1 := W1) (W2 := W2)
        hSTypeP_orig
  have hCompLocal :
      (P.subgroupOf D0).IsComplement' (U.subgroupOf D0) := by
    have hcomp' :
        (U.subgroupOf D0).IsComplement' (P.subgroupOf D0) :=
      Section13.section13_complementIn_of_normal_isComplement'
        (G := G) (H := D0) (K := P) (L := U)
        (by simpa [D0] using hcompPU) (by simpa [D0] using hPnormD)
    exact hcomp'.symm
  have hUHallD :
      IsHallSubgroup (subgroupPrimeSet P)ᶜ (U.subgroupOf D0) :=
    section14_complement_isHall_compl_of_isHall hPHallD hCompLocal
  haveI : Fact rp.val.Prime := ⟨rp.property⟩
  haveI : Nontrivial R0 := (Subgroup.nontrivial_iff_ne_bot R0).2 hR0_ne
  have hrp_dvd_R0 : rp.val ∣ Nat.card R0 := by
    rcases (IsPGroup.nontrivial_iff_card
        (p := rp.val) (G := R0) (hG := hR0p)).1 inferInstance with
      ⟨n, hn, hcard⟩
    rw [hcard]
    exact dvd_pow_self rp.val (Nat.ne_of_gt hn)
  have hrp_dvd_U : rp.val ∣ Nat.card U :=
    hrp_dvd_R0.trans (Subgroup.card_dvd_of_le hR0U)
  have hpUloc_card : rp.val ∣ Nat.card (U.subgroupOf D0) := by
    have hcardUloc : Nat.card (U.subgroupOf D0) = Nat.card U :=
      natCard_subgroupOf_eq U D0 (by simpa [D0] using hUleDer)
    rw [hcardUloc]
    exact hrp_dvd_U
  have hpUHallD : rp ∈ (subgroupPrimeSet P)ᶜ :=
    hUHallD.p_in_pi_of_p_dvd_card rp hpUloc_card
  rcases hR0_sylow with ⟨R0U_rp, hR0_eq⟩
  have hR0_eq_rp : R0 = section10AmbientSylowSubgroup U R0U_rp := by
    simpa [section10AmbientSylowSubgroup] using hR0_eq
  rcases section14_hall_ambientSylow_to_overgroup
      (G := G) (H := D0) (K := U) (by simpa [D0] using hUleDer)
      hUHallD hpUHallD R0U_rp with
    ⟨R0D, hR0Damb⟩
  have hDnormS : section10NormalIn D0 Smax := by
    simpa [D0] using (section12_normalIn_ambientDerivedSubgroup (G := G) (E := Smax))
  have hDHallOf : section16HallSubgroupOf D0 Smax :=
    Section13.section13_complementIn_left_hallSubgroupOf_of_right_hallSubgroupOf
      (G := G) (H := Smax) (K := D0) (L := W1)
      (by simpa [D0] using hScompW1) hDnormS hW1Hall
  rcases hDHallOf with ⟨hDleS, hDHallS⟩
  have hpD : rp ∈ subgroupPrimeSet D0 := by
    have hpDcard : rp.val ∣ Nat.card D0 :=
      hrp_dvd_U.trans (Subgroup.card_dvd_of_le (by simpa [D0] using hUleDer))
    simpa [subgroupPrimeSet] using hpDcard
  rcases section14_hall_ambientSylow_to_overgroup
      (G := G) (H := Smax) (K := D0) hDleS hDHallS hpD R0D with
    ⟨R0S, hR0Samb⟩
  refine ⟨R0S, ?_⟩
  calc
    R0 = section10AmbientSylowSubgroup U R0U_rp := hR0_eq_rp
    _ = section10AmbientSylowSubgroup D0 R0D := hR0Damb.symm
    _ = section10AmbientSylowSubgroup Smax R0S := hR0Samb.symm

public theorem section14_caseA_BG116_inputs_source_adapter
    {G : Type u} [Group G] [Finite G]
    {Smax Tmax W W1 W2 P Q U V C D L H R0 R : Subgroup G}
    {Sfam : Finset (Section1.ClassFunction Smax)}
    {Tfam : Finset (Section1.ClassFunction Tmax)}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {p q u v c d r : ℕ}
    {y : G} {rp : Nat.Primes}
    (_hsource : Section13.hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_h10 : Section13.theorem_13_10_hypothesis Smax P C Sfam p q u)
    (_hnotT : ¬ Section13.theorem_13_10_hypothesis Tmax Q D Tfam q p v)
    (_hq3 : q = 3)
    (_hqp : q < p)
    (_hLHMf : section16MFSubgroup L H)
    (_hUH : U ≤ H)
    (_hcaseA : Section13.case_9_7_a_sourceDataForSection13 Smax P U W1 W2 C p q u)
    (_hrp : rp.val = r)
    (_hr_dvd : r ∣ (p - 1) / 2)
    (_hu : u = (p - 1) ^ 2 / 4)
    (_hyQ : y ∈ Q)
    (_hsemi : Section2.IsInternalSemidirectProduct L H (W1 ⊔ W2.conjBy y))
    (_hR0U : R0 ≤ U)
    (_hR0p : IsPGroup r R0)
    (_hR0_ne : R0 ≠ ⊥)
    (_hR0_sylow : ∃ R0U : Sylow r U, R0 = (R0U : Subgroup U).map U.subtype)
    (_hR0R : R0 ≤ R)
    (_hRH : R ≤ H)
    (_hRp : IsPGroup r R)
    (_hR_sylow : ∃ RH : Sylow r H, R = (RH : Subgroup H).map H.subtype) :
    P ≤ section10Msigma Smax ∧
      ¬ IsCyclic R0 ∧
        Nat.Coprime r (Nat.card P) := by
  have hPσ : P ≤ section10Msigma Smax :=
    section14_caseA_P_le_Msigma_source_adapter _hsource
  have hcop : Nat.Coprime r (Nat.card P) :=
    section14_caseA_r_coprime_card_P_source_adapter _hsource _hq3 _hqp
      (by simpa [← _hrp] using rp.property) _hr_dvd
  have hR0noncyc : ¬ IsCyclic R0 := by
    intro hR0cyc
    have hr : Nat.Prime r := by
      rw [← _hrp]
      exact rp.property
    rcases section14_caseA_R0_card_dvd_embedding_of_isCyclic
        (Smax := Smax) (Tmax := Tmax) (W := W) (W1 := W1) (W2 := W2)
        (P := P) (Q := Q) (U := U) (V := V) (C := C) (D := D)
        (R0 := R0) (Sfam := Sfam) (Tfam := Tfam) (τS := τS) (τT := τT)
        _hsource _hcaseA _hq3 _hR0U hR0cyc with
      ⟨a, ha_dvd_pred, hR0card_dvd_a⟩
    let b : ℕ := (p - 1) / 2
    have hp : Nat.Prime p := by
      have hctx : hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
          Sfam Tfam τS τT p q u v c d := ⟨_hsource, _hqp⟩
      exact (section14_context_primes_of_sourceData hctx).1
    have hp_gt_three : 3 < p := by
      simpa [_hq3] using _hqp
    have hpEven : Even (p - 1) :=
      hp.even_sub_one (by omega)
    have hpred_eq : p - 1 = 2 * b := by
      have h2dvd : 2 ∣ p - 1 := even_iff_two_dvd.mp hpEven
      have hmul : (p - 1) / 2 * 2 = p - 1 := Nat.div_mul_cancel h2dvd
      dsimp [b]
      omega
    have hb_pos : 0 < b := by
      dsimp [b]
      omega
    have hUcard_square : Nat.card U = b ^ 2 := by
      have hUcard : Nat.card U = (p - 1) ^ 2 / 4 := by
        rw [section14_U_card_eq_u_of_pf13_12_source _hsource, _hu]
      have hsquare : (p - 1) ^ 2 / 4 = b ^ 2 := by
        dsimp [b]
        rcases hpEven with ⟨k, hk⟩
        rw [hk]
        have hk2 : k + k = 2 * k := by omega
        rw [hk2]
        have hdiv : (2 * k) / 2 = k := by omega
        rw [hdiv]
        have hcalc : (2 * k) ^ 2 / 4 = k ^ 2 := by
          rw [pow_two]
          ring_nf
          rw [Nat.mul_comm]
          exact Nat.mul_div_right (k ^ 2) (by decide : 0 < 4)
        exact hcalc
      exact hUcard.trans hsquare
    have hUodd : Odd (Nat.card U) := by
      rcases _hsource with
        ⟨_hcase, _hSTypeP, _hTTypeP, _hp, _hq, _hC, _hD, _hc, _hd, _hUcard,
          _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hNotation, _hDadeDiff,
          _hZeroDegree, _hConjIndex, _hConjBetaTau, _hChoice,
          hmin, _hFourSixS, _hFourSixT⟩
      letI : IsMinCE G := hmin
      exact odd_of_card_dvd IsMinCE.odd_order (Subgroup.card_subgroup_dvd_card U)
    have hb_odd : Odd b := by
      have hbsq_odd : Odd (b ^ 2) := by
        rw [hUcard_square] at hUodd
        exact hUodd
      rw [pow_two] at hbsq_odd
      exact Nat.Odd.of_mul_left hbsq_odd
    have hR0_fact :
        Nat.factorization (Nat.card R0) r = Nat.factorization (b ^ 2) r := by
      calc
        Nat.factorization (Nat.card R0) r = Nat.factorization (Nat.card U) r :=
          section14_R0_sylow_factorization_eq_U hr _hR0_sylow
        _ = Nat.factorization (b ^ 2) r := by rw [hUcard_square]
    have ha_dvd_two_b : a ∣ 2 * b := by
      simpa [hpred_eq] using ha_dvd_pred
    exact section14_sylow_square_half_cyclic_arithmetic_contra
      hr hb_pos _hr_dvd hb_odd hR0_fact Nat.card_pos.ne' hR0card_dvd_a ha_dvd_two_b
  exact ⟨hPσ, hR0noncyc, hcop⟩

public theorem section14_caseA_centralizerInP_element_source_adapter
    {G : Type u} [Group G] [Finite G]
    {Smax Tmax W W1 W2 P Q U V C D L H R0 R : Subgroup G}
    {Sfam : Finset (Section1.ClassFunction Smax)}
    {Tfam : Finset (Section1.ClassFunction Tmax)}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {p q u v c d r : ℕ}
    {y : G} {rp : Nat.Primes}
    (_hsource : Section13.hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_h10 : Section13.theorem_13_10_hypothesis Smax P C Sfam p q u)
    (_hnotT : ¬ Section13.theorem_13_10_hypothesis Tmax Q D Tfam q p v)
    (_hq3 : q = 3)
    (_hqp : q < p)
    (_hLHMf : section16MFSubgroup L H)
    (_hUH : U ≤ H)
    (_hcaseA : Section13.case_9_7_a_sourceDataForSection13 Smax P U W1 W2 C p q u)
    (_hrp : rp.val = r)
    (_hr_dvd : r ∣ (p - 1) / 2)
    (_hu : u = (p - 1) ^ 2 / 4)
    (_hyQ : y ∈ Q)
    (_hsemi : Section2.IsInternalSemidirectProduct L H (W1 ⊔ W2.conjBy y))
    (_hR0U : R0 ≤ U)
    (_hR0p : IsPGroup r R0)
    (_hR0_ne : R0 ≠ ⊥)
    (_hR0_sylow : ∃ R0U : Sylow r U, R0 = (R0U : Subgroup U).map U.subtype)
    (_hR0R : R0 ≤ R)
    (_hRH : R ≤ H)
    (_hRp : IsPGroup r R)
    (_hR_sylow : ∃ RH : Sylow r H, R = (RH : Subgroup H).map H.subtype) :
    P ≤ section10Msigma Smax ∧
      ∃ x : G, x ∈ R0 ∧ x ≠ 1 ∧ elementCentralizerIn P x ≠ ⊥ := by
  rcases section14_caseA_BG116_inputs_source_adapter
      (Smax := Smax) (Tmax := Tmax) (W := W) (W1 := W1) (W2 := W2)
      (P := P) (Q := Q) (U := U) (V := V) (C := C) (D := D)
      (L := L) (H := H) (R0 := R0) (R := R) (Sfam := Sfam)
      (Tfam := Tfam) (τS := τS) (τT := τT) (p := p) (q := q)
      (u := u) (v := v) (c := c) (d := d) (r := r) (y := y) (rp := rp)
      _hsource _h10 _hnotT _hq3 _hqp _hLHMf _hUH _hcaseA _hrp _hr_dvd _hu
      _hyQ _hsemi _hR0U _hR0p _hR0_ne _hR0_sylow _hR0R _hRH _hRp
      _hR_sylow with
    ⟨hPσ, hR0noncyc, hcop⟩
  have h132 := Section13.theorem_13_2 Smax Tmax W W1 W2 P Q U V C D
    Sfam Tfam τS τT p q u v c d _hsource
  rcases _hsource with
    ⟨_hcase, hSTypeP, _hTTypeP, _hp, _hq, _hC, _hD, _hc, _hd, _hUcard,
      _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hNotation, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau, _hChoice, _hMin, _hFourSixS, _hFourSixT⟩
  rcases hSTypeP with
    ⟨hSmaxMF, _hW1cyc, _hW1ne, _hW1hall, _hW1comp, hUleDer, _hUnil,
      _hW1normU, _hcompPU, hPnoncyc, _hSecond, _hFitEq, _hFitLe, _hW2le,
      _hW2cyc, _hW2ne, _hCentralizer, _hHatNorm⟩
  rcases hSmaxMF with ⟨⟨hPS, hPnormal, _hPnil, _hPHall⟩, _hmax⟩
  have hSmax_norm_P : Smax ≤ Subgroup.normalizer (P : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (H := P) (K := Smax) hPS).1
      hPnormal
  have hR0normP : R0 ≤ Subgroup.normalizer (P : Set G) := by
    intro x hxR0
    exact hSmax_norm_P (section12_ambientDerivedSubgroup_le (hUleDer (_hR0U hxR0)))
  rcases h132 with
    ⟨_hSmaxMF, _htypeS, _htypeII, hUcomm, _hUfrob, _hPelem, _hPcard,
      _huBound, _hSfamCoh, _hA0TI, _hTauS⟩
  have hR0comm : IsMulCommutative R0 := by
    constructor
    constructor
    intro x y
    apply Subtype.ext
    show ((x * y : R0) : G) = ((y * x : R0) : G)
    change (x : G) * (y : G) = (y : G) * (x : G)
    let xU : U := ⟨(x : G), _hR0U x.property⟩
    let yU : U := ⟨(y : G), _hR0U y.property⟩
    have hxy : xU * yU = yU * xU := hUcomm.is_comm.comm xU yU
    exact congrArg (fun z : U => (z : G)) hxy
  have hPne : P ≠ ⊥ := by
    intro hbot
    apply hPnoncyc
    rw [hbot]
    infer_instance
  have hr : Nat.Prime r := by
    rw [← _hrp]
    exact rp.property
  exact ⟨hPσ,
    section14_exists_elementCentralizerIn_of_BG116 hr hR0normP hR0comm
      _hR0p hR0noncyc hcop hPne⟩

public theorem section14_caseA_hatMsigma_element_source_adapter
    {G : Type u} [Group G] [Finite G]
    {Smax Tmax W W1 W2 P Q U V C D L H R0 R : Subgroup G}
    {Sfam : Finset (Section1.ClassFunction Smax)}
    {Tfam : Finset (Section1.ClassFunction Tmax)}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {p q u v c d r : ℕ}
    {y : G} {rp : Nat.Primes}
    (_hsource : Section13.hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_h10 : Section13.theorem_13_10_hypothesis Smax P C Sfam p q u)
    (_hnotT : ¬ Section13.theorem_13_10_hypothesis Tmax Q D Tfam q p v)
    (_hq3 : q = 3)
    (_hqp : q < p)
    (_hLHMf : section16MFSubgroup L H)
    (_hUH : U ≤ H)
    (_hcaseA : Section13.case_9_7_a_sourceDataForSection13 Smax P U W1 W2 C p q u)
    (_hrp : rp.val = r)
    (_hr_dvd : r ∣ (p - 1) / 2)
    (_hu : u = (p - 1) ^ 2 / 4)
    (_hyQ : y ∈ Q)
    (_hsemi : Section2.IsInternalSemidirectProduct L H (W1 ⊔ W2.conjBy y))
    (_hR0U : R0 ≤ U)
    (_hR0p : IsPGroup r R0)
    (_hR0_ne : R0 ≠ ⊥)
    (_hR0_sylow : ∃ R0U : Sylow r U, R0 = (R0U : Subgroup U).map U.subtype)
    (_hR0R : R0 ≤ R)
    (_hRH : R ≤ H)
    (_hRp : IsPGroup r R)
    (_hR_sylow : ∃ RH : Sylow r H, R = (RH : Subgroup H).map H.subtype) :
    ∃ x : G, x ∈ R0 ∧ x ≠ 1 ∧
        x ∈ section16HatMsigmaSet Smax := by
  rcases section14_caseA_centralizerInP_element_source_adapter
      (Smax := Smax) (Tmax := Tmax) (W := W) (W1 := W1) (W2 := W2)
      (P := P) (Q := Q) (U := U) (V := V) (C := C) (D := D)
      (L := L) (H := H) (R0 := R0) (R := R) (Sfam := Sfam)
      (Tfam := Tfam) (τS := τS) (τT := τT) (p := p) (q := q)
      (u := u) (v := v) (c := c) (d := d) (r := r) (y := y) (rp := rp)
      _hsource _h10 _hnotT _hq3 _hqp _hLHMf _hUH _hcaseA _hrp _hr_dvd _hu
      _hyQ _hsemi _hR0U _hR0p _hR0_ne _hR0_sylow _hR0R _hRH _hRp
      _hR_sylow with
    ⟨hPσ, hxPkg⟩
  rcases _hsource with
    ⟨_hcase, hSTypeP, _hTTypeP, _hp, _hq, _hC, _hD, _hc, _hd, _hUcard,
      _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hNotation, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau, _hChoice, _hMin, _hFourSixS, _hFourSixT⟩
  rcases hSTypeP with
    ⟨_hSmaxMF, _hW1cyc, _hW1ne, _hW1hall, _hW1comp, hUleDer, _hUnil,
      _hW1normU, _hcompPU, _hPnoncyc, _hSecond, _hFitEq, _hFitLe, _hW2le,
      _hW2cyc, _hW2ne, _hCentralizer, _hHatNorm⟩
  rcases hxPkg with ⟨x, hxR0, hxne, hcentP⟩
  have hxSmax : x ∈ Smax :=
    section12_ambientDerivedSubgroup_le (hUleDer (_hR0U hxR0))
  exact ⟨x, hxR0, hxne,
    section14_mem_hatMsigma_of_centralizerIn_ne_bot hPσ hxSmax hcentP⟩


public theorem section14_caseA_centralizer_source_adapter
    {G : Type u} [Group G] [Finite G]
    {Smax Tmax W W1 W2 P Q U V C D L H R0 R : Subgroup G}
    {Sfam : Finset (Section1.ClassFunction Smax)}
    {Tfam : Finset (Section1.ClassFunction Tmax)}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {p q u v c d r : ℕ}
    {y : G} {rp : Nat.Primes}
    (_hsource : Section13.hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_h10 : Section13.theorem_13_10_hypothesis Smax P C Sfam p q u)
    (_hnotT : ¬ Section13.theorem_13_10_hypothesis Tmax Q D Tfam q p v)
    (_hq3 : q = 3)
    (_hqp : q < p)
    (_hLHMf : section16MFSubgroup L H)
    (_hUH : U ≤ H)
    (_hcaseA : Section13.case_9_7_a_sourceDataForSection13 Smax P U W1 W2 C p q u)
    (_hrp : rp.val = r)
    (_hr_dvd : r ∣ (p - 1) / 2)
    (_hu : u = (p - 1) ^ 2 / 4)
    (_hyQ : y ∈ Q)
    (_hsemi : Section2.IsInternalSemidirectProduct L H (W1 ⊔ W2.conjBy y))
    (_hR0U : R0 ≤ U)
    (_hR0p : IsPGroup r R0)
    (_hR0_ne : R0 ≠ ⊥)
    (_hR0_sylow : ∃ R0U : Sylow r U, R0 = (R0U : Subgroup U).map U.subtype)
    (_hR0R : R0 ≤ R)
    (_hRH : R ≤ H)
    (_hRp : IsPGroup r R)
    (_hR_sylow : ∃ RH : Sylow r H, R = (RH : Subgroup H).map H.subtype) :
    ∃ x : G, x ∈ R0 ∧ x ≠ 1 ∧
        Subgroup.centralizer ({x} : Set G) ≤ Smax := by
  have hsourceOrig := _hsource
  rcases section14_caseA_hatMsigma_element_source_adapter
      (Smax := Smax) (Tmax := Tmax) (W := W) (W1 := W1) (W2 := W2)
      (P := P) (Q := Q) (U := U) (V := V) (C := C) (D := D)
      (L := L) (H := H) (R0 := R0) (R := R) (Sfam := Sfam)
      (Tfam := Tfam) (τS := τS) (τT := τT) (p := p) (q := q)
      (u := u) (v := v) (c := c) (d := d) (r := r) (y := y) (rp := rp)
      _hsource _h10 _hnotT _hq3 _hqp _hLHMf _hUH _hcaseA _hrp _hr_dvd _hu
      _hyQ _hsemi _hR0U _hR0p _hR0_ne _hR0_sylow _hR0R _hRH _hRp
      _hR_sylow with
    ⟨x, hxR0, hxne, _hxHat⟩
  rcases _hsource with
    ⟨_hcase, hSTypeP, _hTTypeP, _hp, _hq, _hC, _hD, _hc, _hd, _hUcard,
      _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hNotation, _hDadeDiff,
      _hZeroDegree, _hConjIndex, _hConjBetaTau, _hChoice,
      _hMin, _hFourSixS, _hFourSixT⟩
  rcases hSTypeP with
    ⟨_hSmaxMF, _hW1cyc, _hW1ne, _hW1hall, _hW1comp, hUleDer, _hUnil,
      _hW1normU, _hcompPU, _hPnoncyc, _hSecond, _hFitEq, _hFitLe, _hW2le,
      _hW2cyc, _hW2ne, _hCentralizer, _hHatNorm⟩
  have hxSmax : x ∈ Smax :=
    section12_ambientDerivedSubgroup_le (hUleDer (_hR0U hxR0))
  rcases Section13.theorem_13_2_agreesWithInductionOnBookAZero
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsourceOrig with
    ⟨_Ms, A0book, _H_A0, _hA0M, _hMsChoice, hA0TI, _hMsSharp,
      _hFittingSharp, hASetA0, _hτDade, _hτInd⟩
  have hxASet : x ∈ section16ASet Smax U := by
    refine ⟨_hxHat, ?_, hxne⟩
    rw [Set.mem_mul]
    exact ⟨x, _hR0U hxR0, 1, Subgroup.one_mem _, by simp⟩
  have hxA0book : x ∈ A0book := by
    exact hASetA0 hxASet
  exact ⟨x, hxR0, hxne,
    section14_centralizer_singleton_le_of_tiWithNormalizer_mem hA0TI hxA0book hxne⟩

public theorem section14_caseA_center_le_Smax_inf_source_adapter
    {G : Type u} [Group G] [Finite G]
    {Smax Tmax W W1 W2 P Q U V C D L H R0 R : Subgroup G}
    {Sfam : Finset (Section1.ClassFunction Smax)}
    {Tfam : Finset (Section1.ClassFunction Tmax)}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {p q u v c d r : ℕ}
    {y : G} {rp : Nat.Primes}
    (_hsource : Section13.hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_h10 : Section13.theorem_13_10_hypothesis Smax P C Sfam p q u)
    (_hnotT : ¬ Section13.theorem_13_10_hypothesis Tmax Q D Tfam q p v)
    (_hq3 : q = 3)
    (_hqp : q < p)
    (_hLHMf : section16MFSubgroup L H)
    (_hUH : U ≤ H)
    (_hcaseA : Section13.case_9_7_a_sourceDataForSection13 Smax P U W1 W2 C p q u)
    (_hrp : rp.val = r)
    (_hr_dvd : r ∣ (p - 1) / 2)
    (_hu : u = (p - 1) ^ 2 / 4)
    (_hyQ : y ∈ Q)
    (_hsemi : Section2.IsInternalSemidirectProduct L H (W1 ⊔ W2.conjBy y))
    (_hR0U : R0 ≤ U)
    (_hR0p : IsPGroup r R0)
    (_hR0_ne : R0 ≠ ⊥)
    (_hR0_sylow : ∃ R0U : Sylow r U, R0 = (R0U : Subgroup U).map U.subtype)
    (_hR0R : R0 ≤ R)
    (_hRH : R ≤ H)
    (_hRp : IsPGroup r R)
    (_hR_sylow : ∃ RH : Sylow r H, R = (RH : Subgroup H).map H.subtype) :
    (Subgroup.center R).map R.subtype ≤ Smax := by
  rcases section14_caseA_centralizer_source_adapter
      (Smax := Smax) (Tmax := Tmax) (W := W) (W1 := W1) (W2 := W2)
      (P := P) (Q := Q) (U := U) (V := V) (C := C) (D := D)
      (L := L) (H := H) (R0 := R0) (R := R) (Sfam := Sfam)
      (Tfam := Tfam) (τS := τS) (τT := τT) (p := p) (q := q)
      (u := u) (v := v) (c := c) (d := d) (r := r) (y := y) (rp := rp)
      _hsource _h10 _hnotT _hq3 _hqp _hLHMf _hUH _hcaseA _hrp _hr_dvd _hu
      _hyQ _hsemi _hR0U _hR0p _hR0_ne _hR0_sylow _hR0R _hRH _hRp
      _hR_sylow with
    ⟨x, hxR0, hxne, hxcent⟩
  exact section14_center_map_le_Smax_of_centralizer_source _hR0R
    ⟨x, hxR0, hxne, hxcent⟩

public theorem section14_caseA_center_le_R0_source_adapter
    {G : Type u} [Group G] [Finite G]
    {Smax Tmax W W1 W2 P Q U V C D L H R0 R : Subgroup G}
    {Sfam : Finset (Section1.ClassFunction Smax)}
    {Tfam : Finset (Section1.ClassFunction Tmax)}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {p q u v c d r : ℕ}
    {y : G} {rp : Nat.Primes}
    (_hsource : Section13.hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_h10 : Section13.theorem_13_10_hypothesis Smax P C Sfam p q u)
    (_hnotT : ¬ Section13.theorem_13_10_hypothesis Tmax Q D Tfam q p v)
    (_hq3 : q = 3)
    (_hqp : q < p)
    (_hLHMf : section16MFSubgroup L H)
    (_hUH : U ≤ H)
    (_hcaseA : Section13.case_9_7_a_sourceDataForSection13 Smax P U W1 W2 C p q u)
    (_hrp : rp.val = r)
    (_hr_dvd : r ∣ (p - 1) / 2)
    (_hu : u = (p - 1) ^ 2 / 4)
    (_hyQ : y ∈ Q)
    (_hsemi : Section2.IsInternalSemidirectProduct L H (W1 ⊔ W2.conjBy y))
    (_hR0U : R0 ≤ U)
    (_hR0p : IsPGroup r R0)
    (_hR0_ne : R0 ≠ ⊥)
    (_hR0_sylow : ∃ R0U : Sylow r U, R0 = (R0U : Subgroup U).map U.subtype)
    (_hR0R : R0 ≤ R)
    (_hRH : R ≤ H)
    (_hRp : IsPGroup r R)
    (_hR_sylow : ∃ RH : Sylow r H, R = (RH : Subgroup H).map H.subtype) :
    (Subgroup.center R).map R.subtype ≤ R0 := by
  have hcenterS : (Subgroup.center R).map R.subtype ≤ Smax :=
    section14_caseA_center_le_Smax_inf_source_adapter
      (Smax := Smax) (Tmax := Tmax) (W := W) (W1 := W1) (W2 := W2)
      (P := P) (Q := Q) (U := U) (V := V) (C := C) (D := D)
      (L := L) (H := H) (R0 := R0) (R := R) (Sfam := Sfam)
      (Tfam := Tfam) (τS := τS) (τT := τT) (p := p) (q := q)
      (u := u) (v := v) (c := c) (d := d) (r := r) (y := y) (rp := rp)
      _hsource _h10 _hnotT _hq3 _hqp _hLHMf _hUH _hcaseA _hrp _hr_dvd _hu
      _hyQ _hsemi _hR0U _hR0p _hR0_ne _hR0_sylow _hR0R _hRH _hRp
      _hR_sylow
  have hR0_sylowS : ∃ R0S : Sylow rp.val Smax,
      R0 = (R0S : Subgroup Smax).map Smax.subtype :=
    section14_caseA_R0_sylow_in_Smax_source_adapter
      (Smax := Smax) (Tmax := Tmax) (W := W) (W1 := W1) (W2 := W2)
      (P := P) (Q := Q) (U := U) (V := V) (C := C) (D := D)
      (R0 := R0) (Sfam := Sfam) (Tfam := Tfam) (τS := τS) (τT := τT)
      (p := p) (q := q) (u := u) (v := v) (c := c) (d := d) (r := r)
      (rp := rp) _hsource _hrp _hR0U _hR0p _hR0_ne _hR0_sylow
  have hRp_rp : IsPGroup rp.val R := by
    simpa [_hrp] using _hRp
  refine section14_subgroup_le_sylow_image_of_le_pSubgroup_intermediate
    (A := Smax) (P := R0) (R := R)
    (Z := (Subgroup.center R).map R.subtype) (p := rp.val)
    _hR0R hRp_rp hR0_sylowS hcenterS ?_
  intro x hx
  rw [Subgroup.mem_map] at hx
  rcases hx with ⟨z, _hz, rfl⟩
  exact z.property

public theorem section14_caseA_center_rank_inputs_source_adapter
    {G : Type u} [Group G] [Finite G]
    {Smax Tmax W W1 W2 P Q U V C D L H R0 R : Subgroup G}
    {Sfam : Finset (Section1.ClassFunction Smax)}
    {Tfam : Finset (Section1.ClassFunction Tmax)}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {p q u v c d r : ℕ}
    {y : G} {rp : Nat.Primes}
    (_hsource : Section13.hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_h10 : Section13.theorem_13_10_hypothesis Smax P C Sfam p q u)
    (_hnotT : ¬ Section13.theorem_13_10_hypothesis Tmax Q D Tfam q p v)
    (_hq3 : q = 3)
    (_hqp : q < p)
    (_hLHMf : section16MFSubgroup L H)
    (_hUH : U ≤ H)
    (_hcaseA : Section13.case_9_7_a_sourceDataForSection13 Smax P U W1 W2 C p q u)
    (_hrp : rp.val = r)
    (_hr_dvd : r ∣ (p - 1) / 2)
    (_hu : u = (p - 1) ^ 2 / 4)
    (_hyQ : y ∈ Q)
    (_hsemi : Section2.IsInternalSemidirectProduct L H (W1 ⊔ W2.conjBy y))
    (_hR0U : R0 ≤ U)
    (_hR0p : IsPGroup r R0)
    (_hR0_ne : R0 ≠ ⊥)
    (_hR0_sylow : ∃ R0U : Sylow r U, R0 = (R0U : Subgroup U).map U.subtype)
    (_hR0R : R0 ≤ R)
    (_hRH : R ≤ H)
    (_hRp : IsPGroup r R)
    (_hR_sylow : ∃ RH : Sylow r H, R = (RH : Subgroup H).map H.subtype) :
    (Subgroup.center R).map R.subtype ≤ R0 ∧ groupRank R0 ≤ 2 := by
  refine ⟨?_, ?_⟩
  · exact section14_caseA_center_le_R0_source_adapter
      (Smax := Smax) (Tmax := Tmax) (W := W) (W1 := W1) (W2 := W2)
      (P := P) (Q := Q) (U := U) (V := V) (C := C) (D := D)
      (L := L) (H := H) (R0 := R0) (R := R) (Sfam := Sfam)
      (Tfam := Tfam) (τS := τS) (τT := τT) (p := p) (q := q)
      (u := u) (v := v) (c := c) (d := d) (r := r) (y := y) (rp := rp)
      _hsource _h10 _hnotT _hq3 _hqp _hLHMf _hUH _hcaseA _hrp _hr_dvd _hu
      _hyQ _hsemi _hR0U _hR0p _hR0_ne _hR0_sylow _hR0R _hRH _hRp
      _hR_sylow
  · exact section14_caseA_R0_groupRank_le_two_of_quotient_embedding
      (Smax := Smax) (Tmax := Tmax) (W := W) (W1 := W1) (W2 := W2)
      (P := P) (Q := Q) (U := U) (V := V) (C := C) (D := D)
      (R0 := R0) (Sfam := Sfam) (Tfam := Tfam) (τS := τS) (τT := τT)
      _hsource _hcaseA _hq3 _hR0U

public theorem section14_caseA_omegaOneCenter_rank_inputs_source_adapter
    {G : Type u} [Group G] [Finite G]
    {Smax Tmax W W1 W2 P Q U V C D L H R0 R : Subgroup G}
    {Sfam : Finset (Section1.ClassFunction Smax)}
    {Tfam : Finset (Section1.ClassFunction Tmax)}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {p q u v c d r : ℕ}
    {y : G} {rp : Nat.Primes}
    (_hsource : Section13.hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_h10 : Section13.theorem_13_10_hypothesis Smax P C Sfam p q u)
    (_hnotT : ¬ Section13.theorem_13_10_hypothesis Tmax Q D Tfam q p v)
    (_hq3 : q = 3)
    (_hqp : q < p)
    (_hLHMf : section16MFSubgroup L H)
    (_hUH : U ≤ H)
    (_hcaseA : Section13.case_9_7_a_sourceDataForSection13 Smax P U W1 W2 C p q u)
    (_hrp : rp.val = r)
    (_hr_dvd : r ∣ (p - 1) / 2)
    (_hu : u = (p - 1) ^ 2 / 4)
    (_hyQ : y ∈ Q)
    (_hsemi : Section2.IsInternalSemidirectProduct L H (W1 ⊔ W2.conjBy y))
    (_hR0U : R0 ≤ U)
    (_hR0p : IsPGroup r R0)
    (_hR0_ne : R0 ≠ ⊥)
    (_hR0_sylow : ∃ R0U : Sylow r U, R0 = (R0U : Subgroup U).map U.subtype)
    (_hR0R : R0 ≤ R)
    (_hRH : R ≤ H)
    (_hRp : IsPGroup r R)
    (_hR_sylow : ∃ RH : Sylow r H, R = (RH : Subgroup H).map H.subtype) :
    section10OmegaOneCenter rp R ≤ R0 ∧ groupRank R0 ≤ 2 := by
  rcases section14_caseA_center_rank_inputs_source_adapter
      (Smax := Smax) (Tmax := Tmax) (W := W) (W1 := W1) (W2 := W2)
      (P := P) (Q := Q) (U := U) (V := V) (C := C) (D := D)
      (L := L) (H := H) (R0 := R0) (R := R) (Sfam := Sfam)
      (Tfam := Tfam) (τS := τS) (τT := τT) (p := p) (q := q)
      (u := u) (v := v) (c := c) (d := d) (r := r) (y := y) (rp := rp)
      _hsource _h10 _hnotT _hq3 _hqp _hLHMf _hUH _hcaseA _hrp _hr_dvd _hu
      _hyQ _hsemi _hR0U _hR0p _hR0_ne _hR0_sylow _hR0R _hRH _hRp
      _hR_sylow with
    ⟨hZR0, hR0_rank⟩
  exact ⟨section14_omegaOneCenter_le_center_map.trans hZR0, hR0_rank⟩

public theorem section14_caseA_omegaOneCenter_card_bound_source_adapter
    {G : Type u} [Group G] [Finite G]
    {Smax Tmax W W1 W2 P Q U V C D L H R0 R : Subgroup G}
    {Sfam : Finset (Section1.ClassFunction Smax)}
    {Tfam : Finset (Section1.ClassFunction Tmax)}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {p q u v c d r : ℕ}
    {y : G} {rp : Nat.Primes}
    (_hsource : Section13.hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_h10 : Section13.theorem_13_10_hypothesis Smax P C Sfam p q u)
    (_hnotT : ¬ Section13.theorem_13_10_hypothesis Tmax Q D Tfam q p v)
    (_hq3 : q = 3)
    (_hqp : q < p)
    (_hLHMf : section16MFSubgroup L H)
    (_hUH : U ≤ H)
    (_hcaseA : Section13.case_9_7_a_sourceDataForSection13 Smax P U W1 W2 C p q u)
    (_hrp : rp.val = r)
    (_hr_dvd : r ∣ (p - 1) / 2)
    (_hu : u = (p - 1) ^ 2 / 4)
    (_hyQ : y ∈ Q)
    (_hsemi : Section2.IsInternalSemidirectProduct L H (W1 ⊔ W2.conjBy y))
    (_hR0U : R0 ≤ U)
    (_hR0p : IsPGroup r R0)
    (_hR0_ne : R0 ≠ ⊥)
    (_hR0_sylow : ∃ R0U : Sylow r U, R0 = (R0U : Subgroup U).map U.subtype)
    (_hR0R : R0 ≤ R)
    (_hRH : R ≤ H)
    (_hRp : IsPGroup r R)
    (_hR_sylow : ∃ RH : Sylow r H, R = (RH : Subgroup H).map H.subtype) :
    Nat.card (section10OmegaOneCenter rp R) ≤ rp.val ^ 2 := by
  rcases section14_caseA_omegaOneCenter_rank_inputs_source_adapter
      (Smax := Smax) (Tmax := Tmax) (W := W) (W1 := W1) (W2 := W2)
      (P := P) (Q := Q) (U := U) (V := V) (C := C) (D := D)
      (L := L) (H := H) (R0 := R0) (R := R) (Sfam := Sfam)
      (Tfam := Tfam) (τS := τS) (τT := τT) (p := p) (q := q)
      (u := u) (v := v) (c := c) (d := d) (r := r) (y := y) (rp := rp)
      _hsource _h10 _hnotT _hq3 _hqp _hLHMf _hUH _hcaseA _hrp _hr_dvd _hu
      _hyQ _hsemi _hR0U _hR0p _hR0_ne _hR0_sylow _hR0R _hRH _hRp
      _hR_sylow with
    ⟨hΩR0, hR0_rank⟩
  exact section14_omegaOneCenter_card_bound_of_le_rank_two hΩR0 hR0_rank

public theorem section14_caseA_omegaOneCenter_rankTwo_source_adapter
    {G : Type u} [Group G] [Finite G]
    {Smax Tmax W W1 W2 P Q U V C D L H R0 R : Subgroup G}
    {Sfam : Finset (Section1.ClassFunction Smax)}
    {Tfam : Finset (Section1.ClassFunction Tmax)}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {p q u v c d r : ℕ}
    {y : G} {rp : Nat.Primes}
    (_hsource : Section13.hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_h10 : Section13.theorem_13_10_hypothesis Smax P C Sfam p q u)
    (_hnotT : ¬ Section13.theorem_13_10_hypothesis Tmax Q D Tfam q p v)
    (_hq3 : q = 3)
    (_hqp : q < p)
    (_hLHMf : section16MFSubgroup L H)
    (_hUH : U ≤ H)
    (_hcaseA : Section13.case_9_7_a_sourceDataForSection13 Smax P U W1 W2 C p q u)
    (_hrp : rp.val = r)
    (_hr_dvd : r ∣ (p - 1) / 2)
    (_hu : u = (p - 1) ^ 2 / 4)
    (_hyQ : y ∈ Q)
    (_hsemi : Section2.IsInternalSemidirectProduct L H (W1 ⊔ W2.conjBy y))
    (_hR0U : R0 ≤ U)
    (_hR0p : IsPGroup r R0)
    (_hR0_ne : R0 ≠ ⊥)
    (_hR0_sylow : ∃ R0U : Sylow r U, R0 = (R0U : Subgroup U).map U.subtype)
    (_hR0R : R0 ≤ R)
    (_hRH : R ≤ H)
    (_hRp : IsPGroup r R)
    (_hR_sylow : ∃ RH : Sylow r H, R = (RH : Subgroup H).map H.subtype) :
    W2.conjBy y ≤
        Subgroup.normalizer (section10OmegaOneCenter rp R : Set G) ∧
      Nat.card (section10OmegaOneCenter rp R) ≤ rp.val ^ 2 := by
  constructor
  · exact section14_caseA_omegaOneCenter_normalizer_of_mf_sylow
      (by simpa [← _hrp] using rp.property) _hLHMf _hsemi _hRH _hR_sylow
  · exact section14_caseA_omegaOneCenter_card_bound_source_adapter
      (Smax := Smax) (Tmax := Tmax) (W := W) (W1 := W1) (W2 := W2)
      (P := P) (Q := Q) (U := U) (V := V) (C := C) (D := D)
      (L := L) (H := H) (R0 := R0) (R := R) (Sfam := Sfam)
      (Tfam := Tfam) (τS := τS) (τT := τT) (p := p) (q := q)
      (u := u) (v := v) (c := c) (d := d) (r := r) (y := y) (rp := rp)
      _hsource _h10 _hnotT _hq3 _hqp _hLHMf _hUH _hcaseA _hrp _hr_dvd _hu
      _hyQ _hsemi _hR0U _hR0p _hR0_ne _hR0_sylow _hR0R _hRH _hRp
      _hR_sylow

public theorem section14_caseA_omegaOneCenter_source_inputs
    {G : Type u} [Group G] [Finite G]
    {Smax Tmax W W1 W2 P Q U V C D L H R0 R : Subgroup G}
    {Sfam : Finset (Section1.ClassFunction Smax)}
    {Tfam : Finset (Section1.ClassFunction Tmax)}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {p q u v c d r : ℕ}
    {y : G} {rp : Nat.Primes}
    (_hsource : Section13.hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_h10 : Section13.theorem_13_10_hypothesis Smax P C Sfam p q u)
    (_hnotT : ¬ Section13.theorem_13_10_hypothesis Tmax Q D Tfam q p v)
    (_hq3 : q = 3)
    (_hqp : q < p)
    (_hLHMf : section16MFSubgroup L H)
    (_hUH : U ≤ H)
    (_hcaseA : Section13.case_9_7_a_sourceDataForSection13 Smax P U W1 W2 C p q u)
    (_hrp : rp.val = r)
    (_hr_dvd : r ∣ (p - 1) / 2)
    (_hu : u = (p - 1) ^ 2 / 4)
    (_hyQ : y ∈ Q)
    (_hsemi : Section2.IsInternalSemidirectProduct L H (W1 ⊔ W2.conjBy y))
    (_hR0U : R0 ≤ U)
    (_hR0p : IsPGroup r R0)
    (_hR0_ne : R0 ≠ ⊥)
    (_hR0_sylow : ∃ R0U : Sylow r U, R0 = (R0U : Subgroup U).map U.subtype)
    (_hR0R : R0 ≤ R)
    (_hRH : R ≤ H)
    (_hRp : IsPGroup r R)
    (_hR_sylow : ∃ RH : Sylow r H, R = (RH : Subgroup H).map H.subtype) :
    ∃ Ω : Subgroup G,
      Ω ≤ H ∧
        W2.conjBy y ≤ Subgroup.normalizer (Ω : Set G) ∧
          (Nat.card Ω = r ∨ Nat.card Ω = r ^ 2) := by
  have _hCbot : C = ⊥ :=
    section14_C_eq_bot_of_pf13_12_source _hsource
  have _hUcard : Nat.card U = u :=
    section14_U_card_eq_u_of_pf13_12_source _hsource
  rcases section14_caseA_quotient_embedding_data _hcaseA with
    ⟨_a, _ha_dvd, _hCU_caseA, _hnormal, _φ, _hφinj⟩
  rcases section14_caseA_quotient_card_le_square_of_q_eq_three _hcaseA _hq3 with
    ⟨_aBound, _haBound_dvd, _hu_le_aBound_sq⟩
  have _hRp_rp : IsPGroup rp.val R := by
    simpa [_hrp] using _hRp
  have _hOmegaCard_of_bound :
      Nat.card (section10OmegaOneCenter rp R) ≤ rp.val ^ 2 →
        Nat.card (section10OmegaOneCenter rp R) = rp.val ∨
          Nat.card (section10OmegaOneCenter rp R) = rp.val ^ 2 := by
    intro hcard_le
    exact section14_omegaOneCenter_card_eq_prime_or_prime_sq_of_le_square
      _hR0_ne _hR0R _hRp_rp hcard_le
  have hΩH : section10OmegaOneCenter rp R ≤ H :=
    (section10_omegaOneCenter_le R).trans _hRH
  rcases section14_caseA_omegaOneCenter_rankTwo_source_adapter
      (Smax := Smax) (Tmax := Tmax) (W := W) (W1 := W1) (W2 := W2)
      (P := P) (Q := Q) (U := U) (V := V) (C := C) (D := D)
      (L := L) (H := H) (R0 := R0) (R := R) (Sfam := Sfam)
      (Tfam := Tfam) (τS := τS) (τT := τT) (p := p) (q := q)
      (u := u) (v := v) (c := c) (d := d) (r := r) (y := y) (rp := rp)
      _hsource _h10 _hnotT _hq3 _hqp _hLHMf _hUH _hcaseA _hrp _hr_dvd _hu
      _hyQ _hsemi _hR0U _hR0p _hR0_ne _hR0_sylow _hR0R _hRH _hRp
      _hR_sylow with
    ⟨hW2normΩ, hΩcard_le⟩
  refine ⟨section10OmegaOneCenter rp R, hΩH, hW2normΩ, ?_⟩
  simpa [_hrp] using _hOmegaCard_of_bound hΩcard_le

public theorem section14_mixed_13_10_q_eq_three_case_a_omegaSubgroup_of_u_formula_source_bridge
    {G : Type u} [Group G] [Finite G]
    {Smax Tmax W W1 W2 P Q U V C D L H : Subgroup G}
    {Sfam : Finset (Section1.ClassFunction Smax)}
    {Tfam : Finset (Section1.ClassFunction Tmax)}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {p q u v c d r : ℕ}
    {y : G}
    (_hsource : Section13.hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_h10 : Section13.theorem_13_10_hypothesis Smax P C Sfam p q u)
    (_hnotT : ¬ Section13.theorem_13_10_hypothesis Tmax Q D Tfam q p v)
    (_hq3 : q = 3)
    (_hqp : q < p)
    (_hLHMf : section16MFSubgroup L H)
    (_hUH : U ≤ H)
    (_hcaseA : Section13.case_9_7_a_sourceDataForSection13 Smax P U W1 W2 C p q u)
    (_hr : Nat.Prime r)
    (_hr_dvd : r ∣ (p - 1) / 2)
    (_hu : u = (p - 1) ^ 2 / 4)
    (_hyQ : y ∈ Q)
    (_hsemi : Section2.IsInternalSemidirectProduct L H (W1 ⊔ W2.conjBy y)) :
    ∃ Ω : Subgroup G,
      Ω ≤ H ∧
        W2.conjBy y ≤ Subgroup.normalizer (Ω : Set G) ∧
          (Nat.card Ω = r ∨ Nat.card Ω = r ^ 2) := by
  have _hr_dvd_u : r ∣ u := by
    rw [_hu]
    exact section14_dvd_square_div_four_of_dvd_half _hr_dvd
  have _hbarU_r_dvd :
      ∃ _hCU : C ≤ U, ∃ hnormal : (C.subgroupOf U).Normal,
        letI : (C.subgroupOf U).Normal := hnormal
        r ∣ Nat.card (U ⧸ C.subgroupOf U) :=
    section14_caseA_prime_dvd_barU_card_of_u_formula _hcaseA _hr_dvd _hu
  have _hr_dvd_U : r ∣ Nat.card U :=
    section14_caseA_prime_dvd_U_card_of_u_formula _hcaseA _hr_dvd _hu
  have _hR0_exists :
      ∃ R0 : Subgroup G, R0 ≤ U ∧ IsPGroup r R0 ∧ R0 ≠ ⊥ ∧
        ∃ R0U : Sylow r U, R0 = (R0U : Subgroup U).map U.subtype :=
    section14_caseA_exists_nontrivial_rSubgroup_U_of_u_formula
      _hr _hcaseA _hr_dvd _hu
  rcases _hR0_exists with ⟨R0, hR0U, hR0p, _hR0_ne, hR0_sylow⟩
  have _hr_dvd_H : r ∣ Nat.card H :=
    _hr_dvd_U.trans (Subgroup.card_dvd_of_le _hUH)
  have hR0H : R0 ≤ H := hR0U.trans _hUH
  have _hR_containing_R0 :
      ∃ R : Subgroup G, R0 ≤ R ∧ R ≤ H ∧ IsPGroup r R ∧
        ∃ RH : Sylow r H, R = (RH : Subgroup H).map H.subtype :=
    section14_exists_ambient_sylow_containing_pSubgroup hR0H hR0p
  rcases _hR_containing_R0 with ⟨R, hR0R, hRH, hRp, hR_sylow⟩
  let rp : Nat.Primes := ⟨r, _hr⟩
  have hrp : rp.val = r := rfl
  exact section14_caseA_omegaOneCenter_source_inputs
      (Smax := Smax) (Tmax := Tmax) (W := W) (W1 := W1) (W2 := W2)
      (P := P) (Q := Q) (U := U) (V := V) (C := C) (D := D)
      (L := L) (H := H) (R0 := R0) (R := R) (Sfam := Sfam)
      (Tfam := Tfam) (τS := τS) (τT := τT) (p := p) (q := q)
      (u := u) (v := v) (c := c) (d := d) (r := r) (y := y) (rp := rp)
      _hsource _h10 _hnotT _hq3 _hqp
      _hLHMf _hUH _hcaseA hrp _hr_dvd _hu _hyQ _hsemi
      hR0U hR0p _hR0_ne hR0_sylow hR0R hRH hRp hR_sylow

public theorem section14_mixed_13_10_q_eq_three_case_a_omegaSubgroup_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {Smax Tmax W W1 W2 P Q U V C D L H : Subgroup G}
    {Sfam : Finset (Section1.ClassFunction Smax)}
    {Tfam : Finset (Section1.ClassFunction Tmax)}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {Lfam : Finset (Section1.ClassFunction L)}
    {RL : G → Subgroup G}
    {τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {φ : Section1.ClassFunction L}
    {μ01 : Section1.ClassFunction Smax}
    {ν10 : Section1.ClassFunction Tmax}
    {βS : Section1.ClassFunction Smax}
    {βT : Section1.ClassFunction Tmax}
    {βL : Section1.ClassFunction L}
    {p q u v c d r : ℕ}
    {y : G}
    (hctx : hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (h143 : hypothesis_14_3_data Smax Tmax L H P Q U W1 W2
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL)
    (h10 : Section13.theorem_13_10_hypothesis Smax P C Sfam p q u)
    (hnotT : ¬ Section13.theorem_13_10_hypothesis Tmax Q D Tfam q p v)
    (hq3 : q = 3)
    (hcaseA : Section13.case_9_7_a_sourceDataForSection13 Smax P U W1 W2 C p q u)
    (hr : Nat.Prime r)
    (hr_dvd : r ∣ (p - 1) / 2)
    (_hyQ : y ∈ Q)
    (_hsemi : Section2.IsInternalSemidirectProduct L H (W1 ⊔ W2.conjBy y)) :
    ∃ Ω : Subgroup G,
      Ω ≤ H ∧
        W2.conjBy y ≤ Subgroup.normalizer (Ω : Set G) ∧
          (Nat.card Ω = r ∨ Nat.card Ω = r ^ 2) := by
  have _h10 := h10
  have _hnotT := hnotT
  have _hq3 := hq3
  have hu : u = (p - 1) ^ 2 / 4 :=
    (Section13.theorem_13_13 Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d hctx.1 hcaseA).2
  rcases section14_theorem_14_5_pf13_17_inputs (hctx := hctx) (h143 := h143) with
    ⟨_htypeII, _hfrobLH, hUH, _hcomp⟩
  rcases h143 with
    ⟨_hLmax, _hNormUleL, hLHMf, _hTypeI, _hDadeL, _hLfam, _hTauL,
      _hTauL₁, _hφfam, _hφirr, _hφdeg, _hβS, _hβT, _hβL⟩
  exact section14_mixed_13_10_q_eq_three_case_a_omegaSubgroup_of_u_formula_source_bridge
    hctx.1 h10 hnotT hq3 hctx.2 hLHMf hUH hcaseA hr hr_dvd hu _hyQ _hsemi

public theorem section14_mixed_13_10_q_eq_three_case_a_fixedPointFree_square_congruence_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {Smax Tmax W W1 W2 P Q U V C D L H : Subgroup G}
    {Sfam : Finset (Section1.ClassFunction Smax)}
    {Tfam : Finset (Section1.ClassFunction Tmax)}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {Lfam : Finset (Section1.ClassFunction L)}
    {RL : G → Subgroup G}
    {τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {φ : Section1.ClassFunction L}
    {μ01 : Section1.ClassFunction Smax}
    {ν10 : Section1.ClassFunction Tmax}
    {βS : Section1.ClassFunction Smax}
    {βT : Section1.ClassFunction Tmax}
    {βL : Section1.ClassFunction L}
    {p q u v c d : ℕ}
    (hctx : hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (h143 : hypothesis_14_3_data Smax Tmax L H P Q U W1 W2
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL)
    (h145 : theorem_14_5_data L H W1 W2 Q)
    (h10 : Section13.theorem_13_10_hypothesis Smax P C Sfam p q u)
    (hnotT : ¬ Section13.theorem_13_10_hypothesis Tmax Q D Tfam q p v)
    (hq3 : q = 3)
    (hcaseA : Section13.case_9_7_a_sourceDataForSection13 Smax P U W1 W2 C p q u)
    {r : ℕ}
    (hr : Nat.Prime r)
    (hr_dvd : r ∣ (p - 1) / 2) :
    p ∣ r ^ 2 - 1 := by
  rcases h145 with ⟨y, hyQ, hsemi⟩
  have hW2y_card : Nat.card (W2.conjBy y) = p := by
    rcases hctx.1 with
      ⟨_hcase, _hSTypeP, _hTTypeP, hp_card, _hq_card, _hC, _hD, _hc, _hd,
        _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hNotation, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau, _hChoice, _hMin, _hFourSixS, _hFourSixT⟩
    calc
      Nat.card (W2.conjBy y) = Nat.card W2 := section11_card_conjBy (G := G) W2 y
      _ = p := hp_card.symm
  have hfrobLH : Section7.frobeniusWithKernel L H :=
    (section14_theorem_14_5_pf13_17_inputs (hctx := hctx) (h143 := h143)).2.1
  have hW2y_le_L : W2.conjBy y ≤ L :=
    (le_sup_right : W2.conjBy y ≤ W1 ⊔ W2.conjBy y).trans hsemi.right_le
  have hW2y_not_H : ∀ a : W2.conjBy y, a ≠ 1 → (a : G) ∉ H := by
    intro a ha hH
    have ha_inf : (a : G) ∈ H ⊓ (W1 ⊔ W2.conjBy y) :=
      ⟨hH, (le_sup_right : W2.conjBy y ≤ W1 ⊔ W2.conjBy y) a.property⟩
    have ha_bot : (a : G) ∈ (⊥ : Subgroup G) := by
      simpa [hsemi.inf_eq_bot] using ha_inf
    exact ha (Subtype.ext (by simpa using ha_bot))
  have hOmegaAction :
      ∃ E : Type u, ∃ _hGroup : Group E, ∃ _hFinite : Finite E,
        ∃ _hAction : MulDistribMulAction (W2.conjBy y) E,
          (Nat.card E = r ∨ Nat.card E = r ^ 2) ∧
            ∀ a : W2.conjBy y, a ≠ 1 → ∀ e : E, a • e = e → e = 1 := by
    rcases section14_mixed_13_10_q_eq_three_case_a_omegaSubgroup_source_bridge
        (hctx := hctx) (h143 := h143) h10 hnotT hq3 hcaseA hr hr_dvd hyQ hsemi with
      ⟨Ω, hΩ_le_H, hW2y_norm_Ω, hΩ_card⟩
    rcases section14_frobeniusWithKernel_invariant_subgroup_fixedPointFree_action
        (hfrob := hfrobLH) (A := W2.conjBy y) (Ω := Ω)
        hW2y_le_L hW2y_not_H hΩ_le_H hW2y_norm_Ω with
      ⟨hΩAction, hΩfree⟩
    exact ⟨Ω, inferInstance, inferInstance, hΩAction, hΩ_card, hΩfree⟩
  rcases hOmegaAction with ⟨E, hEGroup, hEFinite, hEAction, hEcard, hfree⟩
  letI : Group E := hEGroup
  letI : Finite E := hEFinite
  letI : MulDistribMulAction (W2.conjBy y) E := hEAction
  exact section14_fixedPointFree_card_prime_square_congruence
    (A := W2.conjBy y) (E := E) hW2y_card hr hEcard hfree

public theorem section14_mixed_13_10_q_eq_three_case_a_fixedPointFree_congruence_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {Smax Tmax W W1 W2 P Q U V C D L H : Subgroup G}
    {Sfam : Finset (Section1.ClassFunction Smax)}
    {Tfam : Finset (Section1.ClassFunction Tmax)}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {Lfam : Finset (Section1.ClassFunction L)}
    {RL : G → Subgroup G}
    {τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {φ : Section1.ClassFunction L}
    {μ01 : Section1.ClassFunction Smax}
    {ν10 : Section1.ClassFunction Tmax}
    {βS : Section1.ClassFunction Smax}
    {βT : Section1.ClassFunction Tmax}
    {βL : Section1.ClassFunction L}
    {p q u v c d : ℕ}
    (hctx : hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (h143 : hypothesis_14_3_data Smax Tmax L H P Q U W1 W2
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL)
    (h145 : theorem_14_5_data L H W1 W2 Q)
    (h10 : Section13.theorem_13_10_hypothesis Smax P C Sfam p q u)
    (hnotT : ¬ Section13.theorem_13_10_hypothesis Tmax Q D Tfam q p v)
    (hq3 : q = 3)
    (hcaseA : Section13.case_9_7_a_sourceDataForSection13 Smax P U W1 W2 C p q u)
    {r : ℕ}
    (hr : Nat.Prime r)
    (hr_dvd : r ∣ (p - 1) / 2) :
    p ∣ r - 1 ∨ p ∣ r + 1 := by
  rcases section14_context_primes_of_sourceData hctx with ⟨hp, _hq⟩
  exact section14_prime_dvd_pm_of_dvd_square_sub_one hp hr
    (section14_mixed_13_10_q_eq_three_case_a_fixedPointFree_square_congruence_source_bridge
      hctx h143 h145 h10 hnotT hq3 hcaseA hr hr_dvd)

public theorem section14_mixed_13_10_q_eq_three_case_a_prime_congruence_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {Smax Tmax W W1 W2 P Q U V C D L H : Subgroup G}
    {Sfam : Finset (Section1.ClassFunction Smax)}
    {Tfam : Finset (Section1.ClassFunction Tmax)}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {Lfam : Finset (Section1.ClassFunction L)}
    {RL : G → Subgroup G}
    {τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {φ : Section1.ClassFunction L}
    {μ01 : Section1.ClassFunction Smax}
    {ν10 : Section1.ClassFunction Tmax}
    {βS : Section1.ClassFunction Smax}
    {βT : Section1.ClassFunction Tmax}
    {βL : Section1.ClassFunction L}
    {p q u v c d : ℕ}
    (hctx : hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (h143 : hypothesis_14_3_data Smax Tmax L H P Q U W1 W2
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL)
    (h145 : theorem_14_5_data L H W1 W2 Q)
    (h10 : Section13.theorem_13_10_hypothesis Smax P C Sfam p q u)
    (hnotT : ¬ Section13.theorem_13_10_hypothesis Tmax Q D Tfam q p v)
    (hq3 : q = 3)
    (hcaseA : Section13.case_9_7_a_sourceDataForSection13 Smax P U W1 W2 C p q u) :
    ∃ r : ℕ, Nat.Prime r ∧ r ∣ (p - 1) / 2 ∧ (p ∣ r - 1 ∨ p ∣ r + 1) := by
  rcases section14_context_primes_of_sourceData hctx with ⟨hp, _hq⟩
  have h3p : 3 < p := by
    simpa [hq3] using hctx.2
  rcases section14_exists_prime_dvd_half_of_prime_gt_three hp h3p with
    ⟨r, hr, hr_dvd⟩
  have hcong :
      p ∣ r - 1 ∨ p ∣ r + 1 :=
    section14_mixed_13_10_q_eq_three_case_a_fixedPointFree_congruence_source_bridge
      hctx h143 h145 h10 hnotT hq3 hcaseA hr hr_dvd
  exact ⟨r, hr, hr_dvd, hcong⟩

public theorem section14_mixed_13_10_q_eq_three_case_a_contradiction_of_theorem_14_5
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {Smax Tmax W W1 W2 P Q U V C D L H : Subgroup G}
    {Sfam : Finset (Section1.ClassFunction Smax)}
    {Tfam : Finset (Section1.ClassFunction Tmax)}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {Lfam : Finset (Section1.ClassFunction L)}
    {RL : G → Subgroup G}
    {τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {φ : Section1.ClassFunction L}
    {μ01 : Section1.ClassFunction Smax}
    {ν10 : Section1.ClassFunction Tmax}
    {βS : Section1.ClassFunction Smax}
    {βT : Section1.ClassFunction Tmax}
    {βL : Section1.ClassFunction L}
    {p q u v c d : ℕ}
    (hctx : hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (h143 : hypothesis_14_3_data Smax Tmax L H P Q U W1 W2
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL)
    (h145 : theorem_14_5_data L H W1 W2 Q)
    (h10 : Section13.theorem_13_10_hypothesis Smax P C Sfam p q u)
    (hnotT : ¬ Section13.theorem_13_10_hypothesis Tmax Q D Tfam q p v)
    (hq3 : q = 3)
    (hcaseA : Section13.case_9_7_a_sourceDataForSection13 Smax P U W1 W2 C p q u) :
    False := by
  rcases section14_mixed_13_10_q_eq_three_case_a_prime_congruence_source_bridge
      hctx h143 h145 h10 hnotT hq3 hcaseA with
    ⟨r, hr, hr_dvd, hcong⟩
  have h3p : 3 < p := by
    simpa [hq3] using hctx.2
  exact section14_no_prime_divisor_half_with_pm_congruence h3p hr hr_dvd hcong

public theorem section14_mixed_13_10_q_eq_three_source_data_of_theorem_14_5
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {Smax Tmax W W1 W2 P Q U V C D L H : Subgroup G}
    {Sfam : Finset (Section1.ClassFunction Smax)}
    {Tfam : Finset (Section1.ClassFunction Tmax)}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {Lfam : Finset (Section1.ClassFunction L)}
    {RL : G → Subgroup G}
    {τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {φ : Section1.ClassFunction L}
    {μ01 : Section1.ClassFunction Smax}
    {ν10 : Section1.ClassFunction Tmax}
    {βS : Section1.ClassFunction Smax}
    {βT : Section1.ClassFunction Tmax}
    {βL : Section1.ClassFunction L}
    {p q u v c d : ℕ}
    (hctx : hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (h143 : hypothesis_14_3_data Smax Tmax L H P Q U W1 W2
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL)
    (h145 : theorem_14_5_data L H W1 W2 Q)
    (h10 : Section13.theorem_13_10_hypothesis Smax P C Sfam p q u)
    (hnotT : ¬ Section13.theorem_13_10_hypothesis Tmax Q D Tfam q p v)
    (hq3 : q = 3) :
    Section13.case_9_7_b_sourceDataForSection13 Smax P U W1 W2 C p q u := by
  rcases Section13.theorem_13_2_case_9_7_sourceData_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hctx.1 with hcaseA | hcaseB
  · exact False.elim
      (section14_mixed_13_10_q_eq_three_case_a_contradiction_of_theorem_14_5
        hctx h143 h145 h10 hnotT hq3 hcaseA)
  · exact hcaseB

public theorem section14_mixed_13_10_q_eq_three_source_data_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {Smax Tmax W W1 W2 P Q U V C D L H : Subgroup G}
    {Sfam : Finset (Section1.ClassFunction Smax)}
    {Tfam : Finset (Section1.ClassFunction Tmax)}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {Lfam : Finset (Section1.ClassFunction L)}
    {RL : G → Subgroup G}
    {τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {φ : Section1.ClassFunction L}
    {μ01 : Section1.ClassFunction Smax}
    {ν10 : Section1.ClassFunction Tmax}
    {βS : Section1.ClassFunction Smax}
    {βT : Section1.ClassFunction Tmax}
    {βL : Section1.ClassFunction L}
    {p q u v c d : ℕ}
    (hctx : hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (h143 : hypothesis_14_3_data Smax Tmax L H P Q U W1 W2
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL)
    (h10 : Section13.theorem_13_10_hypothesis Smax P C Sfam p q u)
    (hnotT : ¬ Section13.theorem_13_10_hypothesis Tmax Q D Tfam q p v)
    (hq3 : q = 3) :
    Section13.case_9_7_b_sourceDataForSection13 Smax P U W1 W2 C p q u := by
  have h145 : theorem_14_5_data L H W1 W2 Q :=
    section14_theorem_14_5_source_bridge
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL p q u v c d hctx h143
  exact section14_mixed_13_10_q_eq_three_source_data_of_theorem_14_5
    hctx h143 h145 h10 hnotT hq3

public theorem section14_mixed_13_10_source_data_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {Smax Tmax W W1 W2 P Q U V C D L H : Subgroup G}
    {Sfam : Finset (Section1.ClassFunction Smax)}
    {Tfam : Finset (Section1.ClassFunction Tmax)}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {Lfam : Finset (Section1.ClassFunction L)}
    {RL : G → Subgroup G}
    {τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {φ : Section1.ClassFunction L}
    {μ01 : Section1.ClassFunction Smax}
    {ν10 : Section1.ClassFunction Tmax}
    {βS : Section1.ClassFunction Smax}
    {βT : Section1.ClassFunction Tmax}
    {βL : Section1.ClassFunction L}
    {p q u v c d : ℕ}
    (hctx : hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (h143 : hypothesis_14_3_data Smax Tmax L H P Q U W1 W2
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL) :
    Section13.theorem_13_10_hypothesis Smax P C Sfam p q u →
      ¬ Section13.theorem_13_10_hypothesis Tmax Q D Tfam q p v →
        Section13.case_9_7_b_sourceDataForSection13 Smax P U W1 W2 C p q u := by
  intro h10 hnotT
  by_cases hq3 : q = 3
  · exact section14_mixed_13_10_q_eq_three_source_data_bridge
      hctx h143 h10 hnotT hq3
  · exact Section13.theorem_13_13_case_9_7_b_sourceData_of_q_ne_three
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hctx.1 hq3


public theorem section14_theorem_14_6_source_data_of_not_theorem_13_10_hypothesis
    {G : Type u} [Group G] [Finite G]
    {Smax Tmax W W1 W2 P Q U V C D : Subgroup G}
    {Sfam : Finset (Section1.ClassFunction Smax)}
    {Tfam : Finset (Section1.ClassFunction Tmax)}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {p q u v c d : ℕ}
    (hctx : hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnot : ¬ Section13.theorem_13_10_hypothesis Smax P C Sfam p q u) :
    Section13.case_9_7_b_sourceDataForSection13 Smax P U W1 W2 C p q u :=
  (((Section13.theorem_13_3 Smax Tmax W W1 W2 P Q U V C D
    Sfam Tfam τS τT p q u v c d hctx.1).2 hnot).2.1)


public theorem section14_theorem_14_6_source_data_of_swapped_theorem_13_10
    {G : Type u} [Group G] [Finite G]
    {Smax Tmax W W1 W2 P Q U V C D : Subgroup G}
    {Sfam : Finset (Section1.ClassFunction Smax)}
    {Tfam : Finset (Section1.ClassFunction Tmax)}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {p q u v c d : ℕ}
    (hctx : hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (h10T : Section13.theorem_13_10_hypothesis Tmax Q D Tfam q p v) :
    Section13.case_9_7_b_sourceDataForSection13 Smax P U W1 W2 C p q u := by
  rcases (Section13.theorem_13_4 Tmax Smax W W2 W1 Q P V U D C
      Tfam Sfam τT τS q p v u d c
      (section14_hypothesis_13_1_sourceData_swap hctx.1) h10T).2 with
    ⟨hsource, _hu⟩
  exact hsource

public theorem section14_theorem_14_6_mixed_13_10_source_data_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {Smax Tmax W W1 W2 P Q U V C D L H : Subgroup G}
    {Sfam : Finset (Section1.ClassFunction Smax)}
    {Tfam : Finset (Section1.ClassFunction Tmax)}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {Lfam : Finset (Section1.ClassFunction L)}
    {RL : G → Subgroup G}
    {τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {φ : Section1.ClassFunction L}
    {μ01 : Section1.ClassFunction Smax}
    {ν10 : Section1.ClassFunction Tmax}
    {βS : Section1.ClassFunction Smax}
    {βT : Section1.ClassFunction Tmax}
    {βL : Section1.ClassFunction L}
    {p q u v c d : ℕ}
    (hctx : hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (h143 : hypothesis_14_3_data Smax Tmax L H P Q U W1 W2
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL)
    (h10 : Section13.theorem_13_10_hypothesis Smax P C Sfam p q u)
    (hnotT : ¬ Section13.theorem_13_10_hypothesis Tmax Q D Tfam q p v) :
    Section13.case_9_7_b_sourceDataForSection13 Smax P U W1 W2 C p q u := by
  exact section14_mixed_13_10_source_data_bridge hctx h143 h10 hnotT


public theorem section14_theorem_14_6_source_data_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (p q u v c d : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        Section13.case_9_7_b_sourceDataForSection13 Smax P U W1 W2 C p q u := by
  intro hctx h143
  by_cases h10 : Section13.theorem_13_10_hypothesis Smax P C Sfam p q u
  · by_cases h10T : Section13.theorem_13_10_hypothesis Tmax Q D Tfam q p v
    · exact section14_theorem_14_6_source_data_of_swapped_theorem_13_10 hctx h10T
    · exact section14_theorem_14_6_mixed_13_10_source_data_bridge hctx h143 h10 h10T
  · exact section14_theorem_14_6_source_data_of_not_theorem_13_10_hypothesis hctx h10

public theorem section14_theorem_14_6_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (p q u v c d : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        Section13.case_9_7_b_for_section13 Smax C p q u := by
  intro hctx h143
  exact section14_case_9_7_b_for_section13_of_sourceData
    (section14_theorem_14_6_source_data_bridge
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL p q u v c d hctx h143)


end CFSG.Section14
