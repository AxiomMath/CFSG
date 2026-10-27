module
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_1.NormalizerGrowth
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_2.Core

namespace CFSG
end CFSG
open CFSG

/-!
# Huppert IV.5.1(a)

Burnside IV.5.1 setup and the prime-power witness extraction.  The final
public facade `huppert_IV_5_1_a_prime_power_witness_of_fields` is the source
statement: from the two-Sylow/normalizer-failure field data one obtains a
prime-power `q'` element and a `q`-subgroup witness.
-/

namespace CFSG.BenderSuzuki
namespace External

open PFchapter1section1 PFAppendixIII
open scoped Pointwise

universe u v

public theorem hkt_exists_qprime_divisor_card_of_not_isPGroup
    (q : ℕ) [Fact q.Prime] (G : Type u) [Group G] [Finite G]
    (hnot : ¬ IsPGroup q G) :
    ∃ r : ℕ, r.Prime ∧ r ≠ q ∧ r ∣ Nat.card G := by
  classical
  by_contra h
  have hforall : ∀ r : ℕ, r.Prime → r ∣ Nat.card G → r = q := by
    intro r hr hdvd
    by_contra hrq
    exact h ⟨r, hr, hrq, hdvd⟩
  have hpgroup : IsPGroup q G := by
    rw [IsPGroup.iff_card]
    let n := Nat.card G
    have hn0 : n ≠ 0 := Nat.card_pos.ne'
    refine ⟨n.factorization q, ?_⟩
    have hfac : n.factorization = Finsupp.single q (n.factorization q) := by
      ext r
      by_cases hrq : r = q
      · subst hrq
        simp
      · by_cases hr : r.Prime
        · have hzero : n.factorization r = 0 := by
            by_contra hpos
            have hdvd : r ∣ n := Nat.dvd_of_factorization_pos hpos
            exact hrq (hforall r hr hdvd)
          simp [hzero, hrq]
        · have hzero : n.factorization r = 0 :=
            Nat.factorization_eq_zero_of_not_prime n hr
          simp [hzero, hrq]
    exact Nat.eq_pow_of_factorization_eq_single hn0 hfac
  exact hnot hpgroup

public theorem hkt_exists_pElement_notMem_of_prime_dvd_quotient
    {G : Type u} [Group G] [Finite G] (N : Subgroup G) [N.Normal]
    {p : ℕ} [Fact p.Prime] (hdvd : p ∣ Nat.card (G ⧸ N)) :
    ∃ x : G, IsPElement (p := p) x ∧ x ∉ N := by
  classical
  let f : G →* G ⧸ N := QuotientGroup.mk' N
  let P : Sylow p G := Sylow.nonempty.some
  let Pbar : Sylow p (G ⧸ N) :=
    P.mapSurjective (f := f) (QuotientGroup.mk'_surjective N)
  have hPbar_ne_bot : (Pbar : Subgroup (G ⧸ N)) ≠ ⊥ :=
    Sylow.ne_bot_of_dvd_card Pbar hdvd
  have hy_exists : ∃ y : G ⧸ N, y ∈ (Pbar : Subgroup (G ⧸ N)) ∧ y ≠ 1 := by
    by_contra hnone
    apply hPbar_ne_bot
    rw [Subgroup.eq_bot_iff_forall]
    intro y hy
    by_contra hyne
    exact hnone ⟨y, hy, hyne⟩
  obtain ⟨y, hyPbar, hyne⟩ := hy_exists
  have hy_map : y ∈ (P : Subgroup G).map f := by
    simpa [Pbar, Sylow.coe_mapSurjective] using hyPbar
  rcases hy_map with ⟨x, hxP, hxy⟩
  refine ⟨x, ?_, ?_⟩
  · obtain ⟨k, hk⟩ :=
      (IsPGroup.iff_orderOf.mp P.isPGroup') (⟨x, hxP⟩ : (P : Subgroup G))
    refine ⟨k, ?_⟩
    exact (Subgroup.orderOf_coe
      (H := (P : Subgroup G)) (a := (⟨x, hxP⟩ : (P : Subgroup G)))).trans hk
  · intro hxN
    have hxq : f x = 1 := by
      simpa [f] using (QuotientGroup.eq_one_iff (N := N) x).2 hxN
    apply hyne
    rw [← hxy, hxq]


private theorem hkt_burnside_iv51_M_le_Dsub
    {Q : Type u} [Group Q] {q : ℕ}
    (T : Sylow q Q) (M Dsub : Subgroup Q)
    (M_le_T : M ≤ (T : Subgroup Q))
    (Dsub_eq_denominator : Dsub = (T : Subgroup Q) ⊓ Subgroup.normalizer (M : Set Q)) :
    M ≤ Dsub := by
  classical
  intro x hxM
  rw [Dsub_eq_denominator]
  exact ⟨(M_le_T) hxM, Subgroup.le_normalizer hxM⟩

private theorem hkt_burnside_iv51_Dsub_p
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (T : Sylow q Q) (M Dsub : Subgroup Q)
    (Dsub_eq_denominator : Dsub = (T : Subgroup Q) ⊓ Subgroup.normalizer (M : Set Q)) :
    IsPGroup q Dsub := by
  classical
  exact IsPGroup.to_le T.isPGroup' (by
    intro x hxD
    have hxDen : x ∈ (T : Subgroup Q) ⊓ Subgroup.normalizer (M : Set Q) := by
      simpa [Dsub_eq_denominator] using hxD
    exact hxDen.1)

private theorem hkt_burnside_iv51_Esub_le_normalizer_Dsub
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S T : Sylow q Q) (M Dsub Esub : Subgroup Q)
    (Dsub_eq_denominator : Dsub = (T : Subgroup Q) ⊓ Subgroup.normalizer (M : Set Q))
    (Dsub_le_selected_sylow : Dsub ≤ (S : Subgroup Q))
    (Esub_eq_firstNormalizer : Esub = (Subgroup.normalizer ((((T : Subgroup Q) ⊓ Subgroup.normalizer (M : Set Q)).subgroupOf (S : Subgroup Q) : Set (S : Subgroup Q)))).map (S : Subgroup Q).subtype) :
    Esub ≤ Subgroup.normalizer (Dsub : Set Q) := by
  classical
  have hD_le_S : Dsub ≤ (S : Subgroup Q) := Dsub_le_selected_sylow
  have hmap_le :=
    sylow_subgroupOf_normalizer_map_le_normalizer
      (S := S) (U := Dsub) hD_le_S
  simpa [Esub_eq_firstNormalizer, Dsub_eq_denominator] using hmap_le

private theorem hkt_burnside_iv51_Estar_le_normalizer_Dsub
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (T : Sylow q Q) (M Dsub EstarSub : Subgroup Q)
    (Dsub_eq_denominator : Dsub = (T : Subgroup Q) ⊓ Subgroup.normalizer (M : Set Q))
    (EstarSub_eq_secondNormalizer :
      EstarSub = (Subgroup.normalizer ((((T : Subgroup Q) ⊓ Subgroup.normalizer (M : Set Q)).subgroupOf (T : Subgroup Q) : Set (T : Subgroup Q)))).map (T : Subgroup Q).subtype) :
    EstarSub ≤ Subgroup.normalizer (Dsub : Set Q) := by
  classical
  have hD_le_T : Dsub ≤ (T : Subgroup Q) := by
    intro x hxD
    have hxDen : x ∈ (T : Subgroup Q) ⊓ Subgroup.normalizer (M : Set Q) := by
      simpa [Dsub_eq_denominator] using hxD
    exact hxDen.1
  have hmap_le :=
    sylow_subgroupOf_normalizer_map_le_normalizer
      (S := T) (U := Dsub) hD_le_T
  simpa [EstarSub_eq_secondNormalizer, Dsub_eq_denominator] using hmap_le

private theorem hkt_burnside_iv51_normalizer_Dsub_quotient_not_qgroup_source
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S T : Sylow q Q) (M Dsub Esub EstarSub : Subgroup Q)
    (M_le_T : M ≤ (T : Subgroup Q))
    (Dsub_eq_denominator : Dsub = (T : Subgroup Q) ⊓ Subgroup.normalizer (M : Set Q))
    (Dsub_le_selected_sylow : Dsub ≤ (S : Subgroup Q))
    (Esub_eq_firstNormalizer : Esub = (Subgroup.normalizer ((((T : Subgroup Q) ⊓ Subgroup.normalizer (M : Set Q)).subgroupOf (S : Subgroup Q) : Set (S : Subgroup Q)))).map (S : Subgroup Q).subtype)
    (EstarSub_eq_secondNormalizer :
      EstarSub = (Subgroup.normalizer ((((T : Subgroup Q) ⊓ Subgroup.normalizer (M : Set Q)).subgroupOf (T : Subgroup Q) : Set (T : Subgroup Q)))).map (T : Subgroup Q).subtype)
    (Dsub_card_lt_EstarSub : Nat.card (↥Dsub) < Nat.card (↥EstarSub))
    (Esub_p : IsPGroup q Esub)
    (intermediate_normalizes_M :
      ∀ B : Subgroup Q,
        Esub ≤ B → IsPGroup q B → B ≤ Subgroup.normalizer (M : Set Q)) :
    ¬ IsPGroup q
      ((Subgroup.normalizer (Dsub : Set Q)) ⧸
        ((Subgroup.centralizer (Dsub : Set Q)).subgroupOf
          (Subgroup.normalizer (Dsub : Set Q)))) := by
  classical
  intro hquot
  let N : Subgroup Q := Subgroup.normalizer (Dsub : Set Q)
  let C : Subgroup N := (Subgroup.centralizer (Dsub : Set Q)).subgroupOf N
  haveI : C.Normal := by
    simpa [C, N] using
      (inferInstance :
        ((Subgroup.centralizer (Dsub : Set Q)).subgroupOf
          (Subgroup.normalizer (Dsub : Set Q))).Normal)
  have hE_le_N : Esub ≤ N := by
    simpa [N] using hkt_burnside_iv51_Esub_le_normalizer_Dsub
      (Q := Q) (q := q) S T M Dsub Esub Dsub_eq_denominator
      Dsub_le_selected_sylow Esub_eq_firstNormalizer
  let EN : Subgroup N := Esub.subgroupOf N
  have hEN_p : IsPGroup q EN := by
    simpa [EN, N] using
      Esub_p.of_equiv
        ((Subgroup.subgroupOfEquivOfLe (H := Esub) (K := N) hE_le_N).symm)
  obtain ⟨SN, hEN_le_SN⟩ := IsPGroup.exists_le_sylow (G := N) (p := q) hEN_p
  have hquot_NC : IsPGroup q (N ⧸ C) := by
    simpa [N, C] using hquot
  have hdecomp : ∀ n : N, ∃ s : N, s ∈ (SN : Subgroup N) ∧ n * s⁻¹ ∈ C := by
    intro n
    exact hkt_exists_sylow_div_mem_of_quotient_isPGroup
      (G := N) (p := q) SN C hquot_NC n
  let B : Subgroup Q := (SN : Subgroup N).map N.subtype
  have hE_le_B : Esub ≤ B := by
    intro x hxE
    let xN : N := ⟨x, hE_le_N hxE⟩
    have hxEN : xN ∈ EN := by simpa [EN, Subgroup.mem_subgroupOf, xN] using hxE
    exact ⟨xN, hEN_le_SN hxEN, rfl⟩
  have hB_p : IsPGroup q B := by
    exact SN.isPGroup'.map N.subtype
  have hB_le_normalizer_M : B ≤ Subgroup.normalizer (M : Set Q) :=
    intermediate_normalizes_M B hE_le_B hB_p
  have hN_le_normalizer_M : N ≤ Subgroup.normalizer (M : Set Q) := by
    intro n hn
    let nn : N := ⟨n, hn⟩
    rcases hdecomp nn with ⟨s, hsSN, hc⟩
    have hs_norm_M : (s : Q) ∈ Subgroup.normalizer (M : Set Q) := by
      exact hB_le_normalizer_M ⟨s, hsSN, rfl⟩
    have hc_cent_D : ((nn * s⁻¹ : N) : Q) ∈ Subgroup.centralizer (Dsub : Set Q) := by
      simpa [C, N, Subgroup.mem_subgroupOf] using hc
    have hc_cent_M : ((nn * s⁻¹ : N) : Q) ∈ Subgroup.centralizer (M : Set Q) := by
      rw [Subgroup.mem_centralizer_iff]
      intro m hm
      exact (Subgroup.mem_centralizer_iff.mp hc_cent_D) m
        (hkt_burnside_iv51_M_le_Dsub (Q := Q) (q := q) T M Dsub M_le_T Dsub_eq_denominator hm)
    have hc_norm_M : ((nn * s⁻¹ : N) : Q) ∈ Subgroup.normalizer (M : Set Q) :=
      centralizer_le_normalizer (M) hc_cent_M
    have hn_eq : n = ((nn * s⁻¹ : N) : Q) * (s : Q) := by
      simp [nn, mul_assoc]
    rw [hn_eq]
    exact (Subgroup.normalizer (M : Set Q)).mul_mem hc_norm_M hs_norm_M
  have hEstar_le_D : EstarSub ≤ Dsub := by
    intro x hxE
    have hxN : x ∈ N := hkt_burnside_iv51_Estar_le_normalizer_Dsub
      (Q := Q) (q := q) T M Dsub EstarSub Dsub_eq_denominator
      EstarSub_eq_secondNormalizer hxE
    have hxNormM : x ∈ Subgroup.normalizer (M : Set Q) := hN_le_normalizer_M hxN
    have hxT : x ∈ (T : Subgroup Q) := by
      have hxSecond : x ∈ (Subgroup.normalizer ((((T : Subgroup Q) ⊓ Subgroup.normalizer (M : Set Q)).subgroupOf (T : Subgroup Q) : Set (T : Subgroup Q)))).map (T : Subgroup Q).subtype := by
        simpa [EstarSub_eq_secondNormalizer] using hxE
      rcases hxSecond with ⟨y, _hy, rfl⟩
      exact y.property
    rw [Dsub_eq_denominator]
    exact ⟨hxT, hxNormM⟩
  exact (not_lt_of_ge (Subgroup.card_le_of_le hEstar_le_D)) Dsub_card_lt_EstarSub

private theorem hkt_burnside_iv51_witness_of_normalizer_growth
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S T : Sylow q Q) (M Dsub Esub EstarSub : Subgroup Q)
    (M_le_T : M ≤ (T : Subgroup Q))
    (Dsub_eq_denominator : Dsub = (T : Subgroup Q) ⊓ Subgroup.normalizer (M : Set Q))
    (Dsub_le_selected_sylow : Dsub ≤ (S : Subgroup Q))
    (Esub_eq_firstNormalizer : Esub = (Subgroup.normalizer ((((T : Subgroup Q) ⊓ Subgroup.normalizer (M : Set Q)).subgroupOf (S : Subgroup Q) : Set (S : Subgroup Q)))).map (S : Subgroup Q).subtype)
    (EstarSub_eq_secondNormalizer :
      EstarSub = (Subgroup.normalizer ((((T : Subgroup Q) ⊓ Subgroup.normalizer (M : Set Q)).subgroupOf (T : Subgroup Q) : Set (T : Subgroup Q)))).map (T : Subgroup Q).subtype)
    (Dsub_card_lt_EstarSub : Nat.card (↥Dsub) < Nat.card (↥EstarSub))
    (Esub_p : IsPGroup q Esub)
    (intermediate_normalizes_M :
      ∀ B : Subgroup Q,
        Esub ≤ B → IsPGroup q B → B ≤ Subgroup.normalizer (M : Set Q)) :
    ∃ A : Subgroup Q,
      IsPGroup q A ∧
        ∃ r : ℕ,
          r.Prime ∧ r ≠ q ∧
            ∃ x : Q,
              IsPElement (p := r) x ∧
                x ∈ Subgroup.normalizer (A : Set Q) ∧
                  x ∉ Subgroup.centralizer (A : Set Q) := by
  classical
  let Γ : Type u :=
    (Subgroup.normalizer (Dsub : Set Q)) ⧸
      ((Subgroup.centralizer (Dsub : Set Q)).subgroupOf
        (Subgroup.normalizer (Dsub : Set Q)))
  have hnot : ¬ IsPGroup q Γ := by
    simpa [Γ] using
      hkt_burnside_iv51_normalizer_Dsub_quotient_not_qgroup_source
        (Q := Q) (q := q) S T M Dsub Esub EstarSub M_le_T
        Dsub_eq_denominator Dsub_le_selected_sylow Esub_eq_firstNormalizer
        EstarSub_eq_secondNormalizer Dsub_card_lt_EstarSub Esub_p
        intermediate_normalizes_M
  obtain ⟨r, hr, hr_ne_q, hr_dvd⟩ :=
    hkt_exists_qprime_divisor_card_of_not_isPGroup q Γ hnot
  let N : Subgroup Q := Subgroup.normalizer (Dsub : Set Q)
  let C : Subgroup N := (Subgroup.centralizer (Dsub : Set Q)).subgroupOf N
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : C.Normal := by
    simpa [C, N] using
      (inferInstance :
        ((Subgroup.centralizer (Dsub : Set Q)).subgroupOf
          (Subgroup.normalizer (Dsub : Set Q))).Normal)
  have hdiv : r ∣ Nat.card (N ⧸ C) := by
    simpa [Γ, N, C] using hr_dvd
  obtain ⟨y, hy_r, hy_not_C⟩ :=
    hkt_exists_pElement_notMem_of_prime_dvd_quotient (G := N) (N := C) hdiv
  exact ⟨Dsub,
    hkt_burnside_iv51_Dsub_p
      (Q := Q) (q := q) T M Dsub Dsub_eq_denominator,
    r, hr, hr_ne_q, (y : Q),
    by
      obtain ⟨k, hk⟩ := hy_r
      refine ⟨k, ?_⟩
      exact (Subgroup.orderOf_coe (H := N) (a := y)).trans hk,
    y.property,
    by
      intro hy_cent
      apply hy_not_C
      change (y : Q) ∈ Subgroup.centralizer (Dsub : Set Q)
      exact hy_cent⟩

/-- Huppert IV.5.2 in the form needed by IV.5.3: from the weak-closure
failure of `Z(S)`, produce the Burnside IV.5.1 field data. -/
private theorem hkt_huppert_iv52_burnside_fields_of_center_failure
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S T : Sylow q Q)
    (hcenter_le_T :
      centerIn (G := Q) (S : Subgroup Q) ≤ (T : Subgroup Q))
    (hcenter_ne_T :
      centerIn (G := Q) (S : Subgroup Q) ≠
        centerIn (G := Q) (T : Subgroup Q)) :
    ∃ M : Subgroup Q,
      IsPGroup q M ∧
        M ≤ (S : Subgroup Q) ∧
        (S : Subgroup Q) ≤ Subgroup.normalizer (M : Set Q) ∧
        M ≤ (T : Subgroup Q) ∧
        ¬ (T : Subgroup Q) ≤ Subgroup.normalizer (M : Set Q) := by
  classical
  let M : Subgroup Q := centerIn (G := Q) (S : Subgroup Q)
  have hM_p : IsPGroup q M :=
    IsPGroup.to_le S.isPGroup'
      (show M ≤ (S : Subgroup Q) from by
        intro x hx
        exact hx.1)
  have hM_le_S : M ≤ (S : Subgroup Q) := by
    intro x hx
    exact hx.1
  have hS_le_normalizer_M :
      (S : Subgroup Q) ≤ Subgroup.normalizer (M : Set Q) := by
    simpa [M] using hkt_huppert_iv52_sylow_le_normalizer_centerIn (Q := Q) (q := q) S
  have hM_le_T : M ≤ (T : Subgroup Q) := by
    intro x hx
    exact hcenter_le_T hx
  have hfail : ¬ (T : Subgroup Q) ≤ Subgroup.normalizer (M : Set Q) := by
    simpa [M] using hkt_huppert_iv52_normalizer_failure_of_center_mismatch
      (Q := Q) (q := q) S T hcenter_le_T hcenter_ne_T
  exact ⟨M, hM_p, hM_le_S, hS_le_normalizer_M, hM_le_T, hfail⟩

/-- Burnside IV.5.1, at the strength of the book statement. From the
field data supplied by IV.5.2, one obtains a `q`-subgroup and a `q'`
prime-power element normalizing but not centralizing it. This is deliberately
weaker than the IV.5.3 Sylow witness: Burnside IV.5.1 only needs a `q`-subgroup. -/
public theorem hkt_burnside_iv51_witness_of_fields
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S T : Sylow q Q) (M : Subgroup Q)
    (M_p : IsPGroup q M)
    (M_le_S : M ≤ (S : Subgroup Q))
    (S_le_normalizer_M : (S : Subgroup Q) ≤ Subgroup.normalizer (M : Set Q))
    (M_le_T : M ≤ (T : Subgroup Q))
    (not_T_le_normalizer_M :
      ¬ (T : Subgroup Q) ≤ Subgroup.normalizer (M : Set Q)) :
    ∃ A : Subgroup Q,
      IsPGroup q A ∧
        ∃ r : ℕ,
          r.Prime ∧ r ≠ q ∧
            ∃ x : Q,
              IsPElement (p := r) x ∧
                x ∈ Subgroup.normalizer (A : Set Q) ∧
                  x ∉ Subgroup.centralizer (A : Set Q) := by
  classical
  obtain ⟨Smin, Tmin, Mmin, hMmin_p, hMmin_le_S, hSmin_norm,
      hMmin_le_T, hTmin_not, hminimal, hgrowth⟩ :=
    hkt_burnside_iv51_growth_subgroups_of_minimal_choice
      (Q := Q) (q := q) S T M M_p M_le_S S_le_normalizer_M M_le_T
      not_T_le_normalizer_M
  rcases hgrowth with ⟨Dsub, Esub, EstarSub, hDsub_eq_denominator,
    hDsub_le_selected_sylow, hEsub_eq_firstNormalizer,
    hEstarSub_eq_secondNormalizer, hDsub_le_Esub, hDsub_card_lt_Esub,
    hDsub_le_EstarSub, hDsub_card_lt_EstarSub, hEsub_p,
    hintermediate_normalizes_M⟩
  exact hkt_burnside_iv51_witness_of_normalizer_growth
    (Q := Q) (q := q) Smin Tmin Mmin Dsub Esub EstarSub
    hMmin_le_T hDsub_eq_denominator hDsub_le_selected_sylow
    hEsub_eq_firstNormalizer hEstarSub_eq_secondNormalizer
    hDsub_card_lt_EstarSub hEsub_p hintermediate_normalizes_M

public theorem sylow_le_normalizer_centerIn
    {Q : Type u} [Group Q] {q : ℕ} (S : Sylow q Q) :
    (S : Subgroup Q) ≤
      Subgroup.normalizer ((centerIn (G := Q) (S : Subgroup Q) : Subgroup Q) : Set Q) := by
  classical
  have hS_norm :
      (S : Subgroup Q) ≤ Subgroup.normalizer ((S : Subgroup Q) : Set Q) :=
    Subgroup.le_normalizer
  have hcenter_norm :
      Subgroup.normalizer ((S : Subgroup Q) : Set Q) ≤
        Subgroup.normalizer
          ((((Subgroup.center (S : Subgroup Q) : Subgroup (S : Subgroup Q)).map
            (S : Subgroup Q).subtype : Subgroup Q) : Set Q)) :=
    hkt_normalizer_le_normalizer_map_subtype_of_characteristic
      (Q := Q) (S : Subgroup Q) (Subgroup.center (S : Subgroup Q))
  simpa [centerIn_eq_map_center_local] using hS_norm.trans hcenter_norm

public theorem hkt_huppert_iv53_witness_of_not_pNormal
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q) (hnot_pnormal : ¬ ∀ T : Sylow q Q, centerIn (G := Q) (S : Subgroup Q) ≤ (T : Subgroup Q) → centerIn (G := Q) (S : Subgroup Q) = centerIn (G := Q) (T : Subgroup Q)) :
    ∃ A : Subgroup Q,
      IsPGroup q A ∧
        ∃ r : ℕ,
          r.Prime ∧ r ≠ q ∧
            ∃ x : Q,
              IsPElement (p := r) x ∧
                x ∈ Subgroup.normalizer (A : Set Q) ∧
                  x ∉ Subgroup.centralizer (A : Set Q) := by
  classical
  push Not at hnot_pnormal
  rcases hnot_pnormal with ⟨T, hcenter_le_T, hcenter_ne_T⟩
  obtain ⟨M, hM_p, hM_le_S, hS_le_normalizer_M, hM_le_T, hfail⟩ :=
    hkt_huppert_iv52_burnside_fields_of_center_failure
      (Q := Q) (q := q) S T hcenter_le_T hcenter_ne_T
  exact hkt_burnside_iv51_witness_of_fields
    (Q := Q) (q := q) S T M hM_p hM_le_S hS_le_normalizer_M hM_le_T hfail


end External
end CFSG.BenderSuzuki
