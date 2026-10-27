module

public import CFSG.Timmesfeld.ARS.CaseHOrder
public import CFSG.Timmesfeld.ARS.Sec8Regular
public import Mathlib.Tactic.Monotonicity.Lemmas
public import Mathlib.Topology.Sheaves.Presheaf

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace CaseH

section Two

variable (h : Hyp G R) (hH : SigmaEqLambda R)
include h hH

theorem ncard_omegaSet {A : Subgroup G} (hA : A ∈ R) {q L : ℕ} (hq : Nat.card A = q)
    (hL : (linesThrough R A).ncard = L) : (omegaSet R A).ncard = (L - 1) ^ 2 * q ^ 3 := by
  have := h.finite
  have hΛ := ncard_lambdaSet h hA
  have hΨ := ncard_psiSet h hH hA
  have hΩ := ncard_omegaSet_mul h hH hA
  rw [hL, hq] at hΛ
  rw [hΛ, hq] at hΨ
  rw [hL, hΨ, hΛ, hq] at hΩ
  have hL1 : 1 ≤ L := by
    rw [← hL, Nat.one_le_iff_ne_zero]
    intro h0
    have := ncard_lambdaSet h hA
    rw [h0, zero_mul, Set.ncard_eq_zero (Set.toFinite _)] at this
    exact (lambdaSet_nonempty h.root h.noIsolated h.nondeg hA).ne_empty this
  have hsub : L * q - q = (L - 1) * q := (Nat.sub_one_mul L q).symm
  rw [hsub] at hΩ
  refine Nat.eq_of_mul_eq_mul_right hL1 ?_
  rw [hΩ]
  ring

omit hH in
theorem commutatorElement_mul_of_mem_M {A : Subgroup G} (hA : A ∈ R) {x y z : G}
    (hx : x ∈ M R A) (hy : y ∈ M R A) (hz : z ∈ M R A) : ⁅x * y, z⁆ = ⁅y, z⁆ * ⁅x, z⁆ := by
  have := h.finite
  obtain ⟨-, -, hMM, -, -⟩ := Q_eq_M h hA
  have hyz : ⁅y, z⁆ ∈ A := hMM ▸ Subgroup.commutator_mem_commutator hy hz
  have hc : x * ⁅y, z⁆ * x⁻¹ = ⁅y, z⁆ := by
    rw [(QD.commuting_M h.root hA _ hyz x hx).symm.eq, mul_inv_cancel_right]
  calc ⁅x * y, z⁆ = (x * ⁅y, z⁆ * x⁻¹) * ⁅x, z⁆ := by
        simp only [commutatorElement_def]
        group
    _ = ⁅y, z⁆ * ⁅x, z⁆ := by rw [hc]

omit hH in
theorem conjSub_mem_omegaSet {A B : Subgroup G} (hA : A ∈ R) (hB : B ∈ omegaSet R A) {m : G}
    (hm : m ∈ M R A) : conjSub B m ∈ omegaSet R A := by
  have := h.finite
  have hmA : conjSub A m = A := conjSub_eq_self_iff.2 ((isPGroup_M h.root hA).2.1 hm)
  refine ⟨h.root.conjSub_mem hB.1 m, ?_⟩
  have := Opposite.conj hB.2 m
  rwa [hmA] at this

omit hH in
theorem orbitMap_injective {A B : Subgroup G} (hA : A ∈ R) (hB : B ∈ omegaSet R A) :
    Function.Injective fun m : M R A => conjSub B (m : G) := by
  intro m m' e
  have e' : conjSub B ((m' : G)⁻¹ * m) = B := by
    change conjSub B m = conjSub B m' at e
    rw [conjSub_mul, e, ← conjSub_mul, inv_mul_cancel, conjSub_one]
  have := eq_one_of_mem_M_of_conjSub_eq h hA hB ((M R A).mul_mem ((M R A).inv_mem m'.2) m.2) e'
  exact (Subtype.ext (inv_mul_eq_one.mp this)).symm

omit hH in
theorem card_M_dvd {A : Subgroup G} (hA : A ∈ R) : Nat.card (M R A) ∣ (omegaSet R A).ncard := by
  classical
  have := h.finite
  let _ : MulAction (M R A) (omegaSet R A) :=
    { smul := fun m B => ⟨conjSub B.1 m, conjSub_mem_omegaSet h hA B.2 m.2⟩
      one_smul := fun B => Subtype.ext (conjSub_one B.1)
      mul_smul := fun m m' B => Subtype.ext (conjSub_mul B.1 m m') }
  have hstab : ∀ B : omegaSet R A, MulAction.stabilizer (M R A) B = ⊥ := by
    intro B
    refine eq_bot_iff.2 fun m hm => ?_
    have hmB : conjSub B.1 (m : G) = B.1 := congrArg Subtype.val (MulAction.mem_stabilizer_iff.1 hm)
    exact Subgroup.mem_bot.2 (Subtype.ext (eq_one_of_mem_M_of_conjSub_eq h hA B.2 m.2 hmB))
  have : Fintype (MulAction.orbitRel.Quotient (M R A) (omegaSet R A)) := Fintype.ofFinite _
  rw [← Nat.card_coe_set_eq,
    Nat.card_congr (MulAction.selfEquivSigmaOrbits (M R A) (omegaSet R A)), Nat.card_sigma]
  refine Finset.dvd_sum fun ω _ => ?_
  rw [Nat.card_coe_set_eq, ← MulAction.index_stabilizer, hstab, Subgroup.index_bot]

theorem two_pow_le_card_M {A : Subgroup G} (hA : A ∈ R) (hq : Nat.card A = 2) :
    2 ^ (linesThrough R A).ncard ≤ Nat.card (M R A) := by
  classical
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hcard : ∀ X ∈ R, Nat.card X = 2 := fun X hX => (hR.card_eq hX hA).trans hq
  obtain ⟨a, ha, ha1⟩ := hR.exists_ne_one hA
  have hpt : ∀ V : linesThrough R A, ∃ D, D ∈ lambdaSet R A ∧ V.1 = A ⊔ D := fun V => by
    obtain ⟨D, hD, e⟩ := (mem_linesThrough_iff h hA).1 V.2
    exact ⟨D, hD, e⟩
  choose pt hptA hptV using hpt
  have hel : ∀ V : linesThrough R A, ∃ x, x ∈ pt V ∧ x ≠ 1 := fun V => by
    obtain ⟨x, hx, hx1⟩ := hR.exists_ne_one (hptA V).1.1
    exact ⟨x, hx, hx1⟩
  choose el helV hel1 using hel
  have : Fintype (linesThrough R A) := Fintype.ofFinite _
  have hptM : ∀ V : linesThrough R A, pt V ≤ M R A := fun V => QD.le_M (hptA V)
  have helM : ∀ V : linesThrough R A, el V ∈ M R A := fun V => hptM V (helV V)
  have hspec : ∀ V W : linesThrough R A, V ≠ W → ⁅el V, el W⁆ = a := by
    intro V W hVW
    have hpV := hptA V
    have hpW := hptA W
    have hnc : ¬ Commuting (pt V) (pt W) := by
      intro hc
      apply hVW
      have hle : pt W ≤ A ⊔ pt V := le_line h hH hA hpV hA le_sup_left hpV.1.1 le_sup_right
        hpV.1.2.1.symm hpW.1.1 hpW.1.2.2.symm hc.symm
      refine Subtype.ext ?_
      rw [hptV V, hptV W]
      exact (eq_of_le_of_le h hA hpV hA hpW hA hpW.1.1 hpW.1.2.1.symm le_sup_left hle
        le_sup_left le_sup_right)
    obtain ⟨-, hcomm⟩ := special_of_mem_lambdaSet_of_mem_lambdaSet h hA hpV hpW hnc
    have hmem : ⁅el V, el W⁆ ∈ A := hcomm ▸ Subgroup.commutator_mem_commutator (helV V) (helV W)
    refine eq_of_mem_of_card_eq_two hq ha ha1 hmem fun h1 => hnc ?_
    exact commuting_of_commute_of_card_eq_two (hcard _ hpV.1.1) (hcard _ hpW.1.1) (helV V)
      (hel1 V) (helV W) (hel1 W) (commutatorElement_eq_one_iff_commute.mp h1)
  have hnot : ∀ (S : Finset (linesThrough R A)) (V W : linesThrough R A), V ∉ S → W ∉ S →
      V ≠ W → el V ∉ A ⊔ ⨆ U ∈ S, pt U := by
    intro S V W hVS hWS hVW hmemV
    let T : Subgroup G :=
      { carrier := {x | x ∈ M R A ∧ ⁅x, el W⁆ = ⁅x, el V⁆}
        mul_mem' := by
          rintro x y ⟨hx, hxe⟩ ⟨hy, hye⟩
          refine ⟨(M R A).mul_mem hx hy, ?_⟩
          rw [commutatorElement_mul_of_mem_M h hA hx hy (helM W),
            commutatorElement_mul_of_mem_M h hA hx hy (helM V), hxe, hye]
        one_mem' := ⟨(M R A).one_mem, by simp⟩
        inv_mem' := by
          rintro x ⟨hx, hxe⟩
          refine ⟨(M R A).inv_mem hx, ?_⟩
          have e1 := commutatorElement_mul_of_mem_M h hA ((M R A).inv_mem hx) hx (helM W)
          have e2 := commutatorElement_mul_of_mem_M h hA ((M R A).inv_mem hx) hx (helM V)
          rw [inv_mul_cancel, commutatorElement_one_left] at e1 e2
          rw [eq_comm, mul_eq_one_iff_eq_inv] at e1 e2
          have e1' : ⁅x⁻¹, el W⁆ = ⁅x, el W⁆⁻¹ := by rw [e1, inv_inv]
          have e2' : ⁅x⁻¹, el V⁆ = ⁅x, el V⁆⁻¹ := by rw [e2, inv_inv]
          rw [e1', e2', hxe] }
    have hHT : A ⊔ ⨆ U ∈ S, pt U ≤ T := by
      refine sup_le (fun x hx => ⟨QD.le_M_self hx, ?_⟩) (iSup₂_le fun U hU => ?_)
      · rw [commutatorElement_eq_one_iff_commute.mpr (QD.commuting_M hR hA x hx _ (helM W)),
          commutatorElement_eq_one_iff_commute.mpr (QD.commuting_M hR hA x hx _ (helM V))]
      · intro u hu
        refine ⟨hptM U hu, ?_⟩
        rcases eq_or_ne u 1 with rfl | hu1
        · simp
        rw [eq_of_mem_of_card_eq_two (hcard _ (hptA U).1.1) (helV U) (hel1 U) hu hu1,
          hspec U W (fun e => hWS (e ▸ hU)), hspec U V (fun e => hVS (e ▸ hU))]
    have h1 := (hHT hmemV).2
    rw [commutatorElement_self, hspec V W hVW] at h1
    exact ha1 h1
  have hdouble : ∀ S : Finset (linesThrough R A), S.card < Fintype.card (linesThrough R A) →
      2 ^ (S.card + 1) ≤ Nat.card ↥(A ⊔ ⨆ U ∈ S, pt U) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro _
      simp only [Finset.notMem_empty, iSup_false, iSup_bot, sup_bot_eq, Finset.card_empty,
        zero_add, pow_one, hq, le_refl]
    | insert V S hVS ih =>
      intro hcardS
      rw [Finset.card_insert_of_notMem hVS] at hcardS ⊢
      have hih := ih (by omega)
      obtain ⟨W, hWS⟩ : ∃ W, W ∉ insert V S := by
        by_contra hno
        push Not at hno
        have := Finset.card_le_card (show Finset.univ ⊆ insert V S from fun W _ => hno W)
        rw [Finset.card_insert_of_notMem hVS, Finset.card_univ] at this
        omega
      have hWV : V ≠ W := fun e => hWS (e ▸ Finset.mem_insert_self V S)
      have hWS' : W ∉ S := fun hw => hWS (Finset.mem_insert_of_mem hw)
      have hle : A ⊔ ⨆ U ∈ S, pt U ≤ A ⊔ ⨆ U ∈ insert V S, pt U :=
        sup_le_sup_left (iSup₂_le fun U hU =>
          le_iSup₂_of_le (f := fun U (_ : U ∈ insert V S) => pt U) U
            (Finset.mem_insert_of_mem hU) le_rfl) _
      have hmem : el V ∈ A ⊔ ⨆ U ∈ insert V S, pt U :=
        Subgroup.mem_sup_right (Subgroup.mem_iSup_of_mem V (Subgroup.mem_iSup_of_mem
          (Finset.mem_insert_self V S) (helV V)))
      have hne : A ⊔ ⨆ U ∈ S, pt U ≠ A ⊔ ⨆ U ∈ insert V S, pt U := fun e =>
        hnot S V W hVS hWS' hWV (e ▸ hmem)
      obtain ⟨c, hc⟩ := Subgroup.card_dvd_of_le hle
      have hc0 : c ≠ 0 := by
        rintro rfl
        rw [mul_zero] at hc
        exact Nat.card_pos.ne' hc
      have hc1 : c ≠ 1 := by
        rintro rfl
        rw [mul_one] at hc
        exact hne (Subgroup.eq_of_le_of_card_ge hle hc.le)
      calc 2 ^ (S.card + 1 + 1) = 2 ^ (S.card + 1) * 2 := pow_succ 2 _
        _ ≤ Nat.card ↥(A ⊔ ⨆ U ∈ S, pt U) * c := Nat.mul_le_mul hih (by omega)
        _ = _ := hc.symm
  have hL : (linesThrough R A).ncard = Fintype.card (linesThrough R A) := by
    rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  have hLpos : 0 < Fintype.card (linesThrough R A) := by
    obtain ⟨D, hD⟩ := lambdaSet_nonempty hR hiso h.nondeg hA
    exact Fintype.card_pos_iff.2 ⟨⟨A ⊔ D, (mem_linesThrough_iff h hA).2 ⟨D, hD, rfl⟩⟩⟩
  obtain ⟨S, -, hScard⟩ := Finset.exists_subset_card_eq
    (show Fintype.card (linesThrough R A) - 1 ≤ (Finset.univ : Finset (linesThrough R A)).card by
      rw [Finset.card_univ]; omega)
  have h1 := hdouble S (by omega)
  rw [hL]
  calc 2 ^ Fintype.card (linesThrough R A) = 2 ^ (S.card + 1) := by rw [hScard]; congr 1; omega
    _ ≤ Nat.card ↥(A ⊔ ⨆ U ∈ S, pt U) := h1
    _ ≤ Nat.card (M R A) :=
      Subgroup.card_le_of_le (sup_le QD.le_M_self (iSup₂_le fun U _ => hptM U))

theorem M_transitive_of_nine {A : Subgroup G} (hA : A ∈ R) (hq : Nat.card A = 2)
    (hL : (linesThrough R A).ncard = 9) {B B' : Subgroup G} (hB : B ∈ omegaSet R A)
    (hB' : B' ∈ omegaSet R A) : ∃ m ∈ M R A, conjSub B m = B' := by
  classical
  have := h.finite
  have hR := h.root
  have hM := two_pow_le_card_M h hH hA hq
  rw [hL] at hM
  have hΩ := ncard_omegaSet h hH hA hq hL
  norm_num at hΩ
  have hrange : Set.range (fun m : M R A => conjSub B (m : G)) = omegaSet R A := by
    refine Set.eq_of_subset_of_ncard_le
      (Set.range_subset_iff.2 fun m => conjSub_mem_omegaSet h hA hB m.2) ?_ (Set.toFinite _)
    rw [hΩ, ← Nat.card_coe_set_eq, Nat.card_range_of_injective (orbitMap_injective h hA hB)]
    exact hM
  obtain ⟨m, hm⟩ := (hrange ▸ hB' : B' ∈ Set.range fun m : M R A => conjSub B (m : G))
  exact ⟨m, m.2, hm⟩

omit h hH in
theorem eight_mul_sq_lt_two_pow {t : ℕ} (ht : 9 ≤ t) : 8 * t ^ 2 < 2 ^ (t + 1) := by
  induction t, ht using Nat.le_induction with
  | base => norm_num
  | succ t ht ih =>
    calc 8 * (t + 1) ^ 2 ≤ 2 * (8 * t ^ 2) := by nlinarith
      _ < 2 * 2 ^ (t + 1) := by linarith
      _ = 2 ^ (t + 1 + 1) := by ring

theorem ncard_linesThrough_of_two {A : Subgroup G} (hA : A ∈ R) (hq : Nat.card A = 2)
    (h3 : 3 ≤ (linesThrough R A).ncard) :
    (linesThrough R A).ncard = 3 ∨ (linesThrough R A).ncard = 5 ∨
      (linesThrough R A).ncard = 9 := by
  have := h.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (isPGroup_M h.root hA).1.exists_card_eq
  have hM := two_pow_le_card_M h hH hA hq
  have hdvd := card_M_dvd h hA
  rw [ncard_omegaSet h hH hA hq rfl] at hdvd
  obtain ⟨t, ht⟩ : ∃ t, (linesThrough R A).ncard = t + 1 := ⟨_, (Nat.succ_pred_eq_of_pos
    (by omega)).symm⟩
  rw [ht] at hM hdvd h3 ⊢
  rw [Nat.add_sub_cancel] at hdvd
  rw [hn] at hM hdvd
  have hpos : 0 < t ^ 2 * 2 ^ 3 := Nat.mul_pos (pow_pos (by omega) 2) (by norm_num)
  have hle : 2 ^ (t + 1) ≤ t ^ 2 * 2 ^ 3 := hM.trans (Nat.le_of_dvd hpos hdvd)
  have hdvd' : 2 ^ (t + 1) ∣ t ^ 2 * 2 ^ 3 :=
    (Nat.pow_dvd_pow 2 ((Nat.pow_le_pow_iff_right (by norm_num)).1 hM)).trans hdvd
  have ht8 : t ≤ 8 := by
    by_contra h9
    have := eight_mul_sq_lt_two_pow (t := t) (by omega)
    omega
  interval_cases t <;> omega

end Two

end CaseH

end CFSG.Timmesfeld.ARS
