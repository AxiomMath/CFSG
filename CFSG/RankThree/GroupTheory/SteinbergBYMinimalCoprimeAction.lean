module

public import CFSG.GroupTheory.SteinbergBKMinimalCoprimeClassTwo
public import CFSG.GroupTheory.FrattiniQuotient
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Frattini.CoprimeAction

public section

namespace CFSG.RankThree.GroupTheory.SteinbergBY

open CFSG
open scoped commutatorElement

variable {A P : Type*} [Group A] [Group P] [MulDistribMulAction A P]

theorem isInvariant_of_characteristic (N : Subgroup P) [hN : N.Characteristic] :
    IsInvariant A P N := by
  refine ⟨fun a x => ?_⟩
  have h := Subgroup.characteristic_iff_comap_eq.mp hN (MulDistribMulAction.toMulAut A P a)
  constructor
  · intro hx
    rw [← h] at hx
    exact hx
  · intro hx
    rw [← h]
    exact hx

variable (A P) in
@[expose, reducible] noncomputable def frattiniQuotientAction :
    MulDistribMulAction A (P ⧸ frattini P) :=
  quotientMulDistribMulAction (frattini P) (isInvariant_of_characteristic (frattini P))

theorem frattiniQuotientAction_smul (a : A) (q : P) :
    letI := frattiniQuotientAction A P
    a • (q : P ⧸ frattini P) = ((a • q : P) : P ⧸ frattini P) :=
  rfl

variable [Finite A] [Finite P]

omit [Finite P] in
theorem fixedPointSubgroup_quotient_eq_bot (hcop : Nat.Coprime (Nat.card A) (Nat.card P))
    (htop : commutatorAction (A := A) (G := P) = ⊤) (N : Subgroup P) [N.Normal]
    (hNinv : IsInvariant A P N) (hcomm : IsMulCommutative (P ⧸ N)) :
    letI := quotientMulDistribMulAction N hNinv
    fixedPointSubgroup A (P ⧸ N) = ⊥ := by
  let _ := quotientMulDistribMulAction N hNinv
  have hsmul : ∀ (a : A) (q : P), a • (q : P ⧸ N) = ((a • q : P) : P ⧸ N) := fun _ _ => rfl
  have hV : commutatorAction (A := A) (G := P ⧸ N) = ⊤ := by
    rw [eq_top_iff]
    intro v _
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective v
    have hq : q ∈ commutatorAction (A := A) (G := P) := htop ▸ Subgroup.mem_top q
    rw [commutatorAction_eq_closure] at hq ⊢
    have hle : Subgroup.closure {x : P | ∃ a : A, ∃ g : P, x = g⁻¹ * (a • g)} ≤
        (Subgroup.closure {x : P ⧸ N | ∃ a : A, ∃ g : P ⧸ N, x = g⁻¹ * (a • g)}).comap
          (QuotientGroup.mk' N) := by
      rw [Subgroup.closure_le]
      rintro _ ⟨a, g, rfl⟩
      refine Subgroup.subset_closure ⟨a, (g : P ⧸ N), ?_⟩
      rw [hsmul, QuotientGroup.mk'_apply, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    exact hle hq
  have hcop' : Nat.Coprime (Nat.card A) (Nat.card (P ⧸ N)) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_quotient_dvd_card N) hcop
  have hcompl :=
    isCompl_fixedPointSubgroup_commutatorAction_of_sup_eq_top_of_coprime_of_isMulCommutative
      (A := A) (G := P ⧸ N) (by rw [hV, sup_top_eq]) hcop' hcomm
  rw [hV] at hcompl
  simpa using hcompl.inf_eq_bot

theorem frattini_ne_top_of_nontrivial [Nontrivial P] : frattini P ≠ ⊤ := by
  rcases eq_top_or_exists_le_coatom (⊥ : Subgroup P) with h | ⟨M, hM, -⟩
  · exact absurd h bot_ne_top
  · intro h
    exact hM.1 (top_le_iff.mp (h ▸ frattini_le_coatom hM))

omit [Finite P] in
theorem commutatorElement_mul_right_eq (x a b : P) : ⁅x, a * b⁆ = ⁅x, a⁆ * (a * ⁅x, b⁆ * a⁻¹) := by
  simp only [commutatorElement_def]
  group

omit [Finite P] in
theorem commutatorElement_pow_right_of_le_center (hc : commutator P ≤ Subgroup.center P)
    (x y : P) (n : ℕ) : ⁅x, y ^ n⁆ = ⁅x, y⁆ ^ n := by
  induction n with
  | zero => simp [commutatorElement_def]
  | succ n ih =>
    have hmem : ⁅x, y⁆ ∈ commutator P := by
      rw [commutator_eq_closure]
      exact Subgroup.subset_closure (commutator_mem_commutatorSet x y)
    have hcen : ⁅x, y⁆ ∈ Subgroup.center P := hc hmem
    rw [pow_succ, commutatorElement_mul_right_eq, ih, pow_succ]
    congr 1
    rw [Subgroup.mem_center_iff.mp hcen (y ^ n), mul_inv_cancel_right]

theorem minimal_coprime_action_elementary_or_special {l : ℕ} [hl : Fact l.Prime]
    (hP : IsPGroup l P) (hA : ¬ l ∣ Nat.card A) (hnt : ∃ (a : A) (q : P), a • q ≠ q)
    (hmin : ∀ R : Subgroup P, R ≠ ⊤ → (∀ (a : A), ∀ r ∈ R, a • r ∈ R) →
      ∀ (a : A), ∀ r ∈ R, a • r = r) :
    commutatorAction (A := A) (G := P) = ⊤ ∧
      (∀ (a : A), ∀ r ∈ frattini P, a • r = r) ∧
      (letI := frattiniQuotientAction A P;
        Nontrivial (P ⧸ frattini P) ∧ IsElementaryAbelian l (P ⧸ frattini P) ∧
          (∃ (a : A) (v : P ⧸ frattini P), a • v ≠ v) ∧
          ∀ S : Subgroup (P ⧸ frattini P), (∀ (a : A), ∀ s ∈ S, a • s ∈ S) → S = ⊥ ∨ S = ⊤) ∧
      (IsMulCommutative P → frattini P = ⊥ ∧ IsElementaryAbelian l P) ∧
      (¬ IsMulCommutative P → commutator P = frattini P ∧ frattini P = Subgroup.center P ∧
        commutator P ≠ ⊥ ∧ IsElementaryAbelian l (commutator P) ∧
        ∀ (a : A), ∀ z ∈ Subgroup.center P, a • z = z) := by
  have hlp : l.Prime := hl.out
  have hcop : Nat.Coprime (Nat.card A) (Nat.card P) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP
    rw [hk]
    exact Nat.Coprime.pow_right k ((Nat.coprime_comm).mp ((hlp.coprime_iff_not_dvd).mpr hA))
  obtain ⟨hclos, hPZ⟩ := GroupTheory.SteinbergBK.minimal_coprime_pgroup_action_class_two
    (U := A) (Q := P) hP ⊤ (by rwa [Subgroup.card_top])
    (by obtain ⟨a, q, h⟩ := hnt; exact ⟨a, Subgroup.mem_top a, q, h⟩)
    (fun R hR hinv x _ r hr => hmin R hR hinv x r hr)
  have htop : commutatorAction (A := A) (G := P) = ⊤ := by
    rw [commutatorAction_eq_closure, ← hclos]
    congr 1
    ext g
    constructor
    · rintro ⟨a, q, rfl⟩
      exact ⟨q, a, Subgroup.mem_top a, rfl⟩
    · rintro ⟨q, a, -, rfl⟩
      exact ⟨a, q, rfl⟩
  have : Nontrivial P := by
    obtain ⟨a, q, h⟩ := hnt
    refine ⟨⟨q, 1, fun hq => h ?_⟩⟩
    rw [hq, smul_one]
  have hFtop : frattini P ≠ ⊤ := frattini_ne_top_of_nontrivial
  have hFinv : IsInvariant A P (frattini P) := isInvariant_of_characteristic _
  have hFfix : ∀ (a : A), ∀ r ∈ frattini P, a • r = r :=
    hmin _ hFtop fun a r hr => (hFinv.invariant a r).mp hr
  obtain ⟨-, hVcomm, hVpow, hVel, -⟩ := GroupTheory.frattini_elementary_quotient hP
  have hPF : commutator P ≤ frattini P :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mp hVcomm
  have hCinv : IsInvariant A P (commutator P) := isInvariant_of_characteristic _
  have hEcomm : IsMulCommutative (P ⧸ commutator P) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr le_rfl
  have hEfix := fixedPointSubgroup_quotient_eq_bot hcop htop (commutator P) hCinv hEcomm
  have hfixE : ∀ r : P, (∀ a : A, a • r = r) → r ∈ commutator P := by
    intro r hr
    let _ := quotientMulDistribMulAction (commutator P) hCinv
    have hmem : (r : P ⧸ commutator P) ∈ fixedPointSubgroup A (P ⧸ commutator P) := by
      intro a
      change ((a • r : P) : P ⧸ commutator P) = (r : P ⧸ commutator P)
      rw [hr a]
    rw [hEfix, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hmem
    exact hmem
  have hFP : frattini P = commutator P :=
    le_antisymm (fun r hr => hfixE r fun a => hFfix a r hr) hPF
  have hpowF : ∀ x : P, x ^ l ∈ frattini P := by
    intro x
    have h := hVpow (x : P ⧸ frattini P)
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h
    exact h
  refine ⟨htop, hFfix, ?_, fun hab => ?_, fun hnab => ?_⟩
  ·
    let _ := frattiniQuotientAction A P
    have hVfix := fixedPointSubgroup_quotient_eq_bot hcop htop (frattini P) hFinv hVcomm
    have hVnt : Nontrivial (P ⧸ frattini P) := by
      rw [← not_subsingleton_iff_nontrivial]
      intro hs
      apply hFtop
      rw [eq_top_iff]
      intro q _
      rw [← QuotientGroup.eq_one_iff]
      exact Subsingleton.elim _ _
    refine ⟨hVnt, hVel, ?_, fun S hS => ?_⟩
    · by_contra hcon
      push Not at hcon
      have htopfix : fixedPointSubgroup A (P ⧸ frattini P) = ⊤ :=
        eq_top_iff.mpr fun v _ a => hcon a v
      change fixedPointSubgroup A (P ⧸ frattini P) = ⊥ at hVfix
      rw [hVfix] at htopfix
      exact bot_ne_top htopfix
    · by_cases hSt : S = ⊤
      · exact Or.inr hSt
      left
      set S' := S.comap (QuotientGroup.mk' (frattini P))
      have hS't : S' ≠ ⊤ := by
        intro h
        apply hSt
        rw [eq_top_iff]
        intro v _
        obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective v
        have : q ∈ S' := h ▸ Subgroup.mem_top q
        exact this
      have hS'inv : ∀ (a : A), ∀ r ∈ S', a • r ∈ S' := by
        intro a r hr
        have := hS a _ hr
        exact this
      have hS'fix := hmin S' hS't hS'inv
      change fixedPointSubgroup A (P ⧸ frattini P) = ⊥ at hVfix
      rw [eq_bot_iff, ← hVfix]
      intro v hv a
      obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective v
      change ((a • q : P) : P ⧸ frattini P) = (q : P ⧸ frattini P)
      rw [hS'fix a q hv]
  ·
    have hcbot : commutator P = ⊥ := by
      rw [eq_bot_iff, commutator_eq_closure, Subgroup.closure_le]
      rintro _ ⟨x, y, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact (IsMulCommutative.is_comm (M := P)).comm x y
    have hFbot : frattini P = ⊥ := hFP.trans hcbot
    refine ⟨hFbot, ?_⟩
    refine { toIsMulCommutative := hab, exponent_dvd_p := ?_ }
    refine Monoid.exponent_dvd_of_forall_pow_eq_one fun x => ?_
    have := hpowF x
    rwa [hFbot, Subgroup.mem_bot] at this
  ·
    have hZtop : Subgroup.center P ≠ ⊤ := by
      intro h
      apply hnab
      refine ⟨⟨fun x y => ?_⟩⟩
      have : y ∈ Subgroup.center P := h ▸ Subgroup.mem_top y
      exact Subgroup.mem_center_iff.mp this x
    have hZinv : IsInvariant A P (Subgroup.center P) :=
      isInvariant_of_characteristic _
    have hZfix : ∀ (a : A), ∀ z ∈ Subgroup.center P, a • z = z :=
      hmin _ hZtop fun a r hr => (hZinv.invariant a r).mp hr
    have hZP : Subgroup.center P ≤ commutator P := fun z hz => hfixE z fun a => hZfix a z hz
    have hPZeq : commutator P = Subgroup.center P := le_antisymm hPZ hZP
    have hcne : commutator P ≠ ⊥ := by
      intro h
      apply hnab
      refine ⟨⟨fun x y => ?_⟩⟩
      have : ⁅x, y⁆ ∈ commutator P := by
        rw [commutator_eq_closure]
        exact Subgroup.subset_closure (commutator_mem_commutatorSet x y)
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
      exact this
    have hcpow : ∀ z ∈ commutator P, z ^ l = 1 := by
      let Ω : Subgroup P :=
        { carrier := {z | z ∈ Subgroup.center P ∧ z ^ l = 1}
          mul_mem' := by
            rintro z w ⟨hz, hzl⟩ ⟨hw, hwl⟩
            refine ⟨mul_mem hz hw, ?_⟩
            have hzw : Commute z w := Subgroup.mem_center_iff.mp hw z
            rw [hzw.mul_pow, hzl, hwl, one_mul]
          one_mem' := ⟨one_mem _, one_pow l⟩
          inv_mem' := by
            rintro z ⟨hz, hzl⟩
            exact ⟨inv_mem hz, by rw [inv_pow, hzl, inv_one]⟩ }
      have hle : commutator P ≤ Ω := by
        rw [commutator_eq_closure, Subgroup.closure_le]
        rintro _ ⟨x, y, rfl⟩
        have hxy : ⁅x, y⁆ ∈ commutator P := by
          rw [commutator_eq_closure]
          exact Subgroup.subset_closure (commutator_mem_commutatorSet x y)
        refine ⟨hPZ hxy, ?_⟩
        rw [← commutatorElement_pow_right_of_le_center hPZ x y l,
          commutatorElement_eq_one_iff_mul_comm]
        have hyl : y ^ l ∈ Subgroup.center P := hPZ (hFP ▸ hpowF y)
        exact (Subgroup.mem_center_iff.mp hyl x)
      exact fun z hz => (hle hz).2
    have hcel : IsElementaryAbelian l (commutator P) := by
      have hc : IsMulCommutative (commutator P) :=
        ⟨⟨fun a b => Subtype.ext (Subgroup.mem_center_iff.mp (hPZ b.2) (a : P))⟩⟩
      have hexp : Monoid.exponent (commutator P) ∣ l :=
        Monoid.exponent_dvd_of_forall_pow_eq_one fun z => Subtype.ext (by simpa using hcpow z z.2)
      exact ⟨hexp⟩
    exact ⟨hFP.symm, hFP.trans hPZeq, hcne, hcel, hZfix⟩

end CFSG.RankThree.GroupTheory.SteinbergBY
