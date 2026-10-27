module

public import CFSG.RankThree.PartTwo.KFacts.K72SLPiAut
import CFSG.RankThree.PartTwo.KFacts.K72OutL3
import CFSG.RankThree.PartTwo.KFacts.KS14MathieuAutCore
import CFSG.RankThree.PartTwo.Sec13.Item13Models
import CFSG.LocalAnalysis.ComponentInitial.QTNQRLinearUnitaryOuterDerivedLinear
import CFSG.Sporadic.Schreier.MathieuOddCoreM22
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherConjAutInner
import CFSG.RankThree.PartTwo.KFacts.AutPSUInner

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree.PartTwo

@[expose] def OutThreeClosed (X : Type*) [Group X] : Prop :=
  ∀ σ ∈ Subgroup.closure {τ : MulAut X | ∃ k : ℕ, τ ^ 3 ^ k = 1},
    ∃ k : ℕ, σ ^ 3 ^ k ∈ (MulAut.conj : X →* MulAut X).range

@[expose] def OutThreeClosed131 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsQuasisimple X →
    (Sec4.IsSLThreePi X ∨ Sec4.IsTripleCover X (alternatingGroup (Fin 7)) ∨
      Sec4.IsTripleCover X CFSG.Blueprint.NativeSporadic.M22) → OutThreeClosed X

namespace OutThreeClosed

variable {X : Type*} [Group X]

theorem of_forall_mem_range
    (h : ∀ σ : MulAut X, (∃ k : ℕ, σ ^ 3 ^ k = 1) → σ ∈ (MulAut.conj : X →* MulAut X).range) :
    OutThreeClosed X := by
  intro σ hσ
  refine ⟨0, ?_⟩
  rw [pow_zero, pow_one]
  exact (Subgroup.closure_le _).mpr (fun τ hτ => h τ hτ) hσ

theorem of_commutator_mem {D : Subgroup (MulAut X)}
    (hD : ∀ σ τ : MulAut X, σ * τ * σ⁻¹ * τ⁻¹ ∈ D)
    (hD3 : ∀ d ∈ D, d ^ 3 ∈ (MulAut.conj : X →* MulAut X).range) : OutThreeClosed X := by
  have hDn : D.Normal := ⟨fun d hd g => by
    have h1 := D.mul_mem (hD g d) hd
    rwa [show g * d * g⁻¹ * d⁻¹ * d = g * d * g⁻¹ by group] at h1⟩
  have hcomm : ∀ σ τ : MulAut X, Commute (σ : MulAut X ⧸ D) (τ : MulAut X ⧸ D) := by
    intro σ τ
    have h1 : ((σ * τ * σ⁻¹ * τ⁻¹ : MulAut X) : MulAut X ⧸ D) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (hD σ τ)
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv] at h1
    calc (σ : MulAut X ⧸ D) * τ =
        ((σ : MulAut X ⧸ D) * τ * (σ : MulAut X ⧸ D)⁻¹ * (τ : MulAut X ⧸ D)⁻¹) * (τ * σ) := by
          group
      _ = τ * σ := by rw [h1, one_mul]
  have key : ∀ σ ∈ Subgroup.closure {τ : MulAut X | ∃ k : ℕ, τ ^ 3 ^ k = 1},
      ∃ a : ℕ, σ ^ 3 ^ a ∈ D := by
    intro σ hσ
    induction hσ using Subgroup.closure_induction with
    | mem τ hτ =>
      obtain ⟨k, hk⟩ := hτ
      exact ⟨k, by rw [hk]; exact D.one_mem⟩
    | one => exact ⟨0, by rw [one_pow]; exact D.one_mem⟩
    | mul σ τ _ _ hσ hτ =>
      obtain ⟨a, ha⟩ := hσ
      obtain ⟨b, hb⟩ := hτ
      refine ⟨a + b, ?_⟩
      have hσ1 : ((σ ^ 3 ^ (a + b) : MulAut X) : MulAut X ⧸ D) = 1 := by
        rw [pow_add, pow_mul, QuotientGroup.mk_pow, (QuotientGroup.eq_one_iff _).mpr ha, one_pow]
      have hτ1 : ((τ ^ 3 ^ (a + b) : MulAut X) : MulAut X ⧸ D) = 1 := by
        rw [add_comm, pow_add, pow_mul, QuotientGroup.mk_pow, (QuotientGroup.eq_one_iff _).mpr hb,
          one_pow]
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, QuotientGroup.mk_mul,
        (hcomm σ τ).mul_pow, ← QuotientGroup.mk_pow, ← QuotientGroup.mk_pow, hσ1, hτ1, one_mul]
    | inv σ _ hσ =>
      obtain ⟨a, ha⟩ := hσ
      exact ⟨a, by rw [inv_pow]; exact D.inv_mem ha⟩
  intro σ hσ
  obtain ⟨a, ha⟩ := key σ hσ
  exact ⟨a + 1, by rw [pow_succ, pow_mul]; exact hD3 _ ha⟩

theorem of_injective {S P : Type*} [Group S] [Group P] (ψ : MulAut S →* MulAut P)
    (hψ : Function.Injective ψ) (hinn : ∀ x : P, ∃ s : S, ψ (MulAut.conj s) = MulAut.conj x)
    (hP : OutThreeClosed P) : OutThreeClosed S := by
  intro σ hσ
  have hψσ : ψ σ ∈ Subgroup.closure {τ : MulAut P | ∃ k : ℕ, τ ^ 3 ^ k = 1} := by
    have hle : (Subgroup.closure {τ : MulAut S | ∃ k : ℕ, τ ^ 3 ^ k = 1}).map ψ ≤
        Subgroup.closure {τ : MulAut P | ∃ k : ℕ, τ ^ 3 ^ k = 1} := by
      rw [MonoidHom.map_closure]
      apply Subgroup.closure_mono
      rintro _ ⟨τ, ⟨k, hk⟩, rfl⟩
      exact ⟨k, by rw [← map_pow, hk, map_one]⟩
    exact hle (Subgroup.mem_map_of_mem _ hσ)
  obtain ⟨k, x, hx⟩ := hP _ hψσ
  obtain ⟨s, hs⟩ := hinn x
  exact ⟨k, s, hψ (by rw [hs, hx, map_pow])⟩

theorem of_mulEquiv {Y : Type*} [Group Y] (e : X ≃* Y) (hY : OutThreeClosed Y) :
    OutThreeClosed X :=
  of_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective
    (fun y => ⟨e.symm y, by
      rw [MulEquiv.coe_toMonoidHom, KFacts.congr_mulAutConj, MulEquiv.apply_symm_apply]⟩) hY

end OutThreeClosed

namespace Step196Proof

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ClassicalGroups.UnitaryFlag Matrix

theorem centerDescend_conj {S : Type*} [Group S] (g : S) :
    KFacts.centerDescend S (MulAut.conj g) = MulAut.conj (g : S ⧸ Subgroup.center S) := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H x =>
    rw [KFacts.centerDescend_mk, MulAut.conj_apply, MulAut.conj_apply, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_inv]

section Linear

variable {K : Type} [Field K]

theorem pow_three_mem_range_conj_of_mem_linearAutGroup {β : MulAut (projectiveSL 3 K)}
    (hβ : β ∈ linearAutGroup 3 K) :
    β ^ 3 ∈ (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range :=
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag.pow_mem_range_conj_of_mem_linearAutGroup hβ

theorem outThreeClosed_projectiveSL [Finite K] : OutThreeClosed (projectiveSL 3 K) :=
  OutThreeClosed.of_commutator_mem (D := linearAutGroup 3 K)
    (fun σ τ => OuterDerived.commutator_mem_linearAutGroup le_rfl σ τ)
    (fun _ hd => pow_three_mem_range_conj_of_mem_linearAutGroup hd)

theorem descendAut_conj (g : SpecialLinearGroup (Fin 3) K) :
    descendAut 3 K (MulAut.conj g) = MulAut.conj (proj 3 K g) := by
  ext x
  obtain ⟨y, rfl⟩ := proj_surjective 3 K x
  rw [descendAut_proj, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]

theorem outThreeClosed_specialLinearGroup [Finite K] :
    OutThreeClosed (SpecialLinearGroup (Fin 3) K) :=
  OutThreeClosed.of_injective (descendAut 3 K) (fun _ _ h => KFacts.eq_of_descendAut_eq h)
    (fun x => by
      obtain ⟨g, rfl⟩ := proj_surjective 3 K x
      exact ⟨g, descendAut_conj g⟩)
    outThreeClosed_projectiveSL

end Linear

section Unitary

variable {p f : ℕ} {K : Type} [Field K]

theorem pow_three_mem_range_conj_of_mem_psuConj_range (h : UnitaryFieldData p f K)
    {β : MulAut (unitaryPSU h 3)} (hβ : β ∈ (KFacts.psuConj h).range) :
    β ^ 3 ∈ (MulAut.conj : unitaryPSU h 3 →* MulAut (unitaryPSU h 3)).range :=
  KFacts.cube_mem_range_conj_of_mem_psuConj_range hβ

theorem outThreeClosed_unitaryPSU (h : UnitaryFieldData p f K) (hq2 : 2 < p ^ f) :
    OutThreeClosed (unitaryPSU h 3) :=
  OutThreeClosed.of_commutator_mem (D := (KFacts.psuConj h).range)
    (fun σ τ => KFacts.commutator_mem_psuConj_range h hq2 σ τ)
    (fun _ hd => pow_three_mem_range_conj_of_mem_psuConj_range h hd)

theorem outThreeClosed_unitarySU (h : UnitaryFieldData p f K) (hq2 : 2 < p ^ f) :
    OutThreeClosed (unitarySU p f K 3) := by
  refine OutThreeClosed.of_injective ((MulAut.congr (KFacts.suCenterEquiv h hq2)).toMonoidHom.comp
    (KFacts.centerDescend _)) (fun _ _ hβγ => KFacts.eq_of_centerDescend_eq h hq2 hβγ)
    (fun x => ?_) (outThreeClosed_unitaryPSU h hq2)
  obtain ⟨y, rfl⟩ := (KFacts.suCenterEquiv h hq2).surjective x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
  refine ⟨g, ?_⟩
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, centerDescend_conj, KFacts.congr_mulAutConj]

end Unitary

theorem outThreeClosed_slPi {π : Bool} {p f : ℕ} {K : Type} [Field K] (hK : Sec4.PiField π p f K)
    (hq2 : 2 < p ^ f) : OutThreeClosed (Sec4.slPi π 3 (p ^ f) K) := by
  have := hK.finite
  cases π
  · exact OutThreeClosed.of_mulEquiv (Sec4.slPiFalseEquiv p f K)
      (outThreeClosed_unitarySU hK.unitary hq2)
  · exact OutThreeClosed.of_mulEquiv (Sec4.slPiTrueEquiv (p ^ f) K)
      outThreeClosed_specialLinearGroup

theorem outThreeClosed_of_isSLThreePi {X : Type} [Group X] (hXq : IsQuasisimple X)
    (hX : Sec4.IsSLThreePi X) : OutThreeClosed X := by
  obtain ⟨q, K, _, _, hcase⟩ := hX
  have := Fintype.ofFinite K
  obtain ⟨n, hp, hn⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hp⟩
  have hnc : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  obtain ⟨π, f, hK, hq, ⟨e⟩⟩ : ∃ (π : Bool) (f : ℕ), Sec4.PiField π (ringChar K) f K ∧
      Sec4.ModThree π (ringChar K ^ f) ∧ Nonempty (X ≃* Sec4.slPi π 3 (ringChar K ^ f) K) := by
    rcases hcase with ⟨hK, hq, ⟨e⟩⟩ | ⟨hK, hq, ⟨e⟩⟩
    · refine ⟨true, n, ⟨hp, n.2, hnc⟩, ?_, ⟨e⟩⟩
      change ringChar K ^ (n : ℕ) % 3 = 1
      rw [← hnc, hK]
      exact hq
    · have hqd : q ∣ ringChar K ^ (n : ℕ) := ⟨q, by rw [← hnc, hK, sq]⟩
      obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hp).mp hqd
      have hm1 : 1 ≤ m := by
        rcases Nat.eq_zero_or_pos m with h0 | h0
        · rw [h0, pow_zero] at hm
          rw [hm] at hq
          norm_num at hq
        · exact h0
      refine ⟨false, m, ⟨hp, hm1, by rw [hK, hm]; rfl⟩, ?_, ⟨hm ▸ e⟩⟩
      change ringChar K ^ m % 3 = 2
      rw [← hm]
      exact hq
  have hq2 : 2 < ringChar K ^ f := by
    by_contra hle
    have h2 : ringChar K ^ f = 2 := by
      have : 2 ≤ ringChar K ^ f :=
        le_trans hp.two_le (Nat.le_self_pow (by have := hK.one_le; omega) _)
      omega
    cases π
    · have hsol := Sec13.isSolvable_slPi_two hK h2
      have : Group.IsSolvable X :=
        Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
      have : Group.IsPerfect X := hXq.1
      have : Nontrivial X := by
        by_contra hnt
        rw [not_nontrivial_iff_subsingleton] at hnt
        obtain ⟨a, b, hab⟩ := hXq.2.2
        exact hab (Subsingleton.elim _ _)
      exact Group.IsPerfect.not_isSolvable X inferInstance
    · change ringChar K ^ f % 3 = 1 at hq
      omega
  exact OutThreeClosed.of_mulEquiv e (outThreeClosed_slPi hK hq2)

theorem outThreeClosed_of_isTripleCover {X Y : Type*} [Group X] [Group Y] [Finite Y]
    (hXp : Group.IsPerfect X) (hX : Sec4.IsTripleCover X Y) (hZ : Subgroup.center Y = ⊥)
    (hAut : Nat.card (MulAut Y) ≤ 2 * Nat.card Y) : OutThreeClosed X := by
  obtain ⟨-, ⟨e⟩⟩ := hX
  refine OutThreeClosed.of_forall_mem_range fun σ ⟨k, hk⟩ => ?_
  have hσ' : (MulAut.congr e (KFacts.centerDescend X σ)) ^ 3 ^ k = 1 := by
    rw [← map_pow, ← map_pow, hk, map_one, map_one]
  obtain ⟨y, hy⟩ := KFacts.KS14.exists_conj_of_card_mulAut_le hZ hAut _ ⟨k, hσ'⟩
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (e.symm y)
  have hdesc : KFacts.centerDescend X σ = KFacts.centerDescend X (MulAut.conj x) := by
    apply (MulAut.congr e).injective
    rw [hy, centerDescend_conj, KFacts.congr_mulAutConj, hx, MulEquiv.apply_symm_apply]
  have : Group.IsPerfect X := hXp
  refine ⟨x, Sec4.mulAut_eq_of_inv_mul_mem_center fun s => ?_⟩
  have h1 := congrArg (fun τ : MulAut (X ⧸ Subgroup.center X) =>
    τ (s : X ⧸ Subgroup.center X)) hdesc
  simp only [KFacts.centerDescend_mk] at h1
  exact QuotientGroup.eq.mp h1

theorem outThreeClosed_of_isTripleCover_alternatingGroup {X : Type} [Group X]
    (hXq : IsQuasisimple X) (hX : Sec4.IsTripleCover X (alternatingGroup (Fin 7))) :
    OutThreeClosed X := by
  have h4 : 4 ≤ Nat.card (Fin 7) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fin]
    norm_num
  refine outThreeClosed_of_isTripleCover hXq.1 hX (alternatingGroup.center_eq_bot h4) ?_
  rw [KFacts.KS14.card_mulAut_alternatingGroup_seven,
    KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1]

theorem outThreeClosed_of_isTripleCover_m22
    {X : Type} [Group X] (hXq : IsQuasisimple X)
    (hX : Sec4.IsTripleCover X CFSG.Blueprint.NativeSporadic.M22) : OutThreeClosed X :=
  outThreeClosed_of_isTripleCover hXq.1 hX CFSG.Sporadic.Schreier.m22_center_eq_bot'
    CFSG.Sporadic.Schreier.m22_mulAut_card

end Step196Proof

open Step196Proof

theorem outThreeClosed131 :
    OutThreeClosed131 := by
  intro X _ _ hXq hX
  rcases hX with hSL | hA7 | hM22
  · exact outThreeClosed_of_isSLThreePi hXq hSL
  · exact outThreeClosed_of_isTripleCover_alternatingGroup hXq hA7
  · exact outThreeClosed_of_isTripleCover_m22 hXq hM22

end CFSG.RankThree.PartTwo.Sec19
