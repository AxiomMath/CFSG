module

public import CFSG.RankThree.PartTwo.Sec21.Item21Res7ProofCensusTools
public import CFSG.RankThree.PartTwo.Sec21.Item211
import CFSG.RankThree.PartTwo.Sec21.Item2113Res2ProofCases
import CFSG.RankThree.PartTwo.Sec21.Item2113Proof
import CFSG.RankThree.PartTwo.Sec13.Item131Transport
import CFSG.Sporadic.Recognition.HeMultiplierCert
import CFSG.LieType.Universal.SpecialLinear
import CFSG.RankThree.PartOne.S11.SecTenEight

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Blueprint
open Subgroup

@[expose] def KS219M24 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nonempty (X ≃* NativeSporadic.M24) →
    ∀ x : X, x ≠ 1 → IsCentral218 (⊤ : Subgroup X) x →
      x ∈ inSubgroup CFSG.layer (centralizer ({x} : Set X)) ∧
      Sec4.IsTripleCover ↥(inSubgroup CFSG.layer (centralizer ({x} : Set X)))
        (alternatingGroup (Fin 6))

@[expose] def KS219J2 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nonempty (X ≃* NativeSporadic.J2) →
    ∀ x : X, x ≠ 1 → IsCentral218 (⊤ : Subgroup X) x →
      x ∈ inSubgroup CFSG.layer (centralizer ({x} : Set X)) ∧
      Sec4.IsTripleCover ↥(inSubgroup CFSG.layer (centralizer ({x} : Set X)))
        (alternatingGroup (Fin 6))

@[expose] def KS219Ru : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nonempty (X ≃* NativeSporadic.Ru) →
    ∀ x : X, x ≠ 1 → IsCentral218 (⊤ : Subgroup X) x →
      x ∈ inSubgroup CFSG.layer (centralizer ({x} : Set X)) ∧
      Sec4.IsTripleCover ↥(inSubgroup CFSG.layer (centralizer ({x} : Set X)))
        (alternatingGroup (Fin 6))

@[expose] def KS219He : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nonempty (X ≃* NativeSporadic.He) →
    ∀ x : X, x ≠ 1 → IsCentral218 (⊤ : Subgroup X) x →
      x ∈ inSubgroup CFSG.layer (centralizer ({x} : Set X)) ∧
      Sec4.IsTripleCover ↥(inSubgroup CFSG.layer (centralizer ({x} : Set X)))
        (alternatingGroup (Fin 7))

@[expose] def KS219J4 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nonempty (X ≃* NativeSporadic.J4) →
    ∀ x : X, x ≠ 1 → IsCentral218 (⊤ : Subgroup X) x →
      x ∈ inSubgroup CFSG.layer (centralizer ({x} : Set X)) ∧
      Nat.card (center ↥(inSubgroup CFSG.layer (centralizer ({x} : Set X)))) = 6 ∧
      Nonempty (↥(inSubgroup CFSG.layer (centralizer ({x} : Set X))) ⧸
        center ↥(inSubgroup CFSG.layer (centralizer ({x} : Set X))) ≃* NativeSporadic.M22)

@[expose] def KS219J4Mult : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], IsQuasisimple Q →
    Nonempty (Q ⧸ center Q ≃* NativeSporadic.J4) → ¬ 3 ∣ Nat.card (center Q) → center Q = ⊥

@[expose] def KS219G2 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), 0 < n → Even n →
    ChevalleyExceptionalModel X .G2 2 n →
    ∀ x : X, x ≠ 1 → IsCentral218 (⊤ : Subgroup X) x →
      x ∈ inSubgroup CFSG.layer (centralizer ({x} : Set X)) ∧
      Nonempty (↥(inSubgroup CFSG.layer (centralizer ({x} : Set X))) ≃* SL3 n)

@[expose] def KS219D4 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), 0 < n → Even n →
    ChevalleyExceptionalModel X .trialityD4 2 n →
    ∀ x : X, x ≠ 1 → IsCentral218 (⊤ : Subgroup X) x →
      x ∈ inSubgroup CFSG.layer (centralizer ({x} : Set X)) ∧
      Nonempty (↥(inSubgroup CFSG.layer (centralizer ({x} : Set X))) ≃* SL3 n)

namespace Item21Res7Proof

variable {G : Type} [Group G] [Finite G]

theorem theta_eq_bot_of_isTripleCover {Q S : Type*} [Group Q] [Group S] [Finite Q]
    [IsSimpleGroup S] (hQ : Group.IsPerfect Q) (hab : ∃ a b : S, a * b ≠ b * a)
    (h : Sec4.IsTripleCover Q S) : aschbacherSolvableCore 3 Q = ⊥ := by
  obtain ⟨hc, ⟨e⟩⟩ := h
  obtain ⟨a, b, hab⟩ := hab
  have hq : IsQuasisimple Q := ⟨hQ, e.isSimpleGroup, e.symm a, e.symm b, fun h' =>
    hab (e.symm.injective (by rw [map_mul, map_mul, h']))⟩
  refine theta_eq_bot_of_center hq fun z hz => ?_
  have h1 : orderOf (⟨z, hz⟩ : center Q) ∣ 3 := hc ▸ orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk] at h1
  exact orderOf_dvd_iff_pow_eq_one.mp h1

theorem theta_eq_bot_of_mulEquiv {X Y : Type} [Group X] [Group Y] [Finite X] (e : X ≃* Y)
    (h : aschbacherSolvableCore 3 Y = ⊥) : aschbacherSolvableCore 3 X = ⊥ := by
  have h1 := CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv Nat.prime_three e
  rw [h] at h1
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h1

omit [Finite G] in
theorem isPerfect_inSubgroup_layer (H : Subgroup G) :
    Group.IsPerfect ↥(inSubgroup CFSG.layer H) := by
  have : Group.IsPerfect ↥(CFSG.layer ↥H) := CFSG.LocalCores.layer_isPerfect
  exact Group.IsPerfect.ofSurjective
    (f := ((CFSG.layer ↥H).equivMapOfInjective H.subtype H.subtype_injective).toMonoidHom)
    (MulEquiv.surjective _)

theorem theta_SL3_eq_bot (n : ℕ) : aschbacherSolvableCore 3 (SL3 n) = ⊥ := by
  have hq : IsQuasisimple (SL3 n) :=
    CFSG.LieType.Universal.SpecialLinear.isQuasisimple 2 (GaloisField 2 n) le_rfl
  refine theta_eq_bot_of_center hq fun z hz => ?_
  obtain ⟨r, hr, hrz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
  rw [Fintype.card_fin] at hr
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, ← hrz, ← map_pow, hr, map_one]
  rfl

theorem exists_not_comm_six : ∃ a b : alternatingGroup (Fin 6), a * b ≠ b * a := by
  refine ⟨⟨Equiv.swap 0 2 * Equiv.swap 0 1, ?_⟩, ⟨Equiv.swap 0 3 * Equiv.swap 0 1, ?_⟩, ?_⟩
  · rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide),
      Equiv.Perm.sign_swap (by decide)]
    rfl
  · rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide),
      Equiv.Perm.sign_swap (by decide)]
    rfl
  · decide

theorem theta_eq_center {L : Subgroup G} (hL : IsQuasisimple ↥L) (hZ : center (lBar L) = ⊥) :
    aschbacherSolvableCore 3 ↥L = center ↥L := by
  refine le_antisymm (PartOne.theta_le_center_of_quasisimple Nat.prime_three hL) fun z hz => ?_
  have h1 : (z : lBar L) ∈ center (lBar L) := by
    rw [mem_center_iff]
    intro q
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, mem_center_iff.mp hz l]
  rw [hZ, mem_bot, QuotientGroup.eq_one_iff] at h1
  exact h1

omit [Finite G] in
theorem nonempty_mulEquiv_lBar {L : Subgroup G} (h : aschbacherSolvableCore 3 ↥L = ⊥) :
    Nonempty (↥L ≃* lBar L) :=
  ⟨((QuotientGroup.quotientMulEquivOfEq h).trans QuotientGroup.quotientBot).symm⟩

end Item21Res7Proof

open Item21Res7Proof

section Census

theorem item219_of (h211 : Item211) (h213 : Item213) (hM24 : KS219M24) (hJ2 : KS219J2)
    (hRu : KS219Ru) (hHe : KS219He) (hJ4 : KS219J4) (hJ4M : KS219J4Mult) (hG2 : KS219G2)
    (hD4 : KS219D4) : Item219 := by
  intro G _ _ A E U c L hpair hL d hdA hd1 hdcen
  have hLq : IsQuasisimple ↥L := h213 G A E U c L hpair
  have hdL : d ∈ L := Item2113Proof.mem_of_isCentral218 hdcen
  have hd3 : d ^ 3 = 1 := hpair.mem_S.1.1.2 d hdA
  obtain ⟨hT1, hT2, hT3⟩ := iOf218_transport hLq hdL hd3
  have hxc := isCentral_lBar hdL hdcen
  have hZ := Item2113Proof.center_lBar_eq_bot_of_isList218 hL
  have hx1 : ((⟨d, hdL⟩ : L) : lBar L) ≠ 1 := by
    intro h1
    rw [QuotientGroup.eq_one_iff] at h1
    obtain ⟨-, -, hθ3, -⟩ := solvable_prime_complement_core_characterization (H := ↥L)
      Nat.prime_three
    have hord : orderOf (⟨d, hdL⟩ : L) = 3 :=
      orderOf_eq_prime (Subtype.ext (by simpa using hd3)) fun h => hd1 (congrArg Subtype.val h)
    have h2 := orderOf_dvd_natCard (⟨_, h1⟩ : aschbacherSolvableCore 3 ↥L)
    rw [Subgroup.orderOf_mk, hord] at h2
    exact hθ3 h2
  have hθbot : (Nonempty (lBar L ≃* NativeSporadic.He) ∨ Nonempty (lBar L ≃* NativeSporadic.J4)) →
      aschbacherSolvableCore 3 ↥L = ⊥ := by
    intro hHJ
    have hθZ := theta_eq_center hLq hZ
    have hquot : Nonempty (↥L ⧸ center ↥L ≃* lBar L) :=
      ⟨QuotientGroup.quotientMulEquivOfEq hθZ.symm⟩
    obtain ⟨eq⟩ := hquot
    rw [hθZ]
    rcases hHJ with hH' | hJ'
    · obtain ⟨e⟩ := hH'
      exact CFSG.Sporadic.Recognition.HeMultiplier.heldTrivialMultiplier_of_certificate ↥L hLq
        ⟨eq.trans e⟩
    · obtain ⟨e⟩ := hJ'
      obtain ⟨-, -, hθ3, -⟩ := solvable_prime_complement_core_characterization (H := ↥L)
        Nat.prime_three
      exact hJ4M ↥L hLq ⟨eq.trans e⟩ (hθZ ▸ hθ3)
  rcases Item2113Res2Proof.starOf_cases_of_isList218 h211 hpair hL with
    ⟨hS, -⟩ | ⟨⟨n, hn, hev, hGD⟩, -⟩ | ⟨hJ, -⟩
  · rcases hS with hM | hH | hR | hJ4'
    ·
      obtain ⟨hxE, hTC⟩ := hM24 (lBar L) hM _ hx1 hxc
      have : IsSimpleGroup (alternatingGroup (Fin 6)) :=
        alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; norm_num)
      obtain ⟨e⟩ := hT2 (theta_eq_bot_of_isTripleCover (isPerfect_inSubgroup_layer _)
        exists_not_comm_six hTC)
      exact ⟨hT1 hxE, Or.inr (Or.inl ⟨Or.inl hM, Sec13.isTripleCover_of_mulEquiv e.symm hTC⟩)⟩
    ·
      obtain ⟨hxE, hTC⟩ := hHe (lBar L) hH _ hx1 hxc
      have hθ := hθbot (Or.inl hH)
      obtain ⟨e⟩ := hT3 hθ
      obtain ⟨eL⟩ := nonempty_mulEquiv_lBar hθ
      obtain ⟨eH⟩ := hH
      exact ⟨hT1 hxE, Or.inl ⟨⟨eL.trans eH⟩, Sec13.isTripleCover_of_mulEquiv e.symm hTC⟩⟩
    ·
      obtain ⟨hxE, hTC⟩ := hRu (lBar L) hR _ hx1 hxc
      have : IsSimpleGroup (alternatingGroup (Fin 6)) :=
        alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; norm_num)
      obtain ⟨e⟩ := hT2 (theta_eq_bot_of_isTripleCover (isPerfect_inSubgroup_layer _)
        exists_not_comm_six hTC)
      exact ⟨hT1 hxE, Or.inr (Or.inl ⟨Or.inr (Or.inr hR),
        Sec13.isTripleCover_of_mulEquiv e.symm hTC⟩)⟩
    ·
      obtain ⟨hxE, hc6, ⟨eM⟩⟩ := hJ4 (lBar L) hJ4' _ hx1 hxc
      have hθ := hθbot (Or.inr hJ4')
      obtain ⟨e⟩ := hT3 hθ
      obtain ⟨eL⟩ := nonempty_mulEquiv_lBar hθ
      obtain ⟨eJ⟩ := hJ4'
      refine ⟨hT1 hxE, Or.inr (Or.inr (Or.inl ⟨⟨eL.trans eJ⟩, ?_, ?_⟩))⟩
      · rw [← Sec13.map_center_mulEquiv e.symm, card_map_of_injective e.symm.injective, hc6]
      · exact ⟨(QuotientGroup.congr _ _ e (Sec13.map_center_mulEquiv e)).trans eM⟩
  ·
    have key : ((⟨d, hdL⟩ : L) : lBar L) ∈
        inSubgroup CFSG.layer (centralizer {((⟨d, hdL⟩ : L) : lBar L)}) ∧
        Nonempty (↥(inSubgroup CFSG.layer (centralizer {((⟨d, hdL⟩ : L) : lBar L)})) ≃*
          SL3 n) := by
      rcases hGD with hG | hD
      · exact hG2 (lBar L) n hn hev hG _ hx1 hxc
      · exact hD4 (lBar L) n hn hev hD _ hx1 hxc
    obtain ⟨hxE, ⟨eS⟩⟩ := key
    obtain ⟨e⟩ := hT2 (theta_eq_bot_of_mulEquiv eS (theta_SL3_eq_bot n))
    exact ⟨hT1 hxE, Or.inr (Or.inr (Or.inr ⟨n, hn, hev, hGD, ⟨e.trans eS⟩⟩))⟩
  ·
    obtain ⟨hxE, hTC⟩ := hJ2 (lBar L) hJ _ hx1 hxc
    have : IsSimpleGroup (alternatingGroup (Fin 6)) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; norm_num)
    obtain ⟨e⟩ := hT2 (theta_eq_bot_of_isTripleCover (isPerfect_inSubgroup_layer _)
      exists_not_comm_six hTC)
    exact ⟨hT1 hxE, Or.inr (Or.inl ⟨Or.inr (Or.inl hJ),
      Sec13.isTripleCover_of_mulEquiv e.symm hTC⟩)⟩

end Census

end CFSG.RankThree.PartTwo.Sec21
