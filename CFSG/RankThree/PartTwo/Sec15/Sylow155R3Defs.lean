module

public import CFSG.RankThree.PartTwo.Sec4.Statements
public import CFSG.RankThree.PartTwo.Sec4.Vocabulary

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R3

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL projSU localRank)

variable {J : Type} [Group J]

structure Res3Datum (c g : MulAut J) (V U : Subgroup (MulAut J)) : Prop where
  center_pGroup : IsPGroup 3 (Subgroup.center J)
  center_ne : Subgroup.center J ≠ ⊥
  c_pow : c ^ 3 = 1
  comm : Commute c g
  g_primes : ∀ p : ℕ, p.Prime → p ∣ orderOf g → p = 5 ∨ p = 7
  V_isPGroup : IsPGroup 2 V
  U_le : U ≤ V
  c_mem : c ∈ Subgroup.normalizer (V : Set (MulAut J))
  g_mem : g ∈ Subgroup.normalizer (V : Set (MulAut J))
  g_memU : g ∈ Subgroup.normalizer (U : Set (MulAut J))
  U_comm : ⁅U, Subgroup.zpowers g⁆ = U
  U_ne : U ≠ ⊥
  F_cent : ∀ v ∈ V, Commute c v → Commute g v
  outer_threes : c ∉ (MulAut.conj : J →* MulAut J).range →
    ∀ x : J, c x = x → x ^ 3 = 1 → x ∈ Subgroup.center J
  inner_threes : ∀ j : J, MulAut.conj j = c →
    j ^ 3 = 1 ∧ ∀ x : J, Commute x j → x ^ 3 = 1 → x ∈ Subgroup.zpowers j ⊔ Subgroup.center J
  cube : ∀ x : J, c x = x → x ^ 3 ∈ Subgroup.center J → x ^ 3 = 1
  primes : ∀ x : J, c x = x → (orderOf x).Prime →
    orderOf x = 2 ∨ orderOf x = 3 ∨ orderOf x = 5 ∨ orderOf x = 7
  rank5 : ∀ E R : Subgroup J, Nat.card E = 25 → (∀ x ∈ E, x ^ 5 = 1) → IsPGroup 2 R → R ≠ ⊥ →
    E ≤ Subgroup.normalizer (R : Set J) → False

namespace Res3Datum

variable {c g : MulAut J} {V U : Subgroup (MulAut J)}

theorem g_ne_one (h : Res3Datum c g V U) : g ≠ 1 := by
  rintro rfl
  apply h.U_ne
  rw [← h.U_comm, Subgroup.zpowers_one_eq_bot, Subgroup.commutator_bot_right]

theorem c_ne_one (h : Res3Datum c g V U) : c ≠ 1 := by
  rintro rfl
  apply h.U_ne
  rw [← h.U_comm, Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.le_centralizer_iff,
    Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
  intro u hu
  exact (h.F_cent u (h.U_le hu) (Commute.one_left u)).eq.symm

theorem not_two_dvd (h : Res3Datum c g V U) : ¬ 2 ∣ orderOf g := fun h2 => by
  rcases h.g_primes 2 Nat.prime_two h2 with h | h <;> omega

theorem not_three_dvd (h : Res3Datum c g V U) : ¬ 3 ∣ orderOf g := fun h3 => by
  rcases h.g_primes 3 Nat.prime_three h3 with h | h <;> omega

theorem coprime_six (h : Res3Datum c g V U) : Nat.Coprime (orderOf g) 6 := by
  have h2 := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h.not_two_dvd
  have h3 := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h.not_three_dvd
  exact Nat.Coprime.mul_right h2.symm h3.symm

end Res3Datum

@[expose] def Res3NoDatum : Prop :=
  ∀ (J : Type) [Group J] [Finite J], SectionFourHyp J → CFSG.IsQuasisimple J →
    ∀ (c g : MulAut J) (V U : Subgroup (MulAut J)), ¬ Res3Datum c g V U

@[expose] def Res3NoDatumL3Two : Prop :=
  ∀ (J : Type) [Group J] [Finite J], SectionFourHyp J → CFSG.IsQuasisimple J →
    ∀ e : ℕ, 1 ≤ e → IsoLThreePi (J ⧸ Subgroup.center J) 2 e →
      ∀ (c g : MulAut J) (V U : Subgroup (MulAut J)), ¬ Res3Datum c g V U

@[expose] def Res3NoDatumL3Odd : Prop :=
  ∀ (J : Type) [Group J] [Finite J], SectionFourHyp J → CFSG.IsQuasisimple J →
    ∀ (p e : ℕ) [Fact p.Prime], 5 ≤ p → 1 ≤ e → IsoLThreePi (J ⧸ Subgroup.center J) p e →
      ∀ (c g : MulAut J) (V U : Subgroup (MulAut J)), ¬ Res3Datum c g V U

@[expose] def Res3NoDatumA6 : Prop :=
  ∀ (J : Type) [Group J] [Finite J], SectionFourHyp J → CFSG.IsQuasisimple J →
    Nonempty (J ⧸ Subgroup.center J ≃* alternatingGroup (Fin 6)) →
      ∀ (c g : MulAut J) (V U : Subgroup (MulAut J)), ¬ Res3Datum c g V U

@[expose] def Res3NoDatumA7 : Prop :=
  ∀ (J : Type) [Group J] [Finite J], SectionFourHyp J → CFSG.IsQuasisimple J →
    Nonempty (J ⧸ Subgroup.center J ≃* alternatingGroup (Fin 7)) →
      ∀ (c g : MulAut J) (V U : Subgroup (MulAut J)), ¬ Res3Datum c g V U

@[expose] def Res3NoDatumG23 : Prop :=
  ∀ (J : Type) [Group J] [Finite J], SectionFourHyp J → CFSG.IsQuasisimple J →
    Blueprint.ChevalleyExceptionalModel (J ⧸ Subgroup.center J) .G2 3 1 →
      ∀ (c g : MulAut J) (V U : Subgroup (MulAut J)), ¬ Res3Datum c g V U

@[expose] def Res3NoDatumU43 : Prop :=
  ∀ (J : Type) [Group J] [Finite J], SectionFourHyp J → CFSG.IsQuasisimple J →
    Nonempty (J ⧸ Subgroup.center J ≃* projSU 4 3 1) →
      ∀ (c g : MulAut J) (V U : Subgroup (MulAut J)), ¬ Res3Datum c g V U

@[expose] def Res3NoDatumM22 : Prop :=
  ∀ (J : Type) [Group J] [Finite J], SectionFourHyp J → CFSG.IsQuasisimple J →
    Nonempty (J ⧸ Subgroup.center J ≃* Blueprint.NativeSporadic.M22) →
      ∀ (c g : MulAut J) (V U : Subgroup (MulAut J)), ¬ Res3Datum c g V U

@[expose] def Res3NoDatumJ3 : Prop :=
  ∀ (J : Type) [Group J] [Finite J], SectionFourHyp J → CFSG.IsQuasisimple J →
    Nonempty (J ⧸ Subgroup.center J ≃* Blueprint.NativeSporadic.J3) →
      ∀ (c g : MulAut J) (V U : Subgroup (MulAut J)), ¬ Res3Datum c g V U

@[expose] def Res3NoDatumMcL : Prop :=
  ∀ (J : Type) [Group J] [Finite J], SectionFourHyp J → CFSG.IsQuasisimple J →
    Nonempty (J ⧸ Subgroup.center J ≃* Blueprint.NativeSporadic.McL) →
      ∀ (c g : MulAut J) (V U : Subgroup (MulAut J)), ¬ Res3Datum c g V U

@[expose] def Res3NoDatumON : Prop :=
  ∀ (J : Type) [Group J] [Finite J], SectionFourHyp J → CFSG.IsQuasisimple J →
    Nonempty (J ⧸ Subgroup.center J ≃* Blueprint.NativeSporadic.ON) →
      ∀ (c g : MulAut J) (V U : Subgroup (MulAut J)), ¬ Res3Datum c g V U

theorem res3NoDatum_of (h43 : Item4_3) (hL2 : Res3NoDatumL3Two) (hLp : Res3NoDatumL3Odd)
    (hA6 : Res3NoDatumA6) (hA7 : Res3NoDatumA7) (hG2 : Res3NoDatumG23) (hU4 : Res3NoDatumU43)
    (hM22 : Res3NoDatumM22) (hJ3 : Res3NoDatumJ3) (hMcL : Res3NoDatumMcL)
    (hON : Res3NoDatumON) : Res3NoDatum := by
  intro J _ _ hS hq c g V U hd
  have h3 : 3 ∣ Nat.card (Subgroup.center J) :=
    hd.center_pGroup.card_eq_or_dvd.resolve_left fun h1 =>
      hd.center_ne (Subgroup.eq_bot_of_card_eq _ h1)
  rcases h43 J hS hq h3 with ⟨p, e, hp, he, hiso⟩ | h | h | h | h | h | h | h | h
  · haveI := hp
    by_cases hp2 : p = 2
    · subst hp2
      exact hL2 J hS hq e he hiso c g V U hd
    by_cases hp3 : p = 3
    · subst hp3
      have h0 : 3 ^ e % 3 = 0 := Nat.mod_eq_zero_of_dvd (dvd_pow_self 3 (by omega))
      rcases hiso with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h0] at h1 <;> exact absurd h1 (by decide)
    have h5 : 5 ≤ p := by
      have h2 := hp.out.two_le
      by_contra hlt
      interval_cases p
      · exact hp2 rfl
      · exact hp3 rfl
      · exact absurd hp.out (by decide)
    exact hLp J hS hq p e h5 he hiso c g V U hd
  · exact hA6 J hS hq h c g V U hd
  · exact hA7 J hS hq h c g V U hd
  · exact hG2 J hS hq h c g V U hd
  · exact hU4 J hS hq h c g V U hd
  · exact hM22 J hS hq h c g V U hd
  · exact hJ3 J hS hq h c g V U hd
  · exact hMcL J hS hq h c g V U hd
  · exact hON J hS hq h c g V U hd

structure Res3QComp {Q : Type} [Group Q] [Finite Q] (c d : Q) (A B₀ K : Subgroup Q) :
    Prop where
  K_quasi : CFSG.IsQuasisimple ↥K
  K_cover : Sec4.IsTripleCover ↥K (alternatingGroup (Fin 6))
  K_subnormal : K.IsSubnormal
  K_center : (Subgroup.center ↥K).map K.subtype = Subgroup.zpowers d
  d_center : d ∈ Subgroup.center Q
  c_pow : c ^ 3 = 1
  c_cent : c ∈ Subgroup.centralizer (K : Set Q)
  c_notMem : c ∉ K
  B₀_le : B₀ ≤ K
  B₀_card : Nat.card B₀ = 9
  B₀_pow : ∀ x ∈ B₀, x ^ 3 = 1
  d_mem : d ∈ B₀
  A_eq : A = B₀ ⊔ Subgroup.zpowers c

structure Res3QAmb {Q : Type} [Group Q] [Finite Q] (c d : Q) (A : Subgroup Q) : Prop where
  A_max : ∀ x ∈ Subgroup.centralizer (A : Set Q), x ^ 3 = 1 → x ∈ A
  oThreePrime : ∀ N : Subgroup Q, N.Normal → ¬ 3 ∣ Nat.card N → N = ⊥
  R4 : ∀ E T : Subgroup Q, CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 81 → IsPGroup 2 T →
    T ≠ ⊥ → E ≤ Subgroup.normalizer (T : Set Q) → False
  wsym : ∀ e ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers d, e ∉ Subgroup.zpowers d →
    ∃ w : MulAut Q, (∀ a ∈ A, w a ∈ A) ∧ w e ∉ Subgroup.zpowers e

structure Res3QBase {Q : Type} [Group Q] [Finite Q] (c d : Q) (A B₀ K : Subgroup Q) :
    Prop extends Res3QComp c d A B₀ K, Res3QAmb c d A

structure Res3QLocal {Q : Type} [Group Q] [Finite Q] (c : Q) (A : Subgroup Q) : Prop where
  fourHyp : ∀ X : Subgroup Q, CFSG.IsQuasisimple ↥X → SectionFourHyp ↥X
  rank : ∀ X : Subgroup Q, layer ↥X = ⊤ → ∀ p : ℕ, p.Prime → 3 < p → localRank p ↥X < 3
  cube : ∀ x ∈ Subgroup.centralizer (A : Set Q), IsPGroup 3 (Subgroup.zpowers x) →
    orderOf (x ^ 3) = 3 → x ^ 3 ∈ Subgroup.zpowers c
  primes : ∀ x ∈ Subgroup.centralizer (A : Set Q), (orderOf x).Prime →
    orderOf x = 2 ∨ orderOf x = 3 ∨ orderOf x = 5 ∨ orderOf x = 7

structure Res3QObs {Q : Type} [Group Q] [Finite Q] (c g : Q) (A B₀ V₀ U : Subgroup Q) :
    Prop where
  g_cent : g ∈ Subgroup.centralizer (A : Set Q)
  g_primes : ∀ p : ℕ, p.Prime → p ∣ orderOf g → p = 5 ∨ p = 7
  V₀_isPGroup : IsPGroup 2 V₀
  V₀_le : V₀ ≤ Subgroup.centralizer (B₀ : Set Q)
  c_memV₀ : c ∈ Subgroup.normalizer (V₀ : Set Q)
  g_memV₀ : g ∈ Subgroup.normalizer (V₀ : Set Q)
  U_le : U ≤ V₀
  g_memU : g ∈ Subgroup.normalizer (U : Set Q)
  U_comm_g : ⁅U, Subgroup.zpowers g⁆ = U
  U_comm_c : ⁅U, Subgroup.zpowers c⁆ = U
  U_ne : U ≠ ⊥
  F_cent : ∀ v ∈ V₀, Commute c v → Commute g v

structure Res3Q {Q : Type} [Group Q] [Finite Q] (c d g : Q) (A B₀ K V₀ U : Subgroup Q) : Prop
    extends Res3QBase c d A B₀ K, Res3QLocal c A, Res3QObs c g A B₀ V₀ U

structure Res3QCompFacts {Q : Type} [Group Q] [Finite Q] (c d : Q) (A B₀ K : Subgroup Q) :
    Prop where
  le_centralizer : ∀ J : Subgroup Q, CFSG.IsComponent J → J ≠ K →
    J ≤ Subgroup.centralizer (K : Set Q)
  unique : ∀ J₁ J₂ : Subgroup Q, CFSG.IsComponent J₁ → CFSG.IsComponent J₂ → J₁ ≠ K →
    J₂ ≠ K → J₁ = J₂
  d_mem : ∀ J : Subgroup Q, CFSG.IsComponent J → J ≠ K → d ∈ J
  center_pGroup : ∀ J : Subgroup Q, CFSG.IsComponent J → J ≠ K →
    IsPGroup 3 (Subgroup.center ↥J)
  normalizes : ∀ J : Subgroup Q, CFSG.IsComponent J →
    ∀ x ∈ Subgroup.centralizer (B₀ : Set Q), x ∈ Subgroup.normalizer (J : Set Q)
  inf_centralizer : A ⊓ Subgroup.centralizer (K : Set Q) =
    Subgroup.zpowers c ⊔ Subgroup.zpowers d


@[expose] def Res3K9 : Prop :=
  ∀ (S : Type) [Group S] [Finite S], SectionFourHyp S → IsSimpleGroup S →
    (∃ a b : S, a * b ≠ b * a) → ∀ σ : MulAut S, σ ^ 3 = 1 → σ ≠ 1 →
      ∀ C P : Subgroup S, (∀ x, x ∈ C ↔ σ x = x) → P ≤ C → (P.subgroupOf C).IsSubnormal →
        Group.IsPerfect P →
        ∀ (N : Subgroup P) [N.Normal], IsEmpty (P ⧸ N ≃* Blueprint.NativeSporadic.J2)

end CFSG.RankThree.PartTwo.Sec15.Sylow155R3
