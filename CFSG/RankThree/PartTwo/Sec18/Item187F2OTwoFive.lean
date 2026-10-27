module

public import CFSG.RankThree.PartTwo.Sec4.Notation
public import CFSG.GroupTheory.ABGLocalTools.OddOrderLocal
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.GroupTheory.Fitting.LayerTopBot
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item187Proof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Late
open scoped commutatorElement Pointwise

section Helpers

variable {T : Type} [Group T]

theorem oTwoP_characteristic' (p : ℕ) : (Sec4.oTwoP p T).Characteristic := by
  rw [Subgroup.characteristic_iff_comap_eq]
  intro σ
  set O := CFSG.pCore 2 T with hO
  have hOσ : O.map σ.toMonoidHom = O := CFSG.pCore_map_iso 2 σ
  set σ' : T ⧸ O ≃* T ⧸ O := QuotientGroup.congr O O σ hOσ with hσ'
  have hcomm : ∀ x : T, QuotientGroup.mk' O (σ x) = σ' (QuotientGroup.mk' O x) := fun x => rfl
  have hP : (CFSG.pCore p (T ⧸ O)).comap σ'.toMonoidHom = CFSG.pCore p (T ⧸ O) :=
    Subgroup.characteristic_iff_comap_eq.mp inferInstance σ'
  ext x
  change QuotientGroup.mk' O (σ x) ∈ CFSG.pCore p (T ⧸ O) ↔
    QuotientGroup.mk' O x ∈ CFSG.pCore p (T ⧸ O)
  rw [hcomm]
  conv_rhs => rw [← hP]
  rfl

theorem pPrimeCore_five_eq_bot {Y : Type} [Group Y] [Finite Y]
    (hπ : ∀ q : ℕ, q.Prime → q ∣ Nat.card Y → q = 2 ∨ q = 5) (h2 : CFSG.pCore 2 Y = ⊥) :
    CFSG.pPrimeCore 5 Y = ⊥ := by
  refine eq_bot_iff.2 (sSup_le fun K hK => ?_)
  obtain ⟨hKn, hK5⟩ := hK
  have hdiv : ∀ q : ℕ, q.Prime → q ∣ Nat.card K → q = 2 := by
    intro q hq hqK
    rcases hπ q hq (hqK.trans (Subgroup.card_subgroup_dvd_card K)) with h | h
    · exact h
    · subst h
      have h51 : Nat.gcd 5 (Nat.card K) = 1 := hK5
      rw [Nat.gcd_eq_left hqK] at h51
      norm_num at h51
  have hK2 : IsPGroup 2 K := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [IsPGroup.iff_card]
    exact ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' fun hd hdK => hdiv _ hd hdK⟩
  have hKc : K ≤ CFSG.pCore 2 Y := le_sSup ⟨hKn, hK2⟩
  rw [h2] at hKc
  exact hKc

theorem isCharacteristicP_five_of_solvable {Y : Type} [Group Y] [Finite Y] [Group.IsSolvable Y]
    (hπ : ∀ q : ℕ, q.Prime → q ∣ Nat.card Y → q = 2 ∨ q = 5) (h2 : CFSG.pCore 2 Y = ⊥) :
    CFSG.IsCharacteristicP 5 Y := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact CFSG.isCharacteristicP_of_pPrimeCore_eq_bot_of_layer_eq_bot Y 5
    (pPrimeCore_five_eq_bot hπ h2) CFSG.WholeGroup.layer_eq_bot_of_isSolvable

end Helpers

variable {G : Type} [Group G] [Finite G] {A M H : Subgroup G} {c : G} {X : Subgroup G}

@[expose] noncomputable def oTwoFive (X : Subgroup G) : Subgroup G := (Sec4.oTwoP 5 ↥X).map X.subtype

theorem oTwoFive_le (X : Subgroup G) : oTwoFive X ≤ X := Subgroup.map_subtype_le _

theorem pCoreOf_le_oTwoFive (X : Subgroup G) : CFSG.Open.pCoreOf 2 X ≤ oTwoFive X :=
  Subgroup.map_mono (Sec4.pCore_two_le_oTwoP 5 ↥X)

theorem normalizer_le_normalizer_oTwoFive (X : Subgroup G) :
    Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (oTwoFive X : Set G) := by
  haveI := oTwoP_characteristic' (T := ↥X) 5
  exact CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic (Sec4.oTwoP 5 ↥X)

theorem exists_pow_mem_pCoreOf {x : G} (hx : x ∈ oTwoFive X) :
    ∃ n : ℕ, x ^ 5 ^ n ∈ CFSG.Open.pCoreOf 2 X := by
  obtain ⟨y, hy, rfl⟩ := hx
  have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥X) y ∈ CFSG.pCore 5 (↥X ⧸ CFSG.pCore 2 ↥X) := hy
  obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := 5) (G := ↥X ⧸ CFSG.pCore 2 ↥X)) ⟨_, h1⟩
  have h2 : QuotientGroup.mk' (CFSG.pCore 2 ↥X) (y ^ 5 ^ n) = 1 := by
    rw [map_pow]
    have := congrArg Subtype.val hn
    simpa using this
  have hy2 : y ^ 5 ^ n ∈ CFSG.pCore 2 ↥X := (QuotientGroup.eq_one_iff _).1 h2
  refine ⟨n, ?_⟩
  have := Subgroup.mem_map_of_mem X.subtype hy2
  rwa [map_pow] at this

theorem mem_oTwoFive_of_commutator_mem (hsol : Group.IsSolvable ↥X)
    (hπ : ∀ q : ℕ, q.Prime → q ∣ Nat.card X → q = 2 ∨ q = 5) {x : G} (hx : x ∈ X)
    (h : ∀ y ∈ oTwoFive X, ⁅x, y⁆ ∈ CFSG.Open.pCoreOf 2 X) : x ∈ oTwoFive X := by
  haveI := hsol
  have hπY : ∀ q : ℕ, q.Prime → q ∣ Nat.card (↥X ⧸ CFSG.pCore 2 ↥X) → q = 2 ∨ q = 5 :=
    fun q hq hqY => hπ q hq (hqY.trans (Subgroup.card_quotient_dvd_card _))
  have hchar := isCharacteristicP_five_of_solvable hπY
    (CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot (p := 2))
  set x' : ↥X := ⟨x, hx⟩ with hx'
  have hmem : QuotientGroup.mk' (CFSG.pCore 2 ↥X) x' ∈ CFSG.pCore 5 (↥X ⧸ CFSG.pCore 2 ↥X) := by
    apply hchar
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    obtain ⟨y', rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥X) u
    have hy' : y' ∈ Sec4.oTwoP 5 ↥X := hu
    obtain ⟨z, hz, hzeq⟩ := h y'.1 ⟨y', hy', rfl⟩
    have hzz : z = ⁅x', y'⁆ := Subtype.ext hzeq
    have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥X) ⁅x', y'⁆ = 1 :=
      (QuotientGroup.eq_one_iff _).2 (hzz ▸ hz)
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  exact ⟨x', hmem, rfl⟩

end CFSG.RankThree.PartTwo.Sec18.Item187Proof
